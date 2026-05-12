class ComponentStage2Engine {
public:
    ComponentStage2Engine(
        int domain_size,
        const fo2::TypeSystemId& spec,
        const fo2::TypeSystemId& aux_spec,
        fo2::InternTable& interner,
        const std::vector<std::pair<int, int>>& pair_order,
        CircuitBuilder* builder
    )
        : n_(domain_size),
          spec_(spec),
          aux_spec_(aux_spec),
          interner_(interner),
          ground_atom_cache_(interner),
          pair_order_(pair_order),
          builder_(builder) {
        spec_.validate();
        aux_spec_.validate();

        for (int i = 0; i < spec_.unary_count(); ++i) {
            unary_name_to_idx_.emplace(interner_.str(spec_.unary_name_sids[static_cast<std::size_t>(i)]), i);
        }

        m_ = spec_.existential_count();
        all_sat_mask_ = 0;
        for (int i = 0; i < m_; ++i) {
            all_sat_mask_ |= (1 << i);
        }

        prepare_aux_three_block_layout();
        aux_config_index_ = build_aux_config_index();
        aux_config_checker_ = std::make_unique<AuxConfigSATChecker>(aux_spec_);

        prepare_type_signatures();
    }

    int compile_from_unary(const std::vector<int>& unary_assign) {
        std::vector<int> sat_masks(static_cast<std::size_t>(n_), 0);
        for (int i = 0; i < n_; ++i) {
            int u = unary_assign[static_cast<std::size_t>(i)];
            sat_masks[static_cast<std::size_t>(i)] = unary_sat_mask_.at(u);
        }

        std::vector<int> aux_config = init_aux_config(unary_assign, sat_masks);
        const auto& pair_sig_suffixes = pair_signature_suffixes(unary_assign);
        return stage_ii(0, 0, unary_assign, sat_masks, pair_sig_suffixes, aux_config);
    }

    void release_compile_caches() {
        if (aux_config_checker_) {
            aux_config_checker_->release_runtime_caches();
        }
        release_container(subcircuit_cache_);
        pair_suffix_registry_.clear();
        sat_state_registry_.clear();
        release_container(pair_signature_suffix_cache_);
        release_container(grouped_btypes_cache_);
        release_container(binary_group_terms_cache_);
        release_container(binary_group_clause_cache_);
        release_container(binary_term_clause_cache_);
        release_container(binary_clause_cache_);
    }

private:
    int stage_ii(
        int target,
        int pair_idx,
        const std::vector<int>& unary_assign,
        std::vector<int>& sat_masks,
        const std::vector<std::vector<int>>& pair_sig_suffixes,
        std::vector<int>& aux_config
    ) {
        if (pair_idx == static_cast<int>(pair_order_.size())) {
            return kNoneNode;
        }

        int pair_suffix_id = pair_suffix_registry_.id_of(pair_sig_suffixes[static_cast<std::size_t>(pair_idx)]);
        int sat_state_id = sat_state_registry_.id_of(sat_masks);
        SubcircuitMainKey key{pair_suffix_id, sat_state_id};
        auto cached_it = subcircuit_cache_.find(key);
        if (cached_it != subcircuit_cache_.end()) {
            return cached_it->second;
        }

        int i = pair_order_[static_cast<std::size_t>(pair_idx)].first;
        int j = pair_order_[static_cast<std::size_t>(pair_idx)].second;

        int ui = unary_assign[static_cast<std::size_t>(i)];
        int uj = unary_assign[static_cast<std::size_t>(j)];
        int si = sat_masks[static_cast<std::size_t>(i)];
        int sj = sat_masks[static_cast<std::size_t>(j)];

        bool target_shift = (i != target);
        std::vector<int> aux_config_copy;

        if (target_shift) {
            aux_config_copy = aux_config;
            aux_config[aux_index_of(unary_assign[static_cast<std::size_t>(target)], kAuxTarget, sat_masks[static_cast<std::size_t>(target)])] -= 1;
            target = i;
            aux_config[aux_index_of(ui, kAuxDone, si)] -= 1;
            aux_config[aux_index_of(ui, kAuxTarget, si)] += 1;
            move_done_to_todo(aux_config);
        }

        int old_i_aux_idx = aux_index_of(ui, kAuxTarget, si);
        int old_j_aux_idx = aux_index_of(uj, kAuxTodo, sj);
        int candidate_set_id = candidate_set_id_of(ui, uj);

        if (si == all_sat_mask_ && sj == all_sat_mask_) {
            aux_config[old_j_aux_idx] -= 1;
            int new_j_aux_idx = aux_index_of(uj, kAuxDone, sj);
            aux_config[new_j_aux_idx] += 1;

            int binary_clause = binary_group_clause_node(i, j, candidate_set_id);
            int suffix = stage_ii(target, pair_idx + 1, unary_assign, sat_masks, pair_sig_suffixes, aux_config);

            int node = kNoneNode;
            if (binary_clause != kNoneNode && suffix != kNoneNode) {
                node = builder_->and_node({binary_clause, suffix});
            } else if (binary_clause != kNoneNode) {
                node = binary_clause;
            } else {
                node = suffix;
            }

            subcircuit_cache_[key] = node;

            if (target_shift) {
                aux_config = aux_config_copy;
            } else {
                aux_config[new_j_aux_idx] -= 1;
                aux_config[old_j_aux_idx] += 1;
            }
            return node;
        }

        aux_config[old_i_aux_idx] -= 1;
        aux_config[old_j_aux_idx] -= 1;

        std::vector<int> branch_nodes;
        const auto& grouped = grouped_btypes(candidate_set_id, si, sj);
        for (const auto& group : grouped) {
            int new_i_sat_mask = group.first.first;
            int new_j_sat_mask = group.first.second;
            int new_i_aux_idx = aux_index_of(ui, kAuxTarget, new_i_sat_mask);
            int new_j_aux_idx = aux_index_of(uj, kAuxDone, new_j_sat_mask);

            aux_config[new_i_aux_idx] += 1;
            aux_config[new_j_aux_idx] += 1;

            if (!aux_config_checker_->is_config_sat(aux_config)) {
                aux_config[new_i_aux_idx] -= 1;
                aux_config[new_j_aux_idx] -= 1;
                continue;
            }

            sat_masks[static_cast<std::size_t>(i)] = new_i_sat_mask;
            sat_masks[static_cast<std::size_t>(j)] = new_j_sat_mask;

            int group_set_id = candidate_registry_.id_of(group.second);
            int binary_clause = binary_group_clause_node(i, j, group_set_id);
            int suffix = stage_ii(target, pair_idx + 1, unary_assign, sat_masks, pair_sig_suffixes, aux_config);

            if (binary_clause != kNoneNode && suffix != kNoneNode) {
                branch_nodes.push_back(builder_->and_node({binary_clause, suffix}));
            } else if (binary_clause != kNoneNode) {
                branch_nodes.push_back(binary_clause);
            } else if (suffix != kNoneNode) {
                branch_nodes.push_back(suffix);
            }

            sat_masks[static_cast<std::size_t>(i)] = si;
            sat_masks[static_cast<std::size_t>(j)] = sj;
            aux_config[new_i_aux_idx] -= 1;
            aux_config[new_j_aux_idx] -= 1;
        }

        int node = builder_->or_node(branch_nodes);
        subcircuit_cache_[key] = node;

        if (target_shift) {
            aux_config = aux_config_copy;
        } else {
            aux_config[old_i_aux_idx] += 1;
            aux_config[old_j_aux_idx] += 1;
        }
        return node;
    }

    std::vector<int> init_aux_config(const std::vector<int>& unary_assignment, const std::vector<int>& sat_masks) const {
        std::vector<int> aux_config(aux_spec_.unary_name_sids.size(), 0);
        aux_config[aux_index_of(unary_assignment[0], kAuxTarget, sat_masks[0])] += 1;
        for (std::size_t idx = 1; idx < unary_assignment.size(); ++idx) {
            aux_config[aux_index_of(unary_assignment[idx], kAuxTodo, sat_masks[idx])] += 1;
        }
        return aux_config;
    }

    void prepare_type_signatures() {
        int ucount = spec_.unary_count();
        btype_candidate_set_.assign(static_cast<std::size_t>(ucount * ucount), -1);

        for (int u_idx = 0; u_idx < spec_.unary_count(); ++u_idx) {
            unary_sat_mask_[u_idx] = constraints_to_mask(spec_.unary_types.at(static_cast<std::size_t>(u_idx)).satisfies_self);
        }

        for (int b_idx = 0; b_idx < spec_.binary_count(); ++b_idx) {
            const auto& b = spec_.binary_types.at(static_cast<std::size_t>(b_idx));
            binary_sat_mask_[b_idx] = std::make_pair(
                constraints_to_mask(b.satisfies_from_left),
                constraints_to_mask(b.satisfies_from_right)
            );
        }

        for (int left_idx = 0; left_idx < spec_.unary_count(); ++left_idx) {
            for (int right_idx = 0; right_idx < spec_.unary_count(); ++right_idx) {
                int set_id = candidate_registry_.id_of(spec_.pair_choice_names(left_idx, right_idx));
                btype_candidate_set_[static_cast<std::size_t>(unary_pair_slot(left_idx, right_idx, ucount))] = set_id;
            }
        }
    }

    int constraints_to_mask(const std::vector<int>& constraints) const {
        int mask = 0;
        for (int cidx : constraints) {
            mask |= (1 << cidx);
        }
        return mask;
    }

    std::unordered_map<AuxIndexKey, int, AuxIndexKeyHash> build_aux_config_index() const {
        std::unordered_map<AuxIndexKey, int, AuxIndexKeyHash> out;
        for (std::size_t idx = 0; idx < aux_spec_.unary_name_sids.size(); ++idx) {
            auto parsed = parse_aux_unary_name(
                aux_spec_.unary_name_sids[idx],
                spec_,
                unary_name_to_idx_,
                interner_
            );
            if (!parsed.has_value()) {
                throw std::runtime_error("Invalid aux unary type name in component stage2 engine");
            }
            AuxIndexKey key{parsed->base_u_idx, parsed->role, parsed->sat_mask};
            if (!out.emplace(key, static_cast<int>(idx)).second) {
                throw std::runtime_error("Duplicate aux unary mapping in component stage2 engine");
            }
        }
        return out;
    }

    void prepare_aux_three_block_layout() {
        const auto& unames = aux_spec_.unary_name_sids;
        if (unames.empty() || (unames.size() % 3U) != 0U) {
            throw std::runtime_error("aux unary_order size must be divisible by 3 for [target][done][todo] layout");
        }
        int block = static_cast<int>(unames.size() / 3U);
        for (int pos = 0; pos < block; ++pos) {
            auto parsed_t = parse_aux_unary_name(unames[static_cast<std::size_t>(pos)], spec_, unary_name_to_idx_, interner_);
            auto parsed_d = parse_aux_unary_name(unames[static_cast<std::size_t>(block + pos)], spec_, unary_name_to_idx_, interner_);
            auto parsed_o = parse_aux_unary_name(unames[static_cast<std::size_t>(2 * block + pos)], spec_, unary_name_to_idx_, interner_);
            if (!parsed_t.has_value() || !parsed_d.has_value() || !parsed_o.has_value()) {
                throw std::runtime_error("Invalid aux unary name in component stage2 layout");
            }
            if (parsed_t->role != kAuxTarget || parsed_d->role != kAuxDone || parsed_o->role != kAuxTodo) {
                throw std::runtime_error("aux unary_order must be [target][done][todo] in component stage2 engine");
            }
            if (parsed_t->base_u_idx != parsed_d->base_u_idx ||
                parsed_t->base_u_idx != parsed_o->base_u_idx ||
                parsed_t->sat_mask != parsed_d->sat_mask ||
                parsed_t->sat_mask != parsed_o->sat_mask) {
                throw std::runtime_error("aux unary_order blocks must align by (base_uname,sat_mask)");
            }
        }
        aux_block_size_ = block;
        aux_done_block_start_ = block;
        aux_todo_block_start_ = 2 * block;
    }

    void move_done_to_todo(std::vector<int>& aux_config) const {
        for (int offset = 0; offset < aux_block_size_; ++offset) {
            int done_idx = aux_done_block_start_ + offset;
            int todo_idx = aux_todo_block_start_ + offset;
            aux_config[static_cast<std::size_t>(todo_idx)] += aux_config[static_cast<std::size_t>(done_idx)];
            aux_config[static_cast<std::size_t>(done_idx)] = 0;
        }
    }

    int candidate_set_id_of(int left_u_idx, int right_u_idx) const {
        int ucount = spec_.unary_count();
        return btype_candidate_set_.at(static_cast<std::size_t>(unary_pair_slot(left_u_idx, right_u_idx, ucount)));
    }

    const std::vector<std::vector<int>>& pair_signature_suffixes(const std::vector<int>& unary_assign) {
        std::vector<int> pair_sig_seq;
        pair_sig_seq.reserve(pair_order_.size());
        for (const auto& p : pair_order_) {
            int left_u_idx = unary_assign[static_cast<std::size_t>(p.first)];
            int right_u_idx = unary_assign[static_cast<std::size_t>(p.second)];
            pair_sig_seq.push_back(candidate_set_id_of(left_u_idx, right_u_idx));
        }

        auto it = pair_signature_suffix_cache_.find(pair_sig_seq);
        if (it != pair_signature_suffix_cache_.end()) {
            return it->second;
        }

        std::vector<std::vector<int>> suffixes;
        suffixes.reserve(pair_sig_seq.size() + 1);
        for (std::size_t k = 0; k <= pair_sig_seq.size(); ++k) {
            suffixes.emplace_back(pair_sig_seq.begin() + static_cast<std::ptrdiff_t>(k), pair_sig_seq.end());
        }

        auto [inserted_it, _] = pair_signature_suffix_cache_.emplace(std::move(pair_sig_seq), std::move(suffixes));
        return inserted_it->second;
    }

    const std::vector<std::pair<std::pair<int, int>, std::vector<int>>>& grouped_btypes(
        int candidate_set_id,
        int si,
        int sj
    ) {
        GroupedBTypesKey key{candidate_set_id, si, sj};
        auto it = grouped_btypes_cache_.find(key);
        if (it != grouped_btypes_cache_.end()) {
            return it->second;
        }

        std::map<std::pair<int, int>, std::vector<int>> grouped;
        for (int b_idx : candidate_registry_.names(candidate_set_id)) {
            auto [sat_left, sat_right] = binary_sat_mask_.at(b_idx);
            std::pair<int, int> group_key{si | sat_left, sj | sat_right};
            grouped[group_key].push_back(b_idx);
        }

        std::vector<std::pair<std::pair<int, int>, std::vector<int>>> out;
        out.reserve(grouped.size());
        for (auto& kv : grouped) {
            out.push_back(std::move(kv));
        }

        auto [inserted_it, _] = grouped_btypes_cache_.emplace(key, std::move(out));
        return inserted_it->second;
    }

    int binary_clause_node(int x_idx, int y_idx, int bname_idx) {
        BinaryClauseKey key{x_idx, y_idx, bname_idx};
        auto it = binary_clause_cache_.find(key);
        if (it != binary_clause_cache_.end()) {
            return it->second;
        }

        auto literals = spec_.binary_types.at(static_cast<std::size_t>(bname_idx)).literals;
        std::sort(literals.begin(), literals.end());

        std::vector<int> leaves;
        leaves.reserve(literals.size());
        for (const auto& lit : literals) {
            int atom_sid = ground_atom_cache_.binary_atom_sid(lit.first, x_idx, y_idx);
            leaves.push_back(builder_->literal(atom_sid, lit.second));
        }

        if (leaves.size() == 1) {
            return leaves[0];
        }
        int node = builder_->and_node(leaves);
        binary_clause_cache_[key] = node;
        return node;
    }

    int binary_group_clause_node(int x_idx, int y_idx, int candidate_set_id) {
        BinaryGroupClauseKey key{x_idx, y_idx, candidate_set_id};
        auto it = binary_group_clause_cache_.find(key);
        if (it != binary_group_clause_cache_.end()) {
            return it->second;
        }

        const auto& terms = binary_group_terms(candidate_set_id);
        int node = kNoneNode;
        if (!(terms.size() == 1 && terms[0].empty())) {
            std::vector<int> term_nodes;
            term_nodes.reserve(terms.size());
            for (const auto& term : terms) {
                term_nodes.push_back(binary_term_clause_node(x_idx, y_idx, term));
            }
            node = builder_->or_node(term_nodes);
        }

        binary_group_clause_cache_[key] = node;
        return node;
    }

    int binary_term_clause_node(int x_idx, int y_idx, const Term& term) {
        BinaryTermClauseKey key{x_idx, y_idx, term};
        auto it = binary_term_clause_cache_.find(key);
        if (it != binary_term_clause_cache_.end()) {
            return it->second;
        }

        std::vector<int> leaves;
        leaves.reserve(term.size());
        for (const auto& lit : term) {
            int atom_sid = ground_atom_cache_.binary_atom_sid(lit.first, x_idx, y_idx);
            leaves.push_back(builder_->literal(atom_sid, lit.second));
        }

        if (leaves.size() == 1) {
            return leaves[0];
        }
        int node = builder_->and_node(leaves);
        binary_term_clause_cache_[key] = node;
        return node;
    }

    const std::vector<Term>& binary_group_terms(int candidate_set_id) {
        auto it = binary_group_terms_cache_.find(candidate_set_id);
        if (it != binary_group_terms_cache_.end()) {
            return it->second;
        }

        const auto& names = candidate_registry_.names(candidate_set_id);
        if (names.empty()) {
            auto [insert_it, _] = binary_group_terms_cache_.emplace(candidate_set_id, std::vector<Term>{});
            return insert_it->second;
        }

        std::unordered_set<Term, TermHash> terms_set;
        for (int bidx : names) {
            Term term = spec_.binary_types.at(static_cast<std::size_t>(bidx)).literals;
            std::sort(term.begin(), term.end());
            terms_set.insert(std::move(term));
        }

        std::vector<Term> simplified = simplify_dnf_terms(terms_set);
        auto [insert_it, _] = binary_group_terms_cache_.emplace(candidate_set_id, std::move(simplified));
        return insert_it->second;
    }

    static bool terms_conflict(const Term& a, const Term& b) {
        std::size_t i = 0;
        std::size_t j = 0;
        while (i < a.size() && j < b.size()) {
            if (a[i].first < b[j].first) {
                ++i;
                continue;
            }
            if (b[j].first < a[i].first) {
                ++j;
                continue;
            }
            if (a[i].second != b[j].second) {
                return true;
            }
            ++i;
            ++j;
        }
        return false;
    }

    static bool terms_pairwise_disjoint(const std::vector<Term>& terms) {
        for (std::size_t i = 0; i < terms.size(); ++i) {
            for (std::size_t j = i + 1; j < terms.size(); ++j) {
                if (!terms_conflict(terms[i], terms[j])) {
                    return false;
                }
            }
        }
        return true;
    }

    static void normalize_terms(std::vector<Term>& terms) {
        std::sort(terms.begin(), terms.end());
        terms.erase(std::unique(terms.begin(), terms.end()), terms.end());
    }

    static std::vector<Term> simplify_dnf_terms(const std::unordered_set<Term, TermHash>& terms_in) {
        std::vector<Term> terms(terms_in.begin(), terms_in.end());
        normalize_terms(terms);

        if (terms.empty()) {
            return {};
        }
        for (const auto& t : terms) {
            if (t.empty()) {
                return {Term{}};
            }
        }

        bool changed = true;
        while (changed) {
            changed = false;

            bool merged_this_round = false;
            for (std::size_t i = 0; i < terms.size() && !merged_this_round; ++i) {
                for (std::size_t j = i + 1; j < terms.size(); ++j) {
                    const Term& a = terms[i];
                    const Term& b = terms[j];
                    if (a.size() != b.size()) {
                        continue;
                    }

                    bool support_equal = true;
                    for (std::size_t k = 0; k < a.size(); ++k) {
                        if (a[k].first != b[k].first) {
                            support_equal = false;
                            break;
                        }
                    }
                    if (!support_equal) {
                        continue;
                    }

                    int diff_idx = -1;
                    bool too_many_diff = false;
                    for (std::size_t k = 0; k < a.size(); ++k) {
                        if (a[k].second != b[k].second) {
                            if (diff_idx != -1) {
                                too_many_diff = true;
                                break;
                            }
                            diff_idx = static_cast<int>(k);
                        }
                    }
                    if (too_many_diff || diff_idx == -1) {
                        continue;
                    }

                    Term merged = a;
                    merged.erase(merged.begin() + diff_idx);

                    std::vector<Term> next;
                    next.reserve(terms.size() - 1);
                    for (std::size_t p = 0; p < terms.size(); ++p) {
                        if (p != i && p != j) {
                            next.push_back(terms[p]);
                        }
                    }
                    next.push_back(std::move(merged));
                    normalize_terms(next);

                    if (!terms_pairwise_disjoint(next)) {
                        continue;
                    }

                    terms = std::move(next);
                    changed = true;
                    merged_this_round = true;
                    break;
                }
            }
        }

        std::sort(terms.begin(), terms.end(), [](const Term& a, const Term& b) {
            if (a.size() != b.size()) {
                return a.size() < b.size();
            }
            return a < b;
        });
        return terms;
    }

    int aux_index_of(int unary_idx, int role, int sat_mask) const {
        AuxIndexKey key{unary_idx, role, sat_mask};
        auto it = aux_config_index_.find(key);
        if (it == aux_config_index_.end()) {
            throw std::runtime_error("Missing aux config index in component stage2 engine");
        }
        return it->second;
    }

    int n_;
    const fo2::TypeSystemId& spec_;
    const fo2::TypeSystemId& aux_spec_;
    int m_ = 0;
    int all_sat_mask_ = 0;
    fo2::InternTable& interner_;
    GroundAtomCache ground_atom_cache_;
    std::unordered_map<std::string, int> unary_name_to_idx_;

    const std::vector<std::pair<int, int>>& pair_order_;
    CircuitBuilder* builder_ = nullptr;

    int aux_block_size_ = 0;
    int aux_done_block_start_ = 0;
    int aux_todo_block_start_ = 0;
    std::unordered_map<AuxIndexKey, int, AuxIndexKeyHash> aux_config_index_;
    std::unique_ptr<AuxConfigSATChecker> aux_config_checker_;

    CandidateSetRegistry candidate_registry_;
    std::unordered_map<int, int> unary_sat_mask_;
    std::unordered_map<int, std::pair<int, int>> binary_sat_mask_;
    std::vector<int> btype_candidate_set_;

    VectorStateRegistry pair_suffix_registry_;
    VectorStateRegistry sat_state_registry_;
    std::unordered_map<SubcircuitMainKey, int, SubcircuitMainKeyHash> subcircuit_cache_;
    std::unordered_map<std::vector<int>, std::vector<std::vector<int>>, VectorIntHash> pair_signature_suffix_cache_;
    std::unordered_map<GroupedBTypesKey, std::vector<std::pair<std::pair<int, int>, std::vector<int>>>, GroupedBTypesKeyHash> grouped_btypes_cache_;
    std::unordered_map<int, std::vector<Term>> binary_group_terms_cache_;
    std::unordered_map<BinaryGroupClauseKey, int, BinaryGroupClauseKeyHash> binary_group_clause_cache_;
    std::unordered_map<BinaryTermClauseKey, int, BinaryTermClauseKeyHash> binary_term_clause_cache_;
    std::unordered_map<BinaryClauseKey, int, BinaryClauseKeyHash> binary_clause_cache_;
};

