struct UnaryClauseKey {
    int x_idx = 0;
    int uname_idx = 0;

    bool operator==(const UnaryClauseKey& other) const noexcept {
        return x_idx == other.x_idx && uname_idx == other.uname_idx;
    }
};

struct UnaryClauseKeyHash {
    std::size_t operator()(const UnaryClauseKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.x_idx);
        hash_combine(seed, k.uname_idx);
        return seed;
    }
};

struct BinaryClauseKey {
    int x_idx = 0;
    int y_idx = 0;
    int bname_idx = 0;

    bool operator==(const BinaryClauseKey& other) const noexcept {
        return x_idx == other.x_idx && y_idx == other.y_idx && bname_idx == other.bname_idx;
    }
};

struct BinaryClauseKeyHash {
    std::size_t operator()(const BinaryClauseKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.x_idx);
        hash_combine(seed, k.y_idx);
        hash_combine(seed, k.bname_idx);
        return seed;
    }
};

struct BinaryGroupClauseKey {
    int x_idx = 0;
    int y_idx = 0;
    int candidate_set_id = 0;

    bool operator==(const BinaryGroupClauseKey& other) const noexcept {
        return x_idx == other.x_idx && y_idx == other.y_idx && candidate_set_id == other.candidate_set_id;
    }
};

struct BinaryGroupClauseKeyHash {
    std::size_t operator()(const BinaryGroupClauseKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.x_idx);
        hash_combine(seed, k.y_idx);
        hash_combine(seed, k.candidate_set_id);
        return seed;
    }
};

using Literal = std::pair<int, bool>;
using Term = std::vector<Literal>;

struct TermHash {
    std::size_t operator()(const Term& t) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, t.size());
        for (const auto& lit : t) {
            hash_combine(seed, lit.first);
            hash_combine(seed, lit.second);
        }
        return seed;
    }
};

struct BinaryTermClauseKey {
    int x_idx = 0;
    int y_idx = 0;
    Term term;

    bool operator==(const BinaryTermClauseKey& other) const noexcept {
        return x_idx == other.x_idx && y_idx == other.y_idx && term == other.term;
    }
};

struct BinaryTermClauseKeyHash {
    std::size_t operator()(const BinaryTermClauseKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.x_idx);
        hash_combine(seed, k.y_idx);
        hash_combine(seed, TermHash{}(k.term));
        return seed;
    }
};

class Compiler {
public:
    struct DebugStats {
        SATChecker::DebugStats sat;
        AuxConfigSATChecker::DebugStats aux_sat;
        CircuitBuilder::DebugStats circuit;
        std::size_t subcircuit_cache_size = 0;
        std::size_t pair_suffix_registry_size = 0;
        std::size_t pair_suffix_registry_total_refs = 0;
        std::size_t sat_state_registry_size = 0;
        std::size_t sat_state_registry_total_refs = 0;
        std::size_t subcircuit_key_pair_suffix_total = 0;
        std::size_t subcircuit_key_sat_masks_total = 0;
        std::size_t pair_signature_suffix_cache_size = 0;
        std::size_t pair_signature_suffix_key_refs = 0;
        std::size_t pair_signature_suffix_value_refs = 0;
        std::size_t grouped_btypes_cache_size = 0;
        std::size_t grouped_btypes_total_groups = 0;
        std::size_t grouped_btypes_total_name_refs = 0;
        std::size_t binary_group_terms_cache_size = 0;
        std::size_t binary_group_terms_total_terms = 0;
        std::size_t binary_group_terms_total_lits = 0;
        std::size_t binary_group_clause_cache_size = 0;
        std::size_t binary_term_clause_cache_size = 0;
        std::size_t unary_clause_cache_size = 0;
        std::size_t binary_clause_cache_size = 0;
    };

    Compiler(
        int domain_size,
        const fo2::TypeSystemId& spec,
        const fo2::TypeSystemId& aux_spec,
        fo2::InternTable& interner
    )
        : n_(domain_size),
          spec_(spec),
          aux_spec_(aux_spec),
          unary_order_(static_cast<std::size_t>(spec.unary_count()), 0),
          m_(spec.existential_count()),
          interner_(interner),
          ground_atom_cache_(interner) {

        spec_.validate();
        aux_spec_.validate();

        for (int i = 0; i < static_cast<int>(unary_order_.size()); ++i) {
            unary_order_[static_cast<std::size_t>(i)] = i;
            unary_name_to_idx_.emplace(interner_.str(spec_.unary_name_sids[static_cast<std::size_t>(i)]), i);
        }

        bounds_.reserve(unary_order_.size());
        for (int uname_idx : unary_order_) {
            bounds_.push_back(spec_.unary_types.at(static_cast<std::size_t>(uname_idx)).sat_bound.value_or(0));
        }

        all_sat_mask_ = 0;
        for (int i = 0; i < m_; ++i) {
            all_sat_mask_ |= (1 << i);
        }

        for (int i = 0; i < n_; ++i) {
            for (int j = i + 1; j < n_; ++j) {
                pair_order_.emplace_back(i, j);
            }
        }

        prepare_aux_three_block_layout();
        aux_config_index_ = build_aux_config_index();

        sat_checker_ = std::make_unique<SATChecker>(spec_, domain_size, pair_order_);
        aux_config_checker_ = std::make_unique<AuxConfigSATChecker>(aux_spec_);

        prepare_type_signatures();
    }

    int compile_raw() {
        std::vector<int> config(unary_order_.size(), 0);
        std::vector<int> sat_masks(static_cast<std::size_t>(n_), 0);
        std::vector<int> unary_assign;
        unary_assign.reserve(n_);
        return stage_i(0, unary_assign, sat_masks, config);
    }

    CompiledCircuit post_process(int root, int post_process_mode) {
        release_compile_caches();
        const bool prefer_vector_full_postprocess = spec_.unary_count() < spec_.binary_count();
        return builder_.build(root, post_process_mode, prefer_vector_full_postprocess);
    }

    CompiledCircuit compile(int post_process_mode = kPostProcessNone) {
        int root = compile_raw();
        return post_process(root, post_process_mode);
    }

    DebugStats debug_stats() const {
        DebugStats s;
        s.sat = sat_checker_->debug_stats();
        s.aux_sat = aux_config_checker_->debug_stats();
        s.circuit = builder_.debug_stats();

        s.subcircuit_cache_size = subcircuit_cache_.size();
        s.pair_suffix_registry_size = pair_suffix_registry_.size();
        s.pair_suffix_registry_total_refs = pair_suffix_registry_.total_len();
        s.sat_state_registry_size = sat_state_registry_.size();
        s.sat_state_registry_total_refs = sat_state_registry_.total_len();
        for (const auto& kv : subcircuit_cache_) {
            s.subcircuit_key_pair_suffix_total += static_cast<std::size_t>(pair_suffix_registry_.len_of(kv.first.pair_suffix_id));
            s.subcircuit_key_sat_masks_total += static_cast<std::size_t>(sat_state_registry_.len_of(kv.first.sat_state_id));
        }

        s.pair_signature_suffix_cache_size = pair_signature_suffix_cache_.size();
        for (const auto& kv : pair_signature_suffix_cache_) {
            s.pair_signature_suffix_key_refs += kv.first.size();
            for (const auto& suffix : kv.second) {
                s.pair_signature_suffix_value_refs += suffix.size();
            }
        }

        s.grouped_btypes_cache_size = grouped_btypes_cache_.size();
        for (const auto& kv : grouped_btypes_cache_) {
            s.grouped_btypes_total_groups += kv.second.size();
            for (const auto& g : kv.second) {
                s.grouped_btypes_total_name_refs += g.second.size();
            }
        }

        s.binary_group_terms_cache_size = binary_group_terms_cache_.size();
        for (const auto& kv : binary_group_terms_cache_) {
            s.binary_group_terms_total_terms += kv.second.size();
            for (const auto& term : kv.second) {
                s.binary_group_terms_total_lits += term.size();
            }
        }

        s.binary_group_clause_cache_size = binary_group_clause_cache_.size();
        s.binary_term_clause_cache_size = binary_term_clause_cache_.size();
        s.unary_clause_cache_size = unary_clause_cache_.size();
        s.binary_clause_cache_size = binary_clause_cache_.size();
        return s;
    }

private:
    void release_compile_caches() {
        if (sat_checker_) {
            sat_checker_->release_runtime_caches();
        }
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
        release_container(unary_clause_cache_);
        release_container(binary_clause_cache_);
        builder_.release_compile_caches();
    }

    int stage_i(
        int idx,
        std::vector<int>& unary_assign,
        std::vector<int>& sat_masks,
        std::vector<int>& config
    ) {
        if (idx == n_) {
            std::vector<int> aux_config = init_aux_config(unary_assign, sat_masks);
            const auto& pair_sig_suffixes = pair_signature_suffixes(unary_assign);
            return stage_ii(0, 0, unary_assign, sat_masks, pair_sig_suffixes, aux_config);
        }

        std::vector<int> branch_nodes;
        for (int u_idx = 0; u_idx < static_cast<int>(unary_order_.size()); ++u_idx) {
            unary_assign.push_back(u_idx);
            config[static_cast<std::size_t>(u_idx)] += 1;

            if (!sat_checker_->check(unary_assign, config)) {
                config[static_cast<std::size_t>(u_idx)] -= 1;
                unary_assign.pop_back();
                continue;
            }

            int old_sat_mask = sat_masks[static_cast<std::size_t>(idx)];
            sat_masks[static_cast<std::size_t>(idx)] = unary_sat_mask_.at(u_idx);

            int subcircuit = stage_i(idx + 1, unary_assign, sat_masks, config);

            config[static_cast<std::size_t>(u_idx)] -= 1;
            sat_masks[static_cast<std::size_t>(idx)] = old_sat_mask;
            unary_assign.pop_back();

            int unary_clause = unary_clause_node(idx, u_idx);
            if (subcircuit != kNoneNode) {
                branch_nodes.push_back(builder_.and_node({unary_clause, subcircuit}));
            } else {
                branch_nodes.push_back(unary_clause);
            }
        }

        return builder_.or_node(branch_nodes);
    }

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
                node = builder_.and_node({binary_clause, suffix});
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
                branch_nodes.push_back(builder_.and_node({binary_clause, suffix}));
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

        int node = builder_.or_node(branch_nodes);
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
        int ucount = static_cast<int>(unary_order_.size());
        btype_candidate_set_.assign(static_cast<std::size_t>(ucount * ucount), -1);

        for (int u_idx = 0; u_idx < static_cast<int>(unary_order_.size()); ++u_idx) {
            unary_sat_mask_[u_idx] = constraints_to_mask(spec_.unary_types.at(static_cast<std::size_t>(u_idx)).satisfies_self);
        }

        for (int b_idx = 0; b_idx < spec_.binary_count(); ++b_idx) {
            const auto& b = spec_.binary_types.at(static_cast<std::size_t>(b_idx));
            binary_sat_mask_[b_idx] = std::make_pair(
                constraints_to_mask(b.satisfies_from_left),
                constraints_to_mask(b.satisfies_from_right)
            );
        }

        for (int left_idx = 0; left_idx < static_cast<int>(unary_order_.size()); ++left_idx) {
            for (int right_idx = 0; right_idx < static_cast<int>(unary_order_.size()); ++right_idx) {
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
            int aux_uname_sid = aux_spec_.unary_name_sids[idx];
            auto parsed = parse_aux_uname(aux_uname_sid);
            if (!parsed.has_value()) {
                throw std::runtime_error(
                    "Invalid aux unary type name. Expected format '<base_uname>.<target|todo|done>.<sat_mask>'."
                );
            }

            const auto& [base_uname_idx, role, sat_mask] = *parsed;
            if (base_uname_idx < 0 || base_uname_idx >= spec_.unary_count()) {
                throw std::runtime_error(
                    "aux unary type uses unknown base unary type"
                );
            }

            AuxIndexKey key{base_uname_idx, role, sat_mask};
            auto it = out.find(key);
            if (it != out.end()) {
                throw std::runtime_error(
                    "Duplicate aux unary mapping for key=(base_idx=" + std::to_string(base_uname_idx) + "," +
                    std::string(aux_role_to_cstr(role)) + "," + std::to_string(sat_mask) + ")"
                );
            }
            out[key] = static_cast<int>(idx);
        }

        return out;
    }

    std::optional<std::tuple<int, int, int>> parse_aux_uname(int aux_uname_sid) const {
        const std::string& aux_uname = interner_.str(aux_uname_sid);
        std::size_t last_dot = aux_uname.rfind('.');
        if (last_dot == std::string::npos) {
            return std::nullopt;
        }
        std::size_t second_dot = aux_uname.rfind('.', last_dot - 1);
        if (second_dot == std::string::npos) {
            return std::nullopt;
        }

        std::string base_uname = aux_uname.substr(0, second_dot);
        std::string role_str = aux_uname.substr(second_dot + 1, last_dot - second_dot - 1);
        std::string sat_mask_str = aux_uname.substr(last_dot + 1);

        if (base_uname.empty()) {
            return std::nullopt;
        }
        auto role = aux_role_from_string(role_str);
        if (!role.has_value()) {
            return std::nullopt;
        }

        int sat_mask = 0;
        try {
            std::size_t parsed = 0;
            sat_mask = std::stoi(sat_mask_str, &parsed);
            if (parsed != sat_mask_str.size()) {
                return std::nullopt;
            }
        } catch (...) {
            return std::nullopt;
        }

        auto base_it = unary_name_to_idx_.find(base_uname);
        if (base_it == unary_name_to_idx_.end()) {
            return std::nullopt;
        }
        return std::make_tuple(base_it->second, *role, sat_mask);
    }

    void prepare_aux_three_block_layout() {
        const auto& unames = aux_spec_.unary_name_sids;
        int total = static_cast<int>(unames.size());
        if (total % 3 != 0) {
            throw std::runtime_error("aux unary_order size must be divisible by 3 for [target][done][todo] layout");
        }

        int block = total / 3;
        for (int pos = 0; pos < block; ++pos) {
            int t_name_sid = unames[static_cast<std::size_t>(pos)];
            int d_name_sid = unames[static_cast<std::size_t>(block + pos)];
            int o_name_sid = unames[static_cast<std::size_t>(2 * block + pos)];

            auto parsed_t = parse_aux_uname(t_name_sid);
            auto parsed_d = parse_aux_uname(d_name_sid);
            auto parsed_o = parse_aux_uname(o_name_sid);
            if (!parsed_t.has_value() || !parsed_d.has_value() || !parsed_o.has_value()) {
                throw std::runtime_error(
                    "Invalid aux unary name at layout position " + std::to_string(pos) + "; expected '<base_uname>.<target|done|todo>.<sat_mask>'."
                );
            }

            const auto& [base_t, role_t, mask_t] = *parsed_t;
            const auto& [base_d, role_d, mask_d] = *parsed_d;
            const auto& [base_o, role_o, mask_o] = *parsed_o;

            if (role_t != kAuxTarget || role_d != kAuxDone || role_o != kAuxTodo) {
                throw std::runtime_error("aux unary_order must be partitioned as [target block][done block][todo block]");
            }
            if (!(base_t == base_d && base_t == base_o && mask_t == mask_d && mask_t == mask_o)) {
                throw std::runtime_error("aux unary_order blocks must be one-to-one aligned by (base_uname, sat_mask)");
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
        int ucount = static_cast<int>(unary_order_.size());
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

    int unary_clause_node(int x_idx, int uname_idx) {
        UnaryClauseKey key{x_idx, uname_idx};
        auto it = unary_clause_cache_.find(key);
        if (it != unary_clause_cache_.end()) {
            return it->second;
        }

        auto literals = spec_.unary_types.at(static_cast<std::size_t>(uname_idx)).literals;
        std::sort(literals.begin(), literals.end());

        std::vector<int> leaves;
        leaves.reserve(literals.size());
        for (const auto& lit : literals) {
            int atom_sid = ground_atom_cache_.unary_atom_sid(lit.first, x_idx);
            leaves.push_back(builder_.literal(atom_sid, lit.second));
        }

        if (leaves.size() == 1) {
            return leaves[0];
        }

        int node = builder_.and_node(leaves);
        unary_clause_cache_[key] = node;
        return node;
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
            leaves.push_back(builder_.literal(atom_sid, lit.second));
        }

        if (leaves.size() == 1) {
            return leaves[0];
        }

        int node = builder_.and_node(leaves);
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
            node = builder_.or_node(term_nodes);
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
            leaves.push_back(builder_.literal(atom_sid, lit.second));
        }

        if (leaves.size() == 1) {
            return leaves[0];
        }

        int node = builder_.and_node(leaves);
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

        // We must preserve deterministic OR semantics for strict d-DNNF:
        // only accept merges when the resulting terms remain pairwise disjoint.
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
            throw std::runtime_error(
                "Missing aux config index for (unary_idx=" + std::to_string(unary_idx) + ", " +
                std::string(aux_role_to_cstr(role)) + ", " + std::to_string(sat_mask) + ")"
            );
        }
        return it->second;
    }

    int n_;
    const fo2::TypeSystemId& spec_;
    const fo2::TypeSystemId& aux_spec_;

    std::vector<int> unary_order_;
    int m_ = 0;
    std::vector<int> bounds_;
    int all_sat_mask_ = 0;
    fo2::InternTable& interner_;
    GroundAtomCache ground_atom_cache_;
    std::unordered_map<std::string, int> unary_name_to_idx_;

    std::vector<std::pair<int, int>> pair_order_;

    int aux_block_size_ = 0;
    int aux_done_block_start_ = 0;
    int aux_todo_block_start_ = 0;

    std::unordered_map<AuxIndexKey, int, AuxIndexKeyHash> aux_config_index_;

    CircuitBuilder builder_;
    std::unique_ptr<SATChecker> sat_checker_;
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

    std::unordered_map<UnaryClauseKey, int, UnaryClauseKeyHash> unary_clause_cache_;
    std::unordered_map<BinaryClauseKey, int, BinaryClauseKeyHash> binary_clause_cache_;
};
