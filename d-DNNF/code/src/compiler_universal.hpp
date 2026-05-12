class CompilerUniversal {
public:
    struct DebugStats {
        CircuitBuilder::DebugStats circuit;
        std::size_t subcircuit_cache_size = 0;
        std::size_t pair_suffix_registry_size = 0;
        std::size_t pair_suffix_registry_total_refs = 0;
        std::size_t subcircuit_key_refs = 0;
        std::size_t pair_signature_suffix_cache_size = 0;
        std::size_t pair_signature_suffix_key_refs = 0;
        std::size_t pair_signature_suffix_value_refs = 0;
        std::size_t grouped_btypes_cache_size = 0;
        std::size_t unary_clause_cache_size = 0;
        std::size_t binary_clause_cache_size = 0;
    };

    CompilerUniversal(
        int domain_size,
        const fo2::TypeSystemId& spec,
        fo2::InternTable& interner
    )
        : n_(domain_size),
          spec_(spec),
          unary_order_(static_cast<std::size_t>(spec.unary_count()), 0),
          ground_atom_cache_(interner) {
        spec_.validate();
        if (spec_.existential_count() != 0) {
            throw std::runtime_error("CompilerUniversal requires empty existential_constraints");
        }
        for (int i = 0; i < static_cast<int>(unary_order_.size()); ++i) {
            unary_order_[static_cast<std::size_t>(i)] = i;
        }

        for (int i = 0; i < n_; ++i) {
            for (int j = i + 1; j < n_; ++j) {
                pair_order_.emplace_back(i, j);
            }
        }

        prepare_type_signatures();
    }

    int compile_raw() {
        std::vector<int> unary_assign;
        unary_assign.reserve(n_);
        return stage_i(0, unary_assign);
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
        s.circuit = builder_.debug_stats();
        s.subcircuit_cache_size = subcircuit_cache_.size();
        s.pair_suffix_registry_size = pair_suffix_registry_.size();
        s.pair_suffix_registry_total_refs = pair_suffix_registry_.total_len();
        for (const auto& kv : subcircuit_cache_) {
            s.subcircuit_key_refs += static_cast<std::size_t>(pair_suffix_registry_.len_of(kv.first));
        }
        s.pair_signature_suffix_cache_size = pair_signature_suffix_cache_.size();
        for (const auto& kv : pair_signature_suffix_cache_) {
            s.pair_signature_suffix_key_refs += kv.first.size();
            for (const auto& suffix : kv.second) {
                s.pair_signature_suffix_value_refs += suffix.size();
            }
        }
        s.grouped_btypes_cache_size = grouped_btypes_cache_.size();
        s.unary_clause_cache_size = unary_clause_cache_.size();
        s.binary_clause_cache_size = binary_clause_cache_.size();
        return s;
    }

private:
    void release_compile_caches() {
        release_container(subcircuit_cache_);
        pair_suffix_registry_.clear();
        release_container(pair_signature_suffix_cache_);
        release_container(grouped_btypes_cache_);
        release_container(unary_clause_cache_);
        release_container(binary_clause_cache_);
        builder_.release_compile_caches();
    }

    int stage_i(int idx, std::vector<int>& unary_assign) {
        if (idx == n_) {
            const auto& suffixes = pair_signature_suffixes(unary_assign);
            return stage_ii(0, unary_assign, suffixes);
        }

        std::vector<int> branch_nodes;
        for (int uname_idx = 0; uname_idx < static_cast<int>(unary_order_.size()); ++uname_idx) {
            unary_assign.push_back(uname_idx);
            int subcircuit = stage_i(idx + 1, unary_assign);
            unary_assign.pop_back();

            int unary_clause = unary_clause_node(idx, uname_idx);
            if (subcircuit != kNoneNode) {
                branch_nodes.push_back(builder_.and_node({unary_clause, subcircuit}));
            } else {
                branch_nodes.push_back(unary_clause);
            }
        }

        return builder_.or_node(branch_nodes);
    }

    int stage_ii(
        int pair_idx,
        const std::vector<int>& unary_assign,
        const std::vector<std::vector<int>>& pair_sig_suffixes
    ) {
        if (pair_idx == static_cast<int>(pair_order_.size())) {
            return kNoneNode;
        }

        int key = pair_suffix_registry_.id_of(pair_sig_suffixes[static_cast<std::size_t>(pair_idx)]);
        auto cached_it = subcircuit_cache_.find(key);
        if (cached_it != subcircuit_cache_.end()) {
            return cached_it->second;
        }

        int i = pair_order_[static_cast<std::size_t>(pair_idx)].first;
        int j = pair_order_[static_cast<std::size_t>(pair_idx)].second;
        int ui = unary_assign[static_cast<std::size_t>(i)];
        int uj = unary_assign[static_cast<std::size_t>(j)];

        int candidate_set_id = candidate_set_id_of(ui, uj);
        const auto& grouped = grouped_btypes(candidate_set_id);

        std::vector<int> branch_nodes;
        for (const auto& bnames : grouped) {
            int binary_clause = kNoneNode;
            if (bnames.size() == 1) {
                binary_clause = binary_clause_node(i, j, bnames[0]);
            } else {
                std::vector<int> grouped_clauses;
                grouped_clauses.reserve(bnames.size());
                for (int bidx : bnames) {
                    grouped_clauses.push_back(binary_clause_node(i, j, bidx));
                }
                binary_clause = builder_.or_node(grouped_clauses);
            }

            int suffix = stage_ii(pair_idx + 1, unary_assign, pair_sig_suffixes);
            if (binary_clause != kNoneNode && suffix != kNoneNode) {
                branch_nodes.push_back(builder_.and_node({binary_clause, suffix}));
            } else if (binary_clause != kNoneNode) {
                branch_nodes.push_back(binary_clause);
            } else if (suffix != kNoneNode) {
                branch_nodes.push_back(suffix);
            }
        }

        int node = builder_.or_node(branch_nodes);
        subcircuit_cache_[key] = node;
        return node;
    }

    void prepare_type_signatures() {
        int ucount = static_cast<int>(unary_order_.size());
        btype_candidate_set_.assign(static_cast<std::size_t>(ucount * ucount), -1);

        for (int left_idx = 0; left_idx < static_cast<int>(unary_order_.size()); ++left_idx) {
            for (int right_idx = 0; right_idx < static_cast<int>(unary_order_.size()); ++right_idx) {
                int set_id = candidate_registry_.id_of(spec_.pair_choice_names(left_idx, right_idx));
                btype_candidate_set_[static_cast<std::size_t>(unary_pair_slot(left_idx, right_idx, ucount))] = set_id;
            }
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

    const std::vector<std::vector<int>>& grouped_btypes(int candidate_set_id) {
        auto it = grouped_btypes_cache_.find(candidate_set_id);
        if (it != grouped_btypes_cache_.end()) {
            return it->second;
        }

        std::vector<std::vector<int>> out;
        const auto& names = candidate_registry_.names(candidate_set_id);
        if (!names.empty()) {
            out.push_back(names);
        }

        auto [inserted_it, _] = grouped_btypes_cache_.emplace(candidate_set_id, std::move(out));
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
        int node = builder_.and_node(leaves);
        binary_clause_cache_[key] = node;
        return node;
    }

    int n_;
    const fo2::TypeSystemId& spec_;
    std::vector<int> unary_order_;
    GroundAtomCache ground_atom_cache_;

    std::vector<std::pair<int, int>> pair_order_;

    CircuitBuilder builder_;
    CandidateSetRegistry candidate_registry_;

    std::vector<int> btype_candidate_set_;
    VectorStateRegistry pair_suffix_registry_;
    std::unordered_map<int, int> subcircuit_cache_;
    std::unordered_map<std::vector<int>, std::vector<std::vector<int>>, VectorIntHash> pair_signature_suffix_cache_;
    std::unordered_map<int, std::vector<std::vector<int>>> grouped_btypes_cache_;

    std::unordered_map<UnaryClauseKey, int, UnaryClauseKeyHash> unary_clause_cache_;
    std::unordered_map<BinaryClauseKey, int, BinaryClauseKeyHash> binary_clause_cache_;
};

[[maybe_unused]] static void save_dot(const CompiledCircuit& circuit, const fs::path& path, const fo2::InternTable& interner) {
    auto escape_label = [](const std::string& s) {
        std::string out;
        out.reserve(s.size() + 8);
        for (char c : s) {
            if (c == '\\') {
                out += "\\\\";
            } else if (c == '"') {
                out += "\\\"";
            } else {
                out.push_back(c);
            }
        }
        return out;
    };

    auto node_shape = [](CircuitNode::Kind kind) {
        if (kind == CircuitNode::Kind::LIT) {
            return std::string("box");
        }
        if (kind == CircuitNode::Kind::TRUE_NODE || kind == CircuitNode::Kind::FALSE_NODE) {
            return std::string("diamond");
        }
        return std::string("ellipse");
    };

    std::ofstream out(path);
    if (!out) {
        throw std::runtime_error("Failed to open DOT output file: " + path.string());
    }
    out << "digraph DNNF {\n";
    out << "  rankdir=TB;\n";

    std::vector<int> node_ids;
    node_ids.reserve(circuit.nodes.size());
    for (std::size_t node_id = 0; node_id < circuit.nodes.size(); ++node_id) {
        if (circuit.is_alive(static_cast<int>(node_id))) {
            node_ids.push_back(static_cast<int>(node_id));
        }
    }

    for (int node_id : node_ids) {
        const auto& node = circuit.nodes[static_cast<std::size_t>(node_id)];
        std::string label;
        if (node.kind == CircuitNode::Kind::LIT) {
            label = interner.str(node.atom_sid);
            if (!node.positive) {
                label = "~" + label;
            }
        } else if (node.kind == CircuitNode::Kind::AND) {
            label = "AND";
        } else if (node.kind == CircuitNode::Kind::OR) {
            label = "OR";
        } else if (node.kind == CircuitNode::Kind::TRUE_NODE) {
            label = "TRUE";
        } else {
            label = "FALSE";
        }
        out << "  n" << node.id << " [label=\"" << escape_label(label)
            << "\", shape=" << node_shape(node.kind) << "];\n";
    }

    for (int node_id : node_ids) {
        const auto& node = circuit.nodes[static_cast<std::size_t>(node_id)];
        for (int child : node.children) {
            if (!circuit.is_alive(child)) {
                continue;
            }
            out << "  n" << node.id << " -> n" << child << ";\n";
        }
    }
    out << "}\n";
}

struct VerificationStats {
    std::size_t sat_raw_models = 0;
    std::size_t sat_unique_atom_models = 0;
    std::size_t dnnf_raw_models = 0;
    std::size_t dnnf_unique_atom_models = 0;
    bool sat_enum_truncated = false;
    bool dnnf_enum_truncated = false;
};

struct VerificationResult {
    bool ok = false;
    VerificationStats stats;
    std::string message;
};
