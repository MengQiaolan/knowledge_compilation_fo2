#include "stage2_component_engine.hpp"

class CompilerIndependent {
public:
    CompilerIndependent(
        int domain_size,
        const fo2::TypeSystemId& spec,
        const std::vector<fo2::TypeSystemId>& component_specs,
        const std::vector<fo2::TypeSystemId>& component_aux_specs,
        fo2::InternTable& interner
    )
        : n_(domain_size),
          spec_(spec),
          unary_order_(static_cast<std::size_t>(spec.unary_count()), 0),
          interner_(interner),
          ground_atom_cache_(interner) {
        spec_.validate();
        if (component_specs.empty()) {
            throw std::runtime_error("CompilerIndependent requires at least one component");
        }
        if (component_specs.size() != component_aux_specs.size()) {
            throw std::runtime_error("CompilerIndependent component spec/aux size mismatch");
        }

        for (int i = 0; i < static_cast<int>(unary_order_.size()); ++i) {
            unary_order_[static_cast<std::size_t>(i)] = i;
        }
        for (int i = 0; i < n_; ++i) {
            for (int j = i + 1; j < n_; ++j) {
                pair_order_.emplace_back(i, j);
            }
        }

        sat_checker_ = std::make_unique<SATChecker>(spec_, domain_size, pair_order_);
        for (std::size_t i = 0; i < component_specs.size(); ++i) {
            component_engines_.emplace_back(
                domain_size,
                component_specs[i],
                component_aux_specs[i],
                interner_,
                pair_order_,
                &builder_
            );
        }
    }

    int compile_raw() {
        std::vector<int> config(unary_order_.size(), 0);
        std::vector<int> unary_assign;
        unary_assign.reserve(n_);
        return stage_i(0, unary_assign, config);
    }

    CompiledCircuit post_process(int root, int post_process_mode) {
        release_compile_caches();
        const bool prefer_vector_full_postprocess = spec_.unary_count() < spec_.binary_count();
        return builder_.build(root, post_process_mode, prefer_vector_full_postprocess);
    }

private:
    void release_compile_caches() {
        if (sat_checker_) {
            sat_checker_->release_runtime_caches();
        }
        for (auto& engine : component_engines_) {
            engine.release_compile_caches();
        }
        release_container(unary_clause_cache_);
        builder_.release_compile_caches();
    }

    int stage_i(
        int idx,
        std::vector<int>& unary_assign,
        std::vector<int>& config
    ) {
        if (idx == n_) {
            std::vector<int> comp_nodes;
            comp_nodes.reserve(component_engines_.size());
            for (auto& engine : component_engines_) {
                int node = engine.compile_from_unary(unary_assign);
                if (node != kNoneNode) {
                    comp_nodes.push_back(node);
                }
            }
            if (comp_nodes.empty()) {
                return kNoneNode;
            }
            if (comp_nodes.size() == 1) {
                return comp_nodes[0];
            }
            return builder_.and_node(comp_nodes);
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

            int subcircuit = stage_i(idx + 1, unary_assign, config);

            config[static_cast<std::size_t>(u_idx)] -= 1;
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

    int n_;
    const fo2::TypeSystemId& spec_;
    std::vector<int> unary_order_;
    fo2::InternTable& interner_;
    GroundAtomCache ground_atom_cache_;
    std::vector<std::pair<int, int>> pair_order_;
    CircuitBuilder builder_;
    std::unique_ptr<SATChecker> sat_checker_;
    std::deque<ComponentStage2Engine> component_engines_;
    std::unordered_map<UnaryClauseKey, int, UnaryClauseKeyHash> unary_clause_cache_;
};
