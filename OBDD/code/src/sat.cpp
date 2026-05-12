class DPLLSolver {
public:
    explicit DPLLSolver(int num_vars = 0)
        : num_vars_(num_vars),
          activity_(static_cast<std::size_t>(num_vars + 1), 0) {}

    void add_clause(const std::vector<int>& clause) {
        clauses_.push_back(clause);
        for (int lit : clause) {
            int var = std::abs(lit);
            if (var > num_vars_) {
                set_num_vars(var);
            }
            activity_[static_cast<std::size_t>(var)] += 1;
        }
    }

    bool solve(const std::vector<int>& assumptions = {}) const {
        std::vector<int8_t> assign(static_cast<std::size_t>(num_vars_ + 1), 0);

        for (int lit : assumptions) {
            const int var = std::abs(lit);
            if (var == 0 || var > num_vars_) {
                return false;
            }
            const int8_t value = (lit > 0) ? 1 : -1;
            if (assign[static_cast<std::size_t>(var)] == 0) {
                assign[static_cast<std::size_t>(var)] = value;
            } else if (assign[static_cast<std::size_t>(var)] != value) {
                return false;
            }
        }

        return dpll(assign);
    }

private:
    void set_num_vars(int n) {
        if (n <= num_vars_) {
            return;
        }
        num_vars_ = n;
        activity_.resize(static_cast<std::size_t>(num_vars_ + 1), 0);
    }

    bool dpll(std::vector<int8_t>& assign) const {
        if (!unit_propagate(assign)) {
            return false;
        }

        const int var = choose_var(assign);
        if (var == 0) {
            return true;
        }

        {
            std::vector<int8_t> assign_true = assign;
            assign_true[static_cast<std::size_t>(var)] = 1;
            if (dpll(assign_true)) {
                return true;
            }
        }

        {
            std::vector<int8_t> assign_false = assign;
            assign_false[static_cast<std::size_t>(var)] = -1;
            if (dpll(assign_false)) {
                return true;
            }
        }

        return false;
    }

    bool unit_propagate(std::vector<int8_t>& assign) const {
        bool changed = true;
        while (changed) {
            changed = false;
            for (const auto& clause : clauses_) {
                if (clause.empty()) {
                    return false;
                }

                bool satisfied = false;
                int unassigned_lit = 0;
                bool multiple_unassigned = false;

                for (int lit : clause) {
                    int var = std::abs(lit);
                    int8_t value = assign[static_cast<std::size_t>(var)];
                    if (value == 0) {
                        if (unassigned_lit == 0) {
                            unassigned_lit = lit;
                        } else {
                            multiple_unassigned = true;
                        }
                        continue;
                    }
                    if ((value == 1 && lit > 0) || (value == -1 && lit < 0)) {
                        satisfied = true;
                        break;
                    }
                }

                if (satisfied) {
                    continue;
                }
                if (unassigned_lit == 0) {
                    return false;
                }
                if (multiple_unassigned) {
                    continue;
                }

                int var = std::abs(unassigned_lit);
                int8_t forced = (unassigned_lit > 0) ? 1 : -1;
                int8_t& slot = assign[static_cast<std::size_t>(var)];
                if (slot == 0) {
                    slot = forced;
                    changed = true;
                } else if (slot != forced) {
                    return false;
                }
            }
        }
        return true;
    }

    int choose_var(const std::vector<int8_t>& assign) const {
        int best_var = 0;
        int best_score = -1;
        for (int var = 1; var <= num_vars_; ++var) {
            if (assign[static_cast<std::size_t>(var)] != 0) {
                continue;
            }
            int score = activity_[static_cast<std::size_t>(var)];
            if (score > best_score) {
                best_score = score;
                best_var = var;
            }
        }
        return best_var;
    }

    int num_vars_;
    std::vector<std::vector<int>> clauses_;
    std::vector<int> activity_;
};

class SatSolver {
public:
    explicit SatSolver(int num_vars = 0) : num_vars_(0) {
        set_num_vars(num_vars);
    }

    void set_num_vars(int n) {
        if (n <= num_vars_) {
            return;
        }
        num_vars_ = n;
        while (minisat_.nVars() < num_vars_) {
            minisat_.newVar();
        }
    }

    void add_clause(const std::vector<int>& clause) {
        clause_count_ += 1;
        lit_count_ += clause.size();
        if (clause.empty()) {
            minisat_.addEmptyClause();
            return;
        }

        Minisat::vec<Minisat::Lit> lits;
        for (int lit : clause) {
            int var = std::abs(lit);
            if (var > num_vars_) {
                set_num_vars(var);
            }
            lits.push(Minisat::mkLit(var - 1, lit < 0));
        }
        minisat_.addClause(lits);
    }

    bool solve(const std::vector<int>& assumptions = {}) {
        if (!minisat_.okay()) {
            return false;
        }

        Minisat::vec<Minisat::Lit> assumps;
        for (int lit : assumptions) {
            int var = std::abs(lit);
            if (var == 0 || var > num_vars_) {
                return false;
            }
            assumps.push(Minisat::mkLit(var - 1, lit < 0));
        }
        return minisat_.solve(assumps);
    }

    // Model APIs are valid only after solve() returned true.
    bool model_is_true(int var) const {
        if (var <= 0 || var > num_vars_) {
            throw std::runtime_error("model_is_true: variable out of range");
        }
        Minisat::lbool value = minisat_.modelValue(var - 1);
        // Avoid Minisat's l_True macro/constant compatibility differences across distros.
        return Minisat::toInt(value) == 0;
    }

    // Return signed literal from current model; undef is treated as false.
    int model_lit(int var) const {
        return model_is_true(var) ? var : -var;
    }

    std::vector<int> model_blocking_clause() const {
        std::vector<int> clause;
        clause.reserve(static_cast<std::size_t>(num_vars_));
        for (int var = 1; var <= num_vars_; ++var) {
            clause.push_back(-model_lit(var));
        }
        return clause;
    }

    std::size_t clause_count() const { return clause_count_; }
    std::size_t lit_count() const { return lit_count_; }
    int num_vars() const { return num_vars_; }

private:
    int num_vars_;
    Minisat::Solver minisat_;
    std::size_t clause_count_ = 0;
    std::size_t lit_count_ = 0;
};

class CandidateSetRegistry {
public:
    int id_of(const std::vector<int>& names_raw) {
        std::vector<int> names = names_raw;
        std::sort(names.begin(), names.end());
        names.erase(std::unique(names.begin(), names.end()), names.end());
        auto it = ids_.find(names);
        if (it != ids_.end()) {
            return it->second;
        }
        int id = static_cast<int>(id_to_names_.size());
        id_to_names_.push_back(names);
        ids_.emplace(std::move(names), id);
        return id;
    }

    const std::vector<int>& names(int id) const {
        return id_to_names_.at(static_cast<std::size_t>(id));
    }

private:
    std::unordered_map<std::vector<int>, int, VectorIntHash> ids_;
    std::vector<std::vector<int>> id_to_names_;
};

class VectorStateRegistry {
public:
    int id_of(const std::vector<int>& state_raw) {
        auto it = ids_.find(state_raw);
        if (it != ids_.end()) {
            return it->second;
        }
        int id = static_cast<int>(id_to_len_.size());
        ids_.emplace(state_raw, id);
        id_to_len_.push_back(static_cast<int>(state_raw.size()));
        return id;
    }

    int len_of(int id) const {
        return id_to_len_.at(static_cast<std::size_t>(id));
    }

    std::size_t size() const {
        return id_to_len_.size();
    }

    std::size_t total_len() const {
        std::size_t sum = 0;
        for (int len : id_to_len_) {
            sum += static_cast<std::size_t>(len);
        }
        return sum;
    }

    void clear() {
        release_container(ids_);
        release_container(id_to_len_);
    }

private:
    std::unordered_map<std::vector<int>, int, VectorIntHash, VectorIntEq> ids_;
    std::vector<int> id_to_len_;
};

struct SATBVarKey {
    int pair_idx = 0;
    int left_u_idx = 0;
    int right_u_idx = 0;
    int local_choice = 0;

    bool operator==(const SATBVarKey& other) const noexcept {
        return pair_idx == other.pair_idx &&
               left_u_idx == other.left_u_idx &&
               right_u_idx == other.right_u_idx &&
               local_choice == other.local_choice;
    }
};

struct SATBVarKeyHash {
    std::size_t operator()(const SATBVarKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.pair_idx);
        hash_combine(seed, k.left_u_idx);
        hash_combine(seed, k.right_u_idx);
        hash_combine(seed, k.local_choice);
        return seed;
    }
};

struct SATConfigKeyHash {
    std::size_t operator()(const std::vector<int>& key) const noexcept {
        return VectorIntHash{}(key);
    }
};

class SATChecker {
public:
    struct DebugStats {
        std::size_t u_var_size = 0;
        std::size_t b_var_size = 0;
        std::size_t pair_groups = 0;
        std::size_t pair_group_lits_total = 0;
        std::size_t config_cache_size = 0;
        std::size_t config_cache_key_refs = 0;
        std::size_t cnf_clauses = 0;
        std::size_t cnf_lits = 0;
        int solver_vars = 0;
    };

    SATChecker(
        const fo2::TypeSystemId& spec,
        int domain_size,
        const std::vector<std::pair<int, int>>& pair_order
    )
        : spec_(spec),
          n_(domain_size),
          pair_order_(pair_order),
          ucount_(spec.unary_count()),
          solver_(0) {
        allocate_variables();
        build_base_formula();
    }

    bool check(const std::vector<int>& unary_prefix, const std::vector<int>& config) {
        auto it = config_cache_.find(config);
        if (it != config_cache_.end()) {
            return it->second;
        }
        std::vector<int> assumptions;
        assumptions.reserve(unary_prefix.size());
        for (std::size_t x = 0; x < unary_prefix.size(); ++x) {
            int u_idx = unary_prefix[x];
            assumptions.push_back(u_var_at(static_cast<int>(x), u_idx));
        }
        bool result = solver_.solve(assumptions);
        config_cache_[config] = result;
        return result;
    }

    DebugStats debug_stats() const {
        DebugStats s;
        s.u_var_size = u_var_.size();
        s.b_var_size = b_var_.size();
        s.pair_groups = pair_groups_.size();
        for (const auto& g : pair_groups_) {
            s.pair_group_lits_total += g.size();
        }
        s.config_cache_size = config_cache_.size();
        for (const auto& kv : config_cache_) {
            s.config_cache_key_refs += kv.first.size();
        }
        s.cnf_clauses = solver_.clause_count();
        s.cnf_lits = solver_.lit_count();
        s.solver_vars = solver_.num_vars();
        return s;
    }

    void release_runtime_caches() {
        release_container(config_cache_);
    }

private:
    int u_var_at(int x, int u_idx) const {
        return u_var_.at(static_cast<std::size_t>(uvar_slot(x, u_idx, ucount_)));
    }

    void allocate_variables() {
        int next_var = 1;
        const int ucount = ucount_;

        u_var_.assign(static_cast<std::size_t>(n_ * ucount), 0);

        for (int x = 0; x < n_; ++x) {
            for (int u_idx = 0; u_idx < ucount; ++u_idx) {
                u_var_[static_cast<std::size_t>(uvar_slot(x, u_idx, ucount))] = next_var;
                ++next_var;
            }
        }

        for (int pair_idx = 0; pair_idx < static_cast<int>(pair_order_.size()); ++pair_idx) {
            std::vector<int> group;
            for (int left_u_idx = 0; left_u_idx < ucount; ++left_u_idx) {
                for (int right_u_idx = 0; right_u_idx < ucount; ++right_u_idx) {
                    const auto& candidates = spec_.pair_choice_names(left_u_idx, right_u_idx);
                    for (int local_choice = 0; local_choice < static_cast<int>(candidates.size()); ++local_choice) {
                        SATBVarKey key{pair_idx, left_u_idx, right_u_idx, local_choice};
                        b_var_[key] = next_var;
                        group.push_back(next_var);
                        ++next_var;
                    }
                }
            }
            pair_groups_.push_back(std::move(group));
        }

        solver_.set_num_vars(next_var - 1);
    }

    void build_base_formula() {
        const int ucount = ucount_;
        for (int x = 0; x < n_; ++x) {
            std::vector<int> vars_x;
            vars_x.reserve(static_cast<std::size_t>(ucount));
            for (int u_idx = 0; u_idx < ucount; ++u_idx) {
                vars_x.push_back(u_var_at(x, u_idx));
            }
            add_exactly_one(vars_x);
        }

        for (const auto& group : pair_groups_) {
            if (group.empty()) {
                solver_.add_clause({});
            } else {
                add_exactly_one(group);
            }
        }

        for (const auto& kv : b_var_) {
            const SATBVarKey& key = kv.first;
            int bvar = kv.second;
            auto [i, j] = pair_order_[key.pair_idx];
            solver_.add_clause({-bvar, u_var_at(i, key.left_u_idx)});
            solver_.add_clause({-bvar, u_var_at(j, key.right_u_idx)});
        }

        for (int x = 0; x < n_; ++x) {
            for (int u_idx = 0; u_idx < ucount; ++u_idx) {
                int uvar = u_var_at(x, u_idx);
                const auto& utype = spec_.unary_types[static_cast<std::size_t>(u_idx)];

                for (int cidx = 0; cidx < spec_.existential_count(); ++cidx) {
                    if (std::find(utype.satisfies_self.begin(), utype.satisfies_self.end(), cidx) != utype.satisfies_self.end()) {
                        continue;
                    }
                    std::vector<int> witness = witness_vars_for(x, u_idx, cidx);
                    std::vector<int> clause;
                    clause.reserve(1 + witness.size());
                    clause.push_back(-uvar);
                    clause.insert(clause.end(), witness.begin(), witness.end());
                    solver_.add_clause(clause);
                }
            }
        }
    }

    std::vector<int> witness_vars_for(int x, int u_idx, int constraint_idx) const {
        std::unordered_set<int> out;
        const int ucount = ucount_;
        for (int y = 0; y < n_; ++y) {
            if (y == x) {
                continue;
            }
            if (x < y) {
                int pair_idx = entity_pair_slot(x, y, n_);
                for (int v_idx = 0; v_idx < ucount; ++v_idx) {
                    const auto& candidate_names = spec_.pair_choice_names(u_idx, v_idx);
                    for (int local_choice = 0; local_choice < static_cast<int>(candidate_names.size()); ++local_choice) {
                        int bidx = candidate_names[static_cast<std::size_t>(local_choice)];
                        const auto& btype = spec_.binary_types[static_cast<std::size_t>(bidx)];
                        if (std::find(btype.satisfies_from_left.begin(), btype.satisfies_from_left.end(), constraint_idx) != btype.satisfies_from_left.end()) {
                            SATBVarKey key{pair_idx, u_idx, v_idx, local_choice};
                            out.insert(b_var_.at(key));
                        }
                    }
                }
            } else {
                int pair_idx = entity_pair_slot(y, x, n_);
                for (int v_idx = 0; v_idx < ucount; ++v_idx) {
                    const auto& candidate_names = spec_.pair_choice_names(v_idx, u_idx);
                    for (int local_choice = 0; local_choice < static_cast<int>(candidate_names.size()); ++local_choice) {
                        int bidx = candidate_names[static_cast<std::size_t>(local_choice)];
                        const auto& btype = spec_.binary_types[static_cast<std::size_t>(bidx)];
                        if (std::find(btype.satisfies_from_right.begin(), btype.satisfies_from_right.end(), constraint_idx) != btype.satisfies_from_right.end()) {
                            SATBVarKey key{pair_idx, v_idx, u_idx, local_choice};
                            out.insert(b_var_.at(key));
                        }
                    }
                }
            }
        }
        std::vector<int> vec(out.begin(), out.end());
        std::sort(vec.begin(), vec.end());
        return vec;
    }

    void add_exactly_one(const std::vector<int>& vars) {
        solver_.add_clause(vars);
        for (std::size_t i = 0; i < vars.size(); ++i) {
            for (std::size_t j = i + 1; j < vars.size(); ++j) {
                solver_.add_clause({-vars[i], -vars[j]});
            }
        }
    }

    const fo2::TypeSystemId& spec_;
    int n_;
    const std::vector<std::pair<int, int>>& pair_order_;
    int ucount_ = 0;

    std::vector<int> u_var_;
    std::unordered_map<SATBVarKey, int, SATBVarKeyHash> b_var_;
    std::vector<std::vector<int>> pair_groups_;

    std::unordered_map<std::vector<int>, bool, SATConfigKeyHash> config_cache_;
    SatSolver solver_;
};

struct AuxConfigKeyHash {
    std::size_t operator()(const std::vector<int>& v) const noexcept {
        return VectorIntHash{}(v);
    }
};

class AuxConfigSATChecker {
public:
    struct DebugStats {
        std::size_t raw_result_cache_size = 0;
        std::size_t reduced_result_cache_size = 0;
        std::size_t raw_result_key_refs = 0;
        std::size_t reduced_result_key_refs = 0;
    };

    explicit AuxConfigSATChecker(const fo2::TypeSystemId& spec)
        : spec_(spec) {
        spec_.validate();
    }

    bool is_config_sat(const std::vector<int>& config) {
        auto raw_it = raw_result_cache_.find(config);
        if (raw_it != raw_result_cache_.end()) {
            return raw_it->second;
        }

        std::vector<int> reduced;
        reduced.reserve(config.size());
        for (std::size_t i = 0; i < config.size(); ++i) {
            const auto& u = spec_.unary_types.at(i);
            if (!u.sat_bound.has_value()) {
                throw std::runtime_error("Aux spec unary type missing sat_bound");
            }
            reduced.push_back(std::min(config[i], *u.sat_bound));
        }

        auto red_it = result_cache_.find(reduced);
        if (red_it != result_cache_.end()) {
            raw_result_cache_[config] = red_it->second;
            return red_it->second;
        }

        std::vector<int> unary_assignment = assignment_from_config(reduced);
        auto clauses = build_binary_only_formula(unary_assignment);
        bool result = solve(clauses);
        result_cache_[reduced] = result;
        raw_result_cache_[config] = result;
        return result;
    }

    DebugStats debug_stats() const {
        DebugStats s;
        s.raw_result_cache_size = raw_result_cache_.size();
        s.reduced_result_cache_size = result_cache_.size();
        for (const auto& kv : raw_result_cache_) {
            s.raw_result_key_refs += kv.first.size();
        }
        for (const auto& kv : result_cache_) {
            s.reduced_result_key_refs += kv.first.size();
        }
        return s;
    }

    void release_runtime_caches() {
        release_container(raw_result_cache_);
        release_container(result_cache_);
    }

private:
    std::vector<int> assignment_from_config(const std::vector<int>& config) const {
        std::vector<int> assignment;
        for (std::size_t i = 0; i < config.size(); ++i) {
            int count = config[i];
            for (int k = 0; k < count; ++k) {
                assignment.push_back(static_cast<int>(i));
            }
        }
        return assignment;
    }

    std::vector<std::vector<int>> build_binary_only_formula(const std::vector<int>& unary_assignment) const {
        int domain_size = static_cast<int>(unary_assignment.size());
        std::vector<std::pair<int, int>> pair_order;
        for (int i = 0; i < domain_size; ++i) {
            for (int j = i + 1; j < domain_size; ++j) {
                pair_order.emplace_back(i, j);
            }
        }

        std::map<std::pair<int, int>, std::vector<int>> pair_candidates;
        for (const auto& p : pair_order) {
            int i = p.first;
            int j = p.second;
            pair_candidates[p] = spec_.pair_choice_names(unary_assignment[i], unary_assignment[j]);
        }

        int next_var = 1;
        std::map<std::tuple<int, int, int>, int> b_var;
        std::vector<std::vector<int>> clauses;

        for (const auto& p : pair_order) {
            int i = p.first;
            int j = p.second;
            const auto& names = pair_candidates[p];
            if (names.size() == 1) {
                continue;
            }
            std::vector<int> vars;
            vars.reserve(names.size());
            for (int bidx : names) {
                b_var[std::make_tuple(i, j, bidx)] = next_var;
                vars.push_back(next_var);
                ++next_var;
            }
            auto extra = exactly_one_clauses(vars);
            clauses.insert(clauses.end(), extra.begin(), extra.end());
        }

        for (int x = 0; x < domain_size; ++x) {
            const auto& u = spec_.unary_types.at(static_cast<std::size_t>(unary_assignment[x]));

            for (int cidx = 0; cidx < spec_.existential_count(); ++cidx) {
                if (std::find(u.satisfies_self.begin(), u.satisfies_self.end(), cidx) != u.satisfies_self.end()) {
                    continue;
                }

                std::vector<int> witness_vars;
                bool satisfied_by_fixed_choice = false;

                for (int y = 0; y < domain_size; ++y) {
                    if (y == x) {
                        continue;
                    }

                    int i = (x < y) ? x : y;
                    int j = (x < y) ? y : x;
                    const auto& names = pair_candidates.at(std::make_pair(i, j));
                    const bool looking_from_left = (x < y);

                    for (int bidx : names) {
                        const auto& b = spec_.binary_types.at(static_cast<std::size_t>(bidx));
                        bool ok = looking_from_left
                            ? (std::find(b.satisfies_from_left.begin(), b.satisfies_from_left.end(), cidx) != b.satisfies_from_left.end())
                            : (std::find(b.satisfies_from_right.begin(), b.satisfies_from_right.end(), cidx) != b.satisfies_from_right.end());
                        if (!ok) {
                            continue;
                        }

                        auto var_it = b_var.find(std::make_tuple(i, j, bidx));
                        if (var_it == b_var.end()) {
                            satisfied_by_fixed_choice = true;
                            break;
                        }
                        witness_vars.push_back(var_it->second);
                    }

                    if (satisfied_by_fixed_choice) {
                        break;
                    }
                }

                if (satisfied_by_fixed_choice) {
                    continue;
                }
                if (witness_vars.empty()) {
                    return {std::vector<int>{}};
                }
                clauses.push_back(std::move(witness_vars));
            }
        }

        return clauses;
    }

    static std::vector<std::vector<int>> exactly_one_clauses(const std::vector<int>& vars) {
        std::vector<std::vector<int>> clauses;
        clauses.push_back(vars);
        for (std::size_t i = 0; i < vars.size(); ++i) {
            for (std::size_t j = i + 1; j < vars.size(); ++j) {
                clauses.push_back({-vars[i], -vars[j]});
            }
        }
        return clauses;
    }

    static bool solve(const std::vector<std::vector<int>>& clauses) {
        int max_var = 0;
        for (const auto& clause : clauses) {
            if (clause.empty()) {
                return false;
            }
            for (int lit : clause) {
                max_var = std::max(max_var, std::abs(lit));
            }
        }

        SatSolver solver(max_var);
        for (const auto& clause : clauses) {
            solver.add_clause(clause);
        }
        return solver.solve();
    }

    const fo2::TypeSystemId& spec_;

    std::unordered_map<std::vector<int>, bool, AuxConfigKeyHash> raw_result_cache_;
    std::unordered_map<std::vector<int>, bool, AuxConfigKeyHash> result_cache_;
};
