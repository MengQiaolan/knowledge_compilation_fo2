#include "compiler_common.hpp"
#include "compiler_branches.hpp"

class BigUInt {
public:
    BigUInt() = default;
    explicit BigUInt(std::uint64_t v) { set(v); }

    BigUInt& operator=(std::uint64_t v) {
        set(v);
        return *this;
    }

    BigUInt& operator+=(const BigUInt& rhs) {
        const std::size_t n = std::max(limbs_.size(), rhs.limbs_.size());
        limbs_.resize(n, 0U);
        std::uint64_t carry = 0;
        for (std::size_t i = 0; i < n; ++i) {
            std::uint64_t a = limbs_[i];
            std::uint64_t b = (i < rhs.limbs_.size()) ? rhs.limbs_[i] : 0U;
            std::uint64_t sum = a + b + carry;
            limbs_[i] = static_cast<std::uint32_t>(sum & 0xFFFFFFFFULL);
            carry = sum >> 32U;
        }
        if (carry != 0) {
            limbs_.push_back(static_cast<std::uint32_t>(carry));
        }
        return *this;
    }

    BigUInt& operator*=(const BigUInt& rhs) {
        if (is_zero() || rhs.is_zero()) {
            limbs_.clear();
            return *this;
        }
        std::vector<std::uint32_t> out(limbs_.size() + rhs.limbs_.size(), 0U);
        for (std::size_t i = 0; i < limbs_.size(); ++i) {
            unsigned __int128 carry = 0;
            for (std::size_t j = 0; j < rhs.limbs_.size(); ++j) {
                unsigned __int128 cur =
                    static_cast<unsigned __int128>(out[i + j]) +
                    static_cast<unsigned __int128>(limbs_[i]) * rhs.limbs_[j] +
                    carry;
                out[i + j] = static_cast<std::uint32_t>(cur & 0xFFFFFFFFULL);
                carry = cur >> 32U;
            }
            std::size_t k = i + rhs.limbs_.size();
            while (carry != 0) {
                if (k >= out.size()) {
                    out.push_back(0U);
                }
                unsigned __int128 cur = static_cast<unsigned __int128>(out[k]) + carry;
                out[k] = static_cast<std::uint32_t>(cur & 0xFFFFFFFFULL);
                carry = cur >> 32U;
                ++k;
            }
        }
        limbs_.swap(out);
        trim();
        return *this;
    }

    BigUInt& operator<<=(int bits) {
        if (bits <= 0 || is_zero()) {
            return *this;
        }
        const int word_shift = bits / 32;
        const int bit_shift = bits % 32;

        if (word_shift > 0) {
            limbs_.insert(limbs_.begin(), static_cast<std::size_t>(word_shift), 0U);
        }

        if (bit_shift > 0) {
            std::uint64_t carry = 0;
            for (std::size_t i = 0; i < limbs_.size(); ++i) {
                std::uint64_t cur = (static_cast<std::uint64_t>(limbs_[i]) << bit_shift) | carry;
                limbs_[i] = static_cast<std::uint32_t>(cur & 0xFFFFFFFFULL);
                carry = cur >> 32U;
            }
            if (carry != 0) {
                limbs_.push_back(static_cast<std::uint32_t>(carry));
            }
        }
        return *this;
    }

    friend std::ostream& operator<<(std::ostream& os, const BigUInt& v) {
        os << v.to_string();
        return os;
    }

private:
    bool is_zero() const { return limbs_.empty(); }

    void set(std::uint64_t v) {
        limbs_.clear();
        if (v == 0) {
            return;
        }
        limbs_.push_back(static_cast<std::uint32_t>(v & 0xFFFFFFFFULL));
        std::uint32_t hi = static_cast<std::uint32_t>(v >> 32U);
        if (hi != 0U) {
            limbs_.push_back(hi);
        }
    }

    void trim() {
        while (!limbs_.empty() && limbs_.back() == 0U) {
            limbs_.pop_back();
        }
    }

    std::string to_string() const {
        if (limbs_.empty()) {
            return "0";
        }
        static constexpr std::uint32_t kBase10 = 1000000000U;

        std::vector<std::uint32_t> tmp = limbs_;
        std::vector<std::uint32_t> parts;
        while (!tmp.empty()) {
            std::uint64_t rem = 0;
            for (std::size_t idx = tmp.size(); idx-- > 0;) {
                std::uint64_t cur = (rem << 32U) + tmp[idx];
                tmp[idx] = static_cast<std::uint32_t>(cur / kBase10);
                rem = cur % kBase10;
            }
            parts.push_back(static_cast<std::uint32_t>(rem));
            while (!tmp.empty() && tmp.back() == 0U) {
                tmp.pop_back();
            }
        }

        std::ostringstream oss;
        oss << parts.back();
        for (std::size_t i = parts.size() - 1; i-- > 0;) {
            oss << std::setw(9) << std::setfill('0') << parts[i];
        }
        return oss.str();
    }

    std::vector<std::uint32_t> limbs_;
};

using BigInt = BigUInt;

struct OriginalFormulaEncoding {
    struct BVarKey {
        int pair_idx = 0;
        int left_u_idx = 0;
        int right_u_idx = 0;
        int bname_idx = 0;

        bool operator==(const BVarKey& other) const noexcept {
            return pair_idx == other.pair_idx &&
                   left_u_idx == other.left_u_idx &&
                   right_u_idx == other.right_u_idx &&
                   bname_idx == other.bname_idx;
        }
    };

    struct BVarKeyHash {
        std::size_t operator()(const BVarKey& k) const noexcept {
            std::size_t seed = 0;
            hash_combine(seed, k.pair_idx);
            hash_combine(seed, k.left_u_idx);
            hash_combine(seed, k.right_u_idx);
            hash_combine(seed, k.bname_idx);
            return seed;
        }
    };

    int num_vars = 0;
    std::unordered_map<int, int> atom_sid_to_var;
    std::unordered_map<int, int> var_to_atom_sid;
    std::vector<int> atom_var_order;
    std::vector<std::pair<int, int>> pair_order;
    std::vector<int> u_var;
    std::unordered_map<BVarKey, int, BVarKeyHash> b_var;
    std::vector<std::vector<int>> clauses;
};

struct DnnfTseitinEncoding {
    int num_vars = 0;
    int root_var = 0;
    std::vector<std::vector<int>> clauses;
};

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

static void save_dot(const CompiledCircuit& circuit, const fs::path& path, const fo2::InternTable& interner) {
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

static std::vector<int> collect_ground_atom_sids(
    const fo2::TypeSystemId& spec,
    int domain_size,
    GroundAtomCache& ground_atom_cache,
    const fo2::InternTable& interner
) {
    std::unordered_set<int> unary_templates;
    for (const auto& utype : spec.unary_types) {
        for (const auto& lit : utype.literals) {
            unary_templates.insert(lit.first);
        }
    }

    std::unordered_set<int> binary_templates;
    for (const auto& btype : spec.binary_types) {
        for (const auto& lit : btype.literals) {
            binary_templates.insert(lit.first);
        }
    }

    std::unordered_set<int> atom_sid_set;
    for (int x = 0; x < domain_size; ++x) {
        for (int templ_sid : unary_templates) {
            atom_sid_set.insert(ground_atom_cache.unary_atom_sid(templ_sid, x));
        }
    }
    for (int i = 0; i < domain_size; ++i) {
        for (int j = i + 1; j < domain_size; ++j) {
            for (int templ_sid : binary_templates) {
                atom_sid_set.insert(ground_atom_cache.binary_atom_sid(templ_sid, i, j));
            }
        }
    }

    std::vector<int> atom_sids(atom_sid_set.begin(), atom_sid_set.end());
    std::sort(atom_sids.begin(), atom_sids.end(), [&interner](int a, int b) {
        return interner.str(a) < interner.str(b);
    });
    return atom_sids;
}

static bool contains_int(const std::vector<int>& xs, int value) {
    return std::find(xs.begin(), xs.end(), value) != xs.end();
}

static void add_exactly_one(std::vector<std::vector<int>>& clauses, const std::vector<int>& vars) {
    clauses.push_back(vars);
    for (std::size_t i = 0; i < vars.size(); ++i) {
        for (std::size_t j = i + 1; j < vars.size(); ++j) {
            clauses.push_back({-vars[i], -vars[j]});
        }
    }
}

static OriginalFormulaEncoding build_original_formula_encoding(
    const fo2::TypeSystemId& spec,
    int domain_size,
    fo2::InternTable& interner
) {
    OriginalFormulaEncoding out;
    GroundAtomCache ground_atom_cache(interner);
    std::vector<int> atom_sids = collect_ground_atom_sids(spec, domain_size, ground_atom_cache, interner);

    int next_var = 1;
    for (int atom_sid : atom_sids) {
        out.atom_sid_to_var[atom_sid] = next_var;
        out.var_to_atom_sid[next_var] = atom_sid;
        out.atom_var_order.push_back(next_var);
        ++next_var;
    }

    const int ucount = spec.unary_count();
    out.u_var.assign(static_cast<std::size_t>(domain_size * ucount), 0);
    for (int x = 0; x < domain_size; ++x) {
        for (int u_idx = 0; u_idx < ucount; ++u_idx) {
            out.u_var[static_cast<std::size_t>(uvar_slot(x, u_idx, ucount))] = next_var;
            ++next_var;
        }
    }

    std::vector<std::vector<int>> pair_groups;
    for (int i = 0; i < domain_size; ++i) {
        for (int j = i + 1; j < domain_size; ++j) {
            out.pair_order.emplace_back(i, j);
        }
    }

    for (int pair_idx = 0; pair_idx < static_cast<int>(out.pair_order.size()); ++pair_idx) {
        std::vector<int> group;
        for (int left_u = 0; left_u < ucount; ++left_u) {
            for (int right_u = 0; right_u < ucount; ++right_u) {
                std::vector<int> candidates = spec.pair_choice_names(left_u, right_u);
                std::sort(candidates.begin(), candidates.end());
                for (int bidx : candidates) {
                    OriginalFormulaEncoding::BVarKey key{pair_idx, left_u, right_u, bidx};
                    out.b_var[key] = next_var;
                    group.push_back(next_var);
                    ++next_var;
                }
            }
        }
        pair_groups.push_back(std::move(group));
    }

    out.num_vars = next_var - 1;

    for (int x = 0; x < domain_size; ++x) {
        std::vector<int> vars_x;
        vars_x.reserve(static_cast<std::size_t>(ucount));
        for (int u_idx = 0; u_idx < ucount; ++u_idx) {
            vars_x.push_back(out.u_var[static_cast<std::size_t>(uvar_slot(x, u_idx, ucount))]);
        }
        add_exactly_one(out.clauses, vars_x);
    }

    for (const auto& group : pair_groups) {
        if (group.empty()) {
            out.clauses.push_back({});
        } else {
            add_exactly_one(out.clauses, group);
        }
    }

    for (const auto& kv : out.b_var) {
        const auto& key = kv.first;
        int bvar = kv.second;
        auto [i, j] = out.pair_order.at(static_cast<std::size_t>(key.pair_idx));
        int ui_var = out.u_var.at(static_cast<std::size_t>(uvar_slot(i, key.left_u_idx, ucount)));
        int uj_var = out.u_var.at(static_cast<std::size_t>(uvar_slot(j, key.right_u_idx, ucount)));
        out.clauses.push_back({-bvar, ui_var});
        out.clauses.push_back({-bvar, uj_var});
    }

    for (int x = 0; x < domain_size; ++x) {
        for (int u_idx = 0; u_idx < ucount; ++u_idx) {
            int uvar = out.u_var.at(static_cast<std::size_t>(uvar_slot(x, u_idx, ucount)));
            auto literals = spec.unary_types.at(static_cast<std::size_t>(u_idx)).literals;
            std::sort(literals.begin(), literals.end());
            for (const auto& lit : literals) {
                int atom_sid = ground_atom_cache.unary_atom_sid(lit.first, x);
                int avar = out.atom_sid_to_var.at(atom_sid);
                out.clauses.push_back({-uvar, lit.second ? avar : -avar});
            }
        }
    }

    for (const auto& kv : out.b_var) {
        const auto& key = kv.first;
        int bvar = kv.second;
        auto [i, j] = out.pair_order.at(static_cast<std::size_t>(key.pair_idx));
        auto literals = spec.binary_types.at(static_cast<std::size_t>(key.bname_idx)).literals;
        std::sort(literals.begin(), literals.end());
        for (const auto& lit : literals) {
            int atom_sid = ground_atom_cache.binary_atom_sid(lit.first, i, j);
            int avar = out.atom_sid_to_var.at(atom_sid);
            out.clauses.push_back({-bvar, lit.second ? avar : -avar});
        }
    }

    for (int x = 0; x < domain_size; ++x) {
        for (int u_idx = 0; u_idx < ucount; ++u_idx) {
            int uvar = out.u_var.at(static_cast<std::size_t>(uvar_slot(x, u_idx, ucount)));
            const auto& utype = spec.unary_types.at(static_cast<std::size_t>(u_idx));
            for (int cidx = 0; cidx < spec.existential_count(); ++cidx) {
                if (contains_int(utype.satisfies_self, cidx)) {
                    continue;
                }

                std::unordered_set<int> witness_vars;
                for (int y = 0; y < domain_size; ++y) {
                    if (y == x) {
                        continue;
                    }

                    if (x < y) {
                        int pair_idx = entity_pair_slot(x, y, domain_size);
                        for (int v_idx = 0; v_idx < ucount; ++v_idx) {
                            std::vector<int> candidates = spec.pair_choice_names(u_idx, v_idx);
                            std::sort(candidates.begin(), candidates.end());
                            for (int bidx : candidates) {
                                const auto& btype = spec.binary_types.at(static_cast<std::size_t>(bidx));
                                if (!contains_int(btype.satisfies_from_left, cidx)) {
                                    continue;
                                }
                                OriginalFormulaEncoding::BVarKey key{pair_idx, u_idx, v_idx, bidx};
                                witness_vars.insert(out.b_var.at(key));
                            }
                        }
                    } else {
                        int pair_idx = entity_pair_slot(y, x, domain_size);
                        for (int v_idx = 0; v_idx < ucount; ++v_idx) {
                            std::vector<int> candidates = spec.pair_choice_names(v_idx, u_idx);
                            std::sort(candidates.begin(), candidates.end());
                            for (int bidx : candidates) {
                                const auto& btype = spec.binary_types.at(static_cast<std::size_t>(bidx));
                                if (!contains_int(btype.satisfies_from_right, cidx)) {
                                    continue;
                                }
                                OriginalFormulaEncoding::BVarKey key{pair_idx, v_idx, u_idx, bidx};
                                witness_vars.insert(out.b_var.at(key));
                            }
                        }
                    }
                }

                std::vector<int> witness_sorted(witness_vars.begin(), witness_vars.end());
                std::sort(witness_sorted.begin(), witness_sorted.end());
                std::vector<int> clause;
                clause.reserve(1 + witness_sorted.size());
                clause.push_back(-uvar);
                clause.insert(clause.end(), witness_sorted.begin(), witness_sorted.end());
                out.clauses.push_back(std::move(clause));
            }
        }
    }

    return out;
}

static int popcount_row_bits(
    const std::vector<std::uint64_t>& bits,
    std::size_t row_offset,
    std::size_t words_per_row
) {
    int cnt = 0;
    for (std::size_t w = 0; w < words_per_row; ++w) {
        cnt += std::popcount(bits[row_offset + w]);
    }
    return cnt;
}

static BigInt model_count_circuit(
    const fo2::TypeSystemId& spec,
    const CompiledCircuit& circuit,
    int domain_size,
    fo2::InternTable& interner
) {
    if (!circuit.is_alive(circuit.root)) {
        throw std::runtime_error("Model counting failed: root node is not alive");
    }

    GroundAtomCache ground_atom_cache(interner);
    std::vector<int> atom_sids = collect_ground_atom_sids(spec, domain_size, ground_atom_cache, interner);
    const int atom_universe_size = static_cast<int>(atom_sids.size());

    std::unordered_map<int, int> atom_sid_to_pos;
    atom_sid_to_pos.reserve(atom_sids.size());
    for (int pos = 0; pos < atom_universe_size; ++pos) {
        atom_sid_to_pos.emplace(atom_sids[static_cast<std::size_t>(pos)], pos);
    }

    const int node_count = static_cast<int>(circuit.nodes.size());
    std::vector<uint8_t> reachable(static_cast<std::size_t>(node_count), 0);
    std::vector<int> stack;
    stack.push_back(circuit.root);
    while (!stack.empty()) {
        int node_id = stack.back();
        stack.pop_back();
        if (node_id < 0 || node_id >= node_count) {
            throw std::runtime_error("Model counting failed: node id out of range");
        }
        if (!circuit.is_alive(node_id)) {
            throw std::runtime_error("Model counting failed: encountered non-alive node");
        }
        if (reachable[static_cast<std::size_t>(node_id)] != 0) {
            continue;
        }
        reachable[static_cast<std::size_t>(node_id)] = 1;
        for (int child : circuit.nodes[static_cast<std::size_t>(node_id)].children) {
            stack.push_back(child);
        }
    }

    std::vector<std::vector<int>> parents(static_cast<std::size_t>(node_count));
    std::vector<int> pending_children(static_cast<std::size_t>(node_count), 0);
    int reachable_count = 0;
    for (int node_id = 0; node_id < node_count; ++node_id) {
        if (reachable[static_cast<std::size_t>(node_id)] == 0) {
            continue;
        }
        reachable_count += 1;
        const auto& node = circuit.nodes[static_cast<std::size_t>(node_id)];
        for (int child : node.children) {
            if (child < 0 || child >= node_count || !circuit.is_alive(child)) {
                throw std::runtime_error("Model counting failed: child node invalid or not alive");
            }
            if (reachable[static_cast<std::size_t>(child)] == 0) {
                throw std::runtime_error("Model counting failed: child node not reachable");
            }
            parents[static_cast<std::size_t>(child)].push_back(node_id);
            pending_children[static_cast<std::size_t>(node_id)] += 1;
        }
    }

    const std::size_t words_per_row = (atom_sids.size() + 63U) / 64U;
    std::vector<std::uint64_t> support_bits(static_cast<std::size_t>(node_count) * words_per_row, 0ULL);
    std::vector<int> support_sizes(static_cast<std::size_t>(node_count), 0);
    std::vector<BigInt> model_counts(static_cast<std::size_t>(node_count), BigInt(0));

    std::deque<int> ready;
    for (int node_id = 0; node_id < node_count; ++node_id) {
        if (reachable[static_cast<std::size_t>(node_id)] == 0) {
            continue;
        }
        if (pending_children[static_cast<std::size_t>(node_id)] == 0) {
            ready.push_back(node_id);
        }
    }

    int processed = 0;
    while (!ready.empty()) {
        int node_id = ready.front();
        ready.pop_front();
        processed += 1;

        const CircuitNode& node = circuit.nodes[static_cast<std::size_t>(node_id)];
        const std::size_t row_off = static_cast<std::size_t>(node_id) * words_per_row;

        if (node.kind == CircuitNode::Kind::TRUE_NODE) {
            model_counts[static_cast<std::size_t>(node_id)] = 1;
            support_sizes[static_cast<std::size_t>(node_id)] = 0;
        } else if (node.kind == CircuitNode::Kind::FALSE_NODE) {
            model_counts[static_cast<std::size_t>(node_id)] = 0;
            support_sizes[static_cast<std::size_t>(node_id)] = 0;
        } else if (node.kind == CircuitNode::Kind::LIT) {
            model_counts[static_cast<std::size_t>(node_id)] = 1;
            auto it = atom_sid_to_pos.find(node.atom_sid);
            if (it == atom_sid_to_pos.end()) {
                throw std::runtime_error("Model counting failed: literal atom missing from ground atom universe");
            }
            if (words_per_row > 0) {
                int atom_pos = it->second;
                std::size_t w = static_cast<std::size_t>(atom_pos / 64);
                std::size_t b = static_cast<std::size_t>(atom_pos % 64);
                support_bits[row_off + w] |= (1ULL << b);
            }
            support_sizes[static_cast<std::size_t>(node_id)] = 1;
        } else if (node.kind == CircuitNode::Kind::AND) {
            BigInt count(1);
            for (int child : node.children) {
                count *= model_counts[static_cast<std::size_t>(child)];
                if (words_per_row > 0) {
                    const std::size_t child_off = static_cast<std::size_t>(child) * words_per_row;
                    for (std::size_t w = 0; w < words_per_row; ++w) {
                        support_bits[row_off + w] |= support_bits[child_off + w];
                    }
                }
            }
            model_counts[static_cast<std::size_t>(node_id)] = std::move(count);
            support_sizes[static_cast<std::size_t>(node_id)] = popcount_row_bits(support_bits, row_off, words_per_row);
        } else if (node.kind == CircuitNode::Kind::OR) {
            for (int child : node.children) {
                if (words_per_row > 0) {
                    const std::size_t child_off = static_cast<std::size_t>(child) * words_per_row;
                    for (std::size_t w = 0; w < words_per_row; ++w) {
                        support_bits[row_off + w] |= support_bits[child_off + w];
                    }
                }
            }
            const int node_support = popcount_row_bits(support_bits, row_off, words_per_row);
            support_sizes[static_cast<std::size_t>(node_id)] = node_support;

            BigInt count(0);
            for (int child : node.children) {
                int child_support = support_sizes[static_cast<std::size_t>(child)];
                if (child_support > node_support) {
                    throw std::runtime_error("Model counting failed: child support larger than OR support");
                }
                BigInt term = model_counts[static_cast<std::size_t>(child)];
                term <<= (node_support - child_support);
                count += std::move(term);
            }
            model_counts[static_cast<std::size_t>(node_id)] = std::move(count);
        } else {
            throw std::runtime_error("Model counting failed: unknown node kind");
        }

        for (int parent : parents[static_cast<std::size_t>(node_id)]) {
            int& pending = pending_children[static_cast<std::size_t>(parent)];
            pending -= 1;
            if (pending == 0) {
                ready.push_back(parent);
            }
        }
    }

    if (processed != reachable_count) {
        throw std::runtime_error("Model counting failed: cycle detected in circuit DAG");
    }

    int root_support = support_sizes[static_cast<std::size_t>(circuit.root)];
    if (root_support > atom_universe_size) {
        throw std::runtime_error("Model counting failed: root support exceeds atom universe");
    }

    BigInt out = model_counts[static_cast<std::size_t>(circuit.root)];
    out <<= (atom_universe_size - root_support);
    return out;
}

static std::unique_ptr<SatSolver> new_solver_from_clauses(
    int num_vars,
    const std::vector<std::vector<int>>& clauses
) {
    auto solver = std::make_unique<SatSolver>(num_vars);
    for (const auto& clause : clauses) {
        solver->add_clause(clause);
    }
    return solver;
}

static DnnfTseitinEncoding build_dnnf_tseitin_encoding(
    const CompiledCircuit& circuit,
    const std::unordered_map<int, int>& atom_sid_to_var
) {
    DnnfTseitinEncoding out;

    int next_var = 1;
    for (const auto& kv : atom_sid_to_var) {
        next_var = std::max(next_var, kv.second + 1);
    }

    std::unordered_map<int, int> node_var;
    std::vector<int> node_ids;
    node_ids.reserve(circuit.nodes.size());
    for (std::size_t node_id = 0; node_id < circuit.nodes.size(); ++node_id) {
        if (circuit.is_alive(static_cast<int>(node_id))) {
            node_ids.push_back(static_cast<int>(node_id));
        }
    }

    for (int node_id : node_ids) {
        node_var[node_id] = next_var;
        ++next_var;
    }
    out.num_vars = next_var - 1;

    auto root_it = node_var.find(circuit.root);
    if (root_it == node_var.end()) {
        throw std::runtime_error("DNNF Tseitin encoding failed: root node not found");
    }
    out.root_var = root_it->second;

    for (int node_id : node_ids) {
        if (!circuit.is_alive(node_id)) {
            throw std::runtime_error("DNNF Tseitin encoding failed: unknown node id");
        }
        const CircuitNode& node = circuit.nodes[static_cast<std::size_t>(node_id)];
        int nvar = node_var.at(node_id);

        if (node.kind == CircuitNode::Kind::TRUE_NODE) {
            out.clauses.push_back({nvar});
            continue;
        }
        if (node.kind == CircuitNode::Kind::FALSE_NODE) {
            out.clauses.push_back({-nvar});
            continue;
        }
        if (node.kind == CircuitNode::Kind::LIT) {
            auto atom_it = atom_sid_to_var.find(node.atom_sid);
            if (atom_it == atom_sid_to_var.end()) {
                throw std::runtime_error("DNNF Tseitin encoding failed: literal atom missing in atom universe");
            }
            int avar = atom_it->second;
            int lit = node.positive ? avar : -avar;
            out.clauses.push_back({-nvar, lit});
            out.clauses.push_back({nvar, -lit});
            continue;
        }

        std::vector<int> child_vars;
        child_vars.reserve(node.children.size());
        for (int child_id : node.children) {
            if (!circuit.is_alive(child_id)) {
                throw std::runtime_error("DNNF Tseitin encoding failed: child node not alive");
            }
            auto child_it = node_var.find(child_id);
            if (child_it == node_var.end()) {
                throw std::runtime_error("DNNF Tseitin encoding failed: child node not found");
            }
            child_vars.push_back(child_it->second);
        }

        if (node.kind == CircuitNode::Kind::AND) {
            for (int cvar : child_vars) {
                out.clauses.push_back({-nvar, cvar});
            }
            std::vector<int> backward;
            backward.reserve(1 + child_vars.size());
            backward.push_back(nvar);
            for (int cvar : child_vars) {
                backward.push_back(-cvar);
            }
            out.clauses.push_back(std::move(backward));
            continue;
        }

        if (node.kind == CircuitNode::Kind::OR) {
            std::vector<int> forward;
            forward.reserve(1 + child_vars.size());
            forward.push_back(-nvar);
            forward.insert(forward.end(), child_vars.begin(), child_vars.end());
            out.clauses.push_back(std::move(forward));
            for (int cvar : child_vars) {
                out.clauses.push_back({-cvar, nvar});
            }
            continue;
        }

        throw std::runtime_error("DNNF Tseitin encoding failed: unknown node kind");
    }

    out.clauses.push_back({out.root_var});
    return out;
}

static std::vector<int> model_to_atom_assignment(
    const SatSolver& solver,
    const std::vector<int>& atom_var_order
) {
    std::vector<int> out;
    out.reserve(atom_var_order.size());
    for (int var : atom_var_order) {
        out.push_back(solver.model_lit(var));
    }
    return out;
}

static bool evaluate_circuit(
    const CompiledCircuit& circuit,
    const std::unordered_map<int, int>& atom_sid_to_var,
    const std::vector<int>& atom_assignment
) {
    std::vector<int8_t> atom_values(atom_assignment.size() + 1, -1);
    for (int lit : atom_assignment) {
        int var = std::abs(lit);
        if (var <= 0 || static_cast<std::size_t>(var) >= atom_values.size()) {
            throw std::runtime_error("evaluate_circuit: atom assignment var out of range");
        }
        atom_values[static_cast<std::size_t>(var)] = (lit > 0) ? 1 : 0;
    }

    std::unordered_map<int, bool> memo;
    memo.reserve(circuit.nodes.size());

    std::function<bool(int)> eval = [&](int node_id) -> bool {
        auto memo_it = memo.find(node_id);
        if (memo_it != memo.end()) {
            return memo_it->second;
        }

        if (!circuit.is_alive(node_id)) {
            throw std::runtime_error("evaluate_circuit: node id not found");
        }
        const CircuitNode& node = circuit.nodes[static_cast<std::size_t>(node_id)];

        bool value = false;
        if (node.kind == CircuitNode::Kind::TRUE_NODE) {
            value = true;
        } else if (node.kind == CircuitNode::Kind::FALSE_NODE) {
            value = false;
        } else if (node.kind == CircuitNode::Kind::LIT) {
            auto atom_it = atom_sid_to_var.find(node.atom_sid);
            if (atom_it == atom_sid_to_var.end()) {
                throw std::runtime_error("evaluate_circuit: missing atom value");
            }
            int var = atom_it->second;
            bool atom_value = false;
            if (var > 0 && static_cast<std::size_t>(var) < atom_values.size()) {
                atom_value = atom_values[static_cast<std::size_t>(var)] == 1;
            }
            value = node.positive ? atom_value : !atom_value;
        } else if (node.kind == CircuitNode::Kind::AND) {
            value = true;
            for (int child : node.children) {
                if (!eval(child)) {
                    value = false;
                    break;
                }
            }
        } else if (node.kind == CircuitNode::Kind::OR) {
            value = false;
            for (int child : node.children) {
                if (eval(child)) {
                    value = true;
                    break;
                }
            }
        } else {
            throw std::runtime_error("evaluate_circuit: unknown node kind");
        }

        memo[node_id] = value;
        return value;
    };

    return eval(circuit.root);
}

static std::string format_atom_assignment(
    const std::vector<int>& atom_assignment,
    const std::unordered_map<int, int>& var_to_atom_sid,
    const fo2::InternTable& interner,
    std::size_t max_atoms = 30,
    bool true_only = false
) {
    std::vector<std::string> items;
    items.reserve(atom_assignment.size());
    for (int lit : atom_assignment) {
        if (true_only && lit <= 0) {
            continue;
        }
        int var = std::abs(lit);
        auto it = var_to_atom_sid.find(var);
        if (it == var_to_atom_sid.end()) {
            continue;
        }
        const std::string& atom = interner.str(it->second);
        items.push_back((lit > 0 ? "" : "~") + atom);
    }

    std::ostringstream oss;
    std::size_t shown = (max_atoms == 0) ? items.size() : std::min(max_atoms, items.size());
    for (std::size_t i = 0; i < shown; ++i) {
        if (i != 0) {
            oss << " & ";
        }
        oss << items[i];
    }
    if (max_atoms != 0 && items.size() > shown) {
        if (shown != 0) {
            oss << " & ";
        }
        oss << "... (" << (items.size() - shown) << " more)";
    }
    return oss.str();
}

static VerificationResult verify_circuit_by_enumeration(
    const fo2::TypeSystemId& spec,
    const CompiledCircuit& circuit,
    int domain_size,
    fo2::InternTable& interner,
    int max_sat_models,
    int max_dnnf_models
) {
    OriginalFormulaEncoding original = build_original_formula_encoding(spec, domain_size, interner);
    DnnfTseitinEncoding dnnf = build_dnnf_tseitin_encoding(circuit, original.atom_sid_to_var);
    VerificationStats stats;

    auto sat_enum_solver = new_solver_from_clauses(original.num_vars, original.clauses);
    std::unordered_set<std::vector<int>, VectorIntHash> seen_sat;
    while (sat_enum_solver->solve()) {
        stats.sat_raw_models += 1;
        std::vector<int> atom_assignment = model_to_atom_assignment(*sat_enum_solver, original.atom_var_order);
        sat_enum_solver->add_clause(sat_enum_solver->model_blocking_clause());

        if (!seen_sat.insert(atom_assignment).second) {
            continue;
        }
        stats.sat_unique_atom_models += 1;

        if (!evaluate_circuit(circuit, original.atom_sid_to_var, atom_assignment)) {
            return VerificationResult{
                false,
                stats,
                "Counterexample (SAT -> d-DNNF): SAT formula has a model that does not satisfy the compiled d-DNNF.\n"
                "Model: " + format_atom_assignment(
                    atom_assignment,
                    original.var_to_atom_sid,
                    interner,
                    /*max_atoms=*/0,
                    /*true_only=*/true
                )
            };
        }

        if (max_sat_models > 0 && static_cast<int>(stats.sat_unique_atom_models) >= max_sat_models) {
            stats.sat_enum_truncated = true;
            break;
        }
    }

    auto dnnf_enum_solver = new_solver_from_clauses(dnnf.num_vars, dnnf.clauses);
    auto sat_check_solver = new_solver_from_clauses(original.num_vars, original.clauses);
    std::unordered_set<std::vector<int>, VectorIntHash> seen_dnnf;
    while (dnnf_enum_solver->solve()) {
        stats.dnnf_raw_models += 1;
        std::vector<int> atom_assignment = model_to_atom_assignment(*dnnf_enum_solver, original.atom_var_order);
        dnnf_enum_solver->add_clause(dnnf_enum_solver->model_blocking_clause());

        if (!seen_dnnf.insert(atom_assignment).second) {
            continue;
        }
        stats.dnnf_unique_atom_models += 1;

        if (!sat_check_solver->solve(atom_assignment)) {
            return VerificationResult{
                false,
                stats,
                "Counterexample (d-DNNF -> SAT): compiled d-DNNF has a model that does not satisfy the SAT formula.\n"
                "Model: " + format_atom_assignment(
                    atom_assignment,
                    original.var_to_atom_sid,
                    interner,
                    /*max_atoms=*/0,
                    /*true_only=*/true
                )
            };
        }

        if (max_dnnf_models > 0 && static_cast<int>(stats.dnnf_unique_atom_models) >= max_dnnf_models) {
            stats.dnnf_enum_truncated = true;
            break;
        }
    }

    if (stats.sat_enum_truncated || stats.dnnf_enum_truncated) {
        return VerificationResult{
            true,
            stats,
            "No counterexample found within model limits (verification was truncated; not a complete proof)."
        };
    }

    return VerificationResult{
        true,
        stats,
        "Bidirectional model-enumeration check passed."
    };
}

#include "compiler_entry.hpp"
