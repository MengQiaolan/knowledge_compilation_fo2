struct ParsedBinaryAtomTemplate {
    int predicate_sid = -1;
    int dir = -1;  // 0: (x,y), 1: (y,x)
};

static std::optional<ParsedBinaryAtomTemplate> parse_binary_atom_template_sid(
    int atom_sid,
    fo2::InternTable& interner
) {
    const std::string& atom = interner.str(atom_sid);
    std::size_t lpar = atom.find('(');
    std::size_t rpar = atom.rfind(')');
    if (lpar == std::string::npos || rpar == std::string::npos || rpar <= lpar) {
        return std::nullopt;
    }
    std::string pred = trim_ascii(atom.substr(0, lpar));
    if (pred.empty()) {
        return std::nullopt;
    }
    std::string args = atom.substr(lpar + 1, rpar - lpar - 1);
    std::size_t comma = args.find(',');
    if (comma == std::string::npos) {
        return std::nullopt;
    }
    std::string a1 = trim_ascii(args.substr(0, comma));
    std::string a2 = trim_ascii(args.substr(comma + 1));
    int dir = -1;
    if (a1 == "x" && a2 == "y") {
        dir = 0;
    } else if (a1 == "y" && a2 == "x") {
        dir = 1;
    } else {
        return std::nullopt;
    }
    return ParsedBinaryAtomTemplate{interner.intern(pred), dir};
}

struct PredBitState {
    int8_t xy = -1;  // -1 unknown, 0 false, 1 true
    int8_t yx = -1;

    bool operator==(const PredBitState& other) const noexcept {
        return xy == other.xy && yx == other.yx;
    }
};

static int encode_pred_state(const PredBitState& s) {
    return (static_cast<int>(s.xy) + 1) * 3 + (static_cast<int>(s.yx) + 1);
}

static PredBitState decode_pred_state(int code) {
    PredBitState out;
    out.xy = static_cast<int8_t>(code / 3 - 1);
    out.yx = static_cast<int8_t>(code % 3 - 1);
    return out;
}

struct ProjBinaryKey {
    std::vector<int> pred_state_codes;
    std::vector<int> sat_left;
    std::vector<int> sat_right;

    bool operator==(const ProjBinaryKey& other) const noexcept {
        return pred_state_codes == other.pred_state_codes &&
               sat_left == other.sat_left &&
               sat_right == other.sat_right;
    }
};

struct ProjBinaryKeyHash {
    std::size_t operator()(const ProjBinaryKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.pred_state_codes.size());
        for (int v : k.pred_state_codes) {
            hash_combine(seed, v);
        }
        hash_combine(seed, k.sat_left.size());
        for (int v : k.sat_left) {
            hash_combine(seed, v);
        }
        hash_combine(seed, k.sat_right.size());
        for (int v : k.sat_right) {
            hash_combine(seed, v);
        }
        return seed;
    }
};

class Dsu {
public:
    explicit Dsu(int n) : parent_(static_cast<std::size_t>(n)), rank_(static_cast<std::size_t>(n), 0) {
        for (int i = 0; i < n; ++i) {
            parent_[static_cast<std::size_t>(i)] = i;
        }
    }

    int find(int x) {
        int& p = parent_[static_cast<std::size_t>(x)];
        if (p != x) {
            p = find(p);
        }
        return p;
    }

    void unite(int a, int b) {
        int ra = find(a);
        int rb = find(b);
        if (ra == rb) {
            return;
        }
        int& rra = rank_[static_cast<std::size_t>(ra)];
        int& rrb = rank_[static_cast<std::size_t>(rb)];
        if (rra < rrb) {
            std::swap(ra, rb);
        }
        parent_[static_cast<std::size_t>(rb)] = ra;
        if (rra == rrb) {
            rra += 1;
        }
    }

private:
    std::vector<int> parent_;
    std::vector<int> rank_;
};

static std::optional<AuxUnaryParsed> parse_aux_unary_name(
    int aux_name_sid,
    const fo2::TypeSystemId& spec,
    const std::unordered_map<std::string, int>& base_name_to_idx,
    const fo2::InternTable& interner
) {
    const std::string& name = interner.str(aux_name_sid);
    std::size_t last_dot = name.rfind('.');
    if (last_dot == std::string::npos) {
        return std::nullopt;
    }
    std::size_t second_dot = name.rfind('.', last_dot - 1);
    if (second_dot == std::string::npos) {
        return std::nullopt;
    }
    std::string base_name = name.substr(0, second_dot);
    std::string role_s = name.substr(second_dot + 1, last_dot - second_dot - 1);
    std::string mask_s = name.substr(last_dot + 1);

    auto b_it = base_name_to_idx.find(base_name);
    if (b_it == base_name_to_idx.end()) {
        return std::nullopt;
    }

    std::optional<int> role = aux_role_from_string(role_s);
    if (!role.has_value()) {
        return std::nullopt;
    }

    std::size_t parsed = 0;
    int sat_mask = 0;
    try {
        sat_mask = std::stoi(mask_s, &parsed);
    } catch (...) {
        return std::nullopt;
    }
    if (parsed != mask_s.size() || sat_mask < 0) {
        return std::nullopt;
    }

    if (b_it->second < 0 || b_it->second >= spec.unary_count()) {
        return std::nullopt;
    }

    return AuxUnaryParsed{b_it->second, *role, sat_mask};
}

static int project_mask(
    int global_mask,
    const std::vector<int>& global_constraint_to_local
) {
    int local_mask = 0;
    for (int g = 0; g < static_cast<int>(global_constraint_to_local.size()); ++g) {
        int local = global_constraint_to_local[static_cast<std::size_t>(g)];
        if (local < 0) {
            continue;
        }
        if ((global_mask & (1 << g)) != 0) {
            local_mask |= (1 << local);
        }
    }
    return local_mask;
}

static std::string aux_role_name(int role) {
    if (role == kAuxTarget) {
        return "target";
    }
    if (role == kAuxDone) {
        return "done";
    }
    if (role == kAuxTodo) {
        return "todo";
    }
    return "unknown";
}

static std::vector<std::unordered_map<int, PredBitState>> build_binary_pred_states(
    const fo2::TypeSystemId& spec,
    fo2::InternTable& interner
) {
    std::vector<std::unordered_map<int, PredBitState>> out(
        static_cast<std::size_t>(spec.binary_count())
    );
    for (int bidx = 0; bidx < spec.binary_count(); ++bidx) {
        const auto& bt = spec.binary_types[static_cast<std::size_t>(bidx)];
        auto& row = out[static_cast<std::size_t>(bidx)];
        for (const auto& lit : bt.literals) {
            auto parsed = parse_binary_atom_template_sid(lit.first, interner);
            if (!parsed.has_value()) {
                continue;
            }
            auto& state = row[parsed->predicate_sid];
            int8_t v = lit.second ? 1 : 0;
            if (parsed->dir == 0) {
                if (state.xy != -1 && state.xy != v) {
                    throw std::runtime_error("Conflicting binary literal assignment on (x,y)");
                }
                state.xy = v;
            } else {
                if (state.yx != -1 && state.yx != v) {
                    throw std::runtime_error("Conflicting binary literal assignment on (y,x)");
                }
                state.yx = v;
            }
        }
    }
    return out;
}

static std::vector<int> projection_key_for_component(
    int bidx,
    const std::vector<int>& pred_sids,
    const std::vector<std::unordered_map<int, PredBitState>>& b_pred_states
) {
    std::vector<int> key;
    key.reserve(pred_sids.size());
    const auto& row = b_pred_states[static_cast<std::size_t>(bidx)];
    for (int pred_sid : pred_sids) {
        auto it = row.find(pred_sid);
        if (it == row.end()) {
            key.push_back(encode_pred_state(PredBitState{}));
        } else {
            key.push_back(encode_pred_state(it->second));
        }
    }
    return key;
}

struct ComponentAuxBuildResult {
    bool ok = false;
    fo2::TypeSystemId component_aux;
    std::string error;
};

struct ComponentMainBuildResult {
    bool ok = false;
    fo2::TypeSystemId component_main;
    std::vector<int> main_bidx_to_proj;
    std::string error;
};

static ComponentMainBuildResult build_component_main_spec(
    const fo2::TypeSystemId& spec,
    fo2::InternTable& interner,
    int component_id,
    const std::vector<int>& component_pred_sids,
    const std::vector<int>& component_constraint_indices,
    const std::vector<std::unordered_map<int, PredBitState>>& b_pred_states
) {
    ComponentMainBuildResult out;

    std::vector<int> global_to_local_constraint(static_cast<std::size_t>(spec.existential_count()), -1);
    for (int i = 0; i < static_cast<int>(component_constraint_indices.size()); ++i) {
        int g = component_constraint_indices[static_cast<std::size_t>(i)];
        global_to_local_constraint[static_cast<std::size_t>(g)] = i;
    }

    fo2::TypeSystemId comp;
    comp.existential_constraint_sids.reserve(component_constraint_indices.size());
    for (int g : component_constraint_indices) {
        comp.existential_constraint_sids.push_back(spec.existential_constraint_sids[static_cast<std::size_t>(g)]);
    }

    for (int uidx = 0; uidx < spec.unary_count(); ++uidx) {
        const auto& src_u = spec.unary_types[static_cast<std::size_t>(uidx)];
        fo2::UnaryTypeId dst_u;
        dst_u.name_sid = src_u.name_sid;
        dst_u.sat_bound = src_u.sat_bound;

        dst_u.literals = src_u.literals;

        dst_u.satisfies_self.clear();
        for (int g : src_u.satisfies_self) {
            int local = global_to_local_constraint[static_cast<std::size_t>(g)];
            if (local >= 0) {
                dst_u.satisfies_self.push_back(local);
            }
        }
        dst_u.satisfies_self = canonicalize_ints(std::move(dst_u.satisfies_self));

        int idx = static_cast<int>(comp.unary_types.size());
        if (!comp.unary_sid_to_idx.emplace(dst_u.name_sid, idx).second) {
            out.error = "Duplicate unary name while building component-main";
            return out;
        }
        comp.unary_name_sids.push_back(dst_u.name_sid);
        comp.unary_types.push_back(std::move(dst_u));
    }

    std::unordered_map<ProjBinaryKey, int, ProjBinaryKeyHash> key_to_proj_bidx;
    out.main_bidx_to_proj.assign(static_cast<std::size_t>(spec.binary_count()), -1);

    for (int bidx = 0; bidx < spec.binary_count(); ++bidx) {
        ProjBinaryKey key;
        key.pred_state_codes = projection_key_for_component(bidx, component_pred_sids, b_pred_states);

        const auto& bt = spec.binary_types[static_cast<std::size_t>(bidx)];
        for (int g : bt.satisfies_from_left) {
            int local = global_to_local_constraint[static_cast<std::size_t>(g)];
            if (local >= 0) {
                key.sat_left.push_back(local);
            }
        }
        for (int g : bt.satisfies_from_right) {
            int local = global_to_local_constraint[static_cast<std::size_t>(g)];
            if (local >= 0) {
                key.sat_right.push_back(local);
            }
        }
        key.sat_left = canonicalize_ints(std::move(key.sat_left));
        key.sat_right = canonicalize_ints(std::move(key.sat_right));

        auto it = key_to_proj_bidx.find(key);
        if (it != key_to_proj_bidx.end()) {
            out.main_bidx_to_proj[static_cast<std::size_t>(bidx)] = it->second;
            continue;
        }

        fo2::BinaryTypeId out_bt;
        out_bt.name_sid = interner.intern(
            "component" + std::to_string(component_id) + "_b" + std::to_string(static_cast<int>(comp.binary_types.size()))
        );
        out_bt.satisfies_from_left = key.sat_left;
        out_bt.satisfies_from_right = key.sat_right;

        for (std::size_t pidx = 0; pidx < component_pred_sids.size(); ++pidx) {
            int pred_sid = component_pred_sids[pidx];
            PredBitState st = decode_pred_state(key.pred_state_codes[pidx]);
            const std::string pred_name = interner.str(pred_sid);
            if (st.xy != -1) {
                int atom_sid = interner.intern(pred_name + "(x,y)");
                out_bt.literals.emplace_back(atom_sid, st.xy == 1);
            }
            if (st.yx != -1) {
                int atom_sid = interner.intern(pred_name + "(y,x)");
                out_bt.literals.emplace_back(atom_sid, st.yx == 1);
            }
        }
        std::sort(out_bt.literals.begin(), out_bt.literals.end());

        int new_idx = static_cast<int>(comp.binary_types.size());
        key_to_proj_bidx.emplace(std::move(key), new_idx);
        if (!comp.binary_sid_to_idx.emplace(out_bt.name_sid, new_idx).second) {
            out.error = "Duplicate binary name while building component-main";
            return out;
        }
        comp.binary_name_sids.push_back(out_bt.name_sid);
        comp.binary_types.push_back(std::move(out_bt));
        out.main_bidx_to_proj[static_cast<std::size_t>(bidx)] = new_idx;
    }

    const int u = comp.unary_count();
    comp.pair_binary_choices.assign(static_cast<std::size_t>(u * u), {});
    for (int left = 0; left < spec.unary_count(); ++left) {
        for (int right = 0; right < spec.unary_count(); ++right) {
            std::vector<int> cand;
            for (int bidx : spec.pair_choice_names(left, right)) {
                int projected = out.main_bidx_to_proj[static_cast<std::size_t>(bidx)];
                if (projected < 0) {
                    out.error = "Internal projection mapping missing while building component-main";
                    return out;
                }
                cand.push_back(projected);
            }
            comp.pair_binary_choices[static_cast<std::size_t>(unary_pair_slot(left, right, u))] =
                canonicalize_ints(std::move(cand));
        }
    }

    try {
        comp.validate();
    } catch (const std::exception& e) {
        out.error = "Projected component-main validation failed: " + std::string(e.what());
        return out;
    }

    out.ok = true;
    out.component_main = std::move(comp);
    return out;
}

static ComponentAuxBuildResult build_component_aux_spec(
    const fo2::TypeSystemId& spec,
    const fo2::TypeSystemId& aux_spec,
    fo2::InternTable& interner,
    int component_id,
    const std::vector<int>& component_pred_sids,
    const std::vector<int>& component_constraint_indices,
    const std::vector<std::unordered_map<int, PredBitState>>& b_pred_states
) {
    ComponentAuxBuildResult out;

    std::vector<int> global_to_local_constraint(static_cast<std::size_t>(spec.existential_count()), -1);
    for (int i = 0; i < static_cast<int>(component_constraint_indices.size()); ++i) {
        int g = component_constraint_indices[static_cast<std::size_t>(i)];
        global_to_local_constraint[static_cast<std::size_t>(g)] = i;
    }
    const int local_m = static_cast<int>(component_constraint_indices.size());
    const int local_mask_count = (local_m == 0) ? 1 : (1 << local_m);

    fo2::TypeSystemId comp;
    comp.existential_constraint_sids.reserve(component_constraint_indices.size());
    for (int g : component_constraint_indices) {
        comp.existential_constraint_sids.push_back(spec.existential_constraint_sids[static_cast<std::size_t>(g)]);
    }

    std::unordered_map<std::string, int> base_name_to_idx;
    for (int u = 0; u < spec.unary_count(); ++u) {
        base_name_to_idx.emplace(interner.str(spec.unary_name_sids[static_cast<std::size_t>(u)]), u);
    }

    std::vector<AuxUnaryParsed> parsed_aux_unary(aux_spec.unary_count());
    for (int idx = 0; idx < aux_spec.unary_count(); ++idx) {
        auto parsed = parse_aux_unary_name(
            aux_spec.unary_name_sids[static_cast<std::size_t>(idx)],
            spec,
            base_name_to_idx,
            interner
        );
        if (!parsed.has_value()) {
            out.error = "Invalid aux unary naming in source aux spec while building component-aux";
            return out;
        }
        parsed_aux_unary[static_cast<std::size_t>(idx)] = *parsed;
    }

    struct BoundKey {
        int base_u_idx = -1;
        int role = -1;
        int local_mask = 0;
        bool operator==(const BoundKey& other) const noexcept {
            return base_u_idx == other.base_u_idx &&
                   role == other.role &&
                   local_mask == other.local_mask;
        }
    };
    struct BoundKeyHash {
        std::size_t operator()(const BoundKey& k) const noexcept {
            std::size_t seed = 0;
            hash_combine(seed, k.base_u_idx);
            hash_combine(seed, k.role);
            hash_combine(seed, k.local_mask);
            return seed;
        }
    };

    std::unordered_map<BoundKey, int, BoundKeyHash> projected_sat_bound;
    for (int idx = 0; idx < aux_spec.unary_count(); ++idx) {
        const auto& pu = parsed_aux_unary[static_cast<std::size_t>(idx)];
        int local_mask = project_mask(pu.sat_mask, global_to_local_constraint);
        BoundKey key{pu.base_u_idx, pu.role, local_mask};
        int sat_bound = aux_spec.unary_types[static_cast<std::size_t>(idx)].sat_bound.value_or(0);
        auto it = projected_sat_bound.find(key);
        if (it == projected_sat_bound.end()) {
            projected_sat_bound.emplace(key, sat_bound);
        } else {
            it->second = std::max(it->second, sat_bound);
        }
    }

    const std::vector<int> roles = {kAuxTarget, kAuxDone, kAuxTodo};
    for (int role : roles) {
        for (int base_u = 0; base_u < spec.unary_count(); ++base_u) {
            const std::string base_name = interner.str(spec.unary_name_sids[static_cast<std::size_t>(base_u)]);
            for (int local_mask = 0; local_mask < local_mask_count; ++local_mask) {
                fo2::UnaryTypeId ut;
                ut.name_sid = interner.intern(base_name + "." + aux_role_name(role) + "." + std::to_string(local_mask));
                ut.sat_bound = 0;

                std::vector<int> sat_self;
                for (int bit = 0; bit < local_m; ++bit) {
                    if ((local_mask & (1 << bit)) != 0) {
                        sat_self.push_back(bit);
                    }
                }
                ut.satisfies_self = std::move(sat_self);

                BoundKey key{base_u, role, local_mask};
                auto it = projected_sat_bound.find(key);
                if (it != projected_sat_bound.end()) {
                    ut.sat_bound = it->second;
                } else {
                    ut.sat_bound = (role == kAuxTarget) ? 1 : 2;
                }

                int idx = static_cast<int>(comp.unary_types.size());
                if (!comp.unary_sid_to_idx.emplace(ut.name_sid, idx).second) {
                    out.error = "Duplicate unary name while building component-aux";
                    return out;
                }
                comp.unary_name_sids.push_back(ut.name_sid);
                comp.unary_types.push_back(std::move(ut));
            }
        }
    }

    int aux_fool_idx = -1;
    for (int bidx = 0; bidx < aux_spec.binary_count(); ++bidx) {
        if (interner.str(aux_spec.binary_name_sids[static_cast<std::size_t>(bidx)]) == "fool") {
            aux_fool_idx = bidx;
            break;
        }
    }

    int projected_fool_idx = -1;
    if (aux_fool_idx >= 0) {
        fo2::BinaryTypeId bt;
        bt.name_sid = aux_spec.binary_name_sids[static_cast<std::size_t>(aux_fool_idx)];
        int idx = static_cast<int>(comp.binary_types.size());
        comp.binary_sid_to_idx.emplace(bt.name_sid, idx);
        comp.binary_name_sids.push_back(bt.name_sid);
        comp.binary_types.push_back(std::move(bt));
        projected_fool_idx = idx;
    }

    std::unordered_map<ProjBinaryKey, int, ProjBinaryKeyHash> key_to_proj_bidx;
    std::vector<int> main_bidx_to_proj(spec.binary_count(), -1);

    for (int bidx = 0; bidx < spec.binary_count(); ++bidx) {
        ProjBinaryKey key;
        key.pred_state_codes = projection_key_for_component(bidx, component_pred_sids, b_pred_states);

        const auto& bt = spec.binary_types[static_cast<std::size_t>(bidx)];
        for (int g : bt.satisfies_from_left) {
            int local = global_to_local_constraint[static_cast<std::size_t>(g)];
            if (local >= 0) {
                key.sat_left.push_back(local);
            }
        }
        for (int g : bt.satisfies_from_right) {
            int local = global_to_local_constraint[static_cast<std::size_t>(g)];
            if (local >= 0) {
                key.sat_right.push_back(local);
            }
        }
        key.sat_left = canonicalize_ints(std::move(key.sat_left));
        key.sat_right = canonicalize_ints(std::move(key.sat_right));

        auto it = key_to_proj_bidx.find(key);
        if (it != key_to_proj_bidx.end()) {
            main_bidx_to_proj[static_cast<std::size_t>(bidx)] = it->second;
            continue;
        }

        fo2::BinaryTypeId out_bt;
        out_bt.name_sid = interner.intern(
            "component" + std::to_string(component_id) + "_b" + std::to_string(static_cast<int>(comp.binary_types.size()))
        );
        out_bt.satisfies_from_left = key.sat_left;
        out_bt.satisfies_from_right = key.sat_right;

        for (std::size_t pidx = 0; pidx < component_pred_sids.size(); ++pidx) {
            int pred_sid = component_pred_sids[pidx];
            PredBitState st = decode_pred_state(key.pred_state_codes[pidx]);
            const std::string pred_name = interner.str(pred_sid);
            if (st.xy != -1) {
                int atom_sid = interner.intern(pred_name + "(x,y)");
                out_bt.literals.emplace_back(atom_sid, st.xy == 1);
            }
            if (st.yx != -1) {
                int atom_sid = interner.intern(pred_name + "(y,x)");
                out_bt.literals.emplace_back(atom_sid, st.yx == 1);
            }
        }
        std::sort(out_bt.literals.begin(), out_bt.literals.end());

        int new_idx = static_cast<int>(comp.binary_types.size());
        key_to_proj_bidx.emplace(std::move(key), new_idx);
        if (!comp.binary_sid_to_idx.emplace(out_bt.name_sid, new_idx).second) {
            out.error = "Duplicate binary name while building component-aux";
            return out;
        }
        comp.binary_name_sids.push_back(out_bt.name_sid);
        comp.binary_types.push_back(std::move(out_bt));
        main_bidx_to_proj[static_cast<std::size_t>(bidx)] = new_idx;
    }

    std::vector<int> aux_binary_to_component(aux_spec.binary_count(), -1);
    for (int aux_bidx = 0; aux_bidx < aux_spec.binary_count(); ++aux_bidx) {
        int sid = aux_spec.binary_name_sids[static_cast<std::size_t>(aux_bidx)];
        const std::string& bname = interner.str(sid);
        if (aux_bidx == aux_fool_idx || bname == "fool") {
            if (projected_fool_idx < 0) {
                fo2::BinaryTypeId bt;
                bt.name_sid = interner.intern("fool");
                projected_fool_idx = static_cast<int>(comp.binary_types.size());
                comp.binary_sid_to_idx.emplace(bt.name_sid, projected_fool_idx);
                comp.binary_name_sids.push_back(bt.name_sid);
                comp.binary_types.push_back(std::move(bt));
            }
            aux_binary_to_component[static_cast<std::size_t>(aux_bidx)] = projected_fool_idx;
            continue;
        }
        auto it_main = spec.binary_sid_to_idx.find(sid);
        if (it_main == spec.binary_sid_to_idx.end()) {
            out.error = "Aux binary type '" + bname + "' not found in main spec binary pool";
            return out;
        }
        int mapped = main_bidx_to_proj[static_cast<std::size_t>(it_main->second)];
        if (mapped < 0) {
            out.error = "Internal mapping failure while projecting aux binary candidates";
            return out;
        }
        aux_binary_to_component[static_cast<std::size_t>(aux_bidx)] = mapped;
    }

    std::vector<int> aux_unary_to_component(aux_spec.unary_count(), -1);
    for (int aux_uidx = 0; aux_uidx < aux_spec.unary_count(); ++aux_uidx) {
        const auto& pu = parsed_aux_unary[static_cast<std::size_t>(aux_uidx)];
        int local_mask = project_mask(pu.sat_mask, global_to_local_constraint);
        const std::string base_name = interner.str(spec.unary_name_sids[static_cast<std::size_t>(pu.base_u_idx)]);
        int sid = interner.intern(base_name + "." + aux_role_name(pu.role) + "." + std::to_string(local_mask));
        auto it = comp.unary_sid_to_idx.find(sid);
        if (it == comp.unary_sid_to_idx.end()) {
            out.error = "Internal mapping failure while projecting aux unary candidates";
            return out;
        }
        aux_unary_to_component[static_cast<std::size_t>(aux_uidx)] = it->second;
    }

    const int cu = comp.unary_count();
    comp.pair_binary_choices.assign(static_cast<std::size_t>(cu * cu), {});
    bool pair_conflict = false;
    for (int left = 0; left < aux_spec.unary_count(); ++left) {
        for (int right = 0; right < aux_spec.unary_count(); ++right) {
            int new_left = aux_unary_to_component[static_cast<std::size_t>(left)];
            int new_right = aux_unary_to_component[static_cast<std::size_t>(right)];
            int slot = unary_pair_slot(new_left, new_right, cu);
            std::vector<int> projected;
            for (int old_bidx : aux_spec.pair_choice_names(left, right)) {
                int mapped = aux_binary_to_component[static_cast<std::size_t>(old_bidx)];
                if (mapped < 0) {
                    out.error = "Internal mapping failure for aux pair binary choices";
                    return out;
                }
                projected.push_back(mapped);
            }
            projected = canonicalize_ints(std::move(projected));

            auto& existing = comp.pair_binary_choices[static_cast<std::size_t>(slot)];
            if (existing.empty()) {
                existing = projected;
            } else if (existing != projected) {
                pair_conflict = true;
            }
        }
    }

    if (pair_conflict) {
        out.error = "Projected aux pair choices conflict after collapsing global masks; independence projection is invalid";
        return out;
    }
    for (int left = 0; left < cu; ++left) {
        for (int right = 0; right < cu; ++right) {
            if (comp.pair_choice_names(left, right).empty()) {
                out.error = "Projected aux pair choices are incomplete";
                return out;
            }
        }
    }

    try {
        comp.validate();
    } catch (const std::exception& e) {
        out.error = "Projected component-aux validation failed: " + std::string(e.what());
        return out;
    }

    out.ok = true;
    out.component_aux = std::move(comp);
    return out;
}

static void write_typesystem_json(
    const fo2::TypeSystemId& spec,
    const fo2::InternTable& interner,
    const fs::path& out_path
) {
    std::ofstream ofs(out_path);
    if (!ofs) {
        throw std::runtime_error("Cannot open file for writing: " + out_path.string());
    }

    ofs << "{\n";

    ofs << "  \"existential_constraints\": [";
    for (std::size_t i = 0; i < spec.existential_constraint_sids.size(); ++i) {
        if (i != 0) {
            ofs << ", ";
        }
        ofs << "\"" << json_escape(interner.str(spec.existential_constraint_sids[i])) << "\"";
    }
    ofs << "],\n";

    ofs << "  \"unary_types\": [\n";
    for (std::size_t i = 0; i < spec.unary_types.size(); ++i) {
        const auto& ut = spec.unary_types[i];
        ofs << "    {\n";
        ofs << "      \"name\": \"" << json_escape(interner.str(ut.name_sid)) << "\",\n";
        ofs << "      \"literals\": {";
        for (std::size_t j = 0; j < ut.literals.size(); ++j) {
            if (j != 0) {
                ofs << ", ";
            }
            ofs << "\"" << json_escape(interner.str(ut.literals[j].first)) << "\": "
                << (ut.literals[j].second ? "true" : "false");
        }
        ofs << "},\n";
        ofs << "      \"satisfies_self\": [";
        for (std::size_t j = 0; j < ut.satisfies_self.size(); ++j) {
            if (j != 0) {
                ofs << ", ";
            }
            int cidx = ut.satisfies_self[j];
            ofs << "\"" << json_escape(interner.str(spec.existential_constraint_sids[static_cast<std::size_t>(cidx)])) << "\"";
        }
        ofs << "],\n";
        ofs << "      \"sat_bound\": ";
        if (ut.sat_bound.has_value()) {
            ofs << *ut.sat_bound;
        } else {
            ofs << "null";
        }
        ofs << "\n";
        ofs << "    }";
        if (i + 1 != spec.unary_types.size()) {
            ofs << ",";
        }
        ofs << "\n";
    }
    ofs << "  ],\n";

    ofs << "  \"binary_types\": [\n";
    for (std::size_t i = 0; i < spec.binary_types.size(); ++i) {
        const auto& bt = spec.binary_types[i];
        ofs << "    {\n";
        ofs << "      \"name\": \"" << json_escape(interner.str(bt.name_sid)) << "\",\n";
        ofs << "      \"literals\": {";
        for (std::size_t j = 0; j < bt.literals.size(); ++j) {
            if (j != 0) {
                ofs << ", ";
            }
            ofs << "\"" << json_escape(interner.str(bt.literals[j].first)) << "\": "
                << (bt.literals[j].second ? "true" : "false");
        }
        ofs << "},\n";
        ofs << "      \"satisfies_from_left\": [";
        for (std::size_t j = 0; j < bt.satisfies_from_left.size(); ++j) {
            if (j != 0) {
                ofs << ", ";
            }
            int cidx = bt.satisfies_from_left[j];
            ofs << "\"" << json_escape(interner.str(spec.existential_constraint_sids[static_cast<std::size_t>(cidx)])) << "\"";
        }
        ofs << "],\n";
        ofs << "      \"satisfies_from_right\": [";
        for (std::size_t j = 0; j < bt.satisfies_from_right.size(); ++j) {
            if (j != 0) {
                ofs << ", ";
            }
            int cidx = bt.satisfies_from_right[j];
            ofs << "\"" << json_escape(interner.str(spec.existential_constraint_sids[static_cast<std::size_t>(cidx)])) << "\"";
        }
        ofs << "]\n";
        ofs << "    }";
        if (i + 1 != spec.binary_types.size()) {
            ofs << ",";
        }
        ofs << "\n";
    }
    ofs << "  ],\n";

    std::unordered_map<std::vector<int>, int, VectorIntHash> set_id_of;
    std::vector<std::vector<int>> set_values;
    const int u = spec.unary_count();
    for (int left = 0; left < u; ++left) {
        for (int right = 0; right < u; ++right) {
            std::vector<int> cand = canonicalize_ints(spec.pair_choice_names(left, right));
            auto it = set_id_of.find(cand);
            if (it == set_id_of.end()) {
                int id = static_cast<int>(set_values.size());
                set_id_of.emplace(cand, id);
                set_values.push_back(std::move(cand));
            }
        }
    }

    ofs << "  \"candidate_sets\": {\n";
    for (std::size_t sid = 0; sid < set_values.size(); ++sid) {
        ofs << "    \"S" << sid << "\": [";
        const auto& cand = set_values[sid];
        for (std::size_t j = 0; j < cand.size(); ++j) {
            if (j != 0) {
                ofs << ", ";
            }
            ofs << "\"" << json_escape(interner.str(spec.binary_name_sids[static_cast<std::size_t>(cand[j])])) << "\"";
        }
        ofs << "]";
        if (sid + 1 != set_values.size()) {
            ofs << ",";
        }
        ofs << "\n";
    }
    ofs << "  },\n";

    ofs << "  \"pair_binary_rules\": [\n";
    bool first_rule = true;
    for (int left = 0; left < u; ++left) {
        for (int right = 0; right < u; ++right) {
            std::vector<int> cand = canonicalize_ints(spec.pair_choice_names(left, right));
            int set_id = set_id_of.at(cand);
            if (!first_rule) {
                ofs << ",\n";
            }
            first_rule = false;
            ofs << "    {\"left_type\": \"" << json_escape(interner.str(spec.unary_name_sids[static_cast<std::size_t>(left)]))
                << "\", \"right_type\": \"" << json_escape(interner.str(spec.unary_name_sids[static_cast<std::size_t>(right)]))
                << "\", \"set\": \"S" << set_id << "\"}";
        }
    }
    ofs << "\n";
    ofs << "  ]\n";
    ofs << "}\n";
}

struct IndependenceComponentReport {
    int component_id = -1;
    std::vector<int> predicate_sids;
    std::vector<int> constraint_indices;
    bool main_ok = false;
    std::string main_error;
    fo2::TypeSystemId main_spec;
    bool aux_ok = false;
    std::string aux_error;
    fo2::TypeSystemId aux_spec;
    std::optional<fs::path> dumped_aux_path;
};

struct IndependenceAnalysisReport {
    bool has_split = false;
    bool valid = false;
    std::string reason;
    std::vector<int> all_predicate_sids;
    std::vector<IndependenceComponentReport> components;
};

static IndependenceAnalysisReport analyze_independence_and_build_components(
    const fo2::TypeSystemId& spec,
    const fo2::TypeSystemId& aux_spec,
    fo2::InternTable& interner,
    const std::optional<fs::path>& dump_dir
) {
    IndependenceAnalysisReport report;
    report.valid = true;

    const auto b_pred_states = build_binary_pred_states(spec, interner);

    std::unordered_set<int> pred_set;
    for (const auto& row : b_pred_states) {
        for (const auto& kv : row) {
            pred_set.insert(kv.first);
        }
    }
    report.all_predicate_sids.assign(pred_set.begin(), pred_set.end());
    std::sort(report.all_predicate_sids.begin(), report.all_predicate_sids.end(), [&interner](int a, int b) {
        return interner.str(a) < interner.str(b);
    });

    if (report.all_predicate_sids.size() <= 1) {
        report.reason = "Binary predicate count <= 1; no independent split";
        return report;
    }

    std::unordered_map<int, int> pred_to_pos;
    for (int i = 0; i < static_cast<int>(report.all_predicate_sids.size()); ++i) {
        pred_to_pos.emplace(report.all_predicate_sids[static_cast<std::size_t>(i)], i);
    }

    Dsu dsu(static_cast<int>(report.all_predicate_sids.size()));

    for (int ul = 0; ul < spec.unary_count(); ++ul) {
        for (int ur = 0; ur < spec.unary_count(); ++ur) {
            const auto& cand = spec.pair_choice_names(ul, ur);
            for (int pi = 0; pi < static_cast<int>(report.all_predicate_sids.size()); ++pi) {
                int pred_a = report.all_predicate_sids[static_cast<std::size_t>(pi)];
                for (int pj = pi + 1; pj < static_cast<int>(report.all_predicate_sids.size()); ++pj) {
                    int pred_b = report.all_predicate_sids[static_cast<std::size_t>(pj)];
                    std::unordered_set<int> proj_a;
                    std::unordered_set<int> proj_b;
                    std::unordered_set<int> proj_ab;
                    proj_a.reserve(cand.size());
                    proj_b.reserve(cand.size());
                    proj_ab.reserve(cand.size());

                    for (int bidx : cand) {
                        const auto& row = b_pred_states[static_cast<std::size_t>(bidx)];
                        PredBitState sa;
                        PredBitState sb;
                        auto ia = row.find(pred_a);
                        if (ia != row.end()) {
                            sa = ia->second;
                        }
                        auto ib = row.find(pred_b);
                        if (ib != row.end()) {
                            sb = ib->second;
                        }
                        int code_a = encode_pred_state(sa);
                        int code_b = encode_pred_state(sb);
                        proj_a.insert(code_a);
                        proj_b.insert(code_b);
                        proj_ab.insert(code_a * 16 + code_b);
                    }

                    std::size_t expected = proj_a.size() * proj_b.size();
                    if (proj_ab.size() != expected) {
                        dsu.unite(pi, pj);
                    }
                }
            }
        }
    }

    std::map<int, std::vector<int>> grouped_pred_sids;
    for (int pi = 0; pi < static_cast<int>(report.all_predicate_sids.size()); ++pi) {
        int root = dsu.find(pi);
        grouped_pred_sids[root].push_back(report.all_predicate_sids[static_cast<std::size_t>(pi)]);
    }
    std::vector<std::vector<int>> components_predicates;
    for (auto& kv : grouped_pred_sids) {
        auto preds = kv.second;
        std::sort(preds.begin(), preds.end(), [&interner](int a, int b) {
            return interner.str(a) < interner.str(b);
        });
        components_predicates.push_back(std::move(preds));
    }
    std::sort(components_predicates.begin(), components_predicates.end(), [&interner](const auto& a, const auto& b) {
        if (a.empty() || b.empty()) {
            return a.size() < b.size();
        }
        return interner.str(a.front()) < interner.str(b.front());
    });

    if (components_predicates.size() <= 1) {
        report.reason = "Candidate sets couple all predicates into one component";
        return report;
    }

    report.has_split = true;

    for (int ul = 0; ul < spec.unary_count(); ++ul) {
        for (int ur = 0; ur < spec.unary_count(); ++ur) {
            const auto& cand = spec.pair_choice_names(ul, ur);
            std::unordered_set<std::vector<int>, VectorIntHash> seen_tuple;
            std::vector<std::unordered_set<std::vector<int>, VectorIntHash>> per_comp_sets(
                components_predicates.size()
            );
            for (int bidx : cand) {
                std::vector<int> flat;
                for (std::size_t ci = 0; ci < components_predicates.size(); ++ci) {
                    std::vector<int> key = projection_key_for_component(
                        bidx,
                        components_predicates[ci],
                        b_pred_states
                    );
                    per_comp_sets[ci].insert(key);
                    flat.insert(flat.end(), key.begin(), key.end());
                    flat.push_back(99);  // separator
                }
                seen_tuple.insert(std::move(flat));
            }
            std::size_t expected = 1;
            for (const auto& s : per_comp_sets) {
                expected *= s.size();
            }
            if (seen_tuple.size() != expected) {
                report.reason = "Full candidate-set cartesian factorization failed after predicate grouping";
                report.has_split = false;
                report.valid = true;
                return report;
            }
        }
    }

    std::vector<int> constraint_to_component(static_cast<std::size_t>(spec.existential_count()), -1);
    for (int cidx = 0; cidx < spec.existential_count(); ++cidx) {
        auto side_assign = [&](bool from_left) -> std::optional<int> {
            bool all_same = true;
            bool first = from_left
                ? contains_int(spec.binary_types[0].satisfies_from_left, cidx)
                : contains_int(spec.binary_types[0].satisfies_from_right, cidx);
            for (int bidx = 1; bidx < spec.binary_count(); ++bidx) {
                bool v = from_left
                    ? contains_int(spec.binary_types[static_cast<std::size_t>(bidx)].satisfies_from_left, cidx)
                    : contains_int(spec.binary_types[static_cast<std::size_t>(bidx)].satisfies_from_right, cidx);
                if (v != first) {
                    all_same = false;
                    break;
                }
            }
            if (all_same) {
                return std::nullopt;
            }

            std::vector<int> possible_components;
            for (int comp_id = 0; comp_id < static_cast<int>(components_predicates.size()); ++comp_id) {
                std::unordered_map<std::vector<int>, int, VectorIntHash> key_to_seen;
                bool ok = true;
                for (int bidx = 0; bidx < spec.binary_count(); ++bidx) {
                    std::vector<int> key = projection_key_for_component(
                        bidx,
                        components_predicates[static_cast<std::size_t>(comp_id)],
                        b_pred_states
                    );
                    bool v = from_left
                        ? contains_int(spec.binary_types[static_cast<std::size_t>(bidx)].satisfies_from_left, cidx)
                        : contains_int(spec.binary_types[static_cast<std::size_t>(bidx)].satisfies_from_right, cidx);
                    int value = v ? 1 : 0;
                    auto it = key_to_seen.find(key);
                    if (it == key_to_seen.end()) {
                        key_to_seen.emplace(std::move(key), value);
                    } else if (it->second != value) {
                        ok = false;
                        break;
                    }
                }
                if (ok) {
                    possible_components.push_back(comp_id);
                }
            }

            if (possible_components.size() == 1) {
                return possible_components[0];
            }
            return std::optional<int>{-2};  // inconsistent
        };

        std::optional<int> left_comp = side_assign(true);
        std::optional<int> right_comp = side_assign(false);
        if ((left_comp.has_value() && *left_comp == -2) || (right_comp.has_value() && *right_comp == -2)) {
            report.reason = "Constraint witness dependency is not component-separable";
            report.has_split = false;
            report.valid = true;
            return report;
        }

        int assign = -1;
        if (left_comp.has_value() && right_comp.has_value()) {
            if (*left_comp != *right_comp) {
                report.reason = "Constraint left/right dependency falls into different components";
                report.has_split = false;
                report.valid = true;
                return report;
            }
            assign = *left_comp;
        } else if (left_comp.has_value()) {
            assign = *left_comp;
        } else if (right_comp.has_value()) {
            assign = *right_comp;
        }
        constraint_to_component[static_cast<std::size_t>(cidx)] = assign;
    }

    report.components.clear();
    for (int comp_id = 0; comp_id < static_cast<int>(components_predicates.size()); ++comp_id) {
        IndependenceComponentReport comp;
        comp.component_id = comp_id;
        comp.predicate_sids = components_predicates[static_cast<std::size_t>(comp_id)];
        for (int cidx = 0; cidx < spec.existential_count(); ++cidx) {
            if (constraint_to_component[static_cast<std::size_t>(cidx)] == comp_id) {
                comp.constraint_indices.push_back(cidx);
            }
        }

        auto build_main = build_component_main_spec(
            spec,
            interner,
            comp_id,
            comp.predicate_sids,
            comp.constraint_indices,
            b_pred_states
        );
        comp.main_ok = build_main.ok;
        comp.main_error = build_main.error;
        if (build_main.ok) {
            comp.main_spec = std::move(build_main.component_main);
        }

        auto build_aux = build_component_aux_spec(
            spec,
            aux_spec,
            interner,
            comp_id,
            comp.predicate_sids,
            comp.constraint_indices,
            b_pred_states
        );
        comp.aux_ok = build_aux.ok;
        comp.aux_error = build_aux.error;
        if (build_aux.ok) {
            comp.aux_spec = std::move(build_aux.component_aux);
            if (dump_dir.has_value()) {
                fs::create_directories(*dump_dir);
                fs::path out_path = *dump_dir / ("component_aux_" + std::to_string(comp_id) + ".json");
                write_typesystem_json(comp.aux_spec, interner, out_path);
                comp.dumped_aux_path = out_path;
            }
        }
        report.components.push_back(std::move(comp));
    }

    bool all_ok = true;
    for (const auto& comp : report.components) {
        if (!comp.main_ok || !comp.aux_ok) {
            all_ok = false;
            break;
        }
    }
    report.valid = all_ok;
    if (!all_ok && report.reason.empty()) {
        report.reason = "At least one component main/aux projection failed";
    }
    if (all_ok) {
        report.reason = "independence detected and component main/aux projection passed";
    }
    return report;
}

