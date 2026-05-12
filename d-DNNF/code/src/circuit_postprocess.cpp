struct CircuitNode {
    enum class Kind : uint8_t {
        LIT = 0,
        AND = 1,
        OR = 2,
        TRUE_NODE = 3,
        FALSE_NODE = 4,
    };

    int id = -1;
    Kind kind = Kind::LIT;
    int atom_sid = -1;
    bool positive = true;
    std::vector<int> children;
};

struct CircuitStats {
    int nodes = 0;
    int edges = 0;
    int leaf_nodes = 0;
    int logical_nodes = 0;
    int and_nodes = 0;
    int or_nodes = 0;
};

struct CompiledCircuit {
    int root = -1;
    std::vector<CircuitNode> nodes;
    std::vector<uint8_t> alive;

    bool is_alive(int node_id) const {
        return node_id >= 0 &&
               static_cast<std::size_t>(node_id) < nodes.size() &&
               static_cast<std::size_t>(node_id) < alive.size() &&
               alive[static_cast<std::size_t>(node_id)] != 0;
    }

    CircuitStats stats() const {
        CircuitStats s;
        for (std::size_t node_id = 0; node_id < nodes.size(); ++node_id) {
            if (!is_alive(static_cast<int>(node_id))) {
                continue;
            }
            const CircuitNode& node = nodes[node_id];
            s.nodes += 1;
            for (int child : node.children) {
                if (is_alive(child)) {
                    s.edges += 1;
                }
            }
            if (node.kind == CircuitNode::Kind::LIT ||
                node.kind == CircuitNode::Kind::TRUE_NODE ||
                node.kind == CircuitNode::Kind::FALSE_NODE) {
                s.leaf_nodes += 1;
            }
            if (node.kind == CircuitNode::Kind::AND) {
                s.and_nodes += 1;
            }
            if (node.kind == CircuitNode::Kind::OR) {
                s.or_nodes += 1;
            }
        }
        s.logical_nodes = s.and_nodes + s.or_nodes;
        return s;
    }
};

static constexpr int kNoneNode = -1;
static constexpr int kPostProcessFull = -1;
static constexpr int kPostProcessNone = 0;
static constexpr int kPostProcessSinglePass = 1;

struct LitKey {
    int atom_sid = -1;
    bool positive = true;

    bool operator==(const LitKey& other) const {
        return atom_sid == other.atom_sid && positive == other.positive;
    }
};

struct LitKeyHash {
    std::size_t operator()(const LitKey& k) const noexcept {
        std::size_t seed = 0;
        hash_combine(seed, k.atom_sid);
        hash_combine(seed, k.positive);
        return seed;
    }
};

struct VectorIntEq {
    bool operator()(const std::vector<int>& a, const std::vector<int>& b) const noexcept {
        return a == b;
    }
};

class CircuitBuilder {
public:
    struct DebugStats {
        std::size_t node_count = 0;
        std::size_t lit_cache_size = 0;
        std::size_t and_cache_size = 0;
        std::size_t or_cache_size = 0;
        std::size_t node_child_refs = 0;
        std::size_t and_cache_key_refs = 0;
        std::size_t or_cache_key_refs = 0;
    };

    int literal(int atom_sid, bool positive) {
        LitKey key{atom_sid, positive};
        auto it = lit_cache_.find(key);
        if (it != lit_cache_.end()) {
            return it->second;
        }

        int node_id = new_lit_node(atom_sid, positive);
        lit_cache_[std::move(key)] = node_id;
        return node_id;
    }

    int and_node(const std::vector<int>& children) {
        if (children.size() == 1) {
            return children[0];
        }
        if (children.size() == 2) {
            int a = children[0];
            int b = children[1];
            if (b < a) {
                std::swap(a, b);
            }
            std::vector<int> normalized{a, b};
            auto it = and_cache_.find(normalized);
            if (it != and_cache_.end()) {
                return it->second;
            }
            int node_id = new_node(CircuitNode::Kind::AND, normalized);
            and_cache_[normalized] = node_id;
            return node_id;
        }

        std::vector<int> normalized = children;
        std::sort(normalized.begin(), normalized.end());
        normalized.erase(std::unique(normalized.begin(), normalized.end()), normalized.end());
        if (normalized.size() == 1) {
            return normalized[0];
        }
        auto it = and_cache_.find(normalized);
        if (it != and_cache_.end()) {
            return it->second;
        }
        int node_id = new_node(CircuitNode::Kind::AND, normalized);
        and_cache_[normalized] = node_id;
        return node_id;
    }

    int or_node(const std::vector<int>& children) {
        if (children.size() == 1) {
            return children[0];
        }
        if (children.size() == 2) {
            int a = children[0];
            int b = children[1];
            if (b < a) {
                std::swap(a, b);
            }
            std::vector<int> normalized{a, b};
            auto it = or_cache_.find(normalized);
            if (it != or_cache_.end()) {
                return it->second;
            }
            int node_id = new_node(CircuitNode::Kind::OR, normalized);
            or_cache_[normalized] = node_id;
            return node_id;
        }

        std::vector<int> normalized = children;
        std::sort(normalized.begin(), normalized.end());
        normalized.erase(std::unique(normalized.begin(), normalized.end()), normalized.end());
        if (normalized.size() == 1) {
            return normalized[0];
        }
        auto it = or_cache_.find(normalized);
        if (it != or_cache_.end()) {
            return it->second;
        }
        int node_id = new_node(CircuitNode::Kind::OR, normalized);
        or_cache_[normalized] = node_id;
        return node_id;
    }

    CompiledCircuit build(int root, int post_process_mode, bool prefer_vector_full_postprocess) {
        // Post-process consumes builder state to avoid keeping both builder.nodes_ and output nodes alive.
        release_compile_caches();
        std::vector<CircuitNode> nodes = std::move(nodes_);
        release_container(nodes_);

        std::vector<uint8_t> alive(nodes.size(), 1);
        if (post_process_mode == kPostProcessFull) {
            if (prefer_vector_full_postprocess) {
                remove_redundent_and_node_vector(root, nodes, alive);
            } else {
                remove_redundent_and_node_hash(root, nodes, alive);
            }
        } else if (post_process_mode == kPostProcessSinglePass) {
            remove_redundent_and_node_single_pass(root, nodes, alive);
        } else if (post_process_mode == kPostProcessNone) {
            // No-op.
        } else {
            throw std::runtime_error(
                "Invalid post_process mode: " + std::to_string(post_process_mode) + " (expected -1, 0, or 1)"
            );
        }
        return CompiledCircuit{root, std::move(nodes), std::move(alive)};
    }

    DebugStats debug_stats() const {
        DebugStats s;
        s.node_count = nodes_.size();
        s.lit_cache_size = lit_cache_.size();
        s.and_cache_size = and_cache_.size();
        s.or_cache_size = or_cache_.size();
        for (const auto& node : nodes_) {
            s.node_child_refs += node.children.size();
        }
        for (const auto& kv : and_cache_) {
            s.and_cache_key_refs += kv.first.size();
        }
        for (const auto& kv : or_cache_) {
            s.or_cache_key_refs += kv.first.size();
        }
        return s;
    }

    void release_compile_caches() {
        release_container(lit_cache_);
        release_container(and_cache_);
        release_container(or_cache_);
    }

private:
    int new_lit_node(int atom_sid, bool positive) {
        int node_id = next_id_++;
        CircuitNode node;
        node.id = node_id;
        node.kind = CircuitNode::Kind::LIT;
        node.atom_sid = atom_sid;
        node.positive = positive;
        nodes_.push_back(std::move(node));
        return node_id;
    }

    int new_node(CircuitNode::Kind kind, const std::vector<int>& children) {
        int node_id = next_id_++;
        CircuitNode node;
        node.id = node_id;
        node.kind = kind;
        node.children = children;
        nodes_.push_back(std::move(node));
        return node_id;
    }

    static void remove_redundent_and_node_vector(
        int root,
        std::vector<CircuitNode>& nodes,
        std::vector<uint8_t>& alive
    ) {
        auto sort_unique = [](std::vector<int>& v) {
            std::sort(v.begin(), v.end());
            v.erase(std::unique(v.begin(), v.end()), v.end());
        };

        auto erase_sorted_one = [](std::vector<int>& v, int x) {
            auto it = std::lower_bound(v.begin(), v.end(), x);
            if (it != v.end() && *it == x) {
                v.erase(it);
            }
        };

        auto insert_sorted_unique = [](std::vector<int>& v, int x) {
            auto it = std::lower_bound(v.begin(), v.end(), x);
            if (it == v.end() || *it != x) {
                v.insert(it, x);
            }
        };

        auto union_sorted = [](const std::vector<int>& a, const std::vector<int>& b) {
            std::vector<int> out;
            out.reserve(a.size() + b.size());
            std::size_t i = 0;
            std::size_t j = 0;
            while (i < a.size() && j < b.size()) {
                if (a[i] < b[j]) {
                    out.push_back(a[i++]);
                } else if (b[j] < a[i]) {
                    out.push_back(b[j++]);
                } else {
                    out.push_back(a[i]);
                    ++i;
                    ++j;
                }
            }
            while (i < a.size()) {
                out.push_back(a[i++]);
            }
            while (j < b.size()) {
                out.push_back(b[j++]);
            }
            return out;
        };

        const int n = static_cast<int>(nodes.size());
        if (n == 0) {
            return;
        }

        auto valid_alive = [&](int id) {
            return id >= 0 && id < n &&
                   static_cast<std::size_t>(id) < alive.size() &&
                   alive[static_cast<std::size_t>(id)] != 0;
        };

        if (!valid_alive(root)) {
            return;
        }

        std::vector<int> node_ids;
        node_ids.reserve(nodes.size());
        std::vector<int> and_ids;
        and_ids.reserve(nodes.size() / 2 + 1);

        for (int node_id = 0; node_id < n; ++node_id) {
            if (!valid_alive(node_id)) {
                continue;
            }
            node_ids.push_back(node_id);
            if (nodes[static_cast<std::size_t>(node_id)].kind == CircuitNode::Kind::AND) {
                and_ids.push_back(node_id);
            }
        }

        std::vector<int> and_idx_of(nodes.size(), -1);
        for (std::size_t i = 0; i < and_ids.size(); ++i) {
            and_idx_of[static_cast<std::size_t>(and_ids[i])] = static_cast<int>(i);
        }

        std::vector<std::vector<int>> and_children(and_ids.size());
        for (std::size_t k = 0; k < and_ids.size(); ++k) {
            int node_id = and_ids[k];
            std::vector<int> ch = nodes[static_cast<std::size_t>(node_id)].children;
            sort_unique(ch);
            and_children[k] = std::move(ch);
        }

        std::vector<std::vector<int>> and_parents(and_ids.size());
        for (int parent_id : node_ids) {
            const CircuitNode& parent = nodes[static_cast<std::size_t>(parent_id)];
            const std::vector<int>* parent_kids = &parent.children;
            int parent_and_idx = and_idx_of[static_cast<std::size_t>(parent_id)];
            if (parent_and_idx >= 0) {
                parent_kids = &and_children[static_cast<std::size_t>(parent_and_idx)];
            }

            for (int child_id : *parent_kids) {
                if (!valid_alive(child_id)) {
                    continue;
                }
                int child_and_idx = and_idx_of[static_cast<std::size_t>(child_id)];
                if (child_and_idx < 0) {
                    continue;
                }
                and_parents[static_cast<std::size_t>(child_and_idx)].push_back(parent_id);
            }
        }

        for (auto& plist : and_parents) {
            sort_unique(plist);
        }

        std::vector<uint8_t> removed(nodes.size(), 0);
        std::vector<uint8_t> children_changed(nodes.size(), 0);
        std::vector<uint8_t> seen(nodes.size(), 0);
        std::deque<int> todo;
        seen[static_cast<std::size_t>(root)] = 1;
        todo.push_back(root);

        while (!todo.empty()) {
            const int node_id = todo.front();
            todo.pop_front();
            if (!valid_alive(node_id)) {
                continue;
            }

            const CircuitNode& node = nodes[static_cast<std::size_t>(node_id)];
            std::vector<int> node_children = node.children;

            int node_and_idx = and_idx_of[static_cast<std::size_t>(node_id)];
            if (node_and_idx >= 0) {
                node_children = and_children[static_cast<std::size_t>(node_and_idx)];
            }

            for (int child_id : node_children) {
                if (!valid_alive(child_id)) {
                    continue;
                }
                if (seen[static_cast<std::size_t>(child_id)] != 0) {
                    continue;
                }
                seen[static_cast<std::size_t>(child_id)] = 1;
                todo.push_back(child_id);
            }

            if (node.kind != CircuitNode::Kind::AND || node_and_idx < 0) {
                continue;
            }

            auto& parents = and_parents[static_cast<std::size_t>(node_and_idx)];
            if (parents.size() != 1) {
                continue;
            }

            int parent_id = parents[0];
            if (!valid_alive(parent_id)) {
                continue;
            }
            int parent_and_idx = and_idx_of[static_cast<std::size_t>(parent_id)];
            if (parent_and_idx < 0) {
                continue;
            }

            removed[static_cast<std::size_t>(node_id)] = 1;

            std::vector<int>& parent_children = and_children[static_cast<std::size_t>(parent_and_idx)];
            const std::vector<int>& this_children = and_children[static_cast<std::size_t>(node_and_idx)];

            erase_sorted_one(parent_children, node_id);
            parent_children = union_sorted(parent_children, this_children);
            children_changed[static_cast<std::size_t>(parent_id)] = 1;

            for (int child_id : this_children) {
                if (!valid_alive(child_id)) {
                    continue;
                }
                int child_and_idx = and_idx_of[static_cast<std::size_t>(child_id)];
                if (child_and_idx < 0) {
                    continue;
                }
                auto& plist = and_parents[static_cast<std::size_t>(child_and_idx)];
                erase_sorted_one(plist, node_id);
                insert_sorted_unique(plist, parent_id);
            }
        }

        for (int node_id : node_ids) {
            if (removed[static_cast<std::size_t>(node_id)] != 0) {
                alive[static_cast<std::size_t>(node_id)] = 0;
                nodes[static_cast<std::size_t>(node_id)].children.clear();
                continue;
            }

            if (children_changed[static_cast<std::size_t>(node_id)] != 0) {
                int and_idx = and_idx_of[static_cast<std::size_t>(node_id)];
                if (and_idx >= 0) {
                    std::vector<int> normalized;
                    const auto& src = and_children[static_cast<std::size_t>(and_idx)];
                    normalized.reserve(src.size());
                    for (int cid : src) {
                        if (valid_alive(cid) && removed[static_cast<std::size_t>(cid)] == 0) {
                            normalized.push_back(cid);
                        }
                    }
                    nodes[static_cast<std::size_t>(node_id)].children = std::move(normalized);
                }
            }
        }
    }

    static void remove_redundent_and_node_hash(
        int root,
        std::vector<CircuitNode>& nodes,
        std::vector<uint8_t>& alive
    ) {
        const int n = static_cast<int>(nodes.size());
        if (n == 0) {
            return;
        }

        auto valid_alive = [&](int id) {
            return id >= 0 && id < n &&
                   static_cast<std::size_t>(id) < alive.size() &&
                   alive[static_cast<std::size_t>(id)] != 0;
        };

        if (!valid_alive(root)) {
            return;
        }

        std::vector<int> node_ids;
        node_ids.reserve(nodes.size());
        std::vector<int> and_ids;
        and_ids.reserve(nodes.size() / 2 + 1);

        for (int node_id = 0; node_id < n; ++node_id) {
            if (!valid_alive(node_id)) {
                continue;
            }
            node_ids.push_back(node_id);
            if (nodes[static_cast<std::size_t>(node_id)].kind == CircuitNode::Kind::AND) {
                and_ids.push_back(node_id);
            }
        }

        std::vector<int> and_idx_of(nodes.size(), -1);
        for (std::size_t i = 0; i < and_ids.size(); ++i) {
            and_idx_of[static_cast<std::size_t>(and_ids[i])] = static_cast<int>(i);
        }

        std::vector<std::unordered_set<int>> and_children(and_ids.size());
        for (std::size_t k = 0; k < and_ids.size(); ++k) {
            int node_id = and_ids[k];
            const auto& src = nodes[static_cast<std::size_t>(node_id)].children;
            auto& dst = and_children[k];
            dst.reserve(src.size() * 2 + 1);
            for (int child_id : src) {
                if (valid_alive(child_id)) {
                    dst.insert(child_id);
                }
            }
        }

        std::vector<std::unordered_set<int>> and_parents(and_ids.size());
        for (int parent_id : node_ids) {
            const CircuitNode& parent = nodes[static_cast<std::size_t>(parent_id)];
            int parent_and_idx = and_idx_of[static_cast<std::size_t>(parent_id)];
            if (parent_and_idx >= 0) {
                const auto& parent_children = and_children[static_cast<std::size_t>(parent_and_idx)];
                for (int child_id : parent_children) {
                    int child_and_idx = and_idx_of[static_cast<std::size_t>(child_id)];
                    if (child_and_idx >= 0) {
                        and_parents[static_cast<std::size_t>(child_and_idx)].insert(parent_id);
                    }
                }
            } else {
                for (int child_id : parent.children) {
                    if (!valid_alive(child_id)) {
                        continue;
                    }
                    int child_and_idx = and_idx_of[static_cast<std::size_t>(child_id)];
                    if (child_and_idx >= 0) {
                        and_parents[static_cast<std::size_t>(child_and_idx)].insert(parent_id);
                    }
                }
            }
        }

        std::vector<uint8_t> removed(nodes.size(), 0);
        std::vector<uint8_t> children_changed(nodes.size(), 0);
        std::vector<uint8_t> seen(nodes.size(), 0);
        std::deque<int> todo;
        seen[static_cast<std::size_t>(root)] = 1;
        todo.push_back(root);

        while (!todo.empty()) {
            const int node_id = todo.front();
            todo.pop_front();
            if (!valid_alive(node_id)) {
                continue;
            }

            const CircuitNode& node = nodes[static_cast<std::size_t>(node_id)];
            int node_and_idx = and_idx_of[static_cast<std::size_t>(node_id)];
            if (node_and_idx >= 0) {
                const auto& chset = and_children[static_cast<std::size_t>(node_and_idx)];
                for (int child_id : chset) {
                    if (!valid_alive(child_id)) {
                        continue;
                    }
                    if (seen[static_cast<std::size_t>(child_id)] != 0) {
                        continue;
                    }
                    seen[static_cast<std::size_t>(child_id)] = 1;
                    todo.push_back(child_id);
                }

                auto& parents = and_parents[static_cast<std::size_t>(node_and_idx)];
                if (parents.size() != 1) {
                    continue;
                }

                int parent_id = *parents.begin();
                if (!valid_alive(parent_id)) {
                    continue;
                }
                int parent_and_idx = and_idx_of[static_cast<std::size_t>(parent_id)];
                if (parent_and_idx < 0) {
                    continue;
                }

                removed[static_cast<std::size_t>(node_id)] = 1;

                auto& parent_children = and_children[static_cast<std::size_t>(parent_and_idx)];
                parent_children.erase(node_id);
                children_changed[static_cast<std::size_t>(parent_id)] = 1;

                for (int child_id : chset) {
                    if (!valid_alive(child_id)) {
                        continue;
                    }
                    int child_and_idx = and_idx_of[static_cast<std::size_t>(child_id)];
                    if (child_and_idx >= 0) {
                        and_parents[static_cast<std::size_t>(child_and_idx)].erase(node_id);
                        and_parents[static_cast<std::size_t>(child_and_idx)].insert(parent_id);
                    }
                    parent_children.insert(child_id);
                }
                continue;
            }

            for (int child_id : node.children) {
                if (!valid_alive(child_id)) {
                    continue;
                }
                if (seen[static_cast<std::size_t>(child_id)] != 0) {
                    continue;
                }
                seen[static_cast<std::size_t>(child_id)] = 1;
                todo.push_back(child_id);
            }
        }

        for (int node_id : node_ids) {
            if (removed[static_cast<std::size_t>(node_id)] != 0) {
                alive[static_cast<std::size_t>(node_id)] = 0;
                nodes[static_cast<std::size_t>(node_id)].children.clear();
                continue;
            }

            if (children_changed[static_cast<std::size_t>(node_id)] != 0) {
                int and_idx = and_idx_of[static_cast<std::size_t>(node_id)];
                if (and_idx >= 0) {
                    std::vector<int> normalized;
                    const auto& src = and_children[static_cast<std::size_t>(and_idx)];
                    normalized.reserve(src.size());
                    for (int cid : src) {
                        if (valid_alive(cid) && removed[static_cast<std::size_t>(cid)] == 0) {
                            normalized.push_back(cid);
                        }
                    }
                    nodes[static_cast<std::size_t>(node_id)].children = std::move(normalized);
                }
            }
        }
    }

    static void remove_redundent_and_node_single_pass(
        int root,
        std::vector<CircuitNode>& nodes,
        std::vector<uint8_t>& alive
    ) {
        (void)root;

        auto sort_unique = [](std::vector<int>& v) {
            std::sort(v.begin(), v.end());
            v.erase(std::unique(v.begin(), v.end()), v.end());
        };

        const int n = static_cast<int>(nodes.size());
        if (n == 0) {
            return;
        }

        auto valid_alive = [&](int id) {
            return id >= 0 && id < n &&
                   static_cast<std::size_t>(id) < alive.size() &&
                   alive[static_cast<std::size_t>(id)] != 0;
        };

        std::vector<int> indegree(nodes.size(), 0);
        for (int node_id = 0; node_id < n; ++node_id) {
            if (!valid_alive(node_id)) {
                continue;
            }
            const CircuitNode& node = nodes[static_cast<std::size_t>(node_id)];
            for (int child : node.children) {
                if (valid_alive(child)) {
                    indegree[static_cast<std::size_t>(child)] += 1;
                }
            }
        }

        std::vector<uint8_t> changed(nodes.size(), 0);
        std::vector<std::vector<int>> updates(nodes.size());
        std::vector<uint8_t> bypassed(nodes.size(), 0);

        for (int node_id = 0; node_id < n; ++node_id) {
            if (!valid_alive(node_id)) {
                continue;
            }
            const CircuitNode& node = nodes[static_cast<std::size_t>(node_id)];
            if (node.kind != CircuitNode::Kind::AND && node.kind != CircuitNode::Kind::OR) {
                continue;
            }

            std::vector<int> expanded;
            expanded.reserve(node.children.size());
            for (int child_id : node.children) {
                if (
                    valid_alive(child_id) &&
                    nodes[static_cast<std::size_t>(child_id)].kind == node.kind &&
                    indegree[static_cast<std::size_t>(child_id)] == 1
                ) {
                    const auto& gchildren = nodes[static_cast<std::size_t>(child_id)].children;
                    expanded.insert(expanded.end(), gchildren.begin(), gchildren.end());
                    bypassed[static_cast<std::size_t>(child_id)] = 1;
                } else {
                    expanded.push_back(child_id);
                }
            }

            sort_unique(expanded);
            if (expanded != node.children) {
                changed[static_cast<std::size_t>(node_id)] = 1;
                updates[static_cast<std::size_t>(node_id)] = std::move(expanded);
            }
        }

        for (int node_id = 0; node_id < n; ++node_id) {
            if (changed[static_cast<std::size_t>(node_id)] != 0) {
                nodes[static_cast<std::size_t>(node_id)].children = std::move(updates[static_cast<std::size_t>(node_id)]);
            }
        }

        // Prune only bypassed nodes that have no live incoming references after the update.
        // This avoids producing alive->dead edges when chain bypass happens in one pass.
        std::vector<int> incoming(nodes.size(), 0);
        for (int node_id = 0; node_id < n; ++node_id) {
            if (!valid_alive(node_id)) {
                continue;
            }
            const auto& node = nodes[static_cast<std::size_t>(node_id)];
            for (int child_id : node.children) {
                if (!valid_alive(child_id)) {
                    continue;
                }
                incoming[static_cast<std::size_t>(child_id)] += 1;
            }
        }

        std::deque<int> prune_queue;
        for (int node_id = 0; node_id < n; ++node_id) {
            if (bypassed[static_cast<std::size_t>(node_id)] == 0 || !valid_alive(node_id)) {
                continue;
            }
            if (incoming[static_cast<std::size_t>(node_id)] == 0) {
                prune_queue.push_back(node_id);
            }
        }

        while (!prune_queue.empty()) {
            int node_id = prune_queue.front();
            prune_queue.pop_front();
            if (!valid_alive(node_id) || bypassed[static_cast<std::size_t>(node_id)] == 0) {
                continue;
            }

            alive[static_cast<std::size_t>(node_id)] = 0;
            auto& children = nodes[static_cast<std::size_t>(node_id)].children;
            for (int child_id : children) {
                if (!valid_alive(child_id)) {
                    continue;
                }
                int& deg = incoming[static_cast<std::size_t>(child_id)];
                if (deg > 0) {
                    deg -= 1;
                }
                if (bypassed[static_cast<std::size_t>(child_id)] != 0 && deg == 0) {
                    prune_queue.push_back(child_id);
                }
            }
            children.clear();
        }
    }

    std::vector<CircuitNode> nodes_;
    int next_id_ = 0;
    std::unordered_map<LitKey, int, LitKeyHash> lit_cache_;
    std::unordered_map<std::vector<int>, int, VectorIntHash, VectorIntEq> and_cache_;
    std::unordered_map<std::vector<int>, int, VectorIntHash, VectorIntEq> or_cache_;
};
