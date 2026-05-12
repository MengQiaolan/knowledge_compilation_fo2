#include "compiler_branches.hpp"

#include "compiler_common.hpp"
#include "compiler_existential.hpp"
#include "compiler_universal.hpp"

namespace {

std::string format_duration_branch(double seconds) {
    std::ostringstream oss;
    oss << std::fixed << std::setprecision(6) << seconds << "s ("
        << std::setprecision(2) << (seconds * 1000.0) << " ms)";
    return oss.str();
}

}  // namespace

int run_universal_compile_branch(
    int domain_size,
    int post_process_mode,
    bool mem_debug,
    bool analyze_independence,
    bool analyze_independence_only,
    const std::string& spec_name,
    const std::string& aux_spec_name,
    const fo2::TypeSystemId& spec,
    fo2::InternTable& interner,
    const std::chrono::steady_clock::time_point& t0,
    const std::chrono::steady_clock::time_point& t1,
    int& root,
    CompiledCircuit& circuit
) {
    if (analyze_independence) {
        std::cout << "Independence analysis:\n";
        std::cout << "  skipped (universal-only mode; no auxiliary existential SAT state)\n";
        if (analyze_independence_only) {
            return 0;
        }
    }

    CompilerUniversal compiler(domain_size, spec, interner);
    root = compiler.compile_raw();
    std::optional<CompilerUniversal::DebugStats> debug_before_post;
    if (mem_debug) {
        debug_before_post = compiler.debug_stats();
    }
    const auto t2 = std::chrono::steady_clock::now();
    circuit = compiler.post_process(root, post_process_mode);
    const auto t3 = std::chrono::steady_clock::now();

    const double pre = std::chrono::duration<double>(t1 - t0).count();
    const double compiling = std::chrono::duration<double>(t2 - t1).count();
    const double post = std::chrono::duration<double>(t3 - t2).count();

    const auto stats = circuit.stats();
    std::cout << "Spec: " << spec_name << "\n";
    std::cout << "Aux spec: " << aux_spec_name << "\n";
    std::cout << "Domain size n: " << domain_size << "\n";
    std::cout << "Timing:\n";
    std::cout << "  pre processing: " << format_duration_branch(pre) << "\n";
    std::cout << "  compiling: " << format_duration_branch(compiling) << "\n";
    std::cout << "  post processing: " << format_duration_branch(post) << "\n";
    std::cout << "Circuit stats:\n";
    std::cout << "  nodes: " << stats.nodes << "  (and: " << stats.and_nodes
              << ", or: " << stats.or_nodes << ", leaves: " << stats.leaf_nodes << ")\n";
    std::cout << "  edges: " << stats.edges << "\n";

    if (mem_debug) {
        const auto& ds = debug_before_post.value();
        std::cout << "MEMDEBUG universal:\n";
        std::cout << "  circuit.node_count: " << ds.circuit.node_count << "\n";
        std::cout << "  circuit.node_child_refs: " << ds.circuit.node_child_refs << "\n";
        std::cout << "  circuit.and_cache_size: " << ds.circuit.and_cache_size << "\n";
        std::cout << "  circuit.and_cache_key_refs: " << ds.circuit.and_cache_key_refs << "\n";
        std::cout << "  circuit.or_cache_size: " << ds.circuit.or_cache_size << "\n";
        std::cout << "  circuit.or_cache_key_refs: " << ds.circuit.or_cache_key_refs << "\n";
        std::cout << "  subcircuit_cache_size: " << ds.subcircuit_cache_size << "\n";
        std::cout << "  pair_suffix_registry_size: " << ds.pair_suffix_registry_size << "\n";
        std::cout << "  pair_suffix_registry_total_refs: " << ds.pair_suffix_registry_total_refs << "\n";
        std::cout << "  subcircuit_key_refs: " << ds.subcircuit_key_refs << "\n";
        std::cout << "  pair_signature_suffix_cache_size: " << ds.pair_signature_suffix_cache_size << "\n";
        std::cout << "  pair_signature_suffix_key_refs: " << ds.pair_signature_suffix_key_refs << "\n";
        std::cout << "  pair_signature_suffix_value_refs: " << ds.pair_signature_suffix_value_refs << "\n";
        std::cout << "  grouped_btypes_cache_size: " << ds.grouped_btypes_cache_size << "\n";
        std::cout << "  unary_clause_cache_size: " << ds.unary_clause_cache_size << "\n";
        std::cout << "  binary_clause_cache_size: " << ds.binary_clause_cache_size << "\n";
    }

    return 0;
}
