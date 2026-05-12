#pragma once

#include <chrono>
#include <string>

#include "spec_id.hpp"

struct CompiledCircuit;

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
);

int run_existential_compile_branch(
    int domain_size,
    int post_process_mode,
    bool mem_debug,
    bool analyze_independence,
    bool analyze_independence_only,
    const std::string& component_aux_out_dir,
    const std::string& json_spec_path,
    const std::string& spec_name,
    const fo2::TypeSystemId& spec,
    fo2::InternTable& interner,
    const std::chrono::steady_clock::time_point& t0,
    const std::chrono::steady_clock::time_point& t1,
    std::string& aux_spec_name,
    int& root,
    CompiledCircuit& circuit
);
