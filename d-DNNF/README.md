# d-DNNF Compiler for FO2

This is a C++ implementation of the compilation algorithm in the paper.

## Build

```bash
clang++ -std=c++20 -O2 -Wall -Wextra -pedantic \
  -Icode/include \
  code/run.cpp \
  code/src/compiler_core.cpp \
  code/src/compiler_universal.cpp \
  code/src/compiler_existential.cpp \
  code/src/spec_loader.cpp \
  -lminisat \
  -o run
```

## Run

```bash
./run --json-spec ./examples/non_isolated_graph.json -n 7
```

Options:

- `-n, --domain-size`
- `--json-spec` [ input sentence ]
- `-s` [ optional: save circuit as dot file]
- `-o` [ optional: the path to save dot file ]
- `--post-process` [ `-1`: post-process(default), `0`: disable, `1`: lite post-process ]
- `--model-count` [ optional: output the model counting result ]
- `--verify-correctness` [ optional: bidirectional model-enumeration check ]
- `--max-sat-models` [ optional: maximum number of enumerated models by SAT solver ]
- `--max-dnnf-models` [ optional: maximum number of enumerated model by our circuit ]

## Input JSON Format

- `existential_constraints: [str, ...]`
- `unary_types: [object, ...]`
- `binary_types: [object, ...]`
- `candidate_sets: [binary_type set, ...]`
- `pair_binary_rules: [object, ...]`

### unary_types

- `name: str`
- `literals: { "<atom_template>": bool, ... }`
- `satisfies_self: [constraint_name, ...]`
- `sat_bound: int | null`

### binary_types

- `name: str`
- `literals: { "<atom_template>": bool, ... }`
- `satisfies_from_left: [constraint_name, ...]`
- `satisfies_from_right: [constraint_name, ...]`

### pair_binary_rules

- `left_types: [unary_type_name, ...]`
- `right_types: [unary_type_name, ...]`
- `candidates: [candidate_set_name, ...]`


### Aux Spec Format（`*_aux.json`）

- The auxiliary sentence.