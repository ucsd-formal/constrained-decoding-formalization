# Formal Verification of Grammar-Constrained Decoding

A Lean 4 formalization of the paper [*Flexible and Efficient Grammar-Constrained Decoding*](https://arxiv.org/pdf/2502.05111). This project proves correctness of a grammar-constrained decoding algorithm that composes a detokenizing lexer FST with a pushdown parser to compute valid next-token masks during LLM inference.

## Overview

Grammar-constrained decoding ensures that language model outputs conform to a given formal grammar (e.g., JSON, SQL, code). The core algorithm works by:

1. **Lexing** — An FST maps token sequences to character sequences, handling the mismatch between an LLM's token vocabulary and the grammar's character-level rules.
2. **Parsing** — A pushdown automaton (PDA) checks whether character sequences belong to the target language.
3. **Composition** — The lexer FST and parser are composed so that, at each decoding step, the system can determine which tokens lead to strings still accepted by the grammar.

This formalization verifies that the composed system correctly computes the set of valid next tokens, establishing both **soundness** (every token in the mask extends to a valid parse) and **completeness** (no valid token is excluded).

## Formalization Structure

| File | Description |
|------|-------------|
| `Char.lean` | EOS-extended alphabet (`ExtChar α`) used throughout |
| `Automata.lean` | Deterministic FSA and FST with composition and mathlib DFA/NFA conversions |
| `Language.lean` | Language helpers and prefix closure, bridging to `Mathlib.Computability.Language` |
| `Vocabulary.lean` | `Vocabulary α β` typeclass mapping tokens to character sequences |
| `Producible.lean` | DFS-based computation of singleton-producible FST outputs with correctness proof |
| `PDA.lean` | Pushdown automaton with stack semantics, `evalFrom`, and NFA overapproximation |
| `Lexing.lean` | Lexer spec, lexing FST construction, and detokenizing FST composition |
| `RealizableSequence.lean` | One-step output enumeration and inverse token spanner table |
| `Checker.lean` | Executable checker interface with soundness/completeness specs |
| `GrammarConstrainedDecoding.lean` | Main assembly: preprocessing, valid-token mask computation, and end-to-end correctness theorems |

## Key Theorems

- **`accept_if_ComputedValidTokenMask`** — Tokens in the computed mask extend to valid FST runs through the parser.
- **`mem_ComputeValidTokenMask_preprocess_iff`** — Semantic characterization of the valid-token mask: a token is in the mask iff it is realizable and the resulting output is accepted by the parser from the current state.
- **`computeSingleProducible_correct`** — The executable DFS for singleton-producible outputs matches the semantic specification.

## Building

Requires [Lean 4](https://lean-lang.org/) (toolchain `leanprover/lean4:v4.29.0-rc6`).

```bash
# Download prebuilt mathlib oleans (recommended before first build)
lake exe cache get

# Build the full project
lake build
```

## Dependency Visualizer

An interactive declaration dependency graph is available at:

**[ucsd-formal.github.io/constrained-decoding-formalization](https://ucsd-formal.github.io/constrained-decoding-formalization/)**

To run locally:

```bash
./lean-dep-viz serve          # Serve at localhost:3000
./lean-dep-viz build --output-dir site  # Generate static site
```

## Assumptions

The completeness proof relies on one hypothesis about the lexer specification beyond what is stated in the paper:

**Lexer restartability (`hrestart`).** Every accepting state of the character automaton has at least one character that does *not* extend the current lexeme but *can* start a new lexeme from the start state:

```
∀ s ∈ A.accept, ∃ c, A.step s c = none ∧ (A.step A.start c).isSome
```

This is needed because the lexing FST has two emission patterns: a single-symbol `[char t]` (when completing a token and restarting) and a two-symbol `[char t, eos]` (when completing at end-of-stream). The completeness argument requires that the head of any nonempty output is *singleton-producible*—i.e., there exists an input that produces exactly that one symbol. For the EOS case, the two-symbol emission `[char t, eos]` cannot directly witness singleton producibility, so we need the restart path to produce just `[char t]`. The `hrestart` hypothesis guarantees such a restart character exists.

This holds for all practical lexer specifications: it requires only that (1) the start state has at least one outgoing transition, and (2) each accepting state has at least one character class it does not recognize. Both conditions are trivially satisfied by standard lexers for programming languages, JSON, etc., where different token types (identifiers, operators, literals) use disjoint character classes.

## License

This project is licensed under the Apache License 2.0. See [LICENSE](LICENSE) for details.
