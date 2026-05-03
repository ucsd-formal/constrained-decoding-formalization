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
| `Lexing.lean` | Compatibility import for the split lexing development |
| `Lexing/Base.lean` | Lexer specs, partial lexing, and lexing FST construction |
| `Lexing/Correctness.lean` | Equivalence between partial lexing, relational lexing, and the lexing FST |
| `Lexing/Detokenizing.lean` | Detokenizing FST and its composition with the lexing FST |
| `Lexing/Whitespace.lean` | Whitespace exchange and singleton-producibility lemmas |
| `RealizableSequence.lean` | One-step output enumeration and inverse token spanner table |
| `Checker.lean` | Executable checker interface with soundness/completeness specs |
| `ParserWithEOS.lean` | EOS-augmented parser used when lexer outputs include an end marker |
| `GCDAssumptions.lean` | End-to-end GCD assumptions, including parser-side whitespace ignoring |
| `GCDAlgorithm.lean` | Preprocessing, valid-token mask computation, and executable GCD checker |
| `GCDStepProofs.lean` | Step-level preprocessing, soundness, completeness, and EOS completeness |
| `GCDCheckerLanguage.lean` | Bridge from step-level proofs to `checkerLanguage = GCDLanguage` |
| `GCDProductivity.lean` | Productivity, path independence, and final checker correctness |
| `GrammarConstrainedDecoding.lean` | Compatibility import for the split GCD proof development |

## Main Theorems
- **`GCDChecker_correct`** — The checker satisfies the full `checkerCorrect` interface, which states that EOS is accepted if and only if the input string is in the target language, and any intermediate accepted token sequence is the prefix of some sequence in the target language.
- **`GCDChecker_pathIndependent`** — `checkerAllows` is invariant under retokenizations with the same flattened character content.

## Other Theorems 
- **`GCDChecker_checkerLanguage_eq_GCDLanguage`** — The accepted token language of `GCDChecker spec P` is exactly the lexer/parser target language.
- **`GCDChecker_productive`** — Every incrementally allowed prefix extends to an accepted checker word.
- **Step-level soundness (`Soundness`)** — If a token's mask bit is true, then there exists a continuation where the composed FST+parser accepts. *(Paper Theorem C.4)*
- **Step-level completeness (`Completeness`, `EOSCompleteness`)** — If a viable continuation exists through the composed system, the token's mask bit is true. *(Paper Theorem C.5)*
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

## Paper-to-Formalization Reference

This table maps definitions, algorithms, and theorems from the paper to their Lean 4 counterparts.

### Structures and Definitions

| Paper | Notation | Lean Name | File |
|-------|----------|-----------|------|
| EOS-extended alphabet | $\Sigma \cup \{$`EOS`$\}$ | `ExtChar α` (abbrev `Ch α`) | `Char.lean` |
| Finite-state automaton (FSA) | $\mathcal{A} = (\Sigma, Q, q_0, \delta, F)$ | `FSA α σ` | `Automata.lean` |
| Finite-state transducer (FST) | $\mathcal{T} = (\Sigma, \Gamma, Q, q_0, \delta, F)$ | `FST α Γ σ` | `Automata.lean` |
| Pushdown automaton (PDA) | $\mathcal{P} = (\Sigma, \Pi, Q, q_0, Z_0, \delta, F)$ | `PDA Γ π σ` | `PDA.lean` |
| Lexer specification | $\{(\mathcal{A}^i, T^i)\}_i$ | `LexerSpec α Γ σ` | `Lexing/Base.lean` |
| Token vocabulary | $\mathcal{V} \subseteq \Sigma^+$ | `Vocabulary α β` | `Vocabulary.lean` |
| Context-free grammar language | $\mathcal{L}(\mathcal{G})$ | `PDA.accepts` | `PDA.lean` |
| Prefix language | $\mathcal{L}_{\text{prefix}}(\mathcal{G})$ | `Language.prefixes` | `Language.lean` |
| Producible terminals (Def. C.1) | $\textit{Prod}(q)$ | `FST.singleProducible q` | `Producible.lean` |
| Realizable terminal sequences (Def. 3.2) | $Re_{\mathcal{A} \circ \mathcal{V}}$ | `RealizableSequences fst_comp` | `RealizableSequence.lean` |
| Inverse token spanner table (Def. 3.3) | $T_{\text{inv}}(q, \alpha)$ | `InverseTokenSpannerTable fst_comp` | `RealizableSequence.lean` |
| Always-accepted tokens | $A(q^\mathcal{A}, q^\mathcal{P})$ | `PPTable` (accepted bucket) | `GCDAlgorithm.lean` |
| Context-dependent sequences | $D(q^\mathcal{A}, q^\mathcal{P})$ | `PPTable` (dependent bucket) | `GCDAlgorithm.lean` |
| Checker | $\mathcal{C}$ | `Checker β` | `Checker.lean` |
| GCD target language | $\mathcal{L}^{\text{Lex}}(\mathcal{G})$ | `GCDLanguage spec P` | `GCDCheckerLanguage.lean` |

### Algorithms

| Paper Algorithm | Lean Name | File |
|-----------------|-----------|------|
| Alg. 1: ConstrainedDecoding | `GCDChecker spec P` | `GCDAlgorithm.lean` |
| Alg. 2: BuildLexingFST | `BuildLexingFST spec` | `Lexing/Base.lean` |
| Alg. 3: BuildDetokenizingFST | `BuildDetokenizingFST` | `Lexing/Detokenizing.lean` |
| FST composition ($\mathcal{T}_{\mathcal{A} \circ \mathcal{V}}$) | `Detokenizing.BuildDetokLexer spec` | `Lexing/Detokenizing.lean` |
| Alg. 4: BuildInverseTokenSpannerTable | `BuildInverseTokenSpannerTable fst_comp` | `RealizableSequence.lean` |
| Alg. 5: PreprocessParser | `PreprocessParser fst_comp P` | `GCDAlgorithm.lean` |
| Alg. 6: ComputeValidTokenMask | `ComputeValidTokenMask P itst table qa qp st` | `GCDAlgorithm.lean` |
| Partial lexer ($\text{Lex}$) | `PartialLex spec` | `Lexing/Base.lean` |
| PDA $\to$ NFA overapproximation | `PDA.toNFA` | `PDA.lean` |
| DFS singleton-producible computation | `FST.computeSingleProducible q` | `Producible.lean` |

### Propositions and Theorems

| Paper Result | Lean Name | File |
|-------------|-----------|------|
| Stack invariance (Prop. 3.1) | `PDA.stackInvariance` | `PDA.lean` |
| Overapproximation via FSA (Prop. 3.2) | `PDA.overApproximation` | `PDA.lean` |
| Lexer-FST equivalence (Thm. C.1) | `PartialLex_to_LexingFST` | `Lexing/Correctness.lean` |
| Producible $\Rightarrow$ singleton-producible (Lemma C.3) | `computeSingleProducible_correct` | `Producible.lean` |
| Valid mask characterization | `mem_ComputeValidTokenMask_preprocess_iff` | `GCDStepProofs.lean` |
| Soundness (Thm. C.4) | `Soundness` | `GCDStepProofs.lean` |
| Completeness (Thm. C.5) | `Completeness`, `EOSCompleteness` | `GCDStepProofs.lean` |
| Mask $\Rightarrow$ viable continuation | `accept_if_ComputedValidTokenMask` | `GCDStepProofs.lean` |
| $\text{checkerLanguage} = \mathcal{L}^{\text{Lex}}(\mathcal{G})$ | `GCDChecker_checkerLanguage_eq_GCDLanguage` | `GCDCheckerLanguage.lean` |
| Checker productivity | `GCDChecker_productive` | `GCDProductivity.lean` |
| Checker path independence | `GCDChecker_pathIndependent` | `GCDProductivity.lean` |
| Full checker interface | `GCDChecker_correct` | `GCDProductivity.lean` |

### Type Parameters

Throughout the codebase, these type variables recur:

| Variable | Role | Paper notation |
|----------|------|----------------|
| `α` | Character/input alphabet | $\Sigma$ |
| `β` | Token alphabet | $\mathcal{V}$ |
| `Γ` | Terminal/output alphabet | $\Gamma$ |
| `π` | Stack alphabet | $\Pi$ |
| `σ`, `σa`, `σp` | Automaton/parser state types | $Q$ |

Most require `FinEnum`, `DecidableEq`, or `BEq`/`LawfulBEq` instances.

## Assumptions

The final checker theorems use one public package, `GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite`.

```
structure GCDAssumptions where
  hempty        : [] ∉ spec.automaton.accepts
  lexer_pruned  : spec.automaton.pruned
  parser_pruned : P.pruned
  whitespace    : GCDWhitespaceAssumption spec P tnonwhite twhite qnonwhite qwhite
```

**Non-empty-string lexing (`hempty`).** The lexer automaton's start state is not accepting. This rules out empty lexer tokens.

**Lexer prunedness.** Every reachable lexer state can still reach an accepting lexer state (no dead states). This is used by the whitespace-modulo lexer realizability argument.

**Parser prunedness.** Every reachable parser configuration has some accepted continuation (no dead states). 

**Full whitespace assumption.** `GCDWhitespaceAssumption` intuitively states that the language must contain a whitespace token that acts as a universal separator. More formally, it states that there is a a distinguished whitespace terminal `twhite`, as well as at least one non whitespace terminal `tnonwhite`. The parser must ignore whitespace. Whitespace tokens must only be accepted by the lexer if and only if the current state is `qstart` or `qwhite`.


**Singleton vocabulary tokens.** The `Vocabulary α β` instance is part of the theorem context. It provides an embedding of individual characters as singleton tokens (`flatten (embed a) = [a]`) and rules out empty tokens (`flatten b ≠ []`). The EOS-extended vocabulary preserves this singleton embedding for plain characters and maps EOS to the singleton EOS token. This is the vocabulary shape needed by the detokenization and whitespace-exchange proofs.

### What this means for users

The checker productivity and path-independence obligations are no longer external hypotheses. To instantiate the end-to-end theorem, provide finite/enumerable alphabets and states, a `Vocabulary` instance, and prove `GCDAssumptions`. The core files currently build with no Lean `sorry`.

## License

This project is licensed under the Apache License 2.0. See [LICENSE](LICENSE) for details.
