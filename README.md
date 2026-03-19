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

- **Step-level soundness (`Soundness`)** — If a token's mask bit is true, then there exists a continuation where the composed FST+parser accepts. *(Paper Theorem C.4)*
- **Step-level completeness (`Completeness`, `EOSCompleteness`)** — If a viable continuation exists through the composed system, the token's mask bit is true. *(Paper Theorem C.5)*
- **`accept_if_ComputedValidTokenMask`** — Tokens in the computed mask extend to valid FST runs through the parser.
- **`mem_ComputeValidTokenMask_preprocess_iff`** — Semantic characterization of the valid-token mask: a token is in the mask iff it is realizable and the resulting output is accepted by the parser from the current state.
- **`computeSingleProducible_correct`** — The executable DFS for singleton-producible outputs matches the semantic specification.
- **Cumulative checker correctness (`GCDChecker_sound`, `GCDChecker_complete`)** — The step-level theorems lift to the full token-sequence checker interface, establishing that the checker's accepted language equals the target grammar-constrained language. These take two explicit assumptions as hypotheses (see [Assumptions](#assumptions)).

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
| Lexer specification | $\{(\mathcal{A}^i, T^i)\}_i$ | `LexerSpec α Γ σ` | `Lexing.lean` |
| Token vocabulary | $\mathcal{V} \subseteq \Sigma^+$ | `Vocabulary α β` | `Vocabulary.lean` |
| Context-free grammar language | $\mathcal{L}(\mathcal{G})$ | `PDA.accepts` | `PDA.lean` |
| Prefix language | $\mathcal{L}_{\text{prefix}}(\mathcal{G})$ | `Language.prefixes` | `Language.lean` |
| Producible terminals (Def. C.1) | $\textit{Prod}(q)$ | `FST.singleProducible q` | `Producible.lean` |
| Realizable terminal sequences (Def. 3.2) | $Re_{\mathcal{A} \circ \mathcal{V}}$ | `RealizableSequences fst_comp` | `RealizableSequence.lean` |
| Inverse token spanner table (Def. 3.3) | $T_{\text{inv}}(q, \alpha)$ | `InverseTokenSpannerTable fst_comp` | `RealizableSequence.lean` |
| Always-accepted tokens | $A(q^\mathcal{A}, q^\mathcal{P})$ | `PPTable` (accepted bucket) | `GrammarConstrainedDecoding.lean` |
| Context-dependent sequences | $D(q^\mathcal{A}, q^\mathcal{P})$ | `PPTable` (dependent bucket) | `GrammarConstrainedDecoding.lean` |
| Checker | $\mathcal{C}$ | `Checker β` | `Checker.lean` |
| GCD target language | $\mathcal{L}^{\text{Lex}}(\mathcal{G})$ | `GCDLanguage spec P` | `GrammarConstrainedDecoding.lean` |

### Algorithms

| Paper Algorithm | Lean Name | File |
|-----------------|-----------|------|
| Alg. 1: ConstrainedDecoding | `GCDChecker spec P` | `GrammarConstrainedDecoding.lean` |
| Alg. 2: BuildLexingFST | `BuildLexingFST spec` | `Lexing.lean` |
| Alg. 3: BuildDetokenizingFST | `BuildDetokenizingFST` | `Lexing.lean` |
| FST composition ($\mathcal{T}_{\mathcal{A} \circ \mathcal{V}}$) | `Detokenizing.BuildDetokLexer spec` | `Lexing.lean` |
| Alg. 4: BuildInverseTokenSpannerTable | `BuildInverseTokenSpannerTable fst_comp` | `RealizableSequence.lean` |
| Alg. 5: PreprocessParser | `PreprocessParser fst_comp P` | `GrammarConstrainedDecoding.lean` |
| Alg. 6: ComputeValidTokenMask | `ComputeValidTokenMask P itst table qa qp st` | `GrammarConstrainedDecoding.lean` |
| Partial lexer ($\text{Lex}$) | `PartialLex spec` | `Lexing.lean` |
| PDA $\to$ NFA overapproximation | `PDA.toNFA` | `PDA.lean` |
| DFS singleton-producible computation | `FST.computeSingleProducible q` | `Producible.lean` |

### Propositions and Theorems

| Paper Result | Lean Name | File |
|-------------|-----------|------|
| Stack invariance (Prop. 3.1) | `PDA.stackInvariance` | `PDA.lean` |
| Overapproximation via FSA (Prop. 3.2) | `PDA.overApproximation` | `PDA.lean` |
| Lexer-FST equivalence (Thm. C.1) | `PartialLex_to_LexingFST` | `Lexing.lean` |
| Producible $\Rightarrow$ singleton-producible (Lemma C.3) | `computeSingleProducible_correct` | `Producible.lean` |
| Valid mask characterization | `mem_ComputeValidTokenMask_preprocess_iff` | `GrammarConstrainedDecoding.lean` |
| Soundness (Thm. C.4) | `Soundness` | `GrammarConstrainedDecoding.lean` |
| Completeness (Thm. C.5) | `Completeness`, `EOSCompleteness` | `GrammarConstrainedDecoding.lean` |
| Mask $\Rightarrow$ viable continuation | `accept_if_ComputedValidTokenMask` | `GrammarConstrainedDecoding.lean` |
| Checker soundness (Thm. 4.1) | `GCDChecker_sound` | `GrammarConstrainedDecoding.lean` |
| Checker completeness | `GCDChecker_complete` | `GrammarConstrainedDecoding.lean` |
| $\text{checkerLanguage} = \mathcal{L}^{\text{Lex}}(\mathcal{G})$ | `GCDChecker_checkerLanguage_eq_GCDLanguage` | `GrammarConstrainedDecoding.lean` |

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

The formalization relies on four explicit assumptions. The first two are hypotheses on the lexer specification used by the step-level completeness proofs. The latter two are hypotheses on the cumulative checker theorems that lift step-level results to full token sequences.

### Lexer assumptions

These are properties of the lexer automaton that hold for all practical lexer specifications. They are required by the step-level completeness proofs (`Completeness`, `EOSCompleteness`).

**Non-empty-string lexing (`hempty`).** The lexer automaton's start state is not an accepting state—i.e., the empty string is not a valid token.

```
A.start ∉ A.accept
```

**Lexer restartability (`hrestart`).** Every accepting state of the character automaton has at least one character that does *not* extend the current lexeme but *can* start a new lexeme from the start state:

```
∀ s ∈ A.accept, ∃ c, A.step s c = none ∧ (A.step A.start c).isSome
```

This is needed because the lexing FST has two emission patterns: a single-symbol `[char t]` (when completing a token and restarting) and a two-symbol `[char t, eos]` (when completing at end-of-stream). The completeness argument requires that the head of any nonempty output is *singleton-producible*—i.e., there exists an input that produces exactly that one symbol. For the EOS case, the two-symbol emission `[char t, eos]` cannot directly witness singleton producibility, so we need the restart path to produce just `[char t]`. The `hrestart` hypothesis guarantees such a restart character exists.

Both `hempty` and `hrestart` are trivially satisfied by standard lexers for programming languages, JSON, etc.: the empty string is never a valid token, and different token types (identifiers, operators, literals) use disjoint character classes so every accepting state has characters that cannot extend it but can start a new token.

### Cumulative checker assumptions

The cumulative checker theorems (`GCDChecker_sound`, `GCDChecker_complete`) connect the step-level soundness and completeness results to the full `checkerAllows`/`checkerAccepts` interface over token sequences. They take two additional hypotheses:

**Productivity (`checkerAllowsTermination`).** Every token prefix that the checker incrementally allows can be extended to a complete accepted sequence:

```
∀ w, checkerAllows c w → ∃ w', checkerAccepts c w' ∧ w.isPrefixOf w'
```

This is a liveness property of the composed FST+parser system: from any reachable viable state, there exists a path to acceptance. It cannot be proved from the algorithm alone—it depends on the grammar being productive (no infinite derivations or dead-end nonterminals from reachable states). The paper assumes this implicitly. In practice, any well-formed context-free grammar used for constrained decoding (JSON schemas, SQL grammars, etc.) satisfies this property.

**Path independence (`checkerPathIndependent`).** The checker's incremental decisions depend only on the flattened character content of the token prefix, not on the particular tokenization:

```
∀ w₁ w₂, w₁.flatMap flatten = w₂.flatMap flatten → checkerAllows c w₁ = checkerAllows c w₂
```

We prove that each *individual* mask check depends only on the FST state, which in turn depends only on the character content (`MaskChecker_eq_of_eval_eq` + `BuildDetokLexer_eval_flatMap_eq`). However, lifting this to the full conjunction `checkerAllows` is harder: different tokenizations of the same string create checker calls at different character boundaries, so the proof requires showing consistency across retokenization. This is a property of the tokenizer vocabulary rather than the constrained decoding algorithm itself, and is left as an explicit hypothesis. In practice, this holds because LLM tokenizers use deterministic tokenization (e.g., BPE), so each character string has a unique tokenization.

### What this means for users

**The core result is fully proved with no sorry's.** The step-level theorems—that the mask computation is sound and complete at each decoding step—are unconditionally proved (modulo `hempty`/`hrestart`, which are trivially checkable properties of your lexer).

The cumulative checker theorems package the step-level results into a cleaner interface over full token sequences. These hold under the productivity and path independence assumptions, which are satisfied by any well-formed grammar with a deterministic tokenizer—the standard setup for grammar-constrained decoding in practice. If you are using this formalization to justify correctness of a GCD implementation, you need only verify that your grammar has no unreachable/unproductive nonterminals and your tokenizer is deterministic.

## License

This project is licensed under the Apache License 2.0. See [LICENSE](LICENSE) for details.
