# Machine-Checked Grammar-Constrained Decoding

A Lean 4 formalization of grammar-constrained decoding (GCD), following the
algorithm of [*Flexible and Efficient Grammar-Constrained Decoding*](https://arxiv.org/pdf/2502.05111)
(Park et al.). It builds an executable next-token checker by composing a
detokenizing lexer transducer with a pushdown parser, and proves that the
checker is **sound** and **complete**: after any token prefix it allows exactly
the next tokens that can still be extended to a grammatical output.

## Highlights

- **An end-to-end machine-checked correctness theorem** (`GCDChecker_correct`)
  for an executable GCD checker, under a small, explicit bundle of assumptions.
- **A bug found in the published lexing construction.** The original lexer has no
  distinguished start state, so it accepts end-of-stream whenever the lexing
  automaton happens to return to its start state, i.e. in the middle of an
  unfinished terminal. The regex `(ab)*a` triggers it. We give a corrected
  construction with a separate start state and verify it.
- **The assumptions made precise.** The paper leaves several conditions implicit.
  The one that does real work is the *universal separator*: a distinguished
  whitespace terminal that ends any lexeme and is a no-op for the parser. It is
  what collapses the otherwise unbounded set of lexer continuations to a finite
  check.
- **Reusable infrastructure** with no GCD-specific dependencies: partial finite
  automata and transducers with executable composition (`Automata.lean`),
  nondeterministic pushdown automata with stack lemmas and a stack-forgetting NFA
  over-approximation (`PDA.lean`), and a verified finite graph search
  (`Producible.lean`).

## Building

Requires [Lean 4](https://lean-lang.org/), toolchain `leanprover/lean4:v4.29.0-rc6`
(see `lean-toolchain`); mathlib is pinned in `lake-manifest.json`.

```bash
lake exe cache get   # prebuilt mathlib oleans, recommended before the first build
lake build ConstrainedDecodingFormalization ConstrainedDecodingFormalization.GCDTest
```

The development contains no `sorry` and declares no axioms.

## The pipeline

An LLM emits **tokens**; a grammar is defined over **terminals** that a lexer
groups from **characters**. The target semantics is the composition

```
tokens --detokenize--> characters --lex--> terminals --parse--> accept
```

A complete token sequence is valid exactly when this pipeline succeeds. The
checker decides, incrementally, whether a candidate token keeps that pipeline
completable.

1. **Lexing.** `BuildLexingFST` compiles a lexer specification (a character
   automaton labeled with terminals) into a one-lookahead maximal-munch
   transducer. `Lexing/Correctness.lean` proves it equivalent to the relational
   specification `PartialLexRel`.
2. **Detokenization.** `BuildDetokenizingFST` flattens tokens to characters;
   composing it with the lexer gives `BuildDetokLexer`, driven directly by tokens.
3. **Realizable tails.** Modulo whitespace, the terminal sequences the lexer can
   still produce from a state are exactly those whose first terminal is
   *single-producible* there. This is the finiteness result the checker rests on.
4. **Tables.** `BuildInverseTokenSpannerTable` records, per lexer state, the
   *realizable sequence heads* each token exposes and inverts that map back to
   tokens. `PreprocessParser` sorts heads into always-allowed, always-rejected,
   and stack-dependent using stack invariance and NFA over-approximation.
5. **Online mask.** `ComputeValidTokenMask` seeds the mask with the
   always-allowed tokens and tests each stack-dependent head against the live
   parser configuration. `GCDChecker` wires this to a prefix evaluation.

## Module map

| File | Role |
|------|------|
| `Char.lean` | EOS-extended alphabet `ExtChar α` (abbrev `Ch α`) |
| `Language.lean` | Prefix closure `Language.prefixes`, bridging to `Mathlib.Computability.Language` |
| `Automata.lean` | Partial deterministic FSA and FST, executable composition, mathlib DFA/NFA conversions |
| `PDA.lean` | Pushdown automaton, stack semantics, `evalFrom`, `toNFA` over-approximation |
| `Producible.lean` | Depth-first search for single-producible terminals, with its correctness proof |
| `Vocabulary.lean` | `Vocabulary α β` typeclass: tokens to character strings, with the singleton-token law |
| `Lexing/Base.lean` | Lexer specs, the partial lexer `PartialLex`/`PartialLexRel`, and `BuildLexingFST` |
| `Lexing/Correctness.lean` | Equivalence of partial lexing, the relational lexer, and the lexing FST |
| `Lexing/Detokenizing.lean` | Detokenizing FST and its composition `BuildDetokLexer` |
| `Lexing/Whitespace.lean` | Whitespace-exchange lemmas and the realizable-tail characterization |
| `Lexing.lean` | Compatibility import for the four `Lexing/` modules |
| `RealizableSequence.lean` | Realizable sequence heads and the inverse token-spanner table |
| `Checker.lean` | The executable `Checker β` interface and its language-level semantics |
| `ParserWithEOS.lean` | EOS-augmented parser used when lexer output carries an end marker |
| `GCDAssumptions.lean` | The `GCDAssumptions` bundle, including the universal-separator condition |
| `GCDAlgorithm.lean` | `PreprocessParser`, `ComputeValidTokenMask`, and the executable `GCDChecker` |
| `GCDStepProofs.lean` | Step-level mask correctness: `Soundness`, `Completeness`, `EOSCompleteness` |
| `GCDCheckerLanguage.lean` | Bridge to `checkerLanguage = TargetLanguage` |
| `GCDProductivity.lean` | Productivity, path independence, and the final `GCDChecker_correct` |
| `GrammarConstrainedDecoding.lean` | Compatibility import for the GCD proof stack |
| `GCDTest.lean` | A finite JSON-like grammar with all assumptions discharged (`jsonChecker_correct`) |

## Main theorems

| Theorem | Statement |
|---------|-----------|
| `GCDChecker_correct` | The checker satisfies the full `checkerCorrect` interface: EOS is allowed iff the prefix is in the target language, and every allowed token sequence is a prefix of some target-language word. |
| `GCDChecker_checkerLanguage_eq_TargetLanguage` | The accepted token language of `GCDChecker spec P` equals the lexer/parser target language. |
| `GCDChecker_intermediateLanguage_eq_TargetLanguage_prefixes` | The prefixes the checker allows equal the prefix closure of the target language. |
| `GCDChecker_productive` | Every incrementally allowed prefix extends to an accepted word. |
| `GCDChecker_pathIndependent` | The checker depends only on the flattened character content of the prefix. |
| `Soundness` / `Completeness` / `EOSCompleteness` | Step level: a token's mask bit is true iff a viable continuation exists through the composed FST and parser. |
| `computeSingleProducible_correct` | The executable DFS enumerates exactly the single-producible terminals. |
| `mem_ComputeValidTokenMask_preprocess_iff` | Semantic membership characterization of the online mask. |

## Assumptions

The final theorems are parameterized by one package,
`GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite`:

```lean
structure GCDAssumptions
    (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
    (tnonwhite twhite : α) (qnonwhite qwhite : σa) : Prop where
  hempty        : [] ∉ spec.automaton.accepts
  lexer_pruned  : spec.automaton.pruned
  parser_pruned : P.pruned
  whitespace    : GCDWhitespaceAssumption spec P tnonwhite twhite qnonwhite qwhite
```

- **No empty lexeme (`hempty`).** The lexer automaton's start state is not
  accepting, so no lexeme is empty.
- **Lexer prunedness.** Every reachable lexer state can still reach an accepting
  state. Used by the realizable-tail argument.
- **Parser prunedness.** Every reachable parser configuration has an accepted
  continuation.
- **Universal separator (`GCDWhitespaceAssumption`).** The condition is organized
  around a distinguished whitespace character `twhite` (with a witnessing
  non-whitespace character `tnonwhite`, and the lexer states `qwhite`/`qnonwhite`
  they lead to). On the lexer side, `twhite` belongs to no lexeme other than the
  whitespace terminal, so it always ends the preceding lexeme and returns the
  lexer to a clean post-separator state. On the parser side,
  `ParserIgnoresTerminal` holds: every state reads the whitespace terminal with
  the identity transition.
- **Singleton tokens.** Carried by the `Vocabulary α β` instance: every single
  character is itself a token (`flatten (embed a) = [a]`) and no token flattens
  to nothing (`flatten b ≠ []`).

To instantiate the end-to-end theorem for a grammar, supply finite/enumerable
alphabets and states, a `Vocabulary` instance, and a proof of `GCDAssumptions`.
The generic theorems are not reproved. `GCDTest.lean` does this for a shallow
JSON grammar, using newline as the separator; `native_decide` discharges the
finite side conditions there.

## Dependency visualizer

An interactive declaration dependency graph is at
**[ucsd-formal.github.io/constrained-decoding-formalization](https://ucsd-formal.github.io/constrained-decoding-formalization/)**.

```bash
./lean-dep-viz serve                     # serve at localhost:3000
./lean-dep-viz build --output-dir site   # generate a static site
```

## Paper-to-formalization reference

Maps definitions, algorithms, and results from Park et al. to their Lean
counterparts.

### Structures and definitions

| Paper | Notation | Lean | File |
|-------|----------|------|------|
| EOS-extended alphabet | Σ ∪ {EOS} | `ExtChar α` (abbrev `Ch α`) | `Char.lean` |
| Finite-state automaton | (Σ, Q, q₀, δ, F) | `FSA α σ` | `Automata.lean` |
| Finite-state transducer | (Σ, Γ, Q, q₀, δ, F) | `FST α Γ σ` | `Automata.lean` |
| Pushdown automaton | (Σ, Π, Q, q₀, Z₀, δ, F) | `PDA Γ π σ` | `PDA.lean` |
| Lexer specification | automaton + terminal label per class | `LexerSpec α Γ σ` | `Lexing/Base.lean` |
| Token vocabulary | V ⊆ Σ⁺ | `Vocabulary α β` | `Vocabulary.lean` |
| Grammar language | L(G) | `PDA.accepts` | `PDA.lean` |
| Prefix language | prefixes of L(G) | `Language.prefixes` | `Language.lean` |
| Single-producible terminals (Def. C.1) | Prod(q) | `FST.singleProducible q` | `Producible.lean` |
| Realizable sequence heads (Def. 3.2) | Re | `RealizableSequenceHeads fst_comp` | `RealizableSequence.lean` |
| Realizable terminal sequences | — | `FST.realizableSequences q` | `Automata.lean` |
| Inverse token-spanner table (Def. 3.3) | T_inv(q, a) | `InverseTokenSpannerTable fst_comp` | `RealizableSequence.lean` |
| Always-allowed tokens | A(q_lex, q_parse) | `PPTable` first component | `GCDAlgorithm.lean` |
| Stack-dependent heads | D(q_lex, q_parse) | `PPTable` second component | `GCDAlgorithm.lean` |
| Checker | C | `Checker β` | `Checker.lean` |
| GCD target language | Lex-language of G | `TargetLanguage spec P` | `GCDCheckerLanguage.lean` |

### Algorithms

| Paper | Lean | File |
|-------|------|------|
| Alg. 1: ConstrainedDecoding | `GCDChecker spec P` | `GCDAlgorithm.lean` |
| Alg. 2: BuildLexingFST | `BuildLexingFST spec` | `Lexing/Base.lean` |
| Alg. 3: BuildDetokenizingFST | `BuildDetokenizingFST` | `Lexing/Detokenizing.lean` |
| FST composition (detok ∘ lex) | `Detokenizing.BuildDetokLexer spec` | `Lexing/Detokenizing.lean` |
| Alg. 4: BuildInverseTokenSpannerTable | `BuildInverseTokenSpannerTable fst_comp` | `RealizableSequence.lean` |
| Alg. 5: PreprocessParser | `PreprocessParser fst_comp P` | `GCDAlgorithm.lean` |
| Alg. 6: ComputeValidTokenMask | `ComputeValidTokenMask P itst table qa qp st` | `GCDAlgorithm.lean` |
| Partial lexer (Lex) | `PartialLex spec` | `Lexing/Base.lean` |
| PDA → NFA over-approximation | `PDA.toNFA` | `PDA.lean` |
| DFS for single-producible terminals | `FST.computeSingleProducible q` | `Producible.lean` |

### Propositions and theorems

| Paper result | Lean | File |
|--------------|------|------|
| Stack invariance (Prop. 3.1) | `PDA.stackInvariance` | `PDA.lean` |
| Over-approximation via FSA (Prop. 3.2) | `PDA.overApproximation` | `PDA.lean` |
| Lexer-FST equivalence (Thm. C.1) | `PartialLex_to_LexingFST`, `LexingFST_to_PartialLexRel` | `Lexing/Correctness.lean` |
| Single-producibility (Lemma C.3) | `computeSingleProducible_correct` | `Producible.lean` |
| Valid-mask characterization | `mem_ComputeValidTokenMask_preprocess_iff` | `GCDStepProofs.lean` |
| Soundness (Thm. C.4) | `Soundness` | `GCDStepProofs.lean` |
| Completeness (Thm. C.5) | `Completeness`, `EOSCompleteness` | `GCDStepProofs.lean` |
| Mask ⇒ viable continuation | `accept_if_ComputedValidTokenMask` | `GCDStepProofs.lean` |
| checkerLanguage = target language | `GCDChecker_checkerLanguage_eq_TargetLanguage` | `GCDCheckerLanguage.lean` |
| Checker productivity | `GCDChecker_productive` | `GCDProductivity.lean` |
| Checker path independence | `GCDChecker_pathIndependent` | `GCDProductivity.lean` |
| Full checker interface | `GCDChecker_correct` | `GCDProductivity.lean` |

### Type parameters

| Variable | Role | Paper |
|----------|------|-------|
| `α` | Character / input alphabet | Σ |
| `β` | Token alphabet | V |
| `Γ` | Terminal / output alphabet | Γ |
| `π` | Stack alphabet | Π |
| `σ`, `σa`, `σp` | Automaton / parser state types | Q |

Most carry `FinEnum`, `DecidableEq`, or `BEq`/`LawfulBEq` instances.

## License

Apache License 2.0. See [LICENSE](LICENSE).
