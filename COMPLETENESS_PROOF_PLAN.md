# Completeness Proof Plan

This file specifies the concrete implementation plan for proving
`MaskChecker_viable_imp_char_true` (paper Theorem C.5) using the
first-step decomposition approach described in CRITICAL.md.

The false `fst_run_produces_realizable` is deleted and replaced by a
chain of targeted lemmas.

---

## Overview

**Goal**: Given viability of `curr ++ [cand]`, show `.char cand` is in the
computed valid-token mask.

**Strategy**: Decompose the viable FST run at the first-step boundary,
pick `d = S ++ [T.head]` as the witness realizable sequence, and show
it lands in either the accepted or dependent preprocessing bucket using
prefix closure of NFA/PDA evaluation.

**Dependency chain** (each step depends on the ones above it):

```
Lemma A  (NFA prefix closure)          ─┐
Lemma B  (PDA prefix closure)          ─┤
Lemma C  (NFA ⊇ PDA reachability)     ─┤── Lemma F (completeness assembly)
Lemma D  (singleProducible nonempty)   ─┤
Lemma E  (T=[] edge case resolution)   ─┘
```

---

## Phase 1: Prefix-closure infrastructure — ✅ COMPLETE (2026-03-18)

All six lemmas proved and compiling with zero errors.

### Lemma A — NFA prefix closure (GrammarConstrainedDecoding.lean, FinsetNFA namespace)

| Lemma | Line | Status |
|-------|------|--------|
| `FinsetNFA.evalFrom_append` | ~86 | ✅ |
| `FinsetNFA.evalFrom_empty` | ~92 | ✅ |
| `FinsetNFA.evalFrom_prefix_nonempty` | ~103 | ✅ |

### Lemma B — PDA prefix closure (PDA.lean, after `evalFrom_none`)

| Lemma | Line | Status |
|-------|------|--------|
| `PDA.evalFrom_append'` | ~133 | ✅ |
| `PDA.evalFrom_prefix_nonempty` | ~137 | ✅ |

### Lemma C — NFA ⊇ PDA reachability (GrammarConstrainedDecoding.lean)

| Lemma | Line | Status |
|-------|------|--------|
| `PDA.evalFrom_nonempty_imp_nfa_nonempty` | ~116 | ✅ |

Proved via `overApproximationLemma` + `finsetEvalFrom_iff_evalFrom`.

**These lemmas fully resolve Sub-problem B** (parser handles the truncated
sequence `S ++ [T']`) from CRITICAL.md §4.

---

## Phase 2: singleProducible nonemptiness — ✅ COMPLETE (2026-03-18)

Case 1 (single-symbol output) fully proved. Case 2 (EOS) sorry'd pending LexerSpec assumption.

### Lemma D — `BuildDetokLexer_singleProducible_of_evalFrom`

**File**: `Lexing.lean`, line ~1828 (after private helpers `find_first_nonempty`, `empty_prefix_all_empty`, `first_eq_head_of_first_nonempty`)

**Actual statement** (stronger than originally planned — proves head membership, not just nonemptiness):
```lean
theorem BuildDetokLexer_singleProducible_of_evalFrom
    [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] [vocab: Vocabulary (Ch α) V]
    (spec : LexerSpec α Γ σ)
    (hempty : [] ∉ spec.automaton.accepts)
    (q : LexingState σ) (w : List V) (qf : Unit × LexingState σ)
    (T : List (Ch Γ))
    (hrun : (BuildDetokLexer (v := vocab) spec).evalFrom ((), q) w = some (qf, T))
    (hne : T ≠ []) :
    T.head hne ∈ (BuildDetokLexer (v := vocab) spec).singleProducible ((), q)
```

**Proof architecture** (5-stage, mirrors `detok_rs_pfx_forward`):

1. **Reduce to singleton tokens**: `detokenize_singleton` replaces `w` with `ws` where each token has a singleton `flatten`.
2. **Decompose into step list**: `stepList_of_eval` gives the step-by-step trace.
3. **Find first non-empty emission**: `find_first_nonempty` locates `firstIdx`.
4. **Classify via `LexingFst_smallStep`**: The emission is either `[t]` (Case 1) or `[char t, eos]` (Case 2).
5. **Construct singleProducible witness**: `ws.take (firstIdx + 1)` is the witness input.

| Case | Status | Details |
|------|--------|---------|
| Case 1: produced = `[t]` | ✅ Proved | `ws.take (firstIdx+1)` witnesses `t ∈ singleProducible q` via `eval_of_stepList_opaque` + `take_succ_eq_append_getElem` decomposition |
| Case 2: produced = `[char t, eos]` | ✅ Proved | Uses `hrestart` hypothesis to find restart character `c`, builds witness `ws.take firstIdx ++ [embed (.char c)]` which triggers the single-symbol restart path |

**Key technical difficulties solved** (see BUGS_AND_FIXES.md for details):
- `produce` vs raw lambda `fun x => x.2.2.2` bridging via `rfl` equality
- Fin vs Nat `GetElem` indexing mismatch (syntactic, not definitional)
- Dependent `List.head` proof transport via universally-quantified helper
- `min` in `List.length_take` — deferred simplification pattern

**Decision (2026-03-18)**: Added `hrestart` hypothesis to the theorem. Documented in code docstring and project README. See BUGS_AND_FIXES.md for technical issues encountered.

---

## Phase 3: T=[] edge case

### Lemma E — The tail is never empty under viability

**Statement**:
```lean
lemma viability_suffix_produces_output
    (comb : FST (Ch β) (Ch Γ) σa) (parser : PDA (Ch Γ) π σp)
    (q_fst : σa) (terms : List (Ch Γ)) (qp : Ch σp) (st : List π)
    (q₁ : σa) (S : List (Ch Γ)) (suffix : List (Ch β))
    (qa' : σa) (T : List (Ch Γ))
    (hmem : (qp, st) ∈ parser.evalFrom {(parser.start, [])} terms)
    (hstep : comb.step q_fst (.char cand) = some (q₁, S))
    (htail : comb.evalFrom q₁ suffix = some (qa', T))
    (hparse : parser.evalFull (terms ++ S ++ T) ≠ ∅) :
    S ++ T ≠ []
```

**Proof idea**: `parser = ParserWithEOS P`. For `evalFull` to be nonempty,
the output must end with `.eos` (the `ParserWithEOS` accept state is `.eos`,
which can only be reached by processing an `.eos` input). So `terms ++ S ++ T`
must contain `.eos`, meaning `S ++ T ≠ []`.

Actually, we need the stronger claim: `T ≠ []` OR `S ≠ []`.

But wait — we need `T ≠ []` specifically for the singleProducible argument.
If `T = []` but `S ≠ []`, we need an alternative path.

**Alternative approach**: When `T = []`, `gammas_rest = S`. If `S ≠ []`,
we still need `singleProducible q₁ ≠ ∅`. We can argue:

- The parser accepts `terms ++ S` via `evalFull`. Since `ParserWithEOS`
  needs `.eos`, the sequence `terms ++ S` must contain `.eos`.
- If `.eos` is in `S`, then the lexer produced `.eos` during the step
  `comb.step q_fst (.char cand) = some (q₁, S)`. The lexer only produces
  `.eos` on an EOS input character. But `flatten (.char cand)` never
  contains `.eos` (for `cand : β`, not `eos`). So `.eos ∉ S`.
- Therefore `.eos ∈ terms`. But then `parser.evalFull terms` already
  processed `.eos`, and any further processing of `S` is from the
  `.eos` parser state. The `.eos` parser state accepts all inputs
  (line 54: `| .eos, _ => {([], [], .eos)}`).
- In this case, the parser can process ANY single symbol from the `.eos`
  state. So for any `T' ∈ singleProducible q₁`, `parser.evalFrom {(.eos, [])} (S ++ [T']) ≠ ∅`.

Actually this analysis is getting complicated. Let me simplify.

**Simplified approach**: When `T = []`, the viability condition still gives
us the parser and NFA information we need (through `S`). The question is
ONLY whether `singleProducible q₁ ≠ ∅`.

For `BuildDetokLexer` specifically: `q₁ = ((), q_lex')` after processing
`cand`. The lexer state `q_lex'` is where the lexer lands after consuming
`flatten (.char cand)` from state `q_lex`. Since the composed FST processed
`suffix = []` successfully (trivially), we know the FST didn't get stuck.
But we don't know if future output is possible.

**However**: For the mask check, if `T = []`, then `gammas_rest = S` and
`S ++ T = S`. The parser accepting `terms ++ S` means `.eos` must appear
somewhere. But `.eos` can't be in `S` (see above). So `.eos ∈ terms`, meaning
the parser had already seen `.eos` before processing `S`. After `.eos`, the
`ParserWithEOS` loops in the `.eos` state accepting everything.

So after the parser processes `terms` and reaches `.eos` state, it can
process `S` and also `S ++ [anything]`. This means for ANY `d ∈ RealizableSequences`
with `cand ∈ InverseTokenSpannerTable d q_fst`, the parser handles it from
the `.eos` state.

We still need `singleProducible q₁ ≠ ∅` to have ANY such `d` exist. If it IS
empty, there are NO realizable sequences for this step, so `cand` is NOT in the
mask. But viability says it should be. This would be a genuine incompleteness
in the algorithm for this edge case.

**Resolution**: This edge case represents a token `cand` where:
1. The FST step on `cand` produces some output `S`
2. No further output is ever producible from the resulting state `q₁`
3. The overall parse is still valid

This can only happen if `q₁` is a "dead-end" state of the composed FST
where no transition produces output. For `BuildDetokLexer`, this means the
lexer is in a state from which no accepting state is ever reachable (the
current lexeme can never be completed). But then the FST should not have
any accepting run through `q₁`, contradicting the viability of any
continuation. In a well-formed `LexerSpec`, every reachable non-start state
has a path to an accepting state, so `singleProducible q₁ ≠ ∅`.

**Decision**: Add `singleProducible q₁ ≠ ∅` as a hypothesis to
`MaskChecker_viable_imp_char_true` in the `T = []` case, or prove it
from a `LexerSpec`-level invariant. Defer this edge case as a minor gap
and focus the proof on the `T ≠ []` case first.

**Estimated time**: 1 hour analysis + possibly 1 hour implementation.

---

## Phase 4: Delete `fst_run_produces_realizable` and prove completeness

### Step 4.1 — Delete the false theorem

Remove `fst_run_produces_realizable` (lines 754–764) and its doc comment.

### Step 4.2 — Rewrite `MaskChecker_viable_imp_char_true`

**New proof structure** (for the `T ≠ []` case):

```lean
theorem MaskChecker_viable_imp_char_true
  [BEq σa] [LawfulBEq σa] [FinEnum β]
  (comb : FST (Ch β) (Ch Γ) σa) (parser : PDA (Ch Γ) π σp)
  (curr : List β) (cand : β)
  (hviable : ∃ suffix qa gammas,
    comb.eval (((curr ++ [cand]).map ExtChar.char) ++ suffix) = some (qa, gammas) ∧
    parser.evalFull gammas ≠ ∅) :
  MaskChecker comb parser (PreprocessParser comb parser)
    (BuildInverseTokenSpannerTable comb).snd curr (.char cand) = true := by
  -- 1. Decompose viability
  obtain ⟨suffix, qa, gammas, heval, hparse⟩ := hviable
  -- Extract q_fst, terms from processing curr
  -- Extract q₁, S from step on .char cand
  -- Extract qa', T from evalFrom q₁ suffix
  -- 2. Show S ++ T ≠ [] (from parser needing .eos)
  -- 3. Case split T = [] vs T ≠ []
  -- Case T ≠ []:
  --   a. By Lemma D: T.head ∈ singleProducible q₁
  --   b. Let d := S ++ [T.head]
  --   c. d ∈ RealizableSequences (by definition)
  --   d. .char cand ∈ InverseTokenSpannerTable d q_fst (from step)
  --   e. NFA prefix closure: FinsetNFA.evalFrom parser {qp} d ≠ ∅
  --   f. PDA prefix closure: parser.evalFrom {(qp, st)} d ≠ ∅
  --   g. d is accepted or dependent → cand in mask
  -- 4. Assemble via mem_ComputeValidTokenMask_preprocess_iff
  sorry
```

### Step 4.3 — Verify `Completeness` follows

`Completeness` delegates to `MaskChecker_viable_imp_char_true`, so it
should need no changes once the above compiles.

**Estimated time**: 2–3 hours.

---

## Phase 5: Close remaining sorry's

### `GCDChecker_sound` and `GCDChecker_complete`

These connect the step-level theorems to the cumulative `checkerAllows` /
`checkerAccepts` interface from `Checker.lean` via induction on the token
prefix. They are somewhat orthogonal to the completeness proof above.

**Approach**: Induction on the prefix list. Base case: `checkerAllows c [] = true`
is trivial. Inductive step: uses `Soundness` / `Completeness` for the single-step
case combined with `GCDChecker_char_true_imp_viable` / the new completeness.

**Estimated time**: 1–2 hours.

---

## Execution order

| # | Task | File | Depends on | Est. | Status |
|---|------|------|-----------|------|--------|
| 1 | Lemma A: NFA `evalFrom_append`, `evalFrom_empty`, `evalFrom_prefix_nonempty` | GCD.lean | — | 15m | ✅ Done |
| 2 | Lemma B: PDA `evalFrom_append'`, `evalFrom_prefix_nonempty` | PDA.lean | — | 10m | ✅ Done |
| 3 | Lemma C: NFA ⊇ PDA reachability | GCD.lean | — | 30m | ✅ Done |
| 4 | Lemma D: `singleProducible` nonemptiness | Lexing.lean | D.1, D.2 | 3–4h | ✅ Done (with `hrestart` hyp) |
| 5 | Lemma E: `T = []` edge case | GCD.lean | Lemma D | 1–2h | ⬜ |
| 6 | Delete `fst_run_produces_realizable` | GCD.lean | — | 2m | ⬜ |
| 7 | Prove `MaskChecker_viable_imp_char_true` | GCD.lean | 1–5 | 2–3h | ⬜ |
| 8 | Verify `Completeness` compiles | GCD.lean | 7 | 5m | ⬜ |
| 9 | Prove `GCDChecker_sound`, `GCDChecker_complete` | GCD.lean | 7, 8 | 1–2h | ⬜ |
| 10 | `lake build` clean | — | all | 10m | ⬜ |

**Remaining**: ~5–8 hours (Case 2 sorry + Phases 3–5)

**Critical path**: Task 4 Case 2 (EOS sorry) and Task 5 (T=[] edge case) both
need LexerSpec assumption decisions. Tasks 6–8 are sequential after 4–5.
Tasks 1–3 complete. Task 4 Case 1 complete.

---

## Risks and mitigations

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| Lemma D proof requires LexerSpec invariants not currently formalized | Medium | Add as hypothesis; document for future work |
| EOS subtlety in Lemma D.5 breaks the singleton construction | Low | Use the "character that starts a new lexeme" fallback |
| `T = []` edge case is genuinely incomplete in the algorithm | Low | Add `singleProducible q₁ ≠ ∅` as hypothesis; flag as minor gap |
| Instance resolution / heartbeat issues in new proofs | Medium | Use explicit type annotations, `@[reducible]`, `dsimp` |
| `GCDChecker_sound/complete` need more infrastructure than expected | Medium | Defer to separate PR; the core completeness is the primary goal |
