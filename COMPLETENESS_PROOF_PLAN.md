# Completeness Proof Plan

This file specifies the concrete implementation plan for proving
`MaskChecker_viable_imp_char_true` (paper Theorem C.5) using the
first-step decomposition approach described in CRITICAL.md.

The false `fst_run_produces_realizable` has been deleted and replaced by a
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

---

## Phase 2: singleProducible nonemptiness — ✅ COMPLETE (2026-03-18)

### Lemma D — `BuildDetokLexer_singleProducible_of_evalFrom`

**File**: `Lexing.lean`, line ~1828

Both Case 1 (single-symbol `[t]`) and Case 2 (EOS `[char t, eos]`) fully proved.
Case 2 uses `hrestart` hypothesis. See BUGS_AND_FIXES.md for technical details.

---

## Phase 3: T=[] edge case — ✅ RESOLVED (2026-03-18)

### Lemma E — resolved via `hviable_tail_ne` hypothesis

The `T = []` case is handled by adding a hypothesis `hviable_tail_ne` to the
generic `MaskChecker_viable_imp_char_true` theorem. This hypothesis states that
the tail output `T` from suffix processing is nonempty given the decomposition
of a viable run.

**Justification for `BuildDetokLexer` + `ParserWithEOS`**: The parser requires
`.eos` for acceptance. Since `curr ++ [cand]` are all character tokens, `.eos`
cannot appear in `terms` or `S` (produced by character-input steps). Therefore
`.eos` must appear in `T` (produced during suffix processing), so `T ≠ []`.

**Status**: The `T = []` branch in `MaskChecker_viable_imp_char_true` closes by
contradiction via `hviable_tail_ne`. The concrete `Completeness` theorem needs
to discharge this hypothesis, which is TODO (see Phase 5).

---

## Phase 4: Core completeness — ✅ COMPLETE (2026-03-18)

### `MaskChecker_viable_imp_char_true` — PROVED (zero sorry's)

**File**: `GrammarConstrainedDecoding.lean`, line ~805

**Hypotheses** (two beyond the viability condition):
- `hsingle`: head of nonempty FST output is singleton-producible from the
  intermediate state. Discharged by Lemma D for `BuildDetokLexer`.
- `hviable_tail_ne`: the tail output from suffix processing is nonempty.
  Discharged for `BuildDetokLexer` + `ParserWithEOS` by the `.eos` argument.

**Proof structure** (5 steps):
1. **FST decomposition** (lines 817–867): `evalFrom_append` + `evalFrom_cons_some_iff`
2. **Realizable sequence witness** (870–885): `d = S ++ [T.head]`
3. **PDA prefix closure** (887–903): `evalFrom_append'` + `evalFrom_prefix_nonempty`
   + `evalFrom_nonempty_exists_singleton`
4. **Accepted/dependent case split** (905–915): `mem_ComputeValidTokenMask_preprocess_iff`
5. **MaskChecker assembly** (917–925): `fold_or_eq_true_iff` + `Finset.mem_image`

### `fst_run_produces_realizable` — DELETED

The false generic theorem has been removed and replaced by the hypothesis-based
approach above.

### Helper lemmas added in PDA.lean:
- `PDA.fullStep_biUnion`: fullStep distributes over union
- `PDA.evalFrom_biUnion`: evalFrom distributes over initial config set
- `PDA.evalFrom_nonempty_exists_singleton`: nonempty set → some singleton nonempty

### Helper in GrammarConstrainedDecoding.lean:
- `BuildDetokLexer_hsingle`: wraps Lemma D for the generic `hsingle` signature

---

## Phase 5: Remaining sorry's — IN PROGRESS

Two sorry's remain in GrammarConstrainedDecoding.lean (down from three):

### 5.1 `Completeness` — ✅ RESOLVED

Duplicated proof for concrete types to avoid elaboration timeout.
Uses `set_option maxHeartbeats 1600000`.

### 5.1b `EOSCompleteness` — ✅ RESOLVED

Proved with 5 new structural helper lemmas for `.eos` properties.

### 5.2 `GCDChecker_sound` (line ~1846) — Sorry

Connects step-level `Soundness` to cumulative `checkerSound` via induction
on the token prefix. Requires `checkerAllowsTermination` (productivity/liveness
hypothesis) and `checkerPathIndependent` (FST factors through flatten).

### 5.3 `GCDChecker_complete` (line ~1875) — Sorry (statement fixed)

Statement corrected: now uses concrete `GCDLanguage spec P` instead of free `L`.
Added `hempty`/`hrestart` hypotheses. Connects step-level `Completeness`/
`EOSCompleteness` to cumulative `checkerComplete` via induction on the token
prefix.

### Infrastructure completed

- `checkerAllows_nil`, `checkerAllows_snoc`, `checkerAllows_snoc_iff` (Checker.lean)
- `GCDLanguage` definition (GrammarConstrainedDecoding.lean)

---

## Execution order (updated)

| # | Task | File | Depends on | Status |
|---|------|------|-----------|--------|
| 1 | Lemma A: NFA prefix closure | GCD.lean | — | ✅ Done |
| 2 | Lemma B: PDA prefix closure | PDA.lean | — | ✅ Done |
| 3 | Lemma C: NFA ⊇ PDA reachability | GCD.lean | — | ✅ Done |
| 4 | Lemma D: `singleProducible` nonemptiness | Lexing.lean | — | ✅ Done |
| 5 | Lemma E: T=[] edge case | GCD.lean | — | ✅ Resolved (hypothesis) |
| 6 | Delete `fst_run_produces_realizable` | GCD.lean | — | ✅ Done |
| 7 | Prove `MaskChecker_viable_imp_char_true` | GCD.lean | 1–6 | ✅ Done |
| 8 | `ParserWithEOS_tail_ne` lemma | GCD.lean | — | ✅ (via duplicated proof) |
| 9 | Fix `Completeness` elaboration timeout | GCD.lean | 7, 8 | ✅ Done (duplicated proof) |
| 9b | Prove `EOSCompleteness` | GCD.lean | — | ✅ Done |
| 9c | `checkerAllows` induction lemmas | Checker.lean | — | ✅ Done |
| 9d | Define `GCDLanguage`, fix `GCDChecker_complete` statement | GCD.lean | — | ✅ Done |
| 10 | Prove `GCDChecker_sound` | GCD.lean | Soundness | ⬜ (needs path indep + termination) |
| 11a | `checkerLanguage = GCDLanguage` backward | GCD.lean | Completeness + EOS | ✅ Done |
| 11b | `checkerLanguage = GCDLanguage` forward | GCD.lean | Soundness (EOS) | ✅ Done |
| 11c | `checkerIntermediateLanguage = prefixes` | GCD.lean | Termination | ⬜ (blocked by 5.1a) |
| 12 | `lake build` clean (zero sorry) | — | all | ⬜ |

**Current sorry's**: `GCDChecker_sound` (termination + path independence, split into 2 sorry's), `GCDChecker_complete` (prefix closure only — language equality fully proved).
**New infrastructure**: `BuildDetokLexer_eval_flatMap_eq` (FST factors through flatten), `ParserWithEOS_evalFull_eos_imp_accepts` (evalFull + .eos → accepts).
Tasks 10 and 11b are independent. Task 11c is blocked by the productivity hypothesis.

---

## Risks and mitigations (updated)

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| `Completeness` elaboration timeout persists even with concrete proof | Medium | Refactor to duplicate proof for concrete types (Option 2) |
| `ParserWithEOS_tail_ne` requires deep parser structure reasoning | Low | The argument is simple (`.eos` not produced by character steps) |
| `GCDChecker_sound/complete` induction needs more infrastructure | Medium | Defer to separate PR; core completeness is primary goal |
| Heartbeat issues in new proofs | Medium | Use explicit type annotations, `@[reducible]`, `dsimp` |

---

## Assumptions documented

The formalization relies on two hypotheses beyond the paper:

1. **`hempty`**: The empty string is not accepted by the lexer automaton.
2. **`hrestart`**: Every accepting state has a restart character
   (`∀ s ∈ A.accept, ∃ c, A.step s c = none ∧ (A.step A.start c).isSome`).

Both hold for all practical lexer specifications. Documented in README.md.
