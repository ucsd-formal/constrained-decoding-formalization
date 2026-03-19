# Phase 4: Completeness Assembly

## Goal

Prove `MaskChecker_viable_imp_char_true` (paper Theorem C.5) and delete the false `fst_run_produces_realizable`.

## Current State

- `fst_run_produces_realizable` (line ~800): False theorem, sorry'd. Claims any one-step FST run decomposes into RealizableSequences + InverseTokenSpannerTable. This is overclaimed — it doesn't account for the singleProducible witness.
- `MaskChecker_viable_imp_char_true` (line ~814): sorry'd. Generic completeness over any `comb : FST` and `parser : PDA`.
- `Completeness` (line ~903): Delegates directly to `MaskChecker_viable_imp_char_true`, so it compiles once that's proved.

## Key Definitions

**RealizableSequences** (RealizableSequence.lean:50):
```
{ Ts' | ∃ q_0 t Ts q_1 T,
    fst_comp.step q_0 t = some (q_1, Ts) ∧
    T ∈ fst_comp.singleProducible q_1 ∧ Ts' = Ts ++ [T] }
```

**InverseTokenSpannerTable** (RealizableSequence.lean:59):
```
fun rs st =>
  if h : rs ≠ [] then
    let Ts := rs.dropLast; let T := rs.getLast h
    { t | ∃ q_1, fst_comp.step st t = some (q_1, Ts) ∧ T ∈ fst_comp.singleProducible q_1 }
  else ∅
```

**mem_ComputeValidTokenMask_preprocess_iff** (GCD.lean:443): Token in mask ↔
- **Accepted path**: `∃ d ∈ Re, P.evalFrom {(qp,[])} d ≠ ∅ ∧ tok ∈ ITST d qa`
- **Dependent path**: `∃ d ∈ Re, P.evalFrom {(qp,[])} d = ∅ ∧ NFA.evalFrom P {qp} d ≠ ∅ ∧ P.evalFrom {(qp,st)} d ≠ ∅ ∧ tok ∈ ITST d qa`

**MaskChecker** (GCD.lean:511): Evals `comb` on `curr.map char`, gets `(q_fst, terms)`, computes PDA configs from terms, folds OR over `ComputeValidTokenMask` results.

## Proof Strategy for `MaskChecker_viable_imp_char_true`

### Input
```
hviable : ∃ suffix qa gammas,
  comb.eval (((curr ++ [cand]).map char) ++ suffix) = some (qa, gammas) ∧
  parser.evalFull gammas ≠ ∅
```

### Step 1: Decompose the FST eval

From `hviable`, extract:
- `comb.eval (curr.map char)` = `some (q_fst, terms)` (prefix on curr)
- `comb.step q_fst (.char cand)` = `some (q₁, S)` (one step on cand)
- `comb.evalFrom q₁ suffix` = `some (qa', T)` (tail)
- `gammas = terms ++ S ++ T`

Use `FST.evalFrom_append` and `FST.evalFrom_cons_some_iff`.

### Step 2: Handle T ≠ [] (assume as hypothesis for now)

If `T ≠ []`, we can take `T.head`. The `T = []` case is Phase 3/5.

For the generic theorem, add `T ≠ []` as a hypothesis or prove `S ++ T ≠ []` from parser needing EOS. For now: **add a hypothesis that `singleProducible q₁ ≠ ∅`** as a fallback, OR just handle both cases.

Actually, we don't need T ≠ [] specifically. We need `singleProducible q₁` to be nonempty. If T ≠ [], Lemma D gives us T.head ∈ singleProducible q₁. But the generic theorem is over ANY `comb`, not just `BuildDetokLexer`. So Lemma D (which is specific to BuildDetokLexer) can't be used directly in the generic theorem.

**Key insight**: `fst_run_produces_realizable` was trying to be the generic bridge. But it's false in general. The right approach is either:
(a) Prove the generic `MaskChecker_viable_imp_char_true` with an extra hypothesis `∀ q₁ suffix qa' T, comb.evalFrom q₁ suffix = some (qa', T) → T ≠ [] → T.head ∈ comb.singleProducible q₁`, OR
(b) Prove completeness directly for `BuildDetokLexer` (not generic `comb`), using Lemma D.

Option (b) is cleaner — prove `Completeness` directly without going through the generic `MaskChecker_viable_imp_char_true`.

### Revised approach: Prove `Completeness` directly

Skip the generic `MaskChecker_viable_imp_char_true` (or add a singleProducible hypothesis to it). Prove `Completeness` (line ~903) directly for `BuildDetokLexer` using Lemma D.

### Step 2 (revised): Build the witness realizable sequence

Let `d = S ++ [T.head hne]` where `T.head hne ∈ singleProducible q₁` by Lemma D.

Show:
- `d ∈ RealizableSequences comb`: witness q₀=q_fst, t=.char cand, Ts=S, q₁, T=T.head
- `.char cand ∈ InverseTokenSpannerTable comb d q_fst`: d.dropLast = S, d.getLast = T.head, step matches

### Step 3: Parser handles `d`

From viability: `parser.evalFrom {(start,[])} (terms ++ S ++ T) ≠ ∅`

By `evalFrom_append'`: `parser.evalFrom (parser.evalFrom {(start,[])} terms) (S ++ T) ≠ ∅`

So ∃ `(qp, st)` in `parser.evalFrom {(start,[])} terms` with `parser.evalFrom {(qp,st)} (S ++ T) ≠ ∅`.

Since `S ++ T = (S ++ [T.head]) ++ T.tail = d ++ T.tail`:
By prefix closure: `parser.evalFrom {(qp,st)} d ≠ ∅`

### Step 4: Case split accepted/dependent

- If `P.evalFrom {(qp,[])} d ≠ ∅`: use accepted path
- If `P.evalFrom {(qp,[])} d = ∅`: use dependent path
  - `FinsetNFA.evalFrom P {qp} d ≠ ∅` from Lemma C + `P.evalFrom {(qp,st)} d ≠ ∅`
  - `P.evalFrom {(qp,st)} d ≠ ∅` from Step 3

### Step 5: Assemble MaskChecker = true

From `mem_ComputeValidTokenMask_preprocess_iff`, we have `cand ∈ ComputeValidTokenMask ...`.
Then unfold `MaskChecker`: `comb.eval (curr.map char) = some (q_fst, terms)`, PDA eval gives configs containing `(qp, st)`, the fold-or is true.

## Status: ✅ COMPLETE (2026-03-18)

All tasks in this phase are done. `MaskChecker_viable_imp_char_true` is fully
proved (zero sorry's).

| # | Task | Status |
|---|------|--------|
| 1 | Delete `fst_run_produces_realizable` | ✅ |
| 2 | Add `hsingle` + `hviable_tail_ne` hypotheses | ✅ |
| 3 | Decompose FST eval (Step 1) | ✅ |
| 4 | Build realizable sequence witness (Step 2) | ✅ |
| 5 | Parser prefix closure (Step 3) | ✅ |
| 6 | Case split + mask membership (Step 4) | ✅ |
| 7 | Assemble MaskChecker = true (Step 5) | ✅ |
| 8 | Verify `Completeness` compiles | ✅ Resolved (duplicated proof for concrete types) |

## Decision taken

**Generic with hypotheses**: `MaskChecker_viable_imp_char_true` stays generic
with two hypotheses:
- `hsingle`: head of nonempty output is singleton-producible
- `hviable_tail_ne`: tail output from suffix processing is nonempty

`Completeness` was resolved by duplicating the proof for concrete types
(`BuildDetokLexer` + `ParserWithEOS`) to avoid the kernel elaboration timeout.
Uses `set_option maxHeartbeats 1600000`. `EOSCompleteness` also fully proved.
