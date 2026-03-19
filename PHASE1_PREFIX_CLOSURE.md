# Phase 1: Prefix-Closure Infrastructure — Detailed Subplan

**Parent plan**: COMPLETENESS_PROOF_PLAN.md, Phase 1 + Lemma C from the dependency chain
**Goal**: Prove the three prefix-closure families (NFA, PDA, NFA⊇PDA) that gate the completeness assembly in Phase 4.

---

## Scope

This phase covers tasks 1–3 from the execution table:

| Task | Lemma | Est. |
|------|-------|------|
| 1 | NFA `evalFrom_append`, `evalFrom_empty`, `evalFrom_prefix_nonempty` | 15m |
| 2 | PDA `evalFrom_append'`, `evalFrom_prefix_nonempty` | 10m |
| 3 | NFA ⊇ PDA reachability | 30m |

**Total estimated**: ~55 min
**No external dependencies** — all three tasks are parallelizable.

---

## Existing Infrastructure (what we already have)

| Lemma | File | Line | Status |
|-------|------|------|--------|
| `FST.evalFrom_append` | Automata.lean | 530 | ✅ Proved |
| `FSA.evalFrom_append` | Automata.lean | 65 | ✅ Proved |
| `PDA.evalFrom_none` | PDA.lean | 126 | ✅ Proved (`P.evalFrom {} w = {}`) |
| `PDA.fullStep_none` | PDA.lean | ~90 | ✅ Proved |
| `PDA.evalFrom_cons` | PDA.lean | 122 | ✅ Proved |
| `PDA.overApproximationLemma` | PDA.lean | 255 | ✅ Proved (PDA run → NFA run on `.image Prod.fst`) |
| `FinsetNFA.evalFrom` | GCD.lean | 68 | ✅ Defined as `List.foldl (stepSet p) q s` |
| `FinsetNFA.finsetEvalFrom_iff_evalFrom` | GCD.lean | 73 | ✅ Proved (finset ↔ NFA evaluator) |

---

## Task 1: NFA Prefix-Closure Lemmas

**File**: `GrammarConstrainedDecoding.lean`, in the `FinsetNFA` namespace (after line 86, before `end FinsetNFA` or after it if the namespace is already closed).

### 1a. `FinsetNFA.evalFrom_append`

**Statement**:
```lean
lemma FinsetNFA.evalFrom_append (p : PDA Γ π σp) (S : Finset σp)
    (xs ys : List Γ) :
    FinsetNFA.evalFrom p S (xs ++ ys) =
      FinsetNFA.evalFrom p (FinsetNFA.evalFrom p S xs) ys
```

**Proof strategy**: Unfold `FinsetNFA.evalFrom` to `List.foldl`, then apply `List.foldl_append`.

**Expected proof**:
```lean
by simp [FinsetNFA.evalFrom, List.foldl_append]
```

**Placement**: Inside the `FinsetNFA` namespace block (before `end FinsetNFA` at line 86). If the namespace is already closed, reopen it or place right after with qualified name.

### 1b. `FinsetNFA.evalFrom_empty`

**Statement**:
```lean
@[simp]
lemma FinsetNFA.evalFrom_empty (p : PDA Γ π σp) (w : List Γ) :
    FinsetNFA.evalFrom p ∅ w = ∅
```

**Proof strategy**: Induction on `w`. Base: `foldl _ ∅ [] = ∅`. Step: `stepSet p ∅ h = ∅` (biUnion over empty is empty), then apply IH.

**Expected proof**:
```lean
by
  induction w with
  | nil => simp [FinsetNFA.evalFrom]
  | cons h t ih =>
    simp [FinsetNFA.evalFrom, FinsetNFA.stepSet, ih]
```

**Note**: The `cons` case needs `Finset.biUnion_empty` to close `stepSet p ∅ h = ∅`. Check that `simp` picks this up; if not, add `Finset.biUnion_empty` to the simp set.

### 1c. `FinsetNFA.evalFrom_prefix_nonempty`

**Statement**:
```lean
lemma FinsetNFA.evalFrom_prefix_nonempty (p : PDA Γ π σp) (S : Finset σp)
    (xs ys : List Γ) :
    FinsetNFA.evalFrom p S (xs ++ ys) ≠ ∅ →
      FinsetNFA.evalFrom p S xs ≠ ∅
```

**Proof strategy**: Contrapositive — if the prefix result is `∅`, then by `evalFrom_empty` the full result is `∅`.

**Expected proof**:
```lean
by
  intro h habs
  rw [FinsetNFA.evalFrom_append, habs, FinsetNFA.evalFrom_empty] at h
  exact h rfl
```

**Dependencies**: 1a (`evalFrom_append`) and 1b (`evalFrom_empty`).

### Verification

After adding all three, run:
```bash
lake build ConstrainedDecodingFormalization.GrammarConstrainedDecoding
```
Check no `sorry` was introduced and no errors in the new lemmas.

---

## Task 2: PDA Prefix-Closure Lemmas

**File**: `PDA.lean` (preferred, near line 132 after `evalFrom_none`) or `GrammarConstrainedDecoding.lean`.

### 2a. `PDA.evalFrom_append'`

**Statement**:
```lean
lemma PDA.evalFrom_append' (P : PDA Γ π σp) (S : Finset (σp × List π))
    (xs ys : List Γ) :
    P.evalFrom S (xs ++ ys) = P.evalFrom (P.evalFrom S xs) ys
```

**Proof strategy**: Same as NFA — unfold `evalFrom` to foldl, apply `List.foldl_append`.

**Expected proof**:
```lean
by simp [PDA.evalFrom, List.foldl_append]
```

**Note**: `PDA.evalFrom` is defined as `List.foldl (fun s a => fullStep P s a) s` (PDA.lean:114). The `List.foldl_append` lemma should work directly. If `simp` doesn't close it, try `rfl` or `exact List.foldl_append ..`.

### 2b. `PDA.evalFrom_prefix_nonempty`

**Statement**:
```lean
lemma PDA.evalFrom_prefix_nonempty (P : PDA Γ π σp)
    (S : Finset (σp × List π)) (xs ys : List Γ) :
    P.evalFrom S (xs ++ ys) ≠ ∅ → P.evalFrom S xs ≠ ∅
```

**Proof strategy**: Identical to the NFA case: contrapositive using `evalFrom_append'` + `evalFrom_none`.

**Expected proof**:
```lean
by
  intro h habs
  rw [PDA.evalFrom_append', habs, PDA.evalFrom_none] at h
  exact h rfl
```

**Dependencies**: 2a (`evalFrom_append'`) and existing `PDA.evalFrom_none`.

### Verification

```bash
lake build ConstrainedDecodingFormalization.PDA
```

---

## Task 3: NFA Overapproximates PDA Reachability

**File**: `GrammarConstrainedDecoding.lean` (after the FinsetNFA lemmas).

### Statement

```lean
lemma PDA.evalFrom_nonempty_imp_nfa_nonempty (P : PDA Γ π σp)
    (qp : σp) (st : List π) (w : List Γ) :
    P.evalFrom {(qp, st)} w ≠ ∅ →
      FinsetNFA.evalFrom P {qp} w ≠ ∅
```

### Proof strategy

This is the most involved lemma in Phase 1. Two approaches:

**Approach A (via `overApproximationLemma` + `finsetEvalFrom_iff_evalFrom`)**:

1. From `P.evalFrom {(qp, st)} w ≠ ∅`, extract a witness `(s', st') ∈ P.evalFrom {(qp, st)} w`.
2. By `PDA.overApproximationLemma` (PDA.lean:255): `s' ∈ P.toNFA.evalFrom ({(qp, st)}.image Prod.fst) w`.
3. Simplify: `{(qp, st)}.image Prod.fst = {qp}`.
4. By `finsetEvalFrom_iff_evalFrom` (GCD.lean:73): `s' ∈ FinsetNFA.evalFrom P {qp} w`.
5. Therefore `FinsetNFA.evalFrom P {qp} w ≠ ∅`.

**Proof sketch**:
```lean
by
  intro hne
  rw [Finset.ne_empty_iff_exists_mem] at hne ⊢  -- or use nonempty_iff
  obtain ⟨⟨s', st'⟩, hmem⟩ := hne
  have := PDA.overApproximationLemma P w {(qp, st)} s' st' hmem
  simp at this
  exact ⟨s', (FinsetNFA.finsetEvalFrom_iff_evalFrom P {qp} w s').mpr this⟩
```

**Potential issues**:
- `Finset.ne_empty_iff_exists_mem` may be named differently; alternatives: `Finset.nonempty_iff_ne_empty`, `Finset.exists_mem_of_ne_empty`.
- The `image Prod.fst` simplification: `{(qp, st)}.image Prod.fst = {qp}` should be handled by `simp`.
- Universe polymorphism: ensure the type variables line up between the PDA and FinsetNFA namespaces.

**Fallback approach B (direct induction)**:

If approach A has universe/instance issues, prove directly by induction on `w`, using:
- Base: both are singletons, trivial.
- Step: if PDA takes a step and produces nonempty configs, then NFA step on the projected control states is also nonempty (since every PDA transition projects to an NFA transition via `toNFA`).

### Generalization (optional but useful)

A more general version that Phase 4 might need:

```lean
lemma PDA.evalFrom_nonempty_imp_nfa_nonempty' (P : PDA Γ π σp)
    (S : Finset (σp × List π)) (w : List Γ) :
    P.evalFrom S w ≠ ∅ →
      FinsetNFA.evalFrom P (S.image Prod.fst) w ≠ ∅
```

This follows by the same argument. Prove this first if it simplifies things; the singleton version is a corollary.

### Verification

```bash
lake build ConstrainedDecodingFormalization.GrammarConstrainedDecoding
```

---

## Combined Verification

After all three tasks, run a full project build:
```bash
lake build ConstrainedDecodingFormalization
```

Check that no new `sorry`s were introduced with:
```bash
grep -n "sorry" ConstrainedDecodingFormalization/PDA.lean ConstrainedDecodingFormalization/GrammarConstrainedDecoding.lean
```

---

## Outputs / Deliverables

Upon completion, the following lemmas are available for Phase 4 (completeness assembly):

| Lemma | Used in completeness for... |
|-------|-----------------------------|
| `FinsetNFA.evalFrom_append` | Decomposing NFA eval of `S ++ [T.head]` from `S ++ T` |
| `FinsetNFA.evalFrom_empty` | Supporting `evalFrom_prefix_nonempty` |
| `FinsetNFA.evalFrom_prefix_nonempty` | Showing NFA accepts `d = S ++ [T']` given it accepts `S ++ T` |
| `PDA.evalFrom_append'` | Decomposing PDA eval of `S ++ [T.head]` from `S ++ T` |
| `PDA.evalFrom_prefix_nonempty` | Showing PDA accepts `d` from actual stack given full viability |
| `PDA.evalFrom_nonempty_imp_nfa_nonempty` | Bridging PDA viability → NFA nonemptiness for the preprocessing bucket check |

These six lemmas, together with the existing `overApproximationLemma` and `finsetEvalFrom_iff_evalFrom`, fully resolve **Sub-problem B** (parser handles `S ++ [T']`) from CRITICAL.md §4.

---

## What's NOT in scope

- Lemma D (`singleProducible` nonemptiness) — Phase 2
- The `T = []` edge case — Phase 3
- Deleting `fst_run_produces_realizable` or modifying `MaskChecker_viable_imp_char_true` — Phase 4
- `GCDChecker_sound` / `GCDChecker_complete` — Phase 5
