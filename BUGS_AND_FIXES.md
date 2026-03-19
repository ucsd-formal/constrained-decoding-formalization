# Bugs and Fixes Log

Tracks formalization bugs encountered during implementation and the fixes applied.

---

## Phase 1: Prefix-Closure Infrastructure

*No blocking bugs encountered. Phase completed cleanly.*

---

## Phase 2: singleProducible Nonemptiness (Case 1)

### Bug 1: `Finset.eq_empty_iff_forall_not_mem` naming
- **Symptom**: Lean couldn't find `Finset.eq_empty_iff_forall_not_mem`.
- **Cause**: Mathlib uses camelCase: `Finset.eq_empty_iff_forall_notMem`.
- **Fix**: Renamed to `Finset.eq_empty_iff_forall_notMem`. Found via `lean_loogle`.

### Bug 2: `FinsetNFA.evalFrom_empty` cons case didn't close with `simp`
- **Symptom**: `simp [FinsetNFA.evalFrom, FinsetNFA.stepSet, ih]` left goals open.
- **Cause**: `simp` couldn't chain the stepSet-on-empty reduction with the IH.
- **Fix**: Manual unfolding: `simp only [FinsetNFA.evalFrom, List.foldl_cons]`, then `have : stepSet p {} h = {} := by simp [stepSet]`, then `rw [this]; exact ih`.

### Bug 3: `omit [DecidableEq Γ] in` placement
- **Symptom**: Parse error when `omit` came after docstring.
- **Cause**: `omit ... in` must precede the docstring, not follow it.
- **Fix**: Reorder to `omit ... in /-- ... -/ lemma ...`.

### Bug 4: Forward reference to private helpers
- **Symptom**: `find_first_nonempty`, `empty_prefix_all_empty`, `first_eq_head_of_first_nonempty` not in scope.
- **Cause**: These are `private` and defined later in the file.
- **Fix**: Moved `BuildDetokLexer_singleProducible_of_evalFrom` to after these helpers (~line 1822).

### Bug 5: `min` in `List.length_take` not simplifying
- **Symptom**: After `simp [List.length_take, Nat.min_eq_left hlt]`, the `min` remained in the step list take length.
- **Cause**: `hlt` had type `↑firstIdx + 1 ≤ ws.length` but the min involved `firstIdx.toNat + 1`; `simp` couldn't unify the coercion forms.
- **Fix**: Used `some (take wfinal.length step_list)` pattern (matching the working code at line ~2166) instead of trying to eagerly simplify the min. Deferred min simplification to a separate `h_wfinal_len` lemma.

### Bug 6: `produce` vs `fun x => x.2.2.2` — function extensionality mismatch
- **Symptom**: `convert h_prefix_empty_flat using 1; simp[produce]` either left goals or caused "no goals to be solved"; anonymous lambdas with `_` type holes caused synthesis failures.
- **Cause**: `h_prefix_empty_flat` uses `produce` (a named function with implicit params `{σ V Γ}`), while `eval_of_stepList_opaque` introduces `fun x => x.2.2.2`. Anonymous lambda `(fun (x : _ × _ × _ × List (Ch Γ)) => x.2.2.2)` couldn't synthesize the `_` implicit args.
- **Fix**: Proved `h_produce_eq : (fun (x : (Unit × LexingState σ) × V × (Unit × LexingState σ) × List (Ch Γ)) => x.2.2.2) = produce := rfl` with concrete types, then used `rw[h_produce_eq, h_prefix_empty_flat, ...]`.

### Bug 7: Fin vs Nat `GetElem` indexing — `rw` pattern mismatch
- **Symptom**: `rw[←hprod_eq]` failed: couldn't find `step_list[firstIdx].2.2.2` in target `step_list[↑firstIdx].2.2.2 = [t]`.
- **Cause**: `step_list[firstIdx]` (Fin-indexed via `GetElem List (Fin n)`) and `step_list[↑firstIdx]` (Nat-indexed via `GetElem List Nat`) are definitionally equal (`rfl` proves it) but `rw` uses syntactic matching and treats them as distinct.
- **Fix**: Proved a Nat-indexed version `hprod_nat : step_list[↑firstIdx].2.2.2 = [t]` using `have : step_list[↑firstIdx] = step_list[firstIdx] := rfl; rw[this, ←hprod_eq]; exact ht`, then used `hprod_nat` directly.

### Bug 8: Dependent type in `List.head` blocks `rw`
- **Symptom**: `rw[hprod_nat]` on goal `step_list[...].2.2.2.head hft_ne = t` failed with "motive is not type correct" — the proof `hft_ne : produce step_list[firstIdx] ≠ []` depends on the term being rewritten.
- **Cause**: `List.head` takes a proof `h : l ≠ []`. When `rw` abstracts `l` to create the motive `fun _a => _a.head h = t`, the proof `h` no longer type-checks for generic `_a`.
- **Fix**: Universally quantified helper: `have : ∀ (l : List (Ch Γ)) (hl : l ≠ []), l = [t] → l.head hl = t := by intros l hl heq; subst heq; rfl`. Then applied: `exact this _ hft_ne hprod_t`.

---

## Phase 2: singleProducible Nonemptiness (Case 2 — EOS)

### Design Decision: `hrestart` hypothesis
- **Problem**: When the lexer's first emission is the two-symbol EOS pattern `[char t, eos]`, there is no direct way to produce just `[char t]` (one symbol) as a singleton-producible witness.
- **Root cause**: The EOS step always emits two symbols. If the accepting state has outgoing transitions on ALL characters, then every `char c` input extends the lexeme (output `[]`) rather than triggering the restart path that produces `[char t]`.
- **Resolution**: Added hypothesis `hrestart : ∀ s ∈ spec.automaton.accept, ∃ c : α, spec.automaton.step s c = none ∧ (spec.automaton.step spec.automaton.start c).isSome`. This guarantees a restart character exists for every accepting state. The proof uses `vocab.embed (.char c)` as a replacement token, triggering the restart path (line 246-248 of `BuildLexingFST`) which outputs `[ExtChar.char t]`.
- **Justification**: Holds for all practical lexer specs — documented in README and theorem docstring.
