import ConstrainedDecodingFormalization.PDA
import ConstrainedDecodingFormalization.Lexing
import ConstrainedDecodingFormalization.RealizableSequence
import ConstrainedDecodingFormalization.Vocabulary
import ConstrainedDecodingFormalization.Checker

/-!
# Grammar-constrained decoding

This file assembles the main constructions of the development. It combines a
detokenizing lexer FST with a pushdown parser, precomputes one-step parser/FST
interaction tables, and turns them into an executable valid-token checker.

The central flow is:

`LexerSpec` + `Vocabulary` + `PDA`
→ `PreprocessParser`
→ `ComputeValidTokenMask`
→ `MaskChecker` / `GCDChecker`.
-/

universe u v w x y z
variable {α : Type u} {β : Type x} {Γ : Type y} {π : Type v} {σp : Type w} {σa : Type z}

variable
  [FinEnum σp] [FinEnum Γ] [FinEnum α] [FinEnum σa] [FinEnum π]
  [DecidableEq σp] [DecidableEq β] [DecidableEq Γ] [DecidableEq α] [DecidableEq π]

/-- The preprocessing table indexed by parser state and automaton state.

For each pair of states it stores:

* accepted next tokens,
* dependent realizable sequences,
* all realizable sequences accepted from the parser state with empty stack.
-/
abbrev PPTable (α σp σa Γ) := (σp → σa → (List α × List (List Γ) × List (List Γ)))

-- TODO: replace this ad hoc EOS-extension with a cleaner construction.
/-- Extend a token PDA with EOS so it can be composed with lexer outputs over
`Ch Γ`. -/
def ParserWithEOS (p : PDA Γ π σp) : PDA (Ch Γ) π (Ch σp) :=
  let start := ExtChar.char p.start
  let accept := ExtChar.eos
  let step := fun s c =>
    match s, c with
    | .char s, .char c =>
      (p.step s c).image (fun (spt, spr, s) => (spt, spr, ExtChar.char s))
    | .char s, .eos =>
      if s ∈ p.accept then
        { ([], [], accept) }
      else
        ∅
    | .eos, _ => {([], [], .eos)}

  ⟨start, step, {accept}⟩


-- TODO is there a better way to avoid this mess?
namespace FinsetNFA

/-- One NFA-style step on the control-state projection of a PDA. -/
def stepSet (p: PDA Γ π σp) (q : Finset σp) (s : Γ) : Finset σp :=
  Finset.biUnion q (fun q' => (p.step q' s).image fun x => x.2.2)

/-- Fold `stepSet` over a word. This is the finite-set presentation of the
parser overapproximation. -/
def evalFrom (p : PDA Γ π σp) (q : Finset σp) (s : List Γ) : Finset σp :=
  List.foldl (stepSet p) q s

omit [DecidableEq Γ] [DecidableEq π]
/-- The finite-set evaluator agrees with the NFA obtained from `PDA.toNFA`. -/
theorem finsetEvalFrom_iff_evalFrom (p: PDA Γ π σp) (q : Finset σp) (s : List Γ) :
  ∀ u, u ∈ FinsetNFA.evalFrom p q s ↔ u ∈ p.toNFA.evalFrom q s := by
  intro u
  simp[NFA.evalFrom, FinsetNFA.evalFrom]
  induction s generalizing q
  case nil => simp
  case cons h t ih =>
    simp[stepSet, NFA.stepSet]
    suffices
      (q.biUnion fun q' => Finset.image (fun x => x.2.2) (p.step q' h)) = (⋃ s ∈ q, p.toNFA.step s h) by
      rw[←this]
      apply ih
    exact Finset.coe_biUnion
end FinsetNFA

/-- Characterize membership in a left fold of list concatenation with an
arbitrary initial accumulator. -/
lemma mem_foldl_append_iff_acc {δ : Type _} (x : δ) :
  ∀ acc : List δ, ∀ xs : List (List δ),
    x ∈ xs.foldl List.append acc ↔ x ∈ acc ∨ ∃ ys ∈ xs, x ∈ ys := by
  intro acc xs
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      simp [List.foldl_cons, ih, or_assoc, or_left_comm, or_comm]

lemma mem_foldl_append_iff {δ : Type _} (x : δ) (xs : List (List δ)) :
  x ∈ xs.foldl List.append [] ↔ ∃ ys ∈ xs, x ∈ ys := by
  simpa using (mem_foldl_append_iff_acc (x := x) ([] : List δ) xs)

lemma mem_foldl_append_if_iff {δ ε : Type _} (x : δ) (f : ε → List δ) (p : ε → Prop)
  [DecidablePred p] :
  ∀ acc : List δ, ∀ xs : List ε,
    x ∈ xs.foldl (fun acc y => if p y then acc ++ f y else acc) acc ↔
      x ∈ acc ∨ ∃ y ∈ xs, p y ∧ x ∈ f y := by
  intro acc xs
  induction xs generalizing acc with
  | nil =>
      simp
  | cons y ys ih =>
      by_cases hy : p y
      · simp [List.foldl_cons, hy, ih, List.mem_append, or_assoc]
      · simp [List.foldl_cons, hy, ih]

/-- Removing an element from a nodup list removes that element. -/
lemma not_mem_erase_of_nodup {δ : Type _} [BEq δ] [LawfulBEq δ] {x : δ} {l : List δ}
  (h : l.Nodup) : x ∉ l.erase x := by
  induction l with
  | nil => simp
  | cons y ys ih =>
      rcases List.nodup_cons.1 h with ⟨hnot, hndys⟩
      by_cases hyx : y = x
      · subst hyx
        simpa [List.erase_cons_head] using hnot
      · have hbeq : ¬ (y == x) = true := by
          intro hb
          exact hyx (LawfulBEq.eq_of_beq hb)
        have hxy : x ≠ y := fun hxy => hyx hxy.symm
        simp [List.erase_cons_tail, hbeq, hxy, ih hndys]

lemma mem_diff_iff_of_nodup {δ : Type _} [BEq δ] [LawfulBEq δ] {x : δ} {l₁ l₂ : List δ}
  (hnd : l₁.Nodup) : x ∈ l₁.diff l₂ ↔ x ∈ l₁ ∧ x ∉ l₂ := by
  induction l₂ generalizing l₁ with
  | nil => simp
  | cons y ys ih =>
      rw [List.diff_eq_foldl, List.foldl_cons, ← List.diff_eq_foldl (l₁.erase y) ys]
      have hnd' : (l₁.erase y).Nodup := List.Nodup.erase y hnd
      rw [ih hnd']
      by_cases hxy : x = y
      · subst hxy
        constructor
        · intro h
          rcases h with ⟨hmem, _⟩
          exact False.elim ((not_mem_erase_of_nodup hnd) hmem)
        · intro h
          rcases h with ⟨_, hnot⟩
          exact False.elim (hnot List.mem_cons_self)
      · simp [List.mem_erase_of_ne hxy, hxy, List.mem_cons]

lemma nodup_eraseDups {δ : Type _} [BEq δ] [LawfulBEq δ] :
  ∀ l : List δ, l.eraseDups.Nodup := by
  intro l
  let P : Nat → Prop := fun n => ∀ l : List δ, l.length = n → l.eraseDups.Nodup
  have hstep : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih l hlen
    cases l with
    | nil => simp
    | cons a as =>
        rw [List.eraseDups_cons]
        refine List.nodup_cons.2 ?_
        constructor
        · intro hm
          rw [List.mem_eraseDups] at hm
          simp at hm
        · have hn : n = as.length + 1 := by simpa using hlen.symm
          have hlt' : as.length < n := by
            calc
              as.length < as.length + 1 := Nat.lt_succ_self _
              _ = n := hn.symm
          have hlt : (List.filter (fun b => !b == a) as).length < n := by
            exact lt_of_le_of_lt (List.length_filter_le _ _) hlt'
          exact ih _ hlt _ rfl
  have hP : P l.length := Nat.strongRecOn l.length hstep
  exact hP l rfl

/-- Precompute the parser/FST interaction table for grammar-constrained
decoding.

For each parser state `qp` and automaton state `qa`, this separates realizable
output sequences into immediately accepted ones, immediately rejected ones, and
dependent ones whose acceptance depends on the current stack.
-/
def PreprocessParser (fst_comp : FST α Γ σa) (p : PDA Γ π σp) : PPTable α σp σa Γ :=
  let (re, tist) := BuildInverseTokenSpannerTable fst_comp
  fun qp =>
    let accepted := re.filter (λ s => (p.evalFrom {(qp, [])} s) ≠  ∅)
    let rejected := re.filter (λ s => FinsetNFA.evalFrom p {qp} s = ∅)

    let dependent := List.diff (List.diff re accepted) rejected
    fun qa =>
      let accepted_a := (accepted.map (fun tok => (tist tok qa))).foldl List.append []
      let accepted_a := accepted_a.dedup
      let dependent_a := dependent.filter (fun tok => (tist tok qa) ≠ [])
      let dependent_a := dependent_a.dedup
      (accepted_a, dependent_a, accepted)

/-- Characterize the realizable sequences that land in the "accepted" part of
`PreprocessParser`. -/
lemma mem_preprocess_accepted_sequences_iff
  (fst_comp : FST α Γ σa) (p : PDA Γ π σp) (qp : σp) (qa : σa) (d : List Γ) :
  d ∈ (PreprocessParser fst_comp p qp qa).2.2 ↔
    d ∈ RealizableSequences fst_comp ∧
    p.evalFrom {(qp, [])} d ≠ ∅ := by
  constructor
  · intro hd
    have hacc :
        d ∈ (BuildInverseTokenSpannerTable fst_comp).fst ∧
        p.evalFrom {(qp, [])} d ≠ ∅ := by
      simpa [PreprocessParser, List.mem_filter] using hd
    exact ⟨(mem_re_iff (fst_comp := fst_comp) (d := d)).1 hacc.1, hacc.2⟩
  · rintro ⟨hd, hp⟩
    have hacc :
        d ∈ (BuildInverseTokenSpannerTable fst_comp).fst ∧
        p.evalFrom {(qp, [])} d ≠ ∅ :=
      ⟨(mem_re_iff (fst_comp := fst_comp) (d := d)).2 hd, hp⟩
    simpa [PreprocessParser, List.mem_filter] using hacc

omit [DecidableEq π] in
lemma mem_rejected_sequences_iff
  (fst_comp : FST α Γ σa) (p : PDA Γ π σp) (qp : σp) (d : List Γ) :
  d ∈ ((BuildInverseTokenSpannerTable fst_comp).fst.filter
      (fun s => FinsetNFA.evalFrom p {qp} s = ∅)) ↔
    d ∈ RealizableSequences fst_comp ∧
    FinsetNFA.evalFrom p {qp} d = ∅ := by
  constructor
  · intro hd
    have hrej :
        d ∈ (BuildInverseTokenSpannerTable fst_comp).fst ∧
        FinsetNFA.evalFrom p {qp} d = ∅ := by
      simpa [List.mem_filter] using hd
    exact ⟨(mem_re_iff (fst_comp := fst_comp) (d := d)).1 hrej.1, hrej.2⟩
  · rintro ⟨hd, hrej⟩
    have hmem :
        d ∈ (BuildInverseTokenSpannerTable fst_comp).fst ∧
        FinsetNFA.evalFrom p {qp} d = ∅ :=
      ⟨(mem_re_iff (fst_comp := fst_comp) (d := d)).2 hd, hrej⟩
    simpa [List.mem_filter] using hmem

/-- Characterize the accepted next tokens extracted by `PreprocessParser`. -/
lemma mem_preprocess_accepted_tokens_iff
  [BEq α] [ReflBEq α] [LawfulBEq α]
  (fst_comp : FST α Γ σa) (p : PDA Γ π σp) (qp : σp) (qa : σa) (tok : α) :
  tok ∈ (PreprocessParser fst_comp p qp qa).1 ↔
    ∃ d,
      d ∈ RealizableSequences fst_comp ∧
      p.evalFrom {(qp, [])} d ≠ ∅ ∧
      tok ∈ InverseTokenSpannerTable fst_comp d qa := by
  constructor
  · intro h
    have hmem :
        tok ∈
          ((List.map (fun d => (BuildInverseTokenSpannerTable fst_comp).snd d qa)
            (((BuildInverseTokenSpannerTable fst_comp).fst).filter
              (fun s => p.evalFrom {(qp, [])} s ≠ ∅))).foldl List.append []).dedup := by
      simpa [PreprocessParser] using h
    rw [List.mem_dedup] at hmem
    rcases (mem_foldl_append_iff tok _).1 hmem with ⟨ys, hys, htok⟩
    rcases (List.mem_map.1 hys) with ⟨d, hdacc, hysEq⟩
    have htok' : tok ∈ (BuildInverseTokenSpannerTable fst_comp).snd d qa := by
      simpa [hysEq] using htok
    refine ⟨d, ?_, ?_, ?_⟩
    · exact (mem_preprocess_accepted_sequences_iff
        (fst_comp := fst_comp) (p := p) (qp := qp) (qa := qa) (d := d)).1 hdacc |>.1
    · exact (mem_preprocess_accepted_sequences_iff
        (fst_comp := fst_comp) (p := p) (qp := qp) (qa := qa) (d := d)).1 hdacc |>.2
    · exact (mem_itst_iff (fst_comp := fst_comp) (d := d) (qa := qa) (tok := tok)).1 htok'
  · rintro ⟨d, hrs, hp, hitst⟩
    have hdacc :
        d ∈ ((BuildInverseTokenSpannerTable fst_comp).fst).filter
          (fun s => p.evalFrom {(qp, [])} s ≠ ∅) := by
      exact (mem_preprocess_accepted_sequences_iff
        (fst_comp := fst_comp) (p := p) (qp := qp) (qa := qa) (d := d)).2 ⟨hrs, hp⟩
    have hys :
        (BuildInverseTokenSpannerTable fst_comp).snd d qa ∈
          List.map (fun d => (BuildInverseTokenSpannerTable fst_comp).snd d qa)
            (((BuildInverseTokenSpannerTable fst_comp).fst).filter
              (fun s => p.evalFrom {(qp, [])} s ≠ ∅)) := by
      exact List.mem_map.2 ⟨d, hdacc, rfl⟩
    have htok :
        tok ∈
          (List.map (fun d => (BuildInverseTokenSpannerTable fst_comp).snd d qa)
            (((BuildInverseTokenSpannerTable fst_comp).fst).filter
              (fun s => p.evalFrom {(qp, [])} s ≠ ∅))).foldl List.append [] := by
      exact (mem_foldl_append_iff tok _).2
        ⟨(BuildInverseTokenSpannerTable fst_comp).snd d qa, hys,
          (mem_itst_iff (fst_comp := fst_comp) (d := d) (qa := qa) (tok := tok)).2 hitst⟩
    have hdedup :
        tok ∈
          ((List.map (fun d => (BuildInverseTokenSpannerTable fst_comp).snd d qa)
            (((BuildInverseTokenSpannerTable fst_comp).fst).filter
              (fun s => p.evalFrom {(qp, [])} s ≠ ∅))).foldl List.append []).dedup := by
      rw [List.mem_dedup]
      exact htok
    simpa [PreprocessParser] using hdedup

/-- Characterize the "dependent" realizable sequences whose acceptance depends
on the current stack contents. -/
lemma mem_preprocess_dependent_sequences_iff
  (fst_comp : FST α Γ σa) (p : PDA Γ π σp) (qp : σp) (qa : σa) (d : List Γ) :
  d ∈ (PreprocessParser fst_comp p qp qa).2.1 ↔
    d ∈ RealizableSequences fst_comp ∧
    p.evalFrom {(qp, [])} d = ∅ ∧
    FinsetNFA.evalFrom p {qp} d ≠ ∅ ∧
    (BuildInverseTokenSpannerTable fst_comp).snd d qa ≠ [] := by
  let re := (BuildInverseTokenSpannerTable fst_comp).fst
  let accepted := re.filter (fun s => p.evalFrom {(qp, [])} s ≠ ∅)
  let rejected := re.filter (fun s => FinsetNFA.evalFrom p {qp} s = ∅)
  let dependent := List.diff (List.diff re accepted) rejected
  have hre_nodup : re.Nodup := by
    unfold re
    simpa [BuildInverseTokenSpannerTable] using
      (nodup_eraseDups
        ((FinEnum.toList (α := σa)).flatMap (fun q =>
          (FinEnum.toList (α := α)).flatMap (fun c =>
            match fst_comp.step q c with
            | none => []
            | some (q', Ts) =>
              (fst_comp.computeSingleProducible q').map (fun t => Ts ++ [t])))))
  have hdep0_nodup : (List.diff re accepted).Nodup :=
    List.Nodup.diff (l₂ := accepted) hre_nodup
  constructor
  · intro hd
    have hdep :
        d ∈ dependent ∧ (BuildInverseTokenSpannerTable fst_comp).snd d qa ≠ [] := by
      simpa [PreprocessParser, re, accepted, rejected, dependent, List.mem_filter, List.mem_dedup] using hd
    have hdiff2 := (mem_diff_iff_of_nodup
      (x := d) (l₁ := List.diff re accepted) (l₂ := rejected) hdep0_nodup).1 hdep.1
    have hdiff1 := (mem_diff_iff_of_nodup (x := d) (l₁ := re) (l₂ := accepted) hre_nodup).1 hdiff2.1
    refine ⟨(mem_re_iff (fst_comp := fst_comp) (d := d)).1 hdiff1.1, ?_, ?_, hdep.2⟩
    · by_cases hp0 : p.evalFrom {(qp, [])} d = ∅
      · exact hp0
      · exfalso
        exact hdiff1.2 ((mem_preprocess_accepted_sequences_iff
          (fst_comp := fst_comp) (p := p) (qp := qp) (qa := qa) (d := d)).2
            ⟨(mem_re_iff (fst_comp := fst_comp) (d := d)).1 hdiff1.1, hp0⟩)
    · by_cases hrej : FinsetNFA.evalFrom p {qp} d = ∅
      · exfalso
        exact hdiff2.2 ((mem_rejected_sequences_iff
          (fst_comp := fst_comp) (p := p) (qp := qp) (d := d)).2
            ⟨(mem_re_iff (fst_comp := fst_comp) (d := d)).1 hdiff1.1, hrej⟩)
      · exact hrej
  · rintro ⟨hrs, hp0, hrej, hitst⟩
    have hre : d ∈ re := (mem_re_iff (fst_comp := fst_comp) (d := d)).2 hrs
    have hnotacc : d ∉ accepted := by
      intro hacc
      have hacc' := (mem_preprocess_accepted_sequences_iff
        (fst_comp := fst_comp) (p := p) (qp := qp) (qa := qa) (d := d)).1 hacc
      exact hacc'.2 hp0
    have hnotrej : d ∉ rejected := by
      intro hmem
      have hrej' := (mem_rejected_sequences_iff
        (fst_comp := fst_comp) (p := p) (qp := qp) (d := d)).1 hmem
      exact hrej hrej'.2
    have hdep0 : d ∈ List.diff re accepted := List.mem_diff_of_mem hre hnotacc
    have hdep : d ∈ dependent := List.mem_diff_of_mem hdep0 hnotrej
    have hdepf :
        d ∈ dependent.filter (fun tok => (BuildInverseTokenSpannerTable fst_comp).snd tok qa ≠ []) := by
      simpa [List.mem_filter] using And.intro hdep hitst
    simpa [PreprocessParser, re, accepted, rejected, dependent, List.mem_filter, List.mem_dedup] using hdepf

/-- Compute the valid next-token mask for a given parser state, automaton state,
and current parser stack. -/
def ComputeValidTokenMask (P : PDA Γ π σp) (itst : List Γ → σa → List α)
  (table : PPTable α σp σa Γ) (qa : σa) (qp : σp) (st : List π) : List α :=
  let accepted := (table qp qa).fst
  let dependent := (table qp qa).2.1
  let accepted :=
    dependent.foldl
      (fun acc d =>
        if (P.evalFrom {(qp, st)} d) ≠ ∅ then
          acc ++ (itst d qa)
        else
          acc)
      accepted
  accepted.dedup

omit [FinEnum α] [FinEnum σa] [DecidableEq Γ] in
/-- Membership in `ComputeValidTokenMask` is exactly membership in either the
preaccepted token list or a dependent sequence that succeeds on the current
stack. -/
lemma mem_ComputeValidTokenMask_iff
  [BEq α] [ReflBEq α] [LawfulBEq α]
  (P : PDA Γ π σp) (itst : List Γ → σa → List α) (table : PPTable α σp σa Γ)
  (qa : σa) (qp : σp) (st : List π) (tok : α) :
  tok ∈ ComputeValidTokenMask P itst table qa qp st ↔
    tok ∈ (table qp qa).fst ∨
      ∃ d ∈ (table qp qa).2.1, P.evalFrom {(qp, st)} d ≠ ∅ ∧ tok ∈ itst d qa := by
  rw [ComputeValidTokenMask, List.mem_dedup]
  simpa using
    (mem_foldl_append_if_iff
      (x := tok)
      (f := fun d => itst d qa)
      (p := fun d => P.evalFrom {(qp, st)} d ≠ ∅)
      ((table qp qa).fst)
      ((table qp qa).2.1))

/-- Specialize `mem_ComputeValidTokenMask_iff` to the preprocessing table built
from an FST and a PDA. -/
lemma mem_ComputeValidTokenMask_preprocess_iff
  [BEq α] [ReflBEq α] [LawfulBEq α]
  (fst_comp : FST α Γ σa) (P : PDA Γ π σp) (qa : σa) (qp : σp) (st : List π) (tok : α) :
  tok ∈ ComputeValidTokenMask P (BuildInverseTokenSpannerTable fst_comp).snd
      (PreprocessParser fst_comp P) qa qp st ↔
    (∃ d,
      d ∈ RealizableSequences fst_comp ∧
      P.evalFrom {(qp, [])} d ≠ ∅ ∧
      tok ∈ InverseTokenSpannerTable fst_comp d qa) ∨
    (∃ d,
      d ∈ RealizableSequences fst_comp ∧
      P.evalFrom {(qp, [])} d = ∅ ∧
      FinsetNFA.evalFrom P {qp} d ≠ ∅ ∧
      P.evalFrom {(qp, st)} d ≠ ∅ ∧
      tok ∈ InverseTokenSpannerTable fst_comp d qa) := by
  rw [mem_ComputeValidTokenMask_iff]
  constructor
  · intro h
    rcases h with hacc | ⟨d, hddep, hcur, htok⟩
    · left
      rcases (mem_preprocess_accepted_tokens_iff
        (fst_comp := fst_comp) (p := P) (qp := qp) (qa := qa) (tok := tok)).1 hacc with
        ⟨d, hrs, hacc0, htok'⟩
      exact ⟨d, hrs, hacc0, htok'⟩
    · right
      have hdep := (mem_preprocess_dependent_sequences_iff
        (fst_comp := fst_comp) (p := P) (qp := qp) (qa := qa) (d := d)).1 hddep
      exact ⟨d, hdep.1, hdep.2.1, hdep.2.2.1, hcur,
        (mem_itst_iff (fst_comp := fst_comp) (d := d) (qa := qa) (tok := tok)).1 htok⟩
  · intro h
    rcases h with ⟨d, hrs, hacc0, htok⟩ | ⟨d, hrs, hp0, hrej, hcur, htok⟩
    · left
      exact (mem_preprocess_accepted_tokens_iff
        (fst_comp := fst_comp) (p := P) (qp := qp) (qa := qa) (tok := tok)).2
          ⟨d, hrs, hacc0, htok⟩
    · right
      refine ⟨d,
        (mem_preprocess_dependent_sequences_iff
          (fst_comp := fst_comp) (p := P) (qp := qp) (qa := qa) (d := d)).2
            ⟨hrs, hp0, hrej, ?_⟩,
        hcur,
        (mem_itst_iff (fst_comp := fst_comp) (d := d) (qa := qa) (tok := tok)).2 htok⟩
      intro hnil
      have : tok ∈ ([] : List α) := by simpa [hnil] using
        ((mem_itst_iff (fst_comp := fst_comp) (d := d) (qa := qa) (tok := tok)).2 htok)
      simp at this

/-- The combined detokenizing lexer FST used by grammar-constrained decoding. -/
abbrev GCDComb [Vocabulary α β] (spec : LexerSpec α Γ σa) :
    FST (Ch β) (Ch Γ) (Unit × LexingState σa) :=
  Detokenizing.BuildDetokLexer (V := Ch β) spec

/-- The EOS-augmented parser used by grammar-constrained decoding. -/
abbrev GCDParser (P : PDA Γ π σp) : PDA (Ch Γ) π (Ch σp) :=
  ParserWithEOS P

/-- The preprocessing table used by the full GCD checker. -/
abbrev GCDPPTable [Vocabulary α β] [FinEnum β] (P : PDA Γ π σp) (spec : LexerSpec α Γ σa) :
    PPTable (Ch β) (Ch σp) (Unit × LexingState σa) (Ch Γ) :=
  PreprocessParser (GCDComb (α := α) (β := β) spec) (GCDParser P)

/-- The inverse token-spanner table specialized to the full GCD construction. -/
abbrev GCDItst [Vocabulary α β] [FinEnum β] (spec : LexerSpec α Γ σa) :
    List (Ch Γ) → (Unit × LexingState σa) → List (Ch β) :=
  (BuildInverseTokenSpannerTable (GCDComb (α := α) (β := β) spec)).snd

/-- The generic mask checker built from a lexer/parser combination together
with its preprocessing artifacts. -/
def MaskChecker
  [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa]
  (comb : FST (Ch β) (Ch Γ) σa) (parser : PDA (Ch Γ) π σp)
  (pp_table : PPTable (Ch β) σp σa (Ch Γ))
  (itst : List (Ch Γ) → σa → List (Ch β)) : List β → Ch β → Bool :=
  fun curr cand =>
    match comb.eval (curr.map ExtChar.char) with
    | none => false
    | some (q_fst, terms) =>
      let q_pda := parser.evalFrom {(parser.start, [])} terms
      let in_curr := q_pda.image
        (fun (q_parse, st) => (ComputeValidTokenMask parser itst pp_table q_fst q_parse st).contains cand)
      Finset.fold Bool.or false id in_curr

-- TODO use more consistent notions of variable names
/-- The end-to-end grammar-constrained checker associated to a lexer
specification and a parser. -/
@[reducible] def GCDChecker
  [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
  [DecidableEq σa]
  [FinEnum β] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
  (spec: LexerSpec α Γ σa) (parser0: PDA Γ π σp) : List β → Ch β → Bool :=
  MaskChecker
    (Detokenizing.BuildDetokLexer (V := Ch β) spec)
    (ParserWithEOS parser0)
    (PreprocessParser (Detokenizing.BuildDetokLexer (V := Ch β) spec) (ParserWithEOS parser0))
    (BuildInverseTokenSpannerTable (Detokenizing.BuildDetokLexer (V := Ch β) spec)).snd

/-- Folding `Bool.or` over a finite set is true exactly when the set contains
`true`. -/
lemma Finset.fold_or_eq_true_iff (s : Finset Bool) :
  Finset.fold Bool.or false id s = true ↔ true ∈ s := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      cases a with
      | false =>
          simpa [Finset.fold_insert, ha] using ih
      | true =>
          simp [Finset.fold_insert, ha]

/-- Semantic viable-prefix predicate for the full GCD construction. -/
@[reducible] def GCDViablePrefix
  [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
  [DecidableEq σa]
  [FinEnum β] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (w : List β) : Prop :=
  ∃ suffix qa gammas,
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval
      (w.map ExtChar.char ++ suffix) = some (qa, gammas) ∧
    (ParserWithEOS P).evalFull gammas ≠ ∅

-- want to say that for any lexer state
-- any thing that starts with a realizable sequence is producible
omit [FinEnum Γ] [FinEnum α] [FinEnum σa] [DecidableEq Γ] [DecidableEq α] in
/-- Unfold `singleProducible` into an explicit singleton-output run. -/
lemma mem_singleProducible_iff_exists_evalFrom_singleton
  (fst_comp : FST α Γ σa) (q : σa) (T : Γ) :
  T ∈ fst_comp.singleProducible q ↔
    ∃ ts q', fst_comp.evalFrom q ts = some (q', [T]) := by
  simp [FST.singleProducible]

omit [FinEnum Γ] [FinEnum α] [FinEnum σa] [DecidableEq Γ] [DecidableEq α] in
/-- Any token found in the inverse token-spanner table extends to a concrete FST
run realizing the corresponding output sequence. -/
theorem realizableSequencesComplete (fst_comp : FST α Γ σa) :
  ∀ qa t gammas,
    t ∈ InverseTokenSpannerTable fst_comp gammas qa →
    ∃ ts qa', fst_comp.evalFrom qa (t :: ts) = some (qa', gammas) := by
  intro qa t gammas hitst
  have hne : gammas ≠ [] := by
    intro hnil
    subst hnil
    simp [InverseTokenSpannerTable] at hitst
  have hstep_prod :
      ∃ q1,
        fst_comp.step qa t = some (q1, gammas.dropLast) ∧
        gammas.getLast hne ∈ fst_comp.singleProducible q1 := by
    simpa [InverseTokenSpannerTable, hne] using hitst
  rcases hstep_prod with ⟨q1, hstep, hprod⟩
  rcases (mem_singleProducible_iff_exists_evalFrom_singleton
    (fst_comp := fst_comp) (q := q1) (T := gammas.getLast hne)).1 hprod with ⟨ts, qa', htail⟩
  refine ⟨ts, qa', ?_⟩
  exact (FST.evalFrom_cons_some_iff (M := fst_comp)
    (s := qa) (s'' := qa') (a := t) (as := ts) (U := gammas)).2
      ⟨q1, gammas.dropLast, [gammas.getLast hne], hstep, htail,
        (List.dropLast_append_getLast hne).symm⟩

omit [DecidableEq Γ] in
/-- Nonemptiness from the empty stack lifts to nonemptiness from any larger
stack by stack invariance. -/
lemma evalFrom_empty_stack_nonempty_any_stack
  (p : PDA Γ π σp) (q : σp) (w : List Γ) (st : List π) :
  p.evalFrom {(q, [])} w ≠ ∅ → p.evalFrom {(q, st)} w ≠ ∅ := by
  intro hnonempty hempty
  rcases Finset.nonempty_iff_ne_empty.mpr hnonempty with ⟨⟨qf, stf⟩, hmem⟩
  have hlift := p.stackInvariance_lem q [] qf stf st w (by simp) hmem
  simp [hempty] at hlift

/-- Every token admitted by the computed valid-token mask extends to a concrete
FST run whose emitted terminals remain parseable by `P`. -/
theorem accept_if_ComputedValidTokenMask
  (fst_comp : FST α Γ σa) (P : PDA Γ π σp) :
  ∀ qp st qa t,
    t ∈ ComputeValidTokenMask P (BuildInverseTokenSpannerTable fst_comp).snd
      (PreprocessParser fst_comp P) qa qp st →
    ∃ ts qa' gammas,
      fst_comp.evalFrom qa (t :: ts) = some (qa', gammas) ∧
      P.evalFrom {(qp, st)} gammas ≠ ∅ := by
  intro qp st qa t ht
  rcases (mem_ComputeValidTokenMask_preprocess_iff
    (fst_comp := fst_comp) (P := P) (qa := qa) (qp := qp) (st := st) (tok := t)).1 ht with
    ⟨gammas, _, hacc0, htok⟩ | ⟨gammas, _, _, _, hcur, htok⟩
  · rcases realizableSequencesComplete (fst_comp := fst_comp) qa t gammas htok with ⟨ts, qa', hrun⟩
    exact ⟨ts, qa', gammas, hrun,
      evalFrom_empty_stack_nonempty_any_stack P qp gammas st hacc0⟩
  · rcases realizableSequencesComplete (fst_comp := fst_comp) qa t gammas htok with ⟨ts, qa', hrun⟩
    exact ⟨ts, qa', gammas, hrun, hcur⟩

theorem MaskChecker_true_witness
  [BEq σa] [LawfulBEq σa] [FinEnum β]
  (comb : FST (Ch β) (Ch Γ) σa) (parser : PDA (Ch Γ) π σp)
  (curr : List β) (cand : Ch β)
  (h : MaskChecker comb parser (PreprocessParser comb parser)
    (BuildInverseTokenSpannerTable comb).snd curr cand = true) :
  ∃ q_fst terms qp st,
    comb.eval (curr.map ExtChar.char) = some (q_fst, terms) ∧
    (qp, st) ∈ parser.evalFrom {(parser.start, [])} terms ∧
    cand ∈ ComputeValidTokenMask parser (BuildInverseTokenSpannerTable comb).snd
      (PreprocessParser comb parser) q_fst qp st := by
  unfold MaskChecker at h
  cases hcomb : comb.eval (curr.map ExtChar.char) with
  | none =>
      have hcombFrom : comb.evalFrom comb.start (curr.map ExtChar.char) = none := by
        simpa [FST.eval] using hcomb
      have hfalse : false = true := by
        simp [hcombFrom] at h
      cases hfalse
  | some result =>
      rcases result with ⟨q_fst, terms⟩
      let qPda : Finset (σp × List π) := parser.evalFrom {(parser.start, [])} terms
      let inCurr : Finset Bool :=
        qPda.image (fun (q_parse, st) =>
          (ComputeValidTokenMask parser (BuildInverseTokenSpannerTable comb).snd
            (PreprocessParser comb parser) q_fst q_parse st).contains cand)
      have hfold : Finset.fold Bool.or false id inCurr = true := by
        simp only [hcomb] at h
        convert h
      have himg : true ∈ inCurr := (Finset.fold_or_eq_true_iff _).1 hfold
      have hwit :
          ∃ qp st,
            (qp, st) ∈ parser.evalFrom {(parser.start, [])} terms ∧
            (ComputeValidTokenMask parser (BuildInverseTokenSpannerTable comb).snd
              (PreprocessParser comb parser) q_fst qp st).contains cand = true := by
        simpa [qPda, inCurr, Finset.mem_image] using himg
      rcases hwit with ⟨qp, st, hmem, hcontains⟩
      refine ⟨q_fst, terms, qp, st, rfl, hmem, ?_⟩
      exact (List.contains_iff_mem).1 hcontains

theorem MaskChecker_char_true_imp_viable
  [BEq σa] [LawfulBEq σa] [FinEnum β]
  (comb : FST (Ch β) (Ch Γ) σa) (parser : PDA (Ch Γ) π σp)
  (curr : List β) (cand : β)
  (h : MaskChecker comb parser (PreprocessParser comb parser)
    (BuildInverseTokenSpannerTable comb).snd curr (.char cand) = true) :
  ∃ suffix qa gammas,
    comb.eval (((curr ++ [cand]).map ExtChar.char) ++ suffix) = some (qa, gammas) ∧
    parser.evalFull gammas ≠ ∅ := by
  rcases MaskChecker_true_witness
    (comb := comb) (parser := parser) (curr := curr) (cand := .char cand) h with
    ⟨q_fst, terms, qp, st, hcomb, hmem, hmask⟩
  have hmask' :
      .char cand ∈
        ComputeValidTokenMask parser (BuildInverseTokenSpannerTable comb).snd
          (PreprocessParser comb parser) q_fst qp st := by
    simpa using hmask
  rcases accept_if_ComputedValidTokenMask
    (fst_comp := comb) (P := parser) qp st q_fst (.char cand) hmask' with
    ⟨ts, qa', gammas, hrun, hparse⟩
  refine ⟨ts, qa', terms ++ gammas, ?_, ?_⟩
  · calc
      comb.eval (((curr ++ [cand]).map ExtChar.char) ++ ts)
          = comb.evalFrom comb.start (curr.map ExtChar.char ++ (.char cand :: ts)) := by
              simp [FST.eval, List.map_append, List.append_assoc]
      _ = some (qa', terms ++ gammas) := by
        have hcombFrom : comb.evalFrom comb.start (curr.map ExtChar.char) = some (q_fst, terms) := by
          simpa [FST.eval] using hcomb
        have happ := FST.evalFrom_append (M := comb) comb.start
          (curr.map ExtChar.char) (.char cand :: ts)
        rw [hcombFrom] at happ
        simp [hrun] at happ
        exact happ
  · rw [parser.evalFull_append terms gammas]
    rcases Finset.nonempty_iff_ne_empty.mpr hparse with ⟨cfg, hcfg⟩
    have hsingle :
        ({(qp, st)} : Finset (σp × List π)) ⊆ parser.evalFull terms := by
      intro x hx
      simp at hx
      rcases hx with rfl
      simpa [PDA.evalFull] using hmem
    have hcfg' : cfg ∈ parser.evalFrom (parser.evalFull terms) gammas :=
      (parser.evalFrom_subset {(qp, st)} (parser.evalFull terms) hsingle gammas) hcfg
    exact Finset.nonempty_iff_ne_empty.mp ⟨cfg, hcfg'⟩

/-- The EOS case: if the mask checker accepts `.eos`, the current token sequence
can be extended with `.eos` to form a sequence that the FST processes and the
parser accepts. -/
theorem MaskChecker_eos_true_imp_viable
  [BEq σa] [LawfulBEq σa] [FinEnum β]
  (comb : FST (Ch β) (Ch Γ) σa) (parser : PDA (Ch Γ) π σp)
  (curr : List β)
  (h : MaskChecker comb parser (PreprocessParser comb parser)
    (BuildInverseTokenSpannerTable comb).snd curr .eos = true) :
  ∃ suffix qa gammas,
    comb.eval (curr.map ExtChar.char ++ (.eos :: suffix)) = some (qa, gammas) ∧
    parser.evalFull gammas ≠ ∅ := by
  rcases MaskChecker_true_witness
    (comb := comb) (parser := parser) (curr := curr) (cand := .eos) h with
    ⟨q_fst, terms, qp, st, hcomb, hmem, hmask⟩
  have hmask' :
      ExtChar.eos ∈
        ComputeValidTokenMask parser (BuildInverseTokenSpannerTable comb).snd
          (PreprocessParser comb parser) q_fst qp st := by
    simpa using hmask
  rcases accept_if_ComputedValidTokenMask
    (fst_comp := comb) (P := parser) qp st q_fst .eos hmask' with
    ⟨ts, qa', gammas, hrun, hparse⟩
  refine ⟨ts, qa', terms ++ gammas, ?_, ?_⟩
  · calc
      comb.eval (curr.map ExtChar.char ++ (.eos :: ts))
          = comb.evalFrom comb.start (curr.map ExtChar.char ++ (.eos :: ts)) := by
              simp [FST.eval]
      _ = some (qa', terms ++ gammas) := by
        have hcombFrom : comb.evalFrom comb.start (curr.map ExtChar.char) = some (q_fst, terms) := by
          simpa [FST.eval] using hcomb
        have happ := FST.evalFrom_append (M := comb) comb.start
          (curr.map ExtChar.char) (.eos :: ts)
        rw [hcombFrom] at happ
        simp [hrun] at happ
        exact happ
  · rw [parser.evalFull_append terms gammas]
    rcases Finset.nonempty_iff_ne_empty.mpr hparse with ⟨cfg, hcfg⟩
    have hsingle :
        ({(qp, st)} : Finset (σp × List π)) ⊆ parser.evalFull terms := by
      intro x hx
      simp at hx
      rcases hx with rfl
      simpa [PDA.evalFull] using hmem
    have hcfg' : cfg ∈ parser.evalFrom (parser.evalFull terms) gammas :=
      (parser.evalFrom_subset {(qp, st)} (parser.evalFull terms) hsingle gammas) hcfg
    exact Finset.nonempty_iff_ne_empty.mp ⟨cfg, hcfg'⟩

/-- GCD-specialized EOS theorem: if the checker accepts EOS, the current token
sequence extends to a viable run through the combined FST and parser. -/
theorem GCDChecker_eos_true_imp_viable
  [BEq σa] [LawfulBEq σa] [FinEnum β] [Vocabulary α β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (curr : List β)
  (h : MaskChecker
    (Detokenizing.BuildDetokLexer (V := Ch β) spec)
    (ParserWithEOS P)
    (PreprocessParser (Detokenizing.BuildDetokLexer (V := Ch β) spec) (ParserWithEOS P))
    (BuildInverseTokenSpannerTable (Detokenizing.BuildDetokLexer (V := Ch β) spec)).snd
    curr .eos = true) :
  ∃ suffix qa gammas,
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval
      (curr.map ExtChar.char ++ (.eos :: suffix)) = some (qa, gammas) ∧
    (ParserWithEOS P).evalFull gammas ≠ ∅ :=
  MaskChecker_eos_true_imp_viable
    (comb := Detokenizing.BuildDetokLexer (V := Ch β) spec)
    (parser := ParserWithEOS P)
    (curr := curr) h

/-! ## Completeness direction

The completeness direction states: if a token extends the current prefix to a
viable one, then that token is in the computed valid-token mask.

The key structural property needed is that any FST one-step-and-tail run
produces an output that decomposes into a realizable sequence with a
corresponding inverse token-spanner entry. This requires reasoning about the
internal structure of the FST, specifically that `step` followed by
`singleProducible` captures all one-token output spans.
-/

omit [FinEnum Γ] [FinEnum α] [FinEnum σa] [DecidableEq Γ] [DecidableEq α] in
/-- Any one-step FST run decomposes into a step producing an initial output
segment followed by a singleProducible tail, yielding membership in
`InverseTokenSpannerTable` and `RealizableSequences`. -/
theorem fst_run_produces_realizable
  (fst_comp : FST α Γ σa) (qa qa' : σa) (t : α) (ts : List α) (gammas : List Γ)
  (hne : gammas ≠ [])
  (hrun : fst_comp.evalFrom qa (t :: ts) = some (qa', gammas)) :
  gammas ∈ RealizableSequences fst_comp ∧
  t ∈ InverseTokenSpannerTable fst_comp gammas qa := by
  sorry

/-- Completeness of the mask checker: if a token extends the current prefix to
a viable prefix (the FST can process the extended sequence and the parser
accepts), then that token is in the valid-token mask.

This is the reverse direction of `MaskChecker_char_true_imp_viable` and
corresponds to paper Theorem C.5. -/
theorem MaskChecker_viable_imp_char_true
  [BEq σa] [LawfulBEq σa] [FinEnum β]
  (comb : FST (Ch β) (Ch Γ) σa) (parser : PDA (Ch Γ) π σp)
  (curr : List β) (cand : β)
  (hviable : ∃ suffix qa gammas,
    comb.eval (((curr ++ [cand]).map ExtChar.char) ++ suffix) = some (qa, gammas) ∧
    parser.evalFull gammas ≠ ∅) :
  MaskChecker comb parser (PreprocessParser comb parser)
    (BuildInverseTokenSpannerTable comb).snd curr (.char cand) = true := by
  sorry

/-- `GCDChecker` is definitionally the concrete `MaskChecker` built from the
detokenizing lexer/parser pair and their preprocessing artifacts. -/
lemma GCDChecker_eq_MaskChecker
  [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
  [DecidableEq σa]
  [FinEnum β] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (curr : List β) (cand : Ch β) :
  GCDChecker spec P curr cand =
    MaskChecker
      (Detokenizing.BuildDetokLexer (V := Ch β) spec)
      (ParserWithEOS P)
      (PreprocessParser (Detokenizing.BuildDetokLexer (V := Ch β) spec) (ParserWithEOS P))
      (BuildInverseTokenSpannerTable (Detokenizing.BuildDetokLexer (V := Ch β) spec)).snd
      curr cand := by
  rfl

/-- Unfold `GCDViablePrefix` into the concrete witness used by the wrapper
theorems. -/
lemma GCDViablePrefix_iff
  [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
  [DecidableEq σa]
  [FinEnum β] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (w : List β) :
  GCDViablePrefix spec P w ↔
    ∃ suffix qa gammas,
      (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval (w.map ExtChar.char ++ suffix) =
        some (qa, gammas) ∧
      (ParserWithEOS P).evalFull gammas ≠ ∅ := by
  rfl

theorem GCDChecker_char_true_imp_viable
  [BEq σa] [LawfulBEq σa] [FinEnum β] [Vocabulary α β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (curr : List β) (cand : β)
  (h : MaskChecker
    (Detokenizing.BuildDetokLexer (V := Ch β) spec)
    (ParserWithEOS P)
    (PreprocessParser (Detokenizing.BuildDetokLexer (V := Ch β) spec) (ParserWithEOS P))
    (BuildInverseTokenSpannerTable (Detokenizing.BuildDetokLexer (V := Ch β) spec)).snd
    curr (.char cand) = true) :
  ∃ suffix qa gammas,
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval
      (((curr ++ [cand]).map ExtChar.char) ++ suffix) = some (qa, gammas) ∧
    (ParserWithEOS P).evalFull gammas ≠ ∅ :=
  MaskChecker_char_true_imp_viable
    (comb := Detokenizing.BuildDetokLexer (V := Ch β) spec)
    (parser := ParserWithEOS P)
    (curr := curr) (cand := cand) h

/-! ## Paper-facing theorems

Theorem C.8 (Soundness): If the mask checker accepts a character token, then
the extended prefix is viable (the FST can process it and the parser accepts).

Theorem C.5 (Completeness): If the extended prefix is viable, then the mask
checker accepts the token. (Depends on `fst_run_produces_realizable`.)
-/

/-- **Theorem C.8 (Soundness)**: If token `cand` passes the GCD mask checker
after prefix `curr`, then `curr ++ [cand]` extends to a viable run through
the detokenizing lexer and parser. Fully proved. -/
theorem Soundness
  [BEq σa] [LawfulBEq σa] [FinEnum β] [Vocabulary α β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (curr : List β) (cand : β)
  (h : MaskChecker
    (Detokenizing.BuildDetokLexer (V := Ch β) spec)
    (ParserWithEOS P)
    (PreprocessParser (Detokenizing.BuildDetokLexer (V := Ch β) spec) (ParserWithEOS P))
    (BuildInverseTokenSpannerTable (Detokenizing.BuildDetokLexer (V := Ch β) spec)).snd
    curr (.char cand) = true) :
  ∃ suffix qa gammas,
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval
      (((curr ++ [cand]).map ExtChar.char) ++ suffix) = some (qa, gammas) ∧
    (ParserWithEOS P).evalFull gammas ≠ ∅ :=
  GCDChecker_char_true_imp_viable spec P curr cand h

/-- **Theorem C.5 (Completeness)**: If `curr ++ [cand]` extends to a viable
run through the detokenizing lexer and parser, then `cand` passes the GCD mask
checker after prefix `curr`. Depends on `fst_run_produces_realizable`. -/
theorem Completeness
  [BEq σa] [LawfulBEq σa] [FinEnum β] [Vocabulary α β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (curr : List β) (cand : β)
  (hviable : ∃ suffix qa gammas,
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval
      (((curr ++ [cand]).map ExtChar.char) ++ suffix) = some (qa, gammas) ∧
    (ParserWithEOS P).evalFull gammas ≠ ∅) :
  MaskChecker
    (Detokenizing.BuildDetokLexer (V := Ch β) spec)
    (ParserWithEOS P)
    (PreprocessParser (Detokenizing.BuildDetokLexer (V := Ch β) spec) (ParserWithEOS P))
    (BuildInverseTokenSpannerTable (Detokenizing.BuildDetokLexer (V := Ch β) spec)).snd
    curr (.char cand) = true :=
  MaskChecker_viable_imp_char_true
    (comb := Detokenizing.BuildDetokLexer (V := Ch β) spec)
    (parser := ParserWithEOS P) (curr := curr) (cand := cand) hviable

/-! ## Checker interface connection

Connecting the one-step soundness/completeness results above to the cumulative
`checkerAllows`/`checkerAccepts` interface defined in `Checker.lean` requires
induction over the token prefix. The step-level theorems (`Soundness`,
`Completeness`, `GCDChecker_eos_true_imp_viable`) provide the induction step;
the base case is trivial since `checkerAllows c [] = true`.

Full connection to `checkerSound` and `checkerComplete` is deferred pending
resolution of the `sorry` in `fst_run_produces_realizable`.
-/

/-- The GCD mask checker, viewed as an abstract `Checker`, is sound:
every incrementally allowed prefix can be extended to an accepted word,
and decisions depend only on the underlying character content. -/
theorem GCDChecker_sound
  [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
  [DecidableEq σa]
  [FinEnum β] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) :
  checkerSound (α := α) (β := β) (GCDChecker spec P) Vocabulary.flatten := by
  sorry

/-- The GCD mask checker, viewed as an abstract `Checker`, is complete with
respect to the language defined by the composed detokenizing lexer and parser:
it accepts exactly the strings in that language, and its intermediate language
is the prefix closure. -/
theorem GCDChecker_complete
  [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
  [DecidableEq σa]
  [FinEnum β] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  (L : Language β) :
  checkerComplete (β := β) (GCDChecker spec P) L := by
  sorry
