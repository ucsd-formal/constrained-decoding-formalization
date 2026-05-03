import ConstrainedDecodingFormalization.PDA
import ConstrainedDecodingFormalization.Lexing
import ConstrainedDecodingFormalization.RealizableSequence
import ConstrainedDecodingFormalization.Vocabulary
import ConstrainedDecodingFormalization.Checker
import ConstrainedDecodingFormalization.ParserWithEOS
import ConstrainedDecodingFormalization.GCDAssumptions
import ConstrainedDecodingFormalization.GCDAlgorithm

/-!
# Grammar-constrained decoding proofs

This file proves the semantic properties of the grammar-constrained decoding
algorithm defined in `GCDAlgorithm.lean`.  The executable checker is kept in a
separate module; this file characterizes the preprocessing table, proves
step-level soundness/completeness, and lifts those facts to the checker
interface.

The central flow is:

`LexerSpec` + `Vocabulary` + `PDA`
→ `PreprocessParser`
→ `ComputeValidTokenMask`
→ `MaskChecker` / `GCDChecker`
→ language equality and checker correctness.
-/

universe u v w x y z
variable {α : Type u} {β : Type x} {Γ : Type y} {π : Type v} {σp : Type w} {σa : Type z}

variable
  [FinEnum σp] [FinEnum Γ] [FinEnum α] [FinEnum σa] [FinEnum π]
  [DecidableEq σp] [DecidableEq β] [DecidableEq Γ] [DecidableEq α] [DecidableEq π]

/-! ### ParserWithEOS: `.char` inputs preserve `.char` states -/

omit [DecidableEq Γ] in
/-- A single `.char` fullStep from `.char` states yields only `.char` states. -/
private lemma ParserWithEOS_char_fullStep_char_states
    (P : PDA Γ π σp)
    (S : Finset (Ch σp × List π))
    (c : Γ)
    (hall : ∀ x ∈ S, ∃ s, x.1 = ExtChar.char s) :
    ∀ x ∈ (ParserWithEOS P).fullStep S (ExtChar.char c), ∃ s, x.1 = ExtChar.char s := by
  intro ⟨q, st⟩ hmem
  simp only [PDA.fullStep, Finset.mem_biUnion] at hmem
  obtain ⟨⟨q₀, st₀⟩, hq₀mem, hmem'⟩ := hmem
  obtain ⟨s₀, hs₀⟩ := hall _ hq₀mem
  simp only at hs₀; subst hs₀
  -- step (.char s₀) (.char c) = (P.step s₀ c).image ...
  simp only [ParserWithEOS] at hmem'
  obtain ⟨⟨top, rep, dst⟩, htrans, hfinal⟩ := hmem'
  simp only [Finset.mem_image] at htrans
  obtain ⟨⟨top', rep', dst'⟩, _, htreq⟩ := htrans
  simp only [Prod.mk.injEq] at htreq
  obtain ⟨rfl, rfl, rfl⟩ := htreq
  -- dst is ExtChar.char dst', so the result state is .char
  simp only at hfinal
  split at hfinal
  · simp only [Finset.mem_singleton, Prod.mk.injEq] at hfinal
    exact ⟨dst', hfinal.1⟩
  · simp at hfinal

omit [DecidableEq Γ] in
/-- Evaluating `ParserWithEOS P` on a list of `.char` inputs from all-`.char`
    configurations yields only `.char` configurations. -/
private lemma ParserWithEOS_char_evalFrom_char_states
    (P : PDA Γ π σp)
    (S : Finset (Ch σp × List π))
    (w : List Γ)
    (hall : ∀ x ∈ S, ∃ s, x.1 = ExtChar.char s) :
    ∀ x ∈ (ParserWithEOS P).evalFrom S (w.map ExtChar.char),
      ∃ s, x.1 = ExtChar.char s := by
  induction w generalizing S with
  | nil => simpa [PDA.evalFrom] using hall
  | cons h t ih =>
    simp only [List.map_cons, PDA.evalFrom_cons]
    apply ih
    exact ParserWithEOS_char_fullStep_char_states P S h hall

/-- If `gammas ∈ (ParserWithEOS P).accepts`, then `ExtChar.eos ∈ gammas`.

    The accept state of `ParserWithEOS` is `.eos`, reachable only by processing
    an `.eos` input from a `.char s` state with `s ∈ P.accept`. Starting from
    `.char P.start`, all-`.char` inputs keep us in `.char` states, so at least
    one `.eos` must appear in `gammas`. -/
lemma ParserWithEOS_accepts_has_eos
    (P : PDA Γ π σp)
    (gammas : List (Ch Γ))
    (hacc : gammas ∈ (ParserWithEOS P).accepts) :
    ExtChar.eos ∈ gammas := by
  -- Unfold accepts to get the existential
  change ∃ f, f ∈ ((ParserWithEOS P).evalFrom {((ParserWithEOS P).start, [])} gammas).image Prod.fst
    ∧ f ∈ (ParserWithEOS P).accept at hacc
  obtain ⟨f, hf_mem, hf_acc⟩ := hacc
  -- accept = {.eos}, so f = .eos
  have hf_eos : f = ExtChar.eos := by
    change f ∈ ({ExtChar.eos} : Finset (Ch σp)) at hf_acc
    exact Finset.mem_singleton.mp hf_acc
  subst hf_eos
  rw [Finset.mem_image] at hf_mem
  obtain ⟨⟨q, st⟩, hcfg, hq_eos⟩ := hf_mem
  -- Suppose .eos ∉ gammas, derive contradiction
  by_contra h_not_mem
  -- Extract the list of plain Γ values (since no .eos in gammas)
  suffices h : ∀ x ∈ (ParserWithEOS P).evalFrom {(ExtChar.char P.start, ([] : List π))}
      gammas, ∃ s, x.1 = ExtChar.char s by
    obtain ⟨s, hs⟩ := h ⟨q, st⟩ hcfg
    -- hs : q = .char s, but hq_eos : Prod.fst (q, st) = .eos
    simp only at hq_eos
    rw [hq_eos] at hs
    exact absurd hs (by intro h; cases h)
  -- Prove by showing gammas = gammas'.map .char, then using char_evalFrom
  -- First show gammas has no .eos, so it factors through .char
  clear hcfg hq_eos
  have hmap : ∃ gammas' : List Γ, gammas = List.map ExtChar.char gammas' := by
    induction gammas with
    | nil => exact ⟨[], rfl⟩
    | cons g gs ih =>
      have hg : g ≠ ExtChar.eos := by
        intro heq; subst heq; exact h_not_mem List.mem_cons_self
      have hgs : ExtChar.eos ∉ gs := by
        intro hmem; apply h_not_mem; exact List.mem_cons_of_mem _ hmem
      obtain ⟨gs', rfl⟩ := ih hgs
      cases g with
      | char a => exact ⟨a :: gs', by simp [List.map]⟩
      | eos => exact absurd rfl hg
  obtain ⟨gammas', rfl⟩ := hmap
  exact ParserWithEOS_char_evalFrom_char_states P _ gammas'
    (by intro ⟨a, b⟩ hx; simp only [Finset.mem_singleton, Prod.mk.injEq] at hx
        exact ⟨P.start, hx.1⟩)

/-! ### BuildLexingFST: `.char` steps never produce `.eos` output -/

omit [FinEnum Γ] [FinEnum α] [DecidableEq Γ] in
/-- A `.char` input step of `BuildLexingFST` never outputs `ExtChar.eos`. -/
lemma BuildLexingFST_char_step_no_eos
    (spec : LexerSpec α Γ σa)
    (q : LexingState σa) (c : α) (q' : LexingState σa) (out : List (Ch Γ))
    (hstep : (BuildLexingFST spec).step q (ExtChar.char c) = some (q', out)) :
    ExtChar.eos ∉ out := by
  simp only [BuildLexingFST, Id.run] at hstep
  split at hstep
  · -- Case 1: A.step qorg c is some → out = []
    simp only [Option.some.injEq, Prod.mk.injEq] at hstep
    obtain ⟨_, rfl⟩ := hstep; simp
  · -- A.step qorg c is none
    split at hstep
    · -- Case 2: qorg ∈ F → Option.map ... = some (q', out)
      cases hmap : spec.automaton.step spec.automaton.start c with
      | none => simp [hmap, Option.map] at hstep
      | some q'' =>
        simp [hmap, Option.map] at hstep
        obtain ⟨_, rfl⟩ := hstep; simp
    · -- Case 3: none = some → contradiction
      simp at hstep

omit [FinEnum Γ] [FinEnum α] [DecidableEq Γ] in
/-- Evaluating `BuildLexingFST` on a list of `.char` inputs never produces
    `ExtChar.eos` in the output. -/
lemma BuildLexingFST_char_evalFrom_no_eos
    (spec : LexerSpec α Γ σa)
    (q : LexingState σa) (w : List α) (q' : LexingState σa) (out : List (Ch Γ))
    (hrun : (BuildLexingFST spec).evalFrom q (w.map ExtChar.char) = some (q', out)) :
    ExtChar.eos ∉ out := by
  induction w generalizing q out with
  | nil =>
    simp at hrun; obtain ⟨_, rfl⟩ := hrun; simp
  | cons a rest ih =>
    rw [List.map_cons] at hrun
    rw [FST.evalFrom_cons_some_iff] at hrun
    obtain ⟨q₁, S, T, hstep, htail, rfl⟩ := hrun
    have hS : ExtChar.eos ∉ S := BuildLexingFST_char_step_no_eos spec q a q₁ S hstep
    have hT : ExtChar.eos ∉ T := ih q₁ T htail
    simp only [List.mem_append, not_or]; exact ⟨hS, hT⟩

/-! ### BuildDetokLexer: `.char` evaluation never produces `.eos` output -/

omit [DecidableEq β] [FinEnum Γ] [FinEnum α] [DecidableEq Γ] in
/-- A single `.char` input step of `BuildDetokLexer` never outputs `.eos`. -/
lemma BuildDetokLexer_char_step_no_eos
    [v : Vocabulary α β]
    (spec : LexerSpec α Γ σa) (q : Unit × LexingState σa) (tok : β)
    (q' : Unit × LexingState σa) (out : List (Ch Γ))
    (hstep : (Detokenizing.BuildDetokLexer (V := Ch β) spec).step q (ExtChar.char tok) =
      some (q', out)) :
    ExtChar.eos ∉ out := by
  -- BuildDetokLexer = compose BuildDetokenizingFST BuildLexingFST
  -- Step on (.char tok): flatten (.char tok) = (v.flatten tok).map .char, fed to lexer
  have hcomp : (Detokenizing.BuildDetokLexer (V := Ch β) spec).step q (ExtChar.char tok) =
      ((BuildLexingFST spec).evalFrom q.2
        (Vocabulary.flatten (ExtChar.char tok))).map
        (fun (q_lex, out) => (((), q_lex), out)) := by
    simp only [Detokenizing.BuildDetokLexer]
    rw [Detokenizing.detokenizer_comp_step]
  -- For the Vocabulary (Ch α) (Ch β) instance:
  -- flatten (.char tok) = (v.flatten tok).map .char
  have hflatten : (Vocabulary.flatten (β := Ch β) (ExtChar.char tok)) =
      (v.flatten tok).map ExtChar.char := by
    simp [Vocabulary.flatten]
  rw [hcomp, hflatten] at hstep
  -- hstep : (evalFrom q.2 ...).map ... = some (q', out)
  cases heval : (BuildLexingFST spec).evalFrom q.2
      ((v.flatten tok).map ExtChar.char) with
  | none => simp [heval, Option.map] at hstep
  | some p =>
    obtain ⟨q_lex, out_lex⟩ := p
    simp only [heval, Option.map] at hstep
    -- hstep : some (((), q_lex), out_lex) = some (q', out)
    have hout : out = out_lex := by
      cases hstep; rfl
    subst hout
    exact BuildLexingFST_char_evalFrom_no_eos spec q.2 (v.flatten tok) q_lex out heval

omit [DecidableEq β] [FinEnum Γ] [FinEnum α] [DecidableEq Γ] in
/-- Evaluating `BuildDetokLexer` on a list of `.char` token inputs produces
    no `.eos` in the output. -/
lemma BuildDetokLexer_char_evalFrom_no_eos
    [v : Vocabulary α β]
    (spec : LexerSpec α Γ σa) (q : Unit × LexingState σa)
    (toks : List β) (q' : Unit × LexingState σa) (out : List (Ch Γ))
    (hrun : (Detokenizing.BuildDetokLexer (V := Ch β) spec).evalFrom q
      (toks.map ExtChar.char) = some (q', out)) :
    ExtChar.eos ∉ out := by
  induction toks generalizing q out with
  | nil =>
    simp at hrun; obtain ⟨_, rfl⟩ := hrun; simp
  | cons tok rest ih =>
    rw [List.map_cons] at hrun
    rw [FST.evalFrom_cons_some_iff] at hrun
    obtain ⟨q₁, S, T, hstep, htail, rfl⟩ := hrun
    have hS : ExtChar.eos ∉ S :=
      BuildDetokLexer_char_step_no_eos spec q tok q₁ S hstep
    have hT : ExtChar.eos ∉ T := ih q₁ T htail
    simp only [List.mem_append, not_or]; exact ⟨hS, hT⟩

/-! ### Finset-based NFA evaluation -/

-- TODO is there a better way to avoid this mess?
namespace FinsetNFA

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
lemma evalFrom_append (p : PDA Γ π σp) (S : Finset σp)
    (xs ys : List Γ) :
    FinsetNFA.evalFrom p S (xs ++ ys) =
      FinsetNFA.evalFrom p (FinsetNFA.evalFrom p S xs) ys := by
  simp [FinsetNFA.evalFrom, List.foldl_append]

@[simp]
lemma evalFrom_empty (p : PDA Γ π σp) (w : List Γ) :
    FinsetNFA.evalFrom p ∅ w = ∅ := by
  induction w with
  | nil => simp [FinsetNFA.evalFrom]
  | cons h t ih =>
    simp only [FinsetNFA.evalFrom, List.foldl_cons]
    have : stepSet p ∅ h = ∅ := by simp [stepSet]
    rw [this]
    exact ih

lemma evalFrom_prefix_nonempty (p : PDA Γ π σp) (S : Finset σp)
    (xs ys : List Γ) :
    FinsetNFA.evalFrom p S (xs ++ ys) ≠ ∅ →
      FinsetNFA.evalFrom p S xs ≠ ∅ := by
  intro h habs
  rw [FinsetNFA.evalFrom_append, habs, FinsetNFA.evalFrom_empty] at h
  exact h rfl

end FinsetNFA

omit [DecidableEq Γ] in
/-- If the PDA reaches a nonempty configuration set, the NFA overapproximation
also reaches a nonempty state set. -/
lemma PDA.evalFrom_nonempty_imp_nfa_nonempty (P : PDA Γ π σp)
    (qp : σp) (st : List π) (w : List Γ) :
    P.evalFrom {(qp, st)} w ≠ ∅ →
      FinsetNFA.evalFrom P {qp} w ≠ ∅ := by
  intro hne habs
  apply hne
  rw [Finset.eq_empty_iff_forall_notMem] at habs ⊢
  intro ⟨s', st'⟩ hmem
  have hovr := P.overApproximationLemma w {(qp, st)} s' st' hmem
  simp at hovr
  have := (FinsetNFA.finsetEvalFrom_iff_evalFrom P {qp} w s').mpr
  simp at this
  exact habs s' (this hovr)

/-! ### List fold helpers -/

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

/-- Specialization of `mem_foldl_append_iff_acc` with empty initial accumulator. -/
lemma mem_foldl_append_iff {δ : Type _} (x : δ) (xs : List (List δ)) :
  x ∈ xs.foldl List.append [] ↔ ∃ ys ∈ xs, x ∈ ys := by
  simpa using (mem_foldl_append_iff_acc (x := x) ([] : List δ) xs)

/-- Membership in a conditional fold: element is in the accumulator or in some
branch where the predicate holds. -/
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

/-- `eraseDups` always produces a nodup list. -/
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
/-- Characterize the realizable sequences that land in the "rejected" part. -/
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

omit [FinEnum σa] [DecidableEq Γ] in
/-- `MaskChecker` depends on `curr` only through `comb.eval (curr.map ExtChar.char)`.
Two prefixes producing the same FST evaluation yield identical mask decisions. -/
lemma MaskChecker_eq_of_eval_eq
    [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa]
    (comb : FST (Ch β) (Ch Γ) σa) (parser : PDA (Ch Γ) π σp)
    (pp_table : PPTable (Ch β) σp σa (Ch Γ))
    (itst : List (Ch Γ) → σa → List (Ch β))
    (curr₁ curr₂ : List β) (cand : Ch β)
    (heq : comb.eval (curr₁.map ExtChar.char) = comb.eval (curr₂.map ExtChar.char)) :
    MaskChecker comb parser pp_table itst curr₁ cand =
    MaskChecker comb parser pp_table itst curr₂ cand := by
  simp only [MaskChecker, heq]

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

omit [DecidableEq Γ] in
private lemma ParserWithEOS_fullStep_char_image
    (P : PDA Γ π σp) (S : Finset (σp × List π)) (c : Γ) :
    (ParserWithEOS P).fullStep
        (S.image (fun cfg : σp × List π => (ExtChar.char cfg.1, cfg.2)))
        (ExtChar.char c) =
      (P.fullStep S c).image
        (fun cfg : σp × List π => (ExtChar.char cfg.1, cfg.2)) := by
  ext cfg
  constructor
  · intro hcfg
    simp only [PDA.fullStep, Finset.mem_biUnion, Finset.mem_image] at hcfg ⊢
    obtain ⟨⟨q₀, st₀⟩, hstart, hstep⟩ := hcfg
    obtain ⟨⟨q, st⟩, hS, hstart_eq⟩ := hstart
    simp only [Prod.mk.injEq] at hstart_eq
    obtain ⟨hq₀, hst₀⟩ := hstart_eq
    subst hq₀; subst hst₀
    obtain ⟨⟨top, rep, dst⟩, htrans, hstack⟩ := hstep
    simp only [ParserWithEOS] at htrans
    obtain ⟨⟨top', rep', dst'⟩, htransP, hmap⟩ := Finset.mem_image.mp htrans
    simp only [Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl, rfl⟩ := hmap
    cases hmatch : top'.isPrefixOf? st with
    | none =>
        simp [hmatch] at hstack
    | some rem =>
        simp only [hmatch, Finset.mem_singleton] at hstack
        subst hstack
        refine ⟨(dst', rep' ++ rem), ?_, rfl⟩
        refine ⟨(q, st), hS, (top', rep', dst'), htransP, ?_⟩
        simp [hmatch]
  · intro hcfg
    simp only [PDA.fullStep, Finset.mem_biUnion, Finset.mem_image] at hcfg ⊢
    obtain ⟨⟨q', st'⟩, horig, hcfg_eq⟩ := hcfg
    subst cfg
    obtain ⟨⟨q, st⟩, hS, ⟨⟨top, rep, dst⟩, htransP, hstack⟩⟩ := horig
    refine ⟨(ExtChar.char q, st), ?_, ?_⟩
    · exact ⟨(q, st), hS, rfl⟩
    · refine ⟨(top, rep, ExtChar.char dst), ?_, ?_⟩
      · simp only [ParserWithEOS]
        exact Finset.mem_image.mpr ⟨(top, rep, dst), htransP, rfl⟩
      · cases hmatch : top.isPrefixOf? st with
        | none =>
            simp [hmatch] at hstack
        | some rem =>
            simp only [hmatch, Finset.mem_singleton] at hstack ⊢
            exact congrArg (fun cfg : σp × List π => (ExtChar.char cfg.1, cfg.2)) hstack

omit [FinEnum σp] [FinEnum π] [DecidableEq Γ] in
private lemma ParserWithEOS_singleton_char_image
    (q : σp) (st : List π) :
    ({(ExtChar.char q, st)} : Finset (Ch σp × List π)) =
      ({(q, st)} : Finset (σp × List π)).image
        (fun cfg : σp × List π => (ExtChar.char cfg.1, cfg.2)) := by
  ext cfg
  simp only [Finset.mem_singleton, Finset.mem_image]
  constructor
  · intro hcfg
    subst hcfg
    exact ⟨(q, st), rfl, rfl⟩
  · intro hcfg
    obtain ⟨⟨q0, st0⟩, hq0, hcfg_eq⟩ := hcfg
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq0
    exact hcfg_eq.symm

omit [DecidableEq Γ] in
private lemma ParserWithEOS_evalFrom_char_image
    (P : PDA Γ π σp) (S : Finset (σp × List π)) (w : List Γ) :
    (ParserWithEOS P).evalFrom
        (S.image (fun cfg : σp × List π => (ExtChar.char cfg.1, cfg.2)))
        (w.map ExtChar.char) =
      (P.evalFrom S w).image
        (fun cfg : σp × List π => (ExtChar.char cfg.1, cfg.2)) := by
  induction w generalizing S with
  | nil =>
      simp [PDA.evalFrom]
  | cons h t ih =>
      simp only [List.map_cons, PDA.evalFrom_cons]
      rw [ParserWithEOS_fullStep_char_image P S h]
      exact ih (P.fullStep S h)

omit [DecidableEq Γ] in
private lemma ParserWithEOS_evalFull_char_mem_imp
    (P : PDA Γ π σp) (w : List Γ) (q : σp) (st : List π)
    (hmem : (ExtChar.char q, st) ∈
      (ParserWithEOS P).evalFull (w.map ExtChar.char)) :
    (q, st) ∈ P.evalFull w := by
  have heq := ParserWithEOS_evalFrom_char_image P ({(P.start, [])} : Finset (σp × List π)) w
  simp only [PDA.evalFull] at hmem ⊢
  change (ExtChar.char q, st) ∈
    (ParserWithEOS P).evalFrom ({(ExtChar.char P.start, [])} : Finset (Ch σp × List π))
      (w.map ExtChar.char) at hmem
  rw [ParserWithEOS_singleton_char_image P.start ([] : List π)] at hmem
  rw [heq] at hmem
  simp only [Finset.mem_image] at hmem
  obtain ⟨⟨q', st'⟩, horig, hmap⟩ := hmem
  simp only [Prod.mk.injEq] at hmap
  obtain ⟨hq, hst⟩ := hmap
  cases hq
  subst hst
  exact horig
omit [FinEnum Γ] [DecidableEq Γ] in
lemma List.exists_map_char_of_not_mem_eos
    {xs : List (Ch Γ)} (hno : ExtChar.eos ∉ xs) :
    ∃ ys : List Γ, xs = ys.map ExtChar.char := by
  induction xs with
  | nil =>
      exact ⟨[], rfl⟩
  | cons x xs ih =>
      have hx : x ≠ ExtChar.eos := by
        intro hx
        apply hno
        simp [hx]
      have hxs : ExtChar.eos ∉ xs := by
        intro hmem
        apply hno
        exact List.mem_cons_of_mem _ hmem
      obtain ⟨ys, hys⟩ := ih hxs
      cases x with
      | eos =>
          exact (hx rfl).elim
      | char c =>
          refine ⟨c :: ys, ?_⟩
          simp [hys]

omit [FinEnum Γ] [DecidableEq Γ] in
lemma List.exists_map_char_append_eos_of_mem_eos
    {xs : List (Ch Γ)} (heos : ExtChar.eos ∈ xs) :
    ∃ ys : List Γ, ∃ suffix : List (Ch Γ),
      xs = ys.map ExtChar.char ++ (ExtChar.eos :: suffix) := by
  induction xs with
  | nil =>
      simp at heos
  | cons x xs ih =>
      cases x with
      | eos =>
          exact ⟨[], xs, rfl⟩
      | char c =>
          have heos_tail : ExtChar.eos ∈ xs := by
            simpa using heos
          obtain ⟨ys, suffix, hxs⟩ := ih heos_tail
          refine ⟨c :: ys, suffix, ?_⟩
          simp [hxs]

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

/-! ### Soundness direction -/

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

omit [FinEnum α] in
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

The proof decomposes the viable FST run at the first-step boundary, picks the
witness realizable sequence `d = S ++ [T.head]` (where `T.head` is singleton-
producible by hypothesis `hsingle`), and shows `d` lands in either the accepted
or dependent preprocessing bucket via prefix closure of NFA/PDA evaluation.
-/

/-- Completeness of the mask checker: if a token extends the current prefix to
a viable prefix (the FST can process the extended sequence and the parser
accepts), then that token is in the valid-token mask.

The hypothesis `hsingle` requires that the head of any nonempty FST output is
singleton-producible from the intermediate state. For `BuildDetokLexer`, this
is `BuildDetokLexer_singleProducible_of_evalFrom` (Lemma D).

This is the reverse direction of `MaskChecker_char_true_imp_viable` and
corresponds to paper Theorem C.5. -/
theorem MaskChecker_viable_imp_char_true
  [BEq σa] [LawfulBEq σa] [FinEnum β]
  (comb : FST (Ch β) (Ch Γ) σa) (parser : PDA (Ch Γ) π σp)
  (curr : List β) (cand : β)
  (hsingle : ∀ (q₁ : σa) (w : List (Ch β)) (qa' : σa) (T : List (Ch Γ))
    (_ : comb.evalFrom q₁ w = some (qa', T)) (hne : T ≠ []),
      T.head hne ∈ comb.singleProducible q₁)
  (hviable : ∃ suffix qa gammas,
    comb.eval (((curr ++ [cand]).map ExtChar.char) ++ suffix) = some (qa, gammas) ∧
    parser.evalFull gammas ≠ ∅)
  (hviable_tail_ne : ∀ suffix qa q_fst terms q₁ S T,
    comb.evalFrom comb.start (curr.map ExtChar.char) = some (q_fst, terms) →
    comb.step q_fst (.char cand) = some (q₁, S) →
    comb.evalFrom q₁ suffix = some (qa, T) →
    parser.evalFull (terms ++ S ++ T) ≠ ∅ →
    T ≠ []) :
  MaskChecker comb parser (PreprocessParser comb parser)
    (BuildInverseTokenSpannerTable comb).snd curr (.char cand) = true := by
  -- Step 1: Decompose the viable FST run
  obtain ⟨suffix, qa, gammas, heval, hparse⟩ := hviable
  -- Use a helper to decompose: first split at curr boundary, then at cand
  have heval_start : comb.evalFrom comb.start
      (curr.map ExtChar.char ++ (ExtChar.char cand :: suffix)) = some (qa, gammas) := by
    have : comb.eval (List.map ExtChar.char (curr ++ [cand]) ++ suffix) =
        comb.evalFrom comb.start (List.map ExtChar.char (curr ++ [cand]) ++ suffix) := by
      simp [FST.eval]
    rw [this] at heval
    convert heval using 2
    simp [List.map_append, List.append_assoc]
  -- The prefix on curr must succeed for the whole thing to succeed
  -- Use evalFrom_append to decompose
  have hcurr_some : ∃ q_fst terms,
      comb.evalFrom comb.start (curr.map ExtChar.char) = some (q_fst, terms) := by
    by_contra h
    push_neg at h
    have happ := FST.evalFrom_append (M := comb) comb.start
      (curr.map ExtChar.char) (ExtChar.char cand :: suffix)
    cases hc : comb.evalFrom comb.start (curr.map ExtChar.char) with
    | none =>
      rw [hc] at happ
      simp at happ
      rw [happ] at heval_start
      exact absurd heval_start (by simp)
    | some p =>
      exact (h p.1 p.2 hc).elim
  obtain ⟨q_fst, terms, hcurr⟩ := hcurr_some
  -- Now get the rest of the run
  have hrest_eq : ∃ out_rest,
      comb.evalFrom q_fst (ExtChar.char cand :: suffix) = some (qa, out_rest) ∧
      gammas = terms ++ out_rest := by
    have happ := FST.evalFrom_append (M := comb) comb.start
      (curr.map ExtChar.char) (ExtChar.char cand :: suffix)
    rw [hcurr] at happ
    -- happ : evalFrom start (... ++ ...) =
    --   (evalFrom q_fst ...).map (fun (s', ts) => (s', terms ++ ts))
    rw [happ] at heval_start
    -- heval_start : (...).map ... = some (qa, gammas)
    cases hrest : comb.evalFrom q_fst (ExtChar.char cand :: suffix) with
    | none => simp [hrest] at heval_start
    | some p =>
      obtain ⟨qa', out'⟩ := p
      simp [hrest] at heval_start
      exact ⟨out', by rw [heval_start.1], heval_start.2.symm⟩
  obtain ⟨out_rest, hrest, hgammas_split⟩ := hrest_eq
  -- Decompose the cons step
  rcases (FST.evalFrom_cons_some_iff (M := comb)).1 hrest with
    ⟨q₁, S, T, hstep, htail, hout_eq⟩
  -- gammas = terms ++ (S ++ T)
  have hgammas : gammas = terms ++ (S ++ T) := by rw [hgammas_split, hout_eq]
  -- Step 2: Case split on T
  by_cases hTne : T ≠ []
  · -- T is nonempty: build witness d = S ++ [T.head hTne]
    -- T.head is singleton-producible from q₁ by hsingle
    have hhead_sp : (T.head hTne) ∈ comb.singleProducible q₁ :=
      hsingle q₁ suffix qa T htail hTne
    -- d ∈ RealizableSequences comb
    set d := S ++ [T.head hTne] with hd_def
    have hd_rs : d ∈ RealizableSequences comb :=
      ⟨q_fst, ExtChar.char cand, S, q₁, T.head hTne, hstep, hhead_sp, rfl⟩
    -- .char cand ∈ InverseTokenSpannerTable comb d q_fst
    have hd_ne : d ≠ [] := by simp [hd_def]
    have hsingleton_ne : [T.head hTne] ≠ ([] : List (Ch Γ)) := by simp
    have hd_dropLast : d.dropLast = S := by simp [hd_def]
    have hd_getLast : d.getLast hd_ne = T.head hTne := by simp [hd_def]
    have hitst : ExtChar.char cand ∈ InverseTokenSpannerTable comb d q_fst := by
      simp only [InverseTokenSpannerTable, dif_pos hd_ne, hd_dropLast, hd_getLast, Set.mem_setOf_eq]
      exact ⟨q₁, hstep, hhead_sp⟩
    -- Parser prefix closure: gammas = terms ++ (S ++ T) and S ++ T = d ++ T.tail
    rw [hgammas] at hparse
    rw [PDA.evalFull, PDA.evalFrom_append'] at hparse
    have hST_eq : S ++ T = d ++ T.tail := by
      rw [hd_def, List.append_assoc]
      congr 1
      exact (List.cons_head_tail hTne).symm
    rw [hST_eq] at hparse
    -- parser.evalFrom (... terms) d ≠ ∅ by prefix closure
    have hd_ne_empty : parser.evalFrom (parser.evalFrom {(parser.start, [])} terms) d ≠ ∅ :=
      PDA.evalFrom_prefix_nonempty parser _ d (T.tail) hparse
    -- Extract a config (qp, st_p) with evalFrom {(qp, st_p)} d ≠ ∅
    -- evalFrom over a set = biUnion of evalFrom over singletons
    have hcfg : ∃ qp st_p,
        (qp, st_p) ∈ parser.evalFrom {(parser.start, [])} terms ∧
        parser.evalFrom {(qp, st_p)} d ≠ ∅ := by
      rcases PDA.evalFrom_nonempty_exists_singleton parser _ d hd_ne_empty with ⟨⟨qp, st_p⟩, hmem, hne⟩
      exact ⟨qp, st_p, hmem, hne⟩
    obtain ⟨qp, st_p, hmem_qp, hqp_d_ne⟩ := hcfg
    -- Show .char cand ∈ ComputeValidTokenMask
    have hmask : ExtChar.char cand ∈
        ComputeValidTokenMask parser (BuildInverseTokenSpannerTable comb).snd
          (PreprocessParser comb parser) q_fst qp st_p := by
      rw [mem_ComputeValidTokenMask_preprocess_iff]
      by_cases hacc : parser.evalFrom {(qp, [])} d ≠ ∅
      · left; exact ⟨d, hd_rs, hacc, hitst⟩
      · push_neg at hacc; right
        exact ⟨d, hd_rs, hacc,
          PDA.evalFrom_nonempty_imp_nfa_nonempty parser qp st_p d hqp_d_ne,
          hqp_d_ne, hitst⟩
    -- Assemble MaskChecker = true
    unfold MaskChecker
    have hcomb_eval : comb.eval (curr.map ExtChar.char) = some (q_fst, terms) := by
      simp [FST.eval, hcurr]
    simp only [hcomb_eval]
    rw [Finset.fold_or_eq_true_iff]
    rw [Finset.mem_image]
    refine ⟨(qp, st_p), hmem_qp, ?_⟩
    simp only [List.contains_iff_mem]
    exact hmask
  · -- T = []: contradicts hviable_tail_ne
    push_neg at hTne; subst hTne
    have hparse' : parser.evalFull (terms ++ S ++ []) ≠ ∅ := by
      rw [hgammas] at hparse; simpa [List.append_assoc] using hparse
    exact absurd rfl (hviable_tail_ne suffix qa q_fst terms q₁ S [] hcurr hstep htail hparse')

omit [FinEnum σp] [FinEnum α] [FinEnum σa] [FinEnum π] in
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

omit [FinEnum σp] [FinEnum α] [FinEnum σa] [FinEnum π] [DecidableEq β] [DecidableEq Γ] in
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

omit [FinEnum α] in theorem GCDChecker_char_true_imp_viable
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
checker accepts the token. Uses `BuildDetokLexer_singleProducible_of_evalFrom`
(Lemma D) to discharge the `hsingle` hypothesis.
-/

omit [FinEnum α] in
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

/-- If every token in `w` has been allowed incrementally by `GCDChecker`, then
`w` is a semantic viable prefix. This direction uses only one-step soundness and
does not require the whitespace assumption. -/
theorem GCDChecker_checkerAllows_imp_viablePrefix
  [BEq σa] [LawfulBEq σa] [FinEnum β] [Vocabulary α β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (w : List β)
  (hw : checkerAllows (GCDChecker spec P) w = true) :
  GCDViablePrefix spec P w := by
  cases List.eq_nil_or_concat w with
  | inl hnil =>
      subst hnil
      refine ⟨[], (Detokenizing.BuildDetokLexer (V := Ch β) spec).start, [], ?_, ?_⟩
      · simp [FST.eval]
      · simp [PDA.evalFull]
  | inr hsnoc =>
      obtain ⟨pref, last, hsnoc⟩ := hsnoc
      subst hsnoc
      have hw_append : checkerAllows (GCDChecker spec P) (pref ++ [last]) = true := by
        simpa [List.concat_eq_append] using hw
      have hlast : GCDChecker spec P pref (ExtChar.char last) = true := by
        exact (checkerAllows_snoc_iff (GCDChecker spec P) pref last).1 hw_append |>.2
      rw [GCDChecker_eq_MaskChecker] at hlast
      have hviable_append : GCDViablePrefix spec P (pref ++ [last]) :=
        (GCDViablePrefix_iff spec P (pref ++ [last])).2
          (GCDChecker_char_true_imp_viable spec P pref last hlast)
      simpa [List.concat_eq_append] using hviable_append

omit [FinEnum Γ] [FinEnum α] [DecidableEq β] [DecidableEq Γ] in
/-- Helper packaging the singleProducible hypothesis for the detokenizing lexer. -/
lemma BuildDetokLexer_hsingle
  [BEq σa] [LawfulBEq σa] [FinEnum β] [Vocabulary α β]
  [BEq (Ch Γ)] [LawfulBEq (Ch Γ)]
  (spec : LexerSpec α Γ σa)
  (hempty : [] ∉ spec.automaton.accepts)
  (hrestart : ∀ s ∈ spec.automaton.accept,
    ∃ c : α, spec.automaton.step s c = none ∧
      (spec.automaton.step spec.automaton.start c).isSome) :
  ∀ (q₁ : Unit × LexingState σa) (w : List (Ch β))
    (qa' : Unit × LexingState σa) (T : List (Ch Γ)),
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).evalFrom q₁ w = some (qa', T) →
    ∀ (hne : T ≠ []), T.head hne ∈
      (Detokenizing.BuildDetokLexer (V := Ch β) spec).singleProducible q₁ := by
  intro ⟨_, q_lex⟩ w qa' T hrun hne
  exact Detokenizing.BuildDetokLexer_singleProducible_of_evalFrom
    spec hempty hrestart q_lex w qa' T hrun hne

set_option maxHeartbeats 1600000 in
omit [FinEnum α] in
/-- **Theorem C.5 (Completeness)**: If `curr ++ [cand]` extends to an
**accepted** run through the detokenizing lexer and parser, then `cand` passes
the GCD mask checker after prefix `curr`.

The hypothesis uses `(ParserWithEOS P).accepts` (the parser reaches the `.eos`
accept state) rather than the weaker `evalFull gammas ≠ ∅` (mere reachability).
The stronger condition is necessary because the mask checker may correctly
reject a token whose viable run only satisfies reachability but not acceptance
(see the `hviable_tail_ne` discussion).

Uses `BuildDetokLexer_hsingle` (Lemma D) for the `hsingle` hypothesis, and
derives `T ≠ []` from the acceptance condition: `.eos` must appear in the
parser output `gammas`, character-input FST steps never produce `.eos`, so the
suffix-produced output `T` must contain `.eos`.

Requires `hempty` and the full whitespace assumption; the latter rederives the
lexer restart hypothesis used by `BuildDetokLexer_hsingle`. -/
theorem Completeness
  [FinEnum β] [Vocabulary α β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (curr : List β) (cand : β)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite)
  (hviable : ∃ suffix qa gammas,
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval
      (((curr ++ [cand]).map ExtChar.char) ++ suffix) = some (qa, gammas) ∧
    gammas ∈ (ParserWithEOS P).accepts) :
  MaskChecker
    (Detokenizing.BuildDetokLexer (V := Ch β) spec)
    (ParserWithEOS P)
    (PreprocessParser (Detokenizing.BuildDetokLexer (V := Ch β) spec) (ParserWithEOS P))
    (BuildInverseTokenSpannerTable (Detokenizing.BuildDetokLexer (V := Ch β) spec)).snd
    curr (.char cand) = true := by
  -- Abbreviations
  let comb := Detokenizing.BuildDetokLexer (V := Ch β) spec
  let parser := ParserWithEOS P
  have hrestart := GCDWhitespaceAssumption.existsRestartChar spec P hassum.hempty hassum.whitespace
  -- Extract the viable run witnesses
  obtain ⟨suffix, qa, gammas, heval, hacc⟩ := hviable
  -- Acceptance implies evalFull ≠ ∅
  have hparse : parser.evalFull gammas ≠ ∅ := by
    intro hempty_cfg
    change gammas ∈ (ParserWithEOS P).accepts at hacc
    simp only [PDA.accepts, PDA.acceptsFrom] at hacc
    obtain ⟨f, hfmem, _⟩ := hacc
    rw [Finset.mem_image] at hfmem
    obtain ⟨cfg, hcfg, _⟩ := hfmem
    change (ParserWithEOS P).evalFrom {((ParserWithEOS P).start, [])} gammas = ∅ at hempty_cfg
    rw [hempty_cfg] at hcfg
    simp at hcfg
  -- gammas contains .eos (from acceptance)
  have heos_in_gammas : ExtChar.eos ∈ gammas :=
    ParserWithEOS_accepts_has_eos P gammas hacc
  -- Step 1: Decompose the FST run (same as MaskChecker_viable_imp_char_true)
  have heval_start : comb.evalFrom comb.start
      (curr.map ExtChar.char ++ (ExtChar.char cand :: suffix)) = some (qa, gammas) := by
    have : comb.eval (List.map ExtChar.char (curr ++ [cand]) ++ suffix) =
        comb.evalFrom comb.start (List.map ExtChar.char (curr ++ [cand]) ++ suffix) := by
      simp [FST.eval]
    rw [this] at heval
    convert heval using 2
    simp [List.map_append, List.append_assoc]
  have hcurr_some : ∃ q_fst terms,
      comb.evalFrom comb.start (curr.map ExtChar.char) = some (q_fst, terms) := by
    by_contra h
    push_neg at h
    have happ := FST.evalFrom_append (M := comb) comb.start
      (curr.map ExtChar.char) (ExtChar.char cand :: suffix)
    cases hc : comb.evalFrom comb.start (curr.map ExtChar.char) with
    | none => rw [hc] at happ; simp at happ; rw [happ] at heval_start; simp at heval_start
    | some p => exact (h p.1 p.2 hc).elim
  obtain ⟨q_fst, terms, hcurr⟩ := hcurr_some
  have hrest_eq : ∃ out_rest,
      comb.evalFrom q_fst (ExtChar.char cand :: suffix) = some (qa, out_rest) ∧
      gammas = terms ++ out_rest := by
    have happ := FST.evalFrom_append (M := comb) comb.start
      (curr.map ExtChar.char) (ExtChar.char cand :: suffix)
    rw [hcurr] at happ; rw [happ] at heval_start
    cases hrest : comb.evalFrom q_fst (ExtChar.char cand :: suffix) with
    | none => simp [hrest] at heval_start
    | some p =>
      obtain ⟨qa', out'⟩ := p
      simp [hrest] at heval_start
      exact ⟨out', by rw [heval_start.1], heval_start.2.symm⟩
  obtain ⟨out_rest, hrest, hgammas_split⟩ := hrest_eq
  rcases (FST.evalFrom_cons_some_iff (M := comb)).1 hrest with
    ⟨q₁, S, T, hstep, htail, hout_eq⟩
  have hgammas : gammas = terms ++ (S ++ T) := by rw [hgammas_split, hout_eq]
  -- Step 2: Prove T ≠ [] using the acceptance/eos argument
  have heos_not_terms : ExtChar.eos ∉ terms :=
    BuildDetokLexer_char_evalFrom_no_eos spec comb.start curr q_fst terms hcurr
  have heos_not_S : ExtChar.eos ∉ S :=
    BuildDetokLexer_char_step_no_eos spec q_fst cand q₁ S hstep
  have heos_in_T : ExtChar.eos ∈ T := by
    rw [hgammas] at heos_in_gammas
    simp only [List.mem_append] at heos_in_gammas
    tauto
  have hTne : T ≠ [] := by intro h; subst h; simp at heos_in_T
  -- Step 3: Build the realizable sequence witness
  have hhead_sp : (T.head hTne) ∈ comb.singleProducible q₁ :=
    BuildDetokLexer_hsingle spec hassum.hempty hrestart q₁ suffix qa T htail hTne
  set d := S ++ [T.head hTne] with hd_def
  have hd_rs : d ∈ RealizableSequences comb :=
    ⟨q_fst, ExtChar.char cand, S, q₁, T.head hTne, hstep, hhead_sp, rfl⟩
  have hd_ne : d ≠ [] := by simp [hd_def]
  have hd_dropLast : d.dropLast = S := by simp [hd_def]
  have hd_getLast : d.getLast hd_ne = T.head hTne := by simp [hd_def]
  have hitst : ExtChar.char cand ∈ InverseTokenSpannerTable comb d q_fst := by
    simp only [InverseTokenSpannerTable, dif_pos hd_ne, hd_dropLast, hd_getLast, Set.mem_setOf_eq]
    exact ⟨q₁, hstep, hhead_sp⟩
  -- Parser prefix closure
  rw [hgammas] at hparse
  rw [PDA.evalFull, PDA.evalFrom_append'] at hparse
  have hST_eq : S ++ T = d ++ T.tail := by
    rw [hd_def, List.append_assoc]; congr 1
    exact (List.cons_head_tail hTne).symm
  rw [hST_eq] at hparse
  have hd_ne_empty : parser.evalFrom (parser.evalFrom {(parser.start, [])} terms) d ≠ ∅ :=
    PDA.evalFrom_prefix_nonempty parser _ d (T.tail) hparse
  have hcfg : ∃ qp st_p,
      (qp, st_p) ∈ parser.evalFrom {(parser.start, [])} terms ∧
      parser.evalFrom {(qp, st_p)} d ≠ ∅ := by
    rcases PDA.evalFrom_nonempty_exists_singleton parser _ d hd_ne_empty with ⟨⟨qp, st_p⟩, hmem, hne⟩
    exact ⟨qp, st_p, hmem, hne⟩
  obtain ⟨qp, st_p, hmem_qp, hqp_d_ne⟩ := hcfg
  -- Show .char cand ∈ ComputeValidTokenMask
  have hmask : ExtChar.char cand ∈
      ComputeValidTokenMask parser (BuildInverseTokenSpannerTable comb).snd
        (PreprocessParser comb parser) q_fst qp st_p := by
    simp only [mem_ComputeValidTokenMask_preprocess_iff]
    by_cases hacc0 : (ParserWithEOS P).evalFrom {(qp, [])} d ≠ ∅
    · left; exact ⟨d, hd_rs, hacc0, hitst⟩
    · push_neg at hacc0; right
      exact ⟨d, hd_rs, hacc0,
        PDA.evalFrom_nonempty_imp_nfa_nonempty (ParserWithEOS P) qp st_p d hqp_d_ne,
        hqp_d_ne, hitst⟩
  -- Assemble MaskChecker = true
  unfold MaskChecker
  have hcomb_eval : comb.eval (curr.map ExtChar.char) = some (q_fst, terms) := by
    simp [FST.eval, hcurr]
  -- Simplify the match using hcomb_eval
  simp only [show (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval (List.map ExtChar.char curr) =
    some (q_fst, terms) from hcomb_eval]
  rw [Finset.fold_or_eq_true_iff, Finset.mem_image]
  refine ⟨(qp, st_p), hmem_qp, ?_⟩
  simp only [List.contains_iff_mem]
  exact hmask

/-! ## EOS Completeness

The completeness direction for the `.eos` case: if the current prefix is viable
(the FST processes `curr.map char ++ .eos :: suffix` and the parser accepts),
then `MaskChecker` returns `true` for `.eos`.

Unlike the `.char` case, after the `.eos` step the FST output `S` already
contains `.eos`, so the parser reaches the `.eos` dead-loop state. The suffix
output `T` may be empty. When `T ≠ []` we use the same realizable-sequence
argument as the `.char` case. When `T = []` we exploit that `ParserWithEOS`
at `.eos` state handles any further input (dead-loop), and we pick an arbitrary
element from `singleProducible q₁` to form the realizable sequence witness.
-/

omit [DecidableEq Γ] in
/-- `ParserWithEOS` at `.eos` state is a fixed point: `fullStep` returns the
same configuration. -/
private lemma ParserWithEOS_eos_fullStep_eq
    (P : PDA Γ π σp) (st : List π) (c : Ch Γ) :
    (ExtChar.eos, st) ∈ (ParserWithEOS P).fullStep {(ExtChar.eos, st)} c := by
  simp only [PDA.fullStep, Finset.mem_biUnion, Finset.mem_singleton]
  refine ⟨(ExtChar.eos, st), rfl, ?_⟩
  refine ⟨([], [], ExtChar.eos), ?_, ?_⟩
  · show ([], [], ExtChar.eos) ∈ (ParserWithEOS P).step ExtChar.eos c
    simp [ParserWithEOS]
  · -- top = [], so isPrefixOf? [] st = some st, result = {(.eos, [] ++ st)} = {(.eos, st)}
    simp [List.isPrefixOf?]

omit [DecidableEq Γ] in
/-- `ParserWithEOS` at `.eos` state loops: `fullStep` on any input from
a configuration at `.eos` state is nonempty. -/
private lemma ParserWithEOS_eos_fullStep_nonempty
    (P : PDA Γ π σp) (st : List π) (c : Ch Γ) :
    (ParserWithEOS P).fullStep {(ExtChar.eos, st)} c ≠ ∅ := by
  intro h
  have := ParserWithEOS_eos_fullStep_eq P st c
  rw [h] at this
  simp at this

omit [DecidableEq Γ] in
/-- If a PDA evaluation from a set `S` contains an `.eos` configuration, then
extending by one more element keeps the evaluation nonempty (for `ParserWithEOS`). -/
private lemma ParserWithEOS_evalFrom_eos_extend
    (P : PDA Γ π σp) (S : Finset (Ch σp × List π)) (e : Ch Γ)
    (heos : ∃ st', (ExtChar.eos, st') ∈ S) :
    (ParserWithEOS P).fullStep S e ≠ ∅ := by
  obtain ⟨st', hst'⟩ := heos
  intro h
  have hsub : (ParserWithEOS P).fullStep {(ExtChar.eos, st')} e ⊆
      (ParserWithEOS P).fullStep S e :=
    (ParserWithEOS P).fullStep_subset {(ExtChar.eos, st')} S
      (Finset.singleton_subset_iff.mpr hst') e
  have hne := ParserWithEOS_eos_fullStep_nonempty P st' e
  have : (ParserWithEOS P).fullStep {(ExtChar.eos, st')} e = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    exact (Finset.eq_empty_iff_forall_notMem.mp h x) (hsub hx)
  exact hne this

omit [FinEnum Γ] [FinEnum α] [DecidableEq β] [DecidableEq Γ] in
/-- `singleProducible` of `BuildDetokLexer` at the start state is nonempty:
`.eos` is singleton-producible from the start state (via one `.eos` input step
when the start state is not accepting). -/
private lemma BuildDetokLexer_singleProducible_start_nonempty
    [Vocabulary α β]
    (spec : LexerSpec α Γ σa)
    (hempty : [] ∉ spec.automaton.accepts) :
    (ExtChar.eos : Ch Γ) ∈
      (Detokenizing.BuildDetokLexer (V := Ch β) spec).singleProducible
        ((), LexingState.start (σ := σa)) := by
  -- Witness: w = [.eos], evalFrom ((), start) [.eos] = some (((), start), [.eos])
  rw [mem_singleProducible_iff_exists_evalFrom_singleton]
  -- start ∉ accept (from hempty)
  have hstart_not_accept : spec.automaton.start ∉ spec.automaton.accept := by
    intro h; apply hempty; rw [FSA.accepts_iff]; exact ⟨spec.automaton.start, rfl, h⟩
  -- Provide the witness
  refine ⟨[ExtChar.eos], ((), LexingState.start (σ := σa)), ?_⟩
  -- Reduce the step through the composed FST
  -- evalFrom ((), start) [.eos] unfolds to: step ((), start) .eos >>= evalFrom _ []
  simp only [FST.evalFrom]
  -- Use the comp_step decomposition
  simp only [Detokenizing.BuildDetokLexer]
  rw [Detokenizing.detokenizer_comp_step]
  simp only [FST.evalFrom, BuildLexingFST, Id.run, LexingState.src,
    hstart_not_accept, dite_false, ite_true]
  simp

omit [FinEnum Γ] [FinEnum α] [DecidableEq β] [DecidableEq Γ] in
lemma BuildDetokLexer_whitespace_singleProducible_start
    [Vocabulary α β]
    {tnonwhite twhite : α} {qnonwhite qwhite : σa}
    (spec : LexerSpec α Γ σa)
    (hwa : Detokenizing.WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) :
    (ExtChar.char
      (Detokenizing.whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa) : Ch Γ) ∈
      (Detokenizing.BuildDetokLexer (V := Ch β) spec).singleProducible
        ((), LexingState.start (σ := σa)) := by
  rw [mem_singleProducible_iff_exists_evalFrom_singleton]
  let comb := Detokenizing.BuildDetokLexer (V := Ch β) spec
  let whiteTerm := Detokenizing.whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa
  refine ⟨[ExtChar.char (Vocabulary.embed twhite),
      ExtChar.char (Vocabulary.embed tnonwhite)],
    ((), LexingState.id qnonwhite), ?_⟩
  obtain ⟨hqwhite_accept, hwhite_step, hwhite_only, _, _hqnonwhite_accept,
    hqnonwhite_step, hdiff⟩ := hwa
  have hstart_white : spec.automaton.step spec.automaton.start twhite = some qwhite := by
    exact (hwhite_step spec.automaton.start twhite).mpr (by simp)
  have hqwhite_nonwhite : spec.automaton.step qwhite tnonwhite = none := by
    exact hwhite_only tnonwhite (fun h => hdiff h.symm)
  have hstep1 :
      comb.step ((), LexingState.start) (ExtChar.char (Vocabulary.embed twhite)) =
        some (((), LexingState.id qwhite), []) := by
    simp [comb, Detokenizing.BuildDetokLexer, Detokenizing.detokenizer_comp_step,
      Vocabulary.flatten, Vocabulary.fe, BuildLexingFST, Id.run,
      LexingState.src, hstart_white]
  have hstep2 :
      comb.step ((), LexingState.id qwhite) (ExtChar.char (Vocabulary.embed tnonwhite)) =
        some (((), LexingState.id qnonwhite), [ExtChar.char whiteTerm]) := by
    simp [comb, whiteTerm, Detokenizing.BuildDetokLexer,
      Detokenizing.detokenizer_comp_step, Vocabulary.flatten, Vocabulary.fe,
      BuildLexingFST, Id.run, LexingState.src, hqwhite_nonwhite,
      hqwhite_accept, hqnonwhite_step, Detokenizing.whitespaceTerminal]
  rw [FST.evalFrom_cons_some_iff]
  refine ⟨((), LexingState.id qwhite), [], [ExtChar.char whiteTerm], hstep1, ?_, by simp [whiteTerm]⟩
  rw [FST.evalFrom_cons_some_iff]
  refine ⟨((), LexingState.id qnonwhite), [ExtChar.char whiteTerm], [], hstep2, ?_, by simp [whiteTerm]⟩
  simp [FST.evalFrom]

omit [FinEnum Γ] [FinEnum α] [DecidableEq β] [DecidableEq Γ] in
/-- After `.eos` step in `BuildDetokLexer`, the reached state is
`((), LexingState.start)`. -/
private lemma BuildDetokLexer_eos_step_reaches_start
    [v : Vocabulary α β]
    (spec : LexerSpec α Γ σa) (q_fst : Unit × LexingState σa)
    (q₁ : Unit × LexingState σa) (S : List (Ch Γ))
    (hstep : (Detokenizing.BuildDetokLexer (V := Ch β) spec).step q_fst
      ExtChar.eos = some (q₁, S)) :
    q₁ = ((), LexingState.start) := by
  simp only [Detokenizing.BuildDetokLexer] at hstep
  rw [Detokenizing.detokenizer_comp_step] at hstep
  have hflatten : (Vocabulary.flatten (α := Ch α) (β := Ch β) ExtChar.eos) =
      [ExtChar.eos] := by
    simp [Vocabulary.flatten]
  rw [hflatten] at hstep
  -- hstep : (BuildLexingFST spec).evalFrom q_fst.2 [.eos]).map ... = some (q₁, S)
  -- Reduce: unfold the composed FST step completely
  simp only [FST.evalFrom, BuildLexingFST, Id.run] at hstep
  -- The result has a nested split from the compose layer + the lex step
  -- All viable branches go to LexingState.start. Use revert + split.
  revert hstep
  split
  · -- h_1: none case from compose
    intro hstep; simp at hstep
  · -- h_2: some case from compose, need to extract start state from heq✝
    rename_i _ s'' T' heq
    intro hstep
    simp at hstep
    -- hstep : q₁ = ((), s'') ∧ ... ; heq : if-then-else = some (s'', S)
    -- Extract s'' = LexingState.start from heq
    have hs : s'' = LexingState.start := by
      split at heq
      · simp at heq; exact heq.1.symm
      · split at heq
        · simp at heq; exact heq.1.symm
        · simp at heq
    rw [← hstep.1, hs]

omit [FinEnum Γ] [FinEnum α] [DecidableEq β] [DecidableEq Γ] in
/-- After `.eos` step in `BuildDetokLexer`, the output is nonempty. -/
private lemma BuildDetokLexer_eos_step_output_ne_nil
    [Vocabulary α β]
    (spec : LexerSpec α Γ σa) (q_fst : Unit × LexingState σa)
    (q₁ : Unit × LexingState σa) (S : List (Ch Γ))
    (hstep : (Detokenizing.BuildDetokLexer (V := Ch β) spec).step q_fst
      ExtChar.eos = some (q₁, S)) :
    S ≠ [] := by
  intro h; subst h
  simp only [Detokenizing.BuildDetokLexer] at hstep
  rw [Detokenizing.detokenizer_comp_step] at hstep
  simp only [FST.evalFrom, BuildLexingFST, Id.run] at hstep
  revert hstep; split
  · intro hstep; simp at hstep
  · rename_i _ s'' T' heq
    intro hstep; simp at hstep
    -- After simp, hstep gives us q₁ = ((), s'') and T' = []
    -- But heq : if-then-else = some (s'', T'), and with T' = [] all branches contradict
    have : T' = [] := by
      rcases hstep with ⟨_, hT'⟩
      simpa using hT'
    rw [this] at heq
    split at heq <;> simp at heq

omit [FinEnum Γ] [FinEnum α] [DecidableEq β] [DecidableEq Γ] in
/-- After `.eos` step in `BuildDetokLexer`, `.eos` appears in the output. -/
lemma BuildDetokLexer_eos_step_eos_in_output
    [Vocabulary α β]
    (spec : LexerSpec α Γ σa) (q_fst : Unit × LexingState σa)
    (q₁ : Unit × LexingState σa) (S : List (Ch Γ))
    (hstep : (Detokenizing.BuildDetokLexer (V := Ch β) spec).step q_fst
      ExtChar.eos = some (q₁, S)) :
    ExtChar.eos ∈ S := by
  simp only [Detokenizing.BuildDetokLexer] at hstep
  rw [Detokenizing.detokenizer_comp_step] at hstep
  simp only [FST.evalFrom, BuildLexingFST, Id.run] at hstep
  revert hstep; split
  · intro hstep; simp at hstep
  · rename_i _ s'' T' heq
    -- heq : (if-then-else on BuildLexingFST .eos) = some (s'', T')
    -- hstep : Option.map ... (some (s'', T')) = some (q₁, S)
    -- In all branches, T' contains .eos, and S = T'
    intro hstep
    -- First resolve heq to know what T' is
    split at heq
    · -- accepting state: T' = [T_tok, .eos]
      obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
      -- Now hstep : ... = some (q₁, S) with T' = [_, .eos]
      simp at hstep; exact hstep.2 ▸ (by simp)
    · split at heq
      · -- start state: T' = [.eos]
        obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
        simp at hstep; exact hstep.2 ▸ (by simp)
      · -- none case
        simp at heq

omit [FinEnum Γ] [FinEnum α] [DecidableEq β] [DecidableEq Γ] in
/-- After `.eos` step in `BuildDetokLexer`, there exists `S_init` such that
`S = S_init ++ [.eos]`. -/
private lemma BuildDetokLexer_eos_step_snoc
    [Vocabulary α β]
    (spec : LexerSpec α Γ σa) (q_fst : Unit × LexingState σa)
    (q₁ : Unit × LexingState σa) (S : List (Ch Γ))
    (hstep : (Detokenizing.BuildDetokLexer (V := Ch β) spec).step q_fst
      ExtChar.eos = some (q₁, S)) :
    ∃ S_init, S = S_init ++ [ExtChar.eos] := by
  simp only [Detokenizing.BuildDetokLexer] at hstep
  rw [Detokenizing.detokenizer_comp_step] at hstep
  simp only [FST.evalFrom, BuildLexingFST, Id.run] at hstep
  revert hstep; split
  · intro hstep; simp at hstep
  · rename_i _ s'' T' heq
    intro hstep
    split at heq
    · -- accepting state: T' = [T_tok, .eos]
      have hT' : ∃ tok, T' = [ExtChar.char tok, ExtChar.eos] := by
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq); exact ⟨_, rfl⟩
      obtain ⟨tok, rfl⟩ := hT'
      -- hstep : Option.map f (some (s'', [.char tok, .eos])) = some (q₁, S)
      -- which reduces to f (s'', [.char tok, .eos]) = (q₁, S)
      -- where f maps (q_lex, out) to (((), q_lex), out)
      -- so S = [.char tok, .eos]
      have : S = [ExtChar.char tok, ExtChar.eos] := by
        simp only [Option.map] at hstep
        have := (Prod.mk.inj (Option.some.inj hstep)).2
        simpa using this.symm
      exact ⟨[ExtChar.char tok], this⟩
    · split at heq
      · -- start state: T' = [.eos]
        have hT' : T' = [ExtChar.eos] := by
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq); rfl
        subst hT'
        have : S = [ExtChar.eos] := by
          simp only [Option.map] at hstep
          have := (Prod.mk.inj (Option.some.inj hstep)).2
          simpa using this.symm
        exact ⟨[], by simpa using this⟩
      · -- none case
        simp at heq

omit [DecidableEq Γ] in
/-- In `ParserWithEOS`, after `fullStep` on `.eos` input, every config in the
result is at `.eos` state. -/
private lemma ParserWithEOS_fullStep_eos_all_eos
    (P : PDA Γ π σp) (X : Finset (Ch σp × List π))
    (cfg : Ch σp × List π)
    (hcfg : cfg ∈ (ParserWithEOS P).fullStep X ExtChar.eos) :
    ∃ st', cfg = (ExtChar.eos, st') := by
  simp only [PDA.fullStep, Finset.mem_biUnion] at hcfg
  obtain ⟨⟨s, stack⟩, _, hmem⟩ := hcfg
  obtain ⟨⟨top, rep, dst⟩, hstep, hmatch⟩ := hmem
  -- ParserWithEOS.step _ .eos always targets .eos
  -- In all cases, dst = .eos
  have hdst : dst = ExtChar.eos := by
    cases s with
    | char s' =>
      simp only [ParserWithEOS] at hstep
      split at hstep
      · simp at hstep; exact hstep.2.2
      · simp at hstep
    | eos =>
      simp only [ParserWithEOS] at hstep
      simp at hstep; exact hstep.2.2
  subst hdst
  -- top = [], so isPrefixOf? [] stack = some stack
  have htop : top = [] := by
    cases s with
    | char s' =>
      simp only [ParserWithEOS] at hstep
      split at hstep
      · simp at hstep; exact hstep.1
      · simp at hstep
    | eos =>
      simp only [ParserWithEOS] at hstep
      simp at hstep; exact hstep.1
  subst htop
  simp [List.isPrefixOf?] at hmatch
  exact ⟨_, hmatch⟩

omit [DecidableEq Γ] in
/-- In `ParserWithEOS`, evaluating from an all-`.eos`-state configuration set
    preserves the all-`.eos` invariant for any input word. -/
lemma ParserWithEOS_evalFrom_eos_stays
    (P : PDA Γ π σp) (S : Finset (Ch σp × List π)) (w : List (Ch Γ))
    (hall : ∀ cfg ∈ S, ∃ st', cfg = (ExtChar.eos, st')) :
    ∀ cfg ∈ (ParserWithEOS P).evalFrom S w, ∃ st', cfg = (ExtChar.eos, st') := by
  induction w generalizing S with
  | nil => exact hall
  | cons a rest ih =>
    simp only [PDA.evalFrom_cons]
    apply ih
    intro cfg hcfg
    simp only [PDA.fullStep, Finset.mem_biUnion] at hcfg
    obtain ⟨⟨s₀, stack₀⟩, hmem₀, hmem_step⟩ := hcfg
    -- s₀ = .eos (and stack₀ = st₀) by hall
    obtain ⟨st₀, heq₀⟩ := hall ⟨s₀, stack₀⟩ hmem₀
    rw [Prod.mk.injEq] at heq₀
    obtain ⟨hs₀, hstack₀⟩ := heq₀
    subst hs₀; subst hstack₀
    -- step .eos a → dst = .eos, top = []
    obtain ⟨⟨top, rep, dst⟩, hstep, hmatch⟩ := hmem_step
    simp only [ParserWithEOS] at hstep
    -- step .eos a = {([], [], .eos)}
    have hdst : dst = ExtChar.eos := by simp at hstep; exact hstep.2.2
    have htop : top = [] := by simp at hstep; exact hstep.1
    subst hdst; subst htop
    simp [List.isPrefixOf?] at hmatch
    exact ⟨_, hmatch⟩

omit [DecidableEq Γ] in
private lemma ParserWithEOS_evalFrom_eos_mem_imp_eos_state
    (P : PDA Γ π σp) (pre post : List (Ch Γ))
    (cfg : Ch σp × List π)
    (hmem : cfg ∈ (ParserWithEOS P).evalFull (pre ++ ExtChar.eos :: post)) :
    ∃ st', cfg = (ExtChar.eos, st') := by
  have hsplit :
      (ParserWithEOS P).evalFull (pre ++ ExtChar.eos :: post) =
        (ParserWithEOS P).evalFrom
          ((ParserWithEOS P).evalFrom ((ParserWithEOS P).evalFull pre) [ExtChar.eos])
          post := by
    simp only [PDA.evalFull]
    rw [show pre ++ ExtChar.eos :: post = (pre ++ [ExtChar.eos]) ++ post by
        simp [List.append_assoc],
      PDA.evalFrom_append', PDA.evalFrom_append']
  rw [hsplit] at hmem
  have hall_after :
      ∀ cfg ∈ (ParserWithEOS P).evalFrom ((ParserWithEOS P).evalFull pre) [ExtChar.eos],
        ∃ st', cfg = (ExtChar.eos, st') := by
    intro cfg hcfg
    have hstep :
        (ParserWithEOS P).evalFrom ((ParserWithEOS P).evalFull pre) [ExtChar.eos] =
          (ParserWithEOS P).fullStep ((ParserWithEOS P).evalFull pre) ExtChar.eos := rfl
    rw [hstep] at hcfg
    exact ParserWithEOS_fullStep_eos_all_eos P _ cfg hcfg
  exact ParserWithEOS_evalFrom_eos_stays P _ post hall_after cfg hmem

omit [DecidableEq Γ] in
/-- If the original parser is pruned, then the EOS-augmented parser is pruned. -/
lemma ParserWithEOS_pruned
    (P : PDA Γ π σp) (hpruned : P.pruned) :
    (ParserWithEOS P).pruned := by
  intro q st hreach
  cases q with
  | eos =>
      refine ⟨[], ?_⟩
      simp only [PDA.acceptsFrom]
      refine ⟨ExtChar.eos, ?_, ?_⟩
      · simp [PDA.evalFrom]
      · simp [ParserWithEOS]
  | char q =>
      obtain ⟨w, hmem⟩ := hreach
      by_cases heos : ExtChar.eos ∈ w
      · rw [List.mem_iff_append] at heos
        obtain ⟨pre, post, hw⟩ := heos
        rw [hw] at hmem
        obtain ⟨st', hcfg⟩ :=
          ParserWithEOS_evalFrom_eos_mem_imp_eos_state P pre post (ExtChar.char q, st) hmem
        simp at hcfg
      · obtain ⟨wplain, hwplain⟩ := List.exists_map_char_of_not_mem_eos heos
        subst hwplain
        have horig : (q, st) ∈ P.evalFull wplain :=
          ParserWithEOS_evalFull_char_mem_imp P wplain q st hmem
        obtain ⟨tail, htail⟩ := hpruned q st ⟨wplain, horig⟩
        refine ⟨tail.map ExtChar.char ++ [ExtChar.eos], ?_⟩
        simp only [PDA.acceptsFrom] at htail ⊢
        obtain ⟨f, hfmem, hfacc⟩ := htail
        rw [Finset.mem_image] at hfmem
        obtain ⟨⟨f', stf⟩, hforig, hf_eq⟩ := hfmem
        simp only at hf_eq
        subst hf_eq
        refine ⟨ExtChar.eos, ?_, ?_⟩
        · rw [Finset.mem_image]
          refine ⟨(ExtChar.eos, stf), ?_, rfl⟩
          rw [PDA.evalFrom_append']
          change (ExtChar.eos, stf) ∈
            (ParserWithEOS P).fullStep
              ((ParserWithEOS P).evalFrom {(ExtChar.char q, st)}
                (tail.map ExtChar.char)) ExtChar.eos
          have hchar_eval := ParserWithEOS_evalFrom_char_image P ({(q, st)} : Finset (σp × List π)) tail
          have hchar_mem :
              (ExtChar.char f', stf) ∈
                (ParserWithEOS P).evalFrom {(ExtChar.char q, st)} (tail.map ExtChar.char) := by
            rw [ParserWithEOS_singleton_char_image q st]
            rw [hchar_eval]
            exact Finset.mem_image.mpr ⟨(f', stf), hforig, rfl⟩
          exact (ParserWithEOS P).fullStep_subset
            ({(ExtChar.char f', stf)})
            ((ParserWithEOS P).evalFrom {(ExtChar.char q, st)}
              (tail.map ExtChar.char))
            (Finset.singleton_subset_iff.mpr hchar_mem)
            ExtChar.eos
            (by
              simp only [PDA.fullStep, Finset.mem_biUnion, Finset.mem_singleton]
              refine ⟨(ExtChar.char f', stf), rfl, ([], [], ExtChar.eos), ?_, ?_⟩
              · simp [ParserWithEOS, hfacc]
              · simp [List.isPrefixOf?])
        · simp [ParserWithEOS]

omit [DecidableEq Γ] in
lemma PDA.exists_accepts_extension_of_pruned_evalFull_nonempty
    (P : PDA Γ π σp) (hpruned : P.pruned)
    (pref : List Γ) (hne : P.evalFull pref ≠ ∅) :
    ∃ suffix : List Γ, pref ++ suffix ∈ P.accepts := by
  have hpref : pref ∈ P.intermediate := by
    simp only [PDA.intermediate, PDA.eval]
    intro himage
    rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨cfg, hcfg⟩
    have hstate : cfg.1 ∈ (P.evalFrom {(P.start, [])} pref).image Prod.fst := by
      rw [Finset.mem_image]
      exact ⟨cfg, by simpa [PDA.evalFull] using hcfg, rfl⟩
    rw [himage] at hstate
    simp at hstate
  have heq := P.pruned_intermediate_eq_prefix hpruned
  have hpref' : pref ∈ P.accepts.prefixes := by
    rwa [heq] at hpref
  simp only [Language.prefixes] at hpref'
  obtain ⟨full, hfull, hprefix⟩ := hpref'
  obtain ⟨suffix, hfull_eq⟩ := hprefix
  subst hfull_eq
  exact ⟨suffix, hfull⟩

omit [DecidableEq Γ] in
/-- If `(ParserWithEOS P).evalFull gammas ≠ ∅` and `ExtChar.eos ∈ gammas`,
    then `gammas ∈ (ParserWithEOS P).accepts`. -/
lemma ParserWithEOS_evalFull_eos_imp_accepts
    (P : PDA Γ π σp) (gammas : List (Ch Γ))
    (hne : (ParserWithEOS P).evalFull gammas ≠ ∅)
    (heos : ExtChar.eos ∈ gammas) :
    gammas ∈ (ParserWithEOS P).accepts := by
  -- Split gammas at the .eos position: gammas = pre ++ (.eos :: post)
  rw [List.mem_iff_append] at heos
  obtain ⟨pre, post, hgammas⟩ := heos
  -- Abbreviate
  let parser := ParserWithEOS P
  -- Rewrite evalFull gammas using the split
  have hne_split : parser.evalFrom
      (parser.evalFrom (parser.evalFrom {(parser.start, [])} pre) [ExtChar.eos]) post ≠ ∅ := by
    have heq : (ParserWithEOS P).evalFull gammas =
        parser.evalFrom (parser.evalFrom (parser.evalFrom {(parser.start, [])} pre)
          [ExtChar.eos]) post := by
      simp only [PDA.evalFull]
      rw [hgammas, show pre ++ ExtChar.eos :: post = (pre ++ [ExtChar.eos]) ++ post from by
            simp [List.append_assoc],
          PDA.evalFrom_append', PDA.evalFrom_append']
    rwa [heq] at hne
  -- All configs after the .eos step have .eos state
  have hall_after_eos :
      ∀ cfg ∈ parser.evalFrom (parser.evalFrom {(parser.start, [])} pre) [ExtChar.eos],
      ∃ st', cfg = (ExtChar.eos, st') := by
    intro cfg hcfg
    -- evalFrom S [.eos] = fullStep S .eos (definitionally)
    have heq : parser.evalFrom (parser.evalFrom {(parser.start, [])} pre) [ExtChar.eos] =
        parser.fullStep (parser.evalFrom {(parser.start, [])} pre) ExtChar.eos := rfl
    rw [heq] at hcfg
    exact ParserWithEOS_fullStep_eos_all_eos P _ cfg hcfg
  -- All configs in the final set have .eos state (absorbing property)
  have hall_final :
      ∀ cfg ∈ parser.evalFrom
        (parser.evalFrom (parser.evalFrom {(parser.start, [])} pre) [ExtChar.eos]) post,
      ∃ st', cfg = (ExtChar.eos, st') :=
    ParserWithEOS_evalFrom_eos_stays P _ post hall_after_eos
  -- Pick any config from the nonempty final set
  rcases Finset.nonempty_iff_ne_empty.mpr hne_split with ⟨cfg, hcfg⟩
  obtain ⟨st', rfl⟩ := hall_final cfg hcfg
  -- Show gammas ∈ accepts by exhibiting the .eos accept state
  simp only [PDA.accepts, PDA.acceptsFrom]
  refine ⟨ExtChar.eos, ?_, ?_⟩
  · rw [Finset.mem_image]
    refine ⟨(ExtChar.eos, st'), ?_, rfl⟩
    -- (ExtChar.eos, st') ∈ evalFrom {(start,[])} gammas
    rw [hgammas, show pre ++ ExtChar.eos :: post = (pre ++ [ExtChar.eos]) ++ post from by
          simp [List.append_assoc],
        PDA.evalFrom_append', PDA.evalFrom_append']
    exact hcfg
  · simp [ParserWithEOS]

set_option maxHeartbeats 3200000 in
omit [FinEnum α] in
/-- **EOS Completeness**: If `curr` extends to an **accepted** run through the
detokenizing lexer and parser via `.eos`, then `.eos` passes the GCD mask
checker after prefix `curr`.

Uses `BuildDetokLexer_hsingle` (Lemma D) for the `hsingle` hypothesis.
When the suffix output `T = []`, picks `.eos` from `singleProducible q₁`
(which is nonempty at the start state) and shows the parser can handle the
extended sequence via the `.eos` dead-loop property of `ParserWithEOS`.

Requires `hempty` and the full whitespace assumption; the latter rederives the
lexer restart hypothesis used by `BuildDetokLexer_hsingle`. -/
theorem EOSCompleteness
  [FinEnum β] [Vocabulary α β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (curr : List β)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite)
  (hviable : ∃ suffix qa gammas,
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval
      (curr.map ExtChar.char ++ (.eos :: suffix)) = some (qa, gammas) ∧
    gammas ∈ (ParserWithEOS P).accepts) :
  MaskChecker
    (Detokenizing.BuildDetokLexer (V := Ch β) spec)
    (ParserWithEOS P)
    (PreprocessParser (Detokenizing.BuildDetokLexer (V := Ch β) spec) (ParserWithEOS P))
    (BuildInverseTokenSpannerTable (Detokenizing.BuildDetokLexer (V := Ch β) spec)).snd
    curr .eos = true := by
  -- Abbreviations
  let comb := Detokenizing.BuildDetokLexer (V := Ch β) spec
  let parser := ParserWithEOS P
  have hrestart := GCDWhitespaceAssumption.existsRestartChar spec P hassum.hempty hassum.whitespace
  -- Extract the viable run witnesses
  obtain ⟨suffix, qa, gammas, heval, hacc⟩ := hviable
  -- Acceptance implies evalFull ≠ ∅
  have hparse : parser.evalFull gammas ≠ ∅ := by
    intro hempty_cfg
    change gammas ∈ (ParserWithEOS P).accepts at hacc
    simp only [PDA.accepts, PDA.acceptsFrom] at hacc
    obtain ⟨f, hfmem, _⟩ := hacc
    rw [Finset.mem_image] at hfmem
    obtain ⟨cfg, hcfg, _⟩ := hfmem
    change (ParserWithEOS P).evalFrom {((ParserWithEOS P).start, [])} gammas = ∅ at hempty_cfg
    rw [hempty_cfg] at hcfg
    simp at hcfg
  -- Step 1: Decompose the FST run
  have heval_start : comb.evalFrom comb.start
      (curr.map ExtChar.char ++ (.eos :: suffix)) = some (qa, gammas) := by
    simpa [FST.eval] using heval
  have hcurr_some : ∃ q_fst terms,
      comb.evalFrom comb.start (curr.map ExtChar.char) = some (q_fst, terms) := by
    by_contra h
    push_neg at h
    have happ := FST.evalFrom_append (M := comb) comb.start
      (curr.map ExtChar.char) (.eos :: suffix)
    cases hc : comb.evalFrom comb.start (curr.map ExtChar.char) with
    | none => rw [hc] at happ; simp at happ; rw [happ] at heval_start; simp at heval_start
    | some p => exact (h p.1 p.2 hc).elim
  obtain ⟨q_fst, terms, hcurr⟩ := hcurr_some
  have hrest_eq : ∃ out_rest,
      comb.evalFrom q_fst (.eos :: suffix) = some (qa, out_rest) ∧
      gammas = terms ++ out_rest := by
    have happ := FST.evalFrom_append (M := comb) comb.start
      (curr.map ExtChar.char) (.eos :: suffix)
    rw [hcurr] at happ; rw [happ] at heval_start
    cases hrest : comb.evalFrom q_fst (.eos :: suffix) with
    | none => simp [hrest] at heval_start
    | some p =>
      obtain ⟨qa', out'⟩ := p
      simp [hrest] at heval_start
      exact ⟨out', by rw [heval_start.1], heval_start.2.symm⟩
  obtain ⟨out_rest, hrest, hgammas_split⟩ := hrest_eq
  rcases (FST.evalFrom_cons_some_iff (M := comb)).1 hrest with
    ⟨q₁, S, T, hstep, htail, hout_eq⟩
  have hgammas : gammas = terms ++ (S ++ T) := by rw [hgammas_split, hout_eq]
  -- Step 2: Build the realizable sequence witness
  -- For both T=[] and T≠[], we need e ∈ singleProducible q₁
  -- When T≠[], e = T.head. When T=[], we use singleProducible nonemptiness.
  -- We need singleProducible q₁ to be nonempty
  by_cases hTne : T ≠ []
  · -- Case T ≠ []: same as char case
    have hhead_sp : (T.head hTne) ∈ comb.singleProducible q₁ :=
      BuildDetokLexer_hsingle spec hassum.hempty hrestart q₁ suffix qa T htail hTne
    set d := S ++ [T.head hTne] with hd_def
    have hd_rs : d ∈ RealizableSequences comb :=
      ⟨q_fst, .eos, S, q₁, T.head hTne, hstep, hhead_sp, rfl⟩
    have hd_ne : d ≠ [] := by simp [hd_def]
    have hd_dropLast : d.dropLast = S := by simp [hd_def]
    have hd_getLast : d.getLast hd_ne = T.head hTne := by simp [hd_def]
    have hitst : ExtChar.eos ∈ InverseTokenSpannerTable comb d q_fst := by
      simp only [InverseTokenSpannerTable, dif_pos hd_ne, hd_dropLast, hd_getLast, Set.mem_setOf_eq]
      exact ⟨q₁, hstep, hhead_sp⟩
    -- Parser prefix closure
    rw [hgammas] at hparse
    rw [PDA.evalFull, PDA.evalFrom_append'] at hparse
    have hST_eq : S ++ T = d ++ T.tail := by
      rw [hd_def, List.append_assoc]; congr 1
      exact (List.cons_head_tail hTne).symm
    rw [hST_eq] at hparse
    have hd_ne_empty : parser.evalFrom (parser.evalFrom {(parser.start, [])} terms) d ≠ ∅ :=
      PDA.evalFrom_prefix_nonempty parser _ d (T.tail) hparse
    rcases PDA.evalFrom_nonempty_exists_singleton parser _ d hd_ne_empty with
      ⟨⟨qp, st_p⟩, hmem_qp, hqp_d_ne⟩
    have hmask : ExtChar.eos ∈
        ComputeValidTokenMask parser (BuildInverseTokenSpannerTable comb).snd
          (PreprocessParser comb parser) q_fst qp st_p := by
      simp only [mem_ComputeValidTokenMask_preprocess_iff]
      by_cases hacc0 : (ParserWithEOS P).evalFrom {(qp, [])} d ≠ ∅
      · left; exact ⟨d, hd_rs, hacc0, hitst⟩
      · push_neg at hacc0; right
        exact ⟨d, hd_rs, hacc0,
          PDA.evalFrom_nonempty_imp_nfa_nonempty (ParserWithEOS P) qp st_p d hqp_d_ne,
          hqp_d_ne, hitst⟩
    -- Assemble MaskChecker = true
    unfold MaskChecker
    have hcomb_eval : comb.eval (curr.map ExtChar.char) = some (q_fst, terms) := by
      simp [FST.eval, hcurr]
    simp only [show (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval (List.map ExtChar.char curr) =
      some (q_fst, terms) from hcomb_eval]
    rw [Finset.fold_or_eq_true_iff, Finset.mem_image]
    refine ⟨(qp, st_p), hmem_qp, ?_⟩
    simp only [List.contains_iff_mem]
    exact hmask
  · -- Case T = []: use singleProducible nonemptiness + ParserWithEOS looping
    push_neg at hTne; subst hTne
    -- gammas = terms ++ S
    have hgammas' : gammas = terms ++ S := by simp [hgammas]
    -- q₁ is the start state
    have hq₁_start : q₁ = ((), LexingState.start (σ := σa)) :=
      BuildDetokLexer_eos_step_reaches_start spec q_fst q₁ S hstep
    -- Pick e = .eos from singleProducible q₁
    have he_sp : (ExtChar.eos : Ch Γ) ∈ comb.singleProducible q₁ := by
      rw [hq₁_start]
      exact BuildDetokLexer_singleProducible_start_nonempty spec hassum.hempty
    set e := (ExtChar.eos : Ch Γ) with he_def
    set d := S ++ [e] with hd_def
    have hd_rs : d ∈ RealizableSequences comb :=
      ⟨q_fst, .eos, S, q₁, e, hstep, he_sp, rfl⟩
    have hd_ne : d ≠ [] := by simp [hd_def]
    have hd_dropLast : d.dropLast = S := by simp [hd_def]
    have hd_getLast : d.getLast hd_ne = e := by simp [hd_def]
    have hitst : ExtChar.eos ∈ InverseTokenSpannerTable comb d q_fst := by
      simp only [InverseTokenSpannerTable, dif_pos hd_ne, hd_dropLast, hd_getLast, Set.mem_setOf_eq]
      exact ⟨q₁, hstep, he_sp⟩
    -- Parser: evalFrom {(qp, st_p)} (S ++ [e]) ≠ ∅
    -- Use the fact that S ends with .eos, so parser reaches .eos state,
    -- and then fullStep on e succeeds (ParserWithEOS looping)
    rw [hgammas'] at hparse
    rw [PDA.evalFull, PDA.evalFrom_append'] at hparse
    -- parser.evalFrom (evalFrom {start} terms) S ≠ ∅
    have hS_ne : parser.evalFrom (parser.evalFrom {(parser.start, [])} terms) S ≠ ∅ := by
      simpa using hparse
    rcases PDA.evalFrom_nonempty_exists_singleton parser _ S hS_ne with
      ⟨⟨qp, st_p⟩, hmem_qp, hqp_S_ne⟩
    -- parser.evalFrom {(qp, st_p)} S contains .eos state (since S ends with .eos)
    -- then fullStep on e succeeds
    -- S = S_init ++ [.eos] by the FST step structure
    have ⟨S_init, hS_snoc⟩ := BuildDetokLexer_eos_step_snoc spec q_fst q₁ S hstep
    -- Show evalFrom {(qp, st_p)} S has .eos configs (since S ends with .eos)
    have heos_in_eval : ∃ st'', (ExtChar.eos, st'') ∈ parser.evalFrom {(qp, st_p)} S := by
      rw [hS_snoc, PDA.evalFrom_append', PDA.evalFrom_cons]
      simp only [PDA.evalFrom]
      -- Goal: ∃ st'', (.eos, st'') ∈ fullStep (evalFrom {(qp,st_p)} S_init) .eos
      have hne' : parser.fullStep (parser.evalFrom {(qp, st_p)} S_init) ExtChar.eos ≠ ∅ := by
        have : parser.evalFrom {(qp, st_p)} (S_init ++ [ExtChar.eos]) ≠ ∅ := by rwa [← hS_snoc]
        rwa [PDA.evalFrom_append', PDA.evalFrom_cons, show ([] : List (Ch Γ)) = [] from rfl,
          PDA.evalFrom] at this
      obtain ⟨cfg, hcfg⟩ := Finset.nonempty_iff_ne_empty.mpr hne'
      obtain ⟨st'', rfl⟩ := ParserWithEOS_fullStep_eos_all_eos P _ cfg hcfg
      exact ⟨st'', hcfg⟩
    have hqp_d_ne : parser.evalFrom {(qp, st_p)} d ≠ ∅ := by
      rw [hd_def, PDA.evalFrom_append']
      exact ParserWithEOS_evalFrom_eos_extend P _ e heos_in_eval
    have hmask : ExtChar.eos ∈
        ComputeValidTokenMask parser (BuildInverseTokenSpannerTable comb).snd
          (PreprocessParser comb parser) q_fst qp st_p := by
      simp only [mem_ComputeValidTokenMask_preprocess_iff]
      by_cases hacc0 : (ParserWithEOS P).evalFrom {(qp, [])} d ≠ ∅
      · left; exact ⟨d, hd_rs, hacc0, hitst⟩
      · push_neg at hacc0; right
        exact ⟨d, hd_rs, hacc0,
          PDA.evalFrom_nonempty_imp_nfa_nonempty (ParserWithEOS P) qp st_p d hqp_d_ne,
          hqp_d_ne, hitst⟩
    -- Assemble MaskChecker = true
    unfold MaskChecker
    have hcomb_eval : comb.eval (curr.map ExtChar.char) = some (q_fst, terms) := by
      simp [FST.eval, hcurr]
    simp only [show (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval (List.map ExtChar.char curr) =
      some (q_fst, terms) from hcomb_eval]
    rw [Finset.fold_or_eq_true_iff, Finset.mem_image]
    refine ⟨(qp, st_p), hmem_qp, ?_⟩
    simp only [List.contains_iff_mem]
    exact hmask
