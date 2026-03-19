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

/-! ### ParserWithEOS: `.char` inputs preserve `.char` states -/

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
  simp only [ParserWithEOS, Finset.mem_biUnion] at hmem'
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

/-- Evaluating `BuildLexingFST` on a list of `.char` inputs never produces
    `ExtChar.eos` in the output. -/
lemma BuildLexingFST_char_evalFrom_no_eos
    (spec : LexerSpec α Γ σa)
    (q : LexingState σa) (w : List α) (q' : LexingState σa) (out : List (Ch Γ))
    (hrun : (BuildLexingFST spec).evalFrom q (w.map ExtChar.char) = some (q', out)) :
    ExtChar.eos ∉ out := by
  induction w generalizing q out with
  | nil =>
    simp [FST.evalFrom] at hrun; obtain ⟨_, rfl⟩ := hrun; simp
  | cons a rest ih =>
    rw [List.map_cons] at hrun
    rw [FST.evalFrom_cons_some_iff] at hrun
    obtain ⟨q₁, S, T, hstep, htail, rfl⟩ := hrun
    have hS : ExtChar.eos ∉ S := BuildLexingFST_char_step_no_eos spec q a q₁ S hstep
    have hT : ExtChar.eos ∉ T := ih q₁ T htail
    simp only [List.mem_append, not_or]; exact ⟨hS, hT⟩

/-! ### BuildDetokLexer: `.char` evaluation never produces `.eos` output -/

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
    simp [FST.evalFrom] at hrun; obtain ⟨_, rfl⟩ := hrun; simp
  | cons tok rest ih =>
    rw [List.map_cons] at hrun
    rw [FST.evalFrom_cons_some_iff] at hrun
    obtain ⟨q₁, S, T, hstep, htail, rfl⟩ := hrun
    have hS : ExtChar.eos ∉ S :=
      BuildDetokLexer_char_step_no_eos spec q tok q₁ S hstep
    have hT : ExtChar.eos ∉ T := ih q₁ T htail
    simp only [List.mem_append, not_or]; exact ⟨hS, hT⟩

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
    (hrun : comb.evalFrom q₁ w = some (qa', T)) (hne : T ≠ []),
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
checker accepts the token. Uses `BuildDetokLexer_singleProducible_of_evalFrom`
(Lemma D) to discharge the `hsingle` hypothesis.
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

Requires the lexer spec hypotheses `hempty` (empty string not accepted) and
`hrestart` (every accepting state has a restart character). -/
theorem Completeness
  [FinEnum β] [Vocabulary α β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (curr : List β) (cand : β)
  (hempty : [] ∉ spec.automaton.accepts)
  (hrestart : ∀ s ∈ spec.automaton.accept,
    ∃ c : α, spec.automaton.step s c = none ∧
      (spec.automaton.step spec.automaton.start c).isSome)
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
    BuildDetokLexer_hsingle spec hempty hrestart q₁ suffix qa T htail hTne
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

/-- `ParserWithEOS` at `.eos` state is a fixed point: `fullStep` returns the
same configuration. -/
private lemma ParserWithEOS_eos_fullStep_eq
    (P : PDA Γ π σp) (st : List π) (c : Ch Γ) :
    (ExtChar.eos, st) ∈ (ParserWithEOS P).fullStep {(ExtChar.eos, st)} c := by
  simp only [PDA.fullStep, Finset.mem_biUnion, Finset.mem_singleton]
  refine ⟨(ExtChar.eos, st), rfl, ?_⟩
  simp only [Finset.mem_biUnion]
  refine ⟨([], [], ExtChar.eos), ?_, ?_⟩
  · show ([], [], ExtChar.eos) ∈ (ParserWithEOS P).step ExtChar.eos c
    simp [ParserWithEOS]
  · -- top = [], so isPrefixOf? [] st = some st, result = {(.eos, [] ++ st)} = {(.eos, st)}
    simp [List.isPrefixOf?]

/-- `ParserWithEOS` at `.eos` state loops: `fullStep` on any input from
a configuration at `.eos` state is nonempty. -/
private lemma ParserWithEOS_eos_fullStep_nonempty
    (P : PDA Γ π σp) (st : List π) (c : Ch Γ) :
    (ParserWithEOS P).fullStep {(ExtChar.eos, st)} c ≠ ∅ := by
  intro h
  have := ParserWithEOS_eos_fullStep_eq P st c
  rw [h] at this
  simp at this

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
  simp only [Vocabulary.flatten, FST.evalFrom, BuildLexingFST, Id.run, LexingState.src,
    hstart_not_accept, dite_false, ite_true]
  simp

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
  simp only [Detokenizing.BuildDetokLexer, Detokenizing.detokenizer_comp_step,
    Vocabulary.flatten, FST.evalFrom, List.foldl,
    BuildLexingFST, Id.run] at hstep
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
  simp only [Vocabulary.flatten, FST.evalFrom, BuildLexingFST, Id.run] at hstep
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

/-- After `.eos` step in `BuildDetokLexer`, `.eos` appears in the output. -/
private lemma BuildDetokLexer_eos_step_eos_in_output
    [Vocabulary α β]
    (spec : LexerSpec α Γ σa) (q_fst : Unit × LexingState σa)
    (q₁ : Unit × LexingState σa) (S : List (Ch Γ))
    (hstep : (Detokenizing.BuildDetokLexer (V := Ch β) spec).step q_fst
      ExtChar.eos = some (q₁, S)) :
    ExtChar.eos ∈ S := by
  simp only [Detokenizing.BuildDetokLexer] at hstep
  rw [Detokenizing.detokenizer_comp_step] at hstep
  simp only [Vocabulary.flatten, FST.evalFrom, BuildLexingFST, Id.run] at hstep
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
  simp only [Vocabulary.flatten, FST.evalFrom, BuildLexingFST, Id.run] at hstep
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

/-- In `ParserWithEOS`, after `fullStep` on `.eos` input, every config in the
result is at `.eos` state. -/
private lemma ParserWithEOS_fullStep_eos_all_eos
    (P : PDA Γ π σp) (X : Finset (Ch σp × List π))
    (cfg : Ch σp × List π)
    (hcfg : cfg ∈ (ParserWithEOS P).fullStep X ExtChar.eos) :
    ∃ st', cfg = (ExtChar.eos, st') := by
  simp only [PDA.fullStep, Finset.mem_biUnion] at hcfg
  obtain ⟨⟨s, stack⟩, _, hmem⟩ := hcfg
  simp only [Finset.mem_biUnion] at hmem
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

set_option maxHeartbeats 3200000 in
/-- **EOS Completeness**: If `curr` extends to an **accepted** run through the
detokenizing lexer and parser via `.eos`, then `.eos` passes the GCD mask
checker after prefix `curr`.

Uses `BuildDetokLexer_hsingle` (Lemma D) for the `hsingle` hypothesis.
When the suffix output `T = []`, picks `.eos` from `singleProducible q₁`
(which is nonempty at the start state) and shows the parser can handle the
extended sequence via the `.eos` dead-loop property of `ParserWithEOS`.

Requires the lexer spec hypotheses `hempty` (empty string not accepted) and
`hrestart` (every accepting state has a restart character). -/
theorem EOSCompleteness
  [FinEnum β] [Vocabulary α β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) (curr : List β)
  (hempty : [] ∉ spec.automaton.accepts)
  (hrestart : ∀ s ∈ spec.automaton.accept,
    ∃ c : α, spec.automaton.step s c = none ∧
      (spec.automaton.step spec.automaton.start c).isSome)
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
      BuildDetokLexer_hsingle spec hempty hrestart q₁ suffix qa T htail hTne
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
      exact BuildDetokLexer_singleProducible_start_nonempty spec hempty
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

/-! ## Checker interface connection

Connecting the one-step soundness/completeness results above to the cumulative
`checkerAllows`/`checkerAccepts` interface defined in `Checker.lean` requires
induction over the token prefix. The step-level theorems (`Soundness`,
`Completeness`, `GCDChecker_eos_true_imp_viable`) provide the induction step;
the base case is trivial since `checkerAllows c [] = true`.

Full connection to `checkerSound` and `checkerComplete` is deferred pending
completion of the remaining sorry in `MaskChecker_viable_imp_char_true`.
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

/-- The target language of the GCD checker: token sequences `w` such that the
composed detokenizing lexer processes `w.map char ++ [.eos]` successfully and
the EOS-augmented parser accepts the resulting terminal sequence. -/
def GCDLanguage
  [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
  [FinEnum β] [FinEnum σa] [FinEnum α]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp) : Language β :=
  { w | ∃ qa gammas,
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval
      (w.map ExtChar.char ++ [.eos]) = some (qa, gammas) ∧
    gammas ∈ (ParserWithEOS P).accepts }

/-- Any prefix of a word in `GCDLanguage` passes `checkerAllows` for the GCD checker.

This is the key inductive step for completeness: we strengthen the IH from
"the full word is in the language" to "any prefix passes checkerAllows".
The induction is on the length of the prefix `w'`. -/
private theorem GCDLanguage_checkerAllows_prefix
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  (hempty : [] ∉ spec.automaton.accepts)
  (hrestart : ∀ s ∈ spec.automaton.accept,
    ∃ c : α, spec.automaton.step s c = none ∧
      (spec.automaton.step spec.automaton.start c).isSome)
  (w : List β) (hw : w ∈ GCDLanguage spec P)
  (w' : List β) (rest : List β) (hrest : w = w' ++ rest) :
  checkerAllows (GCDChecker spec P) w' = true := by
  -- Extract the GCDLanguage witness
  obtain ⟨qa, gammas, heval, hacc⟩ := hw
  -- We proceed by strong induction on w'.length.
  -- The key property: for any prefix w' of w (i.e. w = w' ++ rest),
  -- checkerAllows holds.
  -- We use Nat.rec_aux on the reverse of w':
  -- specifically, we show the stronger statement:
  -- ∀ (n : Nat) (w' rest : List β), w'.length = n → w = w' ++ rest →
  --   checkerAllows (GCDChecker spec P) w' = true
  suffices h : ∀ (n : Nat) (w' rest : List β),
      w'.length = n → w = w' ++ rest →
      checkerAllows (GCDChecker spec P) w' = true from
    h w'.length w' rest rfl hrest
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro w' rest hlen hweq
    -- Case split: is w' empty or w' = w'' ++ [v]?
    cases List.eq_nil_or_concat w' with
    | inl hnil =>
      subst hnil; simp [checkerAllows_nil]
    | inr hexist =>
      obtain ⟨w'', v, hconcat⟩ := hexist
      subst hconcat
      -- w' = w'' ++ [v], so w = w'' ++ ([v] ++ rest)
      have hlen' : w''.length < n := by
        rw [← hlen]; simp [List.length_append]
      have hrest' : w = w'' ++ ([v] ++ rest) := by
        rw [hweq]; simp [List.append_assoc]
      -- IH: checkerAllows c w'' = true
      have ih_allows : checkerAllows (GCDChecker spec P) w'' = true :=
        ih w''.length hlen' w'' ([v] ++ rest) rfl hrest'
      -- Reduce to two subgoals via checkerAllows_snoc
      -- Note: List.eq_nil_or_concat gives concat form; normalize to append form
      simp only [List.concat_eq_append] at *
      rw [checkerAllows_snoc, Bool.and_eq_true]
      refine ⟨?_, ih_allows⟩
      -- Apply Completeness: suffix = rest.map ExtChar.char ++ [.eos]
      -- The eval witness: eval (((w'' ++ [v]).map char) ++ (rest.map char ++ [.eos])) = some (qa, gammas)
      -- This equals eval (w.map char ++ [.eos]) = some (qa, gammas) (= heval)
      apply Completeness spec P w'' v hempty hrestart
      refine ⟨rest.map ExtChar.char ++ [.eos], qa, gammas, ?_, hacc⟩
      -- Need: eval (((w'' ++ [v]).map char) ++ rest.map char ++ [.eos]) = some (qa, gammas)
      -- From heval: evalFrom start (w.map char ++ [.eos]) = some (qa, gammas)
      -- and hweq: w = w'' ++ [v] ++ rest (after concat_eq_append normalization)
      simp only [FST.eval] at heval ⊢
      have heq : (w'' ++ [v]).map (ExtChar.char (α := β)) ++ (rest.map ExtChar.char ++ [.eos]) =
          w.map ExtChar.char ++ [.eos] := by
        simp [hweq, List.map_append, List.append_assoc]
      rw [heq]
      exact heval

/-- If `w ∈ GCDLanguage spec P`, then the GCD checker accepts `w`. -/
theorem GCDLanguage_imp_checkerAccepts
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  (hempty : [] ∉ spec.automaton.accepts)
  (hrestart : ∀ s ∈ spec.automaton.accept,
    ∃ c : α, spec.automaton.step s c = none ∧
      (spec.automaton.step spec.automaton.start c).isSome)
  (w : List β) (hw : w ∈ GCDLanguage spec P) :
  checkerAccepts (GCDChecker spec P) w = true := by
  obtain ⟨qa, gammas, heval, hacc⟩ := hw
  -- Show checkerAllows holds via the prefix lemma
  have hallows : checkerAllows (GCDChecker spec P) w = true :=
    GCDLanguage_checkerAllows_prefix spec P hempty hrestart w
      ⟨qa, gammas, heval, hacc⟩ w [] (by simp)
  -- Show GCDChecker w .eos = true via EOSCompleteness
  have heos : GCDChecker spec P w .eos = true := by
    apply EOSCompleteness spec P w hempty hrestart
    refine ⟨[], qa, gammas, ?_, hacc⟩
    simp only [FST.eval] at heval ⊢
    exact heval
  -- Combine: checkerAccepts = checkerAllows && c w .eos = true
  simp only [checkerAccepts, hallows, heos, decide_true, Bool.and_self]

/-- The GCD mask checker, viewed as an abstract `Checker`, is complete with
respect to the language defined by the composed detokenizing lexer and parser:
it accepts exactly the strings in that language, and its intermediate language
is the prefix closure.

**Status**: The `checkerLanguage` direction is proved using
`GCDLanguage_imp_checkerAccepts`. The reverse direction (Soundness-based)
and the `checkerIntermediateLanguage` direction remain sorry'd. -/
theorem GCDChecker_complete
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  (hempty : [] ∉ spec.automaton.accepts)
  (hrestart : ∀ s ∈ spec.automaton.accept,
    ∃ c : α, spec.automaton.step s c = none ∧
      (spec.automaton.step spec.automaton.start c).isSome) :
  checkerComplete (β := β) (GCDChecker spec P) (GCDLanguage spec P) := by
  constructor
  · -- checkerLanguage (GCDChecker spec P) = GCDLanguage spec P
    ext w
    simp only [checkerLanguage, checkerAccepts]
    constructor
    · -- (→): if checker accepts w, then w ∈ GCDLanguage spec P
      intro h
      -- TODO: requires Soundness (reverse direction)
      sorry
    · -- (←): if w ∈ GCDLanguage spec P, then checker accepts w
      intro hw
      exact GCDLanguage_imp_checkerAccepts spec P hempty hrestart w hw
  · -- checkerIntermediateLanguage (GCDChecker spec P) = (GCDLanguage spec P).prefixes
    -- TODO: requires inductive prefix argument and checkerAllowsTermination
    sorry
