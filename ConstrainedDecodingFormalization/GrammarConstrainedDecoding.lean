import ConstrainedDecodingFormalization.PDA
import ConstrainedDecodingFormalization.Lexing
import ConstrainedDecodingFormalization.RealizableSequence
import ConstrainedDecodingFormalization.Vocabulary
-- Actual implementation of grammar constrained decoding

universe u v w x y z
variable { α : Type u } { β : Type x } { Γ : Type y } { π : Type v } { σp : Type w } { σa : Type z }

variable
  [ FinEnum σp ] [ FinEnum Γ ] [ FinEnum α ] [ FinEnum σa ] [ FinEnum π ]
  [ DecidableEq σp ] [DecidableEq β] [DecidableEq Γ ] [ DecidableEq α ] [ DecidableEq π ]

abbrev PPTable (α σp σa Γ) := (σp → σa → (List α × List (List Γ) × List (List Γ)))
-- todo use a better solution for extending the number of states by 1
def ParserWithEOS  (p: PDA Γ π σp) : PDA (Ch Γ) π (Ch σp) :=
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

def stepSet (p: PDA Γ π σp) (q : Finset σp) (s : Γ) : Finset σp :=
    Finset.biUnion q (fun q' => (p.step q' s).image fun x => x.2.2)

def evalFrom (p: PDA Γ π σp) (q : Finset σp) (s : List Γ) : Finset σp
  :=
  List.foldl (stepSet p) q s

omit [DecidableEq Γ] [DecidableEq π]
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

def PreprocessParser (fst_comp : FST α Γ σa) (p : PDA Γ π σp) : PPTable α σp σa Γ :=
  let (re, tist) := BuildInverseTokenSpannerTable fst_comp
  fun qp =>
    let accepted := re.filter (λ s => (p.evalFrom {(qp, [])} s) ≠  ∅)
    let rejected := re.filter (λ s => FinsetNFA.evalFrom p {qp} s ≠ ∅)

    let dependent := List.diff (List.diff re accepted) rejected
    fun qa =>
      let accepted_a := (accepted.map (fun tok => (tist tok qa))).foldl List.append []
      let accepted_a := accepted_a.dedup
      let dependent_a := dependent.filter (fun tok => (tist tok qa) ≠ [])
      let dependent_a := dependent_a.dedup
      (accepted_a, dependent_a, accepted)

lemma mem_preprocess_accepted_sequences_iff
  (fst_comp : FST α Γ σa) (p : PDA Γ π σp) (qp : σp) (qa : σa) (d : List Γ) :
  d ∈ (PreprocessParser fst_comp p qp qa).2.2 ↔
    d ∈ RealizableSequences fst_comp ∧
    p.evalFrom {(qp, [])} d ≠ ∅ := by
  letI : BEq Γ := instBEqOfDecidableEq
  letI : ReflBEq Γ := ⟨by intro a; simp⟩
  letI : LawfulBEq Γ := ⟨by intro a b h; simpa using h⟩
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
      (fun s => FinsetNFA.evalFrom p {qp} s ≠ ∅)) ↔
    d ∈ RealizableSequences fst_comp ∧
    FinsetNFA.evalFrom p {qp} d ≠ ∅ := by
  letI : BEq Γ := instBEqOfDecidableEq
  letI : ReflBEq Γ := ⟨by intro a; simp⟩
  letI : LawfulBEq Γ := ⟨by intro a b h; simpa using h⟩
  constructor
  · intro hd
    have hrej :
        d ∈ (BuildInverseTokenSpannerTable fst_comp).fst ∧
        FinsetNFA.evalFrom p {qp} d ≠ ∅ := by
      simpa [List.mem_filter] using hd
    exact ⟨(mem_re_iff (fst_comp := fst_comp) (d := d)).1 hrej.1, hrej.2⟩
  · rintro ⟨hd, hrej⟩
    have hmem :
        d ∈ (BuildInverseTokenSpannerTable fst_comp).fst ∧
        FinsetNFA.evalFrom p {qp} d ≠ ∅ :=
      ⟨(mem_re_iff (fst_comp := fst_comp) (d := d)).2 hd, hrej⟩
    simpa [List.mem_filter] using hmem

lemma mem_preprocess_accepted_tokens_iff
  (fst_comp : FST α Γ σa) (p : PDA Γ π σp) (qp : σp) (qa : σa) (tok : α) :
  tok ∈ (PreprocessParser fst_comp p qp qa).1 ↔
    ∃ d,
      d ∈ RealizableSequences fst_comp ∧
      p.evalFrom {(qp, [])} d ≠ ∅ ∧
      tok ∈ InverseTokenSpannerTable fst_comp d qa := by
  letI : BEq Γ := instBEqOfDecidableEq
  letI : ReflBEq Γ := ⟨by intro a; simp⟩
  letI : LawfulBEq Γ := ⟨by intro a b h; simpa using h⟩
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

lemma mem_preprocess_dependent_sequences_iff
  (fst_comp : FST α Γ σa) (p : PDA Γ π σp) (qp : σp) (qa : σa) (d : List Γ) :
  d ∈ (PreprocessParser fst_comp p qp qa).2.1 ↔
    d ∈ RealizableSequences fst_comp ∧
    p.evalFrom {(qp, [])} d = ∅ ∧
    FinsetNFA.evalFrom p {qp} d = ∅ ∧
    (BuildInverseTokenSpannerTable fst_comp).snd d qa ≠ [] := by
  letI : BEq Γ := instBEqOfDecidableEq
  letI : ReflBEq Γ := ⟨by intro a; simp⟩
  letI : LawfulBEq Γ := ⟨by intro a b h; simpa using h⟩
  let re := (BuildInverseTokenSpannerTable fst_comp).fst
  let accepted := re.filter (fun s => p.evalFrom {(qp, [])} s ≠ ∅)
  let rejected := re.filter (fun s => FinsetNFA.evalFrom p {qp} s ≠ ∅)
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
      · exact hrej
      · exfalso
        exact hdiff2.2 ((mem_rejected_sequences_iff
          (fst_comp := fst_comp) (p := p) (qp := qp) (d := d)).2
            ⟨(mem_re_iff (fst_comp := fst_comp) (d := d)).1 hdiff1.1, hrej⟩)
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
      exact hrej'.2 hrej
    have hdep0 : d ∈ List.diff re accepted := List.mem_diff_of_mem hre hnotacc
    have hdep : d ∈ dependent := List.mem_diff_of_mem hdep0 hnotrej
    have hdepf :
        d ∈ dependent.filter (fun tok => (BuildInverseTokenSpannerTable fst_comp).snd tok qa ≠ []) := by
      simpa [List.mem_filter] using And.intro hdep hitst
    simpa [PreprocessParser, re, accepted, rejected, dependent, List.mem_filter, List.mem_dedup] using hdepf

def ComputeValidTokenMask (P : PDA Γ π σp) (itst : List Γ → σa → List α) (table : PPTable α σp σa Γ) (qa : σa) (qp : σp) (st : List π) : List α := Id.run do
  let mut accepted := (table qp qa).fst
  for d in (table qp qa).2.1 do
    if (P.evalFrom {(qp, st)} d) ≠ ∅ then
      accepted := accepted ++ (itst d qa)

  accepted.dedup


-- TODO use more consistent notions of variable names
/- lexer spec is the automata in terms of the characters
   we also have the actual tokens
   and then the parser
-/
def GCDChecker
   [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
   [DecidableEq σa]
   [FinEnum β] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
   (spec: LexerSpec α Γ σa) (parser: PDA Γ π σp) : List β → Ch β → Bool :=
  let comb : FST (Ch β) (Ch Γ) (Unit × LexingState σa) := Detokenizing.BuildDetokLexer (V := Ch β) spec

  let parser := ParserWithEOS parser

  let pp_table := PreprocessParser comb parser
  let ⟨_, itst⟩ := BuildInverseTokenSpannerTable comb

  fun curr cand =>
    match comb.eval (curr.map ExtChar.char) with
    | none => false
    | some (q_fst, terms) =>
      let q_pda := parser.evalFrom {(parser.start, [])} terms
      let in_curr := q_pda.image
        (fun (q_parse, st) => (ComputeValidTokenMask parser itst pp_table q_fst q_parse st).contains cand)
      Finset.fold Bool.or false id in_curr

-- want to say that for any lexer state
-- any thing that starts with a realizable sequence is producible
-- and producible if and only if that's the case
theorem realizableSequencesComplete [Vocabulary α β] (spec: LexerSpec α Γ σa) :
  True := by
  sorry

-- a token is accepted if and only if in the current state
--
theorem accept_if_ComputedValidTokenMask
  [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
  [DecidableEq σa]
  [FinEnum β] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
  (P : PDA Γ π σp) (spec: LexerSpec α Γ σa) :
  let comb : FST (Ch β) (Ch Γ) (Unit × LexingState σa) := Detokenizing.BuildDetokLexer (V := Ch β) spec

  let parser := ParserWithEOS P

  let pp_table := PreprocessParser comb parser
  let ⟨_, itst⟩ := BuildInverseTokenSpannerTable comb
  ∀ qp st qa t,
    t ∈ (ComputeValidTokenMask parser itst pp_table qa qp st) ↔
    ∃ ts qa' gammas,
      comb.evalFrom qa (t :: ts) = some (qa', gammas) ∧
      gammas ∈ parser.acceptsFrom qp st := by sorry
