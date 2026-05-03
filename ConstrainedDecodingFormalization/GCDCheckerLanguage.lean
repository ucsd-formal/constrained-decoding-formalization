import ConstrainedDecodingFormalization.GCDStepProofs

/-!
# GCD checker language bridge

This module lifts the step-level GCD soundness/completeness proofs to the
accepted-language equality for the full checker.
-/

universe u v w x y z
variable {α : Type u} {β : Type x} {Γ : Type y} {π : Type v} {σp : Type w} {σa : Type z}

variable
  [FinEnum σp] [FinEnum Γ] [FinEnum α] [FinEnum σa] [FinEnum π]
  [DecidableEq σp] [DecidableEq β] [DecidableEq Γ] [DecidableEq α] [DecidableEq π]

/-! ## Checker interface connection

The one-step soundness/completeness results above are connected to the cumulative
`checkerAllows`/`checkerAccepts` interface defined in `Checker.lean` by induction
over the token prefix. The step-level theorems (`Soundness`, `Completeness`,
`GCDChecker_eos_true_imp_viable`) provide the induction step; the base case is
trivial since `checkerAllows c [] = true`.

The complete-string language equality is established by
`GCDChecker_checkerLanguage_eq_GCDLanguage` below.  The intermediate-language
statement is packaged by `GCDChecker_correct`; its productivity obligation is
now derived from the full whitespace assumption.
-/

omit [FinEnum Γ] [FinEnum α] [FinEnum σa] [DecidableEq β] [DecidableEq Γ] in
/-- Evaluating `BuildDetokLexer` on a `.char`-lifted token list depends only on the
flattened character content, not on the tokenization boundaries.

This is a key building block for path independence: two token sequences with the
same `flatMap flatten` value produce identical FST states and output lists. -/
lemma BuildDetokLexer_eval_flatMap_eq
    [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
    [DecidableEq σa] [FinEnum β] [FinEnum σa] [FinEnum α]
    (spec : LexerSpec α Γ σa) (w₁ w₂ : List β)
    (hfm : w₁.flatMap (Vocabulary.flatten (α := α)) = w₂.flatMap (Vocabulary.flatten (α := α))) :
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval (w₁.map ExtChar.char) =
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval (w₂.map ExtChar.char) := by
  -- Reduce to detokenize equality via detokenize_eq_comp
  simp only [FST.eval, Detokenizing.BuildDetokLexer]
  apply Detokenizing.detokenize_eq_comp
  -- Reduce detokenize on .char-lifted lists to flatMap flatten
  rw [Detokenizing.detokenize_flatmap, Detokenizing.detokenize_flatmap]
  -- The extended Vocabulary instance: flatten (char t) = (flatten t).map char
  -- so (w.map char).flatMap Ch_flatten = (w.flatMap flatten).map char
  -- which equals (w.flatMap flatten).map char on both sides.
  have key : ∀ (w : List β),
      (w.map ExtChar.char).flatMap (Vocabulary.flatten (α := Ch α) (β := Ch β)) =
      (w.flatMap Vocabulary.flatten).map ExtChar.char := by
    intro w
    induction w with
    | nil => simp
    | cons h t ih =>
      simp only [List.flatMap_cons, List.map_cons, List.map_append, Vocabulary.flatten]
      exact congrArg _ ih
  rw [key w₁, key w₂, hfm]

omit [FinEnum Γ] [FinEnum α] [FinEnum σa] [DecidableEq β] [DecidableEq Γ] in
/-- Evaluating `BuildDetokLexer` on arbitrary EOS-extended token lists depends
only on their flattened EOS-extended character content. -/
lemma BuildDetokLexer_eval_ch_flatMap_eq
    [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
    [DecidableEq σa] [FinEnum β] [FinEnum σa] [FinEnum α]
    (spec : LexerSpec α Γ σa) (w₁ w₂ : List (Ch β))
    (hfm : w₁.flatMap (Vocabulary.flatten (α := Ch α) (β := Ch β)) =
      w₂.flatMap (Vocabulary.flatten (α := Ch α) (β := Ch β))) :
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval w₁ =
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval w₂ := by
  simp only [FST.eval, Detokenizing.BuildDetokLexer]
  apply Detokenizing.detokenize_eq_comp
  rw [Detokenizing.detokenize_flatmap, Detokenizing.detokenize_flatmap]
  exact hfm

set_option linter.unusedSectionVars false in
/-- A single GCD checker decision depends on the current prefix only through
its flattened character content. -/
theorem GCDChecker_eq_of_flatMap_eq
    [BEq α] [BEq β] [BEq Γ] [BEq σa] [LawfulBEq σa] [Vocabulary α β]
    [DecidableEq σa]
    [FinEnum β] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum α]
    (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
    (w₁ w₂ : List β) (cand : Ch β)
    (hfm : w₁.flatMap (Vocabulary.flatten (α := α)) =
      w₂.flatMap (Vocabulary.flatten (α := α))) :
    GCDChecker spec P w₁ cand = GCDChecker spec P w₂ cand := by
  rw [GCDChecker_eq_MaskChecker, GCDChecker_eq_MaskChecker]
  apply MaskChecker_eq_of_eval_eq
  exact BuildDetokLexer_eval_flatMap_eq spec w₁ w₂ hfm

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

/-- `GCDLanguage` itself depends only on the flattened character content of the
token sequence. -/
lemma GCDLanguage_of_flatMap_eq
    [Vocabulary α β] [FinEnum β]
    (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
    (w₁ w₂ : List β)
    (hfm : w₁.flatMap (Vocabulary.flatten (α := α)) =
      w₂.flatMap (Vocabulary.flatten (α := α))) :
    w₁ ∈ GCDLanguage spec P → w₂ ∈ GCDLanguage spec P := by
  intro hw₁
  obtain ⟨qa, gammas, heval, hacc⟩ := hw₁
  refine ⟨qa, gammas, ?_, hacc⟩
  have key : ∀ (w : List β),
      (w.map ExtChar.char).flatMap (Vocabulary.flatten (α := Ch α) (β := Ch β)) =
      (w.flatMap (Vocabulary.flatten (α := α))).map ExtChar.char := by
    intro w
    induction w with
    | nil => simp
    | cons h t ih =>
      simp only [List.flatMap_cons, List.map_cons, List.map_append, Vocabulary.flatten]
      exact congrArg _ ih
  have hinput :
      (w₁.map ExtChar.char ++ [ExtChar.eos]).flatMap
          (Vocabulary.flatten (α := Ch α) (β := Ch β)) =
        (w₂.map ExtChar.char ++ [ExtChar.eos]).flatMap
          (Vocabulary.flatten (α := Ch α) (β := Ch β)) := by
    simp only [List.flatMap_append, List.flatMap_singleton]
    rw [key w₁, key w₂, hfm]
  have heq := BuildDetokLexer_eval_ch_flatMap_eq spec
    (w₁.map ExtChar.char ++ [ExtChar.eos])
    (w₂.map ExtChar.char ++ [ExtChar.eos]) hinput
  rw [← heq]
  exact heval

/-- The prefix closure of `GCDLanguage` is invariant under retokenizing the
same flattened character content. -/
lemma GCDLanguage_prefixes_iff_of_flatMap_eq
    [Vocabulary α β] [FinEnum β]
    (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
    (w₁ w₂ : List β)
    (hfm : w₁.flatMap (Vocabulary.flatten (α := α)) =
      w₂.flatMap (Vocabulary.flatten (α := α))) :
    w₁ ∈ (GCDLanguage spec P).prefixes ↔
      w₂ ∈ (GCDLanguage spec P).prefixes := by
  constructor
  · rintro ⟨v, hv, hprefix⟩
    obtain ⟨rest, hrest⟩ := hprefix
    refine ⟨w₂ ++ rest, ?_, ⟨rest, rfl⟩⟩
    apply GCDLanguage_of_flatMap_eq spec P v (w₂ ++ rest)
    · rw [← hrest]
      simp [List.flatMap_append, hfm]
    · exact hv
  · rintro ⟨v, hv, hprefix⟩
    obtain ⟨rest, hrest⟩ := hprefix
    refine ⟨w₁ ++ rest, ?_, ⟨rest, rfl⟩⟩
    apply GCDLanguage_of_flatMap_eq spec P v (w₁ ++ rest)
    · rw [← hrest]
      simp [List.flatMap_append, hfm]
    · exact hv

/-- Any prefix of a word in `GCDLanguage` passes `checkerAllows` for the GCD checker.

This is the key inductive step for completeness: we strengthen the IH from
"the full word is in the language" to "any prefix passes checkerAllows".
The induction is on the length of the prefix `w'`. -/
theorem GCDLanguage_checkerAllows_prefix
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite)
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
      apply Completeness spec P w'' v hassum
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
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite)
  (w : List β) (hw : w ∈ GCDLanguage spec P) :
  checkerAccepts (GCDChecker spec P) w = true := by
  obtain ⟨qa, gammas, heval, hacc⟩ := hw
  -- Show checkerAllows holds via the prefix lemma
  have hallows : checkerAllows (GCDChecker spec P) w = true :=
    GCDLanguage_checkerAllows_prefix spec P hassum w
      ⟨qa, gammas, heval, hacc⟩ w [] (by simp)
  -- Show GCDChecker w .eos = true via EOSCompleteness
  have heos : GCDChecker spec P w .eos = true := by
    apply EOSCompleteness spec P w hassum
    refine ⟨[], qa, gammas, ?_, hacc⟩
    simp only [FST.eval] at heval ⊢
    exact heval
  -- Combine: checkerAccepts = checkerAllows && c w .eos = true
  simp only [checkerAccepts, hallows, heos, decide_true, Bool.and_self]

/-- The checker language of `GCDChecker spec P` equals `GCDLanguage spec P`. -/
theorem GCDChecker_checkerLanguage_eq_GCDLanguage
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite) :
  checkerLanguage (β := β) (GCDChecker spec P) = GCDLanguage spec P := by
  ext w
  simp only [checkerLanguage, checkerAccepts]
  constructor
  · -- (→): if checker accepts w, then w ∈ GCDLanguage spec P
    intro h
    -- Extract GCDChecker spec P w .eos = true from h
    have heos_true : GCDChecker spec P w .eos = true := by
      have := (Bool.and_eq_true_iff.mp h).2
      simpa using this
    -- By GCDChecker_eos_true_imp_viable, get a viable FST run with suffix
    obtain ⟨suffix, qa_full, gammas_full, heval_full, hparse_full⟩ :=
      GCDChecker_eos_true_imp_viable spec P w heos_true
    -- Abbreviate
    let comb := Detokenizing.BuildDetokLexer (V := Ch β) spec
    -- Split FST run at w.map char: get comb.eval (w.map char) = some (q_fst, terms)
    have heval_full_from : comb.evalFrom comb.start
        (w.map ExtChar.char ++ (.eos :: suffix)) = some (qa_full, gammas_full) := by
      simpa [FST.eval] using heval_full
    have hcurr_some : ∃ q_fst terms,
        comb.evalFrom comb.start (w.map ExtChar.char) = some (q_fst, terms) := by
      by_contra hall
      push_neg at hall
      have happ := FST.evalFrom_append (M := comb) comb.start
        (w.map ExtChar.char) (.eos :: suffix)
      cases hc : comb.evalFrom comb.start (w.map ExtChar.char) with
      | none => rw [hc] at happ; simp at happ; rw [happ] at heval_full_from; simp at heval_full_from
      | some p => exact (hall p.1 p.2 hc).elim
    obtain ⟨q_fst, terms, hcurr⟩ := hcurr_some
    -- Split FST run at [.eos]: get comb.step q_fst .eos = some (q₁, S)
    have hrest_from : ∃ out_rest,
        comb.evalFrom q_fst (.eos :: suffix) = some (qa_full, out_rest) ∧
        gammas_full = terms ++ out_rest := by
      have happ := FST.evalFrom_append (M := comb) comb.start
        (w.map ExtChar.char) (.eos :: suffix)
      rw [hcurr] at happ; rw [happ] at heval_full_from
      cases hrest : comb.evalFrom q_fst (.eos :: suffix) with
      | none => simp [hrest] at heval_full_from
      | some p =>
        simp only [hrest, Option.map_some, Option.some.injEq, Prod.mk.injEq] at heval_full_from
        obtain ⟨hqa, hterms⟩ := heval_full_from
        -- hqa : p.1 = qa_full, hterms : terms ++ p.2 = gammas_full
        refine ⟨p.2, ?_, hterms.symm⟩
        have heqp : p = (qa_full, p.2) := Prod.ext hqa rfl
        rw [heqp]
    obtain ⟨out_rest, hrest, hgammas_split⟩ := hrest_from
    -- Split the .eos cons step: step at .eos gives (q₁, S)
    rcases (FST.evalFrom_cons_some_iff (M := comb)).1 hrest with
      ⟨q₁, S, T, hstep, htail, hout_eq⟩
    -- Define gammas₁ = terms ++ S (output after processing w ++ [.eos])
    set gammas₁ := terms ++ S with hgammas₁_def
    -- comb.eval (w.map char ++ [.eos]) = some (q₁, gammas₁)
    have heval_eos : comb.eval (w.map ExtChar.char ++ [.eos]) = some (q₁, gammas₁) := by
      simp only [FST.eval]
      have happ := FST.evalFrom_append (M := comb) comb.start
        (w.map ExtChar.char) [.eos]
      rw [hcurr] at happ
      simp only [happ]
      -- comb.evalFrom q_fst [.eos] = some (q₁, S)
      have hstep_eos : comb.evalFrom q_fst [ExtChar.eos] = some (q₁, S) := by
        rw [FST.evalFrom_cons_some_iff]
        exact ⟨q₁, S, [], hstep, by simp [FST.evalFrom], by simp⟩
      simp [hstep_eos, hgammas₁_def]
    -- .eos ∈ gammas₁ (since .eos ∈ S by BuildDetokLexer_eos_step_eos_in_output)
    have heos_in_S : ExtChar.eos ∈ S :=
      BuildDetokLexer_eos_step_eos_in_output spec q_fst q₁ S hstep
    have heos_in_gammas₁ : ExtChar.eos ∈ gammas₁ := by
      simp [hgammas₁_def, List.mem_append]
      right; exact heos_in_S
    -- (ParserWithEOS P).evalFull gammas₁ ≠ ∅
    -- from evalFull gammas_full ≠ ∅ where gammas_full = gammas₁ ++ T
    have hgammas_full_split : gammas_full = gammas₁ ++ T := by
      rw [hgammas_split, hout_eq, hgammas₁_def, List.append_assoc]
    have hparse_gammas₁ : (ParserWithEOS P).evalFull gammas₁ ≠ ∅ := by
      intro h
      apply hparse_full
      rw [hgammas_full_split, (ParserWithEOS P).evalFull_append gammas₁ T, h]
      simp
    -- gammas₁ ∈ (ParserWithEOS P).accepts
    have hacc_gammas₁ : gammas₁ ∈ (ParserWithEOS P).accepts :=
      ParserWithEOS_evalFull_eos_imp_accepts P gammas₁ hparse_gammas₁ heos_in_gammas₁
    -- Therefore w ∈ GCDLanguage
    exact ⟨q₁, gammas₁, heval_eos, hacc_gammas₁⟩
  · -- (←): if w ∈ GCDLanguage spec P, then checker accepts w
    intro hw
    exact GCDLanguage_imp_checkerAccepts spec P hassum w hw
