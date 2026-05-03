import ConstrainedDecodingFormalization.GCDCheckerLanguage

/-!
# GCD checker productivity and final correctness

This module contains the productivity proof derived from the full whitespace
assumption and parser prunedness, plus path independence and the final
`checkerCorrect` theorem.
-/

universe u v w x y z
variable {α : Type u} {β : Type x} {Γ : Type y} {π : Type v} {σp : Type w} {σa : Type z}

variable
  [FinEnum σp] [FinEnum Γ] [FinEnum α] [FinEnum σa] [FinEnum π]
  [DecidableEq σp] [DecidableEq β] [DecidableEq Γ] [DecidableEq α] [DecidableEq π]

private lemma GCDChecker_checkerAccepts_of_allowed_accepted_suffix
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite)
  (curr tail : List β) (suffix : List (Ch β))
  (hcurr : checkerAllows (GCDChecker spec P) curr = true)
  (hrun : ∃ qa gammas,
    (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval
      (curr.map ExtChar.char ++ tail.map ExtChar.char ++ (ExtChar.eos :: suffix)) =
        some (qa, gammas) ∧
    gammas ∈ (ParserWithEOS P).accepts) :
  checkerAccepts (GCDChecker spec P) (curr ++ tail) = true := by
  induction tail generalizing curr with
  | nil =>
      obtain ⟨qa, gammas, heval, hacc⟩ := hrun
      have heos : GCDChecker spec P curr ExtChar.eos = true := by
        rw [GCDChecker_eq_MaskChecker]
        apply EOSCompleteness spec P curr hassum
        refine ⟨suffix, qa, gammas, ?_, hacc⟩
        simpa [List.append_assoc] using heval
      simp [checkerAccepts, hcurr, heos]
  | cons next rest ih =>
      obtain ⟨qa, gammas, heval, hacc⟩ := hrun
      have hnext : GCDChecker spec P curr (ExtChar.char next) = true := by
        rw [GCDChecker_eq_MaskChecker]
        apply Completeness spec P curr next hassum
        refine ⟨rest.map ExtChar.char ++ (ExtChar.eos :: suffix), qa, gammas, ?_, hacc⟩
        simpa [List.map_append, List.append_assoc] using heval
      have hcurr_next : checkerAllows (GCDChecker spec P) (curr ++ [next]) = true := by
        rw [checkerAllows_snoc]
        simp [hnext, hcurr]
      have hrun_next : ∃ qa gammas,
          (Detokenizing.BuildDetokLexer (V := Ch β) spec).eval
            ((curr ++ [next]).map ExtChar.char ++ rest.map ExtChar.char ++
              (ExtChar.eos :: suffix)) = some (qa, gammas) ∧
          gammas ∈ (ParserWithEOS P).accepts := by
        refine ⟨qa, gammas, ?_, hacc⟩
        simpa [List.map_append, List.append_assoc] using heval
      have haccept_next := ih (curr ++ [next]) hcurr_next hrun_next
      simpa [List.append_assoc] using haccept_next

private lemma GCDChecker_char_true_head_witness
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  (curr : List β) (cand : β)
  (h : GCDChecker spec P curr (ExtChar.char cand) = true) :
  let comb := Detokenizing.BuildDetokLexer (V := Ch β) spec
  let parser := ParserWithEOS P
  ∃ q_fst terms qp st q₁ S head,
    comb.eval (curr.map ExtChar.char) = some (q_fst, terms) ∧
    (qp, st) ∈ parser.evalFrom {(parser.start, [])} terms ∧
    comb.step q_fst (ExtChar.char cand) = some (q₁, S) ∧
    head ∈ comb.singleProducible q₁ ∧
    parser.evalFrom {(qp, st)} (S ++ [head]) ≠ ∅ := by
  intro comb parser
  rw [GCDChecker_eq_MaskChecker] at h
  obtain ⟨q_fst, terms, qp, st, hcomb, hcfg, hmask⟩ :=
    MaskChecker_true_witness
      (comb := comb) (parser := parser)
      (curr := curr) (cand := ExtChar.char cand) h
  have hmask_cases := (mem_ComputeValidTokenMask_preprocess_iff
    (fst_comp := comb) (P := parser) (qa := q_fst) (qp := qp) (st := st)
    (tok := ExtChar.char cand)).1 hmask
  rcases hmask_cases with
    ⟨d, _hrs, hacc0, hitst⟩ |
    ⟨d, _hrs, _hacc0, _hnfa, hcur, hitst⟩
  · have hd_ne : d ≠ [] := by
      intro hd
      subst hd
      simp [InverseTokenSpannerTable] at hitst
    have hitst' := hitst
    simp only [InverseTokenSpannerTable, dif_pos hd_ne, Set.mem_setOf_eq] at hitst'
    obtain ⟨q₁, hstep, hsingle⟩ := hitst'
    refine ⟨q_fst, terms, qp, st, q₁, d.dropLast, d.getLast hd_ne,
      hcomb, hcfg, hstep, hsingle, ?_⟩
    have hparse : parser.evalFrom {(qp, st)} d ≠ ∅ :=
      evalFrom_empty_stack_nonempty_any_stack parser qp d st hacc0
    simpa [List.dropLast_append_getLast hd_ne] using hparse
  · have hd_ne : d ≠ [] := by
      intro hd
      subst hd
      simp [InverseTokenSpannerTable] at hitst
    have hitst' := hitst
    simp only [InverseTokenSpannerTable, dif_pos hd_ne, Set.mem_setOf_eq] at hitst'
    obtain ⟨q₁, hstep, hsingle⟩ := hitst'
    refine ⟨q_fst, terms, qp, st, q₁, d.dropLast, d.getLast hd_ne,
      hcomb, hcfg, hstep, hsingle, ?_⟩
    simpa [List.dropLast_append_getLast hd_ne] using hcur

private lemma GCDChecker_nil_checkerAccepts_extension
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite) :
  ∃ w' : List β, checkerAccepts (GCDChecker spec P) w' ∧ ([] : List β).isPrefixOf w' := by
  let comb := Detokenizing.BuildDetokLexer (V := Ch β) spec
  let parser := ParserWithEOS P
  obtain ⟨hlexer, hignoreP⟩ := hassum.whitespace
  let whiteTerm :=
    Detokenizing.whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hlexer
  let whiteCh : Ch Γ := ExtChar.char whiteTerm
  have hignoreParser : ParserIgnoresTerminal parser whiteCh :=
    ParserWithEOS_ignoresTerminal P whiteTerm hignoreP
  have hparserPruned : parser.pruned := ParserWithEOS_pruned P hassum.parser_pruned
  have hstart_ne : parser.evalFull [] ≠ ∅ := by
    simp [parser, PDA.evalFull]
  obtain ⟨cont, haccFull⟩ :=
    PDA.exists_accepts_extension_of_pruned_evalFull_nonempty
      parser hparserPruned [] hstart_ne
  let target : List (Ch Γ) := cont.filter (fun t => t != whiteCh)
  have haccTarget : target ∈ parser.accepts := by
    simpa [target] using
      (ParserIgnoresTerminal.accepts_append_filter_ne
        parser whiteCh hignoreParser [] cont haccFull)
  have htarget_no_white : ¬ target.contains whiteCh := by
    simp [target]
  have hwhite_single :
      (ExtChar.char whiteTerm : Ch Γ) ∈
        comb.singleProducible ((), LexingState.start (σ := σa)) := by
    simpa [comb, whiteCh] using
      BuildDetokLexer_whitespace_singleProducible_start
        (β := β) spec hlexer
  have hmod_eq :=
    Detokenizing.moddedRealizableSequences_eq_not_contains_whitespace
      (vocab := (inferInstance : Vocabulary (Ch α) (Ch β)))
      spec hassum.hempty hassum.lexer_pruned hlexer
      (LexingState.start (σ := σa)) hwhite_single
  have hmod_mem :
      target ∈ comb.moddedRealizableSequences
        ((), LexingState.start (σ := σa)) whiteTerm := by
    rw [← hmod_eq]
    simpa [comb, whiteCh, whiteTerm] using htarget_no_white
  simp only [FST.moddedRealizableSequences] at hmod_mem
  obtain ⟨outReal, houtReal_rs, hfilterOut⟩ := hmod_mem
  change ∃ q' inp,
    comb.evalFrom ((), LexingState.start (σ := σa)) inp =
      some (q', outReal) at houtReal_rs
  obtain ⟨qtail, inp, hlexTail⟩ := houtReal_rs
  have haccOut : outReal ∈ parser.accepts := by
    simpa using
      (ParserIgnoresTerminal.accepts_append_of_filter_ne
        parser whiteCh hignoreParser [] outReal target hfilterOut haccTarget)
  have heos_target : ExtChar.eos ∈ target :=
    ParserWithEOS_accepts_has_eos P target haccTarget
  have heos_out : ExtChar.eos ∈ outReal := by
    rw [← hfilterOut] at heos_target
    simpa [whiteCh] using heos_target
  have heos_inp : ExtChar.eos ∈ inp := by
    by_contra hno
    obtain ⟨inpChars, hinp⟩ := List.exists_map_char_of_not_mem_eos hno
    subst hinp
    have hout_no_eos :=
      BuildDetokLexer_char_evalFrom_no_eos spec
        ((), LexingState.start (σ := σa)) inpChars qtail outReal hlexTail
    exact hout_no_eos heos_out
  obtain ⟨tailTokens, suffixAfter, hinp_decomp⟩ :=
    List.exists_map_char_append_eos_of_mem_eos heos_inp
  have hfull_eval : comb.eval inp = some (qtail, outReal) := by
    simpa [comb, FST.eval] using hlexTail
  refine ⟨tailTokens, ?_, ?_⟩
  · apply GCDChecker_checkerAccepts_of_allowed_accepted_suffix
      spec P hassum [] tailTokens suffixAfter
    · simp
    · refine ⟨qtail, outReal, ?_, haccOut⟩
      simpa [comb, hinp_decomp] using hfull_eval
  · simp

private lemma GCDChecker_snoc_checkerAccepts_extension
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite)
  (pref : List β) (last : β)
  (hw : checkerAllows (GCDChecker spec P) (pref ++ [last]) = true) :
  ∃ w' : List β, checkerAccepts (GCDChecker spec P) w' ∧
    (pref ++ [last]).isPrefixOf w' := by
  have hlast : GCDChecker spec P pref (ExtChar.char last) = true := by
    exact (checkerAllows_snoc_iff (GCDChecker spec P) pref last).1
      (by simpa [List.concat_eq_append] using hw) |>.2
  obtain ⟨q_fst, terms, qp, st, q₁, S, head,
      hcomb, hcfg, hstep, hsingle, hparse⟩ :=
    GCDChecker_char_true_head_witness spec P pref last hlast
  let comb := Detokenizing.BuildDetokLexer (V := Ch β) spec
  let parser := ParserWithEOS P
  obtain ⟨hlexer, hignoreP⟩ := hassum.whitespace
  let whiteTerm :=
    Detokenizing.whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hlexer
  let whiteCh : Ch Γ := ExtChar.char whiteTerm
  have hignoreParser : ParserIgnoresTerminal parser whiteCh := by
    exact ParserWithEOS_ignoresTerminal P whiteTerm hignoreP
  have hparserPruned : parser.pruned := ParserWithEOS_pruned P hassum.parser_pruned
  have hprefix_ne : parser.evalFull (terms ++ (S ++ [head])) ≠ ∅ := by
    rw [parser.evalFull_append terms (S ++ [head])]
    rcases Finset.nonempty_iff_ne_empty.mpr hparse with ⟨cfg, hcfg_tail⟩
    have hsingle_cfg : ({(qp, st)} : Finset (Ch σp × List π)) ⊆ parser.evalFull terms := by
      intro x hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      simpa [parser, PDA.evalFull] using hcfg
    have hcfg' :
        cfg ∈ parser.evalFrom (parser.evalFull terms) (S ++ [head]) :=
      (parser.evalFrom_subset {(qp, st)} (parser.evalFull terms) hsingle_cfg
        (S ++ [head])) hcfg_tail
    exact Finset.nonempty_iff_ne_empty.mp ⟨cfg, hcfg'⟩
  obtain ⟨cont, haccFull⟩ :=
    PDA.exists_accepts_extension_of_pruned_evalFull_nonempty
      parser hparserPruned (terms ++ (S ++ [head])) hprefix_ne
  let tailRaw : List (Ch Γ) := head :: cont
  let tailFiltered : List (Ch Γ) := tailRaw.filter (fun t => t != whiteCh)
  have haccRaw : terms ++ S ++ tailRaw ∈ parser.accepts := by
    simpa [tailRaw, List.append_assoc] using haccFull
  have haccFiltered : terms ++ S ++ tailFiltered ∈ parser.accepts := by
    simpa [tailFiltered, List.append_assoc] using
      (ParserIgnoresTerminal.accepts_append_filter_ne
        parser whiteCh hignoreParser (terms ++ S) tailRaw haccRaw)
  rcases q₁ with ⟨unitState, qlex⟩
  cases unitState
  have htarget_no_white : ¬ tailFiltered.contains whiteCh := by
    simp [tailFiltered]
  have hrealized :
      ∃ inp qtail outReal,
        comb.evalFrom ((), qlex) inp = some (qtail, outReal) ∧
        outReal.filter (fun t => t != whiteCh) = tailFiltered := by
    by_cases hhead_white : head = whiteCh
    · have hwhite_single :
          (ExtChar.char whiteTerm : Ch Γ) ∈ comb.singleProducible ((), qlex) := by
        simpa [whiteCh, hhead_white, comb] using hsingle
      have hmod_eq :=
        Detokenizing.moddedRealizableSequences_eq_not_contains_whitespace
          (vocab := (inferInstance : Vocabulary (Ch α) (Ch β)))
          spec hassum.hempty hassum.lexer_pruned hlexer qlex hwhite_single
      have hmod_mem :
          tailFiltered ∈ comb.moddedRealizableSequences ((), qlex) whiteTerm := by
        rw [← hmod_eq]
        simpa [whiteCh, whiteTerm, comb] using htarget_no_white
      simp only [FST.moddedRealizableSequences] at hmod_mem
      obtain ⟨outReal, houtReal_rs, hfilter⟩ := hmod_mem
      change ∃ q' inp, comb.evalFrom ((), qlex) inp = some (q', outReal) at houtReal_rs
      obtain ⟨qtail, inp, hlexTail⟩ := houtReal_rs
      exact ⟨inp, qtail, outReal, hlexTail, by simpa [whiteCh] using hfilter⟩
    · have htarget_eq :
          tailFiltered = head :: cont.filter (fun t => t != whiteCh) := by
        simp [tailFiltered, tailRaw, hhead_white]
      have htail_eq :=
        Detokenizing.tailModdedRealizableSequences_eq_singleProducibleHead
          (vocab := (inferInstance : Vocabulary (Ch α) (Ch β)))
          spec hassum.hempty hassum.lexer_pruned hlexer qlex
      have htail_mem :
          tailFiltered ∈ comb.tailModdedRealizableSequences ((), qlex) whiteTerm := by
        rw [htail_eq]
        right
        refine ⟨head, cont.filter (fun t => t != whiteCh), ?_, htarget_eq, ?_⟩
        · exact htarget_no_white
        · simpa [comb] using hsingle
      simp only [FST.tailModdedRealizableSequences] at htail_mem
      obtain ⟨outReal, houtReal_rs, _hnotStartWhite, hfilter⟩ := htail_mem
      change ∃ q' inp, comb.evalFrom ((), qlex) inp = some (q', outReal) at houtReal_rs
      obtain ⟨qtail, inp, hlexTail⟩ := houtReal_rs
      exact ⟨inp, qtail, outReal, hlexTail, by simpa [whiteCh] using hfilter⟩
  obtain ⟨inp, qtail, outReal, hlexTail, hfilterOut⟩ := hrealized
  have haccOut : terms ++ S ++ outReal ∈ parser.accepts := by
    simpa [List.append_assoc] using
      (ParserIgnoresTerminal.accepts_append_of_filter_ne
        parser whiteCh hignoreParser (terms ++ S) outReal tailFiltered
        hfilterOut haccFiltered)
  have hterms_no_eos : ExtChar.eos ∉ terms := by
    have hcombFrom : comb.evalFrom comb.start (pref.map ExtChar.char) =
        some (q_fst, terms) := by
      simpa [comb, FST.eval] using hcomb
    exact BuildDetokLexer_char_evalFrom_no_eos spec comb.start pref q_fst terms hcombFrom
  have hS_no_eos : ExtChar.eos ∉ S := by
    simpa [comb] using BuildDetokLexer_char_step_no_eos spec q_fst last ((), qlex) S hstep
  have heos_target : ExtChar.eos ∈ tailFiltered := by
    have heos_full := ParserWithEOS_accepts_has_eos P (terms ++ S ++ tailFiltered) haccFiltered
    rw [show terms ++ S ++ tailFiltered = (terms ++ S) ++ tailFiltered by
      simp [List.append_assoc]] at heos_full
    rw [List.mem_append] at heos_full
    rcases heos_full with htermsS | htail
    · rw [List.mem_append] at htermsS
      rcases htermsS with hterms | hS
      · exact (hterms_no_eos hterms).elim
      · exact (hS_no_eos hS).elim
    · exact htail
  have heos_out : ExtChar.eos ∈ outReal := by
    rw [← hfilterOut] at heos_target
    simpa [whiteCh] using heos_target
  have heos_inp : ExtChar.eos ∈ inp := by
    by_contra hno
    obtain ⟨inpChars, hinp⟩ := List.exists_map_char_of_not_mem_eos hno
    subst hinp
    have hout_no_eos :=
      BuildDetokLexer_char_evalFrom_no_eos spec ((), qlex) inpChars qtail outReal hlexTail
    exact hout_no_eos heos_out
  obtain ⟨tailTokens, suffixAfter, hinp_decomp⟩ :=
    List.exists_map_char_append_eos_of_mem_eos heos_inp
  have hfull_eval :
      comb.eval (((pref ++ [last]).map ExtChar.char) ++ inp) =
        some (qtail, terms ++ S ++ outReal) := by
    simp only [FST.eval]
    have hcombFrom : comb.evalFrom comb.start (pref.map ExtChar.char) =
        some (q_fst, terms) := by
      simpa [comb, FST.eval] using hcomb
    have hrest :
        comb.evalFrom q_fst (ExtChar.char last :: inp) =
          some (qtail, S ++ outReal) := by
      rw [FST.evalFrom_cons_some_iff]
      exact ⟨((), qlex), S, outReal, hstep, hlexTail, rfl⟩
    calc
      comb.evalFrom comb.start (((pref ++ [last]).map ExtChar.char) ++ inp)
          = comb.evalFrom comb.start
              (pref.map ExtChar.char ++ (ExtChar.char last :: inp)) := by
            simp [List.map_append, List.append_assoc]
      _ = some (qtail, terms ++ (S ++ outReal)) := by
            have happ := FST.evalFrom_append (M := comb) comb.start
              (pref.map ExtChar.char) (ExtChar.char last :: inp)
            rw [hcombFrom] at happ
            rw [happ]
            simp [hrest]
      _ = some (qtail, terms ++ S ++ outReal) := by
            simp [List.append_assoc]
  let acceptedWord := (pref ++ [last]) ++ tailTokens
  refine ⟨acceptedWord, ?_, ?_⟩
  · apply GCDChecker_checkerAccepts_of_allowed_accepted_suffix
      spec P hassum (pref ++ [last]) tailTokens suffixAfter
    · simpa [List.concat_eq_append] using hw
    · refine ⟨qtail, terms ++ S ++ outReal, ?_, haccOut⟩
      simpa [comb, hinp_decomp, List.append_assoc] using hfull_eval
  · simp [acceptedWord]

/-- Hard productivity step: the mask witnesses for an incrementally accepted
prefix can be completed to a checker-accepted word under the full GCD
assumptions.

This theorem must use the `checkerAllows` evidence rather than merely a
`GCDViablePrefix`: the latter forgets which single-producible lexer head the
mask proved parseable. -/
theorem GCDChecker_checkerAllows_imp_checkerAccepts_extension
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite)
  (w : List β)
  (hw : checkerAllows (GCDChecker spec P) w = true) :
  ∃ w' : List β, checkerAccepts (GCDChecker spec P) w' ∧ w.isPrefixOf w' := by
  cases List.eq_nil_or_concat w with
  | inl hnil =>
      subst hnil
      exact GCDChecker_nil_checkerAccepts_extension spec P hassum
  | inr hsnoc =>
      obtain ⟨pref, last, hsnoc⟩ := hsnoc
      subst hsnoc
      simpa [List.concat_eq_append] using
        GCDChecker_snoc_checkerAccepts_extension spec P hassum pref last
          (by simpa [List.concat_eq_append] using hw)

/-- Under the full whitespace assumption, every incrementally accepted prefix
can be extended to a complete checker-accepted word. -/
theorem GCDChecker_productive
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite) :
  checkerProductive (β := β) (GCDChecker spec P) := by
  intro w hw
  exact GCDChecker_checkerAllows_imp_checkerAccepts_extension spec P hassum w hw

/-- The GCD checker's intermediate language is the prefix closure of
`GCDLanguage`, assuming the full whitespace assumption. -/
theorem GCDChecker_intermediateLanguage_eq_GCDLanguage_prefixes
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite) :
  checkerIntermediateLanguage (β := β) (GCDChecker spec P) =
    (GCDLanguage (β := β) spec P).prefixes := by
  have hproductive : checkerProductive (β := β) (GCDChecker spec P) :=
    GCDChecker_productive spec P hassum
  ext w
  simp only [checkerIntermediateLanguage, Language.prefixes]
  constructor
  · -- (→): checkerAllows c w → ∃ v ∈ GCDLanguage, w <+: v
    intro hw
    -- Use hproductive to get w' with checkerAccepts c w' and w.isPrefixOf w'
    obtain ⟨w', haccepts, hprefix⟩ := hproductive w hw
    -- Convert isPrefixOf to <+:
    have hprefix' : w <+: w' := List.isPrefixOf_iff_prefix.mp hprefix
    -- Use checkerLanguage = GCDLanguage: w' ∈ checkerLanguage c → w' ∈ GCDLanguage
    have hw'_lang : w' ∈ GCDLanguage spec P := by
      have heq : checkerLanguage (β := β) (GCDChecker spec P) = GCDLanguage spec P :=
        GCDChecker_checkerLanguage_eq_GCDLanguage spec P hassum
      rw [← heq]
      simp only [checkerLanguage]
      exact haccepts
    exact ⟨w', hw'_lang, hprefix'⟩
  · -- (←): ∃ v ∈ GCDLanguage, w <+: v → checkerAllows c w
    intro ⟨v, hv_lang, hprefix⟩
    -- Write v = w ++ rest for some rest
    obtain ⟨rest, hrest⟩ := hprefix
    exact GCDLanguage_checkerAllows_prefix spec P hassum v hv_lang w rest hrest.symm

/-- The GCD checker's cumulative `checkerAllows` predicate is invariant under
retokenizing a prefix with the same flattened character content under the full
whitespace assumption. -/
theorem GCDChecker_pathIndependent
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite) :
  checkerPathIndependent (α := α) (β := β)
    (GCDChecker spec P) (Vocabulary.flatten (α := α)) := by
  intro w₁ w₂ hfm
  have hintermediate :
      checkerIntermediateLanguage (β := β) (GCDChecker spec P) =
        (GCDLanguage (β := β) spec P).prefixes :=
    GCDChecker_intermediateLanguage_eq_GCDLanguage_prefixes spec P hassum
  have hw₁ :
      checkerAllows (GCDChecker spec P) w₁ = true ↔
        w₁ ∈ (GCDLanguage (β := β) spec P).prefixes := by
    have hmem := congrArg (fun l : Language β => w₁ ∈ l) hintermediate
    simpa [checkerIntermediateLanguage] using hmem
  have hw₂ :
      checkerAllows (GCDChecker spec P) w₂ = true ↔
        w₂ ∈ (GCDLanguage (β := β) spec P).prefixes := by
    have hmem := congrArg (fun l : Language β => w₂ ∈ l) hintermediate
    simpa [checkerIntermediateLanguage] using hmem
  have hprefix :
      w₁ ∈ (GCDLanguage (β := β) spec P).prefixes ↔
        w₂ ∈ (GCDLanguage (β := β) spec P).prefixes :=
    GCDLanguage_prefixes_iff_of_flatMap_eq spec P w₁ w₂ hfm
  have hiff :
      checkerAllows (GCDChecker spec P) w₁ = true ↔
        checkerAllows (GCDChecker spec P) w₂ = true :=
    hw₁.trans (hprefix.trans hw₂.symm)
  by_cases h₁ : checkerAllows (GCDChecker spec P) w₁ = true
  · have h₂ : checkerAllows (GCDChecker spec P) w₂ = true := hiff.mp h₁
    rw [h₁, h₂]
  · have h₁false : checkerAllows (GCDChecker spec P) w₁ = false :=
      Bool.eq_false_of_not_eq_true h₁
    have h₂false : checkerAllows (GCDChecker spec P) w₂ = false := by
      apply Bool.eq_false_of_not_eq_true
      intro h₂
      exact h₁ (hiff.mpr h₂)
    rw [h₁false, h₂false]

/-- The GCD mask checker, viewed as an abstract `Checker`, is complete with
respect to the language defined by the composed detokenizing lexer and parser:
it accepts exactly the strings in that language, and its intermediate language
is the prefix closure.

The `checkerLanguage` direction is fully proved (both directions).
The `checkerIntermediateLanguage` direction uses productivity as derived from
the full whitespace assumption. -/
theorem GCDChecker_correct
  [Vocabulary α β] [FinEnum β]
  (spec : LexerSpec α Γ σa) (P : PDA Γ π σp)
  {tnonwhite twhite : α} {qnonwhite qwhite : σa}
  (hassum : GCDAssumptions spec P tnonwhite twhite qnonwhite qwhite) :
  checkerCorrect (β := β) (GCDChecker spec P) (GCDLanguage spec P) := by
  constructor
  · exact GCDChecker_checkerLanguage_eq_GCDLanguage spec P hassum
  · exact GCDChecker_intermediateLanguage_eq_GCDLanguage_prefixes
      spec P hassum
