import ConstrainedDecodingFormalization.Lexing.Base

/-!
# Lexing FST correctness

This module proves that the executable partial lexer, the relational lexer,
and the generated lexing FST agree.
-/

open List

universe u v w

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ]
  [BEq α] [BEq σ] [LawfulBEq σ]

omit [DecidableEq α] [DecidableEq σ] [BEq α] [BEq σ] [LawfulBEq σ] in
/-- Under pruning, the seeded executable lexer and the relational semantics are
equivalent in both directions. This is the technical core behind the later
equivalence theorems. -/
private lemma PartialLexRel_append_singleton_tail (spec: LexerSpec α Γ σ)
    {tail wp : List (Ch α)} {c : Ch α}
    {tokens : List (Ch Γ)} {unlexed : List α}
    (h : PartialLexRel spec ((wp ++ [c]) ++ tail) tokens unlexed) :
    PartialLexRel spec (wp ++ c :: tail) tokens unlexed := by
  simpa using h

omit [DecidableEq α] [DecidableEq σ] [BEq α] in
lemma PartialLex_pruned_eq_PartialLexRel_seed (spec: LexerSpec α Γ σ) (hp: spec.automaton.pruned) :
  (∀ w tokens unlexed, (PartialLexRel spec w tokens unlexed) →
    PartialLex_seed spec (some ([], [])) w = some (tokens, unlexed)) ∧
  (∀ wp ws seed_f seed_s tokens unlexed,
    (PartialLexRel spec wp seed_f seed_s) ∧
      PartialLex_seed spec (some (seed_f, seed_s)) ws = some (tokens, unlexed) →
    PartialLexRel spec (wp ++ ws) tokens unlexed) := by
  have hprune := spec.automaton.pruned_prefixLanguage hp
  have left : (∀ w tokens unlexed, (PartialLexRel spec w tokens unlexed) → PartialLex_seed spec (some ([], [])) w = some (tokens, unlexed)) := by
    intro w tokens unlexed h
    induction h
    case nil =>
      simp[PartialLex_seed]
    case step_nil_eos w wn tokens ih wwn h hacc =>
      simp[PartialLex_seed] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      exact h
    case step_eos w wn tokens unlexed ih wwn h hacc =>
      simp[PartialLex_seed] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      simp[h]
    case step_char_continue w wn tokens unlexed ch ih wwn h hacc =>
      simp[PartialLex_seed] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      cases he: spec.automaton.eval (unlexed ++ [ch]) with
      | none =>
        have : unlexed ++ [ch] ∉ spec.automaton.prefixLanguage := by
          exact Eq.mpr_not (congrFun (id (Eq.symm hprune)) (unlexed ++ [ch])) fun a => a he
        contradiction
      | some σ' =>
        simp at he
        simp[he]
    case step_char_commit w wn tokens unlexed ch ih wwn hni hc_pfx ht hacc =>
      simp[PartialLex_seed] at hacc ⊢
      simp[wwn, hacc, PartialLex_trans]
      cases he: spec.automaton.eval (unlexed ++ [ch]) with
      | none =>
        simp[FSA.eval] at he
        simp[he]
        simp[FSA.accepts, FSA.acceptsFrom] at ht
        split
        <;> simp_all
        rcases ht with ⟨t, ht, ht1⟩
        subst wwn
        simp_all only [reduceCtorEq]
        have ⟨e, he'⟩ := ht
        rename_i σ' _ heq
        simp[he'] at heq
        constructor
        · rw[←hprune] at hc_pfx
          simp[FSA.intermediateLanguage] at hc_pfx
          change spec.automaton.evalFrom spec.automaton.start [ch] ≠ none at hc_pfx
          cases hch : spec.automaton.evalFrom spec.automaton.start [ch] with
          | none =>
              contradiction
          | some qch =>
              simp
        · refine ⟨heq ▸ he'.2, ?_⟩
          subst heq
          have his : (spec.term e).isSome := (spec.hterm e).mp he'.2
          rcases Option.isSome_iff_exists.mp his with ⟨t, hterm⟩
          have hs :
              (spec.automaton.eval unlexed).get
                (by simp [FSA.eval, he'.1]) = e := by
            simp [FSA.eval, he'.1]
          unfold LexerSpec.accept_seq_term
          simp [FSA.eval, he'.1, hterm]
      | some σ' =>
        have : spec.automaton.evalFrom spec.automaton.start (unlexed ++ [ch]) = none := by
          simp[←hprune] at hni
          simp[FSA.intermediateLanguage] at hni
          have : ¬¬ spec.automaton.evalFrom spec.automaton.start (unlexed ++ [ch]) = none := by
            exact hni
          exact not_not.mp this
        simp[this] at he

  constructor
  . exact left
  . intro wp ws seed_f seed_s tokens unlexed h
    induction ws generalizing wp seed_f seed_s
    case nil =>
      simp[PartialLex_seed] at h
      cases h.left
      <;> simp_all
      case step_nil_eos =>
        have ⟨hl, htokens, _⟩ := h
        simp[←htokens]
        exact hl
      case step_eos =>
        have ⟨hl, htokens, _⟩ := h
        simp[←htokens]
        exact hl
      case step_char_continue =>
        have ⟨hl, htokens, hunlexed⟩ := h
        simp[←htokens, ←hunlexed]
        exact hl
      case step_char_commit =>
        have ⟨hl, htokens, hunlexed⟩ := h
        simp[←htokens, ←hunlexed]
        exact hl
    case cons ch tail ih =>
      have my_inductive_seed := h.left
      have computable_eq_some := left wp seed_f seed_s my_inductive_seed
      have h_token_unlexed := h.right

      simp[PartialLex_seed] at h_token_unlexed
      cases hns : (PartialLex_trans spec (some (seed_f, seed_s)) ch) with
      | none =>
        rw[hns] at h_token_unlexed
        have : foldl (PartialLex_trans spec) none tail = none := by
          exact PartialLex_trans_foldl_nil spec tail
        rw[this] at h_token_unlexed
        contradiction
      | some qp =>
        rw[hns] at h_token_unlexed
        let ⟨step_tokens, step_unlexed⟩ := qp

        match ch with
        | ExtChar.eos =>
          simp[PartialLex_trans] at hns
          by_cases haccept : seed_s ∈ spec.automaton.accepts
          . let new_tokens := seed_f ++ [.char (spec.accept_seq_term seed_s haccept), .eos]
            have step := PartialLexRel.step_eos my_inductive_seed rfl haccept
            have htail : PartialLex_seed spec (some (new_tokens, [])) tail = some (tokens, unlexed) := by
              simp[PartialLex_seed]
              simp[haccept] at hns
              have := h_token_unlexed
              simp[←hns.left, ←hns.right, new_tokens] at h_token_unlexed ⊢
              exact h_token_unlexed
            exact PartialLexRel_append_singleton_tail spec (ih (wp ++ [ExtChar.eos]) new_tokens [] ⟨step, htail⟩)
          . simp[haccept] at hns
            let new_tokens := seed_f ++ [.eos]
            simp[hns.left] at my_inductive_seed
            simp[hns] at haccept
            have step := PartialLexRel.step_nil_eos my_inductive_seed rfl haccept
            have htail : PartialLex_seed spec (some (new_tokens, [])) tail = some (tokens, unlexed) := by
              simp[PartialLex_seed]
              have := h_token_unlexed
              simp[←hns.right, new_tokens] at h_token_unlexed ⊢
              exact h_token_unlexed
            exact PartialLexRel_append_singleton_tail spec (ih (wp ++ [ExtChar.eos]) new_tokens [] ⟨step, htail⟩)
        | ExtChar.char ch =>
          simp[PartialLex_trans] at hns
          cases hp : spec.automaton.evalFrom spec.automaton.start (seed_s ++ [ch]) with
          | some σ' =>
            simp[hp] at hns
            let new_tokens := seed_f
            let new_unlexed := seed_s ++ [ch]

            have hint : (seed_s ++ [ch] ∈ spec.automaton.intermediateLanguage) := by
              change spec.automaton.evalFrom spec.automaton.start (seed_s ++ [ch]) ≠ none
              simp [hp]
            have hpfx : (seed_s ++ [ch] ∈ spec.automaton.prefixLanguage) := by
              rw[←hprune]
              exact hint
            have hstep_rel : PartialLexRel spec (wp ++ [ExtChar.char ch]) new_tokens new_unlexed :=
              PartialLexRel.step_char_continue my_inductive_seed rfl hpfx
            have htail : PartialLex_seed spec (some (new_tokens, new_unlexed)) tail = some (tokens, unlexed) := by
              simp[PartialLex_seed]
              simp[new_tokens, new_unlexed, hns]
              exact h_token_unlexed
            exact PartialLexRel_append_singleton_tail spec (ih (wp ++ [ExtChar.char ch]) new_tokens new_unlexed ⟨hstep_rel, htail⟩)
          | none =>
            cases ha : spec.automaton.evalFrom spec.automaton.start seed_s with
            | none => simp[hp, ha] at hns
            | some σ =>
              simp_all
              cases hbo : spec.automaton.eval [ch]
              . simp at hbo
                simp[hbo] at hns
              . have hint : (seed_s ++ [ch] ∉ spec.automaton.intermediateLanguage) := by
                  change ¬ spec.automaton.evalFrom spec.automaton.start (seed_s ++ [ch]) ≠ none
                  simp[←hns.right.right] at hp
                  simp [hp]
                have hpfx : (seed_s ++ [ch] ∉ spec.automaton.prefixLanguage) := by
                  rw[←hprune]
                  exact hint

                have haccept : (seed_s ∈ spec.automaton.accepts) := by
                  have ⟨⟨h, _⟩, ht⟩ := hns.right
                  change ∃ f, spec.automaton.evalFrom spec.automaton.start seed_s = some f ∧ f ∈ spec.automaton.accept
                  exact ⟨σ, ha, h⟩

                -- very round about away but works
                let term := spec.term σ
                have ⟨t, ht⟩ : ∃ t, term = some t := by
                  have ⟨⟨h, _⟩, ht⟩ := hns.right
                  have h2 := (spec.hterm σ).mp h
                  match hc: term with
                  | none =>
                    simp[term] at hc
                    simp[hc] at h2
                  | some t => exists t

                let tused := spec.accept_seq_term seed_s haccept
                have htused : t = tused := by
                  simp[term] at ht
                  simp[tused, LexerSpec.accept_seq_term]
                  conv =>
                    rhs
                    pattern spec.automaton.evalFrom spec.automaton.start seed_s
                    rw[ha]
                  simp[ht]
                let new_tokens := seed_f ++ [ExtChar.char tused]
                let new_unlexed := [ch]

                have hstep_rel : PartialLexRel spec (wp ++ [ExtChar.char ch]) new_tokens new_unlexed := by
                  have ⟨⟨_, hseed⟩, ht'⟩ := hns.right
                  apply PartialLexRel.step_char_commit h.left
                  simp
                  exact hpfx
                  simp[hns]
                  simp_all
                  simp[term] at ht
                  simp[ht] at hseed
                  rw[←hprune]
                  change spec.automaton.evalFrom spec.automaton.start step_unlexed ≠ none
                  rw[hbo]
                  simp
                have htail : PartialLex_seed spec (some (new_tokens, new_unlexed)) tail = some (tokens, unlexed) := by
                  have ⟨⟨_, hseed⟩, ht'⟩ := hns.right
                  simp[new_tokens, new_unlexed, ←ht', ←hseed, ←htused, ht, term] at h_token_unlexed ⊢
                  exact h_token_unlexed
                exact PartialLexRel_append_singleton_tail spec (ih (wp ++ [ExtChar.char ch]) new_tokens new_unlexed hstep_rel htail)

/-! ### Equivalence of relational and executable lexing -/

omit [DecidableEq α] [DecidableEq σ] [BEq α] in
/-- Pruning lets us identify `PartialLex` with the relational lexer semantics. -/
theorem PartialLex_pruned_eq_PartialLexRel (spec: LexerSpec α Γ σ) (hp: spec.automaton.pruned) :
  ∀ w tokens unlexed, (PartialLexRel spec w tokens unlexed) ↔
    PartialLex spec w = some (tokens, unlexed) := by
  intro w tokens unlexed
  apply Iff.intro
  . exact (PartialLex_pruned_eq_PartialLexRel_seed spec hp).left w tokens unlexed
  . intro h
    have : PartialLexRel spec ([] ++ w) tokens unlexed := by
      apply (PartialLex_pruned_eq_PartialLexRel_seed spec hp).right [] w
      exact ⟨PartialLexRel.nil, by simp[PartialLex] at h; exact h⟩
    simp at this
    exact this

/-! ### Lexing FST correctness -/

/-- A character-level FSA run lifts to a lexing-FST run that produces no
output tokens. -/
private def FSA_ch_to_LexingFST (spec: LexerSpec α Γ σ) :
  ∀ (w : List α) q q', (q ≠ LexingState.start ∨ w ≠ []) →
    (spec.automaton.evalFrom (q.src spec) w = some q' ↔
      (BuildLexingFST spec).evalFrom q w = some (LexingState.id q', [])) := by
  intro w q q' h
  induction w generalizing q q'
  case nil =>
    simp[LexingState.src]
    simp at h
    split
    case h_1 x s => simp
    case h_2 s => simp at h
  case cons hd tl ih =>
    simp[FSA.evalFrom]
    simp at h
    cases hstep : spec.automaton.step (LexingState.src spec q) hd
    . simp[FST.evalFrom]
      nth_rewrite 1 [BuildLexingFST, Id.run]
      simp[hstep]
      by_cases haccept: LexingState.src spec q ∈ spec.automaton.accept
      simp_all
      split <;> simp_all
      split <;> simp_all
      intro _ h
      rename_i heq _ _ _ _ _
      have ⟨e, hw⟩ := heq
      simp[←hw.right] at h
      simp[haccept]
    . rename_i astep
      have : (spec.automaton.step (LexingState.src spec q) hd).isSome := by
        simp[hstep]
      simp[FST.evalFrom]
      conv =>
        pattern (BuildLexingFST spec).step q
        unfold BuildLexingFST
      simp[Id.run, this]
      simp[hstep]
      have ih := ih (LexingState.id astep) q' (by simp)
      simp[LexingState.src] at ih
      convert ih
      split <;> simp_all

omit [DecidableEq α] [DecidableEq σ] [BEq α] in
private lemma PartialLex_append_singleton_of_trans (spec: LexerSpec α Γ σ)
    {w : List (Ch α)} {head : Ch α}
    {seed_ts ts : List (Ch Γ)} {seed_wr wr : List α}
    (hw : PartialLex spec w = some (seed_ts, seed_wr))
    (hstep : PartialLex_trans spec (some (seed_ts, seed_wr)) head = some (ts, wr)) :
    PartialLex spec (w ++ [head]) = some (ts, wr) := by
  simp [PartialLex, PartialLex_seed] at hw ⊢
  rw [hw]
  simpa using hstep

omit [DecidableEq α] [DecidableEq σ] [BEq α] [BEq σ] [LawfulBEq σ] in
private lemma FST_eval_append_singleton_of_evalFrom_fold_step (M : FST α Γ σ)
    {w : List α} {head : α} {q q' : σ} {ts ts' : List Γ}
    (hw : M.eval w = some (q, ts))
    (hstep : M.evalFrom_fold_step (some (q, ts)) head = some (q', ts')) :
    M.eval (w ++ [head]) = some (q', ts') := by
  simp [FST.eval] at hw ⊢
  rw [←FST.evalFrom_fold_eq_evalFrom] at hw ⊢
  simp [FST.evalFrom_fold, FST.evalFrom_fold_seed] at hw ⊢
  rw [hw]
  simpa using hstep

private def PartialLex_to_LexingFST_evalFold (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) :
  ∀ wp ws q' seed_ts seed_wr,
    PartialLex spec wp = some (seed_ts, seed_wr) →
    (BuildLexingFST spec).eval wp = some (q', seed_ts) →
    (BuildLexingFST spec).eval seed_wr = some (q', []) →
    (seed_wr = [] ↔ q' = LexingState.start) →
    match PartialLex_seed spec (some (seed_ts, seed_wr)) ws with
    | some (ts, wr) =>
      ∃ q'',
        (BuildLexingFST spec).evalFrom_fold_seed q' ws seed_ts = some (q'', ts) ∧
        (BuildLexingFST spec).evalFrom_fold_seed (BuildLexingFST spec).start wr [] = some (q'', [])
    | none => (BuildLexingFST spec).evalFrom_fold_seed q' ws seed_ts = none := by
  intro wp ws q' seed_ts seed_wr
  let fst := BuildLexingFST spec
  let new_q0 := fst.start
  let old_q0 := spec.automaton.start

  have hlex_nil : fst.eval [] = some (new_q0, []) := by
    simp [fst, new_q0, BuildLexingFST, Id.run, FST.eval, FST.evalFrom]

  have h_q0_na : old_q0 ∉ spec.automaton.accept := by
    by_contra h'
    simp[FSA.accepts_iff] at he
    have : spec.automaton.evalFrom old_q0 [] = some old_q0 := by
      simp[FSA.evalFrom_nil]
    have w : ∃ f, spec.automaton.evalFrom spec.automaton.start [] = some f ∧ f ∈ spec.automaton.accept := by
      exists old_q0
    simp at w
    exact he w

  induction ws generalizing wp q' seed_ts seed_wr
  <;> (
    intro h₀ h₁ h₂ h₃
    have h₂_fsa : spec.automaton.evalFrom spec.automaton.start seed_wr = some (LexingState.src spec q') := by
      by_cases hempty : seed_wr = []
      . simp[hempty]
        have := h₃.mp hempty
        simp[LexingState.src, this]
      . have : q' ≠ LexingState.start := by
          exact (Iff.ne h₃).mp hempty
        have hbase := (FSA_ch_to_LexingFST spec (seed_wr) LexingState.start (q'.src spec) (Or.inr hempty)).mpr (by
          convert h₂
          cases q' <;> simp_all
        )
        simp[LexingState.src] at hbase ⊢
        cases q' <;> simp_all

    simp[FST.evalFrom_fold_seed]
    rw[←FST.eval_fold_eq_eval] at h₂
    simp[FST.eval_fold, FST.evalFrom_fold] at h₂
  )
  case nil =>
    exact h₂
  case cons head tail ih =>
    let pl_step := (PartialLex_trans spec (some (seed_ts, seed_wr)) head)
    have hplex_append :
        ∀ {ts wr}, PartialLex_trans spec (some (seed_ts, seed_wr)) head = some (ts, wr) →
          PartialLex spec (wp ++ [head]) = some (ts, wr) := by
      intro ts wr hstep
      exact PartialLex_append_singleton_of_trans spec h₀ hstep

    have hlex_append :
        ∀ {q'' ts''}, fst.evalFrom_fold_step (some (q', seed_ts)) head = some (q'', ts'') →
          fst.eval (wp ++ [head]) = some (q'', ts'') := by
      intro q'' ts'' hstep
      exact FST_eval_append_singleton_of_evalFrom_fold_step fst h₁ hstep

    cases hh : head
    case eos =>
      simp[PartialLex_trans]
      let afinal := spec.automaton.eval seed_wr
      by_cases haccept : seed_wr ∈ spec.automaton.accepts
      . simp[haccept]
        have ⟨aq', haq'⟩ := spec.automaton.accepts_iff.mp haccept
        have : spec.automaton.evalFrom (LexingState.src spec LexingState.start) seed_wr = some aq' := by
          simp[LexingState.src, haq']
        -- this shows that the state at the fst is "accepting" in the fsa
        have hfsa := (FSA_ch_to_LexingFST spec (seed_wr) LexingState.start aq'
          (by simp; by_contra ha; rw[ha] at haccept; contradiction)).mp this

        have hq'aq' : q' = LexingState.id aq' := by
          rw[FST.evalFrom_fold_seed_eq_evalFrom_seed] at h₂
          simp[FST.evalFrom_seed] at h₂
          simp at hfsa
          simp[hfsa] at h₂
          exact Eq.symm h₂

        -- find out the token that is produced
        let produced_token := spec.accept_seq_term seed_wr haccept
        -- have hseq_term : aq = spec_term
        have hlex_trans :
          (BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) head = some (LexingState.start, seed_ts ++ [ExtChar.char produced_token, ExtChar.eos]) := by
          simp at h₁ ⊢
          rw[←FST.evalFrom_fold_eq_evalFrom] at h₁
          simp[FST.evalFrom_fold_seed] at h₁ ⊢
          simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run, hh]
          simp[hq'aq', LexingState.src, haq']
          simp[produced_token]
          simp[LexerSpec.accept_seq_term]
          have : afinal = spec.automaton.evalFrom spec.automaton.start seed_wr := by simp[afinal]
          conv =>
            rhs
            pattern spec.automaton.evalFrom spec.automaton.start seed_wr
            rw[←this]
          simp[haq', this]

        have hlex_wp_step : fst.eval (wp ++ [head]) = some (LexingState.start, seed_ts ++ [.char produced_token, ExtChar.eos]) :=
          hlex_append hlex_trans

        have hplex_step : PartialLex spec (wp ++ [head]) = some (seed_ts ++ [.char produced_token, ExtChar.eos], []) :=
          hplex_append (by
            simp [PartialLex_trans, hh, produced_token, haccept])

        have ih := ih (wp ++ [head]) LexingState.start (seed_ts ++ [.char produced_token, ExtChar.eos]) [] hplex_step hlex_wp_step hlex_nil

        simp[hh] at hlex_trans
        rw[hlex_trans]
        simp[produced_token] at ih

        convert ih
      . simp[haccept]
        by_cases hempty : seed_wr = []
        . simp at hempty
          have hlex_trans :
            (BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) head = some (LexingState.start, seed_ts ++ [ExtChar.eos]) := by
            simp[FST.eval] at h₁ ⊢
            rw[←FST.evalFrom_fold_eq_evalFrom] at h₁
            simp[FST.evalFrom_fold, FST.evalFrom_fold_seed] at h₁ ⊢
            simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run, hh]
            -- what q' is when seed_wr = []
            have hq'_start : q' = LexingState.start := by
              rw[FST.evalFrom_fold_seed_eq_evalFrom_seed] at h₂
              simp[FST.evalFrom_seed, hempty] at h₂
              exact Eq.symm h₂
            simp[hq'_start, LexingState.src]
            simp[old_q0] at h_q0_na
            simp[h_q0_na]

          have hlex_wp_step : fst.eval (wp ++ [head]) = some (LexingState.start, seed_ts ++ [ExtChar.eos]) :=
            hlex_append hlex_trans

          have hplex_step : PartialLex spec (wp ++ [head]) = some (seed_ts ++ [ExtChar.eos], []) :=
            hplex_append (by
              simp [PartialLex_trans, hh, hempty]
              exact he)

          have ih := ih (wp ++ [head]) LexingState.start (seed_ts ++ [ExtChar.eos]) [] hplex_step hlex_wp_step hlex_nil

          simp[hh] at hlex_trans
          rw[hlex_trans]
          simp at ih
          convert ih
          simp[hempty]
        .  -- we have no transition and must show thats the case for both of them
          simp[hempty]
          -- since seed_wr ≠ [], q' is not start
          have hq'_not_start : q' ≠ LexingState.start := by
            exact (Iff.ne h₃).mp hempty
          -- and so, the corresponding fsa state is the fst state
          simp[LexingState.src] at h₂_fsa
          cases hq' : q'
          case neg.start => contradiction
          rename_i src
          -- in particular, its not accepting
          have hlex_step : ((BuildLexingFST spec).evalFrom_fold_step (some (LexingState.id src, seed_ts)) ExtChar.eos) = none := by
            simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run]
            simp[FSA.accepts_iff] at haccept ⊢
            simp[hq', h₂_fsa] at haccept
            simp[haccept]

          simp[hlex_step]
    case char ch =>
      cases hstep : spec.automaton.step (LexingState.src spec q') ch
      case none =>
        simp_all
        by_cases haccept : LexingState.src spec q' ∈ spec.automaton.accept
        case pos =>
          let qsrc := LexingState.src spec q'
          let term := spec.term qsrc
          let unwrapped := term.get ((spec.hterm qsrc).mp haccept)
          cases hch : spec.automaton.step spec.automaton.start ch
          case none =>
            -- no transition in both if ch is not in the prefix language
            have : PartialLex_trans spec (some (seed_ts, seed_wr)) (ExtChar.char ch) = none := by
              simp[PartialLex_trans]
              simp[FSA.evalFrom_append]
              simp[h₂_fsa, haccept]
              simp[FSA.evalFrom, hstep]
              simp[hch]
            simp[this]
            have : ((BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch)) = none := by
              simp[BuildLexingFST, Id.run, FST.evalFrom_fold_step]
              simp[hch, hstep, haccept]
            simp[this]
          case some qnext =>
            have hplex_step : PartialLex_trans spec (some (seed_ts, seed_wr)) (ExtChar.char ch) = some (seed_ts ++ [ExtChar.char unwrapped], [ch]) := by
              simp[PartialLex_trans]
              simp[FSA.evalFrom_append]
              simp[h₂_fsa, haccept]
              simp[FSA.evalFrom, hstep]
              simp[unwrapped, term, qsrc]
              simp[hch]

            have hplex_trans : PartialLex spec (wp ++ [head]) = some (seed_ts ++ [ExtChar.char unwrapped], [ch]) := by
              simpa [hh] using (PartialLex_append_singleton_of_trans spec h₀ hplex_step)

            have hlex_wp_step : (BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch) = some (LexingState.id qnext, seed_ts ++ [ExtChar.char unwrapped]) := by
              simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run]
              simp[hstep, haccept]
              simp[hch, unwrapped, term, qsrc]

            have hlex_wp_trans : fst.eval (wp ++ [head]) = some (LexingState.id qnext, seed_ts ++ [ExtChar.char unwrapped]) := by
              simpa [fst, hh] using (FST_eval_append_singleton_of_evalFrom_fold_step fst h₁ hlex_wp_step)

            have lex_wr_step : (BuildLexingFST spec).eval [ch] = some (LexingState.id qnext, []) := by
              simp[BuildLexingFST, Id.run, FST.eval, FST.evalFrom]
              simp[LexingState.src, hch]

            have ih := ih (wp ++ [head]) (LexingState.id qnext) (seed_ts ++ [ExtChar.char unwrapped]) [ch] hplex_trans hlex_wp_trans lex_wr_step (by simp)
            rw[hplex_step]
            rw[hlex_wp_step]
            unfold FST.evalFrom_fold_seed at ih
            exact ih
        case neg =>
          have : PartialLex_trans spec (some (seed_ts, seed_wr)) (ExtChar.char ch) = none := by
            simp[PartialLex_trans]
            simp[FSA.evalFrom_append]
            simp[h₂_fsa, FSA.evalFrom, hstep, haccept]
          simp[this]
          have : ((BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch)) = none := by
            simp[BuildLexingFST, Id.run, FST.evalFrom_fold_step]
            simp[hstep, haccept]
          simp[this]
      case some dst =>
        -- both will effectively take the transition specified by automata
        have hplex_step : PartialLex_trans spec (some (seed_ts, seed_wr)) (ExtChar.char ch) = some (seed_ts, seed_wr ++ [ch]) := by
          simp[PartialLex_trans]
          simp[FSA.evalFrom_append]
          simp[h₂_fsa]
          simp[FSA.evalFrom, hstep]

        have hplex_trans : PartialLex spec (wp ++ [head]) = some (seed_ts, seed_wr ++ [ch]) := by
          simpa [hh] using (PartialLex_append_singleton_of_trans spec h₀ hplex_step)

        have hlex_wp_step : (BuildLexingFST spec).evalFrom_fold_step (some (q', seed_ts)) (ExtChar.char ch) = some (LexingState.id dst, seed_ts) := by
          simp[FST.evalFrom_fold_step, BuildLexingFST, Id.run]
          simp[hstep]

        have hlex_wp_trans : fst.eval (wp ++ [head]) = some (LexingState.id dst, seed_ts) := by
          simpa [fst, hh] using (FST_eval_append_singleton_of_evalFrom_fold_step fst h₁ hlex_wp_step)

        have lex_wr_step : (BuildLexingFST spec).eval (seed_wr ++ [ch]) = some (LexingState.id dst, []) := by
          simp[FST.evalFrom, FST.evalFrom_append]
          rw[←FST.evalFrom_fold_eq_evalFrom]
          simp[FST.evalFrom_fold]
          rw[h₂]
          simp[BuildLexingFST, Id.run, hstep]

        have ih := ih (wp ++ [head]) (LexingState.id dst) seed_ts (seed_wr ++ [ch]) hplex_trans hlex_wp_trans lex_wr_step (by simp)
        rw[hplex_step]
        rw[hlex_wp_step]
        unfold FST.evalFrom_fold_seed at ih
        simp at ih
        exact ih

/-- The executable lexer and the lexing FST agree on successful executions. -/
theorem PartialLex_to_LexingFST (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) :
  ∀ w, match PartialLex spec w with
    | some (ts', wr) =>
      ∃ q', (BuildLexingFST spec).eval w = some (q', ts') ∧
        (BuildLexingFST spec).eval wr = some (q', [])
    | none => (BuildLexingFST spec).eval w = none := by
  let fst := BuildLexingFST spec
  let new_q0 := fst.start

  have := PartialLex_to_LexingFST_evalFold spec he
  intro w
  have := this [] w new_q0 [] []
  have := this rfl
  have := this (by simp[FST.eval, fst, new_q0]) (by simp[FST.eval, fst, new_q0]) (by simp[new_q0, fst])
  simp[PartialLex] at this ⊢
  rw[FST.evalFrom_fold_seed_eq_evalFrom_seed] at this
  simp[FST.evalFrom_seed] at this
  split
  <;> simp_all
  rename_i t'' wr _ _ _
  obtain ⟨q'', hq⟩ := this
  exists q''
  split at hq
  simp_all
  rename_i heq
  constructor
  simp[←hq.left]
  exact heq
  rw[FST.evalFrom_fold_seed_eq_evalFrom_seed] at hq
  simp[FST.evalFrom_seed] at hq
  split at hq
  try split at this
  rename_i heq
  simp at hq
  simp[hq] at heq
  simp_all
  split at this
  <;> simp_all
  assumption


/-- A relational lexing derivation yields a corresponding FST execution. -/
theorem PartialLexRel_to_LexingFST (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned) :
  ∀ w terminals unlexed,
    PartialLexRel spec w terminals unlexed →
    ∃ q', (BuildLexingFST spec).eval w = some (q', terminals) ∧
      (BuildLexingFST spec).eval unlexed = some (q', []) := by
  intro w terminals unlexed h
  have hpl := (PartialLex_pruned_eq_PartialLexRel spec hpruned w terminals unlexed).mp h
  have := PartialLex_to_LexingFST spec he w
  simp only [hpl] at this
  obtain ⟨q', heval_w, heval_unlexed⟩ := this
  exists q'

/-- Any successful lexing-FST execution can be reinterpreted as a relational
lexing derivation with some residual unlexed suffix. -/
theorem LexingFST_to_PartialLexRel (spec: LexerSpec α Γ σ) (he: [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned) :
  ∀ w q' terminals,
    (BuildLexingFST spec).eval w = some (q', terminals) →
    ∃ (unlexed : List α),
      (BuildLexingFST spec).eval unlexed = some (q', []) ∧ PartialLexRel spec w terminals unlexed := by
  intro w q' terminals h
  cases hpl : PartialLex spec w
  case none =>
    have : (BuildLexingFST spec).eval w = none := by
      have := PartialLex_to_LexingFST spec he w
      simp only [hpl] at this
      exact this
    simp at this
    simp[this] at h
  case some ts_wr =>
    have ⟨ ts', wr⟩ := ts_wr
    have := PartialLex_to_LexingFST spec he w
    simp only [hpl] at this
    obtain ⟨q'', heval_w, heval_wr⟩ := this
    have heq : q'' = q' ∧ ts' = terminals := by
      simp at h heval_w
      simp[heval_w] at h
      exact h
    exists wr
    simp at heval_wr ⊢
    constructor
    simp[heq] at heval_wr
    exact heval_wr
    have hrel := (PartialLex_pruned_eq_PartialLexRel spec hpruned w ts' wr).mpr
    simp only [hpl, heq] at hrel
    simp[hrel]

/-- Every transition of the lexing FST emits either no tokens, a singleton
token, or the special two-symbol output `[t, eos]` used on finalization. -/
lemma LexingFst_smallStep (spec: LexerSpec α Γ σ) :
  ∀ q a q' terminals,
    (BuildLexingFST spec).step q a = some (q', terminals) →
    terminals = [] ∨ (∃ t, terminals = [t]) ∨ (LexingState.src spec q ∈ spec.automaton.accept ∧ a = ExtChar.eos ∧ ∃ t, terminals = [ExtChar.char t, ExtChar.eos]) := by
  intro q a q' terminals h
  simp[BuildLexingFST, Id.run] at h
  split at h <;> split at h <;> simp_all
  have ⟨ha, _, pf⟩ := h
  apply Or.inr
  have pf := pf.right.right
  rw[←pf]
  simp
  apply Or.inr
  apply Or.inr
  rw[←h.right]
  simp
  simp[←h.right]

