import ConstrainedDecodingFormalization.Lexing.Correctness
import ConstrainedDecodingFormalization.Lexing.Detokenizing
import ConstrainedDecodingFormalization.Producible

/-!
# Whitespace exchange for detokenizing lexers

This file contains the whitespace-specific assumptions and exchange proofs used
to turn single-producibility into whitespace-modulo realizability.
-/

namespace Detokenizing

/-! ### Whitespace exchange arguments -/
open List
universe u v w x
variable {α : Type u} {Γ : Type v} {σ : Type w} {V : Type x}
variable [DecidableEq α] [DecidableEq σ] [BEq α] [BEq σ] [LawfulBEq σ] [BEq V]

/-- Assumptions isolating a distinguished whitespace character and token in the
lexer automaton.

These hypotheses drive the whitespace-specific exchange arguments in the later
part of the file.
-/
def WhitespaceAssumption (spec: LexerSpec α Γ σ) (tnonwhite : α) (twhite : α) (qnonwhite : σ) (qwhite : σ) : Prop :=
  qwhite ∈ spec.automaton.accept ∧
  (∀ s t, spec.automaton.step s t = some qwhite ↔ ((s = qwhite ∨ s = spec.automaton.start) ∧ t = twhite)) ∧
  (∀ t', twhite ≠ t' → spec.automaton.step qwhite t' = none) ∧
  (∀ q, q ≠ spec.automaton.start ∧ q ≠ qwhite → spec.automaton.step q twhite = none) ∧
  qnonwhite ∈ spec.automaton.accept ∧
  spec.automaton.step spec.automaton.start tnonwhite = some qnonwhite ∧
  tnonwhite ≠ twhite

/-- The token emitted by the distinguished whitespace accepting state. -/
def whitespaceTerminal (spec: LexerSpec α Γ σ) (tnonwhite : α) (twhite : α) (qnonwhite : σ) (qwhite : σ) (hw: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) : Γ :=
  let ret := spec.term qwhite
  have := (spec.hterm qwhite).mp hw.left
  ret.get this

omit [DecidableEq α] [BEq α] [BEq σ] [LawfulBEq σ] in
private lemma WhitespaceAssumption.existsRestartChar
    {tnonwhite twhite qnonwhite qwhite}
    (spec : LexerSpec α Γ σ)
    (hempty : [] ∉ spec.automaton.accepts)
    (hwa : WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) :
    ∀ s ∈ spec.automaton.accept,
      ∃ c : α, spec.automaton.step s c = none ∧
        (spec.automaton.step spec.automaton.start c).isSome := by
  intro s hs
  obtain ⟨_, hwhite_step, hwhite_only, hnonwhite_no_white, _, hnonwhite_start, hdiff⟩ := hwa
  by_cases hs_white : s = qwhite
  · subst hs_white
    refine ⟨tnonwhite, ?_, ?_⟩
    · exact hwhite_only tnonwhite (fun h => hdiff h.symm)
    · simp [hnonwhite_start]
  · refine ⟨twhite, ?_, ?_⟩
    · have hs_start : s ≠ spec.automaton.start := by
        intro h
        rw [h] at hs
        simp [FSA.accepts_iff] at hempty
        exact hempty hs
      exact hnonwhite_no_white s ⟨hs_start, hs_white⟩
    · have hstart_white : spec.automaton.step spec.automaton.start twhite = some qwhite := by
        exact (hwhite_step spec.automaton.start twhite).mpr (by simp)
      simp [hstart_white]

@[simp]
private def produce {σ V Γ} (step : σ × V × σ × List (Ch Γ)) : List (Ch Γ) :=
  step.2.2.2

private lemma detok_eval_embed { V Γ } [v: Vocabulary (Ch α) V] (spec: LexerSpec α Γ σ) (q: LexingState σ) (t: ExtChar α) :
  (BuildDetokLexer spec).step ((), q) (v.embed t) =
  (Option.map (fun x => (((), x.1), x.2)) ((BuildLexingFST spec).step q t)) := by
  simp[BuildDetokLexer]
  rw[detokenizer_comp_step]
  simp[v.fe]


private lemma flatMap_prefix_suffix {σ V Γ} (l : List (σ × V × σ × List (Ch Γ))) (j : Nat) (x : List (Ch Γ))
    (h : l.flatMap (fun (_, _, _, d) => d) = x) :
    (l.take j).flatMap (fun (_, _, _, d) => d) ++ (l.drop j).flatMap (fun (_, _, _, d) => d) = x := by
  simp at h
  have h_app : (l.take j) ++ (l.drop j) = l := by simp[List.take_append_drop]
  rw[←h_app] at h
  simp only [List.flatMap_append] at h
  simp
  exact h

-- general exchange argument
-- remove to shortest prefix that produces the token
-- may also assume that each word in the vocabulary is a singleton
section WhitespaceExchange

variable {tnonwhite twhite : α} {qnonwhite qwhite : σ}
variable [vocab : Vocabulary (Ch α) V]

omit [BEq V] in
private lemma exchange_basis (spec: LexerSpec α Γ σ) (char: ExtChar Γ)
  (q : LexingState σ) (hchar: char ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
  ∃ wpfx wlast pfx last,
                (BuildDetokLexer (v := vocab) spec).stepList ((), q) (wpfx) = some (pfx) ∧
                (BuildDetokLexer (v := vocab) spec).stepList ((), q) (wpfx ++ [wlast]) = some (pfx ++ [last]) ∧
                flatMap produce pfx = [] ∧
                produce last = [char] ∧
                (BuildDetokLexer (v := vocab) spec).evalFrom ((), q) (wpfx ++ [wlast]) = some (last.2.2.1, [char]) ∧
                ∀ t ∈ (wpfx ++ [wlast]), ∃ t0, vocab.flatten t = [t0] := by
  let lexer := BuildDetokLexer (v := vocab) spec
  simp[FST.singleProducible] at hchar
  obtain ⟨w, _, qf, hwqforg⟩ := hchar
  simp[BuildDetokLexer] at hwqforg
  obtain ⟨w, hwqf, hw⟩ := detokenize_singleton (v := vocab) (BuildLexingFST spec) q w
  rw[hwqforg, Eq.comm] at hwqf
  have dum : (BuildDetokenizingFST.compose (BuildLexingFST spec)) = BuildDetokLexer (v := vocab) spec := by simp[BuildDetokLexer]
  rw[dum] at hwqf
  have := lexer.stepList_of_eval ((), q) w
  simp[lexer, hwqf] at this
  obtain ⟨step_list, hstep_list, flat_step⟩ := this
  let firstTransitionIndexO := step_list.findFinIdx? (fun step => produce step ≠ [])
  have : firstTransitionIndexO.isSome := by
    by_contra h
    simp only [findFinIdx?_eq_none_iff, Option.not_isSome_iff_eq_none, firstTransitionIndexO] at h
    simp only [produce, ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, Decidable.not_not] at h
    have : flatMap (fun step => produce step) step_list = [] := by
      simp only [mem_map, produce, flatMap, flatten_eq_nil_iff]
      intro l he
      obtain ⟨a, ha⟩ := he
      rw[h a] at ha
      <;> simp[ha]
    simp only [produce] at this
    rw[flat_step.left] at this
    simp at this
  obtain ⟨firstTransitionIndex, ho⟩ : ∃ i, firstTransitionIndexO = some i := by
    simp only [Option.isSome_iff_exists, firstTransitionIndexO] at this
    exact this
  have hfirst := findFinIdx?_eq_some_iff.mp ho
  simp at hfirst
  obtain ⟨hne, hbefore⟩ := hfirst
  have h_prefix_empty : (step_list.take firstTransitionIndex).flatMap produce = [] := by
    simp[flatMap]
    intro l hl
    obtain ⟨j, hjlt, hj⟩ := List.mem_take_iff_getElem.mp (by simpa using hl)
    rw[←hj]
    simp
    have : j < step_list.length := Nat.lt_trans (Nat.lt_min.mp hjlt).left (by simp : firstTransitionIndex < step_list.length)
    exact hbefore (Fin.mk j this) (Nat.lt_min.mp hjlt).left
  unfold produce at h_prefix_empty
  -- The first non-empty transition produces exactly [char]
  have hprod_first : produce step_list[firstTransitionIndex] = [char] := by
    have h_decomp := flatMap_prefix_suffix step_list firstTransitionIndex [char] flat_step.left
    simp[h_prefix_empty] at h_decomp

    have : step_list[firstTransitionIndex] :: (step_list.drop firstTransitionIndex).tail = step_list.drop firstTransitionIndex := by
      have : firstTransitionIndex < step_list.length := by simp
      simp only [List.drop_eq_getElem_cons this]
      simp

    rw[←this] at h_decomp
    simp[flatMap] at h_decomp
    cases hprod : (drop (↑firstTransitionIndex) (map (fun x => x.2.2.2) step_list))
    <;> rw[hprod] at h_decomp
    . simp at h_decomp
    . rename_i head tail
      simp[append_eq_singleton_iff] at h_decomp
      set dummy := head :: tail with hdummy
      have : dummy.head (by simp) = head := by simp[dummy]
      simp_rw[←hprod] at this
      simp at this
      rw[←this] at h_decomp
      cases h_decomp
      case inr h => simp[h]
      case inl h => simp[hne] at h

  have hslen:= lexer.stepList_len ((), q) w
  simp[lexer, hstep_list] at hslen
  have hft_lt_w : firstTransitionIndex.val < w.length := by
    rw[←hslen]
    simp
  exists w.take firstTransitionIndex
  exists w[firstTransitionIndex]'hft_lt_w
  exists step_list.take firstTransitionIndex
  exists step_list[firstTransitionIndex]
  have hpfxo := lexer.stepList_prefix_w ((), q) w
  simp[lexer, hstep_list] at hpfxo
  have hpfx := hpfxo (List.take (↑firstTransitionIndex + 1) w) (by simp[List.take_prefix])
  constructor
  . have hpfx := hpfxo (List.take ↑firstTransitionIndex w) (by simp[List.take_prefix])
    simp[hpfx]
    exact Nat.le_of_lt hft_lt_w
  constructor
  . simp[hpfx]
    simp[hslen]
  . constructor
    · simp[flatMap]
      intro l hl
      obtain ⟨j, hjlt, hj⟩ := List.mem_take_iff_getElem.mp (by simpa using hl)
      rw[←hj]
      simp
      have : j < step_list.length := Nat.lt_trans (Nat.lt_min.mp hjlt).left (by simp : firstTransitionIndex < step_list.length)
      exact hbefore (Fin.mk j this) (Nat.lt_min.mp hjlt).left
    constructor
    . exact hprod_first
    . have := lexer.eval_of_stepList ((), q) (take (↑firstTransitionIndex + 1) w)
      simp[lexer, hpfx] at this
      have hlt : firstTransitionIndex + 1 ≤ w.length := by simp[←hslen, Nat.add_one_le_of_lt]
      simp[hlt] at this
      simp[this]
      simp[getLast?_take]
      rw[take_add_one]
      simp only [List.flatMap_append, h_prefix_empty]
      simp at hprod_first
      simp[hprod_first]
      intro t ht
      apply hw
      exact List.mem_of_mem_take ht

-- the only reachable state from qwhite is qwhite
omit [DecidableEq σ] [BEq α] [BEq σ] [LawfulBEq σ] in
private lemma whitespaceState_evalFrom_eq (spec: LexerSpec α Γ σ)
  (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) :
    ∀ q w, spec.automaton.evalFrom qwhite w = some q → q = qwhite := by
  intro q w h
  induction w
  case nil =>
    simp[FSA.evalFrom] at h
    exact h.symm
  case cons head tail ih =>
    obtain ⟨_, hstay , hwa, _⟩ := hwa
    simp[FSA.evalFrom] at h
    split at h
    simp at h
    rename_i heq
    have : head = twhite := by
      by_contra hx
      have := hwa head (by intro hx'; exact hx hx'.symm)
      rw[this] at heq
      simp at heq
    have hstay := hstay qwhite head
    simp[this] at hstay heq
    rw[hstay] at heq
    simp at heq
    simp[←heq] at h
    exact ih h

-- for any non qwhite state
-- we can build a path to it that does not start with twhite
omit [BEq V] in
private lemma pathToNonWhitespaceState (spec: LexerSpec α Γ σ)
  (hpruned: spec.automaton.pruned) (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite)
  : ∀ qtarget, qtarget ≠ qwhite → qtarget ≠ spec.automaton.start →
    ∃ ws wt qi, ws ≠ twhite ∧
            spec.automaton.step spec.automaton.start ws = some qi ∧
            (BuildDetokLexer (v := vocab) spec).step (Unit.unit, LexingState.start) (vocab.embed ws) = some (((), LexingState.id qi), []) ∧
            (BuildDetokLexer (v := vocab) spec).evalFrom (Unit.unit, LexingState.start) (map vocab.embed (ExtChar.char ws :: wt)) = some ((Unit.unit, LexingState.id qtarget), []) := by
  -- take
  intro qt hqt_nonwhite hqt_nstart
  simp[FSA.pruned] at hpruned
  obtain ⟨w, hw⟩ := (hpruned qt).right
  have : w ≠ [] := by
    intro h
    simp[h] at hw
    exact hqt_nstart hw
  let h := w.head this
  have hhtail : w = h :: w.tail := by simp[h]
  have ⟨step, hstep⟩ : ∃ q, spec.automaton.step spec.automaton.start h = some q := by
    rw[hhtail] at hw
    simp[FSA.evalFrom] at hw
    split at hw
    simp at hw
    rename_i s' heq
    exists s'

  exists h
  exists map ExtChar.char w.tail
  exists step
  constructor
  . intro ha
    rw[hhtail] at hw
    simp[FSA.evalFrom] at hw
    split at hw
    simp at hw
    rename_i heq
    simp[ha] at heq
    have ⟨_, hstay, _⟩ := hwa
    have hstay := hstay spec.automaton.start h
    simp[ha] at hstay
    rw[heq] at hstay
    simp at hstay
    simp[hstay] at hw
    have := whitespaceState_evalFrom_eq spec hwa qt (w.tail) hw.symm
    exact hqt_nonwhite this
  constructor
  exact hstep
  constructor
  . simp[detok_eval_embed, BuildLexingFST, Id.run, LexingState.src]
    simp[hstep]
  . rw[←List.map_cons, ←hhtail]
    generalize hqs : spec.automaton.start = qs at hw
    generalize hq's : LexingState.start = q's
    have hrel : LexingState.src spec q's = qs := by
      simp[LexingState.src, hqs]
      simp[←hq's]
    clear hqs hq's hstep
    induction w generalizing qs q's
    case nil => simp at hhtail
    case cons head tail ih =>
      simp[FSA.evalFrom] at hw
      simp at ih ⊢
      simp[FST.evalFrom]
      split at hw <;> try simp at hw
      simp[detok_eval_embed]
      simp[BuildLexingFST, Id.run]
      rename_i s heq
      simp[hrel, heq]
      by_cases h : tail = []
      simp[h] at hw ⊢
      exact hw.symm
      have ih' := ih h s hw (LexingState.id s) (by simp[LexingState.src])
      rw[ih']

-- extract the common proof that qp.2 = LexingState.id qwhite
omit [BEq V] in
private lemma exchangeBasis_endsAtWhitespaceState (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ)
  (_: (BuildDetokLexer (v := vocab) spec).stepList ((), q) (wpfx ++ [wlast]) = some (pfx ++ [last]))
  (hflat_pfx: flatMap produce pfx = [])
  (hlast: produce last = [ExtChar.char (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa)])
  (hflat: ∀ t ∈ wpfx ++ [wlast], ∃ t0, vocab.flatten t = [t0])
  (heval: (BuildDetokLexer (v := vocab) spec).evalFrom ((), q) (wpfx ++ [wlast]) = some (last.2.2.1, [ExtChar.char (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa)]))
  (hqp: (BuildDetokLexer spec).evalFrom ((), q) wpfx = some ((unt, qp), flatMap (fun x => x.2.2.2) pfx)) : qp = LexingState.id qwhite := by
  simp[FSA.accepts_iff] at hempty
  unfold produce at hflat_pfx hlast
  simp[FST.evalFrom_append, hflat_pfx, hqp] at heval
  simp[BuildDetokLexer] at heval
  rw[detokenizer_comp_step] at heval
  obtain ⟨t, ht⟩ := hflat wlast (by simp)
  rw[ht] at heval
  simp[FST.evalFrom_singleton] at heval
  have ⟨unt, hunt⟩ := heval
  simp[BuildLexingFST, Id.run] at hunt
  split at hunt
  <;> split at hunt
  <;> try split at hunt
  all_goals (
    simp at hunt
  )
  obtain ⟨⟨a, ⟨_, _, hq⟩⟩, x⟩ := hunt
  obtain ⟨haccept, _⟩ := hwa
  simp[whitespaceTerminal] at hq
  have hws := ((spec.hterm qwhite).mp haccept)
  rename_i haccept2 _ _ _
  have hqps := ((spec.hterm (LexingState.src spec qp)).mp haccept2)
  have := spec.term_inj (LexingState.src spec qp) qwhite ((spec.term qwhite).get hws)
  simp at this
  have hterm_eq : spec.term (LexingState.src spec qp) = spec.term qwhite := by
    simp[Option.isSome_iff_exists] at hws hqps
    obtain ⟨a, ha⟩ := hws
    obtain ⟨b, hb⟩ := hqps
    simp_rw[ha, hb] at hq
    simp at hq
    simp[ha, hb]
    exact hq
  simp[hterm_eq] at this
  unfold LexingState.src at this
  split at this <;> try simp[this]
  rw[←this] at haccept
  exact hempty haccept

-- if you can produce a single whitespace,
-- you can produce whitespace while ending up at any non whitespace state
--
-- most complicated of the exchange arguments
-- since white term is producible, we may find a path that goes to qwhite
-- traverse that path, then traverse the path to the qtarget (which must not start with qwhite)
-- these two together will produce the necessary construction
omit [BEq V] in
private lemma exchangeWhitespace (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned) (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ)
  (hwsa: ExtChar.char (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa) ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
    ∀ qtarget, qtarget ≠ qwhite → qtarget ≠ spec.automaton.start →
    ∃ w, (BuildDetokLexer (v := vocab) spec).evalFrom (Unit.unit, q) w = some ((Unit.unit, LexingState.id qtarget), [ExtChar.char (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa)]) := by
  let lexer := BuildDetokLexer (v := vocab) spec
  let white_term := whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa
  obtain ⟨wpfx, wlast, pfx, last, hprefix_list, hstep_list, hflat_pfx, hlast, heval, hflat⟩ := exchange_basis spec white_term q hwsa
  intro qtarget hqt_nonwhite hqt_nstart
  obtain ⟨ws, wt, step, hws_nwhite, hstep, hfst_step, hw⟩ := pathToNonWhitespaceState (vocab := vocab) spec hpruned hwa qtarget hqt_nonwhite hqt_nstart
  let w := wpfx ++ ([vocab.embed ws] ++ (map vocab.embed wt))
  exists w
  simp[w, FST.evalFrom_append]
  rw[←map_cons]
  have := lexer.eval_of_stepList_opaque ((), q) wpfx
  simp[lexer, hprefix_list] at this
  obtain ⟨unt, qp, hqp⟩ := this
  simp[hqp]
  exists ()
  unfold produce at hflat_pfx
  simp[hflat_pfx]
  have hqp_white : qp = LexingState.id qwhite := by
    exact exchangeBasis_endsAtWhitespaceState spec hempty hwa q hstep_list hflat_pfx hlast hflat heval hqp

  simp only [hqp_white]
  have : unt = () := by simp
  rw[this]
  simp[FST.evalFrom] at hw ⊢
  simp[detok_eval_embed]
  simp[BuildLexingFST, Id.run]
  obtain ⟨haccept, _, hwa, _⟩ := hwa
  have hwa := hwa ws (by intro ha; exact hws_nwhite ha.symm)
  simp[hwa, haccept]
  simp[whitespaceTerminal]
  split at hw
  simp at hw
  rename_i heq
  simp[hstep]
  simp[hfst_step] at heq
  rw[heq.left]
  simp[heq] at hw
  split at hw
  simp at hw
  rename_i heq'
  simp[heq']
  simp at hw
  exact hw

-- if you can produce whitespace,
-- you can produce that and eos and end at qwhite
omit [BEq V] in
private lemma exchangeWhitespaceEOS (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ)
  (hwsa: ExtChar.char (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa) ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
    ∃ w, (BuildDetokLexer (v := vocab) spec).evalFrom (Unit.unit, q) w = some ((Unit.unit, LexingState.id qwhite), [ExtChar.char (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa), ExtChar.eos]) := by
  let lexer := BuildDetokLexer (v := vocab) spec
  let white_term := whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa
  obtain ⟨wpfx, wlast, pfx, last, hprefix_list, hstep_list, hflat_pfx, hlast, heval, hflat⟩ := exchange_basis spec white_term q hwsa
  let w := wpfx ++ [vocab.embed .eos, vocab.embed twhite]
  exists w
  simp[w, FST.evalFrom_append]
  have := lexer.eval_of_stepList_opaque ((), q) wpfx
  simp[lexer, hprefix_list] at this
  obtain ⟨unt, qp, hqp⟩ := this
  unfold produce at hflat_pfx
  simp[hqp, hflat_pfx]
  have hqp_white : qp = LexingState.id qwhite := by
    exact exchangeBasis_endsAtWhitespaceState spec hempty hwa q hstep_list hflat_pfx hlast hflat heval hqp

  simp[hqp_white, BuildDetokLexer, FST.evalFrom]
  rw[detokenizer_comp_step]
  simp[vocab.fe]
  simp[BuildLexingFST, Id.run]
  obtain ⟨haccept, hwa, _⟩ := hwa
  simp[haccept]
  rw[detokenizer_comp_step]
  simp[vocab.fe, LexingState.src, FST.evalFrom_singleton]
  have hwa := hwa spec.automaton.start twhite
  simp at hwa
  simp[hwa, whitespaceTerminal]

-- if you can produce a single nonwhitespace,
-- you can produce that nonwhitespace while ending up at qwhite
omit [BEq V] in
private lemma exchangeNonWhitespace (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ) (term: Γ)
  (hterm: term ≠ (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa) ∧ ExtChar.char term ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
    ∃ w, (BuildDetokLexer (v := vocab) spec).evalFrom (Unit.unit, q) w = some ((Unit.unit, LexingState.id qwhite), [ExtChar.char term]) := by
  simp[FSA.accepts_iff] at hempty
  let lexer := BuildDetokLexer (v := vocab) spec
  obtain ⟨wpfx, wlast, pfx, last, hprefix_list, hstep_list, hflat_pfx, hlast, heval, hflat⟩ := exchange_basis spec term q hterm.right
  let w := wpfx ++ [vocab.embed twhite]
  exists w
  simp[w, FST.evalFrom_append]
  have := lexer.eval_of_stepList_opaque ((), q) wpfx
  simp[lexer, hprefix_list] at this
  obtain ⟨unt, qp, hqp⟩ := this
  unfold produce at hflat_pfx
  simp[hflat_pfx] at hqp
  simp[hqp]
  -- since we produced term on the original branch
  -- old state must be that as well (in particular, not whitespace)
  have hqp_nwhite : (LexingState.src spec qp ≠ spec.automaton.start) ∧ qp ≠ LexingState.id qwhite ∧ spec.term (LexingState.src spec qp) = some term := by
    simp[FST.evalFrom_append, hqp] at heval
    simp[BuildDetokLexer] at heval
    rw[detokenizer_comp_step] at heval
    obtain ⟨t, ht⟩ := hflat wlast (by simp)
    rw[ht] at heval
    simp[FST.evalFrom_singleton] at heval
    obtain ⟨a, ha⟩ := heval
    simp[BuildLexingFST, Id.run] at ha
    split at ha
    <;> split at ha
    <;> try split at ha
    all_goals (
      simp at ha
    )
    obtain ⟨⟨q, hsteps, hqa, hspec⟩, g⟩ := ha
    rename_i hfailstep haccept
    constructor
    . intro ha
      rw[ha] at haccept
      exact hempty haccept
    have hspec' : spec.term (LexingState.src spec qp) = some term := by
      simp_rw[←hspec]
      simp
    constructor
    . intro ha
      rw[ha] at hspec'
      simp[whitespaceTerminal] at hterm
      rw[←hspec] at hterm
      simp_rw[ha] at hterm
      simp[LexingState.src] at hterm
    . exact hspec'
  simp[BuildDetokLexer]
  rw[detokenizer_comp_step]
  simp[vocab.fe]
  simp[BuildLexingFST, Id.run]
  cases hstep : (spec.automaton.step (LexingState.src spec qp) twhite)
  simp
  obtain ⟨_, hwa, _⟩ := hwa
  have := hwa spec.automaton.start twhite
  simp at this
  simp[this]
  simp[hqp_nwhite]
  have := (spec.hterm (LexingState.src spec qp)).mpr (by simp[hqp_nwhite.right.right])
  exact this
  simp
  obtain ⟨haccept, _, _,  hwa, _⟩ := hwa
  have := hwa (LexingState.src spec qp)
  simp[hstep] at this
  simp[hqp_nwhite] at this
  unfold LexingState.src at this
  split at this
  rename_i a
  simp at hqp_nwhite hstep
  have := hwa a (by simp[hqp_nwhite])
  simp[this] at hstep
  rw[this] at hempty
  exact hempty haccept

-- if you can produce eos,
-- you can produce eos while ending up at qwhite
omit [BEq V] in
private lemma exchangeEOS (spec: LexerSpec α Γ σ)
  (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ)
  (hterm: ExtChar.eos ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
    ∃ w, (BuildDetokLexer (v := vocab) spec).evalFrom (Unit.unit, q) w = some ((Unit.unit, LexingState.id qwhite), [ExtChar.eos]) := by
  -- exchange basis, can get it to something that has a steplist which is empty and then [target]
  -- and for non eos, that means it must
  let lexer := BuildDetokLexer (v := vocab) spec
  obtain ⟨wpfx, wlast, pfx, last, hprefix_list, hstep_list, hflat_pfx, hlast, heval, hflat⟩ := exchange_basis spec (ExtChar.eos) q hterm
  set w := wpfx ++ [wlast]
  exists w ++ [vocab.embed twhite]
  have := lexer.eval_of_stepList ((), q) w
  simp[lexer] at this
  -- show that last.2.2.1 = qstart since thats the only way to produce a single eos
  have hlast_start : last.2.2.1 = ((), LexingState.start) := by
    have := lexer.stepList_zip ((), q) w
    simp only [lexer, hstep_list] at this
    have := this last (by simp)
    simp at hlast
    have l : last.2.2 = (last.2.2.1, [ExtChar.eos]) := by simp[←hlast]
    rw[l] at this
    simp[BuildDetokLexer] at this
    rw[detokenizer_comp_step] at this
    simp[BuildLexingFST, Id.run] at this
    have hmw : last.2.1 ∈ w := by
      have := lexer.stepList_mem_w  (() , q) w
      rw[hstep_list] at this
      simp only [] at this
      exact this last (by simp)
    obtain ⟨t, ht⟩ := hflat last.2.1 hmw
    rw[ht] at this
    simp[FST.evalFrom_singleton] at this
    split at this
    <;> split at this
    <;> try split at this
    all_goals (
      obtain ⟨a, ha⟩ := this
      simp at ha
    )
    simp[ha]
  simp[FST.evalFrom_append, heval]
  simp[BuildDetokLexer]
  rw[detokenizer_comp_step]
  simp[vocab.fe]
  simp[hlast_start, BuildLexingFST, Id.run]
  obtain ⟨_, hwa, _⟩ := hwa
  have := hwa spec.automaton.start twhite
  simp at this
  simp[LexingState.src, this]

omit [BEq V] in
private lemma whitespaceState_singleProducible (spec: LexerSpec α Γ σ)
  (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) :
    ExtChar.char (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa) ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, LexingState.id qwhite) := by
  simp[FST.singleProducible]
  exists [vocab.embed tnonwhite]
  simp[BuildDetokLexer, detokenizer_comp_step]
  simp[BuildLexingFST, Id.run, vocab.fe]
  obtain ⟨hqwhite, _, h, _, hqnwhite, hqnwhite_t, hdiff⟩ := hwa
  have := h tnonwhite hdiff.symm
  simp[this]
  constructor
  exists qnonwhite
  exists hqwhite

omit [BEq V] in
lemma moddedRealizableSequences_eq_not_contains_whitespace
  [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned)
  (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ)
  (hwsa: ExtChar.char (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa) ∈ (BuildDetokLexer (v := vocab) spec).singleProducible (Unit.unit, q)) :
    let white_term := (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa)
    { Ts | ¬Ts.contains (ExtChar.char (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa)) } =
    (BuildDetokLexer (v := vocab) spec).moddedRealizableSequences (Unit.unit, q) white_term := by
  intro white_term
  ext x
  simp only [Set.mem_setOf]

  apply Iff.intro
  . simp[FST.moddedRealizableSequences]
    intro h
    induction x generalizing q
    case nil =>
      exists []
      simp[FST.realizableSequences]
      exists ()
      exists q
      exists []
    case cons head tail ih =>
      have hwsa_o := hwsa
      simp[FST.singleProducible] at h hwsa
      have ⟨fatwstart, _, q', hq'⟩ := hwsa
      simp[BuildDetokLexer] at hq'
      cases hhead : head
      case char ch =>
        -- first build the sequence that produces just whitespace
        -- then build the actual target
        -- then append a whitespace
        -- then build the tail
        have ⟨qtarget, hqtarget⟩ := spec.term_surj ch
        have hqtarget_accept : qtarget ∈ spec.automaton.accept := by
          simp[spec.hterm, hqtarget]
        have hnestart : qtarget ≠ spec.automaton.start := by
          intro ha
          rw[ha] at hqtarget
          have : spec.automaton.start ∈ spec.automaton.accept := by
            simp[spec.hterm, hqtarget]
          simp[FSA.accepts_iff] at hempty
          exact hempty this
        have hne_qwhite : qtarget ≠ qwhite := by
          intro ha
          simp[ha] at hqtarget
          simp[whitespaceTerminal, hqtarget] at h
          exact h.left hhead.symm
        obtain ⟨wbase, hwbase⟩ := exchangeWhitespace (vocab := vocab) spec hempty hpruned hwa q hwsa_o qtarget hne_qwhite hnestart
        let wfull := wbase ++ [vocab.embed twhite]
        have ⟨tail_seq, htail_seq⟩ := ih (LexingState.id qwhite) (whitespaceState_singleProducible (vocab := vocab) spec hwa) h.right
        exists [ExtChar.char white_term, head] ++ tail_seq
        constructor
        simp[FST.realizableSequences] at htail_seq ⊢
        change
          (∃ a b w, (BuildDetokLexer spec).evalFrom ((), LexingState.id qwhite) w = some ((a, b), tail_seq)) ∧
            filter (fun x => x != ExtChar.char white_term) tail_seq = tail at htail_seq
        change ∃ a b w, (BuildDetokLexer spec).evalFrom ((), q) w = some ((a, b), [ExtChar.char white_term, head] ++ tail_seq)
        exists Unit.unit
        obtain ⟨_, qf, ⟨wtail, hwqf⟩⟩ := htail_seq.left
        exists qf
        exists wfull ++ wtail
        simp[wfull, FST.evalFrom_append]
        simp[hwbase, white_term, FST.evalFrom]
        nth_rewrite 1 [BuildDetokLexer]
        simp[detokenizer_comp_step, vocab.fe, BuildLexingFST, Id.run]
        have : spec.automaton.step qtarget twhite = none := by
          obtain ⟨_, _, _, target, _⟩ := hwa
          have := target qtarget
          simp[hne_qwhite, hnestart] at this
          exact this
        simp[this, hqtarget_accept, hqtarget]
        obtain ⟨_, target, _⟩ := hwa
        have := target spec.automaton.start twhite
        simp at this
        simp[this, hwqf, hhead]
        simp[white_term, filter_cons, htail_seq]
        simp[hhead] at h ⊢
        rw[eq_comm]
        exact h.left
      case eos =>
        obtain ⟨wbase, hwbase⟩ := exchangeWhitespaceEOS (vocab := vocab) spec hempty hwa q hwsa_o
        have ⟨tail_seq, htail_seq⟩ := ih (LexingState.id qwhite) (whitespaceState_singleProducible (vocab := vocab) spec hwa) h.right
        exists [ExtChar.char white_term, ExtChar.eos] ++ tail_seq
        constructor
        simp[FST.realizableSequences] at htail_seq ⊢
        change
          (∃ a b w, (BuildDetokLexer spec).evalFrom ((), LexingState.id qwhite) w = some ((a, b), tail_seq)) ∧
            filter (fun x => x != ExtChar.char white_term) tail_seq = tail at htail_seq
        change ∃ a b w, (BuildDetokLexer spec).evalFrom ((), q) w = some ((a, b), [ExtChar.char white_term, ExtChar.eos] ++ tail_seq)
        exists Unit.unit
        obtain ⟨_, qf, ⟨wtail, hwqf⟩⟩ := htail_seq.left
        exists qf
        exists wbase ++ wtail
        simp[FST.evalFrom_append, hwbase]
        simp[white_term]
        constructor
        exact hwqf
        simp[htail_seq]
  . intro h
    simp[FST.moddedRealizableSequences] at h
    have ⟨v, hv⟩ := h
    simp[white_term] at hv
    rw[←hv.right]
    simp

end WhitespaceExchange

private lemma find_first_nonempty { σ V Γ } [BEq (Ch Γ)] [LawfulBEq (Ch Γ)] (filtered_step_list : List (σ × V × σ × List (Ch Γ)))
    (x : List (Ch Γ)) (he : x ≠ [])
    (h_filt : filtered_step_list.flatMap produce = x) :
    ∃ idx, produce filtered_step_list[idx] ≠ [] ∧
          ∀ (j : Fin filtered_step_list.length), j < idx → produce filtered_step_list[j] = [] := by
  let oFirst := filtered_step_list.findFinIdx? (fun a => produce a != [])
  have h_some : oFirst.isSome := by
    by_contra ha
    simp only [not_not, ne_eq, bne_iff_ne, Option.not_isSome_iff_eq_none, findFinIdx?_eq_none_iff, oFirst] at ha
    have hnull: (List.map produce filtered_step_list) = List.map (fun _ => []) filtered_step_list := by
      apply List.map_congr_left
      exact ha
    simp[flatMap, hnull] at h_filt
    simp[h_filt] at he
  exists oFirst.get h_some
  have h_find : filtered_step_list.findFinIdx? (fun a => produce a != []) = some (oFirst.get h_some) := by
    simp only [Option.some_get, oFirst]
  have := findFinIdx?_eq_some_iff.mp h_find
  simp at this
  exact this

private lemma empty_prefix_all_empty {σ V Γ} (step_list : List (σ × V × σ × List (Ch Γ)))
    (idx : Fin step_list.length)
    (h_prefix : ∀ (j : Fin step_list.length), j < idx → produce step_list[j] = []) :
    (step_list.take idx).flatMap (fun a => produce a) = [] := by
  simp[List.flatMap]
  intro l hl
  obtain ⟨j, hjlt, hj⟩ := List.mem_take_iff_getElem.mp (by simpa using hl)
  rw[←hj]
  simp
  have hjlti := (Nat.lt_min.mp hjlt).left
  have : j < step_list.length := by
    have : idx < step_list.length := by simp
    exact Nat.lt_trans hjlti this
  exact h_prefix (Fin.mk j this) hjlti

-- Helper: show first element equals head of first nonempty transition
private lemma first_eq_head_of_first_nonempty {Γ V σ} (x : List (Ch Γ)) (he : x ≠ [])
    (step_list : List (σ × V × σ × List (Ch Γ))) (idx : Fin step_list.length)
    (h_filt : step_list.flatMap (fun a => produce a) = x)
    (h_prefix_empty : (step_list.take idx).flatMap (fun a => produce a) = [])
    (hne : produce step_list[idx] ≠ []) :
    x.head he = (produce step_list[idx]).head hne := by
  simp at hne
  have h_decomp := flatMap_prefix_suffix step_list idx x h_filt
  simp only [produce] at h_prefix_empty
  simp[h_prefix_empty] at h_decomp
  subst h_decomp
  simp[List.flatMap]
  rw[List.head_flatten_eq_head_head]
  simp
  simp[hne]

section SingleProducibleHead

variable [BEq (Ch Γ)] [LawfulBEq (Ch Γ)]
variable {tnonwhite twhite : α} {qnonwhite qwhite : σ}
variable [vocab : Vocabulary (Ch α) V]

omit [BEq V] in
/-- If the composed detokenizing lexer produces nonempty output from state `q`,
then the head of that output is singleton-producible from `q`.

This is the core FST-side lemma for completeness: it bridges a multi-step run
producing `T ≠ []` to a witness in `singleProducible q`.

The `hrestart` hypothesis asks that every accepting state of the character
automaton has at least one character that does **not** extend the current
lexeme but **can** start a new one from the start state.  This ensures
the lexer can always complete a token with a single-symbol emission
(without appending EOS), which is required when the first emission on a
run is the two-symbol EOS-triggered `[char t, eos]` pattern.  The
hypothesis holds for all practical lexer specifications—see the project
README for discussion. -/
theorem BuildDetokLexer_singleProducible_of_evalFrom
    (spec : LexerSpec α Γ σ)
    (_hempty : [] ∉ spec.automaton.accepts)
    (hrestart : ∀ s ∈ spec.automaton.accept,
      ∃ c : α, spec.automaton.step s c = none ∧
        (spec.automaton.step spec.automaton.start c).isSome)
    (q : LexingState σ) (w : List V) (qf : Unit × LexingState σ)
    (T : List (Ch Γ))
    (hrun : (BuildDetokLexer (v := vocab) spec).evalFrom ((), q) w = some (qf, T))
    (hne : T ≠ []) :
    T.head hne ∈ (BuildDetokLexer (v := vocab) spec).singleProducible ((), q) := by
  let lexer := BuildDetokLexer (v := vocab) spec
  have hlexer : lexer = (BuildDetokenizingFST.compose (BuildLexingFST spec)) := by
    simp[BuildDetokLexer, lexer]
  -- Stage 1: reduce to singleton tokens
  have h_singleton := detokenize_singleton (v := vocab) (BuildLexingFST spec) q w
  rw[←hlexer] at h_singleton
  obtain ⟨ws, h_eq, h_ws_singleton⟩ := h_singleton
  rw[hrun] at h_eq
  -- Stage 2: decompose into step list
  have h_step_list_exists := lexer.stepList_of_eval ((), q) ws
  simp[←h_eq] at h_step_list_exists
  obtain ⟨step_list, h_step_list⟩ := h_step_list_exists
  -- Stage 3: find first non-empty emission
  obtain ⟨firstIdx, hft_ne, h_prefix_empty⟩ :=
    find_first_nonempty step_list T hne h_step_list.right.left
  -- Each token in ws is singleton
  have ⟨flat, h_flat⟩ : ∃ t, vocab.flatten step_list[firstIdx.val].2.1 = [t] := by
    have := lexer.stepList_w ((), q) ws
    simp only [h_step_list] at this
    have : step_list[firstIdx].2.1 ∈ ws := by
      have h_in : step_list[firstIdx].2.1 ∈ List.map (fun x => x.2.1) step_list := by
        apply List.mem_map.mpr
        exists step_list[firstIdx]
        simp
      rw[this] at h_in
      exact h_in
    exact h_ws_singleton step_list[firstIdx].2.1 this
  -- Stage 4: classify via LexingFst_smallStep
  have h_first_production : lexer.step step_list[firstIdx].1 step_list[firstIdx].2.1 =
      some step_list[firstIdx].2.2 := by
    have := lexer.stepList_zip ((), q) ws
    simp only [h_step_list] at this
    exact this step_list[firstIdx] (by simp)
  simp[lexer, BuildDetokLexer] at h_first_production
  rw[detokenizer_comp_step] at h_first_production
  simp[h_flat] at h_first_production
  obtain ⟨q', produced, hstep, hq'produced⟩ := h_first_production
  have h_small := LexingFst_smallStep spec step_list[firstIdx].1.2 flat q' produced hstep
  have hproduced_ne : produced ≠ [] := by
    have : produced = step_list[firstIdx].2.2.2 := by
      simpa using congrArg Prod.snd hq'produced
    rw[this]; simp at hft_ne; exact hft_ne
  simp[hproduced_ne] at h_small
  -- Prefix produces empty output
  have h_prefix_empty_flat : (step_list.take firstIdx).flatMap produce = [] :=
    empty_prefix_all_empty step_list firstIdx h_prefix_empty
  -- Compute the head
  have h_head_eq : T.head hne = (produce step_list[firstIdx]).head (by simp at hft_ne; exact hft_ne) :=
    first_eq_head_of_first_nonempty T hne step_list firstIdx h_step_list.right.left h_prefix_empty_flat hft_ne
  -- stepList prefix/take info
  have hslen := lexer.stepList_len ((), q) ws
  simp[lexer, h_step_list] at hslen
  have hft_lt_w : firstIdx.val < ws.length := by rw[←hslen]; simp
  -- Case split on output structure
  cases h_small with
  | inl h_one =>
    -- Case 1: produced = [t], exactly one symbol
    obtain ⟨t, ht⟩ := h_one
    have hprod_eq : produced = step_list[firstIdx].2.2.2 := by
      simpa using congrArg Prod.snd hq'produced
    let wfinal := ws.take (firstIdx.val + 1)
    have hpfx := lexer.stepList_prefix_w ((), q) ws
    simp[h_step_list] at hpfx
    have h_step_wfinal : lexer.stepList ((), q) wfinal =
        some (take wfinal.length step_list) := by
      apply hpfx; simp[wfinal, List.take_prefix]
    have heval_raw := lexer.eval_of_stepList_opaque ((), q) wfinal
    simp[h_step_wfinal] at heval_raw
    obtain ⟨a, b, heval⟩ := heval_raw
    -- Show wfinal.length = firstIdx.val + 1
    have hlt : firstIdx.val + 1 ≤ ws.length :=
      Nat.add_one_le_of_lt (hslen ▸ firstIdx.isLt)
    have h_wfinal_len : wfinal.length = firstIdx.val + 1 := by
      simp[wfinal, List.length_take, Nat.min_eq_left hlt]
    -- Bridge Fin/Nat indexing
    have hprod_nat : step_list[↑firstIdx].2.2.2 = [t] := by
      have : step_list[↑firstIdx] = step_list[firstIdx] := rfl
      rw[this, ←hprod_eq]; exact ht
    -- Show the flatMap output = [t]
    have h_produce_eq : (fun (x : (Unit × LexingState σ) × V ×
        (Unit × LexingState σ) × List (Ch Γ)) => x.2.2.2) = produce := rfl
    have h_output : (take wfinal.length step_list).flatMap
        (fun x => x.2.2.2) = [t] := by
      rw[h_wfinal_len, List.take_succ_eq_append_getElem firstIdx.isLt]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw[h_produce_eq, h_prefix_empty_flat, List.nil_append]
      exact hprod_nat
    rw[h_output] at heval
    -- Now heval : lexer.evalFrom ((), q) wfinal = some ((a, b), [t])
    have h_head_t : T.head hne = t := by
      have hprod_t : produce step_list[firstIdx] = [t] := by
        unfold produce; exact hprod_nat
      have : ∀ (l : List (Ch Γ)) (hl : l ≠ []), l = [t] → l.head hl = t := by
        intros l hl heq; subst heq; rfl
      rw[h_head_eq]; exact this _ hft_ne hprod_t
    simp only [FST.singleProducible, Set.mem_setOf_eq]
    exact ⟨wfinal, ((a, b), [T.head hne]), by rw[h_head_t]; exact heval, by simp[h_head_t]⟩
  | inr h_two =>
    -- Case 2: produced = [char t, eos], EOS case
    obtain ⟨hq_acc, hflat_eos, t, ht⟩ := h_two
    obtain ⟨c, hc_none, hc_start⟩ := hrestart _ hq_acc
    -- produced = step_list[firstIdx].2.2.2
    have hprod_eq : produced = step_list[firstIdx].2.2.2 := by
      simpa using congrArg Prod.snd hq'produced
    -- T.head = ExtChar.char t
    have h_head_t : T.head hne = ExtChar.char t := by
      have hprod_t : produce step_list[firstIdx] = [ExtChar.char t, ExtChar.eos] := by
        unfold produce; rw[←hprod_eq]; exact ht
      rw[h_head_eq]
      have : ∀ (l : List (Ch Γ)) (hl : l ≠ []), l = [ExtChar.char t, ExtChar.eos] → l.head hl = ExtChar.char t := by
        intros l hl heq; subst heq; rfl
      exact this _ hft_ne hprod_t
    -- Get prefix evaluation
    have hpfx := lexer.stepList_prefix_w ((), q) ws
    simp[h_step_list] at hpfx
    have h_pfx_len : (ws.take firstIdx.val).length = firstIdx.val := by
      rw[List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hft_lt_w)
    have h_step_pfx : lexer.stepList ((), q) (ws.take firstIdx.val) =
        some (step_list.take firstIdx.val) := by
      have h := hpfx (ws.take firstIdx.val) (List.take_prefix _ ws)
      rwa[h_pfx_len] at h
    -- Get evalFrom for prefix
    have heval_pfx_raw := lexer.eval_of_stepList_opaque ((), q) (ws.take firstIdx.val)
    rw[h_step_pfx] at heval_pfx_raw
    obtain ⟨q_mid, heval_pfx⟩ := heval_pfx_raw
    -- Prefix output is empty
    have h_pfx_output : (step_list.take firstIdx.val).flatMap
        (fun (x : (Unit × LexingState σ) × V × (Unit × LexingState σ) × List (Ch Γ)) => x.2.2.2) = [] := by
      change (step_list.take firstIdx.val).flatMap produce = []
      exact h_prefix_empty_flat
    rw[h_pfx_output] at heval_pfx
    -- Get intermediate state = step_list[firstIdx].1
    have hfi : firstIdx.val < ws.length := hslen ▸ firstIdx.isLt
    have h_eval_take := lexer.stepList_eval_take ((), q) ws ⟨firstIdx.val, hfi⟩
    simp[h_step_list] at h_eval_take
    -- h_eval_take : ∃ x, evalFrom ... = some (step_list[↑fi].1, x)
    -- heval_pfx   : evalFrom ... = some (q_mid, [])
    -- Therefore q_mid = step_list[firstIdx].1
    obtain ⟨out_take, h_out_take⟩ := h_eval_take
    rw[h_out_take] at heval_pfx
    have hqmid_eq : q_mid = step_list[firstIdx].1 := by
      have := congrArg (fun x => x.map Prod.fst) heval_pfx
      simp at this; exact this.symm
    subst hqmid_eq
    -- q_mid = step_list[firstIdx].1, which is (Unit × LexingState σ)
    -- Its second component is step_list[firstIdx].1.2
    set b_pfx := step_list[firstIdx].1.2
    have hqmid_pair : step_list[firstIdx].1 = ((), b_pfx) := by
      ext1
      · exact Unit.ext _ _
      · rfl
    -- Extract the terminal from the EOS step
    have h_term_eq : t = (spec.term (LexingState.src spec b_pfx)).get
        ((spec.hterm _).mp hq_acc) := by
      have hstep' := hstep
      simp only [BuildLexingFST, Id.run] at hstep'
      rw[hflat_eos] at hstep'
      simp only [hq_acc, dite_true] at hstep'
      -- hstep' : some (start, [char T_term, eos]) = some (q', produced)
      have hinj := Option.some.inj hstep'
      have hprod := congrArg Prod.snd hinj
      simp at hprod
      -- hprod now equates the terminal list with produced
      rw[ht] at hprod
      -- hprod should equate [char T_term, eos] with [char t, eos]
      simp at hprod
      exact hprod.symm
    -- Build restart step
    obtain ⟨q_new, hq_new⟩ := Option.isSome_iff_exists.mp hc_start
    have h_lex_restart : (BuildLexingFST spec).step b_pfx (.char c) =
        some (LexingState.id q_new, [ExtChar.char t]) := by
      simp only [BuildLexingFST, Id.run]
      have h_not_some : ¬(spec.automaton.step (LexingState.src spec b_pfx) c).isSome := by
        show ¬(spec.automaton.step (LexingState.src spec step_list[↑firstIdx].1.2) c).isSome
        simp[hc_none]
      have hq_acc' : LexingState.src spec b_pfx ∈ spec.automaton.accept := hq_acc
      simp only [h_not_some, hq_acc', dite_true]
      rw[h_term_eq, hq_new]; simp
    -- Lift to composed lexer
    have h_detok_restart : lexer.step ((), b_pfx) (vocab.embed (.char c)) =
        some (((), LexingState.id q_new), [ExtChar.char t]) := by
      have hde := detok_eval_embed (V := V) spec b_pfx (.char c)
      simp only [lexer, BuildDetokLexer] at hde ⊢
      rw[hde, h_lex_restart]; simp
    -- Build witness word and combine
    let wfinal := ws.take firstIdx.val ++ [vocab.embed (.char c)]
    -- Extract out_take = [] from heval_pfx
    have h_out_take_nil : out_take = [] := by
      have hinj := Option.some.inj heval_pfx
      have h2 := (Prod.ext_iff.mp hinj).2
      simp at h2; exact h2
    -- Simplify h_out_take with out_take = []
    rw[h_out_take_nil] at h_out_take
    -- h_out_take : lexer.evalFrom ((), q) (take ...) = some (step_list[↑firstIdx].1, [])
    -- step_list[↑firstIdx].1 = ((), b_pfx) via hqmid_pair
    have h_detok_restart' : lexer.step step_list[↑firstIdx].1 (vocab.embed (.char c)) =
        some (((), LexingState.id q_new), [ExtChar.char t]) := by
      show lexer.step step_list[firstIdx].1 _ = _
      rw[hqmid_pair]; exact h_detok_restart
    have h_eval_wfinal : lexer.evalFrom ((), q) wfinal =
        some (((), LexingState.id q_new), [ExtChar.char t]) := by
      simp only [wfinal]
      rw[lexer.evalFrom_append, h_out_take]
      show (lexer.evalFrom step_list[↑firstIdx].1 [vocab.embed (.char c)]).map _ = _
      rw[lexer.evalFrom_singleton, h_detok_restart']
      simp
    simp only [FST.singleProducible, Set.mem_setOf_eq]
    exact ⟨wfinal, (((), LexingState.id q_new), [T.head hne]),
      by rw[h_head_t]; exact h_eval_wfinal, by simp[h_head_t]⟩

omit [BEq V] in
private lemma tailModdedRealizableSequences_subset_singleProducibleHead (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts)
  (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ) :
  let white_term := (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa)
  let lexer := BuildDetokLexer (v := vocab) spec
  ∀ x ∈ lexer.tailModdedRealizableSequences (Unit.unit, q) white_term,
    x ∈ { Ts | Ts = [] ∨
          (∃ t tsfx,
            ¬Ts.contains (ExtChar.char white_term) ∧
            Ts = t :: tsfx ∧ t ∈ lexer.singleProducible (Unit.unit, q)) } := by
  intro white_term lexer x h
  by_cases he : x = []
  · simp [he]
  · change
      x = [] ∨
        ∃ t tsfx,
          ¬x.contains (ExtChar.char white_term) ∧
            x = t :: tsfx ∧ t ∈ lexer.singleProducible (Unit.unit, q)
    apply Or.inr
    simp [FST.tailModdedRealizableSequences] at h
    change
      ∃ v,
        v ∈ lexer.realizableSequences ((), q) ∧
          ¬[ExtChar.char white_term] <+: v ∧ filter (fun x => x != ExtChar.char white_term) v = x at h
    obtain ⟨v, hv_rs, hv_filter⟩ := h
    have hx_no_white : ¬x.contains (ExtChar.char white_term) := by
      rw [←hv_filter.right]
      simp
    have hvne : v ≠ [] := by
      by_contra hve
      simp [hve] at hv_filter
      exact he hv_filter
    have hv_head_not_white : v.head hvne ≠ ExtChar.char white_term := by
      intro hv_head
      apply hv_filter.left
      exists v.tail
      have hv_cons : v = v.head hvne :: v.tail := by simp
      rw [hv_cons, hv_head]
      simp
    have hx_head : x.head he = v.head hvne := by
      cases v with
      | nil => contradiction
      | cons head tail =>
        simp at hv_head_not_white
        have hx_eq : x = head :: filter (fun x => x != ExtChar.char white_term) tail := by
          rw [←hv_filter.right]
          simp [hv_head_not_white]
        subst x
        simp
    refine ⟨x.head he, x.tail, hx_no_white, by simp, ?_⟩
    simp [FST.realizableSequences] at hv_rs
    change ∃ a b w, lexer.evalFrom ((), q) w = some ((a, b), v) at hv_rs
    obtain ⟨u, qf, w, hw⟩ := hv_rs
    have hrestart := WhitespaceAssumption.existsRestartChar spec hempty hwa
    have hv_head_sp :
        v.head hvne ∈ (BuildDetokLexer (v := vocab) spec).singleProducible ((), q) :=
      BuildDetokLexer_singleProducible_of_evalFrom
        (vocab := vocab) spec hempty hrestart q w (u, qf) v
        (by simpa [lexer] using hw) hvne
    simpa [lexer, hx_head] using hv_head_sp

omit [BEq V] in
private lemma singleProducibleHead_subset_tailModdedRealizableSequences (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned)
  (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ) :
  let white_term := (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa)
  let lexer := BuildDetokLexer (v := vocab) spec
  ∀ x, x ∈ { Ts | Ts = [] ∨
          (∃ t tsfx,
            ¬Ts.contains (ExtChar.char white_term) ∧
            Ts = t :: tsfx ∧ t ∈ lexer.singleProducible (Unit.unit, q)) } →
      x ∈ lexer.tailModdedRealizableSequences (Unit.unit, q) white_term := by
  intro white_term lexer x h
  have hlexer : lexer = (BuildDetokenizingFST.compose (BuildLexingFST spec)) := by
    simp[BuildDetokLexer, lexer]
  simp only [Set.mem_setOf] at h
  cases h
  -- empty sequence is trivial
  . rename_i h
    simp[h]
    simp[FST.tailModdedRealizableSequences]
    change
      ∃ v',
        v' ∈ lexer.realizableSequences ((), q) ∧
          ¬[ExtChar.char white_term] <+: v' ∧ filter (fun x => x != ExtChar.char white_term) v' = []
    exists []
    simp[FST.realizableSequences]
    change ∃ a b w, lexer.evalFrom ((), q) w = some ((a, b), [])
    exists ()
    exists q
    exists []
  . rename_i h
    have ⟨t, tsfx, h_no_white, h_eq, h_singleton⟩ := h
    have ⟨w, hw⟩ := h_singleton
    simp[white_term, h_eq] at h_no_white
    -- our sequence will be to compute the first one as is
    -- and then do whitespace, and then do whatever else via previous lemma
    obtain ⟨w', hw'⟩ : ∃ w', (BuildDetokLexer (v := vocab) spec).evalFrom ((), q) w' = some (((), LexingState.id qwhite), [t]) := by
      cases ht : t
      case char ch =>
        obtain ⟨w', hw'⟩ := exchangeNonWhitespace (vocab := vocab) spec hempty hwa q ch (by
          simp[ht] at h_no_white
          rw[eq_comm] at h_no_white
          simp
          constructor
          exact h_no_white.left
          simp[←ht]
          exact h_singleton
        )
        exists w'
      case eos =>
        obtain ⟨w', hw'⟩ := exchangeEOS (vocab := vocab) spec hwa q (by simp[h_singleton, lexer, ←ht])
        exists w'
    simp[FST.tailModdedRealizableSequences]
    change
      ∃ v',
        v' ∈ lexer.realizableSequences ((), q) ∧
          ¬[ExtChar.char white_term] <+: v' ∧ filter (fun x => x != ExtChar.char white_term) v' = x
    -- build rest of tail via previous lemma
    have htail := moddedRealizableSequences_eq_not_contains_whitespace spec hempty hpruned hwa (LexingState.id qwhite) (whitespaceState_singleProducible (vocab := vocab) spec hwa)
    have htsfx : tsfx ∈ (BuildDetokLexer spec (v := vocab)).moddedRealizableSequences ((), LexingState.id qwhite) (ExtChar.char white_term) := by
      rw[←htail]
      change ¬ tsfx.contains (ExtChar.char white_term)
      simpa using h_no_white.right
    simp[FST.moddedRealizableSequences] at htsfx
    change
      ∃ v,
        v ∈ (BuildDetokLexer spec (v := vocab)).realizableSequences ((), LexingState.id qwhite) ∧
          filter (fun x => x != ExtChar.char white_term) v = tsfx at htsfx
    obtain ⟨v, hv⟩ := htsfx
    exists t :: v
    constructor
    . rcases hv with ⟨hv_rs, hv_filter⟩
      change t :: v ∈ lexer.realizableSequences ((), q)
      simp[FST.realizableSequences]
      have hv_rs' : ∃ a b w,
          (BuildDetokLexer spec (v := vocab)).evalFrom ((), LexingState.id qwhite) w = some ((a, b), v) := by
        simpa [FST.realizableSequences] using hv_rs
      obtain ⟨a, qf, wfinal, hwfinal⟩ := hv_rs'
      exists Unit.unit
      exists qf
      exists w' ++ wfinal
      simp[FST.evalFrom_append, lexer, hw']
      simp[hwfinal]
    . constructor
      · simpa [white_term] using h_no_white.left
      · have : (t != ExtChar.char (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa)) = true := by
          simp
          rw[eq_comm] at h_no_white
          exact h_no_white.left
        calc
          filter (fun x => x != ExtChar.char white_term) (t :: v)
              = t :: filter (fun x => x != ExtChar.char white_term) v := by
                  rw [List.filter_cons]
                  have ht_ne : t ≠ ExtChar.char white_term := by
                    intro htw
                    exact h_no_white.left htw.symm
                  simp [ht_ne]
          _ = t :: tsfx := congrArg (List.cons t) hv.right
          _ = x := by simp [h_eq]

omit [BEq V] in
lemma tailModdedRealizableSequences_eq_singleProducibleHead (spec: LexerSpec α Γ σ)
  (hempty : [] ∉ spec.automaton.accepts) (hpruned: spec.automaton.pruned)
  (hwa: WhitespaceAssumption spec tnonwhite twhite qnonwhite qwhite) (q: LexingState σ) :
  let white_term := (whitespaceTerminal spec tnonwhite twhite qnonwhite qwhite hwa)
  let lexer := BuildDetokLexer (v := vocab) spec
  lexer.tailModdedRealizableSequences (Unit.unit, q) white_term =
    { Ts | Ts = [] ∨
            (∃ t tsfx,
              ¬Ts.contains (ExtChar.char white_term) ∧
              Ts = t :: tsfx ∧ t ∈ lexer.singleProducible (Unit.unit, q)) } := by
  ext x
  apply Iff.intro
  . intro h
    exact tailModdedRealizableSequences_subset_singleProducibleHead spec hempty hwa q x h
  . intro h
    exact singleProducibleHead_subset_tailModdedRealizableSequences spec hempty hpruned hwa q x h

end SingleProducibleHead

end Detokenizing
