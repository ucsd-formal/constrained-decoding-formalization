# Phase 2: singleProducible Nonemptiness — Detailed Subplan

**Parent plan**: COMPLETENESS_PROOF_PLAN.md, Phase 2 (Task 4)
**Goal**: Given an FST run from state `q` producing output `T ≠ []`, show
`T.head ∈ (BuildDetokLexer spec).singleProducible q` (or at minimum
`singleProducible q ≠ ∅`).

---

## Scope

This phase covers Task 4 from the execution table — the **critical path
bottleneck** that gates Phases 3–5.

| Task | Lemma | Est. |
|------|-------|------|
| 4 | `BuildDetokLexer_singleProducible_of_evalFrom` | 3–4h |

---

## Key Discovery: Existing Proof Pattern

**The proof pattern already exists** in `detok_rs_pfx_forward`
(Lexing.lean:1822–2221). That lemma proves the same core fact — given
`lexer.evalFrom ((), q) w = some (qf, v)` with `v ≠ []`, it shows
`v.head ∈ lexer.singleProducible ((), q)` — but it's entangled with
whitespace-filtering logic (`tailModdedRealizableSequences`,
`whitespace_assumption`, `rem_ws`, etc.).

**The strategy is to extract and generalize the clean core** of that proof
into a standalone lemma, without the whitespace machinery.

---

## Existing Infrastructure

| Lemma/Def | File | Line | Role |
|-----------|------|------|------|
| `FST.singleProducible` | Producible.lean | 30 | `{ t \| ∃ w r ∈ evalFrom q w, r.2 = [t] }` |
| `mem_singleProducible_iff_exists_evalFrom_singleton` | GCD.lean | 568 | Unfold to `∃ ts q', evalFrom q ts = some (q', [T])` |
| `detokenize_singleton` | Lexing.lean | 1071 | Replace any token sequence with singleton-character tokens preserving evalFrom |
| `detok_eval_embed` | Lexing.lean | 1135 | `(BuildDetokLexer spec).step ((), q) (embed t) = map ... ((BuildLexingFST spec).step q t)` |
| `LexingFst_smallStep` | Lexing.lean | 940 | Output of one BuildLexingFST step is `[]`, `[t]`, or `[t, .eos]` (and only the last for EOS at accepting state) |
| `detokenizer_comp_step` | Lexing.lean | 1027 | Composed step = lexer evalFrom on flattened characters |
| `FST.stepList_of_eval` | Automata.lean | — | Decompose evalFrom into step list |
| `FST.eval_of_stepList` | Automata.lean | — | Reconstruct evalFrom from step list |
| `exchange_basis` | Lexing.lean | 1157 | Reverse direction: from `singleProducible`, decompose into prefix of empty + single emission |
| `detok_rs_pfx_forward` | Lexing.lean | 1822 | Contains the proof we need, but mixed with whitespace logic |
| `Vocabulary.fe` | Vocabulary.lean | 23 | `flatten (embed a) = [a]` — singleton token axiom |
| `Vocabulary.empty` | Vocabulary.lean | 24 | `flatten b ≠ []` — no empty tokens |

---

## Proof Architecture

### Target Statement

```lean
theorem BuildDetokLexer_singleProducible_of_evalFrom
    [BEq (Ch α)] [LawfulBEq (Ch α)]
    [vocab : Vocabulary (Ch α) V] [BEq V]
    (spec : LexerSpec α Γ σ)
    (q : LexingState σ) (w : List V) (qf : Unit × LexingState σ)
    (T : List (Ch Γ))
    (hrun : (BuildDetokLexer (v := vocab) spec).evalFrom ((), q) w = some (qf, T))
    (hne : T ≠ []) :
    T.head hne ∈ (BuildDetokLexer (v := vocab) spec).singleProducible ((), q)
```

**File placement**: `Lexing.lean`, near line 1157 (after `exchange_basis`,
which proves the reverse direction).

### Proof Outline (extracted from `detok_rs_pfx_forward`)

The proof follows 5 stages:

#### Stage 1: Reduce to singleton tokens

```
detokenize_singleton (BuildLexingFST spec) q w
```
yields `ws` with `evalFrom ((), q) ws = evalFrom ((), q) w` and every
token in `ws` has `flatten t = [t₀]` (singleton character). This lets us
reason character-by-character.

#### Stage 2: Decompose into step list

```
lexer.stepList_of_eval ((), q) ws
```
yields `step_list` with `flatMap produce step_list = T` and each element
records `(state_in, token, state_out, output_fragment)`.

#### Stage 3: Find first non-empty emission

Since `T ≠ []` and `T = flatMap produce step_list`, there exists a first
index `k` where `produce step_list[k] ≠ []`. All earlier entries produce
`[]`.

**Helper needed**: `find_first_nonempty` or equivalent index-finding lemma.
Check if it already exists (used in `detok_rs_pfx_forward` at line 1902).

#### Stage 4: Classify the emission via `LexingFst_smallStep`

Each singleton-token step of `BuildDetokLexer` reduces (via
`detokenizer_comp_step` + singleton flatten) to a single `BuildLexingFST`
step. By `LexingFst_smallStep`, the output is one of:
- `[]` — extending current lexeme (ruled out: this is the first nonempty)
- `[t]` — lexeme completion, one terminal emitted
- `[t, .eos]` — lexeme completion + EOS (only when input is `.eos` and
  state is accepting)

**Case 1** (`[t]`): The prefix `ws.take (k+1)` is a token sequence that
produces exactly `[t]` from `((), q)`. This directly witnesses
`t ∈ singleProducible ((), q)`. Since the empty prefix produces `[]` and
the k-th step produces `[t]`, the total is `[] ++ ... ++ [] ++ [t] = [t]`.

**Case 2** (`[t, .eos]`): The k-th step alone produces 2 symbols, so
`ws.take (k+1)` produces `[t, .eos]`, not a singleton. Need alternative
construction.

#### Stage 5: Handle the EOS case

When the output is `[t, .eos]`, the lexer is at an accepting state `qacc`
and processes `.eos`. We need to produce just `[t]` instead.

**Construction**: Replace the `.eos` token at position `k` with any
character token that triggers lexeme completion from `qacc`. Specifically:

The existing proof (line 2066–2220) uses `embed twhite` (the whitespace
character) because `whitespace_assumption` guarantees `step qacc twhite`
triggers completion. But this requires the whitespace assumption.

**Without whitespace assumption**, we need a different approach:
- **Option A**: Add a mild `LexerSpec` hypothesis that every accepting
  state has some character triggering lexeme completion. This is
  `∀ q ∈ accept, ∃ c, step q₀ c ≠ none` — always true for practical
  lexers since `q₀` is the start and the automaton is nonempty.
  Actually, what we need is weaker: `∃ c, step q₀ c ≠ none` (the
  automaton accepts at least one character from start). Then from `qacc`,
  processing `char c` triggers `[char T]` emission (completing the
  current lexeme) and restarts on `c`.
- **Option B**: Use `[] ∉ spec.automaton.accepts` (already used in
  existing proofs, e.g., `PartialLex_to_LexingFST` at line 850). This
  means the start state is not accepting. Combined with the automaton
  being non-empty (there must be at least one terminal by `term_surj`),
  we can find a character that steps from start.
- **Option C**: Add `singleProducible q ≠ ∅` as a hypothesis for this
  edge case and move on. Flag as a minor gap.

**Recommended**: Option B. `[] ∉ spec.automaton.accepts` is already a
standard assumption in the codebase. `term_surj` guarantees `∃ t, ∃ s,
term s = some t`, so `s ∈ accept` and by `pruned` there's a path from
start to `s`, meaning some character steps from start. This yields a
`char c` that we can substitute for the `.eos` to get a 1-symbol output.

---

## Sub-lemmas

### Sub-lemma D.1: `evalFrom_stepList_prefix_output`

Given a step list where the first `k` entries produce `[]` and entry `k`
produces `out`, show `lexer.evalFrom ((), q) (ws.take (k+1)) = some (q', out)`.

This combines:
- `stepList_prefix_w`: restricting the step list to a prefix
- `eval_of_stepList_opaque`: converting step list back to evalFrom
- The empty-prefix flatMap fact

**Already done** in the existing proof (lines 2022–2065). Just needs
extraction.

### Sub-lemma D.2: `LexingFST_step_accepting_char_produces_one`

When the lexer is at an accepting state `qacc` and processes a character
`c` where `step q₀ c` is defined, the output is `[char T]` (exactly one
symbol).

```lean
lemma LexingFST_step_accepting_char_produces_one (spec : LexerSpec α Γ σ)
    (q : LexingState σ) (c : α) (q₀_steps : (spec.automaton.step spec.automaton.start c).isSome)
    (hacc : LexingState.src spec q ∈ spec.automaton.accept) :
    ∃ q' T, (BuildLexingFST spec).step q (.char c) = some (q', [.char T])
```

**Proof**: Unfold `BuildLexingFST` step. Since `src q ∈ accept`, the
"extending" branch fails for `c` that doesn't extend, but the
"completing + restarting" branch fires. The output is `[.char T]` where
`T = term qacc`.

Wait — the step function first checks if `A.step qorg c` is defined
(extending). If it IS, the step extends with `[]` output. We need `c`
such that `A.step qorg c = none` (can't extend from the accepting state)
AND `A.step q₀ c ≠ none` (can restart). This is a stronger condition.

**Revised**: We need a character `c` where:
1. `spec.automaton.step (src q) c = none` — can't extend current lexeme
2. `spec.automaton.step spec.automaton.start c ≠ none` — can start new lexeme

If such `c` exists, the BuildLexingFST step produces `[.char T]`.

**Existence of such c**: By `term_surj`, there exists a terminal, so
there's an accepting state, so by `pruned` there's a path from start.
The first character of that path gives (2). For (1), we need the
accepting state to NOT be able to step on that character. This is NOT
guaranteed in general — the accepting state might also accept that char.

**Alternative**: Use ANY character. If `A.step qorg c` IS defined, the
step produces `[]` (extending, not completing). So we recurse: from the
new state `A.step qorg c`, try again. Since the automaton is finite, we
either hit an accepting state where we can't extend (producing a
terminal), or we loop. But in a pruned DFA, every reachable state has a
path to acceptance, so we eventually reach a state that triggers emission.

**This means**: Rather than a single step, we need a **multi-step**
argument. From accepting state `qacc`, there exists a character sequence
`cs` (possibly of length > 1) such that `BuildLexingFST.evalFrom qacc cs`
produces exactly `[.char T, ...]` with the first symbol being `[.char T]`.
Then the corresponding singleton-token sequence produces that output.

This is getting complex. Let me reconsider.

### Simpler Alternative for EOS Case

**Key realization**: The EOS case only arises when the FIRST emission
from `q` is via `.eos`. But the viability condition for the completeness
proof gives us `parser.evalFull (terms ++ S ++ T) ≠ ∅`, which requires
`.eos` in the output. If `.eos` appears in the first-step output `S`,
that's fine. If `.eos` appears in `T`, then `T` must contain `.eos`.

For the singleProducible witness, we only need `T.head ∈ singleProducible
q₁`. If `T.head = .eos`, we need `.eos ∈ singleProducible q₁`. By
definition, this means there's a token sequence from `q₁` producing
exactly `[.eos]`. For `BuildDetokLexer`, this means the lexer is at
start state and processes `embed eos`, giving `[.eos]`. So
`.eos ∈ singleProducible ((), LexingState.start)` always.

But `T.head` might be `.char T_term`, produced by the 2-symbol emission
`[.char T_term, .eos]`. In that case, we need `.char T_term ∈
singleProducible q₁`. This is the hard case.

**Pragmatic approach**: Prove the `[t]` (1-symbol) case cleanly. For the
`[t, .eos]` (2-symbol) case, add `[] ∉ spec.automaton.accepts` as
hypothesis (standard) and require **one of**:
- a) A character `c` with `A.step (src q) c = none ∧ A.step q₀ c ≠ none`
- b) The automaton is `pruned` and non-trivial

If we go with (b) and `pruned`, we can use the DFS-based
`computeSingleProducible` to constructively find a witness. But that's
an executable argument, not a clean proof.

**Simplest correct approach**: Add `[] ∉ spec.automaton.accepts` +
`spec.automaton.pruned` as hypotheses (both already standard in the
codebase). Then adapt the EOS case from `detok_rs_pfx_forward` (lines
2066–2220) which already handles it.

---

## Implementation Plan

### Step 1: Extract helper lemmas (~30 min)

Identify which helpers from `detok_rs_pfx_forward` are reusable:

- `find_first_nonempty` — already exists (used at line 1902). Verify it's
  accessible (not private).
- `empty_prefix_all_empty` — already exists (line 1917). Same check.
- `first_eq_head_of_first_nonempty` — already exists (line 1924). Same.
- `flatMap_prefix_suffix` — already exists (line 1143). Already non-private.

If any are private, either make them non-private or duplicate the minimal
needed parts.

### Step 2: Prove the 1-symbol case (~1h)

```lean
private lemma singleProducible_of_evalFrom_one_symbol_step
    [vocab : Vocabulary (Ch α) V] [BEq V]
    (spec : LexerSpec α Γ σ)
    (q : LexingState σ) (ws : List V)
    (h_ws_singleton : ∀ t ∈ ws, ∃ t₀, vocab.flatten t = [t₀])
    (step_list : List _)
    (h_step_list : stepList ... = some step_list ∧ flatMap produce step_list = T)
    (k : Fin step_list.length)
    (h_prefix_empty : ∀ j < k, produce step_list[j] = [])
    (h_one : ∃ t, produce step_list[k] = [t]) :
    T.head hne ∈ (BuildDetokLexer spec).singleProducible ((), q)
```

Proof: `ws.take (k+1)` witnesses `T.head` as singleProducible. The
evalFrom on this prefix produces `[] ++ ... ++ [] ++ [t] = [t]`. By
`first_eq_head_of_first_nonempty`, `t = T.head`.

### Step 3: Prove the 2-symbol (EOS) case (~2h)

This is the harder case. Adapt the approach from `detok_rs_pfx_forward`
lines 2066–2220:

1. The lexer is at accepting state `qacc = src q'` where `q'` is the
   state before the EOS step.
2. Replace `.eos` with a character token that triggers completion.
3. Under `[] ∉ accepts` (start is non-accepting) and `pruned`:
   - Need `A.step (src q') c = none` for some `c` with
     `A.step q₀ c ≠ none`.
   - The existing proof uses `twhite` from whitespace_assumption.
   - Without that, need to find such `c` from `pruned` + `term_surj`.

**Decision point**: Either:
- (a) Add `whitespace_assumption` as hypothesis (matches existing code)
- (b) Add `[] ∉ accepts` + `pruned` and find `c` constructively
- (c) Add a direct hypothesis `∀ q, src q ∈ accept → singleProducible q ≠ ∅`
- (d) Sorry this case and flag it

**Recommendation**: Start with (c) or (d). The 1-symbol case covers the
common path. The EOS case is rare and the proof is 150+ lines in the
existing code. We can add a clean hypothesis and prove it separately
later.

### Step 4: Combine into main theorem (~30 min)

```lean
theorem BuildDetokLexer_singleProducible_of_evalFrom
    [BEq (Ch α)] [LawfulBEq (Ch α)]
    [vocab : Vocabulary (Ch α) V] [BEq V]
    (spec : LexerSpec α Γ σ)
    (hempty : [] ∉ spec.automaton.accepts)  -- standard
    (q : LexingState σ) (w : List V) (qf : Unit × LexingState σ)
    (T : List (Ch Γ))
    (hrun : (BuildDetokLexer spec).evalFrom ((), q) w = some (qf, T))
    (hne : T ≠ []) :
    T.head hne ∈ (BuildDetokLexer spec).singleProducible ((), q)
```

Proof:
1. `detokenize_singleton` → get `ws` with singleton tokens
2. `stepList_of_eval` → get step list
3. Find first nonempty emission at index `k`
4. `LexingFst_smallStep` → case split on output length
5. Case `[t]`: Step 2 handles it
6. Case `[t, .eos]`: Step 3 handles it (or sorry + hypothesis)

### Step 5: Connect to completeness (~15 min)

The completeness proof needs: given `evalFrom q₁ suffix = some (qa', T)`
with `T ≠ []`, produce a witness for `singleProducible q₁`. The main
theorem gives `T.head ∈ singleProducible q₁`, which is exactly the
witness `d = S ++ [T.head]` needed for the realizable sequence in Phase 4.

---

## Risks and Mitigations

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| EOS case needs 150+ lines of whitespace-entangled proof | High | Defer with hypothesis or sorry; focus on 1-symbol case first |
| `find_first_nonempty` and friends are private | Medium | Check accessibility; duplicate if needed |
| Step-list indexing causes dependent-type headaches | Medium | Follow the existing proof's pattern exactly |
| `LexingFst_smallStep` doesn't give a clean disjunction | Low | It does — output is `[]`, `[t]`, or `[t, .eos]` |
| `detokenize_singleton` output needs additional properties | Low | It already guarantees `∀ t ∈ ws, ∃ t₀, flatten t = [t₀]` |

---

## Execution Order

| # | Sub-task | Est. | Depends on |
|---|----------|------|-----------|
| 1 | Check accessibility of helpers (`find_first_nonempty`, etc.) | 15m | — |
| 2 | State main theorem with appropriate hypotheses | 15m | — |
| 3 | Prove Stage 1–3 (reduce to singleton, decompose, find first emission) | 45m | 1 |
| 4 | Prove 1-symbol case (Stage 4, Case 1) | 1h | 3 |
| 5 | Handle EOS case (Stage 4, Case 2) — or defer | 1–2h | 3 |
| 6 | Combine and verify compilation | 30m | 4, 5 |

**Total**: 3–5h depending on EOS case approach.

---

## What's NOT in scope

- Phase 3 (`T = []` edge case) — separate analysis
- Deleting `fst_run_produces_realizable` — Phase 4
- The completeness assembly — Phase 4
- `GCDChecker_sound/complete` — Phase 5
