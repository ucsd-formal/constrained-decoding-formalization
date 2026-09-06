import ConstrainedDecodingFormalization.Char
import ConstrainedDecodingFormalization.PDA

/-!
# EOS-augmented parser

`ParserWithEOS` adapts a parser over grammar terminals to the EOS-extended
terminal stream emitted by the detokenizing lexer. Plain terminals are forwarded
to the original parser. A terminal EOS moves an accepting original parser state
to the distinguished EOS state, which then absorbs all remaining input.
-/

universe u v w
variable {Γ : Type u} {π : Type v} {σp : Type w}
variable [FinEnum Γ] [FinEnum π] [FinEnum σp]
variable [DecidableEq π]

/-- Extend a token PDA with EOS so it can be composed with lexer outputs over
`Ch Γ`. -/
def ParserWithEOS [DecidableEq σp] (p : PDA Γ π σp) : PDA (Ch Γ) π (Ch σp) :=
  let start := ExtChar.char p.start
  let accept := ExtChar.eos
  let step := fun s c =>
    match s, c with
    | ExtChar.char s, ExtChar.char c =>
      (p.step s c).image (fun (spt, spr, s) => (spt, spr, ExtChar.char s))
    | ExtChar.char s, ExtChar.eos =>
      if s ∈ p.accept then
        { ([], [], accept) }
      else
        ∅
    | ExtChar.eos, _ => {([], [], .eos)}

  ⟨start, step, {accept}⟩
