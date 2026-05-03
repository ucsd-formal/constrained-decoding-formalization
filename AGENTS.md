# Lean Grammer Constrained Decoding

This repository is a formalization of grammer constrained decoding, a way to mask LLM output such that it satisfies a certain Context Free Grammar.

The main assumptions are basically that there's a universal separator in the form of whitespace for the lexer, and that the parser "ignores" whitespace in the sense that reading a whitespace token will keep it at the current state. This is somewhat formalized for the lexer in Lexing.lean

def ComputeValidTokenMask (P : PDA Γ π σp) (itst : List Γ → σa → List α)

in GrammatConstrainedDecoding.lean is the actual mask function that we have to prove is correct

The current status is that