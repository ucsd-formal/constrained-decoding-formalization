import ConstrainedDecodingFormalization.Lexing.Base
import ConstrainedDecodingFormalization.Lexing.Correctness
import ConstrainedDecodingFormalization.Lexing.Detokenizing
import ConstrainedDecodingFormalization.Lexing.Whitespace

/-!
# Lexing

Compatibility import for the lexing development. The implementation is split
across:

* `Lexing.Base`: lexer specs, partial lexing, and lexing FST construction;
* `Lexing.Correctness`: character-level lexing/FST equivalence proofs;
* `Lexing.Detokenizing`: token flattening FSTs and their composition with the
  lexer FST;
* `Lexing.Whitespace`: whitespace exchange and singleton-producibility lemmas.
-/
