import ConstrainedDecodingFormalization.GCDStepProofs
import ConstrainedDecodingFormalization.GCDCheckerLanguage
import ConstrainedDecodingFormalization.GCDProductivity

/-!
# Grammar-constrained decoding proofs

Compatibility import for the GCD proof development. The proof stack is split
into:

* `GCDStepProofs`: preprocessing characterizations plus step-level soundness,
  completeness, and EOS completeness;
* `GCDCheckerLanguage`: the bridge from step-level proofs to
  `checkerLanguage = GCDLanguage`;
* `GCDProductivity`: productivity, path independence, and the final
  `checkerCorrect` theorem.
-/
