import OrtegaCerdaMultipliers.Multiplier.Theorem4
import OrtegaCerdaMultipliers.SeveralMultipliers
import OrtegaCerdaMultipliers.Theorem2
import OrtegaCerdaMultipliers.Theorem1
import OrtegaCerdaMultipliers.Theorem5
import OrtegaCerdaMultipliers.Theorem3

/-!
# Main results

Re-exports the modules containing the main theorems of `comparator/statements.lean`:

* `theorem4_disc`, `theorem4_plane` (M08, `Multiplier/Theorem4.lean`);
* `prop2_disc`, `prop2_plane` (M09, `SeveralMultipliers.lean`);
* `theorem2`, `theorem2_uniform`, `theorem2_printed` (M11, `Theorem2.lean`);
* `theorem1`, `theorem1_christ`, `prop1` (M12, `Theorem1.lean`);
* `theorem5` (M13, `Theorem5.lean`);
* `theorem3_weighted` (M14, `Theorem3.lean`), the corrected Theorem 3, unconditional via
  `theoremOCS_holds` (`TheoremOCSProof.lean`, proved in MR1682065, vendored in `OrtegaCerdaSeip/`);
  `theorem3_weighted_of_theoremOCS` is the conditional form (the paper's route);
* `theorem3_printed_false` (M14): the printed `theorem3` is false and is not declared.
-/
