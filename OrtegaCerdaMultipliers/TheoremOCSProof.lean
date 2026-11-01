import OrtegaCerdaMultipliers.Defs
import OrtegaCerdaSeip.Lemma4.Main

/-!
# The Ortega-Cerdà–Seip theorem [OCS99], proved

`TheoremOCS` (`Defs.lean`) is Lemma 4 of Ortega-Cerdà–Seip (J. Funct. Anal. 162, 1999) in the
form quoted on p. 375, with `limsup = 0` (NOTEBOOK N-07).  It is proved, as `OCS.theoremOCS`, in
the companion formalization github.com/joaquimortega/MR1682065 (library `OrtegaCerdaSeip`), whose
definitions `OCS.TheoremOCS`, `OCS.IsWeakDbarSolMeasure` and `OCS.dbar` are verbatim copies of
the ones here.  The needed part of that library is vendored in `OrtegaCerdaSeip/` (see
`OrtegaCerdaSeip/VENDORED.md`); this is the only file that imports it.
-/

namespace OC

/-- **[OCS99, Lemma 4]**, as quoted on p. 375 (with `limsup = 0`), holds.  Proved in the
companion project MR1682065 as `OCS.theoremOCS` (its NOTEBOOK N-08 for the `limsup = 0` clause);
`OCS.TheoremOCS` and `OC.TheoremOCS` agree by definitional unfolding. -/
theorem theoremOCS_holds : TheoremOCS := OCS.theoremOCS

end OC
