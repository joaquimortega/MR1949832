# Vendored library

This directory is a copy of part of the library `OrtegaCerdaSeip` from the companion formalization of
J. Ortega-Cerdà and K. Seip, *Multipliers for entire functions and an interpolation problem of Beurling*,
J. Funct. Anal. 162 (1999): https://github.com/joaquimortega/MR1682065, commit
`05e3ac2ca83f8862636e1dd002467ad9add83396`
(re-copied after the lint fixes of that repository; first vendored at `3f16484`).

Only the import closure of `OrtegaCerdaSeip/Lemma4/Main.lean` is copied. It proves `OCS.theoremOCS : OCS.TheoremOCS`
(Lemma 4 of [OCS99] in the form quoted on p. 375 of the article, with `limsup = 0`), without `sorry`. The 18 files are:

- `Defs.lean`
- `Foundations/Basic.lean`, `Foundations/HoloKernel.lean`, `Foundations/LocalEstimates.lean`, `Foundations/Polar.lean`,
  `Foundations/Pompeiu.lean`, `Foundations/Weyl.lean`, `Foundations/Wirtinger.lean`
- `Carleson/Basic.lean`, `Carleson/Poisson.lean`
- `Jones/Basic.lean`, `Jones/Estimates.lean`, `Jones/LayerCake.lean`, `Jones/Weak.lean`
- `Lemma4/Kernel.lean`, `Lemma4/Main.lean`, `Lemma4/Upper.lean`, `Lemma4/Weak.lean`

The root file `OrtegaCerdaSeip.lean` is not the upstream one: it imports only `OrtegaCerdaSeip.Lemma4.Main`.

It is vendored so that this repository builds with Mathlib as its only dependency. Do not edit it here.
To update it, copy the files again from that repository.
Only `OrtegaCerdaMultipliers/TheoremOCSProof.lean` imports it.
