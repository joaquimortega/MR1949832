# Formalization of Ortega-Cerdà, *Multipliers and weighted ∂̄-estimates* (2002)

A Lean 4 / Mathlib formalization of

> J. Ortega-Cerdà, *Multipliers and weighted ∂̄-estimates*, Rev. Mat. Iberoamericana **18** (2002), 355–377. [doi:10.4171/RMI/322](https://doi.org/10.4171/RMI/322), arXiv:math/9912139.

Page references ("p. 363") are to the journal pagination. The printed PDF used as the reference during the work (`literature/10.4171-rmi-322.pdf`) is not included in the repository.

## What the paper proves

The paper studies the equation `∂̄u = f` with weights `e^{-φ}`, where `φ` is subharmonic and its Laplacian `μ = Δφ` is only assumed to be a (locally) doubling measure. Such a measure defines a natural local scale `ρ(z)`, the radius of the disc around `z` of `μ`-mass one.

**The multiplier theorem (Theorem 4).** For such a weight, in the plane or in the unit disc, there is a holomorphic function `h` that mimics `e^{φ}`:
- its zero set `Λ` is separated at the scale `ρ`;
- `|h(z)| e^{-φ(z)}` is comparable to `d(z,Λ)/ρ(z)`, up to a fixed power, so `|h| ≃ e^{φ}` away from small discs around the zeros.

Proposition 2 provides finitely many such multipliers whose exceptional discs have no common point. Dividing by them turns weighted problems into unweighted ones. The paper obtains three applications.

**Christ's theorem (Theorem 1).** If `Δφ` is doubling, `∂̄u = f` has a solution with `‖u e^{-φ}‖_p ≲ ‖f e^{-φ}‖_p` for all `1 ≤ p ≤ ∞`. The solution is given by an explicit kernel with off-diagonal decay (Proposition 1).

**The disc analogue (Theorem 2).** The estimates hold in the measure `dm/(1−|z|²)`. In particular `sup |u| e^{-φ} ≲ sup |f(ζ)| (1−|ζ|) e^{-φ(ζ)}`.

**Weights whose Laplacian lives on the real line.**
- Theorem 5 constructs multipliers with real zeros.
- Theorem 3 solves `∂̄u = μ` for a measure `μ` with `e^{-φ}|μ|` a two-sided Carleson measure, with a pointwise bound for `u` on the real line.
- Theorem 3 extends Lemma 4 of Ortega-Cerdà–Seip (J. Funct. Anal. 1999), whose case is `φ = ε|Im z|`, and uses that lemma in its proof.

## Main results

All fourteen main results are proved without `sorry`, depend only on `propext`, `Classical.choice` and `Quot.sound`, and are accepted by comparator against `OCChallenge.lean` (2026-11-02). All of them are unconditional except `OC.theorem3_weighted_of_theoremOCS`, the paper's conditional route to Theorem 3.


| Paper | Lean |
|---|---|
| Theorem 4: multipliers in `𝔻` and `ℂ` | `OC.theorem4_disc`, `OC.theorem4_plane` |
| Proposition 2: multipliers with disjoint exceptional sets | `OC.prop2_disc`, `OC.prop2_plane` |
| Theorem 2: `L^p` and sup estimates for `∂̄` in `𝔻` | `OC.theorem2` (one solution, all `p ∈ [1,∞]`), `OC.theorem2_uniform`, `OC.theorem2_printed` |
| Theorem 1: Christ's theorem, locally doubling version | `OC.theorem1`, `OC.theorem1_christ` |
| Proposition 1: kernel decay | `OC.prop1` (upper bound; the printed `≃` is false) |
| Theorem 5: multipliers with real zeros | `OC.theorem5` |
| Theorem 3: corrected (weighted integral) | `OC.theorem3_weighted` (unconditional); `OC.theorem3_weighted_of_theoremOCS : TheoremOCS → …` (the paper's route, from the quoted [OCS99] theorem) |
| Theorem 3 as printed is false | `OC.theorem3_printed_false` (a Lean proof; it does not use `TheoremOCS`) |

The statements are in `comparator/statements.lean` and the definitions they use in `OrtegaCerdaMultipliers/Defs.lean`. `OCChallenge.lean` combines both into a self-contained file for [comparator](https://github.com/leanprover/comparator); see `comparator/README.md`.

**Weights.** A weight is a pair `(φ, μ)`: `φ` is continuous and `Δφ = μ` in the sense of distributions. Mathlib has no Riesz-measure theory. For the paper's weights (subharmonic, with locally doubling Laplacian) this class coincides with the paper's.

**Corrections to the paper.** Theorem 3 as printed is false. The formalized version puts the weight `e^{-φ}` inside the integral. The [OCS99] theorem it relies on (`OC.TheoremOCS`, as quoted on p. 375, with `limsup = 0`) is proved in the companion project MR1682065, so Theorem 3 is unconditional (`OC.theoremOCS_holds`). All errata, gaps and simplifications are in `NOTEBOOK.md`.

## Layout

| Path | Content |
|---|---|
| `blueprint/` | One Markdown file per module, with detailed proofs, Lean statements and dependencies. Start with `blueprint/README.md`; `blueprint/IMPORTS.md` has the module graph. |
| `reviews/` | The independent referee reports from the blueprint review round. |
| `OrtegaCerdaMultipliers/` | The Lean formalization. |
| `OrtegaCerdaSeip/` | Vendored, do not edit: the part of the MR1682065 library that proves [OCS99] Lemma 4 (`OCS.theoremOCS`); see `OrtegaCerdaSeip/VENDORED.md`. Only `OrtegaCerdaMultipliers/TheoremOCSProof.lean` imports it. |
| `NOTEBOOK.md` | Errata (N-xx) and implementation notes (I-xx). |
| `formalization.yaml` | Metadata in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format. |
| `scripts/` | `make_challenge.py`, `check_statements.py` (the statement freeze-check), `new_worktree.sh`. |

## Companion projects

- **BOC.** The companion formalization of Berndtsson–Ortega-Cerdà (1995), [joaquimortega/MR1340337](https://github.com/joaquimortega/MR1340337), uses `OC.theorem2_uniform` to prove its Theorem 6 without the external Theorem G. This project does not depend on BOC. Its foundation files (∂̄ calculus, Cauchy transform, Weyl's lemma, disc geometry) are copied from BOC under namespace `OC`.
- **[OCS99].** The theorem used in Theorem 3 (`TheoremOCS`) is Lemma 4 of Ortega-Cerdà–Seip (1999), with the decay `limsup = 0` that the quotation on p. 375 states and the proof gives. It is proved in the companion formalization [joaquimortega/MR1682065](https://github.com/joaquimortega/MR1682065) as `OCS.theoremOCS`. A sorry-free subset of that library (the 18 files that `OCS.theoremOCS` needs, commit `05e3ac2`) is vendored here in `OrtegaCerdaSeip/`, so this repository still depends only on Mathlib; `OC.theoremOCS_holds : OC.TheoremOCS := OCS.theoremOCS` makes Theorem 3 unconditional.

## Building

```sh
lake exe cache get   # once
lake build           # the default target, OrtegaCerdaMultipliers (it builds the needed part of OrtegaCerdaSeip)
lake build OrtegaCerdaMultipliers OrtegaCerdaSeip OCChallenge OCSolution   # every library
```

Two libraries: `OrtegaCerdaMultipliers` (this project) and `OrtegaCerdaSeip` (vendored from MR1682065, see above); `OCChallenge` and `OCSolution` are the comparator files.

Toolchain: Lean v4.35.0, Mathlib v4.35.0.

## License

Apache License 2.0 (see `LICENSE`).
