# Formalization of Ortega-Cerdà, *Multipliers and weighted ∂̄-estimates* (2002)

A Lean 4 / Mathlib formalization of

> J. Ortega-Cerdà, *Multipliers and weighted ∂̄-estimates*, Rev. Mat. Iberoamericana **18** (2002), 355–377. [doi:10.4171/RMI/322](https://doi.org/10.4171/RMI/322), arXiv:math/9912139.

Page references ("p. 363") are to the journal pagination. The printed PDF used as the reference during the work (`literature/10.4171-rmi-322.pdf`) is not included in the repository.

## Main results

All thirteen main results are proved without `sorry`, depend only on `propext`, `Classical.choice` and `Quot.sound`, and are accepted by comparator against `OCChallenge.lean` (2026-11-01).


| Paper | Lean |
|---|---|
| Theorem 4: multipliers in `𝔻` and `ℂ` | `OC.theorem4_disc`, `OC.theorem4_plane` |
| Proposition 2: multipliers with disjoint exceptional sets | `OC.prop2_disc`, `OC.prop2_plane` |
| Theorem 2: `L^p` and sup estimates for `∂̄` in `𝔻` | `OC.theorem2` (one solution, all `p ∈ [1,∞]`), `OC.theorem2_uniform`, `OC.theorem2_printed` |
| Theorem 1: Christ's theorem, locally doubling version | `OC.theorem1`, `OC.theorem1_christ` |
| Proposition 1: kernel decay | `OC.prop1` (upper bound; the printed `≃` is false) |
| Theorem 5: multipliers with real zeros | `OC.theorem5` |
| Theorem 3: corrected, assuming the quoted [OCS99] theorem | `OC.theorem3_weighted : TheoremOCS → …` |
| Theorem 3 as printed is false | `OC.theorem3_printed_false` (a Lean proof; it does not use `TheoremOCS`) |

The statements are in `comparator/statements.lean` and the definitions they use in `OrtegaCerdaMultipliers/Defs.lean`. `OCChallenge.lean` combines both into a self-contained file for [comparator](https://github.com/leanprover/comparator); see `comparator/README.md`.

**Weights.** A weight is a pair `(φ, μ)`: `φ` is continuous and `Δφ = μ` in the sense of distributions. Mathlib has no Riesz-measure theory. For the paper's weights (subharmonic, with locally doubling Laplacian) this class coincides with the paper's.

**Corrections to the paper.** Theorem 3 as printed is false. Two independent referee agents found this, and it is now proved in Lean (`OC.theorem3_printed_false`). The formalized version puts the weight `e^{-φ}` inside the integral. All errata, gaps and simplifications are in `NOTEBOOK.md`.

## Layout

| Path | Content |
|---|---|
| `blueprint/` | One Markdown file per module, with detailed proofs, Lean statements and dependencies. Start with `blueprint/README.md`; `blueprint/IMPORTS.md` has the module graph. |
| `reviews/` | The independent referee reports from the blueprint review round. |
| `OrtegaCerdaMultipliers/` | The Lean formalization. |
| `NOTEBOOK.md` | Errata (N-xx) and implementation notes (I-xx). |
| `formalization.yaml` | Metadata in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format. |
| `scripts/` | `make_challenge.py`, `check_statements.py` (the statement freeze-check), `new_worktree.sh`. |

## Relation to the BOC project

The companion formalization of Berndtsson–Ortega-Cerdà (1995) uses `OC.theorem2_uniform` to prove its Theorem 6 without the external Theorem G. This project does not depend on BOC. Its foundation files (∂̄ calculus, Cauchy transform, Weyl's lemma, disc geometry) are copied from BOC under namespace `OC`.

## Building

```sh
lake exe cache get   # once
lake build
```

Toolchain: Lean v4.35.0, Mathlib v4.35.0.

## License

Apache License 2.0 (see `LICENSE`).
