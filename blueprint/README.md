# Blueprint: Ortega-Cerdà, *Multipliers and weighted ∂̄-estimates* (RMI 2002)

**Source.** J. Ortega-Cerdà, Rev. Mat. Iberoamericana **18** (2002), 355–377.
- Reference copy (gitignored), the printed version: `literature/10.4171-rmi-322.pdf` (doi:10.4171/rmi/322). `RMI-18-2002-355.pdf` in the root is a byte-identical copy.
- arXiv version: `literature/arXiv-math-9912139.pdf`.
- Page references `[p. 363]` are to the journal pagination.

**Lean project.** Library `OrtegaCerdaMultipliers`, namespace `OC`, Lean/Mathlib v4.35.0.

## 0. Plan and status

This follows the same workflow as the companion BOC project (`../1995ReineAngewMath`):
1. Blueprint: one Markdown file per module, with a detailed proof, the Lean statements and explicit dependencies.
2. Scaffold: all statements compiled, proofs `sorry`.
3. Independent agent review of the blueprint and of every statement.
4. Implementation in git worktrees (`scripts/new_worktree.sh`).
5. `comparator` check of the main results against the self-contained `Challenge.lean`.
6. `formalization.yaml` and `NOTEBOOK.md`.

**Purpose beyond the paper.** Theorem 2 (sup-norm part) supplies, without boundary regularity, the ∂̄-estimate that BOC Theorem 6 needs (BOC NOTEBOOK N-30, I-20). This project must therefore **not** depend on BOC; BOC will `require` this one (BOC module M23). Foundation files are copied from BOC into module M01, each with a provenance line.

## 1. What is formalized

Main results:
- **Theorem 4**, multipliers, in `𝔻` and `ℂ`: `theorem4_disc`, `theorem4_plane`.
- **Proposition 2**, families of multipliers with disjoint exceptional sets: `prop2_disc`, `prop2_plane`.
- **Theorem 2**, `L^p` and sup estimates in `𝔻`: `theorem2` in the normalisation the proof gives, and `theorem2_printed` for the printed `L^p` form.
- **Theorem 1** (Christ) in the locally doubling form: `theorem1`, plus `theorem1_christ` for the doubling form as stated.
- **Proposition 1**, kernel decay: `prop1`.
- **Theorem 5**, multipliers for measures on `ℝ`: `theorem5`.
- **Theorem 3**: `theorem3 : TheoremOCS → …`. It is conditional on the cited Ortega-Cerdà–Seip theorem [OCS99], exactly as the paper uses it.

The statements are in `comparator/statements.lean`, and the definitions in `OrtegaCerdaMultipliers/Defs.lean`.

Not formalized:
- the cited theorems of Hörmander, Christ (cited form), Donnelly–Fefferman, Lyubarskiĭ–Sodin and Seip, which are background only;
- Berndtsson's Example (p. 356), which is optional: the weight takes the value `−∞`.

## 2. Conventions and divergences (see M00)

1. **Weights are pairs `(φ, μ)`** (`IsSubharmonicWeight Ω φ μ`):
   - `φ` is continuous on `Ω`;
   - `μ` is locally finite and carried by `Ω`;
   - `∫ φ Δχ = ∫ χ dμ` for all test functions `χ`.

   This is "continuous subharmonic with Riesz measure `μ`". Continuity is implied by the paper's hypotheses ([Chr91, Lemma 2.3]), so the formal statements are equivalent to the printed ones. Mathlib has no Riesz-measure theory, which is why the pair is needed.
2. **Laplacian.** `Δ` is the standard Laplacian (`Δ log|z| = 2πδ`). The paper's own constant bookkeeping with `2π` is inconsistent (NOTEBOOK).
3. **Hyperbolic distance** `β = artanh ρ`, with `ρ` the pseudo-hyperbolic distance. Any normalisation changes only constants.
4. **Theorem 2 normalisation.** The printed `L^p` estimate uses the weight `e^{-φ}` for every `p`, while the proof (and Theorem 1) uses `‖u e^{-φ}‖_p`. We state both:
   - `theorem2`: one `u` for all `p ∈ [1, ∞]`, including the sup bound;
   - `theorem2_printed`: the printed form, with `u` depending on `p`, obtained by applying `theorem2` to `φ/p`.
5. **Proposition 1** is stated with the upper bound only. The printed `≃` fails at the zeros of the multipliers.
6. **Lemma 5** nodes lie within a bounded multiple of `R`, not inside `R`. The text only uses "near `R_i`".

## 3. Modules

| # | File (doc) | Lean | Content | Paper |
|---|---|---|---|---|
| M00 | `M00_Defs.md` | `Defs.lean` | definitions and main statements | — |
| M01 | `M01_Foundations.md` | `Foundations/*.lean` | copied from BOC: Wirtinger/∂̄ calculus, polar coordinates, Cauchy transform and Pompeiu, Weyl for ∂̄, mean-value estimates, Möbius and pseudo-hyperbolic geometry; new: `β = artanh ρ` (metric, balls, invariance) | — |
| M02 | `M02_Potentials.md` | `Potential/*.lean` | log-kernel identity `∫ log|z−ζ| Δχ = 2πχ(ζ)`; Weyl for `Δ` (weakly harmonic continuous ⇒ harmonic); uniqueness of weights up to harmonic functions; the kernels `k(z,ζ)` of Lemma 6 in `ℂ` and `𝔻`, the Andersson–Pascuas bound, convergence, continuity and `ΔK[ν] = ν` | §4.1 |
| M03 | `M03_Doubling.md` | `Doubling/*.lean` | Lemma 1 (both inequalities; `ℂ`, `𝔻`, `ℝ`); Lemma 2 (segments, arcs and circles are null); `ρ(z)` (well defined, `μ(B(z,ρ(z))) = 1`, positivity, upper bound); Claim 1; Lemma 3; [Chr91, Lemma 2.3]; growth of `μ(B(z,R))` | §2 |
| M04 | `M04_Regularization.md` | `Regularization.lean` | Lemma 6 in `ℂ` and `𝔻` | §4.1 |
| M05 | `M05_Partition.md` | `Partition/*.lean` | Lemma 4 and Claim 2: partition into rectangles of mass `N` (`ℂ`: Cartesian; `𝔻`: polar, including the central region; `ℝ`: intervals) | §3 |
| M06 | `M06_Quadrature.md` | `Quadrature.lean` | Lemma 5: `N` points matching the moments `0..m−1` (generating-function construction) and the shifted set `κ` | §3 |
| M07 | `M07_LogModulus.md` | `LogModulus.lean` | a function on `ℂ` or `𝔻`, harmonic off a discrete set `Λ` with logarithmic singularities of integer multiplicity, is `log|h|` for a holomorphic `h` with zero set `Λ` | §3 (p. 366) |
| M08 | `M08_Multiplier.md` | `Multiplier/*.lean` | Theorem 4 in `𝔻` and `ℂ`: construction and the estimates (2), (3) | §3 |
| M09 | `M09_SeveralMultipliers.md` | `SeveralMultipliers.lean` | Proposition 2: finite colouring of the rectangles; multipliers with zeros moved to `κ(R)` | §3 |
| M10 | `M10_ModelKernels.md` | `ModelKernels.lean` | Lemma 7 (disc) and Lemma 8 (plane); Schur test; Forelli–Rudin-type integrals; weak `∂̄`-equation for the kernels | §4.2 |
| M11 | `M11_Theorem2.md` | `Theorem2.lean` | Theorem 2 and the printed variant; bridge lemma for `C²` weights with `δ ≤ (1−|z|²)²Δψ ≤ M` (used by BOC) | §4.2 |
| M12 | `M12_Theorem1.md` | `Theorem1.lean` | Theorem 1 (locally doubling), the Christ corollary, Proposition 1 | §4.2 |
| M13 | `M13_Theorem5.md` | `Theorem5.lean` | Theorem 5 (zeros on `ℝ`) | §4.3 |
| M14 | `M14_Theorem3.md` | `Theorem3.lean` | Theorem 3 from `TheoremOCS` and Theorem 5 | §4.3 |

### Dependency graph

```
M00 ─┬─ M01 ── M02 ─┬─ M04 ─────────────────┐
     │              │                        │
     └─ M03 ────────┼─ M05 ── M06 ─┐         │
                    │              ├─ M08 ── M09 ─┬─ M11 (Thm 2)
                    └─ M07 ────────┘              ├─ M12 (Thm 1, Prop 1)
                                     M10 ─────────┘
                    M05 M06 M07 M02 ── M13 (Thm 5) ── M14 (Thm 3)
```

Priority: the disc path M01–M11 comes first, since it is what BOC needs. Then the plane (M08/M09 plane, M12), then M13–M14.

## 3a. Design decisions taken while writing the blueprint (2026-11-01)

1. **Moment order.**
   - The proof of Theorem 4 matches the moments of order 0–2 in 2D (`m = 3`) and of order 0–1 on ℝ (`m = 2`). It does not use the paper's `m` with `mγ > 1`.
   - Rectangles are counted by Euclidean or hyperbolic *area* (length on ℝ), not by μ-mass. Together with the decay estimate inside the proof of Lemma 3, this makes any `γ > 0` suffice (M03 §decay, M08).
   - The paper's Lemma 3 is still formalized as printed (M03).
2. **Lemma 5 nodes.**
   - "Inside `R`" is false for general measures (M06 counterexample). M06 proves a construction with nodes near `R`, at distance at most `2m · radius`.
   - In 𝔻 we use two regimes (M08), so that all nodes lie in 𝔻:
     - hyperbolically small cells use M06;
     - large cells use `N` copies of the μ-barycentre (moments 0 and 1).
   - On ℝ, barycentres give real zeros (M13), and no Chebyshev quadrature is needed.
3. **Normalisation.** `ν = Δψ / 2π`, so a zero of `h` carries `ν`-mass 1. In the 2D proofs the cells have `ν`-mass `N = 12`.
4. **Disc partition.** Horocyclic boxes, i.e. Cayley preimages of rectangles in the upper half-plane (M05). This replaces the paper's polar rectangles, which degenerate near the origin and at large scales.
5. **Lemma 6.** Done with compactly supported local radial potentials (M04). The paper's global kernels on p. 371 have a sign error, and its commutation step fails (M02 appendix). Only Theorems 1 and 2 and Proposition 1 use Lemma 6.
6. **Quantitative core.**
   - Theorem 4, Proposition 2 and Theorem 2 are proved in a quantitative form (`*_quant`). Their constants depend only on the doubling constant and the mass radius.
   - The per-weight main statements follow from these, as does `theorem2_uniform`, which BOC uses.
   - Consequence: M03 and M05 must export uniform versions, with constants chosen after `(C_d, R₀)` and before the measure.
7. **Proposition 2 (statement).** Includes the Theorem-4 bounds for each multiplier, as the paper says, and the disjoint exceptional sets.
8. **Theorem 3.**
   - **Suspected false as printed.** The M14 writer gives a counterexample (to be checked in review). The integral needs the weight: `∫ e^{-φ(z)} d|μ|(z) / |x − z|`. A corrected statement `theorem3_weighted` is proposed.
   - **`TheoremOCS`.** It is the version quoted on p. 375, with `limsup = 0`. The published [OCS99] lemma states `limsup < ∞`; `= 0` follows from its proof. This is to be recorded in the yaml.
   - **Multipliers.** Theorem 3 needs multipliers for the signed measure `μ − 2α dx`. M13 builds them; Theorem 5 is the case `α = 0`.
9. **Shared definitions.** `hypArea = dm/(1 − |z|²)²` on 𝔻 is defined once, in M01, and used by M04, M08, M10 and M11.

## 4. Known issues in the source (initial seeds; the verified list is `../NOTEBOOK.md`)

- (Withdrawn: the p. 356 Example does print `≠ 0`; OCR dropped the slash.)
- p. 357, Theorem 2: the printed `L^p` weight `e^{-φ}` is not what the proof gives (see §2.4 above).
- p. 359, Proposition 1: the lower bound in `|k| ≃ …` fails at the zeros of the multipliers.
- p. 365, Lemma 5: "inside `R`". Equal-weight (Chebyshev) quadrature with nodes inside `R` is cited from [Gau76, Kor94]; we use nodes near `R`.
- p. 365, Lemma 4: thin slices are excluded by Lemma 1 only via reverse doubling for strips, which needs an argument.
- p. 364, Lemma 4 in `𝔻`: polar rectangles degenerate near the origin, and the central region is not treated.
- p. 360, Lemma 2 covers segments, but polar rectangles also need arcs and circles to be null.
- p. 366: "the subharmonic function in the statement of Theorem 3" should read Theorem 4.
- p. 366: `log|h| = ψ − (1/2π)∫ log|z−ζ| (Δψ − Σδ)`. The point masses must carry the factor `2π` (or `Δψ` must be divided by `2π`); the same factor appears in the masses `N` of the rectangles.
- p. 372, proof of Theorem 2: the auxiliary weight `ψ = φ − (ε/2) log(1−|z|²)` has the wrong sign. With it the kernel bound gives a factor `(1−|z|)^{-ε/2}` and the sup estimate fails. One needs `ψ = φ + c log(1−|z|²)` with `0 < c` small (here `c = ε/8`, standard Laplacian). The printed kernel estimate `|κ| ≃ … ((1−|ζ|)/(1−|z|))^{ε/2}` inherits the sign. To be verified against the page images.
- p. 373: "|g| ≲ e^ψ, thus ∫|u|^p e^{-φ} … ≲ ∫ |u/g|^p (1−|z|)^{ε/2} …" holds only for `p = 1` in the printed normalisation.
- Lemma 7 and Lemma 8: "an immediate consequence of Hölder's inequality" means the Schur test.

## 5. Handoff to BOC (BOC module M23, to be written in the BOC blueprint)

BOC's finite step needs `W` with `∂̄W = g` on `𝔻` and `|W| e^{-ψ₀/2} ≤ C · sup |g| (1−|z|) e^{-ψ₀/2}`, where `ψ₀ ∈ C²(𝔻)` and `δ ≤ (1−|z|²)² lap ψ₀ ≤ M`.
- **Apply `theorem2` at `p = ∞`** with `φ = ψ₀/2` and `μ = Δ(ψ₀/2) dm`. The hypotheses come from the M11 bridge lemma:
  - `IsSubharmonicWeight` by integration by parts for `C²` functions;
  - local doubling and the mass condition from `Δ̃ ≍ 1`.
- **Then holomorphy near `S`** follows from `∂̄W = 0` there, by Weyl. `W` need not be canonical.
- **On the BOC side:** add `theorem6_uncond` and its comparator statement, and update the yaml.
