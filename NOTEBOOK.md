# Formalization notebook

**Source:** J. Ortega-Cerdà, *Multipliers and weighted ∂̄-estimates*, Rev. Mat. Iberoamericana 18 (2002), 355–377. Page numbers are the journal's.

This notebook records what we noticed in the source while formalizing it: mistakes, gaps, clarifications, simplifications and deliberate divergences.

**Verification.** Every claim about what the paper prints was checked against renders of the publisher's PDF (160–300 dpi). OCR text is not trusted: it drops slashes, for instance in `≠`.

Most entries were confirmed by at least one independent referee agent (reports `rv1`–`rv3`, blueprint review round, 2026-11-01). The status of each entry says so.

**Entry types:**
- **E**: erratum (false as printed);
- **G**: gap or implicit step;
- **T**: typo;
- **S**: simplification;
- **D**: formalization divergence.

---

## Main statements

### N-01 (E, confirmed by two referees) — Theorem 3, p. 358: false as printed
The printed conclusion `|u(x)| e^{-φ(x)} ≤ C (1 + ∫_{|z−x|<1} d|μ|(z)/|x−z|)` fails.

**Counterexample** (blueprint M14 §4, re-derived independently by two referees, with numerical checks):
- the weight `φ₀ = |Im z| + Re z · Im z`, with `Δφ₀ = 2 dx` on ℝ, which is locally doubling and satisfies the mass condition;
- data on the vertical segment `{x₀ − is : δ ≤ s ≤ 1}`, `x₀ = 1/δ`, with `e^{-φ₀} d|μ|` a two-sided Carleson measure with constant 2.

The printed right-hand side stays below `0.6`. But after the gauge `e^{iz²/2}`, any solution differs from a Cauchy transform by an entire function of exponential type. Bernstein's inequality then forces `|u(x₀)| ≳ log(1/δ)`.

The failure does not use the [OCS99] theorem. The problem is invariant under `φ ↦ φ + Re H`, `u ↦ u e^{H}` (`H` entire), and the printed right-hand side is not.

**Formal disproof.** The failure is proved in Lean: `OC.not_theorem3_printed` and the main statement `OC.theorem3_printed_false`. It uses no `TheoremOCS` and needs only the three standard axioms. The formal proof simplifies the counterexample:
- it uses finitely many dyadic point masses `x₀ − i 2^{-(k+6)}` instead of a segment;
- Bernstein's inequality, which is not in Mathlib, is replaced by Phragmén–Lindelöf on the two half-planes, the Cauchy estimate and the mean value theorem.

**Correction.** Weight the integral: `∫_{|z−x|<1} e^{-φ(z)} d|μ|(z)/|x−z|`. The corrected statement is formalized (`theorem3`, conditional on `TheoremOCS` as in the paper). The printed form holds when `φ` is bounded below on `|Im z| < 1`, e.g. `φ = α|Im z|`, the case of [OCS99].

### N-02 (E, confirmed) — Theorem 4, p. 363 (and p. 372): inequalities reversed
The display reads `d(z,Λ)/ρ(z) ≲ |h(z)| e^{-ψ(z)} ≲ (d(z,Λ)/ρ(z))^M`. It should read `(d/ρ)^M ≲ |h| e^{-ψ} ≲ d/ρ`, because `d/ρ ≲ 1`. The formal statement uses the corrected order.

### N-03 (E, confirmed) — Proposition 1, p. 359: the lower bound in `|k(z,ζ)| ≃ e^{-ε|z−ζ|²}/|z−ζ|` is false
- The constructed kernel `Σ_i h_i(z) χ_{Ω_i}(ζ)/h_i(ζ) · …` vanishes when `z` is a zero of `h_i` and `ζ ∈ Ω_i`.
- A referee shows the lower bound fails for *every* kernel solving the equation, e.g. for `φ = |z|² + 2(Re z)₊²` (doubling Laplacian).
- Only `≲` is formalized (`prop1`).

### N-04 (E/G, confirmed) — Theorem 2, p. 357: the printed `L^p` estimate is not what the proof gives
The printed estimate is `∫|u|^p e^{-φ} dm/(1−|z|²) ≲ ∫|f(1−|z|²)|^p e^{-φ} dm/(1−|z|²)` for all `p ∈ [1,∞)` (weight `e^{-φ}`, not `e^{-pφ}`), together with the sup estimate.
- The step on p. 373 ("|g| ≲ e^ψ, thus …") is valid only for `p = 1` in this normalisation.

What we prove:
- **`theorem2`:** one solution `u` with `‖u e^{-φ}‖_{L^p(dm/(1−|z|²))} ≲ ‖f(1−|z|²)e^{-φ}‖_{L^p(dm/(1−|z|²))}` for *all* `p ∈ [1,∞]` at once, by the Schur test. The `p = ∞` case is the printed sup estimate.
- **`theorem2_printed`:** the printed `L^p` form, with `u` depending on `p` (apply `theorem2` to `φ/p`).
- **Open:** whether one `u` satisfies the printed form for every `p` together with the sup bound. This is neither proved nor refuted.

### N-05 (D) — Theorem 1: locally doubling version
The paper states Christ's theorem (doubling `Δφ`) and remarks (p. 357) that the proof gives the locally doubling version. We formalize the latter (`theorem1`) and derive the former (`theorem1_christ`).

### N-06 (D) — weights
A weight is a continuous `φ` with distributional Laplacian `μ` (`IsSubharmonicWeight`).
- The paper's weights (subharmonic, locally doubling Riesz measure) are automatically continuous ([Chr91, Lemma 2.3], applied at every small scale).
- So the formal class equals the paper's (referee-confirmed).
- Mathlib has no Riesz decomposition, so this implication is not formalized.

### N-07 (G, confirmed) — [OCS99] as quoted on p. 375
The paper quotes [OCS99] with `limsup_{z→∞} |u(z)| e^{-α|Im z|} = 0`. The published statement (Lemma 4 of the UB postprint) gives only `< ∞`.
- The `= 0` version follows from the [OCS99] proof (a referee checked each of its three pieces), and Theorem 3 needs it.
- The hypothesis `TheoremOCS` is the p. 375 quotation.

## Section 2: locally doubling measures

### N-08 (T, confirmed) — p. 360, Lemma 1: attributions swapped
The left inequality follows from the definition; the right one is [Chr91, Lemma 2.1].

### N-09 (G, confirmed) — p. 360, Lemma 2
- **The projection argument.** The projected measure is in fact locally doubling at small scales, by covering the strip with balls, but the paper does not check it.
- **Arcs, circles and spheres** are also needed, for polar rectangles and for the continuity of `r ↦ μ(B(z,r))`.
- **Formalization:** porous sets are null, which covers all of these.

### N-10 (G, confirmed) — p. 361, Lemma 3
- **Range.** Stated for `d < 1` but used up to `2 sup ρ` (p. 367); doubling at bounded scales (by chaining) is needed.
- **Exponents.** The exponent bookkeeping mixes the two exponents of Lemma 1.

### N-11 (S, confirmed) — the moment order `m`
The paper chooses `m` with `mγ > 1` (Lemma 3), which can be arbitrarily large.
- **What suffices:** order `m = 3` (moments 0, 1, 2) in 2D, and `m = 2` on ℝ.
- **Why:** count rectangles by area (length on ℝ) instead of by μ-mass. The decay `ρ(ζ)/d(z,ζ) ≲ (ρ(z)/d)^{γ²}` then gives geometric decay over dyadic rings for any `γ > 0`.
- **Consequences:**
  - in the disc it avoids the problem of N-14;
  - on ℝ the zeros can be barycentres, hence real, with no Chebyshev quadrature needed (N-16).
- **Lost:** only the unproved Remark after Theorem 4 (`M = 1`, separated zeros).

## Section 3: multipliers

### N-12 (G, confirmed) — p. 364, Lemma 4
Several steps are missing:
- "a square `R × R` has mass ≥ 1" needs strips of width `2R`;
- the bisection threshold compares rectangles, not balls ("`R ⊂ 2R′`" when `h > w/3`), and the positivity of the half-masses is unchecked;
- "we use Lemma 1" for the final slices is a gap; it is filled by reverse doubling for slabs.

In the disc:
- the central region is not treated;
- polar eccentricity breaks down at large hyperbolic scales.

The formalization uses horocyclic boxes (preimages of rectangles under the Cayley map) instead of polar rectangles.

### N-13 (E, confirmed) — p. 365, Lemma 5: "inside R" is false
- **Atomic counterexample (M06).** For `μ = N(w δ₋₁ + (1−w) δ₁)` on `R = [−1,1]²` with irrational `w`, no equal-weight nodes in `R` match the moments of order ≤ 2.
- **Absolutely continuous counterexamples.** A referee shows by compactness that it also fails for some absolutely continuous measures.
- **Doubling `Δψ|_R`.** For this case it is unproved; the paper cites Chebyshev quadrature [Gau76, Kor94].
- **What we prove instead.** M06 proves nodes within distance `2m · radius` of the centre. In the plane this suffices.

### N-14 (G, confirmed) — p. 368, disc: the proof assumes hyperbolically small rectangles
When `Δψ` is sparse, the rectangles of mass `N` are hyperbolically large, and nodes near `R` may leave `𝔻`. The formalization uses two regimes:
- small cells use the moment-matching nodes;
- large cells use `N` copies of the barycentre (moments 0 and 1).

It also uses Taylor's formula with remainder along segments instead of power series.

### N-15 (E, confirmed) — pp. 366–367: the potential formula and (2)/(3)
- **The point masses** `δ_λ` must carry the factor `2π` (`Δ log|z| = 2πδ`). Equivalently the rectangles have mass `2πN`.
- **Displays (2)/(3):** the middle term has the wrong sign, and (3) lacks `+C`.
- **Wrong theorem number:** "the subharmonic function in the statement of Theorem 3" should read Theorem 4.
- **Laplacian conventions:** the paper mixes `∂∂̄` and the standard Laplacian.

### N-16 (S) — Theorem 5: real zeros without quadrature
With moment order 2 (N-11), each interval's zeros are its barycentre, with multiplicity. The paper appeals to Lemma 5. A referee notes that Bernstein's negative result does not cover the paper's regime `N = mk`, `k ≫ m`, so the literal route is not disproved, only unnecessary.

### N-17 (S, confirmed) — p. 369, Proposition 2
"Besicovitch" can be replaced by a greedy colouring of a bounded-degree graph.

### N-18 (G) — Theorem 3 needs more than Theorem 5
Theorem 3 needs multipliers for `φ − α|Im z|`, whose Laplacian `μ − 2α dx` is a signed measure. The paper has no line version of Lemma 6. The formalization builds these multipliers directly; Theorem 5 is the case `α = 0`.

## Section 4: the ∂̄-estimates

### N-19 (E, confirmed) — p. 371, Lemma 6, plane kernel sign
In `k(z,ζ)` the term `+ z²/(2ζ²)` should be `− z²/(2ζ²)`. With the printed sign the integrals diverge (checked numerically: decay `R⁻²` instead of `R⁻³`).

### N-20 (G, confirmed) — p. 371, Lemma 6, the commutation step
`K[μ₁] − K[μ₁ ⋆ χ] = K[μ₁] − K[μ₁] ⋆ χ` does not hold as written.
- **Plane:** an unbounded harmonic polynomial remains; subtracting it repairs the proof.
- **Disc:** the term `|z|²(1−|ζ|²)²/|1−ζ̄z|²` breaks the commutation.
- **Disc growth class:** `μ(D(0,r)) ≲ (1−r)^{-2}` is too weak for convergence; the true growth is `(1−r)^{-1}`.
- **Formalization:** compactly supported local radial potentials, which also weaken the mass hypothesis to `≥ 1`.

### N-21 (T, confirmed) — p. 370, Lemma 6 in the disc
`Δψ > ε dm` should read `(1−|z|²)² Δψ > ε`. The "dyadic squares" are not specified.

### N-22 (E, confirmed) — pp. 372–374, proof of Theorem 2: sign of the auxiliary weight
The printed `ψ = φ − (ε/2) log(1−|z|²)` has the wrong sign.
- With it, both Schur bounds diverge (a factor `(1−|z|)^{-ε/2}`).
- The correct choice is `ψ = φ′ + c log(1−|z|²)` with `c = min(ε/8, 1/2)` (standard Laplacian), where `φ′` comes from Lemma 6.
- The paper's own "`(1−|z|²)²Δψ > ε/2`" only fits the corrected sign.
- The kernel bound on p. 374, `|κ| ≃ … ((1−|ζ|)/(1−|z|))^{ε/2}`, inherits the sign, and only `≲` holds.

Lemma 6 is used here without being cited.

### N-23 (E, confirmed) — p. 374, Theorem 1: kernel exponent
`e^{2ε(ζ̄z − |ζ|²)}` should be `e^{ε(ζ̄z − |ζ|²)}`. With the printed exponent the kernel does not decay against `e^{-ψ}` with `ψ = φ − (ε/2)|z|²`.

### N-24 (clarification) — Lemmas 7, 8
"An immediate consequence of Hölder's inequality" means the Schur test. Lemma 7 is correct as printed (referee-confirmed).

## Withdrawn

### W-01 — p. 356, Example
An early note claimed the Example prints "`∫_D f dm = 0`". The page image shows `≠ 0`; the OCR dropped the slash. No erratum.

---

## Log of issues found during the Lean implementation

### I-01 (M10) — a false helper statement in the blueprint
The scaffold lemma `lintegral_FR_near` (the near-diagonal Forelli–Rudin bound) claimed
`∫_{B(a,d/2)} (1−|w|²)^{-s} / (|1−āw||a−w|) dm(w) ≤ 2π d^{-s}` for every `s > 0`.
- **Counterexample:** `a = 0`, `s = 10`. The left side is `2π ∫₀^{1/2} (1−r²)^{-10} dr ≈ 1.84 · 2π`.
- **Cause:** the blueprint's step `2^s π d^{-s} ≤ 2π d^{-s}` silently assumes `s ≤ 1`.
- **Resolution:** the lemma was removed. The proved replacement `lintegral_FR_near_of_le_one` adds the hypothesis `s ≤ 1`, which the only consumer (`lintegral_FR`, with `s < 1`) satisfies. This is a blueprint erratum, not a paper erratum.

### I-02 (M10, M11) — confirmations
- **Lemmas 7 and 8** are plain Schur tests (N-24). The printed `L^p` form of Lemma 7 follows by conjugating with `(1−|z|²)^{α/p}`.
- **The corrected auxiliary weight** of N-22, `ψ = φ′ + c log(1−|z|²)` with `c = min(ε/8, 1/2)`, is the one used in the formal proof of Theorem 2.
- **The doubling constant** of `hypArea` in hyperbolic balls is 16, from `hypArea(D(z,r)) = π sinh² r`.

### I-03 (M02) — a false helper statement caused by Lean parsing
The scaffold lemma `integral_bumpPot_mul_laplacian` had the right-hand side `∫ z, k(z − ζ) χ z - χ ζ`.
- **The problem.** Lean parses this as `∫ z, (k χ − χ ζ)`, which is not integrable when `χ ζ ≠ 0`. The Bochner integral is then `0`, so the statement is false.
- **The fix.** It was removed. The intended statement, `integral_bumpPot_mul_laplacian'` (with the parentheses), is proved and used. This is a blueprint/scaffold erratum.

### I-04 (M03) — blueprint gaps and simplifications in the doubling lemmas
- **§3.11 (`massRadiusM_inv_smul`).** The blueprint's argument is circular: the scale depends on constants that themselves depend on the scale. It is repaired by fixing the scale first, with an explicit growth radius `(2N+1)R₀`.
- **§3.12 (Claim 1).** The case `ρ(y) ≥ ρ(x)` is trivial; only `ρ(x) > 2ρ(y)` needs Lemma 1.
- **[Chr91, Lemma 2.3].** Proved from the pointwise bound `log(R/d) ≤ Σ_k log 2 · 1_{B(x, R/2^k)}` plus reverse doubling. This is simpler than dyadic annuli.
- **Lemma 2.** Proved with Vitali's covering instead of Zorn.
- **Uniform constants.** None of the qualitative lemmas, whose constants are chosen after `μ`, could be reused for the uniform versions. They were re-proved with explicit constants (`Doubling/Uniform.lean`, `Doubling/Quant.lean`).

### I-05 (M04) — Lemma 6 constants
Doubling of the regularized measure in the disc: squeezing between `ε·hypArea` and `K·hypArea` gives the constant `max(2C_d, 4cosh²(½)·K/ε)`. This makes the blueprint's `291600 K/ε` and its `artanh` monotonicity argument unnecessary.

### I-06 (M08, M09, M12, M14) — notes from the multiplier and estimate proofs
- **M08 plane far field.** It reuses the near-field dyadic summation instead of the Fubini step with `∫|z − w|^{-3}`.
- **M08 continuity of the cell potentials.** It is proved by uniform approximation with truncated kernels `log max(·, t)`.
- **M09.** The degree bound for the colouring counts disjoint cells of mass `N` near a cell, instead of using hyperbolic areas. One generic colouring proof covers plane and disc. Confirmed (p. 369): Besicovitch is not needed.
- **M12 (N-23 made precise).** With the auxiliary weight `ψ = φ′ − c|z|²`, the plane kernel must carry `e^{2c(ζ̄z − |ζ|²)}`, and then the `±c|·|²` terms cancel exactly to `e^{-c|z−ζ|²}`. The paper's `ψ = φ − (ε/2)|z|²` corresponds to `c = ε/2`, i.e. the exponent `ε`, not `2ε`.
- **M12 (N-03 made formal).** `thm1H_eq_zero_of_zero` proves that the kernel vanishes at the zeros of the multipliers.
- **M14.** The constant of the corrected Theorem 3 is `C = 2 C_up C_O (1 + c⁻¹ e^α)`.
