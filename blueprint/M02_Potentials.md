# M02 — Potential theory for weights `(φ, μ)`

**Lean files** (all new, namespace `OC`):
- `OrtegaCerdaMultipliers/Potential/Radial.lean`: a verbatim copy of BOC `Potential/Radial.lean` (BOC M10), with a provenance line. It is not in the M01 copy list, so M02 copies it. It provides `kernel a b`, `sFun a b`, `wFun a b` and their API.
- `OrtegaCerdaMultipliers/Potential/Fundamental.lean`: §1, the log kernel, local integration by parts, the Green kernel of `𝔻`.
- `OrtegaCerdaMultipliers/Potential/Weyl.lean`: §2–§3, Weyl's lemma for `Δ`, uniqueness, and calculus of weights.
- `OrtegaCerdaMultipliers/Potential/Local.lean`: §4, smoothed point masses and local potentials of measures. These replace the paper's global kernels `K[ν]`, see §0.

**Paper:** §4.1, pp. 370–372: the operators `K[ν]` used in the proof of Lemma 6.

**Depends on:**
- **M01** (copied BOC foundations):
  - `lap φ = ¼ Laplacian.laplacian φ`;
  - `lap_comp_sub`, `lap_comp_normSq`, `integral_mul_lap`;
  - polar/radial integrals: `integral_comp_normSq_sub`, `integrable_comp_normSq_sub`, `lintegral_comp_normSq_sub`, `volume_ball_complex`;
  - `continuous_mul_of_tsupport_subset` and `integrable_mul_of_tsupport_subset`, real-valued variants if needed.
- **The copied** `Potential/Radial.lean`:
  - `isProfile_planeProfile`, `contDiff_kernel`, `kernel_nonneg`, `kernel_eq_zero`, `integral_kernel`, `kernel_le_indicator`, `indicator_le_kernel`;
  - `contDiff_sFun`, `sFun_of_ge`, `lap_sFun_normSq`, `wFun_nonpos`, `wFun_eq_zero`, `contDiffOn_wFun`, `exists_abs_sFun_le`, `sFun_scale`, `kernel_scale`.
- **Mathlib:**
  - `InnerProductSpace.HarmonicAt` / `HarmonicOnNhd`, `InnerProductSpace.laplacian_congr_nhds`, `AnalyticAt.harmonicAt_log_norm`;
  - `HasCompactSupport.contDiff_convolution_right`, `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`;
  - `ContDiff.lipschitzWith_of_hasCompactSupport`;
  - `tendsto_integral_filter_of_dominated_convergence`, `continuousOn_of_dominated`, `integral_integral_swap`, `lintegral_lintegral_swap`;
  - `integral_withDensity_eq_integral_toReal_smul`, `ofReal_integral_le_lintegral_ofReal`;
  - `intervalIntegral.intervalIntegrable_log'`, `integral_Ioi_of_hasDerivAt_of_tendsto`;
  - `exists_contMDiffMap_one_nhds_of_subset_interior` (smooth Urysohn), with `contMDiff_iff_contDiff`.

**Used by:**
- M04 (Lemma 6): §4 and §3;
- M07 (log-modulus): §1 and the Weyl lemma of §2;
- M08 (multiplier construction, potentials of compactly supported signed measures): §1;
- M11 and M12 (Theorems 2 and 1): `IsSubharmonicWeight.sub_contDiffOn` and `isSubharmonicWeight_of_contDiffOn` (bridge lemma).

## 0. Design decision: local potentials instead of the paper's `K[ν]`

The paper (p. 371) introduces global potentials `K[ν](z) = ∫ k(z,ζ) dν(ζ)`, with kernels that have harmonic corrections in `ℂ` and in `𝔻`. It uses them only in Lemma 6, to write `ψ = φ + K[μ̃₁] − K[μ₁]` and to estimate `|K[μ₁] − K[μ̃₁]|`. Checking this route (Appendix A) found the following.
- **Plane kernel sign.** The printed plane kernel has a sign error in the quadratic term. With the printed sign, `K[ν]` diverges for `ν(D(0,r)) ≍ r²`.
- **Plane: `φ − ψ` unbounded.** The cut-off `1 − χ_{D(0,1)}(ζ)` destroys the mean-value property of the correction for `|ζ| < 1 + 2R`. As written, `K[μ₁] − K[μ̃₁]` then contains a harmonic polynomial of degree `≤ 2` in `z`, which is unbounded in general, so `sup|φ − ψ| < ∞` fails.
- **Disc: harmonic correction not covered.** In the disc, the harmonic correction `(1−|ζ|²)(…)` is not harmonic in `ζ`. So the invariant convolution changes it, and the paper's estimate (which only covers the logarithmic part) does not apply to it.
- **Unnecessary detour.** All three global facts (absolute convergence for growing measures, Fubini over infinite measures, continuity) are a detour. The difference `K[μ₁] − K[μ̃₁]` is a **compactly supported** object: the potential of `μ₁ − μ̃₁`, which has zero local average.

**Formal route.** For each `ζ` we use the explicit compactly supported potential `G_s(· − ζ)` of `δ_ζ − k_s(· − ζ)`, where `k_s` is a smooth radial probability density on `ball 0 s`. We integrate it against `μ₁`:

`V(z) = ∫ G_{s(ζ)}(z − ζ) dμ₁(ζ)`,  `ΔV = μ̃₁ − μ₁`,  `μ̃₁ = (∫ k_{s(ζ)}(· − ζ) dμ₁(ζ)) dm`.

The radius `s(ζ)` may vary: `s ≡ R` in `ℂ`, and `s(ζ) = (1−|ζ|²)/4` in `𝔻` (a Euclidean disc comparable to a hyperbolic disc). Then `ψ := φ + V` (M04). `V ≥ 0` is bounded by [Chr91, Lemma 2.3], exactly as in the paper, but no convergence at infinity is ever needed.
- **`G_s` comes from BOC.** `G_s` is BOC's radial potential `−(4π)⁻¹ wFun (s²/4) s²`, so its properties are already proved. Combined with the fundamental solution (§1), the weak identity `ΔG_s = k_s − δ₀` follows in a few lines (§4.2).
- **The paper's kernels are documentation only.** Their formulas (corrected), the Andersson–Pascuas estimate (proved, with constant `4/π`), the convergence classes, and continuity and `ΔK[ν] = ν` are recorded in **Appendix A**. They are not part of the formalization. Their statements typecheck (`kPlane`, `kDisc`, `kDisc_eq`, `abs_kDisc_le`, `abs_kPlane_le`) in case a later module wants them.

**Normalisation.** `Δ` is the standard Laplacian (`Laplacian.laplacian`), so `Δ log|z| = 2πδ₀`, `Δ log|z|² = 4πδ₀`, and `E(z) = (1/4π) log|z|²` is the fundamental solution. BOC's `lap = Δ/4`. The paper's `k(z,ζ) = (1/4π) log|z−ζ|² + …` agrees with this.

---

## 1. The logarithmic kernel (`Potential/Fundamental.lean`)

### Statements

```lean
theorem locallyIntegrable_log_norm_sub (ζ : ℂ) :
    LocallyIntegrable (fun z : ℂ ↦ Real.log ‖z - ζ‖)

/-- **Fundamental solution.** `∫ log|z − ζ| Δχ(z) dm(z) = 2π χ(ζ)`. -/
theorem integral_log_norm_sub_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (ζ : ℂ) :
    ∫ z, Real.log ‖z - ζ‖ * Laplacian.laplacian χ z = 2 * Real.pi * χ ζ

/-- Integration by parts against a test function, for `U ∈ C²(Ω)`. -/
theorem integral_mul_laplacian_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {U χ : ℂ → ℝ}
    (hU : ContDiffOn ℝ 2 U Ω) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ω) :
    ∫ z, U z * Laplacian.laplacian χ z = ∫ z, Laplacian.laplacian U z * χ z

/-- **Green kernel of the disc.** `∫ log ρ(ζ, z) Δχ(z) dm(z) = 2π χ(ζ)`, `χ` supported in `𝔻`. -/
theorem integral_log_pseudoHyp_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ 𝔻) {ζ : ℂ} (hζ : ζ ∈ 𝔻) :
    ∫ z, Real.log (pseudoHyp ζ z) * Laplacian.laplacian χ z = 2 * Real.pi * χ ζ
```

`pseudoHyp ζ z = |ζ − z|/|1 − ζ̄z| = |(z−ζ)/(1−ζ̄z)|`, the paper's Green kernel. At `z = ζ` all logarithms take Lean's junk value `log 0 = 0`. That is a single point, hence irrelevant.

### Proofs

**1.1 `locallyIntegrable_log_norm_sub`.**
- It suffices to show `IntegrableOn (log ‖· − ζ‖) (ball ζ R)` for every `R > 0`, since every compact set lies in such a ball.
- By BOC `lintegral_comp_normSq_sub ζ`, with `F(t) = ofReal(½|log t|) · 1_{t < R²}`, which is measurable:
  `∫⁻_{ball ζ R} |log ‖z−ζ‖| = π ∫_0^{R²} ½|log t| dt < ∞`.
  Here `log ‖z−ζ‖ = ½ log(‖z−ζ‖²)` (`Real.log_sqrt`, or `Real.log_pow`), and `log` is interval integrable on `[0, R²]` (`intervalIntegral.intervalIntegrable_log'`).
- Measurability: `Real.measurable_log.comp` (continuous norm).

**1.2 `integral_log_norm_sub_mul_laplacian`.** We prove `∫ log(‖z−ζ‖²) Δχ = 4π χ(ζ)` and then divide by 2: `log(‖x‖²) = 2 log‖x‖` (`Real.log_pow`), also at `x = 0`.

*Step 0 (translation).* Put `χ_ζ(z) = χ(z + ζ)`. Then:
- `Δχ_ζ(z) = Δχ(z + ζ)` (`lap_comp_sub` with `a = −ζ`, times 4);
- `∫ f(z − ζ) dz = ∫ f(z) dz` (`integral_sub_right_eq_self`).

So assume `ζ = 0`.

*Step 1 (regularisation).* For `ε > 0` let `L_ε(x) = log(‖x‖² + ε)`.
- It is `C^∞`: `Real.contDiff_log`-type lemmas on the positive function `‖x‖² + ε` (`contDiff_norm_sq`).
- With `F(t) = log(t + ε)`, BOC `lap_comp_normSq` gives `lap L_ε(x) = F'(t) + t F''(t)` at `t = ‖x‖²`. Here `F' = 1/(t+ε)` and `F'' = −1/(t+ε)²`, so
  `lap L_ε = 1/(t+ε) − t/(t+ε)² = ε/(t+ε)²`, i.e. `Δ L_ε(x) = P_ε(x) := 4ε/(‖x‖²+ε)²`.

*Step 2 (integration by parts).* By BOC `integral_mul_lap` (`g = χ ∈ C²_c`, `U = L_ε ∈ C²`), multiplied by 4:
`∫ L_ε Δχ = ∫ P_ε χ`.

*Step 3 (`∫ P_ε χ → 4π χ(0)`).*
- By BOC `integral_comp_normSq_sub 0` with `F(t) = 4ε/(t+ε)²`, which is integrable on `Ioi 0`:
  `∫ P_ε = π ∫_0^∞ 4ε/(t+ε)² dt = π · 4 = 4π`.
  The antiderivative is `−4ε/(t+ε)`, via `integral_Ioi_of_hasDerivAt_of_tendsto`.
- `χ` is Lipschitz with some constant `L` (`ContDiff.lipschitzWith_of_hasCompactSupport`, `n = 2 ≠ 0`).
- Using `‖x‖ ≤ (‖x‖² + ε)^{1/2}`:
  `|∫ P_ε χ − 4πχ(0)| = |∫ P_ε(x)(χ(x) − χ(0)) dx| ≤ L ∫ P_ε(x)(‖x‖²+ε)^{1/2} dx`.
- The last integral equals `π ∫_0^∞ 4ε (t+ε)^{-3/2} dt = π · 4ε · 2ε^{-1/2} = 8π√ε`. The antiderivative is `−8ε(t+ε)^{-1/2}`.
- Hence `|∫ P_εχ − 4πχ(0)| ≤ 8πL√ε → 0` as `ε → 0⁺`.

*Step 4 (`∫ L_ε Δχ → ∫ log(‖x‖²) Δχ`).* Dominated convergence along `𝓝[>] 0` (`tendsto_integral_filter_of_dominated_convergence`):
- **Bound.** For `0 < ε ≤ 1` and `x ≠ 0`: `log‖x‖² ≤ L_ε(x) ≤ log(‖x‖²+1)`, so
  `|L_ε(x) Δχ(x)| ≤ (|log ‖x‖²| + log(‖x‖²+1)) · |Δχ(x)|`.
  This bound is integrable: `Δχ` is continuous with compact support, so bounded with compact support, and `log‖·‖²` is locally integrable (1.1).
- **Pointwise.** For `x ≠ 0` (a.e.), `L_ε(x) → log ‖x‖²` by continuity of `log` at `‖x‖² > 0`.

*Step 5.* By Step 2 the two limits are limits of the same function of `ε`. By uniqueness of limits (`tendsto_nhds_unique`), `∫ log(‖x‖²) Δχ = 4πχ(0)`. ∎

**1.3 `integral_mul_laplacian_of_contDiffOn`.**
- Let `K = tsupport χ`, compact `⊆ Ω`. Choose a compact `K'` with `K ⊆ interior K' ⊆ K' ⊆ Ω`, e.g. `K' = cthickening δ K` with `δ` from `IsCompact.exists_cthickening_subset_open`.
- Smooth Urysohn: Mathlib `exists_contMDiffMap_one_nhds_of_subset_interior` on `M = ℂ` (`𝓘(ℝ, ℂ)`, `contMDiff_iff_contDiff`) gives `η ∈ C^∞(ℂ, [0,1])` with `η = 1` on a neighbourhood `N` of `K` and `η = 0` off `K'`.
- Then `Ũ := η · U`, extended by `0`, is `C²` on `ℂ`:
  - on `Ω` it is a product of `C²` functions;
  - on the open set `(K')ᶜ` it vanishes;
  - these two open sets cover `ℂ`.
- Apply BOC `integral_mul_lap` to `Ũ` (times 4): `∫ Ũ Δχ = ∫ ΔŨ χ`.
- Finally:
  - `Ũ = U` on `N ⊇ K ⊇ supp Δχ`;
  - `ΔŨ = ΔU` on `N` (`laplacian_congr_nhds`);
  - `χ = 0` off `K`. ∎

**1.4 `integral_log_pseudoHyp_mul_laplacian`.**
- **Split the logarithm.** For `z ∈ 𝔻∖{ζ}`, `log ρ(ζ,z) = log‖z − ζ‖ − log‖1 − ζ̄ z‖`, with both norms positive. The integrands agree on `𝔻∖{ζ}` and vanish off `𝔻 ⊇ tsupport χ`. Off `tsupport χ`, `Δχ = 0`, because `χ = 0` on that open set (`laplacian_congr_nhds`). So
  `∫ log ρ(ζ,·) Δχ = ∫ log‖· − ζ‖ Δχ − ∫ h Δχ`, where `h(z) = log‖1 − ζ̄z‖`.
- **`h` is harmonic.** `h` is harmonic on `Ω' := {z : 1 − ζ̄z ≠ 0} ⊇ closedBall 0 1`, an open set (`AnalyticAt.harmonicAt_log_norm` with `f(z) = 1 − ζ̄z`). Hence `h` is `C²` on `Ω'` with `Δh = 0`.
- **Conclude.** By 1.3, `∫ hΔχ = ∫ Δh χ = 0`. Conclude with 1.2. ∎

---

## 2. Weyl's lemma for `Δ` (`Potential/Weyl.lean`)

### Statements

```lean
/-- Smooth radial probability density supported in `ball 0 s`
(BOC `kernel` with `a = s²/4`, `b = s²`). -/
def bumpKernel (s : ℝ) (x : ℂ) : ℝ := kernel (s ^ 2 / 4) (s ^ 2) x

/-- **Mean-value form of Weyl.** -/
theorem eq_integral_bumpKernel_of_weakHarmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Ω)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ z, φ z * Laplacian.laplacian χ z = 0)
    {z : ℂ} {s : ℝ} (hs : 0 < s) (hzs : closedBall z s ⊆ Ω) :
    φ z = ∫ w, bumpKernel s (w - z) * φ w

/-- **Weyl's lemma for `Δ`.** A continuous weakly harmonic function is harmonic. -/
theorem harmonicOnNhd_of_weakHarmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Ω)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ z, φ z * Laplacian.laplacian χ z = 0) :
    InnerProductSpace.HarmonicOnNhd φ Ω

/-- **Weyl's lemma for `Δ`, `L¹_loc` form** (added in the scaffold; the body of M07's
`WeylLaplacianStmt`). -/
/-- **Weyl's lemma for `Δ`, `L¹_loc` form** (the body of M07's `WeylLaplacianStmt`): a locally
integrable weakly harmonic function is a.e. equal to a harmonic function.  (Mollify:
`φ * bumpKernel s` is smooth and weakly, hence classically, harmonic, and equals its own
`bumpKernel`-averages; let `s → 0`.) -/
theorem exists_harmonicOnNhd_ae_eq_of_weakHarmonic {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0) :
    ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u U ∧ ∀ᵐ z ∂(volume.restrict U), f z = u z
```

The hypothesis uses `C^∞` test functions, exactly as in `IsSubharmonicWeight.laplacian_eq`. Only continuous `φ` is treated. Every weight is continuous, and the functions M07 applies Weyl to (`ψ` minus potentials) are continuous off the singular set. The `L¹_loc` version is not needed (remark at the end of this section).

### Proof

**Notation.** For `s > 0` let:
- `k_s := bumpKernel s = kernel (s²/4) s²`;
- `S_s(t) := sFun (s²/4) s² t`.

From the copied Radial API, with `a = s²/4 < b = s²`:
- **(R1)** `k_s ∈ C^∞`, `k_s ≥ 0`, `∫ k_s = 1`, and `k_s(x) = 0` for `‖x‖ ≥ s`. The last uses `kernel_eq_zero`: `s² ≤ ‖x‖²`.
- **(R2)** `S_s ∈ C^∞(ℝ)` (`contDiff_sFun`), and `S_s(t) = −log t` for `t ≥ s²` (`sFun_of_ge`).
- **(R3)** `lap (S_s ∘ ‖·‖²) = −π k_s` everywhere (`lap_sFun_normSq`), i.e. `Δ(S_s ∘ ‖·‖²) = −4π k_s`.

**Step 1 (two radii give the same average).** Let `0 < s₁ < s₂` and `closedBall z s₂ ⊆ Ω`.
- Define `v(x) := S_{s₂}(‖x‖²) − S_{s₁}(‖x‖²)`.
  - `v ∈ C^∞` (R2 composed with `contDiff_norm_sq`).
  - For `‖x‖ ≥ s₂`, both terms are `−log ‖x‖²` (R2), so `v(x) = 0` and `tsupport v ⊆ closedBall 0 s₂`.
  - `Δv = 4π(k_{s₁} − k_{s₂})` by (R3).
- Put `χ(w) := v(w − z)`.
  - `χ ∈ C^∞`, `tsupport χ ⊆ closedBall z s₂ ⊆ Ω`, compact support.
  - `Δχ(w) = Δv(w − z)` (`lap_comp_sub`).
- The hypothesis gives `0 = ∫ φ Δχ = 4π (∫ k_{s₁}(w−z) φ(w) dw − ∫ k_{s₂}(w−z) φ(w) dw)`. Both integrals are genuine: the integrands are continuous on `Ω` and supported in `closedBall z s₂ ⊆ Ω`.
- So `A_{s₁}(z) = A_{s₂}(z)`, where `A_s(z) := ∫ k_s(w − z) φ(w) dw`.

**Step 2 (`s₁ → 0`).** Since `z ∈ Ω` and `Ω` is open, `φ` is continuous at `z`. By (R1),
`|A_{s₁}(z) − φ(z)| = |∫ k_{s₁}(w−z)(φ(w) − φ(z)) dw| ≤ sup_{w ∈ ball z s₁} |φ(w) − φ(z)| → 0`.
Hence `φ(z) = A_{s₂}(z)`, which is `eq_integral_bumpKernel_of_weakHarmonic` (`s₂ = s`, any `s₁ ∈ (0, s)`).

**Step 3 (smoothness).** Fix `z₀ ∈ Ω` and `R > 0` with `closedBall z₀ (3R) ⊆ Ω`.
- **Truncate `φ`.** Let `φ̃ := (closedBall z₀ (2R)).indicator φ`. It is integrable: bounded and measurable on a compact set, since `φ` is continuous there.
- **`φ` is a convolution near `z₀`.** For `z ∈ ball z₀ R` we have `closedBall z R ⊆ Ω`, and `k_R(w − z) = 0` unless `w ∈ ball z R ⊆ closedBall z₀ (2R)`. So Step 2 gives
  `φ(z) = ∫ k_R(w − z) φ̃(w) dw = (φ̃ ⋆ k_R)(z) =: F(z)`.
  Here `k_R(w − z) = k_R(z − w)`, since `k_R` depends only on `‖·‖`.
- **`F` is smooth.** In Mathlib form, `F = convolution φ̃ k_R (ContinuousLinearMap.lsmul ℝ ℝ) volume`. By `HasCompactSupport.contDiff_convolution_right` (`k_R` is `C^∞` with compact support, `φ̃` is locally integrable), `F ∈ C^∞(ℂ)`.

**Step 4 (`ΔF = 0` on `ball z₀ R`).**
- Let `β ∈ C^∞_c` with `tsupport β ⊆ ball z₀ R`. Then
  `∫ ΔF β = ∫ F Δβ = ∫ φ Δβ = 0`.
  The steps are BOC `integral_mul_lap` ×4, then `F = φ` on `ball z₀ R ⊇ supp Δβ`, then the hypothesis.
- So `ΔF = 0` a.e. on `ball z₀ R` (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`; `ΔF` is continuous, hence locally integrable).
- By continuity, `ΔF = 0` on `ball z₀ R`. Use `Measure.eqOn_open_of_ae_eq` with `volume`, which is positive on open sets.

**Step 5.**
- `φ =ᶠ[𝓝 z₀] F`, so `ContDiffAt ℝ 2 φ z₀` (`ContDiffAt.congr_of_eventuallyEq`).
- `Laplacian.laplacian φ =ᶠ[𝓝 z₀] Laplacian.laplacian F =ᶠ 0` (`laplacian_congr_nhds`).

That is `HarmonicAt φ z₀`, for every `z₀ ∈ Ω`. ∎

*Remark (`L¹_loc` version, not needed).*
- If `φ ∈ L¹_loc(Ω)`, Step 2 fails pointwise. One instead shows `φ = A_s φ` a.e. by testing.
- For `β` supported in a small ball, `β − k_s ⋆ β = Δ(G_s ⋆ β)` (§4.2), and `G_s ⋆ β` is a test function. So `∫ φ (β − k_s⋆β) = 0`.
- Hence `φ = F` a.e., and Steps 3–5 apply to `F`.

---

## 3. Weights up to harmonic functions; calculus of weights (`Potential/Weyl.lean`)

### Statements

```lean
theorem IsSubharmonicWeight.integrable_mul {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) {f : ℂ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    Integrable (fun z ↦ φ z * f z)

theorem IsSubharmonicWeight.sigmaFinite {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) : SigmaFinite μ

/-- **Uniqueness.** Two weights with the same Laplacian differ by a harmonic function. -/
theorem IsSubharmonicWeight.harmonicOnNhd_sub {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ₁ φ₂ : ℂ → ℝ}
    {μ : Measure ℂ} (h₁ : IsSubharmonicWeight Ω φ₁ μ) (h₂ : IsSubharmonicWeight Ω φ₂ μ) :
    InnerProductSpace.HarmonicOnNhd (fun z ↦ φ₁ z - φ₂ z) Ω

theorem IsSubharmonicWeight.add_harmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ H : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) (hH : InnerProductSpace.HarmonicOnNhd H Ω) :
    IsSubharmonicWeight Ω (fun z ↦ φ z + H z) μ

/-- A `C²` function with `Δu ≥ 0` is a weight, with Laplacian `Δu dm` on `Ω`. -/
theorem isSubharmonicWeight_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) (hpos : ∀ z ∈ Ω, 0 ≤ Laplacian.laplacian u z) :
    IsSubharmonicWeight Ω u
      (volume.withDensity (Ω.indicator fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z)))

/-- Subtracting a `C²` function whose Laplacian is dominated by the absolutely continuous part
of the Laplacian (M11: `ψ + c log(1−|z|²)`; M12: `ψ − c|z|²`). -/
theorem IsSubharmonicWeight.sub_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {ψ u : ℂ → ℝ}
    {ν₀ : Measure ℂ} {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (h : IsSubharmonicWeight Ω ψ (ν₀ + volume.withDensity g)) (hu : ContDiffOn ℝ 2 u Ω)
    (hΔ : ∀ z ∈ Ω, 0 ≤ Laplacian.laplacian u z ∧
      ENNReal.ofReal (Laplacian.laplacian u z) ≤ g z) :
    IsSubharmonicWeight Ω (fun z ↦ ψ z - u z)
      (ν₀ + volume.withDensity
        (fun z ↦ g z - Ω.indicator (fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z)) z))
```

### Proofs

**`integrable_mul`.**
- The function `φ · f` is continuous on `ℂ`:
  - it is continuous on `Ω`;
  - it vanishes on the open set `(tsupport f)ᶜ`;
  - these two open sets cover `ℂ`.

  (Real version of BOC `continuous_mul_of_tsupport_subset`.)
- It has compact support `⊆ tsupport f`.
- Hence it is integrable (`Continuous.integrable_of_hasCompactSupport`).

**`sigmaFinite`.**
- `Ω` is σ-compact (open subset of `ℂ`): `Ω = ⋃ₙ Kₙ` with `Kₙ` compact (`IsOpen.exists_iUnion_isCompact` or `isSigmaCompact_open`-type lemmas).
- The sets `Kₙ ∪ Ωᶜ` cover `ℂ`, and `μ(Kₙ ∪ Ωᶜ) ≤ μ Kₙ + μ Ωᶜ < ∞` by `finite_of_compact` and `carried`.
- Conclude with `Measure.sigmaFinite_of_countable`, or by building a `FiniteSpanningSetsIn` directly.

**`harmonicOnNhd_sub`.**
- `φ₁ − φ₂` is continuous on `Ω`.
- For test `χ`:
  `∫ (φ₁−φ₂)Δχ = ∫ φ₁Δχ − ∫ φ₂Δχ = ∫χ dμ − ∫χ dμ = 0`.
  Splitting the integral uses `integral_sub` with `integrable_mul` (`f = Δχ`, which is continuous with compact support inside `tsupport χ ⊆ Ω`).
- Apply §2. ∎

**`add_harmonic`.**
- `H` is `C²` on `Ω` (`HarmonicOnNhd.contDiffOn`) with `ΔH = 0` on `Ω`. By 1.3, `∫ H Δχ = ∫ ΔH χ = 0`.
- Continuity, `finite_of_compact` and `carried` are unchanged. ∎

**`isSubharmonicWeight_of_contDiffOn`.**
- Continuity: from `hu`.
- `ΔU` is continuous on `Ω`. Since `u ∈ C²` on the open `Ω`, the second Fréchet derivative is continuous there.
- **Finite on compacts.** `∫⁻_K 1_Ω ofReal(Δu) ≤ (sup_K Δu) · vol K < ∞` for compact `K ⊆ Ω` (`IsCompact.exists_bound_of_continuousOn`).
- **Carried.** `withDensity` of an indicator of `Ω` vanishes on `Ωᶜ` (`withDensity_apply`, `setLIntegral_indicator`).
- **Identity.** `∫ uΔχ = ∫ Δu χ` by 1.3. Then
  `∫ χ d(withDensity …) = ∫ (1_Ω ofReal Δu).toReal · χ = ∫ Δu χ`.
  The first equality is `integral_withDensity_eq_integral_toReal_smul`, valid since the density is measurable and finite. The second holds because `Δu ≥ 0` on `Ω` and `χ = 0` off `Ω`. ∎

**`sub_contDiffOn`.** Write `ν = ν₀ + volume.withDensity g` and `g' = g − 1_Ω ofReal(Δu)` (`ENNReal` truncated subtraction, pointwise).
- **Continuity:** clear.
- **Carried.**
  - `ν Ωᶜ = 0` gives `ν₀ Ωᶜ = 0` and `∫⁻_{Ωᶜ} g = 0`.
  - `g' ≤ g`, so `withDensity g' (Ωᶜ) = 0` too.
- **Finite on compacts:** monotonicity, `g' ≤ g`.
- **Identity.** For test `χ`:
  `∫ (ψ − u)Δχ = ∫ ψΔχ − ∫ uΔχ = ∫χ dν₀ + ∫ χ g.toReal − ∫ Δu χ`.
  This uses `integrable_mul` and 1.3. The middle term is `integral_withDensity_eq_integral_toReal_smul`. Its finiteness hypothesis: `g < ∞` a.e., because `∫⁻_K g < ∞` for compact `K ⊆ Ω` and `g = 0` a.e. on `Ωᶜ`.
- **Pointwise on `Ω`.** On `Ω`, `ofReal(Δu) ≤ g` with `Δu ≥ 0`. Where `g < ∞`, this gives `(g − ofReal Δu).toReal = g.toReal − Δu` (`ENNReal.toReal_sub_of_le`).
- **Conclude.** `∫ χ g.toReal − ∫ Δu χ = ∫ χ g'.toReal = ∫ χ d(withDensity g')`. Then `∫χ dν₀ + ∫χ d(withDensity g') = ∫ χ d(ν₀ + withDensity g')` (`integral_add_measure`; integrability on each part follows from finiteness on `tsupport χ`). ∎

---

## 4. Smoothed point masses and local potentials (`Potential/Local.lean`)

### 4.1 Definitions and statements

```lean
/-- `G_s = −(1/4π) wFun (s²/4) s² ≥ 0`: `Δ G_s = bumpKernel s − δ₀`, `G_s = 0` off `ball 0 s`. -/
def bumpPot (s : ℝ) (x : ℂ) : ℝ := -(4 * Real.pi)⁻¹ * wFun (s ^ 2 / 4) (s ^ 2) x

theorem contDiff_bumpKernel {s : ℝ} (hs : 0 < s) : ContDiff ℝ (⊤ : ℕ∞) (bumpKernel s)
theorem bumpKernel_nonneg {s : ℝ} (hs : 0 < s) (x : ℂ) : 0 ≤ bumpKernel s x
theorem bumpKernel_eq_zero {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : s ≤ ‖x‖) : bumpKernel s x = 0
theorem integral_bumpKernel {s : ℝ} (hs : 0 < s) : ∫ x, bumpKernel s x = 1
theorem bumpKernel_le {s : ℝ} (hs : 0 < s) (x : ℂ) :
    bumpKernel s x ≤ 4 / (Real.pi * s ^ 2) * (ball (0 : ℂ) s).indicator 1 x
theorem le_bumpKernel {s : ℝ} (hs : 0 < s) (x : ℂ) :
    1 / (Real.pi * s ^ 2) * (ball (0 : ℂ) (s / 2)).indicator 1 x ≤ bumpKernel s x
theorem measurable_bumpKernel : Measurable (Function.uncurry bumpKernel)

theorem bumpPot_nonneg {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : x ≠ 0) : 0 ≤ bumpPot s x
theorem bumpPot_eq_zero {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : s ≤ ‖x‖) : bumpPot s x = 0
theorem bumpPot_eq {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : x ≠ 0) :
    bumpPot s x = (4 * Real.pi)⁻¹ *
      (Real.log (s ^ 2 / ‖x‖ ^ 2) - sFun (1 / 4) 1 (‖x‖ ^ 2 / s ^ 2))
theorem exists_bumpPot_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ s : ℝ, 0 < s → ∀ x : ℂ, x ≠ 0 → ‖x‖ < s →
    bumpPot s x ≤ (4 * Real.pi)⁻¹ * (Real.log (s ^ 2 / ‖x‖ ^ 2) + C₀)
theorem continuousOn_bumpPot_uncurry :
    ContinuousOn (Function.uncurry bumpPot) {p : ℝ × ℂ | 0 < p.1 ∧ p.2 ≠ 0}
theorem measurable_bumpPot : Measurable (Function.uncurry bumpPot)
theorem exists_integral_abs_bumpPot_le : ∃ C₁ : ℝ, ∀ s : ℝ, 0 < s →
    Integrable (bumpPot s) ∧ ∫ x, |bumpPot s x| ≤ C₁ * s ^ 2

/-- **The smoothed point mass.** `Δ_z G_s(z − ζ) = bumpKernel s (· − ζ) − δ_ζ` weakly. -/
theorem integral_bumpPot_mul_laplacian {s : ℝ} (hs : 0 < s) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (ζ : ℂ) :
    ∫ z, bumpPot s (z - ζ) * Laplacian.laplacian χ z =
      ∫ z, bumpKernel s (z - ζ) * χ z - χ ζ

/-- Density of the smoothed measure `σ̃ = ∫ bumpKernel_{s(ζ)}(· − ζ) dσ(ζ)`. -/
def smoothedDensity (σ : Measure ℂ) (s : ℂ → ℝ) (x : ℂ) : ℝ≥0∞ :=
  ∫⁻ ζ, ENNReal.ofReal (bumpKernel (s ζ) (x - ζ)) ∂σ

/-- The local potential `V(z) = ∫ G_{s(ζ)}(z − ζ) dσ(ζ)`, with `ΔV = σ̃ − σ`. -/
def localPot (σ : Measure ℂ) (s : ℂ → ℝ) (z : ℂ) : ℝ :=
  ∫ ζ, bumpPot (s ζ) (z - ζ) ∂σ

/-- Standing hypotheses for a local potential on the open set `Ω`. -/
structure IsLocalPotData (Ω : Set ℂ) (σ : Measure ℂ) (s : ℂ → ℝ) : Prop where
  isOpen : IsOpen Ω
  measurable : Measurable s
  pos : ∀ ζ ∈ Ω, 0 < s ζ
  bdd : ∃ S : ℝ, ∀ ζ, s ζ ≤ S
  ball_subset : ∀ ζ ∈ Ω, ball ζ (s ζ) ⊆ Ω
  carried : σ Ωᶜ = 0
  sFinite : SFinite σ
  noAtoms : ∀ z, σ {z} = 0
  locFin : ∀ K ⊆ Ω, IsCompact K → σ {ζ | ∃ z ∈ K, dist z ζ < s ζ} < ∞
  logSmall : ∀ K ⊆ Ω, IsCompact K → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
    ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂σ ≤ ENNReal.ofReal η

namespace IsLocalPotData
variable {Ω : Set ℂ} {σ : Measure ℂ} {s : ℂ → ℝ}
theorem measurable_smoothedDensity (h : IsLocalPotData Ω σ s) :
    Measurable (smoothedDensity σ s)
theorem smoothedDensity_eq_zero (h : IsLocalPotData Ω σ s) {x : ℂ} (hx : x ∉ Ω) :
    smoothedDensity σ s x = 0
theorem lintegral_smoothedDensity_lt_top (h : IsLocalPotData Ω σ s) {K : Set ℂ} (hK : K ⊆ Ω)
    (hKc : IsCompact K) : ∫⁻ x in K, smoothedDensity σ s x < ∞
theorem measure_lt_top (h : IsLocalPotData Ω σ s) {K : Set ℂ} (hK : K ⊆ Ω)
    (hKc : IsCompact K) : σ K < ∞
theorem localPot_nonneg (h : IsLocalPotData Ω σ s) (z : ℂ) : 0 ≤ localPot σ s z
theorem continuousOn_localPot (h : IsLocalPotData Ω σ s) : ContinuousOn (localPot σ s) Ω
/-- **`ΔV = σ̃ − σ` weakly.** -/
theorem integral_localPot_mul_laplacian (h : IsLocalPotData Ω σ s) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ Ω) :
    ∫ z, localPot σ s z * Laplacian.laplacian χ z =
      ∫ z, χ z ∂(volume.withDensity (smoothedDensity σ s)) - ∫ z, χ z ∂σ
end IsLocalPotData

/-- **Pointwise bound** (`C₀` universal, from `exists_bumpPot_le`). -/
theorem exists_localPot_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (Ω : Set ℂ) (σ : Measure ℂ) (s : ℂ → ℝ),
    IsLocalPotData Ω σ s → ∀ z : ℂ,
      ENNReal.ofReal (localPot σ s z) ≤
        ∫⁻ ζ in {ζ | dist z ζ < s ζ},
          ENNReal.ofReal ((4 * Real.pi)⁻¹ * (Real.log (s ζ ^ 2 / ‖z - ζ‖ ^ 2) + C₀)) ∂σ
```

**Junk values.**
- **At `x = 0`.** `bumpPot s 0 = −(4π)⁻¹ sFun (s²/4) s² 0`, since Lean has `log 0 = 0`. This finite junk value is harmless:
  - every statement about `bumpPot s x` assumes `x ≠ 0`;
  - in `localPot` the point `ζ = z` is `σ`-null (`noAtoms`).
- **Non-integrable `ζ`-integrand.** If the `ζ`-integrand were not `σ`-integrable, `localPot` would be `0`. The bounds below show that it is integrable for every `z`, because the integrand is `≥ 0` and its lintegral is finite. In any case `localPot_nonneg` holds for every `z`, and `exists_localPot_le` is stated with `ofReal` and `∫⁻`, so it is true without integrability.
- **`logSmall`.** It is written with `log(1/‖z − ζ‖)`, which takes the junk value `0` at `ζ = z`. That point is again `σ`-null.

**Why the hypotheses.**
- `bdd`, `locFin`: Fubini for the weak Laplacian (4.4).
- `noAtoms`, `logSmall`: continuity (4.5).
- `ball_subset`: `σ̃` is carried by `Ω`.

M04 checks them for the measures it uses, from M03.

### 4.2 Proofs for `bumpKernel`, `bumpPot`

Write `a = s²/4`, `b = s²`, so `0 < a < b` for `s > 0`, and `√b = s`, `√a = s/2` (`Real.sqrt_sq`, `Real.sqrt_div`).

**Properties of `bumpKernel`.**
- `contDiff_bumpKernel`, `bumpKernel_nonneg`, `integral_bumpKernel`: `contDiff_kernel`, `kernel_nonneg`, `integral_kernel`.
- `bumpKernel_eq_zero`: `kernel_eq_zero`, with `s ≤ ‖x‖ ⇒ s² ≤ ‖x‖²`.
- `bumpKernel_le`: `kernel_le_indicator`, with `(π a)⁻¹ = 4/(π s²)`.
- `le_bumpKernel`: `indicator_le_kernel`, with `(π b)⁻¹ = 1/(πs²)`.
- `measurable_bumpKernel`. For `s ≠ 0`, `kernel_scale` (with `ε = |s|`, `a = 1/4`, `b = 1`) gives
  `bumpKernel s x = s⁻² · kernel (1/4) 1 (x/|s|)`.
  - This is jointly continuous on `{s ≠ 0}`, and `bumpKernel 0 = 0` (`profMass 0 0 = 0`, division by `0`).
  - Hence the function is piecewise measurable: `Measurable.piecewise` on `{p | p.1 = 0}`.
  - `bumpKernel s` depends only on `s²`, so use `|s|`.

**Properties of `bumpPot`.**
- `bumpPot_nonneg`: `wFun_nonpos` (`x ≠ 0`).
- `bumpPot_eq_zero`: `wFun_eq_zero` (`s² ≤ ‖x‖²`).
- `bumpPot_eq`. `wFun a b x = log‖x‖² + sFun (s²·¼) (s²·1) ‖x‖²` (rewrite `s²/4 = s²·(1/4)`). By `sFun_scale` (`ε = s`):
  `sFun (s²·¼)(s²·1) t = sFun ¼ 1 (t/s²) − log s²`.
  With `log(s²/‖x‖²) = log s² − log ‖x‖²` (`Real.log_div`, both positive), the formula follows.
- `exists_bumpPot_le`.
  - `exists_abs_sFun_le` (plane instance `a = 1/4`, `b = 1`, `B = 1`) gives `C` with `|sFun ¼ 1 t| ≤ C` on `[0,1]`.
  - For `0 < ‖x‖ < s`, `t = ‖x‖²/s² ∈ (0,1)`, so `−sFun ¼ 1 t ≤ C`.
  - Take `C₀ = max C 0`.
- `continuousOn_bumpPot_uncurry`. On `{s > 0, x ≠ 0}` use `bumpPot_eq`: `log`, division and the continuous `sFun ¼ 1` (`contDiff_sFun`) are continuous where the arguments are positive. Conclude with `ContinuousOn.congr`.
- `measurable_bumpPot`. `bumpPot s` depends only on `s²`.
  - On `{s ≠ 0, x ≠ 0}` the function is continuous: `bumpPot_eq` with `|s|`.
  - On `{s = 0}` it equals `−(4π)⁻¹ log‖x‖²`: `planeProfile 0 0 = 0`, so `sFun 0 0 t = −log 0 + 0 = 0`.
  - On `{x = 0, s ≠ 0}` it equals `(4π)⁻¹(log s² − sFun ¼ 1 0)`: `sFun_scale` at `t = 0`.
  - Glue with `Measurable.piecewise`.
- `exists_integral_abs_bumpPot_le`.
  - **Scaling.** For `x ≠ 0` and `s > 0`, `bumpPot s x = bumpPot 1 (x/s)` (`bumpPot_eq` twice). Hence `∫ |bumpPot s| = s² ∫ |bumpPot 1|`, by `Measure.integral_comp_smul` with `R = s⁻¹` (`finrank ℝ ℂ = 2`; `Complex.finrank_real_complex`).
  - **Integrability of `bumpPot 1`.** It is measurable. It vanishes off `ball 0 1`. On it, `0 ≤ bumpPot 1 x ≤ (4π)⁻¹(log(1/‖x‖²) + C₀)`, which is integrable on `ball 0 1` (1.1).
  - Take `C₁ := ∫ |bumpPot 1|`. Integrability of `bumpPot s` follows from the same scaling (`Integrable.comp_smul`).

**`integral_bumpPot_mul_laplacian`.**
- **Write `bumpPot` via the log.** By definition of `wFun`/`wFn`, for every `x` (no junk issue: it is the definition):
  `bumpPot s x = −(4π)⁻¹ (log ‖x‖² + S_s(‖x‖²))`, with `S_s = sFun a b`.
- **Log term.** By 1.2 (`log‖x‖² = 2 log‖x‖`), `∫ log‖z−ζ‖² Δχ(z) dz = 4πχ(ζ)`.
- **Smooth term.** `U(z) := S_s(‖z − ζ‖²)` is `C^∞`. By `lap_sFun_normSq` and `lap_comp_sub`, `ΔU(z) = 4 lap(S_s∘‖·‖²)(z − ζ) = −4π k_s(z − ζ)`. By BOC `integral_mul_lap` (×4), `∫ U Δχ = ∫ ΔU χ = −4π ∫ k_s(z−ζ) χ(z) dz`.
- **Combine.** `∫ bumpPot s (z−ζ) Δχ = −(4π)⁻¹(4πχ(ζ) − 4π∫ k_s(·−ζ)χ) = ∫ k_s(·−ζ) χ − χ(ζ)`.
- **Integrability** of each piece: `log‖·−ζ‖² Δχ` (1.1) and `U Δχ` (continuous, compact support). ∎

### 4.3 Measurability and the measure `σ̃`

Let `h : IsLocalPotData Ω σ s`.

**`measurable_smoothedDensity`.**
- The map `(x, ζ) ↦ ofReal(bumpKernel (s ζ) (x − ζ))` is measurable: `measurable_bumpKernel` composed with `(x,ζ) ↦ (s ζ, x − ζ)`.
- With `SFinite σ`, `Measurable.lintegral_prod_right'` gives measurability of `x ↦ ∫⁻ … ∂σ`.

**`smoothedDensity_eq_zero`.** Let `x ∉ Ω`.
- For `ζ ∈ Ω`, `x ∉ ball ζ (s ζ)` (`ball_subset`), so `‖x − ζ‖ ≥ s ζ > 0` and the kernel vanishes (`bumpKernel_eq_zero`).
- The set `Ωᶜ` is `σ`-null.
- So the integrand is `0` `σ`-a.e. (`lintegral_congr_ae`, `ae_restrict` of `carried`).

**`lintegral_smoothedDensity_lt_top`.** Let `A_K := {ζ | ∃ z ∈ K, dist z ζ < s ζ}`.
- **Tonelli.** `lintegral_lintegral_swap` gives `∫⁻_K f = ∫⁻ ζ, ∫⁻_K ofReal(k_{s(ζ)}(x−ζ)) dx dσ(ζ)`.
- **Inner integral.** For `ζ ∈ Ω ∖ A_K`, the inner integrand vanishes on `K`, since `‖x − ζ‖ ≥ s ζ` for `x ∈ K`. For `ζ ∈ Ω ∩ A_K` the inner integral is `≤ ∫ k_{s(ζ)} = 1`.
- **Conclude.** So `∫⁻_K f ≤ σ(A_K) < ∞` (`locFin`).

**`measure_lt_top`.** `K ∩ Ω ⊆ A_K`, since `dist ζ ζ = 0 < s ζ`, and `K ⊆ Ω`. So `σ K ≤ σ A_K < ∞`.

### 4.4 The weak Laplacian (`integral_localPot_mul_laplacian`)

Let `χ` be a `C²` test function with `tsupport χ =: K ⊆ Ω`, and `A := A_K`. Put `F(z, ζ) := bumpPot (s ζ) (z − ζ) · Δχ(z)`.

**Step 1 (integrability on `volume × σ`).**
- `F` is measurable (`measurable_bumpPot`).
- **Vanishing.** `F(z, ζ) = 0` unless `z ∈ K` and `ζ ∈ A`. Indeed `bumpPot (s ζ) (z−ζ) = 0` when `‖z − ζ‖ ≥ s ζ` (`ζ ∈ Ω`), and `Δχ = 0` off `K`.
- **Bound.** By Tonelli (`lintegral_prod`, `SFinite σ`):
  `∫⁻∫⁻ |F| ≤ ‖Δχ‖_∞ ∫⁻_{A} (∫ |bumpPot (s ζ)| dz) dσ(ζ) ≤ ‖Δχ‖_∞ C₁ S² σ(A) < ∞`.
  This uses `exists_integral_abs_bumpPot_le` and `bdd` (`s ζ ≤ S` and `0 < s ζ` on `Ω`, so `s ζ² ≤ S²`; `σ`-a.e. `ζ ∈ Ω`).
- Hence `Integrable (uncurry F) (volume.prod σ)` (`integrable_prod_iff`, or `Integrable` from finite lintegral of the norm).

**Step 2 (Fubini).** Since `F` is integrable on `volume × σ`, the function `ζ ↦ bumpPot (s ζ)(z − ζ)` is `σ`-integrable for a.e. `z ∈ K`. Hence, for a.e. `z`:
`localPot σ s z · Δχ(z) = ∫ F(z, ζ) dσ(ζ)`.
- For `z ∉ K` both sides are `0`.
- For a.e. `z ∈ K` the `ζ`-integral is genuine.

So, by `integral_integral_swap`:
`∫ localPot σ s z Δχ(z) dz = ∫∫ F(z,ζ) dσ dz = ∫ (∫ F(z,ζ) dz) dσ(ζ)`.

**Step 3 (inner integral).** For `ζ ∈ Ω`, by `integral_bumpPot_mul_laplacian` with `s = s ζ > 0`:
`∫ F(z, ζ) dz = ∫ k_{s(ζ)}(z − ζ) χ(z) dz − χ(ζ)`.

**Step 4.**
- **Split.** `∫ (∫ k_{s(ζ)}(z−ζ)χ(z) dz − χ(ζ)) dσ(ζ) = ∫∫ k_{s(ζ)}(z−ζ)χ(z) dz dσ(ζ) − ∫ χ dσ`.
- **Integrability of each piece.**
  - `χ` is bounded and supported in `K`, and `σ K < ∞` (`measure_lt_top`).
  - `(z, ζ) ↦ k_{s(ζ)}(z−ζ) χ(z)` is supported in `K × A` and bounded by `‖χ‖_∞ k_{s(ζ)}(z−ζ)`, whose double lintegral is `≤ ‖χ‖_∞ σ(A)`.
- **First term.** By `integral_integral_swap` again, it is `∫ χ(z) (∫ k_{s(ζ)}(z−ζ) dσ(ζ)) dz = ∫ χ(z) (smoothedDensity σ s z).toReal dz`. The `ζ`-integral of the nonnegative `k` equals the `toReal` of the lintegral where finite (`integral_eq_lintegral_of_nonneg_ae`); it is finite a.e. on `K` by `lintegral_smoothedDensity_lt_top`.
- **Rewrite.** That equals `∫ χ d(volume.withDensity (smoothedDensity σ s))`, by `integral_withDensity_eq_integral_toReal_smul`. Its hypotheses: `measurable_smoothedDensity`; and density `< ∞` a.e. (it is `0` off `Ω`, and locally integrable on `Ω`). ∎

### 4.5 Continuity (`continuousOn_localPot`)

Fix `z₀ ∈ Ω` and `ε > 0`. Let `C₀` be from `exists_bumpPot_le` and `S` from `bdd`. Choose `r₀ > 0` with `closedBall z₀ (4r₀) ⊆ Ω`, and put `K₀ := closedBall z₀ (4 r₀)`.

**Near part.** Put `η := ε/(4 Λ)` with `Λ := 1 + (4π)⁻¹(2 + |log(S²)| + C₀)`.
- `logSmall` on `K₀` gives `δ₁ ∈ (0, 1]` with `∫⁻_{ball z δ₁} (1 + log(1/‖z−ζ‖)) dσ ≤ η` for all `z ∈ K₀`.
- Let `δ := min(δ₁/3, r₀)`.
- For `z ∈ ball z₀ δ` we have `ball z₀ (2δ) ⊆ ball z (3δ) ⊆ ball z δ₁`.
- **Bound on `ball z₀ (2δ)`.** For a.e. `ζ ∈ ball z₀ (2δ)` (`ζ ≠ z`, `ζ ∈ Ω`):
  - `0 ≤ bumpPot(s ζ)(z − ζ)` (`bumpPot_nonneg`);
  - `bumpPot(s ζ)(z − ζ) ≤ (4π)⁻¹(log(S²) + 2 log(1/‖z−ζ‖) + C₀)` when `‖z−ζ‖ < s ζ`, and it is `0` otherwise;
  - since `‖z − ζ‖ < 1`, this is `≤ (4π)⁻¹(2 + |log S²| + C₀)(1 + log(1/‖z − ζ‖))`.
- Hence `0 ≤ ∫_{ball z₀ (2δ)} bumpPot(s ζ)(z−ζ) dσ(ζ) ≤ Λ η ≤ ε/4`, for every `z ∈ ball z₀ δ`, `z = z₀` included.

**Far part.** Let `Φ(z) := ∫_{(ball z₀ (2δ))ᶜ} bumpPot(s ζ)(z − ζ) dσ(ζ)`.
- **Domination.** For `z ∈ ball z₀ δ` and `ζ ∉ ball z₀ (2δ)`, `‖z − ζ‖ ≥ δ`. So the integrand is bounded by
  `B := (4π)⁻¹ max(0, log(S²/δ²) + C₀)`
  and vanishes unless `ζ ∈ A_{K₀}` (`K₀ ⊇ closedBall z₀ δ`). The dominating function `B · 1_{A_{K₀}}` is `σ`-integrable (`locFin`).
- **Continuity in `z`.** For each such `ζ ∈ Ω`, `z ↦ bumpPot(s ζ)(z−ζ)` is continuous on `ball z₀ δ`. It is evaluated at `z − ζ ≠ 0` with `s ζ > 0` (`continuousOn_bumpPot_uncurry`).
- By `continuousOn_of_dominated`, `Φ` is continuous on `ball z₀ δ`.

**Conclusion.**
- `localPot σ s = near + Φ` on `ball z₀ δ` (`integral_add_compl`). Both pieces are integrable: the near part by the bound, `Φ` by domination.
- `|localPot z − localPot z₀| ≤ |Φ(z) − Φ(z₀)| + ε/4 + ε/4 < ε` for `z` close to `z₀`. ∎

### 4.6 `localPot_nonneg`, `exists_localPot_le`

- **`localPot_nonneg`.** For `σ`-a.e. `ζ` we have `ζ ∈ Ω` and `ζ ≠ z` (`carried`, `noAtoms`), so the integrand is `≥ 0` (`bumpPot_nonneg`). Then `integral_nonneg_of_ae`. This is valid for every `z`; if the integrand is not integrable, the integral is `0`.
- **`exists_localPot_le`.**
  - `ofReal(∫ f dσ) ≤ ∫⁻ ofReal(f) dσ` (`ofReal_integral_le_lintegral_ofReal` if `f` is integrable; otherwise the left side is `ofReal 0 = 0`).
  - Pointwise, for `σ`-a.e. `ζ` (`ζ ∈ Ω`, `ζ ≠ z`):
    - if `dist z ζ < s ζ`, then `bumpPot(s ζ)(z−ζ) ≤ (4π)⁻¹(log(s ζ²/‖z − ζ‖²) + C₀)` (`exists_bumpPot_le`);
    - otherwise it is `0` (`bumpPot_eq_zero`).
  - Restrict the lintegral to `{ζ | dist z ζ < s ζ}`; this set is measurable (`measurable_dist`, `h.measurable`). ∎

---

## 5. Interface

**Assumed from M01** (copied BOC, namespace `OC`):
- `lap`;
- `lap_comp_sub`, `lap_comp_normSq`, `integral_mul_lap`;
- `integral_comp_normSq_sub`, `integrable_comp_normSq_sub`, `lintegral_comp_normSq_sub`, `volume_ball_complex`;
- `continuous_mul_of_tsupport_subset` (a real version may be needed; it is trivial to adapt).

**Copied by M02:** BOC `Potential/Radial.lean` → `OrtegaCerdaMultipliers/Potential/Radial.lean`.
- It depends only on BOC Wirtinger (`lap`, `lap_comp_normSq`, `lap_log_normSq`) and Polar, both in M01.
- **Action for the coordinator:** add it to the M01 copy list if M01 prefers to own all copies.

**Exported (consumers):**
- **M04:**
  - `bumpKernel` API, `IsLocalPotData`, `localPot`, `smoothedDensity`;
  - `IsLocalPotData.{continuousOn_localPot, integral_localPot_mul_laplacian, localPot_nonneg, smoothedDensity_eq_zero, measurable_smoothedDensity, lintegral_smoothedDensity_lt_top}`;
  - `exists_localPot_le`;
  - `IsSubharmonicWeight.{integrable_mul, sigmaFinite}`.
- **M07:**
  - `harmonicOnNhd_of_weakHarmonic`;
  - `integral_log_norm_sub_mul_laplacian` (`Δ (1/2π) log|z − λ| = δ_λ`) and its disc version `integral_log_pseudoHyp_mul_laplacian`;
  - `IsSubharmonicWeight.harmonicOnNhd_sub`, `add_harmonic`.
- **M08:** `integral_log_norm_sub_mul_laplacian`, `locallyIntegrable_log_norm_sub` (potentials of compactly supported signed measures `Δψ|_R − N Σ δ`).
- **M11, M12:**
  - `IsSubharmonicWeight.sub_contDiffOn`, for `ψ + c log(1−|z|²)`, `u = −c log(1−|z|²)`, `Δu = 4c/(1−|z|²)²`, and for `ψ − c|z|²`, `Δu = 4c`;
  - `isSubharmonicWeight_of_contDiffOn` (README §5 bridge lemma);
  - `integral_mul_laplacian_of_contDiffOn`.

### 5a. Interface (reconciled)

Lean files: `Potential/Radial.lean` (verbatim copy of BOC `Potential/Radial.lean`, fully proved), `Potential/Fundamental.lean`, `Potential/Weyl.lean`, `Potential/Local.lean`, and `Potential/GlobalKernels.lean` (Appendix A).
- **Weyl for `L¹_loc` functions.** `LogModulus.lean` applies `WeylLaplacianStmt` to `v − Σ n log|·−ζ|`, which is only `L¹_loc`, and M13 §4.2 assumes the same. So M02 also states `exists_harmonicOnNhd_ae_eq_of_weakHarmonic` (block in §2), whose statement is exactly the body of `WeylLaplacianStmt` (for every open `U`, in particular balls). The remark in §2 that the `L¹_loc` version is not needed is superseded.
- **M02 → M07.** `LogModulusWeak.lean` proves `weylLaplacian : WeylLaplacianStmt` and `logKernel : LogKernelStmt` from the M02 lemmas (term proofs). It also gives the unconditional `IsWeakLogModulus.logModulusBallwise` and `exists_analytic_norm_eq_exp_of_isWeakLogModulus`.
- **Requested by M13 §4.2**, in `Potential/Fundamental.lean`:

```lean
/-- Uniform local integrability of `log|z − a|` for `a` in a compact set. -/
theorem integrableOn_log_norm_sub_uniform {K K' : Set ℂ} (hK : IsCompact K)
    (hK' : IsCompact K') :
    ∃ M : ℝ, ∀ a ∈ K', IntegrableOn (fun z ↦ Real.log ‖z - a‖) K ∧
      ∫ z in K, |Real.log ‖z - a‖| ≤ M
/-- `Δ (∫ log|z − ζ| dν(ζ)) = 2π ν` weakly, for a finite measure with compact support. -/
theorem integral_logPotential_mul_laplacian (ν : Measure ℂ) [IsFiniteMeasure ν] {L : Set ℂ}
    (hL : IsCompact L) (hνL : ν Lᶜ = 0) (χ : ℂ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) :
    ∫ z, (∫ ζ, Real.log ‖z - ζ‖ ∂ν) * Laplacian.laplacian χ z = 2 * Real.pi * ∫ ζ, χ ζ ∂ν
```
- The `bumpKernel` API of §4.1 (`contDiff_bumpKernel` … `measurable_bumpKernel`) is in `Potential/Weyl.lean`, next to the definition, because Weyl's proof uses it. The statements are unchanged.
- `IsSubharmonicWeight.sigmaFinite` and `integral_mul_laplacian_of_contDiffOn` exist only here; M11 and M12 use them. M11's `ContDiff ℝ ⊤` test functions follow by `ContDiff.of_le`.

## 6. Issues found (for NOTEBOOK)

1. **p. 371, plane kernel, sign error.** Printed: `Re(ln|ζ| − z/ζ + ½ z²/ζ²)`. The Taylor expansion `log|ζ − z| = log|ζ| − Re(z/ζ) − ½Re(z²/ζ²) − …` requires `−½ z²/ζ²`.
   - With the printed `+`, `|k(z,ζ)| ≍ |z/ζ|²` as `ζ → ∞`, and `K[ν]` diverges logarithmically for `ν(D(0,r)) ≍ r²`.
   - With `−`, `|k| ≤ (3π)⁻¹|z/ζ|³` for `|ζ| ≥ max(1, 2|z|)`. Checked numerically: decay `R⁻²` versus `R⁻³`.
2. **p. 371–372, plane, `sup|φ − ψ| < ∞`.** The paper reduces `|K[μ₁] − K[μ̃₁]|` to `∫_{D(z,2R)} log(2R/|z−ζ|) dμ₁` via the mean-value property. For `|ζ| < 1 + 2R` this is false: the correction `(1 − χ_{D(0,1)}(ζ)) Re(…)` is not harmonic in `ζ` across `|ζ| = 1`.
   - The resulting error is a harmonic polynomial `a + Re(bz + cz²)` in `z`, generically with `(b, c) ≠ 0`, hence unbounded.
   - It is harmonic, so it can be subtracted from `ψ` without changing `Δψ`, but the paper does not do so.
   - The formalization uses compactly supported local potentials (§0), for which the claim holds as stated.
3. **p. 371, disc.**
   - **Growth bound.** "`μ₁(D(0,r)) ≲ (1−r)⁻²`" is true but too weak for the convergence of `K[ν]`, which needs `∫(1−|ζ|²)² dν < ∞`. Under `(1−r)⁻²` growth, the layer-cake integral diverges logarithmically. The true growth, `≍ (1−r)⁻¹` (hyperbolic unit cells), suffices.
   - **Correction term.** The precise erratum is the last display of p. 371: `|K[μ₁] − K[μ̃₁]| = |K[μ₁] − K[μ₁] ⋆ χ_{D(0,2R)}/|D(0,2R)||`. This commutes `K` with the (invariant) convolution, which is valid only for a translation-, resp. Möbius-, invariant kernel. The disc kernel's correction `(1−|ζ|²)(1/(1−z̄ζ) + 1/(1−zζ̄) − 1)` is neither invariant nor harmonic in `ζ`, and the same display fails in `ℂ` because of the cut-off (item 2). So the reduction to `∫_{D(z,2R)} log(2R/d) dμ₁` ([Chr91, 2.3]) is justified only for the logarithmic part. Not needed here (§0).
4. **p. 371, Andersson–Pascuas estimate.** It is correct. Proof and constant `4/π` in Appendix A, based on the identity `k = (1/4π)[log ρ² + (1−ρ²) + |z|²(1−|ζ|²)²/|1−ζ̄z|²]`, checked numerically.
5. **Normalisation.** `(1/4π) log|z − ζ|²` is the fundamental solution of the standard Laplacian, consistent with the paper's `K`.

---

## Appendix A. The paper's global kernels (documentation; not exported)

```lean
/-- Plane kernel of Lemma 6, sign of the quadratic term corrected. -/
def kPlane (z ζ : ℂ) : ℝ :=
  (4 * Real.pi)⁻¹ * Real.log (‖z - ζ‖ ^ 2) -
    (2 * Real.pi)⁻¹ * (if 1 ≤ ‖ζ‖ then
      Real.log ‖ζ‖ - (z / ζ).re - (z ^ 2 / (2 * ζ ^ 2)).re else 0)

/-- Disc kernel of Lemma 6 (as printed). -/
def kDisc (z ζ : ℂ) : ℝ :=
  (4 * Real.pi)⁻¹ * (Real.log (pseudoHyp ζ z ^ 2) +
    (1 - ‖ζ‖ ^ 2) * (1 / (1 - conj z * ζ) + 1 / (1 - z * conj ζ) - 1).re)

theorem kDisc_eq {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    kDisc z ζ = (4 * Real.pi)⁻¹ * (Real.log (pseudoHyp ζ z ^ 2) + (1 - pseudoHyp ζ z ^ 2) +
      ‖z‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2 / ‖1 - conj ζ * z‖ ^ 2)

/-- **Andersson–Pascuas estimate**, explicit constant. -/
theorem abs_kDisc_le {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) (hne : z ≠ ζ) :
    |kDisc z ζ| ≤ 4 / Real.pi * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) ^ 2 *
      (1 + Real.log (1 / pseudoHyp ζ z))

theorem abs_kPlane_le {z ζ : ℂ} (hζ : 1 ≤ ‖ζ‖) (hzζ : 2 * ‖z‖ ≤ ‖ζ‖) :
    |kPlane z ζ| ≤ (3 * Real.pi)⁻¹ * (‖z‖ / ‖ζ‖) ^ 3
```

**A.1 Harmonicity in `z`.**
- **Plane.** For fixed `ζ`, the correction term of `kPlane` is `Re` of a polynomial in `z`, so it is harmonic.
- **Disc.** `1/(1 − z̄ζ)` is antiholomorphic and `1/(1 − zζ̄)` is holomorphic in `z` on `𝔻`, so the correction is harmonic. Also `log|1 − ζ̄z|²` is harmonic on `𝔻`.
- **Fundamental solution.** In both cases `Δ_z k(·,ζ) = δ_ζ` weakly: §1 and `add_harmonic`.

**A.2 Identity (`kDisc_eq`).** Put `w := zζ̄`.
- **The correction.** `2Re(1/(1−w)) − 1 = (1 − |w|²)/|1−w|²`, so the correction equals `(1−|ζ|²)(1 − |z|²|ζ|²)/|1−zζ̄|²`.
- **Compare with `1 − ρ²`.** The classical identity `1 − ρ(ζ,z)² = (1−|z|²)(1−|ζ|²)/|1 − ζ̄z|²` (BOC `norm_one_sub_conj_mul_sq_sub`) gives
  `correction − (1 − ρ²) = (1−|ζ|²)|z|²(1 − |ζ|²)/|1−ζ̄z|²`.
- Checked numerically to `10⁻¹⁶`.

**A.3 Andersson–Pascuas (`abs_kDisc_le`).** Write `A := (1−|ζ|²)/|1−ζ̄z|` and `ρ := ρ(ζ, z) ∈ (0,1)`. Since `|1 − ζ̄z| ≥ 1 − |z| ≥ (1−|z|²)/2`:
`1 − ρ² = A (1−|z|²)/|1−ζ̄z| ≤ 2A`.
- **Case `ρ ≥ 1/2`.**
  - With `u := 1 − ρ² ≤ 3/4`: `|log(1 − u) + u| = |Σ_{n≥2} uⁿ/n| ≤ u²/(2(1−u)) ≤ 2u² ≤ 8A²`.
  - The third term of `kDisc_eq` is `≤ A²`.
  - Hence `|k| ≤ (9/4π) A²`.
- **Case `ρ < 1/2`.**
  - `1 − ρ² ≥ 3/4`, so `A ≥ 3/8` and `1 ≤ (64/9) A²`.
  - `|k| ≤ (1/4π)(2 log(1/ρ) + 1 + A²) ≤ (1/4π)(128/9 + 1) A² (1 + log(1/ρ))`.
- **Both cases:** `|k| ≤ (16/4π) A² (1 + log(1/ρ)) = (4/π) A²(1 + log 1/ρ)`. Numerically, the sharp ratio is `≈ 0.12`. ∎

**A.4 `abs_kPlane_le`.**
- With `w = z/ζ`, `|w| ≤ 1/2`: `kPlane z ζ = (1/2π)[log|1−w| + Re w + ½ Re w²] = −(1/2π) Re Σ_{n≥3} wⁿ/n`.
- Hence `|k| ≤ (1/6π)|w|³/(1−|w|) ≤ (1/3π)|w|³`. ∎

**A.5 Convergence classes and properties of `K[ν]`.** Let `ν` be a positive measure without atoms.
- **Plane.** Suppose `ν(D(0,r)) ≤ C(1 + r²)`.
  - **Far part.** By A.4 and dyadic layers: `∫_{|ζ| ≥ max(1,2|z|)} |k(z,ζ)| dν ≤ (3π)⁻¹|z|³ Σ_j 2^{-3j} ν(D(0,2^{j+1})) < ∞`, locally uniformly in `z`.
  - **Near part.** On the bounded set `|ζ| < max(1, 2|z|)`, `|k(z,ζ)| ≤ (1/4π)|log|z−ζ|²| + C_z`, with `C_z` locally bounded in `z`.
  - So `K[ν]` converges absolutely and locally uniformly as soon as `ν` is uniformly locally log-integrable (hypothesis `logSmall` of §4).
- **Disc.** Suppose `∫ (1−|ζ|²)² dν < ∞`, e.g. `ν(D(0,r)) ≲ (1−r)^{-1}`.
  - **Far part.** By A.3, on `ρ(ζ,z) ≥ 1/2` we have `|k| ≤ (4/π)(1+log 2) (1−|ζ|²)²/(1−|z|)²`.
  - **Near part.** On `ρ < 1/2` the integrand is `≲ 1 + log(1/ρ)`.
  - **Remark.** The paper's `(1−r)^{-2}` growth does **not** suffice (§6, item 3).
- **Continuity and the Laplacian.** Under these hypotheses, plus `logSmall`:
  - `K[ν]` is continuous: the proof of 4.5, with the near/far split and the far part dominated as above.
  - `ΔK[ν] = ν` weakly. For a test `χ` with support in a compact `L`, Fubini needs `∫ (∫_L |k(z,ζ)| dz) dν(ζ) < ∞`. This holds because `∫_L |k(z,ζ)| dz` is `O(|ζ|^{-3})` (plane), resp. `O((1−|ζ|²)²)` (disc), away from `L`, and bounded near `L`. Then use A.1 and §1 for each `ζ`.

  None of this is used: Lemma 6 is done with §4 (see M04).
