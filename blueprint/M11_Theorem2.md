# M11 — Theorem 2 (disc): weighted `L^p` and sup estimates, the printed form, and the bridge to BOC

**Lean file:** `OrtegaCerdaMultipliers/Theorem2.lean`. Optionally split off `Theorem2/Aux.lean` (the auxiliary weight and the partition) and `Theorem2/Bridge.lean` (§7).

**Paper:** Theorem 2 (p. 357); proof in §4.2 (pp. 372–374).

**Depends on:**
- M00: `IsSubharmonicWeight`, `IsLocallyDoublingDisc`, `hypBall`, `hypDist`, `massRadiusDisc`, `discMeasure`, `IsWeakDbarSol`.
- M01:
  - `hypBall_subset_ball`, `ball_subset_hypBall`, `hypDist_lt_iff`, `continuousOn_pseudoHyp`, `mem_hypBall` (`Foundations/Hyperbolic.lean`);
  - `one_sub_normSq_mobius`, `one_sub_conj_mul_self`, `one_sub_conj_mul_ne_zero_of_mem`, `lap_neg_log_one_sub_normSq` (DiscGeometry);
  - `integral_mul_dbar'`, `integral_mul_dz'`, `dbar_dz_cplx`, `dz_dbar_cplx`, `laplacian_eq_four_mul_lap`, `lap_const_mul` (Wirtinger, Basic);
  - `volume_ball_complex` (Polar).
- M03: growth of `μ(hypBall z R)` (`exists_hypBall_measure_gt`, §2.1).
- M04: Lemma 6 in `𝔻` (`lemma6_disc`, §2.1).
- M09: Proposition 2 in `𝔻` **with the global upper bound** (`prop2_disc_full`, §2.1).
- M10: `disc_kernel_operator`, `sigmaFinite_discMeasure`.
- Mathlib: `Measure.rnDeriv`, `withDensity_rnDeriv_eq`, `rnDeriv_le_one_of_le`, `withDensity_add_left`, `integral_add_measure`, `integral_smul_measure`, `integral_withDensity_eq_integral_toReal_smul`, `withDensity_absolutelyContinuous'`, `ContinuousOn.isOpen_inter_preimage`, `ContinuousOn.measurable_piecewise`.

---

## 0. The paper

**Theorem 2 (p. 357).** Let `φ` be subharmonic in `𝔻` such that `Δφ(D(z,r)) > 1` for some `r > 0` and all hyperbolic discs `D(z,r)`, and suppose `Δφ` is locally doubling for the hyperbolic distance. Then `∂̄u = f` has a solution with
- `∫_𝔻 |u|^p e^{−φ} dm/(1−|z|²) ≲ ∫_𝔻 |f(1−|z|²)|^p e^{−φ} dm/(1−|z|²)` for `p ∈ [1,∞)`;
- `sup |u| e^{−φ} ≲ sup |f(ζ)|(1−|ζ|) e^{−φ(ζ)}`.

**Proof (pp. 372–374), as printed.**
1. Assume `(1−|z|²)²Δφ > ε`, which is Lemma 6.
2. Set `ψ = φ − (ε/2) log(1−|z|²)`, "so that `(1−|z|²)²Δψ > ε/2`".
3. If `f` is supported away from the zeros of a multiplier `g` (`|g| ≃ e^ψ` there), put `u = g v` with `v` from Lemma 7 (`α = ε/2`) applied to `f/g`.
4. In general, take the multipliers `h_i` of Proposition 2, the partition `Ω_i` (`Ω_i := (E_{h_1} ∩ … ∩ E_{h_{i−1}}) ∖ E_{h_i}`), and

   `u(z) = ∫_𝔻 κ(z,ζ) f(ζ) dm(ζ)`, with `κ(z,ζ) = Σ_i h_i(z) χ_{Ω_i}(ζ)/h_i(ζ) · (1/π)(1−|ζ|²)/((1−ζ̄z)(z−ζ))`.
5. "Thus `|κ(z,ζ)| ≃ (1−|ζ|²)/(|1−ζ̄z||ζ−z|) · (1−|ζ|)^{ε/2} e^{φ(z)} / ((1−|z|)^{ε/2} e^{φ(ζ)})`. From this estimate the `L^p` boundedness of the solution follows."

---

## 1. Verification of the suspected issues

All formulas below were read from the page images (PDF pp. 3, 18–20).

### (a) The sign of the auxiliary weight: **confirmed**

The printed `ψ = φ − (ε/2) log(1−|z|²)` appears twice (p. 372 l. −12, p. 373 l. −13). The printed kernel bound (p. 374) is `e^{ψ(z)−ψ(ζ)} |K(z,ζ)|` for this `ψ`. Conjugate it to the operator that maps `F := f(1−|ζ|²)e^{−φ}` to `u e^{−φ}` on `ν := dm/(1−|z|²)` (both sides of Theorem 2 are norms on `L^p(ν)`):

`|k(z,ζ)| := e^{−φ(z)}|κ(z,ζ)|e^{φ(ζ)} ≃ P(z,ζ) := ((1−|ζ|)/(1−|z|))^{ε/2} (1−|ζ|²)/(|1−ζ̄z||ζ−z|)`.

Both Schur integrals of `P` diverge.
- **Sup estimate (`L^∞`).** For `|ζ| < 1/2`: `1−|ζ| ≥ 1/2`, `|1−ζ̄z| ≤ 2`, `|ζ−z| ≤ 2`. Hence

  `∫ P(z,ζ) dν(ζ) = (1−|z|)^{−ε/2} ∫_𝔻 (1−|ζ|)^{ε/2} dm(ζ)/(|1−ζ̄z||ζ−z|) ≥ (π/16) 2^{−ε/2} (1−|z|)^{−ε/2} → ∞` as `|z| → 1`.
- **`L^1`.** `|1−ζ̄z||ζ−z| ≤ 4` and `∫_𝔻 (1−|z|)^{−1−ε/2} dm = ∞`. Hence

  `∫ P(z,ζ) dν(z) ≥ (1/4)(1−|ζ|)^{ε/2}(1−|ζ|²) ∫_𝔻 (1−|z|)^{−ε/2}(1−|z|²)^{−1} dm(z) = ∞` for every `ζ`.

So the printed kernel estimate gives no `L^p` bound at all. In the paper's own scheme (step 3), `|u|e^{−φ} = |v||g|e^{−φ} ≃ |v|(1−|z|²)^{−ε/2}` while Lemma 7 controls `|v|(1−|z|)^{ε/2}`: off by `(1−|z|)^{−ε}`.

**Correction.** Take `ψ = φ' + c log(1−|z|²)` with `0 < c < 1` (with the correct sign).
- With the standard Laplacian, `Δ log(1−|z|²) = −4/(1−|z|²)²` (from `lap_neg_log_one_sub_normSq`). So `(1−|z|²)²Δψ = (1−|z|²)²Δφ' − 4c ≥ ε − 4c`.
- We take `c := min(ε/8, 1/2)`, so `(1−|z|²)²Δψ ≥ ε/2`.
- The paper writes `> ε/2`. That matches `ψ = φ + (ε/2)log(1−|z|²)` with the normalisation `Δ = ∂∂̄` (`∂∂̄ log(1−|z|²) = −(1−|z|²)^{−2}`). With the printed sign the bound would be `> 3ε/2`, so "`ε/2`" confirms that the sign is a typo.
- The conjugated kernel is then `|k| ≤ A M_c` with `M_c(z,ζ) = (1−|z|²)^c(1−|ζ|²)^{1−c}/(|1−ζ̄z||z−ζ|)`. Both Schur integrals are `≤ 24π/(c(1−c))` (M10 §3.3).

### (b) The `L^p` claim: **confirmed**

- **Where the printed proof breaks.** The step (p. 373) "`|g| ≲ e^ψ`, thus `∫|u|^p e^{−φ}/(1−|z|) ≲ ∫|u/g|^p (1−|z|)^{ε/2}/(1−|z|)`" uses `|u|^p e^{−φ} ≲ |u/g|^p e^{pψ−φ}`. With the corrected `ψ` this is `|u/g|^p e^{(p−1)φ}(1−|z|²)^{pc}`, and the factor `e^{(p−1)φ}` is unbounded. The printed estimate therefore follows from that step only for `p = 1`, and only with the corrected sign. The same holds for the next display (`|f/g|^p ≃ |f|^p e^{−pψ}`, not `e^{−φ}`).
- **`theorem2`.** It uses the normalisation `‖u e^{−φ}‖_{L^p(ν)} ≤ C‖f(1−|z|²)e^{−φ}‖_{L^p(ν)}` for **all** `p ∈ [1,∞]`, with **one** `u` and one `C`. The Schur test for the conjugated kernel `k`, with both its `L^1` bound (`sup_ζ ∫|k| dν(z)`) and its `L^∞` bound (`sup_z ∫|k| dν(ζ)`), gives exactly this (M10 `disc_kernel_operator`).
- **`theorem2_printed`.** Apply `theorem2` to `(φ/p, μ/p)`:
  - `‖u e^{−φ/p}‖_p^p = ∫|u|^p e^{−φ} dν` and `‖f(1−|z|²)e^{−φ/p}‖_p^p = ∫|f(1−|z|²)|^p e^{−φ} dν`.
  - `(φ/p, μ/p)` satisfies the hypotheses.
    - `IsSubharmonicWeight`: linearity.
    - Local doubling: same constant (`IsLocallyDoublingDisc.smul`).
    - Mass: `μ(hypBall z R)/p > 1` needs `μ(hypBall z R) > p`, which holds for `R` large by M03's growth lemma. Its hypothesis is `μ(hypBall z r) ≥ 1`, true by `hm`.
  - Both `u` and `C` depend on `p`. Whether one `u` can satisfy the printed estimate for all `p` simultaneously is not claimed. The paper's operator for fixed `φ` has the conjugated kernel `e^{(1−1/p)(φ(z)−φ(ζ))}|k_φ|` in that normalisation, which is unbounded in general.

### Further errata on pp. 372–374

- **p. 372.** The multiplier bound is printed `d/ρ ≲ |g|e^{−ψ} ≲ (d/ρ)^M`, the inequalities in the wrong order, as in Theorem 4 (p. 363). It should read `(d/ρ)^M ≲ |g|e^{−ψ} ≲ d/ρ`.
- **p. 374.** `|κ(z,ζ)| ≃ …`: only `≲` holds, since `κ(z,ζ) = 0` when `ζ ∈ Ω_i` and `h_i(z) = 0`.
- **The proof needs `|h_i(z)| ≲ e^{ψ(z)}` for *all* `z`,** not only off `E_{h_i}`. The paper has it from "satisfying the conclusion of Theorem 4" together with the Remark `d(z,Λ) ≲ ρ(z)` (p. 363). The fixed formal `prop2_disc` states the two-sided bound only on the good set. **It is not sufficient for Theorem 2**; M09 must export `prop2_disc_full` (§2.1).
- **Lemma 6 is used silently.** "We take an arbitrary weight φ under the hypothesis of Theorem 2, that is `(1−|z|²)²Δφ > ε`" is Lemma 6 (`ψ` equivalent to `φ`). In the formal proof the bounded difference `|φ−φ'| ≤ B` enters the constant as `e^{2B}`.

---

## 2. Statements (namespace `OC`)

All statements typecheck (scratch file `m11_check.lean`, which contains M10's statements as well; imports `Defs`, `Foundations.Basic`).

### 2.1 Assumed from other modules (exact form required)

```lean
/-- The hyperbolic area measure `dm(z)/(1-|z|²)²` on `𝔻`. Proposed shared definition; it must
live in the earliest module that uses it (M04). -/
def hypArea : Measure ℂ :=
  (volume.restrict 𝔻).withDensity fun z ↦ ENNReal.ofReal ((1 - ‖z‖ ^ 2)⁻¹ ^ 2)

/-- (M04) Lemma 6 in the disc. -/
theorem lemma6_disc (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ) (ε B : ℝ), 0 < ε ∧ IsSubharmonicWeight 𝔻 φ' μ' ∧
      IsLocallyDoublingDisc μ' ∧ ENNReal.ofReal ε • hypArea ≤ μ' ∧
      ∀ z ∈ 𝔻, |φ z - φ' z| ≤ B

/-- (M03) Growth of hyperbolic balls: any measure with a uniform positive lower bound on
the balls of one radius has arbitrarily large mass on the balls of a larger radius. -/
theorem exists_hypBall_measure_gt {μ : Measure ℂ} {r m₀ : ℝ} (hr : 0 < r) (hm₀ : 0 < m₀)
    (h : ∀ z ∈ 𝔻, ENNReal.ofReal m₀ ≤ μ (hypBall z r)) (M : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, ENNReal.ofReal M < μ (hypBall z R)

/-- (M09) Proposition 2 in the disc, with the global upper bound `|h_i| ≤ C e^ψ` on `𝔻`. -/
theorem prop2_disc_full (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight 𝔻 ψ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z R)) :
    ∃ (n : ℕ) (h : Fin n → ℂ → ℂ) (ε : ℝ) (C : ℝ), 0 < ε ∧ 0 < C ∧
      (∀ i, DifferentiableOn ℂ (h i) 𝔻) ∧
      (∀ z ∈ 𝔻, ∃ i, ∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) ∧
      (∀ i, ∀ z ∈ 𝔻, ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
      ∀ i, ∀ z ∈ 𝔻, (∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) →
        C⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖
```

Notes on these assumptions.
- **`hypArea`.** M01 has `invDensity ζ = (π(1−|ζ|²)²)⁻¹`, so `hypArea = π · (volume.restrict 𝔻).withDensity invDensity`. If M04 uses another normalisation, only the constants `ε` and `π/900` (§4.5) change.
- **`lemma6_disc`.** The paper's Lemma 6 in `𝔻` gives `ε < (1−|z|²)²μ̃₁` (p. 371); `μ' = μ̃₁ + μ₂ ≥ μ̃₁`. If M04 also exports the mass condition for `μ'`, the growth step in §4.8 can be skipped.
- **`exists_hypBall_measure_gt`** needs no doubling: if `hypBall z ((2k+1)r)` contains `k+1` disjoint balls of radius `r` (points along a geodesic, hyperbolic triangle inequality `hypDist_triangle`), its mass is `≥ (k+1)m₀`. The any-measure form is stronger than needed. Every use here has a locally doubling `μ`, so M03 may state the weaker doubling version: with `1 < μ(hypBall z r)`, apply it to `(2/m₀)•μ`.
- **`prop2_disc_full` versus the fixed `prop2_disc`.** The only difference is the conjunct `∀ i, ∀ z ∈ 𝔻, ‖h i z‖ ≤ C * exp (ψ z)`. It is **not** derivable from `prop2_disc`: on the region where `G_i = ∅`, nothing is known about `h_i`. It is part of the paper's Proposition 2 ("satisfying the conclusion of Theorem 4", plus `d(z,Λ) ≲ ρ(z)`), and M08/M09's construction gives it. Then `prop2_disc` is the corollary that drops one conjunct.

### 2.2 Exported helpers

```lean
theorem Measure.exists_add_eq_of_le {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [SigmaFinite μ] (h : ν ≤ μ) : ∃ d : Measure X, d + ν = μ

theorem IsSubharmonicWeight.sigmaFinite {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    {μ : Measure ℂ} (hφ : IsSubharmonicWeight Ω φ μ) : SigmaFinite μ

theorem integral_mul_laplacian_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {U : ℂ → ℝ}
    (hU : ContDiffOn ℝ 2 U Ω) {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ω) :
    ∫ z, U z * Laplacian.laplacian χ z = ∫ z, Laplacian.laplacian U z * χ z

theorem integral_log_one_sub_normSq_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ 𝔻) :
    ∫ z, Real.log (1 - ‖z‖ ^ 2) * Laplacian.laplacian χ z = -(4 * ∫ z, χ z ∂hypArea)

theorem one_sub_normSq_le_of_mem_hypBall {z w : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr1 : r ≤ 1)
    (hw : w ∈ hypBall z r) : 1 - ‖z‖ ^ 2 ≤ 12 * (1 - ‖w‖ ^ 2)

theorem hypArea_hypBall_ge {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (Real.pi * r ^ 2 / 900) ≤ hypArea (hypBall z r)

theorem hypArea_hypBall_le {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    hypArea (hypBall z r) ≤ ENNReal.ofReal (46656 * Real.pi * r ^ 2)

theorem IsLocallyDoublingDisc.of_le_of_le {μ ν : Measure ℂ} (hμ : IsLocallyDoublingDisc μ)
    {a b : ℝ≥0∞} (ha : a ≠ 0) (hb : b ≠ ∞) (h₁ : a • μ ≤ ν) (h₂ : ν ≤ b • μ) :
    IsLocallyDoublingDisc ν

theorem isLocallyDoublingDisc_hypArea : IsLocallyDoublingDisc hypArea

theorem isSubharmonicWeight_add_log {φ' : ℂ → ℝ} {ν : Measure ℂ} {ε c : ℝ} (hc : 0 ≤ c)
    (hcε : 4 * c ≤ ε) (hφ' : IsSubharmonicWeight 𝔻 φ' (ν + ENNReal.ofReal ε • hypArea)) :
    IsSubharmonicWeight 𝔻 (fun z ↦ φ' z + c * Real.log (1 - ‖z‖ ^ 2))
      (ν + ENNReal.ofReal (ε - 4 * c) • hypArea)

theorem exists_aux_weight_disc (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ (ψ : ℂ → ℝ) (μψ : Measure ℂ) (c B : ℝ), 0 < c ∧ c < 1 ∧ 0 ≤ B ∧
      IsSubharmonicWeight 𝔻 ψ μψ ∧ IsLocallyDoublingDisc μψ ∧
      (∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μψ (hypBall z R)) ∧
      ∀ z ∈ 𝔻, |ψ z - (φ z + c * Real.log (1 - ‖z‖ ^ 2))| ≤ B

theorem exists_measurable_partition {X : Type*} [MeasurableSpace X] {n : ℕ} {S : Set X}
    (hS : MeasurableSet S) (G : Fin n → Set X) (hG : ∀ i, MeasurableSet (G i))
    (hcov : ∀ z ∈ S, ∃ i, z ∈ G i) :
    ∃ Ω : Fin n → Set X, (∀ i, MeasurableSet (Ω i)) ∧ (∀ i, Ω i ⊆ G i ∩ S) ∧
      ∀ z ∈ S, ∃! i, z ∈ Ω i

theorem measurableSet_goodSet_disc (Z : Set ℂ) (ρ : ℂ → ℝ) (ε : ℝ) :
    MeasurableSet {z | z ∈ 𝔻 ∧ ∀ w ∈ Z, w ∈ 𝔻 → ε * ρ w ≤ hypDist z w}

/-- The holomorphic factor of the kernel of Theorem 2:
`H(z, ζ) = ∑ᵢ χ_{Ωᵢ}(ζ) hᵢ(z)/hᵢ(ζ) · (1 - |ζ|²)/(1 - ζ̄ z)`. -/
def thm2H {n : ℕ} (h : Fin n → ℂ → ℂ) (Ω : Fin n → Set ℂ) (z ζ : ℂ) : ℂ :=
  (∑ i, (Ω i).indicator (fun ζ ↦ h i z / h i ζ) ζ) *
    (((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) / (1 - conj ζ * z))

theorem exists_disc_solution_kernel (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight 𝔻 φ μ) (hd : IsLocallyDoublingDisc μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ (H : ℂ → ℂ → ℂ) (c A : ℝ), 0 < c ∧ c < 1 ∧ 0 ≤ A ∧ Measurable (Function.uncurry H) ∧
      (∀ ζ ∈ 𝔻, DifferentiableOn ℂ (fun z ↦ H z ζ) 𝔻) ∧ (∀ ζ ∈ 𝔻, H ζ ζ = 1) ∧
      ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) *
        ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖)

theorem IsSubharmonicWeight.div_const {Ω : Set ℂ} {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight Ω φ μ) {p : ℝ} (hp : 0 < p) :
    IsSubharmonicWeight Ω (fun z ↦ φ z / p) (ENNReal.ofReal p⁻¹ • μ)

theorem IsLocallyDoublingDisc.smul {μ : Measure ℂ} (h : IsLocallyDoublingDisc μ) (a : ℝ≥0∞) :
    IsLocallyDoublingDisc (a • μ)
```

### 2.3 Main statements (fixed in `comparator/statements.lean`)

`theorem2` and `theorem2_printed`, verbatim from `comparator/statements.lean` (typechecked again in the scratch file).

### 2.4 The bridge to BOC (§7)

```lean
/-- The Riesz measure of `ψ₀ / 2` for `ψ₀ ∈ C²(𝔻)`: `Δ(ψ₀/2) dm = 2 lap ψ₀ dm` on `𝔻`
(`lap = ¼Δ`, BOC's convention). -/
def bridgeMeasure (ψ₀ : ℂ → ℝ) : Measure ℂ :=
  (volume.restrict 𝔻).withDensity fun z ↦ ENNReal.ofReal (2 * lap ψ₀ z)

theorem bridge_isSubharmonicWeight {ψ₀ : ℂ → ℝ} (hψ : ContDiffOn ℝ 2 ψ₀ 𝔻)
    (hpos : ∀ z ∈ 𝔻, 0 ≤ lap ψ₀ z) :
    IsSubharmonicWeight 𝔻 (fun z ↦ ψ₀ z / 2) (bridgeMeasure ψ₀)

theorem bridge_le_le {ψ₀ : ℂ → ℝ} {δ M : ℝ} (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z)
    (hup : ∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) :
    ENNReal.ofReal (2 * δ) • hypArea ≤ bridgeMeasure ψ₀ ∧
      bridgeMeasure ψ₀ ≤ ENNReal.ofReal (2 * M) • hypArea

theorem bridge_isLocallyDoublingDisc {ψ₀ : ℂ → ℝ} {δ M : ℝ} (hδ : 0 < δ)
    (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) (hup : ∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) :
    IsLocallyDoublingDisc (bridgeMeasure ψ₀)

theorem bridge_mass {ψ₀ : ℂ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < bridgeMeasure ψ₀ (hypBall z R)

/-- The corollary for BOC, with a constant depending on `ψ₀`. -/
theorem dbar_sup_estimate_C2 {ψ₀ : ℂ → ℝ} (hψ : ContDiffOn ℝ 2 ψ₀ 𝔻) {δ M : ℝ} (hδ : 0 < δ)
    (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) (hup : ∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ 𝔻 → ∃ W : ℂ → ℂ, IsWeakDbarSol 𝔻 W g ∧ ∀ B : ℝ,
        (∀ ζ ∈ 𝔻, ‖g ζ‖ * (1 - ‖ζ‖) * Real.exp (-ψ₀ ζ / 2) ≤ B) →
        ∀ᵐ z ∂(volume.restrict 𝔻), ‖W z‖ * Real.exp (-ψ₀ z / 2) ≤ C * B

/-- The corollary BOC actually needs: `C` depends only on `δ` and `M`. NOT derivable from the
fixed statements; needs `prop2_disc_unif` (§8.3). -/
theorem dbar_sup_estimate_C2_uniform {δ M : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ₀ : ℂ → ℝ, ContDiffOn ℝ 2 ψ₀ 𝔻 → (∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) →
      (∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) → ∀ g : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g → tsupport g ⊆ 𝔻 → ∃ W : ℂ → ℂ, IsWeakDbarSol 𝔻 W g ∧ ∀ B : ℝ,
        (∀ ζ ∈ 𝔻, ‖g ζ‖ * (1 - ‖ζ‖) * Real.exp (-ψ₀ ζ / 2) ≤ B) →
        ∀ᵐ z ∂(volume.restrict 𝔻), ‖W z‖ * Real.exp (-ψ₀ z / 2) ≤ C * B

/-- PROPOSED for M09: Proposition 2 with constants uniform over weights comparable to the
hyperbolic area. -/
theorem prop2_disc_unif {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ (n : ℕ) (ε C : ℝ), 0 < ε ∧ 0 < C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      IsSubharmonicWeight 𝔻 ψ μ → ENNReal.ofReal a • hypArea ≤ μ →
      μ ≤ ENNReal.ofReal b • hypArea →
      ∃ h : Fin n → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (h i) 𝔻) ∧
        (∀ z ∈ 𝔻, ∃ i, ∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) ∧
        (∀ i, ∀ z ∈ 𝔻, ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
        ∀ i, ∀ z ∈ 𝔻, (∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) →
          C⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖
```

`invLap ψ₀ = (1−‖z‖²)² · lap ψ₀` (M01 `Foundations/Basic.lean`, copied from BOC), so `δ ≤ invLap ψ₀ ≤ M` is BOC's hypothesis verbatim.

**Count:**
- 3 definitions (`hypArea`, `thm2H`, `bridgeMeasure`);
- 23 theorems: 16 helpers, 2 main, 5 bridge;
- `dbar_sup_estimate_C2_uniform` (stated, flagged) and `prop2_disc_unif` (proposal for M09).

All typecheck. Assumed: 3 theorems (from M03, M04, M09).

---

## 3. Architecture of the proof of `theorem2`

```
lemma6_disc (M04) ──► exists_aux_weight_disc ──► prop2_disc_full (M09) on (ψ, μψ)
                          │                            │
                          │                            ▼
                          │        good sets G_i ─► exists_measurable_partition ─► Ω_i
                          ▼                            │
                |ψ − φ − c log(1−|z|²)| ≤ B            ▼
                          └──────────► exists_disc_solution_kernel  (H = thm2H h̃ Ω)
                                                   │
                                                   ▼
                                 M10 disc_kernel_operator  ──►  theorem2
```

---

## 4. Proofs of the helpers

### 4.1 `Measure.exists_add_eq_of_le`

Let `g := ν.rnDeriv μ`.
- `ν ≤ μ` gives `ν ≪ μ` (`Measure.absolutelyContinuous_of_le`).
- `ν` is σ-finite (`sigmaFinite_of_le`), so `HaveLebesgueDecomposition ν μ` holds by instance.
- `withDensity_rnDeriv_eq ν μ hνμ : μ.withDensity g = ν`.
- `rnDeriv_le_one_of_le h : g ≤ᵐ[μ] 1`.

Put `d := μ.withDensity (1 − g)`. Then

`d + ν = μ.withDensity (1 − g) + μ.withDensity g = μ.withDensity ((1 − g) + g) = μ.withDensity 1 = μ`,

by `withDensity_add_left` (with `(measurable_const.sub (Measure.measurable_rnDeriv _ _))`), `withDensity_congr_ae` (pointwise `tsub_add_cancel_of_le` where `g ≤ 1`), and `withDensity_one`.

### 4.2 `IsSubharmonicWeight.sigmaFinite`

`μ(Ωᶜ) = 0`, and `μ(K) < ∞` for compact `K ⊆ Ω`. Write `Ω = ⋃ₙ Kₙ` with `Kₙ` compact.
- In the two cases used: `𝔻 = ⋃ₙ closedBall 0 (1 − 1/(n+2))` and `univ = ⋃ₙ closedBall 0 n`.
- In general: an open subset of `ℂ` is a countable union of compacts (e.g. `Kₙ = closedBall 0 n ∩ {z | 1/(n+1) ≤ infDist z Ωᶜ}` when `Ω ≠ univ`). Mathlib has no ready-made `IsOpen.isSigmaCompact`.

Then `{Kₙ ∪ Ωᶜ}ₙ` is a countable family of sets of finite measure covering `ℂ` (`sigmaFinite_of_countable`, with `Set.countable_range`). It is acceptable to prove only the cases `Ω = 𝔻` and `Ω = univ`.

### 4.3 `integral_mul_laplacian_of_contDiffOn`

This is the `Ω`-version of M01's `integral_mul_lap`, and the proof is the same with `isOpen_univ` replaced by `hΩ`.
- Pass to `ℂ` (`integral_complex_ofReal`).
- Write `Δ = 4 lap` (`laplacian_eq_four_mul_lap`), `lap U = ∂̄∂U` on `Ω` (`dbar_dz_cplx`, pointwise from `ContDiffAt ℝ 2 U z` for `z ∈ Ω`) and `lap χ = ∂∂̄χ` (`dz_dbar_cplx`).
- Integrate by parts twice on the open set `Ω`:
  - `integral_mul_dbar'` with `u := dz (cplx U)`, which is `ContDiffOn ℝ 1` on `Ω` (`ContDiffOn.fderiv_of_isOpen`, `contDiffOn_succ_iff_fderiv_of_isOpen`), and the test function `cplx χ`;
  - `integral_mul_dz'` with `u := cplx U`, `ContDiffOn ℝ 1` on `Ω`, and the test function `dbar (cplx χ)` (`contDiff_dbar`, `hasCompactSupport_dbar`, `tsupport_dbar_subset`).
- Both sides are genuine integrals: `U Δχ` and `ΔU χ` are continuous on `Ω` with compact support in `Ω` (`integrable_mul_of_tsupport_subset`).

### 4.4 `integral_log_one_sub_normSq_mul_laplacian`

`U := log(1−|z|²)` is `C^∞` on `𝔻` (`Real.contDiffOn_log` composed with `1 − ‖z‖²`, positive on `𝔻`).
- By `lap_neg_log_one_sub_normSq` and `lap_const_mul (−1)`: `lap U = −(1−|z|²)^{−2}`, so `ΔU = −4(1−|z|²)^{−2}` on `𝔻`.
- By §4.3: `∫ U Δχ = −4 ∫_𝔻 (1−|z|²)^{−2} χ dm`.
- That integral equals `∫ χ ∂hypArea` (`integral_withDensity_eq_integral_toReal_smul`, the density measurable and finite; `setIntegral_eq_integral_of_forall_compl_eq_zero` since `χ = 0` off `𝔻`).

### 4.5 Hyperbolic area of hyperbolic discs

Throughout, `z ∈ 𝔻`, `0 < r ≤ 1`, `t := tanh r ≤ tanh 1 < 4/5`. The last inequality is `e² < 9`, M01 `exp_two_mul_lt_nine`.

**`one_sub_normSq_le_of_mem_hypBall`.** Let `w ∈ hypBall z r`.
- Then `ρ := pseudoHyp z w < t` (`hypDist_lt_iff`), and `1 − ρ² = (1−|z|²)(1−|w|²)/|1−z̄w|²` (`one_sub_normSq_mobius`, `pseudoHyp_eq_norm_mobius`).
- So `(1−|z|²)(1−|w|²) ≥ (1−t²)|1−z̄w|² ≥ (9/25)(1−|z|)² ≥ (9/100)(1−|z|²)²`, using `|1−z̄w| ≥ 1−|z|` and `1−|z|² ≤ 2(1−|z|)`.
- Divide by `1−|z|² > 0`: `1−|z|² ≤ (100/9)(1−|w|²) ≤ 12(1−|w|²)`.

**`hypArea_hypBall_le`.**
- `hypBall z r ⊆ ball z (18r(1−|z|))` (M01 `hypBall_subset_ball`).
- On `hypBall z r` the density is `(1−|w|²)^{−2} ≤ 144 (1−|z|²)^{−2}`.
- Hence `hypArea(hypBall z r) ≤ 144(1−|z|²)^{−2} · π(18r(1−|z|))² ≤ 46656 π r²`, using `1−|z| ≤ 1−|z|²` (`setLIntegral_mono`, `withDensity_apply`, `volume_ball_complex`).

**`hypArea_hypBall_ge`.**
- `ball z (r(1−|z|)/10) ⊆ hypBall z r` (M01 `ball_subset_hypBall`).
- On that ball `1−|w|² ≤ 2(1−|w|) ≤ 2(1 + r/10)(1−|z|) ≤ 3(1−|z|)`, so the density is `≥ (9(1−|z|)²)^{−1}`.
- The Euclidean area is `π r²(1−|z|)²/100`.
- The product is `≥ π r²/900`.

**`isLocallyDoublingDisc_hypArea`.** For `0 < r` and `2r < 1`, both `2r ≤ 1` and `r ≤ 1` hold. Then

`hypArea(hypBall z 2r) ≤ 46656π(2r)² ≤ 167961600 · (πr²/900) ≤ 167961600 · hypArea(hypBall z r)`.

Take `C := 167961600`.

### 4.6 `IsLocallyDoublingDisc.of_le_of_le`

Let `C` be the doubling constant of `μ`. Then

`ν(B₂) ≤ b μ(B₂) ≤ b C μ(B₁) ≤ b C a⁻¹ (a μ(B₁)) ≤ (b C a⁻¹) ν(B₁)`.

The constant is `(b * C * a⁻¹).toNNReal`, finite since `a ≠ 0` and `b ≠ ∞` (`ENNReal.mul_le_mul`, `ENNReal.inv_mul_cancel`). `IsLocallyDoublingDisc.smul` is the case `a = b`, done directly: `(a•μ)(B₂) = a μ(B₂) ≤ a C μ(B₁) = C (a μ(B₁))`. This holds for every `a`, including `0` and `∞` (`mul_left_comm`).

### 4.7 `isSubharmonicWeight_add_log`

Let `ψ := φ' + c log(1−|z|²)` and `μψ := ν + ofReal(ε−4c) • hypArea`.
- **`continuousOn`:** sum of continuous functions on `𝔻`.
- **`finite_of_compact`:**
  - `ν(K) ≤ (ν + ε hypArea)(K) < ∞` (`Measure.le_add_right`);
  - `hypArea(K) ≤ (1−r_K²)^{−2} vol(K) < ∞` for `K ⊆ closedBall 0 r_K`, `r_K < 1`.
- **`carried`:** `ν(𝔻ᶜ) ≤ μ'(𝔻ᶜ) = 0`, and `hypArea(𝔻ᶜ) = 0` (`withDensity_apply`, `Measure.restrict_apply`).
- **`laplacian_eq`:** for a test `χ`,

  `∫ ψ Δχ = ∫ φ' Δχ + c ∫ log(1−|z|²)Δχ = (∫χ dν + ε ∫χ dhypArea) − 4c ∫χ dhypArea = ∫χ dν + (ε−4c)∫χ dhypArea = ∫χ dμψ`.
  - Linearity of the Bochner integral (`integral_add`, `integral_const_mul`): `φ'Δχ` and `log(1−|z|²)Δχ` are continuous with compact support in `𝔻` (`integrable_mul_of_tsupport_subset`).
  - `hφ'.laplacian_eq` and `integral_add_measure`, `integral_smul_measure` (`χ` is integrable against `ν` and `hypArea`: bounded, compact support in `𝔻`, finite measure there).
  - §4.4.
  - `ENNReal.toReal_ofReal` (needs `0 ≤ ε − 4c` and `0 ≤ ε`).

### 4.8 `exists_aux_weight_disc`

1. Apply `lemma6_disc` to get `φ', μ', ε, B` with `ε•hypArea ≤ μ'`.
2. `μ'` is σ-finite (§4.2), so §4.1 gives `ν` with `ν + ε•hypArea = μ'`.
3. Put `c := min(ε/8, 1/2)`, so `0 < c < 1` and `4c ≤ ε/2`. Let `ψ := φ' + c log(1−|z|²)` and `μψ := ν + ofReal(ε−4c)•hypArea`. Then `IsSubharmonicWeight 𝔻 ψ μψ` by §4.7.
4. **Comparison.** `(1/2)•μ' ≤ μψ ≤ μ'`:
   - `μψ ≤ ν + ε•hypArea` since `ε − 4c ≤ ε`;
   - `(1/2)(ν + ε•hypArea) ≤ ν + (ε/2)•hypArea ≤ μψ` since `ε − 4c ≥ ε/2`.

   Use `Measure.le_iff` on measurable sets and `ENNReal.ofReal` arithmetic.
5. **Local doubling.** §4.6 with `μ := μ'`, `a := 1/2`, `b := 1`.
6. **Mass.**
   - `μψ(hypBall z 1) ≥ (ε/2) hypArea(hypBall z 1) ≥ (ε/2)(π/900)` (§4.5).
   - `exists_hypBall_measure_gt` with `r = 1`, `m₀ = επ/1800`, `M = 1` gives `R` with `1 < μψ(hypBall z R)`.
7. **Equivalence.** `|ψ − (φ + c log(1−|z|²))| = |φ' − φ| ≤ B` on `𝔻`. Also `B ≥ 0`, from `B ≥ |φ 0 − φ' 0|`.

### 4.9 The partition

**`exists_measurable_partition`.** Put `Ω i := S ∩ G i ∖ ⋃ (j : Fin n) (_ : j < i), G j`.
- Measurable: finite unions and differences.
- `Ω i ⊆ G i ∩ S`.
- For `z ∈ S`, the index `i₀ := Finset.min'` of `{i | z ∈ G i}` (nonempty by `hcov`) is the unique `i` with `z ∈ Ω i`.

**`measurableSet_goodSet_disc`.** Let `G` be the set in the statement. Then

`𝔻 ∖ G = ⋃_{w ∈ Z ∩ 𝔻} {z ∈ 𝔻 | hypDist z w < ε ρ w}`.

Each piece equals `𝔻 ∩ (pseudoHyp w ·)⁻¹' (Iio (tanh (ε ρ w)))` (`hypDist_lt_iff`, `pseudoHyp_comm`). That set is open by `ContinuousOn.isOpen_inter_preimage` with `continuousOn_pseudoHyp`. An arbitrary union of open sets is open, so `G = 𝔻 ∖ (𝔻 ∖ G)` is measurable. No countability of `Z` is needed.

### 4.10 `exists_disc_solution_kernel`

1. `exists_aux_weight_disc` gives `ψ, μψ, c, B`.
2. `prop2_disc_full ψ μψ` gives `n, h, ε_P, C_P`.
3. **Measurable multipliers.** `h̃ i := 𝔻.indicator (h i)` is measurable (`ContinuousOn.measurable_piecewise` with `(hh i).continuousOn`, `continuousOn_const`, `measurableSet_ball`) and equals `h i` on `𝔻`. The fixed statement allows `h i` to be arbitrary off `𝔻`.
4. **Partition.** `G i := {z | z ∈ 𝔻 ∧ ∀ w ∈ {w | h i w = 0}, w ∈ 𝔻 → ε_P * massRadiusDisc μψ w ≤ hypDist z w}`. These are measurable by §4.9 and cover `𝔻` by prop2's second conjunct. `exists_measurable_partition` with `S = 𝔻` gives `Ω`.
5. **Definition.** `H := thm2H h̃ Ω`; `A := C_P² e^{2B}`.
6. **Measurability of `uncurry H`.**
   - `(z,ζ) ↦ (Ω i).indicator (fun ζ ↦ h̃ i z / h̃ i ζ) ζ` is the indicator of `univ ×ˢ Ω i` applied to `(z,ζ) ↦ h̃ i z / h̃ i ζ` (`Measurable.indicator`, `Measurable.div`, `comp measurable_fst/snd`).
   - The second factor is measurable by `measurability`.
7. **For `ζ ∈ 𝔻`, let `i₀` be the unique index** with `ζ ∈ Ω i₀` (`Finset.sum_eq_single`). For `z ∈ 𝔻`:

   `H z ζ = (h i₀ z / h i₀ ζ) · (1−|ζ|²)/(1−ζ̄z)`.
   - **Holomorphy in `z` on `𝔻`.** `DifferentiableOn.congr` with that formula; `h i₀` is holomorphic, `h i₀ ζ` is a constant, and `1 − ζ̄z ≠ 0` (`one_sub_conj_mul_ne_zero_of_mem`).
   - **`H ζ ζ = 1`.** `h i₀ ζ ≠ 0`, because `ζ ∈ G i₀` gives `C_P⁻¹e^{ψ ζ} ≤ ‖h i₀ ζ‖` with the left side positive. And `1 − conj ζ * ζ = (1−|ζ|²:ℝ) ≠ 0` (`one_sub_conj_mul_self`).
   - **Bound.** For `z ∈ 𝔻`:

     `‖H z ζ‖ = ‖h i₀ z‖/‖h i₀ ζ‖ · (1−|ζ|²)/‖1−ζ̄z‖ ≤ C_P e^{ψ z} · C_P e^{−ψ ζ} · (1−|ζ|²)/‖1−ζ̄z‖`,

     using the global upper bound at `z` and the lower bound at `ζ ∈ G i₀`. Moreover

     `ψ z − ψ ζ ≤ (φ z − φ ζ) + c(log(1−|z|²) − log(1−|ζ|²)) + 2B`,

     and `exp(c(log x − log y)) = (x/y)^c` for `x, y > 0` (`Real.log_div`, `Real.rpow_def_of_pos`, `Real.exp_mul`). This gives `hHb` with `A = C_P² e^{2B}`.

### 4.11 `theorem2`

Take `H, c, A` from §4.10 and set `C := (24A/(c(1−c))).toNNReal`. For admissible `f`, put `u := fun z ↦ ∫ ζ in 𝔻, H z ζ/(π(z−ζ)) * f ζ`. M10's `disc_kernel_operator` (with `hφ.continuousOn`) gives `IsWeakDbarSol 𝔻 u f` and the bound for every `p ≥ 1`, with constant `ofReal(24A/(c(1−c))) = ↑C` (`ENNReal.ofReal` is `↑(Real.toNNReal ·)` by definition).

- **Admissibility.** "`f` measurable with the right side finite for *some* `p`" is exactly what M10 needs.
  - The defining integral converges absolutely for a.e. `z`: `Φ ∈ L^{p}_{loc}`, M10 §3.5 step 4.
  - `u` and `f` are in `L¹_loc(𝔻)`: M10 §3.5 steps 4 and 5.
  - Where the integral diverges, the Bochner integral is `0`, which is harmless: only `‖u‖ₑ ≤ Φ` is used.
- **Measurability of `u e^{−φ}`** is part of M10 §3.5 step 3. Without it `eLpNorm` would be `∞` and the bound could fail.

### 4.12 Scaling and `theorem2_printed`

**`IsSubharmonicWeight.div_const`.**
- Continuity and carrier are immediate.
- Finiteness: `(ofReal p⁻¹ • μ)(K) = ofReal p⁻¹ · μ(K) < ∞`.
- `laplacian_eq`: `∫ (φ/p)Δχ = p⁻¹ ∫ φΔχ = p⁻¹ ∫χ dμ = ∫ χ ∂(ofReal p⁻¹ • μ)` (`integral_div`, `integral_smul_measure`, `ENNReal.toReal_ofReal`).

**`theorem2_printed`.** Fix `p ≥ 1`; put `φ̃ := φ/p` and `μ̃ := ofReal p⁻¹ • μ`.
1. **Hypotheses for `(φ̃, μ̃)`.**
   - `div_const` and `IsLocallyDoublingDisc.smul`.
   - Mass: `hm` gives `ofReal 1 ≤ μ(hypBall z r)`. `exists_hypBall_measure_gt` with `M = p` gives `R` with `ofReal p < μ(hypBall z R)`, hence `1 = ofReal p⁻¹ · ofReal p < μ̃(hypBall z R)` (`ENNReal.mul_lt_mul_left`, `ofReal p⁻¹ ≠ 0, ∞`).
2. Let `C̃` be the constant of `theorem2 φ̃ μ̃`, and set `C := C̃ ^ p` (`NNReal.rpow`; `ENNReal.coe_rpow_of_nonneg`).
3. Let `G z := f z * ((1−‖z‖²) e^{−φ z/p} : ℝ)`. Pointwise, `‖G z‖ₑ ^ p = ofReal(‖f z * (1−‖z‖²)‖^p e^{−φ z})` (`Real.mul_rpow`, `Real.abs_rpow…`, `(e^{−φ/p})^p = e^{−φ}` by `← Real.exp_mul`).
   - So the printed hypothesis is `∫⁻‖G‖ₑ^p dν < ∞`, i.e. `eLpNorm G (ofReal p) ν < ∞` (`eLpNorm_eq_lintegral_rpow_enorm_toReal`, `ENNReal.toReal_ofReal`, `ENNReal.rpow_lt_top_of_nonneg`).
   - `G` is `AEStronglyMeasurable` on `ν` from `hf` and continuity of `φ` on `𝔻`.
4. `theorem2` at `ofReal p` gives `u` with `IsWeakDbarSol 𝔻 u f` and `eLpNorm (u e^{−φ̃}) p ν ≤ C̃ eLpNorm G p ν < ∞`.
   - Finiteness forces `u e^{−φ̃}` to be `AEStronglyMeasurable` (`aestronglyMeasurable_of_eLpNorm_ne_top`).
   - Rewrite both sides as `(∫⁻ …)^{1/p}`, raise to the power `p` (`ENNReal.rpow_le_rpow`, `ENNReal.mul_rpow_of_nonneg`, `ENNReal.rpow_inv_rpow`), and use the pointwise identity `‖u e^{−φ/p}‖ₑ^p = ofReal(‖u‖^p e^{−φ})`.

---

## 5. Admissibility, in words

`f` is admissible if `f` is a.e.-strongly measurable on `𝔻` and `F := f(1−|z|²)e^{−φ} ∈ L^{p₀}(ν)` for some `p₀ ∈ [1,∞]`. Then:
- `TF := ∫ M_c(·,ζ)|F(ζ)| dν(ζ) ∈ L^{p₀}(ν)` (Schur). Hence `Φ(z) = ∫|κ(z,ζ)||f(ζ)|dm(ζ) ≤ (A/π)e^{φ(z)} TF(z)` is finite for a.e. `z`, so the integral defining `u` converges absolutely a.e.
- `Φ ∈ L¹_loc(𝔻)` (Hölder on compacts, `ν(K) < ∞`). This gives both Fubini in the weak equation and `u ∈ L¹_loc(𝔻)`.
- `f ∈ L¹_loc(𝔻)`, because `e^{φ}/(1−|z|²)` is bounded on compacts.

For other exponents `p` with `‖F‖_p = ∞` the inequality is trivial. For `p` with `‖F‖_p < ∞` it is the Schur bound. Since `u` does not depend on `p`, one `u` works for all `p`.

---

## 6. Interface

**Consumed.** `lemma6_disc` (M04), `exists_hypBall_measure_gt` (M03), `prop2_disc_full` (M09), all in the exact form of §2.1, plus `disc_kernel_operator` (M10) and the M01 lemmas in the header.
- **Name or shape mismatches** must be resolved with M03, M04 and M09 before implementation. The cheapest fixes are wrapper lemmas in those modules.
- **`hypArea`** must be a shared definition, placed in M04 or earlier.

**Exported.**
- **To M12:** `Measure.exists_add_eq_of_le`, `IsSubharmonicWeight.sigmaFinite`, `exists_measurable_partition`, `IsSubharmonicWeight.div_const`.
- **To BOC (M23):** `bridgeMeasure`, `bridge_*`, `dbar_sup_estimate_C2`, and, once available, `dbar_sup_estimate_C2_uniform`.
- **To the comparator:** `theorem2`, `theorem2_printed`.

---

## 7. The bridge lemma for BOC

**Setting.** BOC has `ψ₀ ∈ C²(𝔻)` with `δ ≤ (1−|z|²)² lap ψ₀ ≤ M` on `𝔻` (`lap = ¼Δ`; `invLap`). BOC needs `W` with `∂̄W = g` on `𝔻` and `|W| e^{−ψ₀/2} ≤ C sup|g|(1−|z|)e^{−ψ₀/2}`.

**Normalisation.** `φ := ψ₀/2` and `μ := Δφ dm = (1/2)·4 lap ψ₀ dm = 2 lap ψ₀ dm` on `𝔻` (`bridgeMeasure`). `lemma6_disc` is not needed here, because `μ ≥ 2δ·hypArea` already. It is used only inside `theorem2`, harmlessly.

**`bridge_isSubharmonicWeight`.**
- `φ` is continuous on `𝔻` (`hψ.continuousOn.div_const`).
- `μ` is finite on compacts: the density is continuous on `𝔻` (`continuousOn_lap`), hence bounded on `K`.
- `μ(𝔻ᶜ) = 0`.
- `laplacian_eq`: `∫ (ψ₀/2) Δχ = (1/2)∫ Δψ₀ χ` (§4.3) `= ∫ 2 lap ψ₀ · χ` (`laplacian_eq_four_mul_lap`) `= ∫ χ ∂μ`.
  - The last step is `integral_withDensity_eq_integral_toReal_smul`, which needs `AEMeasurable` of the density on `volume.restrict 𝔻` (`ContinuousOn.aemeasurable`) and `toReal (ofReal (2 lap ψ₀)) = 2 lap ψ₀` since `lap ψ₀ ≥ 0` on `𝔻` (`hpos`). Then `setIntegral` over `𝔻`.

**`bridge_le_le`.** Pointwise on `𝔻`, `2δ(1−|z|²)^{−2} ≤ 2 lap ψ₀ ≤ 2M(1−|z|²)^{−2}`. Use `Measure.le_iff`, `withDensity_apply`, `setLIntegral_mono` and `lintegral_const_mul` (for `ofReal(2δ) • hypArea`).

**`bridge_isLocallyDoublingDisc`.** Combine `isLocallyDoublingDisc_hypArea` (§4.5), `bridge_le_le` and §4.6. Here `a = ofReal(2δ) ≠ 0` since `δ > 0`, and `b = ofReal(2M) ≠ ∞`.

**`bridge_mass`.** `μ(hypBall z 1) ≥ 2δ·π/900 > 0` (§4.5), then `exists_hypBall_measure_gt`.

**`dbar_sup_estimate_C2`.**
- `hpos` follows from `hlow`: `lap ψ₀ ≥ δ(1−|z|²)^{−2} > 0`.
- Apply `theorem2` to `(ψ₀/2, bridgeMeasure ψ₀)`, which gives `C₂`.
- For `g` smooth with compact support in `𝔻`, `F := g(1−|z|²)e^{−ψ₀/2}` is bounded: by the max of the continuous `‖g‖e^{−ψ₀/2}` on the compact `tsupport g ⊆ 𝔻`. So `eLpNorm F ∞ ν < ∞`, and `f := g` is admissible (`p = ∞`). `theorem2` gives `W` and `eLpNorm (W e^{−φ}) ∞ ν ≤ C₂ eLpNorm F ∞ ν`.
- Given `B` with `‖g ζ‖(1−‖ζ‖)e^{−ψ₀ζ/2} ≤ B` on `𝔻`: `‖F‖ ≤ 2B` on `𝔻`, since `1−|ζ|² ≤ 2(1−|ζ|)`. So `eLpNorm F ∞ ν ≤ ofReal(2B)` (`eLpNormEssSup_le_of_ae_bound`, `ν` carried by `𝔻`).
- So `‖W e^{−φ}‖ ≤ 2C₂B` `ν`-a.e. (`ae_le_eLpNormEssSup`). It holds `volume.restrict 𝔻`-a.e. because `volume.restrict 𝔻 ≪ ν`: the density is `> 0` on `𝔻` (`withDensity_absolutelyContinuous'`).
- `exp (−(ψ₀ z / 2)) = exp (−ψ₀ z / 2)` (`neg_div`). `C := 2C₂`. `B ≥ 0` is automatic.
- **Holomorphy near the nodes** (BOC M22 step 4) then follows on the BOC side from `∂̄W = g = 0` there, by Weyl (`differentiableOn_of_isWeakDbarSol_zero`).

---

## 8. Issues found (for NOTEBOOK)

### 8.1 Errata in the paper (pp. 357, 372–374)

1. **Sign of the auxiliary weight (p. 372 l. −12, p. 373 l. −13).** `ψ = φ − (ε/2)log(1−|z|²)` should be `ψ = φ + (ε/2)log(1−|z|²)` in the paper's normalisation `Δ = ∂∂̄`, or `φ + c log(1−|z|²)` with `0 < c ≤ ε/8` for the standard Laplacian.
   - With the printed sign, both Schur integrals of the printed kernel bound diverge (§1(a)).
   - The printed "`(1−|z|²)²Δψ > ε/2`" fits only the corrected sign.
2. **The kernel bound on p. 374 inherits the sign.** It should read `|κ| ≲ (1−|ζ|²)/(|1−ζ̄z||ζ−z|) · ((1−|z|)/(1−|ζ|))^{c} e^{φ(z)−φ(ζ)}`. Moreover only `≲` holds: `κ` vanishes at the zeros of `h_i`.
3. **The `L^p` normalisation (p. 357, p. 373).** The proof's step `|g| ≲ e^ψ ⇒ …` gives the printed `e^{−φ}`-weighted estimate only for `p = 1`. The construction gives `‖u e^{−φ}‖_{L^p(dm/(1−|z|²))} ≲ ‖f(1−|z|²)e^{−φ}‖_{L^p}` for all `p ∈ [1,∞]` with one `u`. The printed form for each `p` follows by applying this to `φ/p`, with a `p`-dependent solution (`theorem2_printed`).
4. **p. 372, the multiplier bound** `d/ρ ≲ |g|e^{−ψ} ≲ (d/ρ)^M` has its inequalities reversed. It should be `(d/ρ)^M ≲ |g|e^{−ψ} ≲ d/ρ`, as in Theorem 4.
5. **The proof uses `|h_i| ≲ e^ψ` on all of `𝔻`.** That is the Remark after Theorem 4 (`d(z,Λ) ≲ ρ(z)`), and not only the bound off `E_{h_i}` in the statement of Proposition 2.
6. **"We take an arbitrary weight with `(1−|z|²)²Δφ > ε`"** silently invokes Lemma 6. The formal proof pays `e^{2B}` in the constant.

### 8.2 Interface issues (for the coordinator)

7. **The fixed `prop2_disc` is too weak for Theorem 2.** It lacks the global upper bound. M09 must export `prop2_disc_full` (§2.1); `prop2_disc` is then a corollary. The same holds in the plane (M12).
8. **`theorem1`'s hypothesis `1 ≤ μ(ball z r)`** versus Lemma 6/Prop 2's `1 < …` (plane). Handled in M12 by `B(z,3r) ⊇ B(z,r) ⊔ B(z+2r,r)`. In the disc both use `1 <`.

### 8.3 The BOC bridge needs a uniform constant (important)

`dbar_sup_estimate_C2` is provable from `theorem2`, but its constant `C` depends on `ψ₀`. BOC's M22 applies the estimate to the family `ψ₀(S)`, `S ⊆ Γ` finite, with `δ ≤ Δ̃ψ₀(S) ≤ M` uniformly. Its normal-families step needs `C` independent of `S`; M22 says "the constant does not depend on `S`". There is no obvious single reference weight to use instead: `ψ₀(Γ)` diverges in general, because `Σ_{w∈Γ}(−log|φ_w|²) = ∞` for separated sequences that fail the Blaschke condition. Hence BOC needs `dbar_sup_estimate_C2_uniform`, and that is **not derivable from the fixed statements**, since `prop2_disc` has `∃ C` after the weight.

**Proposed fix.**
- M09 exports `prop2_disc_unif` (§2.4): Proposition 2 with `n, ε, C` depending only on `a, b`, for all weights with `a•hypArea ≤ μ ≤ b•hypArea`. Mathematically the construction (M05–M08) is uniform in this class:
  - the doubling constant and the mass radius are controlled by `a, b` (§4.5);
  - `ρ(z)` is comparable to a constant.
- With it, the proof of `dbar_sup_estimate_C2_uniform` is the one above without Lemma 6:
  - `ε := 2δ` and `ν := bridgeMeasure ψ₀ − 2δ•hypArea` (§4.1);
  - `c := min(δ/4, 1/2)`;
  - `μψ = ν + (2δ−4c)•hypArea ∈ [δ•hypArea, 2M•hypArea]`;
  - `A = C_P²` (`B = 0`) and `C = 48 C_P²/(c(1−c))`, uniform.
- The cost falls on M05–M09, which must track constants for this class.
- **Recommendation:** decide this before the M08/M09 statements are frozen.
