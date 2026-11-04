# M10 — Model kernels: Lemmas 7 and 8, the Schur test, Forelli–Rudin integrals

**Lean file:** `OrtegaCerdaMultipliers/ModelKernels.lean` (may be split into `ModelKernels/Schur.lean`, `ModelKernels/ForelliRudin.lean`, `ModelKernels/Weak.lean`, `ModelKernels/Lemmas78.lean`; the split is free).

**Paper:** §4.2, Lemma 7 (p. 372) and Lemma 8 (p. 374). Both are "an immediate consequence of Hölder's inequality".

**Depends on:**
- M00 (`Defs.lean`): `dbar`, `IsWeakDbarSol`, `𝔻`, `discMeasure`.
- M01 (`Foundations/*`, copied from BOC):
  - `pompeiu`, `dbar_mul`, `dbar_eq_zero_of_differentiableAt`, `dbar_congr`, `continuous_dbar`, `hasCompactSupport_dbar`, `tsupport_dbar_subset` (Pompeiu/Wirtinger);
  - `lintegral_inv_norm_sub_ball` (`∫_{B(a,R)} |z−a|⁻¹ = 2πR`), `lintegral_inv_norm_sub_le_of_set`, `lintegral_eq_lintegral_circle`, `lintegral_comp_norm_sub` (Polar);
  - `one_sub_mul_le_norm_one_sub_conj_mul`, `norm_one_sub_conj_mul_sq_sub`, `one_sub_conj_mul_ne_zero_of_mem`, `one_sub_conj_mul_self`, `norm_lt_one_of_mem_disc`, `one_sub_normSq_pos` (DiscGeometry).
- Mathlib:
  - Hölder: `ENNReal.lintegral_mul_le_Lp_mul_Lq`, `eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal`;
  - Tonelli/Fubini: `lintegral_lintegral_swap`, `Measurable.lintegral_prod_right'`, `integral_integral_swap`, `AEStronglyMeasurable.integral_prod_right'`;
  - `eLpNorm_eq_lintegral_rpow_enorm_toReal`, `eLpNormEssSup`, `ae_le_eLpNormEssSup`, `eLpNorm_mono_enorm`, `enorm_integral_le_lintegral_enorm`;
  - the Poisson formula `DiffContOnCl.circleAverage_poissonKernel_smul'` (`Mathlib/Analysis/Complex/Poisson.lean`);
  - `integral_gaussian_Ioi`, `integral_rpow`/`integral_Ioi_rpow_of_lt`, `lintegral_withDensity_eq_lintegral_mul₀`.

**Warning (Mathlib v4.35 junk value).** `eLpNorm f p μ = ∞` whenever `f` is *not* `AEStronglyMeasurable` (`eLpNorm_of_not_aestronglyMeasurable`). Every `L^p` bound on a solution `u` therefore needs a proof that `u` is a.e.-strongly measurable. This is done once, in `isWeakDbarSol_kernel`/`disc_kernel_operator` (§3.4, §3.5), with `AEStronglyMeasurable.integral_prod_right'`.

---

## 0. The paper

**Lemma 7 (p. 372).** For `α ∈ (0,1)` and `p ∈ [1,∞)`, the solution
`u(z) = (1/π) ∫_𝔻 (1−|ζ|²)/(1−ζ̄z) · f(ζ)/(z−ζ) dm(ζ)` of `∂̄u = f` in `𝔻` satisfies
- `∫_𝔻 |u|^p (1−|z|)^{α−1} dm ≲ ∫_𝔻 |f(z)(1−|z|)|^p (1−|z|)^{α−1} dm`;
- `sup_𝔻 |u|(1−|z|)^α ≲ sup_𝔻 |f|(1−|z|)^{1+α}`.

**Lemma 8 (p. 374).** For `α > 0` and `p ∈ [1,∞]`, the solution `u(z) = (1/π) ∫_ℂ e^{2α(ζ̄z−|ζ|²)} f(ζ)/(z−ζ) dm(ζ)` of `∂̄u = f` in `ℂ` satisfies `‖u e^{−α|z|²}‖_p ≲ ‖f e^{−α|ζ|²}‖_p`.

Both are checked below. Lemma 7 as printed is **correct**, including the `L^p` part. The `L^p` part is not a plain Schur test in the printed normalisation: the plain Schur test diverges logarithmically for the weight `(1−|z|)^{α−1}` on both sides. It becomes one after conjugating by `(1−|z|²)^{α/p}` (§3.6). Lemma 8 is correct as printed.

---

## 1. Design

The module provides five things. M11 and M12 use only items 1, 4 and 5; Lemmas 7 and 8 (item 6, 7) are instances of item 5.

1. **The Schur test** (§2.1), for a positive kernel on an arbitrary s-finite measure space, in `eLpNorm` form, for all `p ∈ [1,∞]` at once, with constant `A^{1−1/p} B^{1/p}`.
2. **One Forelli–Rudin estimate** (§2.2). For `0 < s < 1` and `a ∈ 𝔻`:

   `J_s(a) := ∫_𝔻 (1−|w|²)^{−s} / (|1−āw| |a−w|) dm(w) ≤ (24π/(s(1−s))) (1−|a|²)^{−s}`.

   This single estimate gives both Schur bounds for the disc model kernel (§3.3), the sup estimate of Lemma 7, and its `L^p` estimate.
3. **The two positive model kernels** and their Schur bounds (§2.3):
   - disc: `M_c(z,ζ) = (1−|z|²)^c (1−|ζ|²)^{1−c} / (|1−ζ̄z| |z−ζ|)` with respect to `ν = discMeasure = dm/(1−|z|²)`;
   - plane: `G_c(z,ζ) = e^{−c|z−ζ|²}/|z−ζ|` with respect to `dm`.
4. **The weak `∂̄`-equation** (§2.4) for every kernel of the form `κ(z,ζ) = H(z,ζ)/(π(z−ζ))` with `H(·,ζ)` holomorphic and `H(ζ,ζ) = 1`, via Pompeiu. The hypothesis is only a local Fubini condition.
5. **The conjugated-kernel operators** (§2.5), `disc_kernel_operator` and `plane_kernel_operator`. Given a pointwise bound on `H`, they give the weak equation and the weighted `L^p` bound for every `p ∈ [1,∞]` with one `u`. They contain all the analysis of Theorems 1, 2, Lemma 7 and Lemma 8; M11 and M12 only construct `H` from the multipliers.

**What is not needed.** A Schur test with test functions (weighted Schur) is not needed. Riesz–Thorin is not needed (and is not in Mathlib). Only the Forelli–Rudin estimate above is needed, not the general family `∫ (1−|w|²)^t/|1−āw|^{2+t+c}`. Möbius changes of variables are not needed.

---

## 2. Statements (namespace `OC`)

All statements below typecheck (scratch file `m10_check.lean`, proofs `sorry`, `lake env lean`, Lean/Mathlib v4.35; imports `OrtegaCerdaMultipliers.Defs` and `OrtegaCerdaMultipliers.Foundations.Basic`).

### 2.1 The Schur test

```lean
theorem schur_test {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → X → ℝ≥0∞} (hk : Measurable (Function.uncurry k)) {A B : ℝ≥0∞}
    (hA : ∀ᵐ x ∂ν, ∫⁻ y, k x y ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂ν ≤ B)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F ν) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ ∫⁻ y, k x y * F y ∂ν) p ν ≤
      A ^ (1 - p⁻¹.toReal) * B ^ p⁻¹.toReal * eLpNorm F p ν

theorem schur_test_le_max {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → X → ℝ≥0∞} (hk : Measurable (Function.uncurry k)) {A : ℝ≥0∞}
    (hA : ∀ᵐ x ∂ν, ∫⁻ y, k x y ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂ν ≤ A)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F ν) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ ∫⁻ y, k x y * F y ∂ν) p ν ≤ A * eLpNorm F p ν
```

`p⁻¹.toReal` is `0` for `p = ∞` and `1` for `p = 1`, so the constant is `A` for `p = ∞` and `B` for `p = 1`. `ENNReal` `rpow` has `x ^ 0 = 1` for all `x`, including `∞`. The bounds are only needed `ν`-a.e., which avoids junk values of explicit kernels off `𝔻`.

### 2.2 The Forelli–Rudin estimate

```lean
theorem norm_one_sub_conj_mul_le_five_mul {a w : ℂ} (ha : a ∈ 𝔻)
    (h : (1 - ‖a‖) / 2 ≤ ‖a - w‖) : ‖1 - conj a * w‖ ≤ 5 * ‖a - w‖

theorem lintegral_FR_near {s : ℝ} (hs0 : 0 < s) {a : ℂ} (ha : a ∈ 𝔻) :
    ∫⁻ w in ball a ((1 - ‖a‖) / 2),
        ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ (-s) / (‖1 - conj a * w‖ * ‖a - w‖)) ≤
      ENNReal.ofReal (2 * Real.pi * (1 - ‖a‖) ^ (-s))

theorem lintegral_circle_inv_normSq_one_sub {a : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (h : ‖a‖ * ρ < 1) :
    ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ENNReal.ofReal (‖1 - conj a * circleMap 0 ρ θ‖⁻¹ ^ 2) =
      ENNReal.ofReal (2 * Real.pi / (1 - ‖a‖ ^ 2 * ρ ^ 2))

theorem lintegral_Ioo_rpow_div_le {s b : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) :
    ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - ρ) ^ (-s) / (1 - b * ρ)) ≤
      ENNReal.ofReal ((1 - b) ^ (-s) / (s * (1 - s)))

theorem lintegral_disc_rpow_div_normSq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {a : ℂ}
    (ha : a ∈ 𝔻) :
    ∫⁻ w in 𝔻, ENNReal.ofReal ((1 - ‖w‖) ^ (-s) / ‖1 - conj a * w‖ ^ 2) ≤
      ENNReal.ofReal (2 * Real.pi / (s * (1 - s)) * (1 - ‖a‖) ^ (-s))

theorem lintegral_FR {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {a : ℂ} (ha : a ∈ 𝔻) :
    ∫⁻ w in 𝔻, ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ (-s) / (‖1 - conj a * w‖ * ‖a - w‖)) ≤
      ENNReal.ofReal (24 * Real.pi / (s * (1 - s)) * (1 - ‖a‖ ^ 2) ^ (-s))
```

On `𝔻` all bases of `rpow` are positive, so there are no `rpow` junk values. At `w = a`, `x / 0 = 0` and the integrand is `0` on a null set.

### 2.3 Positive model kernels

```lean
instance sigmaFinite_discMeasure : SigmaFinite discMeasure := by
  unfold discMeasure; infer_instance

/-- The positive model kernel of the disc, `(1-|z|²)^c (1-|ζ|²)^{1-c} / (|1-ζ̄z| |z-ζ|)`. -/
def discModel (c : ℝ) (z ζ : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ c * (1 - ‖ζ‖ ^ 2) ^ (1 - c) /
    (‖1 - conj ζ * z‖ * ‖z - ζ‖))

theorem measurable_discModel (c : ℝ) : Measurable (Function.uncurry (discModel c))

theorem lintegral_discModel_left {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {z : ℂ} (hz : z ∈ 𝔻) :
    ∫⁻ ζ, discModel c z ζ ∂discMeasure ≤ ENNReal.ofReal (24 * Real.pi / (c * (1 - c)))

theorem lintegral_discModel_right {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {ζ : ℂ} (hζ : ζ ∈ 𝔻) :
    ∫⁻ z, discModel c z ζ ∂discMeasure ≤ ENNReal.ofReal (24 * Real.pi / (c * (1 - c)))

theorem eLpNorm_discModel_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {F : ℂ → ℝ≥0∞}
    (hF : AEMeasurable F discMeasure) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun z ↦ ∫⁻ ζ, discModel c z ζ * F ζ ∂discMeasure) p discMeasure ≤
      ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) * eLpNorm F p discMeasure

/-- The Gaussian model kernel of the plane, `e^{-c|z-ζ|²} / |z-ζ|`. -/
def planeModel (c : ℝ) (z ζ : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-c * ‖z - ζ‖ ^ 2) / ‖z - ζ‖)

theorem measurable_planeModel (c : ℝ) : Measurable (Function.uncurry (planeModel c))

theorem lintegral_planeModel_left {c : ℝ} (hc : 0 < c) (z : ℂ) :
    ∫⁻ ζ, planeModel c z ζ = ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / c))

theorem lintegral_planeModel_right {c : ℝ} (hc : 0 < c) (ζ : ℂ) :
    ∫⁻ z, planeModel c z ζ = ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / c))

theorem eLpNorm_planeModel_le {c : ℝ} (hc : 0 < c) {F : ℂ → ℝ≥0∞} (hF : AEMeasurable F)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun z ↦ ∫⁻ ζ, planeModel c z ζ * F ζ) p volume ≤
      ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / c)) * eLpNorm F p volume
```

`SFinite discMeasure` is **not** found by instance search, because `discMeasure` is a `def`. The instance above (checked) must be declared before any lemma that needs it.

### 2.4 The weak equation

```lean
theorem integral_holo_mul_dbar_div {Ω : Set ℂ} (hΩ : IsOpen Ω) {H : ℂ → ℂ} {ζ : ℂ}
    (hζ : ζ ∈ Ω) (hH : DifferentiableOn ℂ H Ω) {α : ℂ → ℂ} (hα : ContDiff ℝ (⊤ : ℕ∞) α)
    (hαc : HasCompactSupport α) (hαs : tsupport α ⊆ Ω) :
    ∫ z, H z * dbar α z / ((Real.pi : ℂ) * (z - ζ)) = -(H ζ * α ζ)

theorem isWeakDbarSol_kernel {Ω : Set ℂ} (hΩ : IsOpen Ω) {H : ℂ → ℂ → ℂ} {f : ℂ → ℂ}
    (hHm : Measurable (Function.uncurry H))
    (hHd : ∀ ζ ∈ Ω, DifferentiableOn ℂ (fun z ↦ H z ζ) Ω) (hH1 : ∀ ζ ∈ Ω, H ζ ζ = 1)
    (hf : AEStronglyMeasurable f (volume.restrict Ω)) (hfl : LocallyIntegrableOn f Ω)
    (hloc : ∀ K ⊆ Ω, IsCompact K →
      ∫⁻ z in K, ∫⁻ ζ in Ω, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ < ∞) :
    IsWeakDbarSol Ω (fun z ↦ ∫ ζ in Ω, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) f
```

### 2.5 Conjugated-kernel operators (the form used by M11 and M12)

```lean
theorem disc_kernel_operator {φ : ℂ → ℝ} (hφ : ContinuousOn φ 𝔻) {c A : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) {H : ℂ → ℂ → ℂ} (hHm : Measurable (Function.uncurry H))
    (hHd : ∀ ζ ∈ 𝔻, DifferentiableOn ℂ (fun z ↦ H z ζ) 𝔻) (hH1 : ∀ ζ ∈ 𝔻, H ζ ζ = 1)
    (hHb : ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) *
      ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖))
    (f : ℂ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hadm : ∃ p : ℝ≥0∞, 1 ≤ p ∧
      eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure < ∞) :
    IsWeakDbarSol 𝔻 (fun z ↦ ∫ ζ in 𝔻, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) f ∧
      ∀ p : ℝ≥0∞, 1 ≤ p →
        eLpNorm (fun z ↦ (∫ ζ in 𝔻, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) *
            (Real.exp (-φ z) : ℝ)) p discMeasure ≤
          ENNReal.ofReal (24 * A / (c * (1 - c))) *
            eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure

theorem plane_kernel_operator {φ : ℂ → ℝ} (hφ : Continuous φ) {c A : ℝ} (hc : 0 < c)
    {H : ℂ → ℂ → ℂ} (hHm : Measurable (Function.uncurry H))
    (hHd : ∀ ζ, Differentiable ℂ (fun z ↦ H z ζ)) (hH1 : ∀ ζ, H ζ ζ = 1)
    (hHb : ∀ z ζ, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) * Real.exp (-c * ‖z - ζ‖ ^ 2))
    (f : ℂ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hadm : ∃ p : ℝ≥0∞, 1 ≤ p ∧ eLpNorm (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) p volume < ∞) :
    IsWeakDbarSol univ (fun z ↦ ∫ ζ, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) f ∧
      ∀ p : ℝ≥0∞, 1 ≤ p →
        eLpNorm (fun z ↦ (∫ ζ, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) *
            (Real.exp (-φ z) : ℝ)) p volume ≤
          ENNReal.ofReal (A * Real.sqrt (Real.pi / c)) *
            eLpNorm (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) p volume
```

The constant does not depend on `p`, and the solution does not depend on `p`. That is exactly the shape of `theorem2` and `theorem1`.

### 2.6 Lemma 7

```lean
/-- The kernel of Lemma 7, `K(z, ζ) = (1/π) (1 - |ζ|²) / ((1 - ζ̄ z)(z - ζ))`. -/
def discKernel (z ζ : ℂ) : ℂ :=
  ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) / (1 - conj ζ * z) / ((Real.pi : ℂ) * (z - ζ))

/-- The solution operator of Lemma 7. -/
def lemma7Op (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ ζ in 𝔻, discKernel z ζ * f ζ

theorem lemma7_isWeakDbarSol {f : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hfi : ∫⁻ ζ in 𝔻, ‖f ζ‖ₑ * ENNReal.ofReal (1 - ‖ζ‖ ^ 2) < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f

/-- Lemma 7 in the normalisation of Theorem 2 (weight `e^{-φ} = (1-|z|²)^α`), all `p ∈ [1,∞]`. -/
theorem lemma7 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hadm : ∃ p : ℝ≥0∞, 1 ≤ p ∧ eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α) : ℝ)) p
      discMeasure < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm (fun z ↦ lemma7Op f z * ((1 - ‖z‖ ^ 2) ^ α : ℝ)) p discMeasure ≤
        ENNReal.ofReal (24 / (α * (1 - α))) *
          eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α) : ℝ)) p discMeasure

/-- Lemma 7, the printed `L^p` estimate (`p < ∞`, weight `(1-|z|²)^{α-1}` on both sides). -/
theorem lemma7_Lp_printed {α p : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hfin : ∫⁻ z in 𝔻, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧
      ∫⁻ z in 𝔻, ENNReal.ofReal (‖lemma7Op f z‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) ≤
        ENNReal.ofReal ((24 * p ^ 2 / (α * (p - α))) ^ p) *
          ∫⁻ z in 𝔻, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1))

/-- Lemma 7, the printed sup estimate (pointwise, every `z ∈ 𝔻`). -/
theorem lemma7_sup {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻)) {M : ℝ}
    (hM : ∀ᵐ ζ ∂(volume.restrict 𝔻), ‖f ζ‖ * (1 - ‖ζ‖ ^ 2) ^ (1 + α) ≤ M) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧
      ∀ z ∈ 𝔻, ‖lemma7Op f z‖ * (1 - ‖z‖ ^ 2) ^ α ≤ 24 / (α * (1 - α)) * M
```

We use `1−|z|²` instead of the printed `1−|z|` throughout. Since `1−|z| ≤ 1−|z|² ≤ 2(1−|z|)`, this changes only constants.

### 2.7 Lemma 8

```lean
/-- The kernel of Lemma 8, `(1/π) e^{2α(ζ̄ z - |ζ|²)} / (z - ζ)`. -/
def planeKernel (α : ℝ) (z ζ : ℂ) : ℂ :=
  Complex.exp (2 * α * (conj ζ * z - ((‖ζ‖ ^ 2 : ℝ) : ℂ))) / ((Real.pi : ℂ) * (z - ζ))

def lemma8Op (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ ζ, planeKernel α z ζ * f ζ

theorem norm_exp_planeKernel_num (α : ℝ) (z ζ : ℂ) :
    ‖Complex.exp (2 * α * (conj ζ * z - ((‖ζ‖ ^ 2 : ℝ) : ℂ)))‖ =
      Real.exp (α * ‖z‖ ^ 2 - α * ‖ζ‖ ^ 2) * Real.exp (-α * ‖z - ζ‖ ^ 2)

theorem lemma8 {α : ℝ} (hα : 0 < α) (f : ℂ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hadm : ∃ p : ℝ≥0∞, 1 ≤ p ∧
      eLpNorm (fun z ↦ f z * (Real.exp (-α * ‖z‖ ^ 2) : ℂ)) p volume < ∞) :
    IsWeakDbarSol univ (lemma8Op α f) f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm (fun z ↦ lemma8Op α f z * (Real.exp (-α * ‖z‖ ^ 2) : ℂ)) p volume ≤
        ENNReal.ofReal (Real.sqrt (Real.pi / α)) *
          eLpNorm (fun z ↦ f z * (Real.exp (-α * ‖z‖ ^ 2) : ℂ)) p volume
```

**Count:** 1 instance, 6 definitions (`discModel`, `planeModel`, `discKernel`, `lemma7Op`, `planeKernel`, `lemma8Op`), 26 theorems. All typecheck.

---

## 3. Proofs

Notation: `ν := discMeasure = 1_𝔻 dm/(1−|z|²)`; `d_a := 1−|a|`; `K_s := 24π/(s(1−s))`.

### 3.1 The Schur test (`schur_test`)

**Reduction.**
- Replace `F` by `hF.mk F`. This is measurable, and `∫⁻ y, k x y * F y` does not change for any `x`, because the integrands agree `ν`-a.e. in `y` (`lintegral_congr_ae`, `ae_eq` multiplied by `k x ·`). `eLpNorm F` does not change either (`eLpNorm_congr_ae`).
- So assume `F` is measurable. Then `F` is `AEStronglyMeasurable` (ℝ≥0∞-valued, `Measurable.aestronglyMeasurable`), so the right-hand side `eLpNorm F p ν` is the genuine `L^p` norm and not the junk value `∞`. Write `TF x := ∫⁻ y, k x y * F y ∂ν`.
- `TF` is measurable (`Measurable.lintegral_prod_right'` applied to `(x,y) ↦ k x y * F y`, which is measurable by `hk.mul (hF.comp measurable_snd)`). Hence `TF` is `AEStronglyMeasurable` (ℝ≥0∞ is second countable). This matters because of the junk value of `eLpNorm`.

Split by cases on `p` (`p = ∞`, `p = 1`, `1 < p < ∞`).

**Case `p = ∞`.** The constant is `A`.
- `F y ≤ ‖F‖_∞ := eLpNormEssSup F ν` for a.e. `y` (`ae_le_eLpNormEssSup`; `‖F y‖ₑ = F y` by `enorm_eq_self`).
- For every `x` with `∫⁻ k x · ≤ A`: `TF x ≤ ∫⁻ y, k x y * ‖F‖_∞ = ‖F‖_∞ ∫⁻ k x y ≤ A ‖F‖_∞` (`lintegral_mono_ae`, `lintegral_mul_const`).
- So `TF ≤ A‖F‖_∞` a.e., and `eLpNormEssSup TF ≤ A ‖F‖_∞` (`essSup_le_of_ae_le`).

**Case `p = 1`.** The constant is `B`.
- `∫⁻ TF = ∫⁻_x ∫⁻_y k x y F y = ∫⁻_y F y ∫⁻_x k x y` (`lintegral_lintegral_swap`, `lintegral_mul_const`);
- `≤ ∫⁻_y F y · B = B ∫⁻ F` (`lintegral_mono_ae` with `hB`).
- `eLpNorm _ 1 = ∫⁻ ‖·‖ₑ` (`eLpNorm_one_eq_lintegral_enorm`).

**Case `1 < p < ∞`.** Let `q = p/(p−1)` (`Real.HolderConjugate p q`, e.g. `Real.HolderConjugate.conjExponent`).
- **Pointwise Hölder.** Write `k F = (k^{1/q}) (k^{1/p} F)`; `ENNReal.rpow_add_of_nonneg` gives `k^{1/q} k^{1/p} = k` with no side conditions. By `ENNReal.lintegral_mul_le_Lp_mul_Lq`:

  `TF x ≤ (∫⁻ y, k x y)^{1/q} (∫⁻ y, k x y F y^p)^{1/p}`.
- Raise to the power `p` (`ENNReal.rpow_le_rpow`, `ENNReal.mul_rpow_of_nonneg`). For a.e. `x`:

  `TF x ^ p ≤ A^{p/q} ∫⁻ y, k x y F y^p`.
- **Tonelli.** `∫⁻_x TF^p ≤ A^{p/q} ∫⁻_y F y^p ∫⁻_x k x y ≤ A^{p/q} B ∫⁻ F^p` (`lintegral_lintegral_swap`).
- **Back to `eLpNorm`.** Take the power `1/p` (`eLpNorm_eq_lintegral_rpow_enorm_toReal`, `p.toReal`). Since `(p/q)/p = 1/q = 1 − 1/p`:

  `‖TF‖_p ≤ A^{1−1/p} B^{1/p} ‖F‖_p`.

**`schur_test_le_max`.** Apply `schur_test` with `B := A`. Then `A^{1−1/p} A^{1/p} = A` (`ENNReal.rpow_add_of_nonneg`, `ENNReal.rpow_one`).

### 3.2 The Forelli–Rudin estimate (`lintegral_FR`)

Fix `0 < s < 1` and `a ∈ 𝔻`, and put `d := 1 − |a| ∈ (0,1]`. Two elementary inequalities on `𝔻` are used throughout:
- (i) `|1−āw| ≥ 1 − |a||w| ≥ max(1−|a|, 1−|w|)` (`one_sub_mul_le_norm_one_sub_conj_mul`, `|a|,|w| < 1`);
- (ii) `|1−āw| ≥ |a−w|` (`norm_one_sub_conj_mul_sq_sub`: `|1−āw|² − |a−w|² = (1−|a|²)(1−|w|²) ≥ 0`).

**Step 1, near region (`lintegral_FR_near`).** Let `N := B(a, d/2) ⊆ 𝔻`. For `w ∈ N`:
- `1−|w| ≥ 1−|a|−|w−a| > d/2`, so `(1−|w|²)^{−s} ≤ (1−|w|)^{−s} ≤ (d/2)^{−s}` (`Real.rpow_le_rpow_of_exponent_nonpos`-type monotonicity, base `≥ d/2 > 0`);
- `|1−āw| ≥ d` by (i).

So the integrand is `≤ (d/2)^{−s} d^{−1} |w−a|^{−1}`. By `lintegral_inv_norm_sub_ball`, `∫_N |w−a|^{−1} = 2π(d/2) = πd`. Hence

`∫_N ≤ (d/2)^{−s} d^{−1} π d = 2^s π d^{−s} ≤ 2π d^{−s}`.

(Use `‖a − w‖ = ‖w − a‖`, `norm_sub_rev`.)

**Step 2, far region, pointwise (`norm_one_sub_conj_mul_le_five_mul`).** If `|a−w| ≥ d/2`, then from `1 − āw = (1−|a|²) + ā(a−w)`:

`|1−āw| ≤ (1−|a|²) + |a||a−w| ≤ 2d + |a−w| ≤ 5|a−w|`,

using `1−|a|² = (1−|a|)(1+|a|) ≤ 2d`. So on `𝔻 ∖ N` the integrand is `≤ 5 (1−|w|²)^{−s} |1−āw|^{−2} ≤ 5 (1−|w|)^{−s} |1−āw|^{−2}`.

**Step 3, angular integral (`lintegral_circle_inv_normSq_one_sub`).** For `0 ≤ ρ` with `|a|ρ < 1`:

`∫_0^{2π} |1 − ā ρ e^{iθ}|^{−2} dθ = 2π/(1−|a|²ρ²)`.

*Proof via Mathlib's Poisson formula.*
- `|1 − āρe^{iθ}| = |e^{iθ} − ρa|`: multiply by `|e^{−iθ}| = 1` and conjugate.
- Apply `DiffContOnCl.circleAverage_poissonKernel_smul'` with `f ≡ 1` (`diffContOnCl_const`), `c = 0`, `R = 1`, `w = ρa ∈ ball 0 1`. It gives `circleAverage (θ ↦ (1 − |ρa|²)/|e^{iθ} − ρa|²) 0 1 = 1`.
- Unfold `Real.circleAverage` (`= (2π)⁻¹ ∫_0^{2π} … (circleMap 0 1 θ) dθ`) and divide by `1 − |a|²ρ²`.
- Convert the interval integral of a continuous positive function to the `lintegral` on `Ioc 0 (2π)`: `intervalIntegral.integral_of_le`, `ofReal_integral_eq_lintegral_ofReal`, and integrability from continuity on a compact interval.

*Elementary alternative (if the Poisson API is awkward).* Use only an upper bound `≤ 8π/(1−|a|ρ)`.
- Write `|1 − b e^{iη}|² = (1−b)² + 2b(1−cos η)` with `b = |a|ρ` and `η = θ − arg a`.
- Use 2π-periodicity to recentre (`Function.Periodic.intervalIntegral_add_eq`).
- Use `1 − cos η ≥ 2η²/π²` on `[−π, π]`, from `Real.mul_le_sin`.
- Split `b < 1/2`, where the integrand is `≤ 4`, and `b ≥ 1/2`, where `|1−be^{iη}|² ≥ (1−b)² + 2η²/π²` and `∫_ℝ dη/((1−b)² + 2η²/π²) = π²/(√2(1−b))` (`integral_inv_one_add_sq` after the substitution `η = π(1−b)x/√2`).

Either form suffices for Step 4, since only `≤ C/(1−|a|ρ)` is used.

**Step 4, one-dimensional integral (`lintegral_Ioo_rpow_div_le`).** For `0 ≤ b < 1`, put `δ := 1 − b`. For `ρ ∈ (0,1)`, `1 − bρ ≥ max(1−ρ, δ)`. Substitute `t = 1 − ρ` (`lintegral_comp_...` / `Measure.map` of `ρ ↦ 1−ρ` on `Ioo 0 1`):

`∫_0^1 t^{−s}/max(t,δ) dt ≤ ∫_0^δ t^{−s} δ^{−1} dt + ∫_δ^∞ t^{−s−1} dt = δ^{−s}/(1−s) + δ^{−s}/s = δ^{−s}/(s(1−s))`.

Mathlib: `integral_rpow` (`∫_0^δ t^{−s} = δ^{1−s}/(1−s)`, `−s > −1`) and `integral_Ioi_rpow_of_lt` (`∫_δ^∞ t^{−s−1} = δ^{−s}/s`). Convert with `ofReal_integral_eq_lintegral_ofReal`, and split `Ioo 0 1 ⊆ Ioc 0 δ ∪ Ioi δ` (`lintegral_union_le`).

**Step 5, the `|1−āw|^{−2}` integral (`lintegral_disc_rpow_div_normSq`).** Use polar coordinates at `0` (`lintegral_eq_lintegral_circle 0` applied to the `𝔻`-indicator; or `lintegral_ball_eq_lintegral_circle 0 1`):

`∫_𝔻 (1−|w|)^{−s}|1−āw|^{−2} dm = ∫_0^1 ρ(1−ρ)^{−s} [∫_0^{2π} |1−āρe^{iθ}|^{−2} dθ] dρ`.

(`‖circleMap 0 ρ θ‖ = ρ` by `norm_circleMap_sub_center`.) By Step 3 this is `∫_0^1 ρ(1−ρ)^{−s} 2π/(1−|a|²ρ²) dρ`. Since `ρ ≤ 1` and `1 − |a|²ρ² ≥ 1 − |a|ρ`, it is at most `2π ∫_0^1 (1−ρ)^{−s}/(1−|a|ρ) dρ`. By Step 4 with `b = |a|` this is `≤ 2π d^{−s}/(s(1−s))`.

**Step 6, assembly (`lintegral_FR`).** Split `𝔻 = N ∪ (𝔻∖N)` (`lintegral_union_le` or `lintegral_add_compl`). Then
- `∫_N ≤ 2π d^{−s}` (Step 1);
- `∫_{𝔻∖N} ≤ 5 · 2π d^{−s}/(s(1−s))` (Steps 2 and 5).

The total is `≤ (2π + 10π/(s(1−s))) d^{−s} ≤ 12π d^{−s}/(s(1−s))`, using `s(1−s) ≤ 1`. Finally `d^{−s} = (1−|a|)^{−s} ≤ 2^s (1−|a|²)^{−s} ≤ 2(1−|a|²)^{−s}`, because `1−|a|² ≤ 2(1−|a|)` and the exponent is negative. This gives `K_s (1−|a|²)^{−s}` with `K_s = 24π/(s(1−s))`.

*Numerical sanity check (done):* `J_s(a)(1−|a|²)^s` stays between 6.7 and 30 for `s ∈ {0.1, 0.3, 0.5, 0.9}` and `|a| ≤ 0.99`. The bound `K_s` exceeds 300. The Poisson identity was checked to machine precision.

### 3.3 Model-kernel Schur bounds

**`measurable_discModel`, `measurable_planeModel`.** These follow from `ENNReal.measurable_ofReal`, `Measurable.div`, `Real.rpow` measurability (`Measurable.pow_const`), the norm, `conj` and subtraction. `fun_prop`/`measurability` should close them.

**`lintegral_discModel_left` (`z ∈ 𝔻`).**
- `∫⁻ g ∂ν = ∫⁻_𝔻 g · ofReal(1/(1−|ζ|²)) dm` (`lintegral_withDensity_eq_lintegral_mul₀`, the density being measurable, then `setLIntegral` over `𝔻`).
- On `𝔻`, `(1−|ζ|²)^{1−c} (1−|ζ|²)^{−1} = (1−|ζ|²)^{−c}` (`Real.rpow_sub`, `Real.rpow_neg_one`, positive base). Also `‖1 − conj ζ * z‖ = ‖1 − conj z * ζ‖` (take `conj`; `Complex.norm_conj`) and `‖z − ζ‖ = ‖ζ − z‖`.
- So the integral equals `(1−|z|²)^c · J_c(z)` with `a = z`, `w = ζ`. By `lintegral_FR` with `s = c` it is `≤ (1−|z|²)^c K_c (1−|z|²)^{−c} = K_c`.

**`lintegral_discModel_right` (`ζ ∈ 𝔻`).** The same computation in the variable `z`. Here `(1−|z|²)^c (1−|z|²)^{−1} = (1−|z|²)^{−(1−c)}`, and the integral equals `(1−|ζ|²)^{1−c} J_{1−c}(ζ)` with `a = ζ`, `w = z` (now `‖1 − conj ζ * z‖` matches exactly). By `lintegral_FR` with `s = 1−c` it is `≤ K_{1−c} = K_c`, since `K_s` is symmetric in `s ↔ 1−s`.

**`eLpNorm_discModel_le`.** Apply `schur_test_le_max` with `A = ofReal K_c`. Both bounds hold `ν`-a.e., because `ν(𝔻ᶜ) = 0` (`ae_restrict_mem`, transported through `withDensity`: `withDensity_absolutelyContinuous`).

**`lintegral_planeModel_left/right`.**
- Translate (`lintegral_comp_norm_sub z`, OC Polar): `∫⁻ e^{−c|z−ζ|²}/|z−ζ| dm(ζ) = 2π ∫_0^∞ s · e^{−cs²}/s ds = 2π ∫_0^∞ e^{−cs²} ds`.
- `integral_gaussian_Ioi c`: `∫_{Ioi 0} e^{−cs²} = √(π/c)/2`. So the total is `π √(π/c)`.
- The right version follows by `‖z − ζ‖ = ‖ζ − z‖`.

**`eLpNorm_planeModel_le`.** `schur_test_le_max` with `ν = volume`.

### 3.4 The weak equation

**`integral_holo_mul_dbar_div`.** Let `β := fun z ↦ H z * α z`.
1. **`β ∈ C_c^∞(ℂ)`.** Prove `ContDiffAt ℝ ⊤ β x` at every `x`.
   - If `x ∈ Ω`: `H` is `ℂ`-analytic near `x` (`DifferentiableOn.analyticAt` on the open `Ω`), hence `ContDiffAt ℂ ⊤`, hence `ContDiffAt ℝ ⊤` (`ContDiffAt.restrict_scalars`). Multiply by `α`.
   - If `x ∉ Ω`: then `x ∉ tsupport α`, so `β =ᶠ 0` near `x` (`notMem_tsupport_iff_eventuallyEq`).

   `HasCompactSupport β` follows from `hαc.mul_left`.
2. **`dbar β = H · dbar α` everywhere.**
   - On `Ω`: `dbar_mul` and `dbar_eq_zero_of_differentiableAt` for `H`.
   - Off `Ω`: both sides vanish. `dbar β z = 0` by `dbar_congr` with `β =ᶠ 0`. `dbar α z = 0` because `z ∉ tsupport α ⊇ tsupport (dbar α)` (`tsupport_dbar_subset`).
3. **Pompeiu.** `pompeiu` (OC, `ContDiff ℝ 1 β`) gives `(1/π)∫ dbar β(z)/(ζ − z) dm = β(ζ) = H(ζ)α(ζ)`. Since `1/(π(z−ζ)) = −(1/π)·1/(ζ−z)`, the claim follows (`integral_neg`, `integral_const_mul`, `div_neg`, `neg_sub`).

**`isWeakDbarSol_kernel`.** Write `κ(z,ζ) := H z ζ / (π(z−ζ))` and `u z := ∫_{ζ∈Ω} κ(z,ζ) f ζ`.
1. **Measurability.** `(z,ζ) ↦ κ(z,ζ) f ζ` is `AEStronglyMeasurable` on `(volume.restrict Ω).prod (volume.restrict Ω)` (and on `volume.prod (volume.restrict Ω)`): `hHm` and measurability of `(z,ζ) ↦ (z−ζ)⁻¹` give a measurable factor, and `hf.comp_snd` (`MeasureTheory.AEStronglyMeasurable.comp_snd`) the other. `AEStronglyMeasurable.integral_prod_right'` then makes `u` `AEStronglyMeasurable` on `volume.restrict Ω`.
2. **Local integrability of `u`.** `‖u z‖ₑ ≤ ∫⁻_{ζ∈Ω} ‖κ‖ₑ‖f‖ₑ` (`enorm_integral_le_lintegral_enorm`; this holds even where the Bochner integral is junk). By `hloc`, `∫⁻_K ‖u‖ₑ < ∞` for every compact `K ⊆ Ω`. This gives `IntegrableOn u K`, hence `LocallyIntegrableOn u Ω` (`locallyIntegrableOn_iff` for open sets, `(Or.inr hΩ)`).
3. **The identity.** Let `α` be a test function, `K := tsupport α ⊆ Ω`, and `M := sup |dbar α|` (continuous with compact support).
   - **Fubini.** `(z,ζ) ↦ dbar α z · κ(z,ζ) f ζ` is integrable on `volume.prod (volume.restrict Ω)`. Its `lintegral` is `≤ M ∫⁻_{z∈K}∫⁻_{ζ∈Ω} ‖κ‖‖f‖ < ∞`, since `dbar α = 0` off `K` (`lintegral_prod_le`, `hloc`).
   - Then

     `∫_z u(z) dbar α(z) = ∫_z ∫_{ζ∈Ω} dbar α(z) κ(z,ζ) f ζ` (`integral_mul_left`/`integral_const_mul` under the integral)
     `= ∫_{ζ∈Ω} f ζ ∫_z H z ζ dbar α z/(π(z−ζ))` (`integral_integral_swap`)
     `= ∫_{ζ∈Ω} f ζ · (−H ζ ζ α ζ) = −∫_{ζ∈Ω} f α = −∫ f α`.

     The inner identity is `integral_holo_mul_dbar_div` for `ζ ∈ Ω` (a.e. on `volume.restrict Ω`; `setIntegral_congr_fun`), then `hH1`. The last step uses `α = 0` off `Ω` (`setIntegral_eq_integral_of_forall_compl_eq_zero`).
   - Together with `hfl`, this is `IsWeakDbarSol Ω u f`.

**Which integrability of `f`?** Exactly the local Fubini condition `hloc`.
- For Lemma 7 it is implied by `∫_𝔻 |f|(1−|ζ|²) dm < ∞` (§3.6).
- For the conjugated operators it is implied by `‖f(1−|z|²)e^{−φ}‖_{L^p(ν)} < ∞` for some `p ≥ 1` (§3.5).

### 3.5 The conjugated operators

**`disc_kernel_operator`.** Fix `f` admissible, with `p₀` the exponent from `hadm`. Put `F(ζ) := f(ζ)(1−|ζ|²)e^{−φ(ζ)}` (the right-hand side's function) and `u(z) := ∫_{ζ∈𝔻} κ(z,ζ)f(ζ)`, `κ = H/(π(z−ζ))`.

1. **Pointwise kernel bound.** For `z, ζ ∈ 𝔻`, `hHb` gives

   `‖κ(z,ζ)‖ ≤ (A/π) e^{φ(z)−φ(ζ)} M_c(z,ζ)`, with `M_c = discModel c` read in `ℝ`.

   Pure algebra: `((1−|z|²)/(1−|ζ|²))^c (1−|ζ|²) = (1−|z|²)^c (1−|ζ|²)^{1−c}` (`Real.div_rpow`, `Real.rpow_sub_one`).
2. **The key function.** Put `Φ(z) := ∫⁻_{ζ∈𝔻} ‖κ(z,ζ)‖ₑ ‖f ζ‖ₑ dm(ζ)` and `TF(z) := ∫⁻ discModel c z ζ · ‖F ζ‖ₑ ∂ν(ζ)`. For `z ∈ 𝔻`:

   `Φ(z) ≤ (A/π) e^{φ(z)} TF(z)`.

   Change of measure: `‖F ζ‖ₑ · ofReal(1/(1−|ζ|²)) = ofReal(e^{−φ(ζ)}) ‖f ζ‖ₑ` on `𝔻` (`lintegral_withDensity_eq_lintegral_mul₀`).
3. **The `L^p` bound, for all `p` at once.**
   - `‖u z · e^{−φ z}‖ₑ ≤ e^{−φ(z)} Φ(z) ≤ (A/π) TF(z)` for `z ∈ 𝔻`, hence `ν`-a.e.
   - `u e^{−φ}` is `AEStronglyMeasurable` on `ν`: `u` is, by step 1 of §3.4 (on `volume.restrict 𝔻`, transported by `ν ≪ volume.restrict 𝔻`, `AEStronglyMeasurable.mono_ac`), and `e^{−φ}` is, by `ContinuousOn.aestronglyMeasurable` on the open `𝔻`.
   - `eLpNorm_mono_enorm_ae`, `eLpNorm_const_smul`/`eLpNorm_const_mul`, `eLpNorm_discModel_le` and `eLpNorm_enorm` give `‖u e^{−φ}‖_p ≤ (A/π) K_c ‖F‖_p = (24A/(c(1−c)))‖F‖_p`.
   - `‖F‖ₑ` is `AEMeasurable` because `F` is `AEStronglyMeasurable` on `ν` (from `hf`, `ContinuousOn` of `φ` and of `1−|z|²`).
4. **`hloc`.** Let `K ⊆ 𝔻` be compact; `K ⊆ closedBall 0 r_K` with `r_K < 1` (`IsCompact.exists_bound_of_continuousOn`/`exists_lt_of_isCompact`), and `m_K := max_K φ` (`IsCompact.exists_isMaxOn`). Then

   `∫⁻_K Φ dm ≤ (A/π) e^{m_K} ∫⁻_K TF dm ≤ (A/π) e^{m_K} ∫⁻_K TF dν`

   since `dm ≤ dν` on `𝔻` (density `1/(1−|z|²) ≥ 1`). Next, `∫⁻_K TF dν = eLpNorm TF 1 (ν.restrict K) ≤ ν(K)^{1−1/p₀} eLpNorm TF p₀ (ν.restrict K)` (`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`). This is finite: `ν(K) ≤ (1−r_K²)^{−1} vol(K) < ∞`, and step 3 at `p₀` gives `‖TF‖_{p₀} ≤ K_c‖F‖_{p₀} < ∞`.
5. **`LocallyIntegrableOn f 𝔻`.** On `K` as above, `‖f‖ = ‖F‖ e^{φ}/(1−|z|²) ≤ ‖F‖ e^{m_K}/(1−r_K²)`. Moreover `∫_K ‖F‖ dm ≤ ∫_K ‖F‖ dν ≤ ν(K)^{1−1/p₀}‖F‖_{L^{p₀}(ν)} < ∞`.
6. Apply `isWeakDbarSol_kernel` with `Ω = 𝔻`.

**`plane_kernel_operator`.** The same argument with `ν = volume`, `F = f e^{−φ}`, and `‖κ‖ ≤ (A/π) e^{φ(z)−φ(ζ)} G_c(z,ζ)` from `hHb`. The constant is `(A/π) · π√(π/c) = A√(π/c)` (`eLpNorm_planeModel_le`). For `hloc`, `∫⁻_K TF dm ≤ vol(K)^{1−1/p₀}‖TF‖_{p₀}`; `φ` is continuous, hence bounded on `K`. The integrals are over `ℂ`; with `Ω = univ`, `Measure.restrict_univ` turns `∫ ζ in univ` into `∫ ζ`.

### 3.6 Lemma 7

**`lemma7_isWeakDbarSol`.** Apply `isWeakDbarSol_kernel` with `Ω = 𝔻`, `H(z,ζ) = (1−|ζ|²)/(1−ζ̄z)`.
- `H` is measurable. For `ζ ∈ 𝔻`, `z ↦ H(z,ζ)` is holomorphic on `𝔻`, since `1 − ζ̄z ≠ 0` there (`one_sub_conj_mul_ne_zero_of_mem`).
- `H(ζ,ζ) = 1` (`one_sub_conj_mul_self`, `1−|ζ|² ≠ 0`).
- `discKernel z ζ = H z ζ / (π(z−ζ))` by `div_div`.
- **`hloc`.** For compact `K ⊆ closedBall 0 r_K ⊆ 𝔻` and `z ∈ K`, `|1−ζ̄z| ≥ 1 − r_K`. Tonelli (`lintegral_lintegral_swap`) and `lintegral_inv_norm_sub_le_of_set` (`∫_K |z−ζ|^{−1} dm(z) ≤ 2π + vol K`) give

  `∫⁻_{z∈K}∫⁻_{ζ∈𝔻} |κ||f| ≤ ((2π + vol K)/(π(1−r_K))) ∫_𝔻 |f|(1−|ζ|²) < ∞`.
- **`LocallyIntegrableOn f 𝔻`.** On `K`, `1−|ζ|² ≥ 1−r_K²`.

**`lemma7`.** Apply `disc_kernel_operator` with `φ := fun z ↦ −α · log(1−|z|²)`, `c := α` and `A := 1`. Then:
- `φ` is continuous on `𝔻`;
- `e^{−φ(z)} = (1−|z|²)^α` on `𝔻` (`Real.rpow_def_of_pos`), so the weighted functions agree `ν`-a.e. (`eLpNorm_congr_ae` with `ae_restrict` of `𝔻`);
- `hHb` holds with equality: `e^{φ(z)−φ(ζ)}((1−|z|²)/(1−|ζ|²))^α = 1` on `𝔻`.

The constant is `24·1/(α(1−α))`.

**`lemma7_Lp_printed` (the conjugation trick).** Apply `lemma7` with `α' := α/p ∈ (0,1)` at the exponent `p` (as `ENNReal.ofReal p`).
- `‖u (1−|z|²)^{α/p}‖_{L^p(ν)}^p = ∫_𝔻 |u|^p (1−|z|²)^{α} (1−|z|²)^{−1} dm = ∫_𝔻 |u|^p (1−|z|²)^{α−1} dm`.
- Likewise `‖f(1−|z|²)^{1+α/p}‖_{L^p(ν)}^p = ∫_𝔻 |f(1−|z|²)|^p (1−|z|²)^{α−1} dm`. Hence `hfin` is the admissibility of `lemma7` at `p`.
- Raise the `eLpNorm` inequality to the power `p` (`eLpNorm_eq_lintegral_rpow_enorm_toReal`, `ENNReal.rpow_le_rpow`, `ENNReal.mul_rpow_of_nonneg`). The constant is `(24/(α'(1−α')))^p = (24p²/(α(p−α)))^p`.
- Real `rpow` algebra on `𝔻` (positive bases): `(xy)^p = x^p y^p`, `((1−|z|²)^{α/p})^p = (1−|z|²)^α` (`Real.rpow_natCast`-free: `Real.mul_rpow`, `Real.rpow_mul`).

This is why no weighted Schur test is needed. With the printed weight `(1−|z|)^{α−1}` on both sides, the plain Schur test fails: `sup_z ∫ |k(z,ζ)| dν_α(ζ) = ∫ dm(ζ)/(|1−ζ̄z||z−ζ|) ≈ log(1/(1−|z|))`.

**`lemma7_sup`.**
- The hypothesis implies `∫_𝔻 |f|(1−|ζ|²) ≤ M ∫_𝔻 (1−|ζ|²)^{−α} < ∞` (polar coordinates, `α < 1`), so `lemma7_isWeakDbarSol` applies.
- Pointwise: `|u(z)| ≤ (1/π)∫_𝔻 (1−|ζ|²)|f|/(|1−ζ̄z||z−ζ|) ≤ (M/π) J_α(z) ≤ (M/π) K_α (1−|z|²)^{−α}`, by `norm_integral_le_lintegral_norm`, the a.e. bound and `lintegral_FR`.
- `K_α/π = 24/(α(1−α))`. The `ENNReal`/`ℝ` round trip uses `ENNReal.toReal_le_of_le_ofReal`. `M ≥ 0` is automatic when the integral is nonzero; if `M < 0` the hypothesis forces `f = 0` a.e. and `u = 0`.

### 3.7 Lemma 8

**`norm_exp_planeKernel_num`.**
- `‖exp w‖ = exp (Re w)` (`Complex.norm_exp`).
- `Re(2α(ζ̄z − |ζ|²)) = 2α Re(ζ̄z) − 2α|ζ|²`.
- `−α|z−ζ|² = −α|z|² + 2α Re(ζ̄z) − α|ζ|²` (`Complex.sq_norm`, `normSq_sub`, `Complex.mul_re`, `conj_re`, `conj_im`).
- So `2αRe(ζ̄z) − 2α|ζ|² = (α|z|² − α|ζ|²) + (−α|z−ζ|²)`. Then `Real.exp_add`.

**`lemma8`.** Apply `plane_kernel_operator` with `φ := α|z|²`, `H(z,ζ) := exp(2α(ζ̄z − |ζ|²))`, `c := α`, `A := 1`.
- `H(·,ζ)` is entire (`Differentiable.cexp` of an affine function).
- `H(ζ,ζ) = exp 0 = 1` (`conj ζ * ζ = ‖ζ‖²` as complex numbers, `Complex.conj_mul'`).
- `hHb` holds with equality, by `norm_exp_planeKernel_num`.
- `planeKernel α z ζ = H z ζ/(π(z−ζ))` by definition.

The constant is `1·√(π/α)`.

---

## 4. Interface

**Consumed from M01.** The lemmas listed in the header, with their OC names. In particular:
- `pompeiu : ContDiff ℝ 1 α → HasCompactSupport α → cauchyTransform (dbar α) w = α w`, where `cauchyTransform f w = (1/π)∫ f(z)/(w−z)`;
- `lintegral_inv_norm_sub_ball a hR : ∫⁻ z in ball a R, ofReal ‖z − a‖⁻¹ = ofReal (2πR)`;
- `lintegral_inv_norm_sub_le_of_set K z : ∫⁻ w in K, ofReal ‖w − z‖⁻¹ ≤ ofReal (2π) + volume K`;
- `lintegral_eq_lintegral_circle c hf : ∫⁻ f = ∫⁻ s in Ioi 0, ofReal s * ∫⁻ θ in Ioc 0 (2π), f (circleMap c s θ)`;
- `lintegral_comp_norm_sub a hF : ∫⁻ F ‖z − a‖ = ofReal (2π) * ∫⁻ s in Ioi 0, ofReal s * F s`.

**Exported to M11.**
- `disc_kernel_operator` (the whole analytic content of Theorem 2) and `sigmaFinite_discMeasure`;
- `isWeakDbarSol_kernel` and `lintegral_FR`, if M11 needs them directly;
- `lemma7`, `lemma7_sup`, `lemma7_Lp_printed`, which are paper-fidelity results and not used downstream.

**Exported to M12.** `plane_kernel_operator` and `lemma8`.

**Exported to M13/M14, possibly.** `isWeakDbarSol_kernel` and `schur_test` are general and reusable, e.g. for kernels in a strip.

---

### 4a. Interface (reconciled)

Lean file `ModelKernels.lean`; every statement of §2 is unchanged. Added, for M08 (far field in the disc, `farField_sum_le_disc`), which imports M10:

```lean
/-- Forelli–Rudin, the case `∫_𝔻 dm(w)/|1 − z̄w|³ ≲ (1 − |z|²)⁻¹` used by M08 (far field in the
disc, `farField_sum_le_disc`). -/
theorem integral_one_sub_conj_mul_rpow_neg_three_le :
    ∃ C : ℝ, ∀ z ∈ 𝔻,
      ∫⁻ w in 𝔻, ENNReal.ofReal (1 / ‖1 - conj z * w‖ ^ 3) ≤ ENNReal.ofReal (C / (1 - ‖z‖ ^ 2))
```

## 5. Issues found (for NOTEBOOK)

1. **p. 372, Lemma 7, "immediate consequence of Hölder's inequality".** The sup estimate is the Schur `L^∞` bound with the Forelli–Rudin integral `J_α`. The `L^p` estimate with the printed weight `(1−|z|)^{α−1}` on both sides is *not* a plain Schur test: the `L^∞` Schur integral `∫ dm(ζ)/(|1−ζ̄z||z−ζ|)` diverges like `log 1/(1−|z|)`. It follows either from Schur with power test functions or, more simply, from the `L^∞`/`L^1` Schur test after conjugating by `(1−|z|²)^{α/p}` (§3.6). The printed statement is correct for every `p ∈ [1,∞)`, with a constant that blows up as `p → ∞`. At `p = ∞` the operator `lemma7Op` is unbounded in that normalisation: for fixed `z₀` near `∂𝔻`, the datum `f(ζ) = (1−|ζ|²)^{−1}·\overline{\mathrm{sgn}\,K(z₀,ζ)}` has `sup|f|(1−|ζ|²) = 1` and `|u(z₀)| = (1/π)∫ dm/(|1−ζ̄z₀||z₀−ζ|) ≈ log 1/(1−|z₀|)`. That is why the sup estimate carries different weights.
2. **p. 372, Lemma 7.** The weak equation needs some integrability of `f`. The natural condition is `∫_𝔻 |f|(1−|ζ|²) dm < ∞`. Both of Lemma 7's right-hand sides imply it (Hölder, resp. `α < 1`).
3. **The Forelli–Rudin input** is a single estimate, `∫_𝔻 (1−|w|²)^{−s}/(|1−āw||a−w|) ≤ (24π/(s(1−s)))(1−|a|²)^{−s}` for `0 < s < 1`, proved with a near/far split, the Poisson kernel and a 1-D integral. No dyadic decomposition and no Möbius change of variables are needed.
4. **Lemma 8** is correct as printed. The identity `|e^{2α(ζ̄z−|ζ|²)}| e^{−α|z|²} e^{α|ζ|²} = e^{−α|z−ζ|²}` makes both Schur integrals equal to `π√(π/α)`, so the constant is `√(π/α)` for every `p`.
