/-
Copyright (c) 2026 Joaquim Ortega-Cerdà. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joaquim Ortega-Cerdà
-/
import OrtegaCerdaMultipliers.ModelKernelsBase

/-!
# M10 (ModelKernels), part 2 — Conjugated-kernel operators, Lemmas 7 and 8

See `blueprint/M10_ModelKernels.md`.  Second part of the M10 module (the first part is
`ModelKernelsBase.lean`): the conjugated-kernel operators used by M11 and M12, Lemma 7 (disc) and
Lemma 8 (plane).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate Topology

noncomputable section

namespace OC

/-! ## §5 Conjugated-kernel operators (used by M11 and M12) -/

theorem continuousOn_discDensity : ContinuousOn (fun z : ℂ ↦ 1 / (1 - ‖z‖ ^ 2)) 𝔻 :=
  have hden : ContinuousOn (fun z : ℂ ↦ 1 - ‖z‖ ^ 2) 𝔻 := by fun_prop
  continuousOn_const.div hden fun _ hz ↦ (one_sub_normSq_pos hz).ne'

theorem volume_restrict_disc_le_discMeasure : volume.restrict 𝔻 ≤ discMeasure := by
  calc volume.restrict 𝔻 = (volume.restrict 𝔻).withDensity 1 := withDensity_one.symm
    _ ≤ discMeasure := by
      refine withDensity_mono ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      simp only [Pi.one_apply, ENNReal.one_le_ofReal]
      have := one_sub_normSq_pos hz
      rw [le_div_iff₀ this]
      nlinarith [norm_nonneg z]

theorem discMeasure_lt_top_of_isCompact {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ 𝔻) :
    discMeasure K < ∞ := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuousOn_discDensity.mono hKD)
  rw [discMeasure, withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2)) ∂(volume.restrict 𝔻)
      ≤ ∫⁻ _ in K, ENNReal.ofReal B ∂(volume.restrict 𝔻) :=
        setLIntegral_mono' hK.measurableSet fun z hz ↦
          ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hB z hz))
    _ = ENNReal.ofReal B * (volume.restrict 𝔻) K := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_of_le_of_lt (Measure.restrict_apply_le _ _) hK.measure_lt_top)

theorem lintegral_lt_top_of_eLpNorm_discMeasure {g : ℂ → ℝ≥0∞}
    (hg : AEStronglyMeasurable g discMeasure) {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ 𝔻)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hfin : eLpNorm g p discMeasure < ∞) :
    ∫⁻ z in K, g z < ∞ := by
  have h1 : volume.restrict K ≤ discMeasure.restrict K := by
    calc volume.restrict K = (volume.restrict 𝔻).restrict K := by
          rw [Measure.restrict_restrict_of_subset hKD]
      _ ≤ discMeasure.restrict K :=
          Measure.restrict_mono subset_rfl volume_restrict_disc_le_discMeasure
  have hexp : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
    rw [ENNReal.toReal_one, div_one, sub_nonneg]
    rcases eq_or_ne p ∞ with rfl | hpt
    · simp
    · exact div_le_one_of_le₀ (by rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hpt hp)
        ENNReal.toReal_nonneg
  calc ∫⁻ z in K, g z ≤ ∫⁻ z, g z ∂(discMeasure.restrict K) := lintegral_mono' h1 le_rfl
    _ = eLpNorm g 1 (discMeasure.restrict K) := by
        rw [eLpNorm_one_eq_lintegral_eNorm hg.restrict]; simp
    _ ≤ eLpNorm g p (discMeasure.restrict K) *
          (discMeasure.restrict K) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hg.restrict
    _ ≤ eLpNorm g p discMeasure *
          (discMeasure.restrict K) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) := by
        gcongr
        exact Measure.restrict_le_self
    _ < ∞ := by
        refine ENNReal.mul_lt_top hfin (ENNReal.rpow_lt_top_of_nonneg hexp ?_)
        rw [Measure.restrict_apply_univ]
        exact (discMeasure_lt_top_of_isCompact hK hKD).ne

/-- The pointwise bound of the conjugated disc kernel by the positive model kernel. -/
theorem norm_discKernelH_le {φ : ℂ → ℝ} {c A : ℝ} {H : ℂ → ℂ → ℂ}
    (hHb : ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) *
      ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖))
    {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ ≤ A / Real.pi * Real.exp (φ z - φ ζ) *
      ((1 - ‖z‖ ^ 2) ^ c * (1 - ‖ζ‖ ^ 2) ^ (1 - c) / (‖1 - conj ζ * z‖ * ‖z - ζ‖)) := by
  have hz0 := one_sub_normSq_pos hz
  have hζ0 := one_sub_normSq_pos hζ
  have hY := norm_one_sub_conj_mul_pos hζ hz
  have hpi := Real.pi_pos
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
  rcases eq_or_ne z ζ with rfl | hne
  · simp
  have hZ : 0 < ‖z - ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  calc ‖H z ζ‖ / (Real.pi * ‖z - ζ‖)
      ≤ (A * Real.exp (φ z - φ ζ) * ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c *
          ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖)) / (Real.pi * ‖z - ζ‖) := by
        gcongr
        exact hHb z hz ζ hζ
    _ = _ := by
        rw [Real.div_rpow hz0.le hζ0.le, Real.rpow_sub hζ0, Real.rpow_one]
        field_simp

/-- Pointwise step of the `L^p` estimate for the kernel operators: if the integral of the
absolute value of the kernel against `f` is bounded by `TF z`, then so is the weighted operator. -/
theorem kernel_eNorm_mul_le {μ : Measure ℂ} {Hk f : ℂ → ℂ} {TF : ℝ≥0∞} {a φz : ℝ} (ha : 0 ≤ a)
    (hKP : ∫⁻ ζ, ‖Hk ζ‖ₑ * ‖f ζ‖ₑ ∂μ ≤ ENNReal.ofReal (a * Real.exp φz) * TF) :
    ‖(∫ ζ, Hk ζ * f ζ ∂μ) * ((Real.exp (-φz) : ℝ) : ℂ)‖ₑ ≤ ‖ENNReal.ofReal a * TF‖ₑ := by
  rw [eNorm_eq_self, eNorm_mul, ← ofReal_norm (((Real.exp (-φz) : ℝ) : ℂ)),
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc ‖∫ ζ, Hk ζ * f ζ ∂μ‖ₑ * ENNReal.ofReal (Real.exp (-φz))
      ≤ (∫⁻ ζ, ‖Hk ζ‖ₑ * ‖f ζ‖ₑ ∂μ) * ENNReal.ofReal (Real.exp (-φz)) := by
        gcongr
        refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
        simp_rw [eNorm_mul]
    _ ≤ ENNReal.ofReal (a * Real.exp φz) * TF * ENNReal.ofReal (Real.exp (-φz)) := by
        gcongr
    _ = ENNReal.ofReal a * TF := by
        rw [mul_comm _ TF, mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_assoc,
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one, mul_comm]

/-- Final `L^p` step for the kernel operators: from the pointwise bound by `a · TF` and the
`L^p` bound of `TF`, we get the `L^p` bound of the weighted operator. -/
theorem eLpNorm_kernel_le {ν : Measure ℂ} {u F : ℂ → ℂ} {φ : ℂ → ℝ} {TF : ℂ → ℝ≥0∞} {a K : ℝ}
    (ha : 0 ≤ a) (hv : AEStronglyMeasurable (fun z ↦ u z * ((Real.exp (-φ z) : ℝ) : ℂ)) ν)
    (hTFm : AEStronglyMeasurable TF ν)
    (hpt : ∀ᵐ z ∂ν, ‖u z * ((Real.exp (-φ z) : ℝ) : ℂ)‖ₑ ≤ ‖ENNReal.ofReal a * TF z‖ₑ)
    {p : ℝ≥0∞} (hTFb : eLpNorm TF p ν ≤ ENNReal.ofReal K * eLpNorm F p ν) :
    eLpNorm (fun z ↦ u z * ((Real.exp (-φ z) : ℝ) : ℂ)) p ν ≤
      ENNReal.ofReal (a * K) * eLpNorm F p ν := by
  calc eLpNorm (fun z ↦ u z * ((Real.exp (-φ z) : ℝ) : ℂ)) p ν
      ≤ eLpNorm (fun z ↦ ENNReal.ofReal a * TF z) p ν := eLpNorm_mono_eNorm_ae hv hpt
    _ = ENNReal.ofReal a * eLpNorm TF p ν := eLpNorm_const_mul_ennreal hTFm
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal K * eLpNorm F p ν) := by gcongr
    _ = ENNReal.ofReal (a * K) * eLpNorm F p ν := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha]

/-- Measurability of `f · (1 - |z|²) e^{-φ}` with respect to the hyperbolic measure. -/
theorem aestronglyMeasurable_weighted_disc {φ : ℂ → ℝ} (hφ : ContinuousOn φ 𝔻) {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻)) :
    AEStronglyMeasurable (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) discMeasure := by
  have hνac : discMeasure ≪ volume.restrict 𝔻 := withDensity_absolutelyContinuous _ _
  have hwc : ContinuousOn (fun z : ℂ ↦ (((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ) : ℂ)) 𝔻 :=
    Complex.continuous_ofReal.comp_continuousOn
      ((by fun_prop : Continuous fun z : ℂ ↦ 1 - ‖z‖ ^ 2).continuousOn.mul
        (Real.continuous_exp.comp_continuousOn hφ.neg))
  exact (hf.mul (hwc.aestronglyMeasurable measurableSet_ball)).mono_ac hνac

/-- Local integrability of `f` on the disc from an `L^p` bound on `F = f · (1 - |z|²) e^{-φ}`
with respect to the hyperbolic measure. -/
theorem locallyIntegrableOn_disc_of_eLpNorm {φ : ℂ → ℝ} (hφ : ContinuousOn φ 𝔻) {f F : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻)) (hF : AEStronglyMeasurable F discMeasure)
    (hFnorm : ∀ ζ ∈ 𝔻, ‖F ζ‖ = ‖f ζ‖ * ((1 - ‖ζ‖ ^ 2) * Real.exp (-φ ζ))) {p₀ : ℝ≥0∞}
    (hp₀ : 1 ≤ p₀) (hFfin : eLpNorm F p₀ discMeasure < ∞) : LocallyIntegrableOn f 𝔻 := by
  rw [locallyIntegrableOn_iff isOpen_ball.isLocallyClosed]
  intro K hKD hK
  refine ⟨hf.mono_measure (Measure.restrict_mono hKD le_rfl), ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hφ.mono hKD)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuousOn_discDensity.mono hKD)
  calc ∫⁻ z in K, ‖f z‖ₑ ≤ ∫⁻ z in K, ENNReal.ofReal (Real.exp C * B) * ‖F z‖ₑ := by
        refine setLIntegral_mono' hK.measurableSet fun z hzK ↦ ?_
        have hz := hKD hzK
        have hz0 := one_sub_normSq_pos hz
        rw [← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le
            ((norm_nonneg _).trans (hB z hzK))), hFnorm z hz]
        apply ENNReal.ofReal_le_ofReal
        have h1 : Real.exp (φ z) ≤ Real.exp C :=
          Real.exp_le_exp.2 ((le_abs_self _).trans (hC z hzK))
        have h2 : 1 / (1 - ‖z‖ ^ 2) ≤ B := (le_abs_self _).trans (hB z hzK)
        calc ‖f z‖ = (Real.exp (φ z) * (1 / (1 - ‖z‖ ^ 2))) *
              (‖f z‖ * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z))) := by
              rw [Real.exp_neg]; field_simp
          _ ≤ (Real.exp C * B) * (‖f z‖ * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z))) := by
              gcongr
    _ = ENNReal.ofReal (Real.exp C * B) * ∫⁻ z in K, ‖F z‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lintegral_lt_top_of_eLpNorm_discMeasure hF.eNorm.aestronglyMeasurable hK hKD hp₀
          (by rwa [eLpNorm_eNorm _ hF]))

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
            eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure := by
  set u : ℂ → ℂ := fun z ↦ ∫ ζ in 𝔻, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ
  set F : ℂ → ℂ := fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ) with hFdef
  obtain ⟨p₀, hp₀, hFfin⟩ := hadm
  have h0 : (0 : ℂ) ∈ 𝔻 := mem_ball_self one_pos
  have hA : 1 ≤ A := by
    have := hHb 0 h0 0 h0
    simpa [hH1 0 h0] using this
  have hpi := Real.pi_pos
  have hAπ : 0 ≤ A / Real.pi := div_nonneg (by linarith) hpi.le
  have hνac : discMeasure ≪ volume.restrict 𝔻 := withDensity_absolutelyContinuous _ _
  have hF : AEStronglyMeasurable F discMeasure := aestronglyMeasurable_weighted_disc hφ hf
  have hFe : AEMeasurable (fun z ↦ ‖F z‖ₑ) discMeasure := hF.eNorm
  have hFnorm : ∀ ζ ∈ 𝔻, ‖F ζ‖ = ‖f ζ‖ * ((1 - ‖ζ‖ ^ 2) * Real.exp (-φ ζ)) := by
    intro ζ hζ
    rw [hFdef, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (one_sub_normSq_pos hζ).le (Real.exp_pos _).le)]
  set TF : ℂ → ℝ≥0∞ := fun z ↦ ∫⁻ ζ, discModel c z ζ * ‖F ζ‖ₑ ∂discMeasure with hTF
  have hTFm : AEStronglyMeasurable TF discMeasure := by
    have : AEMeasurable (fun q : ℂ × ℂ ↦ discModel c q.1 q.2 * ‖F q.2‖ₑ)
        (discMeasure.prod discMeasure) :=
      (measurable_discModel c).aemeasurable.mul hFe.comp_snd
    exact this.lintegral_prod_right'.aestronglyMeasurable
  have hTFb : ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm TF p discMeasure ≤
        ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) * eLpNorm F p discMeasure := by
    intro p hp
    have := eLpNorm_discModel_le hc0 hc1 hFe hp
    rwa [eLpNorm_eNorm _ hF] at this
  have hKP : ∀ z ∈ 𝔻, ∫⁻ ζ in 𝔻, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ ≤
      ENNReal.ofReal (A / Real.pi * Real.exp (φ z)) * TF z := by
    intro z hz
    simp only [hTF]
    rw [discMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
      measurable_discDensity (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun ζ hζ ↦ ?_
    have hz0 := one_sub_normSq_pos hz
    have hζ0 := one_sub_normSq_pos hζ
    have hM0 : 0 ≤ (1 - ‖z‖ ^ 2) ^ c * (1 - ‖ζ‖ ^ 2) ^ (1 - c) /
        (‖1 - conj ζ * z‖ * ‖z - ζ‖) := by positivity
    simp only [Pi.mul_apply, discModel]
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul hM0,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      hFnorm ζ hζ]
    apply ENNReal.ofReal_le_ofReal
    calc ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ * ‖f ζ‖
        ≤ (A / Real.pi * Real.exp (φ z - φ ζ) *
            ((1 - ‖z‖ ^ 2) ^ c * (1 - ‖ζ‖ ^ 2) ^ (1 - c) / (‖1 - conj ζ * z‖ * ‖z - ζ‖))) *
              ‖f ζ‖ :=
          mul_le_mul_of_nonneg_right (norm_discKernelH_le hHb hz hζ) (norm_nonneg _)
      _ = _ := by
          rw [Real.exp_sub, Real.exp_neg]
          field_simp
  have hfl : LocallyIntegrableOn f 𝔻 :=
    locallyIntegrableOn_disc_of_eLpNorm hφ hf hF hFnorm hp₀ hFfin
  have hloc : ∀ K ⊆ 𝔻, IsCompact K →
      ∫⁻ z in K, ∫⁻ ζ in 𝔻, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ < ∞ := by
    intro K hKD hK
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hφ.mono hKD)
    calc ∫⁻ z in K, ∫⁻ ζ in 𝔻, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ
        ≤ ∫⁻ z in K, ENNReal.ofReal (A / Real.pi * Real.exp C) * TF z := by
          refine setLIntegral_mono' hK.measurableSet fun z hzK ↦ (hKP z (hKD hzK)).trans ?_
          gcongr
          exact (le_abs_self _).trans (hC z hzK)
      _ = ENNReal.ofReal (A / Real.pi * Real.exp C) * ∫⁻ z in K, TF z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lintegral_lt_top_of_eLpNorm_discMeasure hTFm hK hKD hp₀
            ((hTFb p₀ hp₀).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFfin)))
  refine ⟨isWeakDbarSol_kernel isOpen_ball hHm hHd hH1 hf hfl hloc, fun p hp ↦ ?_⟩
  have hum : AEStronglyMeasurable u volume := weak_aestronglyMeasurable_kernelOp hHm hf
  have hEc : ContinuousOn (fun z : ℂ ↦ ((Real.exp (-φ z) : ℝ) : ℂ)) 𝔻 :=
    Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn hφ.neg)
  have hv : AEStronglyMeasurable (fun z ↦ u z * ((Real.exp (-φ z) : ℝ) : ℂ)) discMeasure :=
    (hum.restrict.mul (hEc.aestronglyMeasurable measurableSet_ball)).mono_ac hνac
  have hpt : ∀ᵐ z ∂discMeasure, ‖u z * ((Real.exp (-φ z) : ℝ) : ℂ)‖ₑ ≤
      ‖ENNReal.ofReal (A / Real.pi) * TF z‖ₑ := by
    filter_upwards [ae_discMeasure_mem] with z hz
    exact kernel_eNorm_mul_le hAπ (hKP z hz)
  refine (eLpNorm_kernel_le hAπ hv hTFm hpt (hTFb p hp)).trans_eq ?_
  congr 2
  field_simp

theorem lintegral_lt_top_of_eLpNorm_volume {g : ℂ → ℝ≥0∞}
    (hg : AEStronglyMeasurable g volume) {K : Set ℂ} (hK : IsCompact K)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hfin : eLpNorm g p volume < ∞) :
    ∫⁻ z in K, g z < ∞ := by
  have hexp : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
    rw [ENNReal.toReal_one, div_one, sub_nonneg]
    rcases eq_or_ne p ∞ with rfl | hpt
    · simp
    · exact div_le_one_of_le₀ (by rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hpt hp)
        ENNReal.toReal_nonneg
  calc ∫⁻ z in K, g z = eLpNorm g 1 (volume.restrict K) := by
        rw [eLpNorm_one_eq_lintegral_eNorm hg.restrict]; simp
    _ ≤ eLpNorm g p (volume.restrict K) *
          (volume.restrict K) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hg.restrict
    _ ≤ eLpNorm g p volume *
          (volume.restrict K) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) := by
        gcongr
        exact Measure.restrict_le_self
    _ < ∞ := by
        refine ENNReal.mul_lt_top hfin (ENNReal.rpow_lt_top_of_nonneg hexp ?_)
        rw [Measure.restrict_apply_univ]
        exact hK.measure_lt_top.ne

/-- The pointwise bound of the conjugated plane kernel by the positive model kernel. -/
theorem norm_planeKernelH_le {φ : ℂ → ℝ} {c A : ℝ} {H : ℂ → ℂ → ℂ}
    (hHb : ∀ z ζ, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) * Real.exp (-c * ‖z - ζ‖ ^ 2)) (z ζ : ℂ) :
    ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ ≤
      A / Real.pi * Real.exp (φ z - φ ζ) * (Real.exp (-c * ‖z - ζ‖ ^ 2) / ‖z - ζ‖) := by
  have hpi := Real.pi_pos
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
  rcases eq_or_ne z ζ with rfl | hne
  · simp
  have hZ : 0 < ‖z - ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  calc ‖H z ζ‖ / (Real.pi * ‖z - ζ‖)
      ≤ (A * Real.exp (φ z - φ ζ) * Real.exp (-c * ‖z - ζ‖ ^ 2)) / (Real.pi * ‖z - ζ‖) := by
        gcongr
        exact hHb z ζ
    _ = _ := by field_simp

/-- Local integrability of `f` on the plane from an `L^p` bound on `F = f · e^{-φ}`. -/
theorem locallyIntegrableOn_univ_of_eLpNorm {φ : ℂ → ℝ} (hφ : Continuous φ) {f F : ℂ → ℂ}
    (hf : AEStronglyMeasurable f volume) (hF : AEStronglyMeasurable F volume)
    (hFnorm : ∀ ζ, ‖F ζ‖ = ‖f ζ‖ * Real.exp (-φ ζ)) {p₀ : ℝ≥0∞} (hp₀ : 1 ≤ p₀)
    (hFfin : eLpNorm F p₀ volume < ∞) : LocallyIntegrableOn f univ := by
  rw [locallyIntegrableOn_iff isOpen_univ.isLocallyClosed]
  intro K _ hK
  refine ⟨hf.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
  calc ∫⁻ z in K, ‖f z‖ₑ ≤ ∫⁻ z in K, ENNReal.ofReal (Real.exp C) * ‖F z‖ₑ := by
        refine setLIntegral_mono' hK.measurableSet fun z hzK ↦ ?_
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, hFnorm z]
        apply ENNReal.ofReal_le_ofReal
        have h1 : Real.exp (φ z) ≤ Real.exp C :=
          Real.exp_le_exp.2 ((le_abs_self _).trans (hC z hzK))
        calc ‖f z‖ = Real.exp (φ z) * (‖f z‖ * Real.exp (-φ z)) := by
              rw [Real.exp_neg]; field_simp
          _ ≤ Real.exp C * (‖f z‖ * Real.exp (-φ z)) := by gcongr
    _ = ENNReal.ofReal (Real.exp C) * ∫⁻ z in K, ‖F z‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lintegral_lt_top_of_eLpNorm_volume hF.eNorm.aestronglyMeasurable hK hp₀
          (by rwa [eLpNorm_eNorm _ hF]))

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
            eLpNorm (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) p volume := by
  set u : ℂ → ℂ := fun z ↦ ∫ ζ, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ
  set F : ℂ → ℂ := fun z ↦ f z * (Real.exp (-φ z) : ℝ) with hFdef
  obtain ⟨p₀, hp₀, hFfin⟩ := hadm
  have hA : 1 ≤ A := by
    have := hHb 0 0
    simpa [hH1 0] using this
  have hpi := Real.pi_pos
  have hAπ : 0 ≤ A / Real.pi := div_nonneg (by linarith) hpi.le
  have hEc : Continuous fun z : ℂ ↦ ((Real.exp (-φ z) : ℝ) : ℂ) := by fun_prop
  have hF : AEStronglyMeasurable F volume := hf.mul hEc.aestronglyMeasurable
  have hFe : AEMeasurable (fun z ↦ ‖F z‖ₑ) volume := hF.eNorm
  have hFnorm : ∀ ζ, ‖F ζ‖ = ‖f ζ‖ * Real.exp (-φ ζ) := by
    intro ζ
    rw [hFdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  set TF : ℂ → ℝ≥0∞ := fun z ↦ ∫⁻ ζ, planeModel c z ζ * ‖F ζ‖ₑ with hTF
  have hTFm : AEStronglyMeasurable TF volume := by
    have : AEMeasurable (fun q : ℂ × ℂ ↦ planeModel c q.1 q.2 * ‖F q.2‖ₑ)
        (volume.prod volume) :=
      (measurable_planeModel c).aemeasurable.mul hFe.comp_snd
    exact this.lintegral_prod_right'.aestronglyMeasurable
  have hTFb : ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm TF p volume ≤
        ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / c)) * eLpNorm F p volume := by
    intro p hp
    have := eLpNorm_planeModel_le hc hFe hp
    rwa [eLpNorm_eNorm _ hF] at this
  have hker : ∀ z ζ, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ ≤
      A / Real.pi * Real.exp (φ z - φ ζ) * (Real.exp (-c * ‖z - ζ‖ ^ 2) / ‖z - ζ‖) :=
    norm_planeKernelH_le hHb
  have hKP : ∀ z, ∫⁻ ζ, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ ≤
      ENNReal.ofReal (A / Real.pi * Real.exp (φ z)) * TF z := by
    intro z
    simp only [hTF]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ζ ↦ ?_
    simp only [planeModel]
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), hFnorm ζ]
    apply ENNReal.ofReal_le_ofReal
    calc ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ * ‖f ζ‖
        ≤ (A / Real.pi * Real.exp (φ z - φ ζ) *
            (Real.exp (-c * ‖z - ζ‖ ^ 2) / ‖z - ζ‖)) * ‖f ζ‖ :=
          mul_le_mul_of_nonneg_right (hker z ζ) (norm_nonneg _)
      _ = _ := by
          rw [Real.exp_sub, Real.exp_neg]
          field_simp
  have hfl : LocallyIntegrableOn f univ :=
    locallyIntegrableOn_univ_of_eLpNorm hφ hf hF hFnorm hp₀ hFfin
  have hloc : ∀ K ⊆ (univ : Set ℂ), IsCompact K →
      ∫⁻ z in K, ∫⁻ ζ in univ, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ < ∞ := by
    intro K _ hK
    simp only [Measure.restrict_univ]
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
    calc ∫⁻ z in K, ∫⁻ ζ, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ
        ≤ ∫⁻ z in K, ENNReal.ofReal (A / Real.pi * Real.exp C) * TF z := by
          refine setLIntegral_mono' hK.measurableSet fun z hzK ↦ (hKP z).trans ?_
          gcongr
          exact (le_abs_self _).trans (hC z hzK)
      _ = ENNReal.ofReal (A / Real.pi * Real.exp C) * ∫⁻ z in K, TF z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lintegral_lt_top_of_eLpNorm_volume hTFm hK hp₀
            ((hTFb p₀ hp₀).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFfin)))
  have hfu : AEStronglyMeasurable f (volume.restrict univ) := by
    rw [Measure.restrict_univ]; exact hf
  have hsol := isWeakDbarSol_kernel isOpen_univ hHm (fun ζ _ ↦ (hHd ζ).differentiableOn)
    (fun ζ _ ↦ hH1 ζ) hfu hfl hloc
  simp only [Measure.restrict_univ] at hsol
  refine ⟨hsol, fun p hp ↦ ?_⟩
  have hum : AEStronglyMeasurable u volume := by
    have := weak_aestronglyMeasurable_kernelOp hHm hfu
    simpa only [Measure.restrict_univ] using this
  have hv : AEStronglyMeasurable (fun z ↦ u z * ((Real.exp (-φ z) : ℝ) : ℂ)) volume :=
    hum.mul hEc.aestronglyMeasurable
  have hpt : ∀ᵐ z ∂volume, ‖u z * ((Real.exp (-φ z) : ℝ) : ℂ)‖ₑ ≤
      ‖ENNReal.ofReal (A / Real.pi) * TF z‖ₑ :=
    Filter.Eventually.of_forall fun z ↦ kernel_eNorm_mul_le hAπ (hKP z)
  refine (eLpNorm_kernel_le hAπ hv hTFm hpt (hTFb p hp)).trans_eq ?_
  congr 2
  field_simp

/-! ## §6 Lemma 7 -/

/-- The kernel of Lemma 7, `K(z, ζ) = (1/π) (1 - |ζ|²) / ((1 - ζ̄ z)(z - ζ))`. -/
def discKernel (z ζ : ℂ) : ℂ :=
  ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) / (1 - conj ζ * z) / ((Real.pi : ℂ) * (z - ζ))

/-- The solution operator of Lemma 7. -/
def lemma7Op (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ ζ in 𝔻, discKernel z ζ * f ζ

/-- The numerator `H(z, ζ) = (1 - |ζ|²)/(1 - ζ̄ z)` of the kernel of Lemma 7. -/
def lemma7H (z ζ : ℂ) : ℂ := ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) / (1 - conj ζ * z)

theorem measurable_lemma7H : Measurable (Function.uncurry lemma7H) := by
  unfold lemma7H Function.uncurry
  fun_prop

theorem differentiableOn_lemma7H {ζ : ℂ} (hζ : ζ ∈ 𝔻) :
    DifferentiableOn ℂ (fun z ↦ lemma7H z ζ) 𝔻 := by
  unfold lemma7H
  have hden : DifferentiableOn ℂ (fun z : ℂ ↦ 1 - conj ζ * z) 𝔻 :=
    (differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)
  have hnum : DifferentiableOn ℂ (fun _ : ℂ ↦ ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ)) 𝔻 :=
    differentiableOn_const _
  exact hnum.div hden fun z hz ↦ one_sub_conj_mul_ne_zero_of_mem hζ hz

theorem lemma7H_self {ζ : ℂ} (hζ : ζ ∈ 𝔻) : lemma7H ζ ζ = 1 := by
  rw [lemma7H, one_sub_conj_mul_self]
  exact div_self (by exact_mod_cast (one_sub_normSq_pos hζ).ne')

theorem norm_lemma7H {z ζ : ℂ} (hζ : ζ ∈ 𝔻) :
    ‖lemma7H z ζ‖ = (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ := by
  rw [lemma7H, norm_div, Complex.norm_real, Real.norm_of_nonneg (one_sub_normSq_pos hζ).le]

theorem lemma7Op_eq (f : ℂ → ℂ) :
    lemma7Op f = fun z ↦ ∫ ζ in 𝔻, lemma7H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ := rfl

theorem lemma7_isWeakDbarSol {f : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hfi : ∫⁻ ζ in 𝔻, ‖f ζ‖ₑ * ENNReal.ofReal (1 - ‖ζ‖ ^ 2) < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f := by
  rw [lemma7Op_eq]
  have hpi := Real.pi_pos
  refine isWeakDbarSol_kernel isOpen_ball measurable_lemma7H
    (fun ζ hζ ↦ differentiableOn_lemma7H hζ) (fun ζ hζ ↦ lemma7H_self hζ) hf ?_ ?_
  · -- local integrability of `f`
    rw [locallyIntegrableOn_iff isOpen_ball.isLocallyClosed]
    intro K hKD hK
    refine ⟨hf.mono_measure (Measure.restrict_mono hKD le_rfl), ?_⟩
    rw [hasFiniteIntegral_iff_eNorm]
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuousOn_discDensity.mono hKD)
    calc ∫⁻ z in K, ‖f z‖ₑ
        ≤ ∫⁻ z in K, ENNReal.ofReal B * (‖f z‖ₑ * ENNReal.ofReal (1 - ‖z‖ ^ 2)) := by
          refine setLIntegral_mono' hK.measurableSet fun z hzK ↦ ?_
          have hz0 := one_sub_normSq_pos (hKD hzK)
          have hB' : 1 / (1 - ‖z‖ ^ 2) ≤ B := (le_abs_self _).trans (hB z hzK)
          have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z hzK)
          rw [mul_comm (‖f z‖ₑ), ← mul_assoc, ← ENNReal.ofReal_mul hB0]
          calc ‖f z‖ₑ = 1 * ‖f z‖ₑ := (one_mul _).symm
            _ ≤ ENNReal.ofReal (B * (1 - ‖z‖ ^ 2)) * ‖f z‖ₑ := by
                gcongr
                rw [ENNReal.one_le_ofReal, ← div_le_iff₀ hz0]
                exact hB'
      _ = ENNReal.ofReal B * ∫⁻ z in K, ‖f z‖ₑ * ENNReal.ofReal (1 - ‖z‖ ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal B * ∫⁻ z in 𝔻, ‖f z‖ₑ * ENNReal.ofReal (1 - ‖z‖ ^ 2) := by
          gcongr
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfi
  · -- the local Fubini condition
    intro K hKD hK
    obtain ⟨r, hr1, hKr⟩ := exists_lt_subset_ball hK.isClosed hKD
    set C0 : ℝ := 1 / (Real.pi * (1 - r)) with hC0
    have hC0p : 0 ≤ C0 := by
      have : 0 < 1 - r := by linarith
      positivity
    set g : ℂ → ℝ≥0∞ := fun ζ ↦ ‖f ζ‖ₑ * ENNReal.ofReal (1 - ‖ζ‖ ^ 2) with hg
    have hgm : AEMeasurable g (volume.restrict 𝔻) := hf.eNorm.mul (by fun_prop)
    calc ∫⁻ z in K, ∫⁻ ζ in 𝔻, ‖lemma7H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ
        ≤ ∫⁻ z in K, ∫⁻ ζ in 𝔻, ENNReal.ofReal (C0 * ‖z - ζ‖⁻¹) * g ζ := by
          refine setLIntegral_mono' hK.measurableSet fun z hzK ↦ ?_
          refine setLIntegral_mono' measurableSet_ball fun ζ hζ ↦ ?_
          have hzr : ‖z‖ < r := by simpa using hKr hzK
          have hζ0 := one_sub_normSq_pos hζ
          have hY : 1 - r ≤ ‖1 - conj ζ * z‖ := by
            have := one_sub_mul_le_norm_one_sub_conj_mul ζ z
            have hζ1 := norm_lt_one_of_mem_disc hζ
            nlinarith [norm_nonneg ζ, norm_nonneg z]
          have hr0 : 0 < 1 - r := by linarith
          rw [hg, ← mul_assoc, ← ofReal_norm, ← ofReal_norm (f ζ),
            ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [norm_div, norm_lemma7H hζ, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg hpi.le]
          rcases eq_or_ne z ζ with rfl | hne
          · simp
          have hZ : 0 < ‖z - ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
          rw [hC0]
          have hYp : 0 < ‖1 - conj ζ * z‖ := lt_of_lt_of_le hr0 hY
          calc _ = (1 - ‖ζ‖ ^ 2) * ‖f ζ‖ / (‖1 - conj ζ * z‖ * (Real.pi * ‖z - ζ‖)) := by
                field_simp
            _ ≤ (1 - ‖ζ‖ ^ 2) * ‖f ζ‖ / ((1 - r) * (Real.pi * ‖z - ζ‖)) := by
                gcongr
            _ = _ := by field_simp
      _ = ∫⁻ ζ in 𝔻, ∫⁻ z in K, ENNReal.ofReal (C0 * ‖z - ζ‖⁻¹) * g ζ := by
          refine lintegral_lintegral_swap ?_
          exact ((by fun_prop : Measurable fun q : ℂ × ℂ ↦
            ENNReal.ofReal (C0 * ‖q.1 - q.2‖⁻¹)).aemeasurable).mul hgm.comp_snd
      _ = ∫⁻ ζ in 𝔻, g ζ * (ENNReal.ofReal C0 * ∫⁻ z in K, ENNReal.ofReal ‖z - ζ‖⁻¹) := by
          refine lintegral_congr fun ζ ↦ ?_
          rw [lintegral_mul_const _ (by fun_prop), mul_comm]
          congr 1
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun z ↦ ?_
          rw [← ENNReal.ofReal_mul hC0p]
      _ ≤ ∫⁻ ζ in 𝔻, g ζ * (ENNReal.ofReal C0 * (ENNReal.ofReal (2 * Real.pi) + volume K)) := by
          gcongr with ζ
          exact lintegral_inv_norm_sub_le_of_set K ζ
      _ = (∫⁻ ζ in 𝔻, g ζ) * (ENNReal.ofReal C0 * (ENNReal.ofReal (2 * Real.pi) + volume K)) :=
          lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hK.measure_lt_top.ne⟩))
      _ < ∞ := ENNReal.mul_lt_top hfi (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hK.measure_lt_top⟩))

theorem lemma7 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hadm : ∃ p : ℝ≥0∞, 1 ≤ p ∧ eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α) : ℝ)) p
      discMeasure < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm (fun z ↦ lemma7Op f z * ((1 - ‖z‖ ^ 2) ^ α : ℝ)) p discMeasure ≤
        ENNReal.ofReal (24 / (α * (1 - α))) *
          eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α) : ℝ)) p discMeasure := by
  set φ : ℂ → ℝ := fun z ↦ -α * Real.log (1 - ‖z‖ ^ 2) with hφ
  have hφc : ContinuousOn φ 𝔻 :=
    continuousOn_const.mul ((by fun_prop : Continuous fun z : ℂ ↦ 1 - ‖z‖ ^ 2).continuousOn.log
      fun z hz ↦ (one_sub_normSq_pos hz).ne')
  have hexp : ∀ z ∈ 𝔻, Real.exp (-φ z) = (1 - ‖z‖ ^ 2) ^ α := by
    intro z hz
    simp only [hφ, neg_mul, neg_neg]
    rw [Real.rpow_def_of_pos (one_sub_normSq_pos hz), mul_comm]
  have hW : ∀ z ∈ 𝔻, (1 - ‖z‖ ^ 2) * Real.exp (-φ z) = (1 - ‖z‖ ^ 2) ^ (1 + α) := by
    intro z hz
    rw [hexp z hz, Real.rpow_add (one_sub_normSq_pos hz), Real.rpow_one]
  have hRHS : ∀ p, eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure =
      eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α) : ℝ)) p discMeasure := by
    intro p
    refine eLpNorm_congr_ae (ae_discMeasure_mem.mono fun z hz ↦ ?_)
    simp only [hW z hz]
  have hHb : ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻, ‖lemma7H z ζ‖ ≤ 1 * Real.exp (φ z - φ ζ) *
      ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ α * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) := by
    intro z hz ζ hζ
    have hz0 := one_sub_normSq_pos hz
    have hζ0 := one_sub_normSq_pos hζ
    rw [norm_lemma7H hζ, Real.exp_sub]
    simp only [hφ]
    rw [mul_comm (-α), ← Real.rpow_def_of_pos hz0, mul_comm (-α), ← Real.rpow_def_of_pos hζ0,
      Real.div_rpow hz0.le hζ0.le, Real.rpow_neg hz0.le, Real.rpow_neg hζ0.le]
    have := Real.rpow_pos_of_pos hz0 α
    have := Real.rpow_pos_of_pos hζ0 α
    apply le_of_eq
    field_simp
  obtain ⟨hsol, hest⟩ := disc_kernel_operator hφc hα0 hα1 measurable_lemma7H
    (fun ζ hζ ↦ differentiableOn_lemma7H hζ) (fun ζ hζ ↦ lemma7H_self hζ) hHb f hf
    (by obtain ⟨p, hp, h⟩ := hadm; exact ⟨p, hp, by rwa [hRHS]⟩)
  refine ⟨hsol, fun p hp ↦ ?_⟩
  have := hest p hp
  rw [hRHS, mul_one] at this
  calc eLpNorm (fun z ↦ lemma7Op f z * ((1 - ‖z‖ ^ 2) ^ α : ℝ)) p discMeasure
      = eLpNorm (fun z ↦ (∫ ζ in 𝔻, lemma7H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) *
          (Real.exp (-φ z) : ℝ)) p discMeasure := by
        refine eLpNorm_congr_ae (ae_discMeasure_mem.mono fun z hz ↦ ?_)
        simp only [hexp z hz]
        rfl
    _ ≤ _ := this

/-- `‖G (1-|z|²)^b‖_{L^p(ν)}^p = ∫_𝔻 |G|^p (1-|z|²)^{bp-1} dm`. -/
theorem eLpNorm_rpow_discMeasure {G : ℂ → ℂ} (hG : AEStronglyMeasurable G discMeasure)
    {b p : ℝ} (hp : 0 < p) :
    eLpNorm (fun z ↦ G z * ((1 - ‖z‖ ^ 2) ^ b : ℝ)) (ENNReal.ofReal p) discMeasure ^ p =
      ∫⁻ z in 𝔻, ENNReal.ofReal (‖G z‖ ^ p * (1 - ‖z‖ ^ 2) ^ (b * p - 1)) := by
  have hm : AEStronglyMeasurable (fun z ↦ G z * ((1 - ‖z‖ ^ 2) ^ b : ℝ)) discMeasure :=
    hG.mul (by fun_prop : Measurable fun z : ℂ ↦ (((1 - ‖z‖ ^ 2) ^ b : ℝ) : ℂ)).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hm,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    discMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
      measurable_discDensity (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
  have hz0 := one_sub_normSq_pos hz
  simp only [Pi.mul_apply]
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hz0.le _),
    Real.mul_rpow (norm_nonneg _) (Real.rpow_nonneg hz0.le _), ← Real.rpow_mul hz0.le,
    Real.rpow_sub_one hz0.ne']
  field_simp

theorem lemma7_Lp_printed {α p : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hfin : ∫⁻ z in 𝔻, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧
      ∫⁻ z in 𝔻, ENNReal.ofReal (‖lemma7Op f z‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) ≤
        ENNReal.ofReal ((24 * p ^ 2 / (α * (p - α))) ^ p) *
          ∫⁻ z in 𝔻, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) := by
  have hp0 : 0 < p := by linarith
  have ha0 : 0 < α / p := div_pos hα0 hp0
  have ha1 : α / p < 1 := (div_lt_one hp0).2 (by linarith)
  have hνac : discMeasure ≪ volume.restrict 𝔻 := withDensity_absolutelyContinuous _ _
  have hfν : AEStronglyMeasurable f discMeasure := hf.mono_ac hνac
  have huν : AEStronglyMeasurable (lemma7Op f) discMeasure :=
    (weak_aestronglyMeasurable_kernelOp measurable_lemma7H hf).restrict.mono_ac hνac
  have hF : eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α / p) : ℝ)) (ENNReal.ofReal p)
      discMeasure ^ p =
      ∫⁻ z in 𝔻, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) := by
    rw [eLpNorm_rpow_discMeasure hfν hp0]
    refine setLIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
    have hz0 := one_sub_normSq_pos hz
    congr 1
    have e : (1 - (‖z‖ : ℂ) ^ 2) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hz0.le,
      Real.mul_rpow (norm_nonneg _) hz0.le, mul_assoc, ← Real.rpow_add hz0]
    congr 2
    field_simp
    ring
  have hU : eLpNorm (fun z ↦ lemma7Op f z * ((1 - ‖z‖ ^ 2) ^ (α / p) : ℝ)) (ENNReal.ofReal p)
      discMeasure ^ p =
      ∫⁻ z in 𝔻, ENNReal.ofReal (‖lemma7Op f z‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) := by
    rw [eLpNorm_rpow_discMeasure huν hp0]
    refine setLIntegral_congr_fun measurableSet_ball fun z _ ↦ ?_
    congr 3
    field_simp
  have hadm : eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α / p) : ℝ)) (ENNReal.ofReal p)
      discMeasure < ∞ := by
    rw [← ENNReal.rpow_lt_top_iff_of_pos hp0, hF]
    exact hfin
  obtain ⟨hsol, hest⟩ := lemma7 ha0 ha1 f hf
    ⟨ENNReal.ofReal p, ENNReal.one_le_ofReal.2 hp, hadm⟩
  refine ⟨hsol, ?_⟩
  have h := ENNReal.rpow_le_rpow (hest (ENNReal.ofReal p) (ENNReal.one_le_ofReal.2 hp)) hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hU, hF,
    ENNReal.ofReal_rpow_of_nonneg (by
      have : 0 < α / p * (1 - α / p) := mul_pos ha0 (by linarith)
      positivity) hp0.le] at h
  convert h using 4
  have hpa : 0 < p - α := by linarith
  field_simp

theorem lemma7_sup {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻)) {M : ℝ}
    (hM : ∀ᵐ ζ ∂(volume.restrict 𝔻), ‖f ζ‖ * (1 - ‖ζ‖ ^ 2) ^ (1 + α) ≤ M) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧
      ∀ z ∈ 𝔻, ‖lemma7Op f z‖ * (1 - ‖z‖ ^ 2) ^ α ≤ 24 / (α * (1 - α)) * M := by
  have hpi := Real.pi_pos
  have h0 : (0 : ℂ) ∈ 𝔻 := mem_ball_self one_pos
  have hvol : volume.restrict 𝔻 ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact (measure_ball_pos volume (0 : ℂ) one_pos).ne'
  have : (ae (volume.restrict 𝔻)).NeBot := ae_neBot.2 hvol
  have hM0 : 0 ≤ M := by
    obtain ⟨ζ, hζ⟩ := (hM.and (ae_restrict_mem measurableSet_ball)).exists
    exact le_trans (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (one_sub_normSq_pos hζ.2).le _)) hζ.1
  have hM' : ∀ᵐ ζ ∂(volume.restrict 𝔻),
      ‖f ζ‖ * (1 - ‖ζ‖ ^ 2) ≤ M * (1 - ‖ζ‖ ^ 2) ^ (-α) := by
    filter_upwards [hM, ae_restrict_mem measurableSet_ball] with ζ h hζ
    have hζ0 := one_sub_normSq_pos hζ
    rw [Real.rpow_add hζ0, Real.rpow_one] at h
    rw [Real.rpow_neg hζ0.le]
    have := Real.rpow_pos_of_pos hζ0 α
    rw [le_mul_inv_iff₀ this]
    linarith [h]
  have hfi : ∫⁻ ζ in 𝔻, ‖f ζ‖ₑ * ENNReal.ofReal (1 - ‖ζ‖ ^ 2) < ∞ := by
    calc ∫⁻ ζ in 𝔻, ‖f ζ‖ₑ * ENNReal.ofReal (1 - ‖ζ‖ ^ 2)
        ≤ ∫⁻ ζ in 𝔻, ENNReal.ofReal M *
            ENNReal.ofReal ((1 - ‖ζ‖) ^ (-α) / ‖1 - conj 0 * ζ‖ ^ 2) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hM', ae_restrict_mem measurableSet_ball] with ζ h hζ
          have hζ1 := norm_lt_one_of_mem_disc hζ
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul hM0]
          apply ENNReal.ofReal_le_ofReal
          simp only [map_zero, zero_mul, sub_zero, norm_one, one_pow, div_one]
          refine h.trans (mul_le_mul_of_nonneg_left ?_ hM0)
          exact Real.rpow_le_rpow_of_nonpos (by linarith)
            (by nlinarith [norm_nonneg ζ]) (by linarith)
      _ = ENNReal.ofReal M * ∫⁻ ζ in 𝔻,
            ENNReal.ofReal ((1 - ‖ζ‖) ^ (-α) / ‖1 - conj 0 * ζ‖ ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal
            (2 * Real.pi / (α * (1 - α)) * (1 - ‖(0 : ℂ)‖) ^ (-α)) := by
          gcongr
          exact lintegral_disc_rpow_div_normSq hα0 hα1 h0
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨lemma7_isWeakDbarSol hf hfi, fun z hz ↦ ?_⟩
  have hz0 := one_sub_normSq_pos hz
  have hint : ∫⁻ ζ in 𝔻, ENNReal.ofReal ‖discKernel z ζ * f ζ‖ ≤
      ENNReal.ofReal (M / Real.pi * (24 * Real.pi / (α * (1 - α)) * (1 - ‖z‖ ^ 2) ^ (-α))) := by
    calc ∫⁻ ζ in 𝔻, ENNReal.ofReal ‖discKernel z ζ * f ζ‖
        ≤ ∫⁻ ζ in 𝔻, ENNReal.ofReal (M / Real.pi) *
            ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ (-α) / (‖1 - conj z * ζ‖ * ‖z - ζ‖)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hM', ae_restrict_mem measurableSet_ball] with ζ h hζ
          rw [← ENNReal.ofReal_mul (div_nonneg hM0 hpi.le)]
          apply ENNReal.ofReal_le_ofReal
          rw [norm_mul, discKernel, norm_div, norm_div, norm_mul, Complex.norm_real,
            Complex.norm_real, Real.norm_of_nonneg (one_sub_normSq_pos hζ).le,
            Real.norm_of_nonneg hpi.le, mk_norm_one_sub_conj_mul_comm ζ z]
          rcases eq_or_ne z ζ with rfl | hne
          · simp
          have hZ : 0 < ‖z - ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
          have hY := norm_one_sub_conj_mul_pos hz hζ
          calc (1 - ‖ζ‖ ^ 2) / ‖1 - conj z * ζ‖ / (Real.pi * ‖z - ζ‖) * ‖f ζ‖
              = (‖f ζ‖ * (1 - ‖ζ‖ ^ 2)) / (Real.pi * (‖1 - conj z * ζ‖ * ‖z - ζ‖)) := by
                field_simp
            _ ≤ (M * (1 - ‖ζ‖ ^ 2) ^ (-α)) / (Real.pi * (‖1 - conj z * ζ‖ * ‖z - ζ‖)) := by
                gcongr
            _ = M / Real.pi * ((1 - ‖ζ‖ ^ 2) ^ (-α) / (‖1 - conj z * ζ‖ * ‖z - ζ‖)) := by
                field_simp
      _ = ENNReal.ofReal (M / Real.pi) * ∫⁻ ζ in 𝔻,
            ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ (-α) / (‖1 - conj z * ζ‖ * ‖z - ζ‖)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M / Real.pi) *
            ENNReal.ofReal (24 * Real.pi / (α * (1 - α)) * (1 - ‖z‖ ^ 2) ^ (-α)) := by
          gcongr
          exact lintegral_FR hα0 hα1 hz
      _ = _ := (ENNReal.ofReal_mul (div_nonneg hM0 hpi.le)).symm
  have hP := Real.rpow_pos_of_pos hz0 α
  have h1 : ‖lemma7Op f z‖ ≤
      M / Real.pi * (24 * Real.pi / (α * (1 - α)) * (1 - ‖z‖ ^ 2) ^ (-α)) := by
    unfold lemma7Op
    exact (norm_integral_le_lintegral_norm _).trans
      (ENNReal.toReal_le_of_le_ofReal (by
        have : 0 < α * (1 - α) := mul_pos hα0 (by linarith)
        have := Real.rpow_nonneg hz0.le (-α)
        positivity) hint)
  calc ‖lemma7Op f z‖ * (1 - ‖z‖ ^ 2) ^ α
      ≤ (M / Real.pi * (24 * Real.pi / (α * (1 - α)) * (1 - ‖z‖ ^ 2) ^ (-α))) *
          (1 - ‖z‖ ^ 2) ^ α := mul_le_mul_of_nonneg_right h1 hP.le
    _ = 24 / (α * (1 - α)) * M := by
        rw [Real.rpow_neg hz0.le]
        have : α * (1 - α) ≠ 0 := (mul_pos hα0 (by linarith)).ne'
        field_simp

/-! ## §7 Lemma 8 -/

/-- The kernel of Lemma 8, `(1/π) e^{2α(ζ̄ z - |ζ|²)} / (z - ζ)`. -/
def planeKernel (α : ℝ) (z ζ : ℂ) : ℂ :=
  Complex.exp (2 * α * (conj ζ * z - ((‖ζ‖ ^ 2 : ℝ) : ℂ))) / ((Real.pi : ℂ) * (z - ζ))

/-- The operator `f ↦ ∫ K_α(z, ζ) f(ζ)` of Lemma 8, with kernel `planeKernel`. -/
def lemma8Op (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ ζ, planeKernel α z ζ * f ζ

theorem norm_exp_planeKernel_num (α : ℝ) (z ζ : ℂ) :
    ‖Complex.exp (2 * α * (conj ζ * z - ((‖ζ‖ ^ 2 : ℝ) : ℂ)))‖ =
      Real.exp (α * ‖z‖ ^ 2 - α * ‖ζ‖ ^ 2) * Real.exp (-α * ‖z - ζ‖ ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp only [Complex.sq_norm, Complex.normSq_apply, mul_re, sub_re, ofReal_re, conj_re,
    conj_im, mul_im, ofReal_im, sub_im, re_ofNat, im_ofNat]
  ring

theorem lemma8 {α : ℝ} (hα : 0 < α) (f : ℂ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hadm : ∃ p : ℝ≥0∞, 1 ≤ p ∧
      eLpNorm (fun z ↦ f z * (Real.exp (-α * ‖z‖ ^ 2) : ℂ)) p volume < ∞) :
    IsWeakDbarSol univ (lemma8Op α f) f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm (fun z ↦ lemma8Op α f z * (Real.exp (-α * ‖z‖ ^ 2) : ℂ)) p volume ≤
        ENNReal.ofReal (Real.sqrt (Real.pi / α)) *
          eLpNorm (fun z ↦ f z * (Real.exp (-α * ‖z‖ ^ 2) : ℂ)) p volume := by
  set φ : ℂ → ℝ := fun z ↦ α * ‖z‖ ^ 2 with hφ
  set H : ℂ → ℂ → ℂ := fun z ζ ↦ Complex.exp (2 * α * (conj ζ * z - ((‖ζ‖ ^ 2 : ℝ) : ℂ)))
    with hH
  have hφe : ∀ z, -φ z = -α * ‖z‖ ^ 2 := fun z ↦ by simp only [hφ]; ring
  have hfun : (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) =
      fun z ↦ f z * (Real.exp (-α * ‖z‖ ^ 2) : ℂ) := by
    funext z; rw [hφe]
  have hHm : Measurable (Function.uncurry H) := by
    simp only [hH]
    fun_prop
  have hHd : ∀ ζ, Differentiable ℂ (fun z ↦ H z ζ) := fun ζ ↦ by
    simp only [hH]
    fun_prop
  have hH1 : ∀ ζ, H ζ ζ = 1 := fun ζ ↦ by
    simp only [hH, Complex.conj_mul']
    push_cast
    simp
  have hHb : ∀ z ζ, ‖H z ζ‖ ≤ 1 * Real.exp (φ z - φ ζ) * Real.exp (-α * ‖z - ζ‖ ^ 2) :=
    fun z ζ ↦ by
      rw [hH, norm_exp_planeKernel_num, one_mul]
  obtain ⟨hsol, hest⟩ := plane_kernel_operator (by fun_prop) hα hHm hHd hH1 hHb f hf
    (by rwa [hfun])
  refine ⟨hsol, fun p hp ↦ ?_⟩
  have := hest p hp
  rw [hfun, one_mul] at this
  convert this using 3 with z
  rw [hφe]
  rfl

end OC
