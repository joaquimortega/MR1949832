import OrtegaCerdaMultipliers.Foundations.Basic
import OrtegaCerdaMultipliers.Foundations.Wirtinger
import OrtegaCerdaMultipliers.Foundations.Polar

/-!
# M01 (Foundations) — Cauchy–Pompeiu formula and the Cauchy transform

See `blueprint/M01_Foundations.md`.

**Provenance.** Copied from `BerndtssonOrtegaCerda/Complex/Pompeiu.lean`
(BOC module M05, blueprint `M05_Pompeiu.md`) of the companion project
`../1995ReineAngewMath` at commit `22104d9` (same author, Apache-2.0).  Changes: namespace
`BOC` → `OC`, imports adjusted; the BOC definitions not in `OrtegaCerdaMultipliers/Defs.lean`
are in `Foundations/Basic.lean`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate Topology Convolution

noncomputable section

namespace OC

/-- Cauchy transform `C[f](w) = (1/π) ∫ f(z)/(w − z) dm(z)`. -/
def cauchyTransform (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  (1 / Real.pi : ℂ) * ∫ z, f z / (w - z)

/-! ### Polar coordinates around a point -/

/-- The unit vector `e^{iθ}`, written as in `Complex.polarCoord_symm_apply`. -/
def unitVec (θ : ℝ) : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I

lemma conj_unitVec (θ : ℝ) : conj (unitVec θ) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
  simp only [unitVec, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma unitVec_mul_conj (θ : ℝ) : unitVec θ * conj (unitVec θ) = 1 := by
  rw [conj_unitVec, unitVec]
  have h : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.cos_sq_add_sin_sq]
    simp
  linear_combination h - (Real.sin θ : ℂ) ^ 2 * I_sq

lemma norm_unitVec (θ : ℝ) : ‖unitVec θ‖ = 1 := by
  have := unitVec_mul_conj θ
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
  have h2 : ‖unitVec θ‖ ^ 2 = 1 := by exact_mod_cast this
  have := norm_nonneg (unitVec θ)
  nlinarith

lemma unitVec_ne_zero (θ : ℝ) : unitVec θ ≠ 0 := by
  intro h; have := norm_unitVec θ; rw [h, norm_zero] at this; exact zero_ne_one this

lemma hasDerivAt_unitVec (θ : ℝ) : HasDerivAt unitVec (I * unitVec θ) θ := by
  have h1 := (Real.hasDerivAt_cos θ).ofReal_comp
  have h2 := ((Real.hasDerivAt_sin θ).ofReal_comp).mul_const I
  convert h1.add h2 using 1
  · ext y; simp [unitVec]
  · simp only [unitVec, Complex.ofReal_neg]
    linear_combination (Real.sin θ : ℂ) * I_sq

lemma continuous_unitVec : Continuous unitVec := by
  unfold unitVec; fun_prop

lemma unitVec_pi : unitVec Real.pi = unitVec (-Real.pi) := by simp [unitVec]

lemma two_dbar_mul_conj (L : ℂ →L[ℝ] ℂ) (θ : ℝ) :
    (L 1 + I * L I) * conj (unitVec θ) = L (unitVec θ) + I * L (I * unitVec θ) := by
  have e1 : unitVec θ = (Real.cos θ) • (1:ℂ) + (Real.sin θ) • I := by
    simp [unitVec, Complex.real_smul]
  have e2 : I * unitVec θ = (Real.cos θ) • I + (-Real.sin θ) • (1:ℂ) := by
    simp only [unitVec, Complex.real_smul, Complex.ofReal_neg]
    linear_combination (Real.sin θ : ℂ) * I_sq
  rw [conj_unitVec, e2, e1, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  simp only [Complex.real_smul, Complex.ofReal_neg]
  linear_combination (- (Real.sin θ : ℂ) * L I) * I_sq

lemma fderiv_eq_zero_of_closedBall_lt {α : ℂ → ℂ} {w : ℂ} {R : ℝ} (hR : tsupport α ⊆ closedBall w R)
    {ζ : ℂ} (hζ : R < ‖ζ - w‖) : fderiv ℝ α ζ = 0 := by
  have : ζ ∉ tsupport α := fun h => by
    have := hR h; rw [mem_closedBall, dist_eq_norm] at this; linarith
  exact Function.notMem_support.mp (fun h => this (support_fderiv_subset ℝ h))

lemma eq_zero_of_closedBall_lt {α : ℂ → ℂ} {w : ℂ} {R : ℝ} (hR : tsupport α ⊆ closedBall w R)
    {ζ : ℂ} (hζ : R < ‖ζ - w‖) : α ζ = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h; have := hR h; rw [mem_closedBall, dist_eq_norm] at this; linarith

lemma norm_add_ofReal_mul_unitVec_sub (w : ℂ) (r θ : ℝ) :
    ‖(w + (r : ℂ) * unitVec θ) - w‖ = |r| := by
  simp [norm_unitVec]

/-- A continuous function on `ℝ × ℝ` vanishing for `|r| > R` is integrable on the polar target. -/
lemma integrableOn_polarTarget_of_continuous {h : ℝ × ℝ → ℂ} (hc : Continuous h) {R : ℝ}
    (hz : ∀ p : ℝ × ℝ, R < |p.1| → h p = 0) :
    IntegrableOn h (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hK : IsCompact (Icc (0:ℝ) R ×ˢ Icc (-Real.pi) Real.pi) := isCompact_Icc.prod isCompact_Icc
  refine (hc.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero
    (measurableSet_Ioi.prod measurableSet_Ioo) ?_
  rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hn⟩
  simp only [mem_Ioi, mem_Ioo] at hr hθ
  simp only [mem_prod, mem_Icc, not_and_or, not_le] at hn
  apply hz
  rcases hn with (h | h) | (h | h)
  · linarith
  · rw [abs_of_pos hr]; exact h
  · linarith
  · linarith

lemma integrableOn_Ioi_of_continuous_of_eq_zero {h : ℝ → ℂ} (hc : Continuous h) {R : ℝ}
    (hz : ∀ r : ℝ, R < r → h r = 0) : IntegrableOn h (Ioi (0:ℝ)) := by
  refine (hc.continuousOn.integrableOn_compact
    (isCompact_Icc (a := (0:ℝ)) (b := R))).of_forall_sdiff_eq_zero
    measurableSet_Ioi ?_
  rintro r ⟨hr, hn⟩
  simp only [mem_Ioi] at hr
  simp only [mem_Icc, not_and_or, not_le] at hn
  apply hz
  rcases hn with h | h
  · linarith
  · exact h

/-- The polar form of `∫ ∂̄α(z)/(w − z)`. -/
lemma integral_dbar_div_eq {α : ℂ → ℂ} (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α)
    (w : ℂ) : ∫ z, dbar α z / (w - z) = Real.pi * α w := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall w
  have hDc : Continuous (fderiv ℝ α) := hα.continuous_fderiv one_ne_zero
  have hαd : Differentiable ℝ α := hα.differentiable one_ne_zero
  set h1 : ℝ × ℝ → ℂ := fun p => fderiv ℝ α (w + p.1 * unitVec p.2) (unitVec p.2) with hh1
  set h2 : ℝ × ℝ → ℂ := fun p => fderiv ℝ α (w + p.1 * unitVec p.2) (I * unitVec p.2) with hh2
  have hcu := continuous_unitVec
  have h1c : Continuous h1 := by
    refine (hDc.comp ?_).clm_apply (hcu.comp continuous_snd)
    exact continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_fst).mul (hcu.comp continuous_snd))
  have h2c : Continuous h2 := by
    refine (hDc.comp ?_).clm_apply (continuous_const.mul (hcu.comp continuous_snd))
    exact continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_fst).mul (hcu.comp continuous_snd))
  have h1z : ∀ p : ℝ × ℝ, R < |p.1| → h1 p = 0 := fun p hp => by
    simp only [h1]
    rw [fderiv_eq_zero_of_closedBall_lt hR (by rwa [norm_add_ofReal_mul_unitVec_sub])]; rfl
  have h2z : ∀ p : ℝ × ℝ, R < |p.1| → h2 p = 0 := fun p hp => by
    simp only [h2]
    rw [fderiv_eq_zero_of_closedBall_lt hR (by rwa [norm_add_ofReal_mul_unitVec_sub])]; rfl
  have hT : polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi := polarCoord_target
  have i1 := integrableOn_polarTarget_of_continuous h1c h1z
  have i2 := integrableOn_polarTarget_of_continuous h2c h2z
  -- Step 1: translation and polar coordinates
  have step1 : ∫ z, dbar α z / (w - z) =
      ∫ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, -(1/2 : ℂ) * (h1 p + I * h2 p) := by
    have e := integral_add_left_eq_self (μ := volume) (fun z => dbar α z / (w - z)) w
    rw [← e, ← Complex.integral_comp_polarCoord_symm, hT]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
    have hp1 : (p.1 : ℂ) ≠ 0 := by
      have : 0 < p.1 := hp.1
      exact_mod_cast this.ne'
    have hsym : Complex.polarCoord.symm p = p.1 * unitVec p.2 := by
      simp [Complex.polarCoord_symm_apply, unitVec]
    have key := two_dbar_mul_conj (fderiv ℝ α (w + p.1 * unitVec p.2)) p.2
    have hconj : conj (unitVec p.2) = (unitVec p.2)⁻¹ :=
      (inv_eq_of_mul_eq_one_right (unitVec_mul_conj p.2)).symm
    have hu := unitVec_ne_zero p.2
    simp only [hsym, h1, h2, ← key, dbar, Complex.real_smul, hconj]
    field_simp
    ring
  -- Step 2: the angular term integrates to zero
  have step2 : ∫ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, h2 p = 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod _ i2]
    refine (setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0:ℂ)) (fun r hr => ?_)).trans
      (by simp)
    have hr : 0 < r := hr
    have hderiv : ∀ θ : ℝ,
        HasDerivAt (fun θ : ℝ => α (w + (r:ℂ) * unitVec θ)) (r • h2 (r, θ)) θ := by
      intro θ
      have hγ : HasDerivAt (fun θ : ℝ => w + (r:ℂ) * unitVec θ) ((r:ℂ) * (I * unitVec θ)) θ :=
        ((hasDerivAt_unitVec θ).const_mul (r:ℂ)).const_add w
      have := (hαd (w + (r:ℂ) * unitVec θ)).hasFDerivAt.comp_hasDerivAt θ hγ
      rw [show ((r:ℂ) * (I * unitVec θ)) = r • (I * unitVec θ) from (Complex.real_smul ..).symm,
        map_smul] at this
      exact this
    have hcont : Continuous (fun θ : ℝ => r • h2 (r, θ)) :=
      (h2c.comp (Continuous.prodMk continuous_const continuous_id)).const_smul r
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
      (hcont.intervalIntegrable (-Real.pi) Real.pi)
    rw [unitVec_pi, sub_self, intervalIntegral.integral_smul,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
      at hftc
    exact (smul_eq_zero.mp hftc).resolve_left hr.ne'
  -- Step 3: the radial term gives `-2π α(w)`
  have step3 : ∫ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, h1 p = -(2 * Real.pi) • α w := by
    rw [Measure.volume_eq_prod, setIntegral_prod _ i1]
    rw [integral_integral_swap (by rw [Measure.prod_restrict]; exact i1)]
    have inner : ∀ θ : ℝ, ∫ r in Ioi (0:ℝ), h1 (r, θ) = -α w := by
      intro θ
      have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => α (w + (r:ℂ) * unitVec θ)) (h1 (r, θ)) r := by
        intro r
        have hγ : HasDerivAt (fun r : ℝ => w + (r:ℂ) * unitVec θ) (unitVec θ) r := by
          have := (((hasDerivAt_id r).ofReal_comp).mul_const (unitVec θ)).const_add w
          simpa using this
        exact (hαd (w + (r:ℂ) * unitVec θ)).hasFDerivAt.comp_hasDerivAt r hγ
      have hcf : Continuous (fun r : ℝ => α (w + (r:ℂ) * unitVec θ)) := by
        exact hα.continuous.comp
          (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
      have hint : IntegrableOn (fun r => h1 (r, θ)) (Ioi 0) :=
        integrableOn_Ioi_of_continuous_of_eq_zero
          (h1c.comp (Continuous.prodMk continuous_id continuous_const))
          (R := R) (fun r hr => h1z _ (lt_of_lt_of_le hr (le_abs_self r)))
      have hlim : Filter.Tendsto (fun r : ℝ => α (w + (r:ℂ) * unitVec θ)) Filter.atTop (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop (max R 0)] with r hr
        symm
        apply eq_zero_of_closedBall_lt hR
        rw [norm_add_ofReal_mul_unitVec_sub]
        exact lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hr (le_abs_self r))
      have := integral_Ioi_of_hasDerivAt_of_tendsto hcf.continuousWithinAt (fun r _ => hderiv r)
        hint hlim
      simpa using this
    rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => inner θ), setIntegral_const]
    rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]),
      smul_neg, neg_smul]
    ring_nf
  rw [step1, integral_const_mul, integral_add i1 (i2.const_mul I), integral_const_mul, step2, step3]
  rw [Complex.real_smul]
  push_cast
  ring


/-! ### Basic properties of `∂̄` on test functions -/

lemma continuous_dbar {α : ℂ → ℂ} (hα : ContDiff ℝ 1 α) : Continuous (dbar α) := by
  have hD := hα.continuous_fderiv one_ne_zero
  unfold dbar
  exact continuous_const.mul ((hD.clm_apply continuous_const).add
    (continuous_const.mul (hD.clm_apply continuous_const)))

lemma support_dbar_subset (α : ℂ → ℂ) : Function.support (dbar α) ⊆ tsupport α := by
  intro z hz
  by_contra h
  apply hz
  have : fderiv ℝ α z = 0 := Function.notMem_support.mp (fun h' => h (support_fderiv_subset ℝ h'))
  simp [dbar, this]

lemma tsupport_dbar_subset (α : ℂ → ℂ) : tsupport (dbar α) ⊆ tsupport α :=
  closure_minimal (support_dbar_subset α) (isClosed_tsupport α)

/-! ### The Cauchy transform as a convolution -/

/-- The Cauchy kernel `z ↦ z⁻¹` is locally integrable. -/
lemma locallyIntegrable_inv_complex : LocallyIntegrable (fun z : ℂ ↦ z⁻¹) := by
  simpa using locallyIntegrable_inv_sub 0

lemma cauchyTransform_eq_convolution (f : ℂ → ℂ) :
    cauchyTransform f = fun w ↦ (1 / Real.pi : ℂ) *
      ((fun z : ℂ ↦ z⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f) w := by
  ext w
  rw [cauchyTransform, convolution_def]
  congr 1
  rw [← integral_sub_left_eq_self (fun z ↦ f z / (w - z)) volume w]
  congr 1
  ext t
  simp [div_eq_mul_inv, mul_comm]

/-- For `f` continuous with compact support, `z ↦ f z / (w - z)` is integrable. -/
lemma integrable_div_sub {f : ℂ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (w : ℂ) :
    Integrable (fun z ↦ f z / (w - z)) := by
  have h := hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_inv_complex hf w
  have h2 := (ConvolutionExistsAt.integrable h).comp_sub_left w
  refine h2.congr (Filter.Eventually.of_forall fun z ↦ ?_)
  simp [div_eq_mul_inv, mul_comm]

/-! ### A Fubini identity for the Cauchy kernel -/

/-- `∫_K |w - z|⁻¹ dm(w) ≤ 2π + |K|`, uniformly in `z`. -/
lemma lintegral_inv_norm_sub_le_of_set (K : Set ℂ) (z : ℂ) :
    ∫⁻ w in K, ENNReal.ofReal ‖w - z‖⁻¹ ≤ ENNReal.ofReal (2 * Real.pi) + volume K := by
  rw [← lintegral_inter_add_sdiff _ K (measurableSet_ball (x := z) (ε := 1))]
  gcongr
  · calc ∫⁻ w in K ∩ ball z 1, ENNReal.ofReal ‖w - z‖⁻¹
        ≤ ∫⁻ w in ball z 1, ENNReal.ofReal ‖w - z‖⁻¹ := lintegral_mono_set inter_subset_right
      _ = ENNReal.ofReal (2 * Real.pi) := by
        rw [lintegral_inv_norm_sub_ball z zero_le_one, mul_one]
  · calc ∫⁻ w in K \ ball z 1, ENNReal.ofReal ‖w - z‖⁻¹
        ≤ ∫⁻ w in K \ ball z 1, 1 := by
          refine setLIntegral_mono measurable_const (fun w hw ↦ ?_)
          have : 1 ≤ ‖w - z‖ := by
            have := hw.2; rw [mem_ball, dist_eq_norm, not_lt] at this; exact this
          rw [ENNReal.ofReal_le_one]
          exact inv_le_one_of_one_le₀ this
      _ = volume (K \ ball z 1) := by rw [setLIntegral_const, one_mul]
      _ ≤ volume K := measure_mono sdiff_subset

/-- The function `(z, w) ↦ f(z) g(w) / (w - z)` is integrable on `ℂ × ℂ` when `f` is integrable and
`g` is continuous with compact support. -/
lemma integrable_cauchyKernel_prod {f g : ℂ → ℂ} (hf : Integrable f) (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Integrable (fun p : ℂ × ℂ ↦ f p.1 * g p.2 / (p.2 - p.1)) (volume.prod volume) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  set K := tsupport g
  have hK : volume K < ∞ := hgc.isCompact.measure_lt_top
  refine ⟨?_, ?_⟩
  · simp_rw [div_eq_mul_inv]
    refine (hf.aestronglyMeasurable.comp_fst.mul (hg.comp continuous_snd).aestronglyMeasurable).mul
      ?_
    exact (measurable_snd.sub measurable_fst).inv.aestronglyMeasurable
  · have hinner : ∀ z, ∫⁻ w, ‖f z * g w / (w - z)‖ₑ ≤
        ‖f z‖ₑ * (ENNReal.ofReal M * (ENNReal.ofReal (2 * Real.pi) + volume K)) := by
      intro z
      calc ∫⁻ w, ‖f z * g w / (w - z)‖ₑ
          ≤ ∫⁻ w, ‖f z‖ₑ * K.indicator (fun w ↦ ENNReal.ofReal M * ENNReal.ofReal ‖w - z‖⁻¹) w := by
            refine lintegral_mono fun w ↦ ?_
            rw [div_eq_mul_inv, enorm_mul, enorm_mul, mul_assoc]
            gcongr
            by_cases hw : w ∈ K
            · rw [indicator_of_mem hw, ← ofReal_norm, ← ofReal_norm,
                ← ENNReal.ofReal_mul (norm_nonneg _), norm_inv,
                ← ENNReal.ofReal_mul (le_trans (norm_nonneg _) (hM w))]
              exact ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (hM w) (inv_nonneg.2 (norm_nonneg _)))
            · rw [indicator_of_notMem hw, image_eq_zero_of_notMem_tsupport hw, enorm_zero,
                zero_mul]
        _ = ‖f z‖ₑ * (ENNReal.ofReal M * ∫⁻ w in K, ENNReal.ofReal ‖w - z‖⁻¹) := by
            rw [lintegral_const_mul' _ _ enorm_ne_top,
              lintegral_indicator (isClosed_tsupport g).measurableSet,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ _ := by gcongr; exact lintegral_inv_norm_sub_le_of_set K z
    calc ∫⁻ p, ‖f p.1 * g p.2 / (p.2 - p.1)‖ₑ ∂(volume.prod volume)
        ≤ ∫⁻ z, ∫⁻ w, ‖f z * g w / (w - z)‖ₑ := lintegral_prod_le _
      _ ≤ ∫⁻ z, ‖f z‖ₑ * (ENNReal.ofReal M * (ENNReal.ofReal (2 * Real.pi) + volume K)) :=
          lintegral_mono hinner
      _ = (∫⁻ z, ‖f z‖ₑ) * (ENNReal.ofReal M * (ENNReal.ofReal (2 * Real.pi) + volume K)) :=
          lintegral_mul_const' _ _ (by
            exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hK.ne⟩))
      _ < ∞ := ENNReal.mul_lt_top hf.2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hK⟩))

/-- Antisymmetry of the Cauchy transform: `∫ g C[f] = -∫ f C[g]`. -/
lemma integral_mul_cauchyTransform_comm {f g : ℂ → ℂ} (hf : Integrable f) (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    ∫ w, g w * cauchyTransform f w = -∫ z, f z * cauchyTransform g z := by
  have hint := integrable_cauchyKernel_prod hf hg hgc
  simp only [cauchyTransform]
  have eL : ∀ w, g w * ((1 / Real.pi : ℂ) * ∫ z, f z / (w - z)) =
      (1 / Real.pi : ℂ) * ∫ z, f z * g w / (w - z) := by
    intro w
    rw [mul_left_comm, ← integral_const_mul (g w)]
    congr 2
    ext z
    ring
  have eR : ∀ z, f z * ((1 / Real.pi : ℂ) * ∫ w, g w / (z - w)) =
      -((1 / Real.pi : ℂ) * ∫ w, f z * g w / (w - z)) := by
    intro z
    rw [mul_left_comm, ← integral_const_mul (f z), ← mul_neg, ← integral_neg]
    congr 2
    ext w
    rw [← neg_sub z w, div_neg]
    ring
  simp_rw [eL, eR, integral_neg, integral_const_mul, neg_neg]
  congr 1
  exact (integral_integral_swap (f := fun z w ↦ f z * g w / (w - z)) hint).symm

theorem pompeiu {α : ℂ → ℂ} (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) (w : ℂ) :
    cauchyTransform (dbar α) w = α w := by
  rw [cauchyTransform, integral_dbar_div_eq hα hc w]
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem continuous_cauchyTransform {f : ℂ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous (cauchyTransform f) := by
  rw [cauchyTransform_eq_convolution]
  exact continuous_const.mul (hc.continuous_convolution_right _ locallyIntegrable_inv_complex hf)

theorem norm_cauchyTransform_le {f : ℂ → ℂ} {M R : ℝ} {c w : ℂ} (hf : Continuous f)
    (hM : ∀ z, ‖f z‖ ≤ M) (hsupp : tsupport f ⊆ Metric.closedBall c R)
    (hw : w ∈ Metric.closedBall c R) :
    ‖cauchyTransform f w‖ ≤ 4 * M * R := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hR0 : 0 ≤ R := le_trans dist_nonneg (mem_closedBall.mp hw)
  have hlint : ∫⁻ z, ENNReal.ofReal ‖f z / (w - z)‖ ≤ ENNReal.ofReal (M * (4 * Real.pi * R)) := by
    calc ∫⁻ z, ENNReal.ofReal ‖f z / (w - z)‖
        ≤ ∫⁻ z, (closedBall c R).indicator
            (fun z ↦ ENNReal.ofReal M * ENNReal.ofReal ‖z - w‖⁻¹) z := by
          refine lintegral_mono fun z ↦ ?_
          by_cases hz : z ∈ closedBall c R
          · rw [indicator_of_mem hz, ← ENNReal.ofReal_mul hM0, norm_div, div_eq_mul_inv,
              norm_sub_rev w z]
            exact ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (hM z) (inv_nonneg.2 (norm_nonneg _)))
          · have : f z = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hsupp h))
            simp [this]
      _ = ENNReal.ofReal M * ∫⁻ z in closedBall c R, ENNReal.ofReal ‖z - w‖⁻¹ := by
          rw [lintegral_indicator measurableSet_closedBall,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (4 * Real.pi * R) := by
          gcongr; exact lintegral_inv_norm_sub_le hw
      _ = ENNReal.ofReal (M * (4 * Real.pi * R)) := (ENNReal.ofReal_mul hM0).symm
  have h1 : ‖∫ z, f z / (w - z)‖ ≤ M * (4 * Real.pi * R) :=
    (norm_integral_le_lintegral_norm _).trans
      (ENNReal.toReal_le_of_le_ofReal (by positivity) hlint)
  rw [cauchyTransform, norm_mul]
  have hpi : ‖(1 / Real.pi : ℂ)‖ = 1 / Real.pi := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hpi]
  calc 1 / Real.pi * ‖∫ z, f z / (w - z)‖ ≤ 1 / Real.pi * (M * (4 * Real.pi * R)) := by
        gcongr
    _ = 4 * M * R := by field_simp

theorem isWeakDbarSol_cauchyTransform {f : ℂ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) :
    IsWeakDbarSol Set.univ (cauchyTransform f) f := by
  refine ⟨(continuous_cauchyTransform hf hc).locallyIntegrable.locallyIntegrableOn _,
    hf.locallyIntegrable.locallyIntegrableOn _, fun α hα hαc _ ↦ ?_⟩
  have hα1 : ContDiff ℝ 1 α := hα.of_le (by exact_mod_cast le_top)
  have := integral_mul_cauchyTransform_comm (hf.integrable_of_hasCompactSupport hc)
    (continuous_dbar hα1) (hasCompactSupport_dbar hαc)
  simp_rw [mul_comm (cauchyTransform f _), this, pompeiu hα1 hαc]

theorem contDiff_cauchyTransform {β : ℂ → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hc : HasCompactSupport β) :
    ContDiff ℝ (⊤ : ℕ∞) (cauchyTransform β) := by
  rw [cauchyTransform_eq_convolution]
  exact contDiff_const.mul (hc.contDiff_convolution_right _ locallyIntegrable_inv_complex hβ)

/-- Directional derivatives of the Cauchy transform of a `C¹` function with compact support. -/
lemma fderiv_cauchyTransform_apply {β : ℂ → ℂ} (hβ : ContDiff ℝ 1 β) (hc : HasCompactSupport β)
    (w v : ℂ) :
    fderiv ℝ (cauchyTransform β) w v = cauchyTransform (fun z ↦ fderiv ℝ β z v) w := by
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_inv_complex hβ w
  have hd2 := hd.const_mul (1 / Real.pi : ℂ)
  rw [← cauchyTransform_eq_convolution] at hd2
  rw [hd2.fderiv, FunLike.coe_smul, Pi.smul_apply,
    convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_inv_complex
      (hc.fderiv ℝ)
      (hβ.continuous_fderiv one_ne_zero) w v, cauchyTransform_eq_convolution]
  rfl

theorem dbar_cauchyTransform {β : ℂ → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hc : HasCompactSupport β)
    (w : ℂ) : dbar (cauchyTransform β) w = β w := by
  have hβ1 : ContDiff ℝ 1 β := hβ.of_le (by exact_mod_cast le_top)
  have hD := hβ1.continuous_fderiv one_ne_zero
  have hDc := hc.fderiv ℝ
  have hcs : ∀ v : ℂ, HasCompactSupport (fun z ↦ fderiv ℝ β z v) := fun v ↦
    hDc.mono' (fun z hz ↦ subset_tsupport _ (fun h ↦ hz (by simp [h])))
  have i1 := integrable_div_sub (hD.clm_apply continuous_const) (hcs 1) w
  have iI := integrable_div_sub (hD.clm_apply continuous_const) (hcs I) w
  rw [← pompeiu hβ1 hc w]
  simp only [dbar, fderiv_cauchyTransform_apply hβ1 hc, cauchyTransform]
  have e : ∀ z, 1 / 2 * (fderiv ℝ β z 1 + I * fderiv ℝ β z I) / (w - z) =
      (1 / 2 : ℂ) * (fderiv ℝ β z 1 / (w - z)) + (1 / 2 * I) * (fderiv ℝ β z I / (w - z)) :=
    fun z ↦ by ring
  simp_rw [e]
  rw [integral_add (i1.const_mul _) (iI.const_mul _), integral_const_mul, integral_const_mul]
  ring

theorem differentiableOn_cauchyTransform {f : ℂ → ℂ} (hf : Integrable f)
    (hc : HasCompactSupport f) {U : Set ℂ} (hU : IsOpen U) (hdisj : Disjoint (tsupport f) U) :
    DifferentiableOn ℂ (cauchyTransform f) U := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  have hwS : w ∉ tsupport f := fun h ↦ Set.disjoint_left.mp hdisj h hw
  obtain ⟨ε, hε, hεS⟩ : ∃ ε > 0, ball w ε ⊆ (tsupport f)ᶜ :=
    Metric.isOpen_iff.mp (isClosed_tsupport f).isOpen_compl w hwS
  have hfar : ∀ z, f z ≠ 0 → ∀ x ∈ ball w (ε / 2), ε / 2 ≤ ‖x - z‖ := by
    intro z hz x hx
    have hzS : z ∈ tsupport f := subset_tsupport f hz
    have h1 : ε ≤ ‖w - z‖ := by
      by_contra h
      exact hεS (by rw [mem_ball, dist_eq_norm, norm_sub_rev]; linarith) hzS
    have h2 : ‖x - w‖ < ε / 2 := by rw [← dist_eq_norm]; exact hx
    have : ‖w - z‖ ≤ ‖w - x‖ + ‖x - z‖ := norm_sub_le_norm_sub_add_norm_sub w x z
    rw [norm_sub_rev w x] at this
    linarith
  have hε2 : 0 < ε / 2 := half_pos hε
  set F : ℂ → ℂ → ℂ := fun x z ↦ f z * (x - z)⁻¹
  set F' : ℂ → ℂ → ℂ := fun x z ↦ -(f z * ((x - z) ^ 2)⁻¹)
  have hmeas : ∀ x, AEStronglyMeasurable (F x) volume := fun x ↦
    hf.aestronglyMeasurable.mul (measurable_const.sub measurable_id).inv.aestronglyMeasurable
  have hbound : ∀ z, ∀ x ∈ ball w (ε / 2), ‖F' x z‖ ≤ ‖f z‖ * ((ε / 2) ^ 2)⁻¹ := by
    intro z x hx
    by_cases hz : f z = 0
    · simp [F', hz]
    · have := hfar z hz x hx
      simp only [F', norm_neg, norm_mul, norm_inv, norm_pow]
      gcongr
  have hFint : Integrable (F w) := by
    refine (hf.norm.mul_const (ε / 2)⁻¹).mono' (hmeas w) (Filter.Eventually.of_forall fun z ↦ ?_)
    by_cases hz : f z = 0
    · simp [F, hz]
    · have := hfar z hz w (mem_ball_self hε2)
      simp only [F, norm_mul, norm_inv]
      gcongr
  have hderiv : ∀ z, ∀ x ∈ ball w (ε / 2), HasDerivAt (fun x ↦ F x z) (F' x z) x := by
    intro z x hx
    by_cases hz : f z = 0
    · simp only [F, F', hz, zero_mul, neg_zero]
      exact hasDerivAt_const x 0
    · have hxz : x - z ≠ 0 := by
        intro h; have := hfar z hz x hx; rw [h, norm_zero] at this; linarith
      have := (((hasDerivAt_id x).sub_const z).inv hxz).const_mul (f z)
      convert this using 1
      · ext y; simp only [F, Pi.inv_apply, id]
      · simp only [F', id]; ring
  have hF'meas : AEStronglyMeasurable (F' w) volume :=
    (hf.aestronglyMeasurable.mul
      ((measurable_const.sub measurable_id).pow_const 2).inv.aestronglyMeasurable).neg
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds w hε2)
    (Filter.Eventually.of_forall hmeas) hFint hF'meas
    (Filter.Eventually.of_forall hbound) (hf.norm.mul_const _) (Filter.Eventually.of_forall hderiv)
  have hC : cauchyTransform f = fun x ↦ (1 / Real.pi : ℂ) * ∫ z, F x z := by
    ext x; simp [cauchyTransform, F, div_eq_mul_inv]
  rw [hC]
  exact (key.2.const_mul _).differentiableAt

end OC
