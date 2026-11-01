import OrtegaCerdaMultipliers.Foundations.Basic

/-!
# M01 (Foundations) — Integrals in polar coordinates

See `blueprint/M01_Foundations.md`.

**Provenance.** Copied from `BerndtssonOrtegaCerda/Calculus/Polar.lean`
(BOC module M02, blueprint `M02_Polar.md`) of the companion project
`../1995ReineAngewMath` at commit `22104d9` (same author, Apache-2.0).  Changes: namespace
`BOC` → `OC`, imports adjusted; the BOC definitions not in `OrtegaCerdaMultipliers/Defs.lean`
are in `Foundations/Basic.lean`.

## Main results

General polar-coordinate formulas (auxiliary, reusable by other modules):

* `OC.lintegral_eq_lintegral_circle`: for measurable `f : ℂ → ℝ≥0∞`,
  `∫⁻ f = ∫⁻ s in (0,∞), s * ∫⁻ θ in (0, 2π], f (c + s e^{iθ})`.
* `OC.lintegral_ball_eq_lintegral_circle`: the same on `ball c r`, with `s ∈ (0, r)`.
* `OC.integral_eq_integral_circleAverage`: for integrable `f : ℂ → E`,
  `∫ f = ∫ s in (0,∞), (2π s) • circleAverage f c s`.
* `OC.setIntegral_ball_eq_integral_circleAverage`,
  `OC.setIntegral_ball_eq_intervalIntegral_circleAverage`: for `f` integrable on `ball c r`,
  `∫_{ball c r} f = ∫₀ʳ (2π s) • circleAverage f c s ds`.
* `OC.lintegral_comp_norm_sub`, `OC.lintegral_ball_comp_norm_sub`: radial functions
  `∫ F(|z - a|) dm = 2π ∫ F(s) s ds`.
* `OC.map_normSq_sub_volume`: the push-forward of Lebesgue measure under `z ↦ |z - a|²` is
  `π · Leb|_(0,∞)`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate Topology

noncomputable section

namespace OC

/-! ### General polar-coordinate formulas -/

theorem lintegral_Ioc_periodic {h : ℝ → ℝ≥0∞} {T : ℝ} (hT : 0 < T)
    (hh : Function.Periodic h T) (t s : ℝ) :
    ∫⁻ x in Ioc t (t + T), h x = ∫⁻ x in Ioc s (s + T), h x := by
  have : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  exact IsAddFundamentalDomain.setLIntegral_eq (G := AddSubgroup.zmultiples T)
    (isAddFundamentalDomain_Ioc hT t) (isAddFundamentalDomain_Ioc hT s) h
    hh.map_vadd_zmultiples

theorem polarCoord_symm_add_eq_circleMap (c : ℂ) (p : ℝ × ℝ) :
    Complex.polarCoord.symm p + c = circleMap c p.1 p.2 := by
  simp [circleMap, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin, add_comm]

theorem continuous_circleMap_prod (c : ℂ) :
    Continuous fun p : ℝ × ℝ ↦ circleMap c p.1 p.2 := by
  unfold circleMap; fun_prop

/-- Polar coordinates, lintegral version: integrate over circles centred at `c`. -/
theorem lintegral_eq_lintegral_circle (c : ℂ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z = ∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal s * ∫⁻ θ in Ioc 0 (2 * Real.pi), f (circleMap c s θ) := by
  rw [← lintegral_add_right_eq_self (fun z ↦ f z) c]
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  simp_rw [polarCoord_symm_add_eq_circleMap]
  have hm : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 • f (circleMap c p.1 p.2) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).smul
      (hf.comp (continuous_circleMap_prod c).measurable)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hm.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs ↦ ?_)
  simp only [smul_eq_mul]
  have hm' : Measurable fun θ ↦ f (circleMap c s θ) :=
    hf.comp (continuous_circleMap c s).measurable
  rw [lintegral_const_mul _ hm']
  congr 1
  have := lintegral_Ioc_periodic (h := fun θ ↦ f (circleMap c s θ)) Real.two_pi_pos
    (fun θ ↦ by simp [periodic_circleMap c s θ]) (-Real.pi) 0
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at this
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, this]
theorem norm_circleMap_sub_center (c : ℂ) (s θ : ℝ) : ‖circleMap c s θ - c‖ = |s| := by
  simp

/-- Polar coordinates on a ball, lintegral version. -/
theorem lintegral_ball_eq_lintegral_circle (c : ℂ) (r : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in ball c r, f z = ∫⁻ s in Ioo (0 : ℝ) r,
      ENNReal.ofReal s * ∫⁻ θ in Ioc 0 (2 * Real.pi), f (circleMap c s θ) := by
  rw [← lintegral_indicator measurableSet_ball,
    lintegral_eq_lintegral_circle c (hf.indicator measurableSet_ball),
    show Ioo (0 : ℝ) r = Iio r ∩ Ioi 0 by ext; simp [and_comm],
    ← Measure.restrict_restrict measurableSet_Iio, ← lintegral_indicator measurableSet_Iio]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s (hs : 0 < s) ↦ ?_)
  by_cases hsr : s < r
  · rw [indicator_of_mem (show s ∈ Iio r from hsr)]
    congr 2
    funext θ
    rw [indicator_of_mem]
    rw [mem_ball, dist_eq_norm, norm_circleMap_sub_center, abs_of_pos hs]
    exact hsr
  · rw [indicator_of_notMem (show s ∉ Iio r from hsr)]
    have : ∀ θ, (ball c r).indicator f (circleMap c s θ) = 0 := fun θ ↦ by
      rw [indicator_of_notMem]
      rw [mem_ball, dist_eq_norm, norm_circleMap_sub_center, abs_of_pos hs]
      exact hsr
    simp [this]


section Bochner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem integrableOn_polarCoord_circleMap (c : ℂ) {f : ℂ → E} (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (circleMap c p.1 p.2)) polarCoord.target := by
  have h1 : Integrable (fun q : ℝ × ℝ ↦ f (measurableEquivRealProd.symm q + c)) := by
    have := (Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
      measurableEquivRealProd.symm.measurableEmbedding (g := fun z ↦ f (z + c))
    exact this.2 (hf.comp_add_right c)
  have h2 := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt) polarCoord.symm.injOn
    (fun q : ℝ × ℝ ↦ f (measurableEquivRealProd.symm q + c))).1 (by
      rw [polarCoord.symm_image_target_eq_source]; exact h1.integrableOn)
  refine h2.congr_fun (fun p hp ↦ ?_) polarCoord.open_target.measurableSet
  simp only [det_fderivPolarCoordSymm, measurableEquivRealProd_symm_polarCoord_symm_apply,
    polarCoord_symm_add_eq_circleMap]
  rw [abs_of_pos hp.1]

omit [CompleteSpace E] in
/-- Polar coordinates, Bochner version: for `f` integrable on `ℂ`,
`∫ f dm = ∫₀^∞ 2π s · circleAverage f c s ds`. -/
theorem integral_eq_integral_circleAverage (c : ℂ) {f : ℂ → E} (hf : Integrable f) :
    ∫ z, f z = ∫ s in Ioi (0 : ℝ), (2 * Real.pi * s) • Real.circleAverage f c s := by
  rw [← integral_add_right_eq_self (fun z ↦ f z) c]
  rw [← Complex.integral_comp_polarCoord_symm]
  have hint := integrableOn_polarCoord_circleMap c hf
  simp_rw [polarCoord_symm_add_eq_circleMap]
  rw [polarCoord_target] at hint ⊢
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s (hs : 0 < s) ↦ ?_)
  simp only
  rw [integral_smul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hper : Function.Periodic (fun θ ↦ f (circleMap c s θ)) (2 * Real.pi) :=
    fun θ ↦ by simp [periodic_circleMap c s θ]
  have := hper.intervalIntegral_add_eq (-Real.pi) 0
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at this
  rw [this, Real.circleAverage_def, smul_smul]
  congr 1
  field_simp [Real.pi_pos.ne']
/-- Polar coordinates on a ball, Bochner version. -/
theorem setIntegral_ball_eq_integral_circleAverage (c : ℂ) (r : ℝ) {f : ℂ → E}
    (hf : IntegrableOn f (ball c r)) :
    ∫ z in ball c r, f z =
      ∫ s in Ioo (0 : ℝ) r, (2 * Real.pi * s) • Real.circleAverage f c s := by
  rw [← integral_indicator measurableSet_ball,
    integral_eq_integral_circleAverage c (hf.integrable_indicator measurableSet_ball),
    show Ioo (0 : ℝ) r = Ioi 0 ∩ Iio r by ext; simp, ← setIntegral_indicator measurableSet_Iio]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s (hs : 0 < s) ↦ ?_)
  by_cases hsr : s < r
  · rw [indicator_of_mem (show s ∈ Iio r from hsr)]
    congr 1
    refine Real.circleAverage_congr_sphere (fun z hz ↦ ?_)
    rw [mem_sphere, abs_of_pos hs] at hz
    rw [indicator_of_mem (by rw [mem_ball, hz]; exact hsr)]
  · rw [indicator_of_notMem (show s ∉ Iio r from hsr)]
    rw [Real.circleAverage_const_on_circle (a := 0) (fun z hz ↦ ?_), smul_zero]
    rw [mem_sphere, abs_of_pos hs] at hz
    rw [indicator_of_notMem (by rw [mem_ball, hz]; exact hsr)]

/-- Polar coordinates on a ball, Bochner version with an interval integral:
`∫_{ball c r} f dm = ∫₀ʳ 2π s · circleAverage f c s ds`. -/
theorem setIntegral_ball_eq_intervalIntegral_circleAverage (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    {f : ℂ → E} (hf : IntegrableOn f (ball c r)) :
    ∫ z in ball c r, f z = ∫ s in (0 : ℝ)..r, (2 * Real.pi * s) • Real.circleAverage f c s := by
  rw [setIntegral_ball_eq_integral_circleAverage c r hf, intervalIntegral.integral_of_le hr,
    integral_Ioc_eq_integral_Ioo]

end Bochner

/-! ### Radial functions -/

/-- `∫₀ʳ s ds = r²/2`, as a lower integral. -/
theorem lintegral_Ioo_ofReal_id {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ s in Ioo (0 : ℝ) r, ENNReal.ofReal s = ENNReal.ofReal (r ^ 2 / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr, integral_id]
    ring_nf
  · exact (continuous_id.integrableOn_Icc (a := 0) (b := r)).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hs.1.le


theorem lintegral_comp_norm_sub (a : ℂ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z : ℂ, F ‖z - a‖ =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal s * F s := by
  rw [lintegral_eq_lintegral_circle a (f := fun z ↦ F ‖z - a‖) (hF.comp (by fun_prop)),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s (hs : 0 < s) ↦ ?_)
  simp only [norm_circleMap_sub_center, abs_of_pos hs, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc, sub_zero]
  ring

/-- Radial functions on a ball: `∫_{ball a R} F(|z - a|) dm = 2π ∫₀^R F(s) s ds`. -/
theorem lintegral_ball_comp_norm_sub (a : ℂ) (R : ℝ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in ball a R, F ‖z - a‖ =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ s in Ioo (0 : ℝ) R, ENNReal.ofReal s * F s := by
  rw [lintegral_ball_eq_lintegral_circle a R (f := fun z ↦ F ‖z - a‖) (hF.comp (by fun_prop)),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun s (hs : s ∈ Ioo 0 R) ↦ ?_)
  simp only [norm_circleMap_sub_center, abs_of_pos hs.1, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc, sub_zero]
  ring

theorem lintegral_comp_normSq_sub (a : ℂ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z : ℂ, F (‖z - a‖ ^ 2) = ENNReal.ofReal Real.pi * ∫⁻ t in Set.Ioi (0 : ℝ), F t := by
  rw [lintegral_comp_norm_sub a (F := fun s ↦ F (s ^ 2)) (hF.comp (measurable_id.pow_const 2))]
  have himg : (fun x : ℝ ↦ x ^ 2) '' Ioi 0 = Ioi 0 := by
    ext t
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩; positivity
    · intro ht; exact ⟨Real.sqrt t, Real.sqrt_pos.2 ht, Real.sq_sqrt ht.le⟩
  have hsub := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ))
    (f := fun x : ℝ ↦ x ^ 2) (f' := fun x ↦ 2 * x) measurableSet_Ioi
    (fun x _ ↦ by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt)
    (fun x hx y hy h ↦
      (sq_eq_sq₀ (show (0 : ℝ) ≤ x from le_of_lt hx)
        (show (0 : ℝ) ≤ y from le_of_lt hy)).1 h) F
  rw [himg] at hsub
  rw [hsub, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s (hs : 0 < s) ↦ ?_)
  rw [abs_of_pos (by positivity), ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul Real.pi_pos.le]
  ring_nf

/-- The push-forward of Lebesgue measure under `z ↦ |z - a|²` is `π` times Lebesgue measure on
`(0, ∞)`. -/
theorem map_normSq_sub_volume (a : ℂ) :
    Measure.map (fun z : ℂ ↦ ‖z - a‖ ^ 2) volume =
      ENNReal.ofReal Real.pi • volume.restrict (Ioi (0 : ℝ)) := by
  have hφ : Measurable (fun z : ℂ ↦ ‖z - a‖ ^ 2) := by fun_prop
  ext s hs
  rw [Measure.map_apply hφ hs, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
  have := lintegral_comp_normSq_sub a (measurable_one.indicator hs)
  rw [lintegral_indicator_one hs, Measure.restrict_apply' measurableSet_Ioi] at this
  rw [← this, ← lintegral_indicator_one (hφ hs)]
  rfl

theorem integral_comp_normSq_sub (a : ℂ) {F : ℝ → ℝ} (hF : IntegrableOn F (Set.Ioi 0)) :
    ∫ z : ℂ, F (‖z - a‖ ^ 2) = Real.pi * ∫ t in Set.Ioi (0 : ℝ), F t := by
  have hφ : AEMeasurable (fun z : ℂ ↦ ‖z - a‖ ^ 2) volume := by fun_prop
  have h1 : Integrable F (Measure.map (fun z : ℂ ↦ ‖z - a‖ ^ 2) volume) := by
    rw [map_normSq_sub_volume]; exact hF.smul_measure ENNReal.ofReal_ne_top
  rw [← integral_map hφ h1.aestronglyMeasurable, map_normSq_sub_volume, integral_smul_measure,
    ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul]

theorem integrable_comp_normSq_sub (a : ℂ) {F : ℝ → ℝ} (hF : IntegrableOn F (Set.Ioi 0)) :
    Integrable (fun z : ℂ ↦ F (‖z - a‖ ^ 2)) := by
  have hφ : AEMeasurable (fun z : ℂ ↦ ‖z - a‖ ^ 2) volume := by fun_prop
  have h1 : Integrable F (Measure.map (fun z : ℂ ↦ ‖z - a‖ ^ 2) volume) := by
    rw [map_normSq_sub_volume]; exact hF.smul_measure ENNReal.ofReal_ne_top
  exact (integrable_map_measure h1.aestronglyMeasurable hφ).mp h1

theorem volume_ball_complex (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball a r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow hr, ENNReal.ofReal_mul Real.pi_pos.le, mul_comm]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]

theorem lintegral_inv_norm_sub_ball (a : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∫⁻ z in Metric.ball a R, ENNReal.ofReal ‖z - a‖⁻¹ = ENNReal.ofReal (2 * Real.pi * R) := by
  rw [lintegral_ball_comp_norm_sub a R (F := fun s ↦ ENNReal.ofReal s⁻¹) (by fun_prop)]
  rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ ↦ 1) (fun s (hs : s ∈ Ioo 0 R) ↦ by
    rw [← ENNReal.ofReal_mul hs.1.le, mul_inv_cancel₀ hs.1.ne', ENNReal.ofReal_one])]
  rw [setLIntegral_one, Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul Real.two_pi_pos.le]
theorem integrableOn_inv_sub_ball (a : ℂ) (R : ℝ) :
    IntegrableOn (fun z : ℂ ↦ (z - a)⁻¹) (Metric.ball a R) := by
  refine IntegrableOn.mono_set ?_ (ball_subset_ball (le_abs_self R))
  refine ⟨(by fun_prop : Measurable fun z : ℂ ↦ (z - a)⁻¹).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [norm_inv]
  rw [lintegral_inv_norm_sub_ball a (abs_nonneg R)]
  exact ENNReal.ofReal_lt_top

theorem locallyIntegrable_inv_sub (a : ℂ) : LocallyIntegrable (fun z : ℂ ↦ (z - a)⁻¹) := by
  intro x
  exact ⟨ball a (dist x a + 1), isOpen_ball.mem_nhds (by simp [mem_ball]),
    integrableOn_inv_sub_ball a _⟩

theorem lintegral_inv_norm_sub_le {c w : ℂ} {R : ℝ} (hw : w ∈ Metric.closedBall c R) :
    ∫⁻ z in Metric.closedBall c R, ENNReal.ofReal ‖z - w‖⁻¹ ≤
      ENNReal.ofReal (4 * Real.pi * R) := by
  have hR : 0 ≤ R := nonempty_closedBall.1 ⟨w, hw⟩
  have hsub : closedBall c R ⊆ closedBall w (2 * R) := by
    intro z hz
    rw [mem_closedBall] at hz hw ⊢
    calc dist z w ≤ dist z c + dist w c := dist_triangle_right z w c
      _ ≤ 2 * R := by linarith
  calc ∫⁻ z in closedBall c R, ENNReal.ofReal ‖z - w‖⁻¹
      ≤ ∫⁻ z in closedBall w (2 * R), ENNReal.ofReal ‖z - w‖⁻¹ := lintegral_mono_set hsub
    _ = ∫⁻ z in ball w (2 * R), ENNReal.ofReal ‖z - w‖⁻¹ := by
        refine setLIntegral_congr ((ae_eq_set).2 ⟨?_, ?_⟩)
        · rw [closedBall_sdiff_ball]; exact Measure.addHaar_sphere volume w _
        · rw [sdiff_eq_empty.2 ball_subset_closedBall]; simp
    _ = ENNReal.ofReal (4 * Real.pi * R) := by
        rw [lintegral_inv_norm_sub_ball w (by positivity)]; ring_nf

theorem lintegral_inv_normSq_sub_ball_eq_top (a : ℂ) {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in Metric.ball a R, ENNReal.ofReal (‖z - a‖⁻¹ ^ 2) = ∞ := by
  rw [lintegral_ball_comp_norm_sub a R (F := fun s ↦ ENNReal.ofReal (s⁻¹ ^ 2)) (by fun_prop)]
  rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun s ↦ ENNReal.ofReal s⁻¹)
    (fun s (hs : s ∈ Ioo 0 R) ↦ by
      rw [← ENNReal.ofReal_mul hs.1.le]; congr 1; field_simp)]
  have : ∫⁻ s in Ioo (0 : ℝ) R, ENNReal.ofReal s⁻¹ = ∞ := by
    by_contra h
    have hint : IntegrableOn (fun s : ℝ ↦ s⁻¹) (Ioo 0 R) := by
      refine ⟨measurable_inv.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal]
      · exact lt_top_iff_ne_top.2 h
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact inv_nonneg.2 hs.1.le
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hR.le, intervalIntegrable_inv_iff] at hint
    rcases hint with h | h
    · exact hR.ne h
    · exact h (by simp [hR.le])
  rw [this, ENNReal.mul_top (by simp [Real.pi_pos])]

end OC
