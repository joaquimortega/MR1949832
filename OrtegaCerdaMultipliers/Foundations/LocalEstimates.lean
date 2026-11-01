import OrtegaCerdaMultipliers.Foundations.Basic
import OrtegaCerdaMultipliers.Foundations.Polar

/-!
# M01 (Foundations) — Local L² estimates for holomorphic functions

See `blueprint/M01_Foundations.md`.

**Provenance.** Copied from `BerndtssonOrtegaCerda/Complex/LocalEstimates.lean`
(BOC module M03, blueprint `M03_LocalEstimates.md`) of the companion project
`../1995ReineAngewMath` at commit `22104d9` (same author, Apache-2.0).  Changes: namespace
`BOC` → `OC`, imports adjusted; the BOC definitions not in `OrtegaCerdaMultipliers/Defs.lean`
are in `Foundations/Basic.lean`.

The circle mean-value property `DiffContOnCl.circleAverage` (applied to `g²`, resp. `G`) is
integrated over the radius with the polar-coordinate formulas of BOC M02 (`Foundations/Polar.lean`)
(`OC.lintegral_ball_eq_lintegral_circle`, `OC.setIntegral_ball_eq_intervalIntegral_circleAverage`).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate Topology

noncomputable section

namespace OC

/-- Sub-mean-value inequality for `|g|²` on a circle, in `lintegral` form. -/
theorem ofReal_two_pi_mul_norm_sq_le_lintegral_circle {g : ℂ → ℂ} {U : Set ℂ} {a : ℂ} {s : ℝ}
    (hg : DifferentiableOn ℂ g U) (hs : closedBall a |s| ⊆ U) :
    ENNReal.ofReal (2 * Real.pi * ‖g a‖ ^ 2) ≤
      ∫⁻ θ in Ioc 0 (2 * Real.pi), ENNReal.ofReal (‖g (circleMap a s θ)‖ ^ 2) := by
  have hmem : ∀ θ, circleMap a s θ ∈ U := fun θ ↦
    hs (sphere_subset_closedBall (circleMap_mem_sphere' a s θ))
  have hcont : Continuous fun θ ↦ ‖g (circleMap a s θ)‖ ^ 2 :=
    ((hg.continuousOn.comp_continuous (continuous_circleMap a s) hmem).norm).pow 2
  have hint : IntegrableOn (fun θ ↦ ‖g (circleMap a s θ)‖ ^ 2) (Ioc 0 (2 * Real.pi)) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun θ ↦ by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- mean value property for `g ^ 2`
  have hd : DiffContOnCl ℂ (fun z ↦ g z ^ 2) (ball a |s|) :=
    (hg.pow 2).diffContOnCl_ball hs
  have hmv := hd.circleAverage
  have hle := Real.norm_circleAverage_le_circleAverage_norm (f := fun z ↦ g z ^ 2) (c := a) (R := s)
  rw [hmv, Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    at hle
  simp only [norm_pow] at hle
  have h2pi : 0 < 2 * Real.pi := Real.two_pi_pos
  have := mul_le_mul_of_nonneg_left hle h2pi.le
  rwa [← mul_assoc, mul_inv_cancel₀ h2pi.ne', one_mul] at this

theorem norm_sq_le_lintegral_ball {g : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.ball a r)) :
    ENNReal.ofReal (Real.pi * r ^ 2 * ‖g a‖ ^ 2) ≤
      ∫⁻ z in Metric.ball a r, ENNReal.ofReal (‖g z‖ ^ 2) := by
  classical
  set f : ℂ → ℝ≥0∞ := (ball a r).indicator (fun z ↦ ENNReal.ofReal (‖g z‖ ^ 2)) with hf_def
  have hf : Measurable f := by
    refine ContinuousOn.measurable_piecewise ?_ continuous_const.continuousOn measurableSet_ball
    exact ENNReal.continuous_ofReal.comp_continuousOn (hg.continuousOn.norm.pow 2)
  have heq : ∫⁻ z in ball a r, ENNReal.ofReal (‖g z‖ ^ 2) = ∫⁻ z in ball a r, f z :=
    setLIntegral_congr_fun measurableSet_ball (fun z hz ↦ by rw [hf_def, indicator_of_mem hz])
  rw [heq, lintegral_ball_eq_lintegral_circle a r hf]
  calc ENNReal.ofReal (Real.pi * r ^ 2 * ‖g a‖ ^ 2)
      = ∫⁻ s in Ioo (0 : ℝ) r, ENNReal.ofReal s * ENNReal.ofReal (2 * Real.pi * ‖g a‖ ^ 2) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_Ioo_ofReal_id hr.le,
          ← ENNReal.ofReal_mul (by positivity)]
        ring_nf
    _ ≤ _ := by
        refine setLIntegral_mono' measurableSet_Ioo (fun s hs ↦ ?_)
        gcongr
        have hsub : closedBall a |s| ⊆ ball a r := by
          rw [abs_of_pos hs.1]; exact closedBall_subset_ball hs.2
        refine (ofReal_two_pi_mul_norm_sq_le_lintegral_circle hg hsub).trans_eq ?_
        refine setLIntegral_congr_fun measurableSet_Ioc (fun θ _ ↦ ?_)
        rw [hf_def, indicator_of_mem (hsub (sphere_subset_closedBall (circleMap_mem_sphere' a s θ)))]
theorem norm_deriv_sq_le {g : ℂ → ℂ} {a z : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (Metric.ball a R)) (hz : z ∈ Metric.ball a (R / 2)) :
    ENNReal.ofReal (‖deriv g z‖ ^ 2) ≤
      ENNReal.ofReal (256 / (Real.pi * R ^ 4)) *
        ∫⁻ w in Metric.ball a R, ENNReal.ofReal (‖g w‖ ^ 2) := by
  set I := ∫⁻ w in Metric.ball a R, ENNReal.ofReal (‖g w‖ ^ 2) with hI_def
  by_cases hI : I = ∞
  · rw [hI, ENNReal.mul_top (by simp; positivity)]; exact le_top
  rw [mem_ball] at hz
  have hball : ∀ w ∈ sphere z (R / 4), ball w (R / 4) ⊆ ball a R := by
    intro w hw u hu
    rw [mem_sphere] at hw; rw [mem_ball] at hu ⊢
    linarith [dist_triangle u w a, dist_triangle w z a]
  have hcl : closedBall z (R / 4) ⊆ ball a R := by
    intro u hu
    rw [mem_closedBall] at hu; rw [mem_ball]
    linarith [dist_triangle u z a]
  have hpt : ∀ w ∈ sphere z (R / 4),
      ‖g w‖ ≤ Real.sqrt (16 * I.toReal / (Real.pi * R ^ 2)) := by
    intro w hw
    have h1 := norm_sq_le_lintegral_ball (r := R / 4) (by positivity) (hg.mono (hball w hw))
    have h2 : ∫⁻ u in ball w (R / 4), ENNReal.ofReal (‖g u‖ ^ 2) ≤ I :=
      lintegral_mono_set (hball w hw)
    have h3 : Real.pi * (R / 4) ^ 2 * ‖g w‖ ^ 2 ≤ I.toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hI).1 (h1.trans h2)
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hd : DiffContOnCl ℂ g (ball z (R / 4)) := hg.diffContOnCl_ball hcl
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hd hpt
  have hsq : ‖deriv g z‖ ^ 2 ≤ 256 / (Real.pi * R ^ 4) * I.toReal := by
    calc ‖deriv g z‖ ^ 2 ≤ (Real.sqrt (16 * I.toReal / (Real.pi * R ^ 2)) / (R / 4)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hC 2
      _ = 16 * I.toReal / (Real.pi * R ^ 2) / (R / 4) ^ 2 := by
          rw [div_pow, Real.sq_sqrt (by positivity)]
      _ = 256 / (Real.pi * R ^ 4) * I.toReal := by
          field_simp
          ring
  calc ENNReal.ofReal (‖deriv g z‖ ^ 2)
      ≤ ENNReal.ofReal (256 / (Real.pi * R ^ 4) * I.toReal) := ENNReal.ofReal_le_ofReal hsq
    _ = ENNReal.ofReal (256 / (Real.pi * R ^ 4)) * I := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hI]

theorem integral_re_ball {G : ℂ → ℂ} {a : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hG : DifferentiableOn ℂ G (Metric.ball a R)) :
    ∫ z in Metric.ball a r, (G z).re = Real.pi * r ^ 2 * (G a).re := by
  have hcont : ContinuousOn G (closedBall a r) :=
    hG.continuousOn.mono (closedBall_subset_ball hrR)
  have hint : IntegrableOn (fun z ↦ (G z).re) (ball a r) :=
    ((continuous_re.comp_continuousOn hcont).integrableOn_compact
      (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  rw [setIntegral_ball_eq_intervalIntegral_circleAverage a hr.le hint]
  have hmv : ∀ s ∈ uIcc 0 r, Real.circleAverage (fun z ↦ (G z).re) a s = (G a).re := by
    intro s hs
    rw [uIcc_of_le hr.le] at hs
    have hsub : closedBall a |s| ⊆ ball a R := by
      rw [abs_of_nonneg hs.1]; exact closedBall_subset_ball (hs.2.trans_lt hrR)
    have hci : CircleIntegrable G a s :=
      ContinuousOn.circleIntegrable' (hG.continuousOn.mono
        (sphere_subset_closedBall.trans hsub))
    have := ContinuousLinearMap.circleAverage_comp_comm Complex.reCLM hci
    simp only [Complex.reCLM_apply] at this
    rw [show (fun z ↦ (G z).re) = (Complex.reCLM ∘ G) from rfl, this,
      (hG.diffContOnCl_ball hsub).circleAverage]
  rw [intervalIntegral.integral_congr (g := fun s ↦ (2 * Real.pi * s) • (G a).re)
    (fun s hs ↦ by simp only [hmv s hs]),
    intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul, integral_id,
    smul_eq_mul]
  ring

end OC
