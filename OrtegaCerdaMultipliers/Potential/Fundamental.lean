import OrtegaCerdaMultipliers.Foundations.Wirtinger
import OrtegaCerdaMultipliers.Foundations.Polar
import OrtegaCerdaMultipliers.Foundations.Hyperbolic
import OrtegaCerdaMultipliers.Potential.Radial

/-!
# M02 (Potentials) §1 — The logarithmic kernel

See `blueprint/M02_Potentials.md` §1.  Scaffold: statements, proofs `sorry`.

* `∫ log|z − ζ| Δχ(z) dm(z) = 2π χ(ζ)` (fundamental solution of the standard Laplacian);
* integration by parts against test functions for `C²` functions;
* the Green kernel `log ρ(ζ, z)` of `𝔻`;
* (requested by M13 §4.2) the uniform `L¹` bound for `log|z − a|` and the weak Laplacian of the
  logarithmic potential of a compactly supported finite measure.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

theorem integrableOn_log_norm_sub_closedBall (ζ : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun z : ℂ ↦ Real.log ‖z - ζ‖) (closedBall ζ R) := by
  set F : ℝ → ℝ := (Iic (R ^ 2)).indicator fun t ↦ Real.log t / 2 with hF
  have hFi : IntegrableOn F (Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ ↦ Real.log t / 2) (Ioc 0 (R ^ 2)) := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := R ^ 2)).div_const 2
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 this
    have h2 : IntegrableOn F (Ioc 0 (R ^ 2)) := by
      refine h1.congr_fun (fun t ht ↦ ?_) measurableSet_Ioc
      simp [hF, indicator_of_mem (show t ∈ Iic (R ^ 2) from ht.2)]
    have h3 : IntegrableOn F (Ioi (R ^ 2)) :=
      (integrableOn_zero).congr_fun (fun t ht ↦ by
        rw [hF, indicator_of_notMem (show t ∉ Iic (R ^ 2) from fun h ↦ (not_le.2 ht) (mem_Iic.1 h))])
        measurableSet_Ioi
    refine (integrableOn_union.2 ⟨h2, h3⟩).mono_set ?_
    intro t ht
    by_cases h : t ≤ R ^ 2
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr (not_le.1 h)
  have hint := integrable_comp_normSq_sub ζ hFi
  have heq : (fun z : ℂ ↦ F (‖z - ζ‖ ^ 2)) =
      (closedBall ζ R).indicator (fun z : ℂ ↦ Real.log ‖z - ζ‖) := by
    ext z
    by_cases hz : z ∈ closedBall ζ R
    · have hz' : ‖z - ζ‖ ^ 2 ≤ R ^ 2 := by
        rw [mem_closedBall, dist_eq_norm] at hz
        exact pow_le_pow_left₀ (norm_nonneg _) hz 2
      rw [indicator_of_mem hz, hF, indicator_of_mem (show ‖z - ζ‖ ^ 2 ∈ Iic (R ^ 2) from hz'),
        Real.log_pow]
      push_cast; ring
    · have hz' : ¬ ‖z - ζ‖ ^ 2 ≤ R ^ 2 := by
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        intro h
        exact absurd (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero |>.1 h) (not_le.2 hz)
      rw [indicator_of_notMem hz, hF, indicator_of_notMem (show ‖z - ζ‖ ^ 2 ∉ Iic (R ^ 2) from hz')]
  rw [heq, integrable_indicator_iff measurableSet_closedBall] at hint
  exact hint

theorem locallyIntegrable_log_norm_sub (ζ : ℂ) :
    LocallyIntegrable (fun z : ℂ ↦ Real.log ‖z - ζ‖) := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall ζ
  exact (integrableOn_log_norm_sub_closedBall ζ (le_max_right R 0)).mono_set
    (hR.trans (closedBall_subset_closedBall (le_max_left R 0)))

/-! ### Smooth bumps and the approximate identity -/

section bump

variable {s : ℝ}

theorem bump_pos (hs : 0 < s) : 0 < s ^ 2 / 4 := by positivity

theorem bump_lt (hs : 0 < s) : s ^ 2 / 4 < s ^ 2 := by nlinarith [pow_pos hs 2]

theorem kernel_bump_eq_zero (hs : 0 < s) {x : ℂ} (hx : s ≤ ‖x‖) :
    kernel (s ^ 2 / 4) (s ^ 2) x = 0 :=
  kernel_eq_zero (bump_pos hs) (bump_lt hs) (pow_le_pow_left₀ hs.le hx 2)

theorem integral_kernel_bump_sub (hs : 0 < s) (ζ : ℂ) :
    ∫ z, kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) = 1 := by
  rw [integral_sub_right_eq_self (fun z ↦ kernel (s ^ 2 / 4) (s ^ 2) z) ζ,
    integral_kernel (bump_pos hs) (bump_lt hs)]

theorem continuous_kernel_bump (hs : 0 < s) : Continuous (kernel (s ^ 2 / 4) (s ^ 2)) :=
  (contDiff_kernel (bump_pos hs) (bump_lt hs)).continuous

/-- `k_s(· − ζ) f` is integrable as soon as `f` is integrable on a closed ball of radius `≥ s`. -/
theorem integrable_kernel_bump_mul {f : ℂ → ℝ} {ζ : ℂ} {r : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    (hf : IntegrableOn f (closedBall ζ r)) :
    Integrable (fun z ↦ kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * f z) := by
  have heq : (fun z ↦ kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * f z) =
      fun z ↦ kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * (closedBall ζ r).indicator f z := by
    ext z
    by_cases hz : z ∈ closedBall ζ r
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, kernel_bump_eq_zero hs, zero_mul, zero_mul]
      rw [mem_closedBall, dist_eq_norm, not_le] at hz
      linarith
  rw [heq]
  refine Integrable.bdd_mul (c := (Real.pi * (s ^ 2 / 4))⁻¹)
    ((integrable_indicator_iff measurableSet_closedBall).2 hf)
    ((continuous_kernel_bump hs).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun z ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg (bump_pos hs) (bump_lt hs) _)]
  exact kernel_le (bump_pos hs) (bump_lt hs) _

/-- **Approximate identity.** `∫ k_s(z − ζ) f(z) dz → f(ζ)` as `s → 0⁺`, at a continuity
point `ζ` of a function integrable near `ζ`. -/
theorem tendsto_integral_kernel_bump_mul {f : ℂ → ℝ} {ζ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : IntegrableOn f (closedBall ζ r)) (hfc : ContinuousAt f ζ) :
    Tendsto (fun s ↦ ∫ z, kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * f z) (𝓝[>] 0) (𝓝 (f ζ)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hfc (ε / 2) (half_pos hε)
  refine ⟨min δ r, lt_min hδ hr, fun s hs hsd ↦ ?_⟩
  have hs0 : 0 < s := hs
  rw [Real.dist_eq, sub_zero, abs_of_pos hs0] at hsd
  have hsr : s ≤ r := (hsd.trans_le (min_le_right _ _)).le
  have hsδ : s < δ := hsd.trans_le (min_le_left _ _)
  have hk0 := kernel_nonneg (bump_pos hs0) (bump_lt hs0)
  have hint := integrable_kernel_bump_mul hs0 hsr hf
  have hkint : Integrable (fun z ↦ kernel (s ^ 2 / 4) (s ^ 2) (z - ζ)) :=
    ((contDiff_kernel (bump_pos hs0) (bump_lt hs0)).continuous.integrable_of_hasCompactSupport
      (by
        refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) s) fun x hx ↦ ?_
        rw [mem_closedBall, dist_zero_right, not_le] at hx
        exact kernel_bump_eq_zero hs0 hx.le)).comp_sub_right ζ
  have key : (∫ z, kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * f z) - f ζ =
      ∫ z, kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * (f z - f ζ) := by
    simp_rw [mul_sub]
    rw [integral_sub hint (hkint.mul_const _), integral_mul_const,
      integral_kernel_bump_sub hs0, one_mul]
  rw [dist_eq_norm, key]
  calc ‖∫ z, kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * (f z - f ζ)‖
      ≤ ∫ z, kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * (ε / 2) := by
        refine norm_integral_le_of_norm_le (hkint.mul_const _) (Eventually.of_forall fun z ↦ ?_)
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hk0 _)]
        by_cases hz : ‖z - ζ‖ < s
        · gcongr
          · exact hk0 _
          · exact (hδf (by rw [dist_eq_norm]; linarith)).le
        · rw [kernel_bump_eq_zero hs0 (not_lt.1 hz), zero_mul, zero_mul]
    _ = ε / 2 := by rw [integral_mul_const, integral_kernel_bump_sub hs0, one_mul]
    _ < ε := half_lt_self hε

end bump

/-! ### The Laplacian of a test function -/

theorem laplacian_eq_zero_of_notMem_tsupport {χ : ℂ → ℝ} {z : ℂ} (hz : z ∉ tsupport χ) :
    Laplacian.laplacian χ z = 0 := by
  have h0 : χ =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := (notMem_tsupport_iff_eventuallyEq).1 hz
  rw [(InnerProductSpace.laplacian_congr_nhds h0).eq_of_nhds]
  simp

theorem hasCompactSupport_laplacian {χ : ℂ → ℝ} (hc : HasCompactSupport χ) :
    HasCompactSupport (Laplacian.laplacian χ) := by
  refine hc.mono' fun z hz ↦ ?_
  by_contra h
  exact hz (laplacian_eq_zero_of_notMem_tsupport h)

theorem tsupport_laplacian_subset (χ : ℂ → ℝ) :
    tsupport (Laplacian.laplacian χ) ⊆ tsupport χ := by
  refine closure_minimal (fun z hz ↦ ?_) (isClosed_tsupport χ)
  by_contra h
  exact hz (laplacian_eq_zero_of_notMem_tsupport h)

theorem continuous_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) :
    Continuous (Laplacian.laplacian χ) := by
  have h := continuousOn_lap isOpen_univ hχ.contDiffOn
  rw [← continuousOn_univ]
  have : Laplacian.laplacian χ = fun z ↦ 4 * lap χ z := funext (laplacian_eq_four_mul_lap χ)
  rw [this]
  exact continuousOn_const.mul h

theorem locallyIntegrable_log_normSq_sub (ζ : ℂ) :
    LocallyIntegrable (fun z : ℂ ↦ Real.log (‖z - ζ‖ ^ 2)) := by
  have h := (locallyIntegrable_log_norm_sub ζ).smul (2 : ℝ)
  convert h using 1
  ext z
  simp [Real.log_pow]

theorem locallyIntegrable_norm_of {f : ℂ → ℝ} (hf : LocallyIntegrable f) :
    LocallyIntegrable (fun z ↦ ‖f z‖) :=
  hf.mono hf.aestronglyMeasurable.norm (Eventually.of_forall fun z ↦ by simp)

/-- `∫ S_s(‖z − ζ‖²) Δχ = −4π ∫ k_s(z − ζ) χ`. -/
theorem integral_sFun_mul_laplacian {s : ℝ} (hs : 0 < s) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (ζ : ℂ) :
    ∫ z, sFun (s ^ 2 / 4) (s ^ 2) (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z =
      -(4 * Real.pi) * ∫ z, kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * χ z := by
  have hU : ContDiff ℝ 2 (fun z : ℂ ↦ sFun (s ^ 2 / 4) (s ^ 2) (‖z - ζ‖ ^ 2)) :=
    ((contDiff_sFun (bump_pos hs) (bump_lt hs)).of_le (WithTop.coe_le_coe.2 le_top)).comp
      ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  have h := integral_mul_lap hχ hc hU
  have hlapU : ∀ z, lap (fun z : ℂ ↦ sFun (s ^ 2 / 4) (s ^ 2) (‖z - ζ‖ ^ 2)) z =
      -Real.pi * kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) := fun z ↦ by
    have := lap_comp_sub (fun w : ℂ ↦ sFun (s ^ 2 / 4) (s ^ 2) (‖w‖ ^ 2)) ζ z
    rw [this, lap_sFun_normSq (bump_pos hs) (bump_lt hs)]
  simp_rw [laplacian_eq_four_mul_lap]
  calc ∫ z, sFun (s ^ 2 / 4) (s ^ 2) (‖z - ζ‖ ^ 2) * (4 * lap χ z)
      = 4 * ∫ z, lap χ z * sFun (s ^ 2 / 4) (s ^ 2) (‖z - ζ‖ ^ 2) := by
        rw [← integral_const_mul]; congr 1; ext z; ring
    _ = 4 * ∫ z, χ z * (-Real.pi * kernel (s ^ 2 / 4) (s ^ 2) (z - ζ)) := by
        rw [← h]; simp_rw [hlapU]
    _ = _ := by
        rw [← integral_const_mul, ← integral_const_mul]; congr 1; ext z; ring

/-- `|W_s(x)| ≤ |log ‖x‖²| + C` for `0 < s ≤ 1`, `x ≠ 0` (`W_s = wFun (s²/4) s²`). -/
theorem exists_abs_wFun_bump_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ x : ℂ, x ≠ 0 →
    |wFun (s ^ 2 / 4) (s ^ 2) x| ≤ |Real.log (‖x‖ ^ 2)| + C := by
  obtain ⟨C, hC⟩ := exists_abs_sFun_le (a := 1 / 4) (b := 1) (by norm_num) (by norm_num) 1
  refine ⟨max C 0, le_max_right _ _, fun s hs hs1 x hx ↦ ?_⟩
  have hW0 := wFun_nonpos (bump_pos hs) (bump_lt hs) hx
  rw [abs_of_nonpos hW0]
  rcases le_or_gt s ‖x‖ with hsx | hsx
  · rw [wFun_eq_zero (bump_pos hs) (bump_lt hs) (pow_le_pow_left₀ hs.le hsx 2), neg_zero]
    positivity
  · have hscale := sFun_scale (a := 1 / 4) (b := 1) (by norm_num) (by norm_num) hs (‖x‖ ^ 2)
    rw [show s ^ 2 * (1 / 4) = s ^ 2 / 4 by ring, mul_one] at hscale
    have hW : wFun (s ^ 2 / 4) (s ^ 2) x =
        Real.log (‖x‖ ^ 2) + sFun (s ^ 2 / 4) (s ^ 2) (‖x‖ ^ 2) := rfl
    have ht : ‖x‖ ^ 2 / s ^ 2 ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, by rw [div_le_one (by positivity)]; nlinarith [norm_nonneg x]⟩
    have h1 := (abs_le.1 (hC _ ht)).1
    have hlog : Real.log (s ^ 2) ≤ 0 := Real.log_nonpos (by positivity) (by nlinarith)
    rw [hW, hscale]
    have := neg_abs_le (Real.log (‖x‖ ^ 2))
    have := le_max_left C 0
    linarith

theorem measurable_wFun_bump {s : ℝ} (hs : 0 < s) : Measurable (wFun (s ^ 2 / 4) (s ^ 2)) := by
  have h : wFun (s ^ 2 / 4) (s ^ 2) =
      fun x : ℂ ↦ Real.log (‖x‖ ^ 2) + sFun (s ^ 2 / 4) (s ^ 2) (‖x‖ ^ 2) := rfl
  rw [h]
  exact (Real.measurable_log.comp (by fun_prop)).add
    ((contDiff_sFun (bump_pos hs) (bump_lt hs)).continuous.measurable.comp (by fun_prop))

/-- `∫ log ‖z − ζ‖² Δχ(z) dm(z) = 4π χ(ζ)`. -/
theorem integral_log_normSq_sub_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (ζ : ℂ) :
    ∫ z, Real.log (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z = 4 * Real.pi * χ ζ := by
  set L := ∫ z, Real.log (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z with hL
  have hΔc := continuous_laplacian hχ
  have hΔs := hasCompactSupport_laplacian hc
  have hlogloc := locallyIntegrable_log_normSq_sub ζ
  have hlogint : Integrable (fun z ↦ Real.log (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z) := by
    simpa [smul_eq_mul] using hlogloc.integrable_smul_right_of_hasCompactSupport hΔc hΔs
  have hSint : ∀ s : ℝ, 0 < s →
      Integrable (fun z ↦ sFun (s ^ 2 / 4) (s ^ 2) (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z) :=
    fun s hs ↦ (((contDiff_sFun (bump_pos hs) (bump_lt hs)).continuous.comp
      ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2)).mul
        hΔc).integrable_of_hasCompactSupport hΔs.mul_left
  -- the identity for each `s > 0`
  have hid : ∀ s : ℝ, 0 < s → L = (∫ z, wFun (s ^ 2 / 4) (s ^ 2) (z - ζ) *
      Laplacian.laplacian χ z) + 4 * Real.pi * ∫ z, kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * χ z := by
    intro s hs
    have hW : (fun z ↦ wFun (s ^ 2 / 4) (s ^ 2) (z - ζ) * Laplacian.laplacian χ z) =
        fun z ↦ Real.log (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z +
          sFun (s ^ 2 / 4) (s ^ 2) (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z := by
      ext z
      rw [show wFun (s ^ 2 / 4) (s ^ 2) (z - ζ) =
        Real.log (‖z - ζ‖ ^ 2) + sFun (s ^ 2 / 4) (s ^ 2) (‖z - ζ‖ ^ 2) from rfl]
      ring
    rw [hW, integral_add hlogint (hSint s hs), integral_sFun_mul_laplacian hs hχ hc ζ, ← hL]
    ring
  -- limits
  obtain ⟨C, hC0, hC⟩ := exists_abs_wFun_bump_le
  have hbound : Integrable (fun z ↦ (‖Real.log (‖z - ζ‖ ^ 2)‖ + C) * ‖Laplacian.laplacian χ z‖) := by
    have h1 : LocallyIntegrable (fun z : ℂ ↦ ‖Real.log (‖z - ζ‖ ^ 2)‖ + C) :=
      (locallyIntegrable_norm_of hlogloc).add (locallyIntegrable_const C)
    simpa [smul_eq_mul] using
      h1.integrable_smul_right_of_hasCompactSupport hΔc.norm hΔs.norm
  have hlimW : Tendsto (fun s ↦ ∫ z, wFun (s ^ 2 / 4) (s ^ 2) (z - ζ) * Laplacian.laplacian χ z)
      (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
      (F := fun s z ↦ wFun (s ^ 2 / 4) (s ^ 2) (z - ζ) * Laplacian.laplacian χ z)
      (f := fun _ ↦ 0) _ ?_ ?_ hbound ?_
    · simpa using this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (((measurable_wFun_bump hs).comp (measurable_id.sub_const ζ)).mul
        hΔc.measurable).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
      filter_upwards [Measure.ae_ne volume ζ] with z hz
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (Real.log _)]
      exact mul_le_mul_of_nonneg_right (hC s hs.1 hs.2.le (z - ζ) (sub_ne_zero.2 hz))
        (norm_nonneg _)
    · filter_upwards [Measure.ae_ne volume ζ] with z hz
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (norm_pos_iff.2 (sub_ne_zero.2 hz))] with s hs
      rw [wFun_eq_zero (bump_pos hs.1) (bump_lt hs.1) (pow_le_pow_left₀ hs.1.le hs.2.le 2),
        zero_mul]
  have hlimK : Tendsto (fun s ↦ ∫ z, kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * χ z)
      (𝓝[>] 0) (𝓝 (χ ζ)) :=
    tendsto_integral_kernel_bump_mul one_pos
      (hχ.continuous.continuousOn.integrableOn_compact (isCompact_closedBall ζ 1)) hχ.continuous.continuousAt
  have hlim := hlimW.add (hlimK.const_mul (4 * Real.pi))
  rw [zero_add] at hlim
  have hev : (fun s ↦ (∫ z, wFun (s ^ 2 / 4) (s ^ 2) (z - ζ) * Laplacian.laplacian χ z) +
      4 * Real.pi * ∫ z, kernel (s ^ 2 / 4) (s ^ 2) (z - ζ) * χ z) =ᶠ[𝓝[>] 0] fun _ ↦ L := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hid s hs).symm
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hlim

/-- **Fundamental solution.** `∫ log|z − ζ| Δχ(z) dm(z) = 2π χ(ζ)`. -/
theorem integral_log_norm_sub_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (ζ : ℂ) :
    ∫ z, Real.log ‖z - ζ‖ * Laplacian.laplacian χ z = 2 * Real.pi * χ ζ := by
  have h := integral_log_normSq_sub_mul_laplacian hχ hc ζ
  have e : ∀ z, Real.log ‖z - ζ‖ * Laplacian.laplacian χ z =
      (1 / 2) * (Real.log (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z) := fun z ↦ by
    rw [Real.log_pow]; push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, h]
  ring

theorem tsupport_dbar_subset (f : ℂ → ℂ) : tsupport (dbar f) ⊆ tsupport f := by
  have h : dbar f = (fun L : ℂ →L[ℝ] ℂ ↦ (1 / 2 : ℂ) * (L 1 + I * L I)) ∘ fderiv ℝ f := rfl
  rw [h]
  exact (tsupport_comp_subset (by simp) _).trans (tsupport_fderiv_subset ℝ)

theorem contDiffOn_dz_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ 2 u Ω) : ContDiffOn ℝ 1 (dz u) Ω := by
  have hf : ContDiffOn ℝ 1 (fun z ↦ fderiv ℝ u z) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
  have h1 : ContDiffOn ℝ 1 (fun z ↦ fderiv ℝ u z 1) Ω := hf.clm_apply contDiffOn_const
  have hI : ContDiffOn ℝ 1 (fun z ↦ fderiv ℝ u z I) Ω := hf.clm_apply contDiffOn_const
  exact contDiffOn_const.mul (h1.sub (contDiffOn_const.mul hI))

/-- Local version of `integral_mul_lap`: `U` is only `C²` on an open set containing the support
of the test function. -/
theorem integral_mul_lap_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {g U : ℂ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hs : tsupport g ⊆ Ω)
    (hU : ContDiffOn ℝ 2 U Ω) : ∫ z, g z * lap U z = ∫ z, lap g z * U z := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  push_cast
  have hUC : ContDiffOn ℝ 2 (cplx U) Ω := ofRealCLM.contDiff.comp_contDiffOn hU
  have hgC : ContDiff ℝ 2 (cplx g) := contDiff_cplx hg
  have hgcC : HasCompactSupport (cplx g) := hasCompactSupport_cplx hgc
  have hsC : tsupport (cplx g) ⊆ Ω := (tsupport_comp_subset (by simp) g).trans hs
  have hU2 : ∀ z ∈ Ω, (lap U z : ℂ) = dbar (dz (cplx U)) z := fun z hz ↦
    (dbar_dz_cplx (hU.contDiffAt (hΩ.mem_nhds hz))).symm
  have hg2 : ∀ z, (lap g z : ℂ) = dz (dbar (cplx g)) z := fun z ↦
    (dz_dbar_cplx hg.contDiffAt).symm
  have h1 := integral_mul_dbar hΩ (u := dz (cplx U)) (α := cplx g)
    (contDiffOn_dz_of_contDiffOn hΩ hUC) (hgC.of_le (by norm_num)) hgcC hsC
  have h2 := integral_mul_dz' hΩ (u := cplx U) (α := dbar (cplx g))
    (hUC.of_le (by norm_num)) (contDiff_dbar hgC) (hasCompactSupport_dbar hgcC)
    ((tsupport_dbar_subset _).trans hsC)
  calc ∫ z, (g z : ℂ) * (lap U z : ℂ) = ∫ z, dbar (dz (cplx U)) z * cplx g z := by
        congr 1; ext z
        by_cases hz : z ∈ Ω
        · rw [hU2 z hz]; simp only [cplx]; ring
        · have : g z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hz (hs h)
          simp [cplx, this]
    _ = -∫ z, dz (cplx U) z * dbar (cplx g) z := by rw [h1, neg_neg]
    _ = ∫ z, cplx U z * dz (dbar (cplx g)) z := h2.symm
    _ = ∫ z, (lap g z : ℂ) * (U z : ℂ) := by
        congr 1; ext z; rw [hg2]; simp only [cplx]; ring

/-- Integration by parts against a test function, for `U ∈ C²(Ω)`. -/
theorem integral_mul_laplacian_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {U χ : ℂ → ℝ}
    (hU : ContDiffOn ℝ 2 U Ω) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ω) :
    ∫ z, U z * Laplacian.laplacian χ z = ∫ z, Laplacian.laplacian U z * χ z := by
  have h := integral_mul_lap_of_contDiffOn hΩ hχ hc hs hU
  simp_rw [laplacian_eq_four_mul_lap]
  calc ∫ z, U z * (4 * lap χ z) = 4 * ∫ z, lap χ z * U z := by
        rw [← integral_const_mul]; congr 1; ext z; ring
    _ = 4 * ∫ z, χ z * lap U z := by rw [h]
    _ = ∫ z, 4 * lap U z * χ z := by
        rw [← integral_const_mul]; congr 1; ext z; ring

/-- **Green kernel of the disc.** `∫ log ρ(ζ, z) Δχ(z) dm(z) = 2π χ(ζ)` for `χ` supported in `𝔻`. -/
theorem integral_log_pseudoHyp_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ 𝔻) {ζ : ℂ} (hζ : ζ ∈ 𝔻) :
    ∫ z, Real.log (pseudoHyp ζ z) * Laplacian.laplacian χ z = 2 * Real.pi * χ ζ := sorry

/-! ### Requested by M13 (§4.2) -/

/-- Uniform local integrability of `log|z − a|` for `a` in a compact set. -/
theorem integrableOn_log_norm_sub_uniform {K K' : Set ℂ} (hK : IsCompact K)
    (hK' : IsCompact K') :
    ∃ M : ℝ, ∀ a ∈ K', IntegrableOn (fun z ↦ Real.log ‖z - a‖) K ∧
      ∫ z in K, |Real.log ‖z - a‖| ≤ M := sorry

/-- `Δ (∫ log|z − ζ| dν(ζ)) = 2π ν` weakly, for a finite measure with compact support. -/
theorem integral_logPotential_mul_laplacian (ν : Measure ℂ) [IsFiniteMeasure ν] {L : Set ℂ}
    (hL : IsCompact L) (hνL : ν Lᶜ = 0) (χ : ℂ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) :
    ∫ z, (∫ ζ, Real.log ‖z - ζ‖ ∂ν) * Laplacian.laplacian χ z = 2 * Real.pi * ∫ ζ, χ ζ ∂ν :=
  sorry

end OC
