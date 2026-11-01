import OrtegaCerdaMultipliers.Line.Potential
import OrtegaCerdaMultipliers.LogModulusWeak
import OrtegaCerdaMultipliers.Potential.Fundamental

/-!
# M13 (Theorem5) — Theorem 5: multipliers for Laplacians carried by the real line

See `blueprint/M13_Theorem5.md` §3.7–§3.8.  `theorem5` (verbatim from
`comparator/statements.lean`) is proved from `lineMultipliers` (case `α = 0`).

* 13.7: Fubini on `ℝ × ℝ` and the fundamental theorem of calculus along horizontal and vertical
  lines (`integral_line_second_deriv`, `integral_abs_mul_line_second_deriv`).
* 13.8: uniform approximation by the truncated potentials `∫ log max(|z − t|, δ)`, with the
  error controlled by (L8) and the uniform continuity of the distribution function.
* 13.9: the series is a finite sum plus a tail dominated, uniformly on balls, by the far-field
  majorant at `0` (`LineConsts.uniform_tail`, `LineConsts.decomp`); the weak Laplacian is
  computed cell by cell (`IsLineMeasure.integral_lineTerm_mul_laplacian`, from M02) and summed
  with `integral_tsum_of_summable_integral_norm`.
* 13.10: M07 applied with the offsets `0` and `s₀`.

Upstream (reconciled): `logKernel`, `weylLaplacian` and the unconditional M07 entry point
(`LogModulusWeak.lean`); `integrableOn_log_norm_sub_uniform`,
`integral_logPotential_mul_laplacian` (M02, `Potential/Fundamental.lean`); `IsLineMeasure` and
L1–L8 (M03, `Doubling/LineMeasure.lean`).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ### Calculus along lines (for 13.7) -/

theorem hasDerivAt_line (z v : ℂ) (s : ℝ) : HasDerivAt (fun s : ℝ ↦ z + s • v) v s := by
  simpa using ((hasDerivAt_id s).smul_const v).const_add z

theorem hasDerivAt_comp_line {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (z v : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (z + s • v)) (fderiv ℝ f (z + s • v) v) s :=
  (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_line z v s)

theorem hasDerivAt_comp_line₂ {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (z v : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ ↦ fderiv ℝ f (z + s • v) v)
      (iteratedFDeriv ℝ 2 f (z + s • v) ![v, v]) s := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 := (hd (z + s • v)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_line z v s)
  have h3 := h2.clm_apply (hasDerivAt_const s v)
  rw [iteratedFDeriv_two_apply]
  simpa using h3

theorem isometry_line (z : ℂ) {v : ℂ} (hv : ‖v‖ = 1) : Isometry fun s : ℝ ↦ z + s • v := by
  refine Isometry.of_dist_eq fun s t ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hv, mul_one]

theorem hasCompactSupport_comp_line {G : ℂ → ℝ} (hG : HasCompactSupport G) (z : ℂ) {v : ℂ}
    (hv : ‖v‖ = 1) : HasCompactSupport fun s : ℝ ↦ G (z + s • v) :=
  hG.comp_isClosedEmbedding (isometry_line z hv).isClosedEmbedding

/-- The three functions of a test function along a line. -/
theorem line_facts {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (z : ℂ)
    {v : ℂ} (hv : ‖v‖ = 1) :
    (Continuous fun s : ℝ ↦ f (z + s • v)) ∧ HasCompactSupport (fun s : ℝ ↦ f (z + s • v)) ∧
    (Continuous fun s : ℝ ↦ fderiv ℝ f (z + s • v) v) ∧
      HasCompactSupport (fun s : ℝ ↦ fderiv ℝ f (z + s • v) v) ∧
    (Continuous fun s : ℝ ↦ iteratedFDeriv ℝ 2 f (z + s • v) ![v, v]) ∧
      HasCompactSupport (fun s : ℝ ↦ iteratedFDeriv ℝ 2 f (z + s • v) ![v, v]) := by
  have hL : Continuous fun s : ℝ ↦ z + s • v := continuous_const.add (continuous_id.smul continuous_const)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.2 le_top)
  refine ⟨hf.continuous.comp hL, hasCompactSupport_comp_line hc z hv, ?_, ?_, ?_, ?_⟩
  · exact ((hf2.continuous_fderiv two_ne_zero).comp hL).clm_apply continuous_const
  · exact hasCompactSupport_comp_line (G := fun w ↦ fderiv ℝ f w v)
      ((hc.fderiv (𝕜 := ℝ)).mono' fun w hw ↦ subset_tsupport _ fun h ↦ hw (by simp [h])) z hv
  · exact (continuous_eval_const _).comp
      ((hf.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr
        (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))).comp hL)
  · exact hasCompactSupport_comp_line (G := fun w ↦ iteratedFDeriv ℝ 2 f w ![v, v])
      ((hc.iteratedFDeriv (𝕜 := ℝ) 2).mono' fun w hw ↦ subset_tsupport _
        fun h ↦ hw (by simp [h])) z hv

theorem eventually_atTop_zero {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    ∀ᶠ s in atTop, g s = 0 := by
  obtain ⟨M, hM⟩ := hg.isBounded.subset_closedBall 0
  filter_upwards [eventually_gt_atTop M] with s hs
  refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
  have := hM h
  rw [mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_abs_self s]

theorem eventually_atBot_zero {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    ∀ᶠ s in atBot, g s = 0 := by
  obtain ⟨M, hM⟩ := hg.isBounded.subset_closedBall 0
  filter_upwards [eventually_lt_atBot (-M)] with s hs
  refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
  have := hM h
  rw [mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [neg_abs_le s]

/-- `∫ f'' = 0` along a line. -/
theorem integral_line_second_deriv {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (z : ℂ) {v : ℂ} (hv : ‖v‖ = 1) :
    ∫ s : ℝ, iteratedFDeriv ℝ 2 f (z + s • v) ![v, v] = 0 := by
  obtain ⟨-, -, h1c, h1s, h2c, h2s⟩ := line_facts hf hc z hv
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun s ↦ hasDerivAt_comp_line₂ (hf.of_le (WithTop.coe_le_coe.2 le_top)) z v s)
    (h2c.integrable_of_hasCompactSupport h2s) (h1c.integrable_of_hasCompactSupport h1s)

/-- `∫ |s| f''(s) ds = 2 f(0)` along a line. -/
theorem integral_abs_mul_line_second_deriv {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (z : ℂ) {v : ℂ} (hv : ‖v‖ = 1) :
    ∫ s : ℝ, |s| * iteratedFDeriv ℝ 2 f (z + s • v) ![v, v] = 2 * f z := by
  obtain ⟨h0c, h0s, h1c, h1s, h2c, h2s⟩ := line_facts hf hc z hv
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.2 le_top)
  set h := fun s : ℝ ↦ f (z + s • v)
  set H := fun s : ℝ ↦ fderiv ℝ f (z + s • v) v
  set H' := fun s : ℝ ↦ iteratedFDeriv ℝ 2 f (z + s • v) ![v, v]
  have hint : Integrable fun s : ℝ ↦ s * H' s :=
    (continuous_id.mul h2c).integrable_of_hasCompactSupport h2s.mul_left
  have hint' : Integrable fun s : ℝ ↦ -s * H' s := by
    simpa [neg_mul] using hint.neg
  -- right half-line
  have hR : ∫ s in Ioi (0 : ℝ), s * H' s = f z := by
    have := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (m := 0)
      (f := fun s ↦ s * H s - h s) (f' := fun s ↦ s * H' s)
      (fun s _ ↦ (((hasDerivAt_id s).mul (hasDerivAt_comp_line₂ hf2 z v s)).sub
          (hasDerivAt_comp_line hf2 z v s)).congr_deriv (by
            simp only [H, H', id, Pi.neg_apply]; ring))
      hint.integrableOn
      (tendsto_const_nhds.congr' (by
        filter_upwards [eventually_atTop_zero h0s, eventually_atTop_zero h1s] with s e0 e1
        simp only [h, H] at e0 e1 ⊢
        rw [e0, e1]; ring))
    rw [this]; simp [h]
  -- left half-line
  have hL : ∫ s in Iic (0 : ℝ), -s * H' s = f z := by
    have := integral_Iic_of_hasDerivAt_of_tendsto' (a := 0) (m := 0)
      (f := fun s ↦ -s * H s + h s) (f' := fun s ↦ -s * H' s)
      (fun s _ ↦ ((((hasDerivAt_id s).neg).mul (hasDerivAt_comp_line₂ hf2 z v s)).add
          (hasDerivAt_comp_line hf2 z v s)).congr_deriv (by
            simp only [H, H', id, Pi.neg_apply]; ring))
      hint'.integrableOn
      (tendsto_const_nhds.congr' (by
        filter_upwards [eventually_atBot_zero h0s, eventually_atBot_zero h1s] with s e0 e1
        simp only [h, H] at e0 e1 ⊢
        rw [e0, e1]; ring))
    rw [this]; simp [h]
  have habs : Integrable fun s : ℝ ↦ |s| * H' s :=
    (continuous_abs.mul h2c).integrable_of_hasCompactSupport h2s.mul_left
  rw [← intervalIntegral.integral_Iic_add_Ioi habs.integrableOn habs.integrableOn]
  rw [setIntegral_congr_fun measurableSet_Iic (g := fun s ↦ -s * H' s)
      (fun s hs ↦ by simp only; rw [abs_of_nonpos hs]),
    setIntegral_congr_fun measurableSet_Ioi (g := fun s ↦ s * H' s)
      (fun s hs ↦ by simp only; rw [abs_of_pos hs]), hL, hR]
  ring

/-! 13.7 the Laplacian of `α|Im z|` -/
theorem integral_abs_im_mul_laplacian (χ : ℂ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) :
    ∫ z, |z.im| * Laplacian.laplacian χ z = 2 * ∫ t : ℝ, χ t := by
  set A : ℂ → ℝ := fun z ↦ iteratedFDeriv ℝ 2 χ z ![1, 1]
  set B : ℂ → ℝ := fun z ↦ iteratedFDeriv ℝ 2 χ z ![I, I]
  have hΔ : ∀ z, Laplacian.laplacian χ z = A z + B z := fun z ↦ by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane χ]
  have hcont2 : Continuous (iteratedFDeriv ℝ 2 χ) :=
    hχ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  have hAc : Continuous A := (continuous_eval_const _).comp hcont2
  have hBc : Continuous B := (continuous_eval_const _).comp hcont2
  have hAs : HasCompactSupport A := (hc.iteratedFDeriv (𝕜 := ℝ) 2).mono' fun w hw ↦
    subset_tsupport _ fun h ↦ hw (by simp [A, h])
  have hBs : HasCompactSupport B := (hc.iteratedFDeriv (𝕜 := ℝ) 2).mono' fun w hw ↦
    subset_tsupport _ fun h ↦ hw (by simp [B, h])
  have iA : Integrable fun z : ℂ ↦ |z.im| * A z :=
    (continuous_im.abs.mul hAc).integrable_of_hasCompactSupport hAs.mul_left
  have iB : Integrable fun z : ℂ ↦ |z.im| * B z :=
    (continuous_im.abs.mul hBc).integrable_of_hasCompactSupport hBs.mul_left
  -- transport to `ℝ × ℝ`
  have hΦ := Complex.volume_preserving_equiv_real_prod
  have tr : ∀ g : ℂ → ℝ, ∫ z, g z = ∫ p : ℝ × ℝ, g (Complex.measurableEquivRealProd.symm p) :=
    fun g ↦ by
      rw [← hΦ.integral_comp' (fun p ↦ g (Complex.measurableEquivRealProd.symm p))]
      simp
  have trI : ∀ g : ℂ → ℝ, Integrable g →
      Integrable (fun p : ℝ × ℝ ↦ g (Complex.measurableEquivRealProd.symm p))
        ((volume : Measure ℝ).prod volume) := fun g hg ↦ by
    rw [← Measure.volume_eq_prod]
    exact hΦ.symm.integrable_comp_of_integrable hg
  have e1 : ∀ x y : ℝ, Complex.measurableEquivRealProd.symm (x, y) = (y * I : ℂ) + x • (1 : ℂ) :=
    fun x y ↦ by apply Complex.ext <;> simp
  have e2 : ∀ x y : ℝ, Complex.measurableEquivRealProd.symm (x, y) = (x : ℂ) + y • I :=
    fun x y ↦ by apply Complex.ext <;> simp
  have hA0 : ∫ z, |z.im| * A z = 0 := by
    rw [tr, Measure.volume_eq_prod, integral_prod_symm _ (trI _ iA)]
    have : ∀ y : ℝ, ∫ x : ℝ, |(Complex.measurableEquivRealProd.symm (x, y)).im| *
        A (Complex.measurableEquivRealProd.symm (x, y)) = 0 := fun y ↦ by
      simp_rw [e1]
      have h1 : ∀ x : ℝ, ((y * I : ℂ) + x • (1 : ℂ)).im = y := fun x ↦ by simp
      simp_rw [h1, A]
      rw [integral_const_mul, integral_line_second_deriv hχ hc (y * I) (v := 1) norm_one,
        mul_zero]
    simp_rw [this]
    simp
  have hB : ∫ z, |z.im| * B z = 2 * ∫ t : ℝ, χ t := by
    rw [tr, Measure.volume_eq_prod, integral_prod _ (trI _ iB)]
    have : ∀ x : ℝ, ∫ y : ℝ, |(Complex.measurableEquivRealProd.symm (x, y)).im| *
        B (Complex.measurableEquivRealProd.symm (x, y)) = 2 * χ x := fun x ↦ by
      simp_rw [e2]
      have h1 : ∀ y : ℝ, ((x : ℂ) + y • I).im = y := fun y ↦ by simp
      simp_rw [h1, B]
      exact integral_abs_mul_line_second_deriv hχ hc (x : ℂ) (v := I) norm_I
    simp_rw [this]
    rw [integral_const_mul]
  have hsplit : (fun z : ℂ ↦ |z.im| * Laplacian.laplacian χ z) =
      fun z ↦ |z.im| * A z + |z.im| * B z := funext fun z ↦ by rw [hΔ]; ring
  rw [hsplit, integral_add iA iB, hA0, hB, zero_add]

/-! 13.8 continuity of the logarithmic potential of a piece of `μ` -/
theorem IsLineMeasure.continuous_logPotential_Ioc {μ : Measure ℂ} (hμ : IsLineMeasure μ)
    (a b : ℝ) :
    Continuous fun z : ℂ ↦ ∫ t in Ioc a b, Real.log ‖z - t‖ ∂linePull μ := by
  have hfin := hμ.isFiniteMeasure_restrict_Ioc a b
  have hmeas : ∀ δ : ℝ, ∀ z : ℂ, Measurable fun t : ℝ ↦ Real.log (max ‖z - t‖ δ) := fun δ z ↦
    Real.measurable_log.comp ((continuous_const.sub continuous_ofReal).norm.max
      continuous_const).measurable
  -- the truncated potentials are continuous
  have hFδ : ∀ δ : ℝ, 0 < δ → Continuous fun z : ℂ ↦
      ∫ t in Ioc a b, Real.log (max ‖z - t‖ δ) ∂linePull μ := by
    intro δ hδ
    rw [continuous_iff_continuousAt]
    intro z₀
    set D := ‖z₀‖ + 1 + |a| + |b|
    refine MeasureTheory.continuousAt_of_dominated
      (bound := fun _ ↦ |Real.log δ| + |Real.log (D + δ)|)
      (Eventually.of_forall fun z ↦ (hmeas δ z).aestronglyMeasurable) ?_ (integrable_const _)
      (Eventually.of_forall fun t ↦ ?_)
    · filter_upwards [ball_mem_nhds z₀ one_pos] with z hz
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hy1 : δ ≤ max ‖z - t‖ δ := le_max_right _ _
      have hD : 0 ≤ D := by positivity
      have hy2 : max ‖z - t‖ δ ≤ D + δ := by
        refine max_le ?_ (by linarith)
        have h1 : ‖z - t‖ ≤ ‖z‖ + |t| := by
          have := norm_sub_le z (t : ℂ); rwa [norm_real, Real.norm_eq_abs] at this
        have h2 : ‖z‖ ≤ ‖z₀‖ + 1 := by
          have := norm_le_norm_add_norm_sub' z z₀
          rw [mem_ball, dist_eq_norm] at hz; linarith
        have h3 : |t| ≤ |a| + |b| := by
          rcases le_total 0 t with h | h
          · rw [abs_of_nonneg h]; linarith [ht.2, le_abs_self b, abs_nonneg a]
          · rw [abs_of_nonpos h]; linarith [ht.1, neg_abs_le a, abs_nonneg b]
        linarith
      rw [Real.norm_eq_abs]
      have hy0 : 0 < max ‖z - t‖ δ := hδ.trans_le hy1
      rcases le_total 1 (max ‖z - t‖ δ) with h1 | h1
      · rw [abs_of_nonneg (Real.log_nonneg h1)]
        have := Real.log_le_log hy0 hy2
        linarith [le_abs_self (Real.log (D + δ)), abs_nonneg (Real.log δ)]
      · rw [abs_of_nonpos (Real.log_nonpos hy0.le h1)]
        have := Real.log_le_log hδ hy1
        linarith [neg_abs_le (Real.log δ), abs_nonneg (Real.log (D + δ))]
    · exact (((continuous_id.sub continuous_const).norm.max continuous_const).continuousAt).log
        (ne_of_gt (hδ.trans_le (le_max_right _ _)))
  -- (L8) at scale 1
  obtain ⟨CL, hCL⟩ := hμ.lintegral_log_line one_pos
  -- the error of the truncation
  have herr : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ z : ℂ,
      |(∫ t in Ioc a b, Real.log ‖z - t‖ ∂linePull μ) -
        ∫ t in Ioc a b, Real.log (max ‖z - t‖ δ) ∂linePull μ| ≤
        if z.re ∈ Icc (a - 1) (b + 1) then CL * (μ (lineInterval z.re δ)).toReal else 0 := by
    intro δ hδ hδ1 z
    set x := z.re
    have hint1 := hμ.integrableOn_log z a b
    have hint2 : IntegrableOn (fun t : ℝ ↦ Real.log (max ‖z - t‖ δ)) (Ioc a b) (linePull μ) := by
      refine Integrable.of_bound (hmeas δ z).aestronglyMeasurable
        (|Real.log δ| + |Real.log (‖z‖ + |a| + |b| + δ)|) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hy1 : δ ≤ max ‖z - t‖ δ := le_max_right _ _
      have hD : 0 ≤ ‖z‖ + |a| + |b| := by positivity
      have hy2 : max ‖z - t‖ δ ≤ ‖z‖ + |a| + |b| + δ := by
        refine max_le ?_ (by linarith)
        have h1 : ‖z - t‖ ≤ ‖z‖ + |t| := by
          have := norm_sub_le z (t : ℂ); rwa [norm_real, Real.norm_eq_abs] at this
        have h3 : |t| ≤ |a| + |b| := by
          rcases le_total 0 t with h | h
          · rw [abs_of_nonneg h]; linarith [ht.2, le_abs_self b, abs_nonneg a]
          · rw [abs_of_nonpos h]; linarith [ht.1, neg_abs_le a, abs_nonneg b]
        linarith
      rw [Real.norm_eq_abs]
      have hy0 : 0 < max ‖z - t‖ δ := hδ.trans_le hy1
      rcases le_total 1 (max ‖z - t‖ δ) with h1 | h1
      · rw [abs_of_nonneg (Real.log_nonneg h1)]
        have := Real.log_le_log hy0 hy2
        linarith [le_abs_self (Real.log (‖z‖ + |a| + |b| + δ)), abs_nonneg (Real.log δ)]
      · rw [abs_of_nonpos (Real.log_nonpos hy0.le h1)]
        have := Real.log_le_log hδ hy1
        linarith [neg_abs_le (Real.log δ), abs_nonneg (Real.log (‖z‖ + |a| + |b| + δ))]
    split_ifs with hx
    · rw [← integral_sub hint1 hint2, ← Real.norm_eq_abs]
      refine (norm_integral_le_lintegral_norm _).trans ?_
      rw [← ENNReal.coe_toReal CL, ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
        (hμ.lineInterval_lt_top x δ).ne) ?_
      calc ∫⁻ t in Ioc a b, ENNReal.ofReal ‖Real.log ‖z - t‖ - Real.log (max ‖z - t‖ δ)‖
            ∂linePull μ
          ≤ ∫⁻ t in Ioc a b, (Ioo (x - δ) (x + δ)).indicator
              (fun t ↦ ENNReal.ofReal (Real.log (δ / |t - x|))) t ∂linePull μ := by
            refine setLIntegral_mono_ae' measurableSet_Ioc ?_
            filter_upwards [hμ.ae_ne x] with t htx _
            have hxt : |t - x| ≤ ‖z - t‖ := norm_sub_ofReal_ge z t
            have hxt0 : 0 < |t - x| := abs_pos.2 (sub_ne_zero.2 htx)
            have hy0 : 0 < ‖z - t‖ := hxt0.trans_le hxt
            rcases le_total δ ‖z - t‖ with h | h
            · rw [max_eq_left h, sub_self, norm_zero, ENNReal.ofReal_zero]; exact bot_le
            · rw [max_eq_right h]
              by_cases hlt : ‖z - t‖ < δ
              · have hmem : t ∈ Ioo (x - δ) (x + δ) := by
                  have := abs_lt.1 (hxt.trans_lt hlt)
                  constructor <;> linarith [this.1, this.2]
                rw [indicator_of_mem hmem]
                apply ENNReal.ofReal_le_ofReal
                rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by
                  linarith [Real.log_le_log hy0 h]), Real.log_div hδ.ne' hxt0.ne']
                linarith [Real.log_le_log hxt0 hxt]
              · have : ‖z - t‖ = δ := le_antisymm h (not_lt.1 hlt)
                rw [this, sub_self, norm_zero, ENNReal.ofReal_zero]; exact bot_le
        _ ≤ ∫⁻ t, (Ioo (x - δ) (x + δ)).indicator
              (fun t ↦ ENNReal.ofReal (Real.log (δ / |t - x|))) t ∂linePull μ :=
            setLIntegral_le_lintegral _ _
        _ = ∫⁻ t in Ioo (x - δ) (x + δ), ENNReal.ofReal (Real.log (δ / |t - x|)) ∂linePull μ :=
            lintegral_indicator measurableSet_Ioo _
        _ ≤ CL * μ (lineInterval x δ) := hCL x δ hδ hδ1
    · have : (∫ t in Ioc a b, Real.log ‖z - t‖ ∂linePull μ) =
          ∫ t in Ioc a b, Real.log (max ‖z - t‖ δ) ∂linePull μ := by
        refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
        have hxt : |t - x| ≤ ‖z - t‖ := norm_sub_ofReal_ge z t
        have : 1 < |t - x| := by
          simp only [mem_Icc, not_and_or, not_le] at hx
          rw [abs_sub_comm]
          rcases hx with hx | hx
          · rw [abs_of_neg (by linarith [ht.1])]; linarith [ht.1]
          · rw [abs_of_pos (by linarith [ht.2])]; linarith [ht.2]
        rw [max_eq_left (by linarith)]
      rw [this, sub_self, abs_zero]
  -- uniform smallness of `μ(I(x, δ))` near `[a, b]`
  have hsmall : ∀ ε > 0, ∃ δ, 0 < δ ∧ δ ≤ 1 ∧ ∀ x ∈ Icc (a - 1) (b + 1),
      (μ (lineInterval x δ)).toReal < ε := by
    intro ε hε
    have hU := (isCompact_Icc (a := a - 2) (b := b + 2)).uniformContinuousOn_of_continuous
      (continuous_lineCDF hμ 0).continuousOn
    obtain ⟨δ₀, hδ₀, hU'⟩ := Metric.uniformContinuousOn_iff.1 hU ε hε
    refine ⟨min 1 (δ₀ / 3), lt_min one_pos (by positivity), min_le_left _ _, fun x hx ↦ ?_⟩
    set δ := min 1 (δ₀ / 3)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ3 : δ ≤ δ₀ / 3 := min_le_right _ _
    have hδ0 : 0 < δ := lt_min one_pos (by positivity)
    have h1 := hU' (x + δ) ⟨by linarith [hx.1], by linarith [hx.2]⟩ (x - δ)
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
      (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)
    have h2 := lineCDF_sub hμ 0 (show x - δ ≤ x + δ by linarith)
    rw [Real.dist_eq] at h1
    have h3 : (μ (lineInterval x δ)).toReal ≤ (linePull μ (Ioc (x - δ) (x + δ))).toReal := by
      rw [← linePull_Ioo]
      exact ENNReal.toReal_mono (hμ.linePull_Ioc_lt_top _ _).ne
        (measure_mono Ioo_subset_Ioc_self)
    have := le_abs_self (lineCDF μ 0 (x + δ) - lineCDF μ 0 (x - δ))
    linarith
  -- conclusion by uniform approximation
  refine continuous_of_uniform_approx_of_continuous fun u hu ↦ ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  have hCL0 : (0 : ℝ) ≤ CL := CL.coe_nonneg
  obtain ⟨δ, hδ, hδ1, hδs⟩ := hsmall (ε / (CL + 1)) (by positivity)
  refine ⟨_, hFδ δ hδ, fun z ↦ hεu ?_⟩
  rw [Real.dist_eq]
  refine (herr δ hδ hδ1 z).trans_lt ?_
  split_ifs with hx
  · calc CL * (μ (lineInterval z.re δ)).toReal ≤ CL * (ε / (CL + 1)) :=
          mul_le_mul_of_nonneg_left (hδs z.re hx).le hCL0
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  · exact hε

/-! ### Helpers for `lineMultipliers` -/

theorem lineZeroCount_eq_zero_iff (μ : Measure ℂ) (α s : ℝ) (z : ℂ) :
    lineZeroCount μ α s z = 0 ↔ z ∉ lineZeroSet μ α s := by
  unfold lineZeroCount lineZeroSet
  by_cases h1 : z ∈ lineNodeSet μ α s true <;> by_cases h2 : z ∈ lineNodeSet μ α s false <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]

theorem ofReal_mem_lineZeroSet {μ : Measure ℂ} {α s x : ℝ} :
    (x : ℂ) ∈ lineZeroSet μ α s ↔ ∃ (k : ℤ) (b : Bool), x = lineNode μ α s k b := by
  unfold lineZeroSet lineNodeSet
  simp only [mem_union, mem_range, ofReal_inj]
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact ⟨k, true, hk.symm⟩
    · exact ⟨k, false, hk.symm⟩
  · rintro ⟨k, b, rfl⟩
    cases b
    · exact Or.inr ⟨k, rfl⟩
    · exact Or.inl ⟨k, rfl⟩

theorem im_eq_zero_of_mem_lineZeroSet {μ : Measure ℂ} {α s : ℝ} {z : ℂ}
    (hz : z ∈ lineZeroSet μ α s) : z.im = 0 := by
  rcases hz with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp

theorem eq_ofReal_re_of_mem_lineZeroSet {μ : Measure ℂ} {α s : ℝ} {z : ℂ}
    (hz : z ∈ lineZeroSet μ α s) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [im_eq_zero_of_mem_lineZeroSet hz])

/-! ### Helpers for 13.9 -/

theorem continuous_logPotential_volume (a b : ℝ) :
    Continuous fun z : ℂ ↦ ∫ t in a..b, Real.log ‖z - t‖ := by
  rcases le_total a b with hab | hab
  · have := isLineMeasure_lebLine.continuous_logPotential_Ioc a b
    rw [linePull_lebLine] at this
    refine this.congr fun z ↦ ?_
    rw [intervalIntegral.integral_of_le hab]
  · have := isLineMeasure_lebLine.continuous_logPotential_Ioc b a
    rw [linePull_lebLine] at this
    refine this.neg.congr fun z ↦ ?_
    rw [intervalIntegral.integral_of_ge hab]
    rfl

theorem continuousAt_log_norm_sub {a z₀ : ℂ} (h : z₀ ≠ a) :
    ContinuousAt (fun z : ℂ ↦ Real.log ‖z - a‖) z₀ :=
  ((continuous_id.sub continuous_const).norm.continuousAt).log
    (norm_ne_zero_iff.2 (sub_ne_zero.2 h))

theorem IsLineMeasure.continuousAt_lineTerm {μ : Measure ℂ} (hμ : IsLineMeasure μ) {α s : ℝ}
    {k : ℤ} {z₀ : ℂ} (hz : ∀ b : Bool, z₀ ≠ lineNode μ α s k b) :
    ContinuousAt (lineTerm μ α s k) z₀ := by
  unfold lineTerm
  refine ((continuousAt_log_norm_sub (hz true)).add (continuousAt_log_norm_sub (hz false))).sub
    (continuousAt_const.mul ((hμ.continuous_logPotential_Ioc _ _).continuousAt.sub
      (continuousAt_const.mul (continuous_logPotential_volume _ _).continuousAt)))

theorem IsLineMeasure.locallyIntegrable_lineTerm {μ : Measure ℂ} (hμ : IsLineMeasure μ)
    (α s : ℝ) (k : ℤ) : LocallyIntegrable (lineTerm μ α s k) := by
  have h1 := (logKernel (lineNode μ α s k true : ℂ)).1
  have h2 := (logKernel (lineNode μ α s k false : ℂ)).1
  have hc1 : Continuous fun z : ℂ ↦
      ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), Real.log ‖z - t‖ ∂linePull μ :=
    hμ.continuous_logPotential_Ioc _ _
  have hc2 : Continuous fun z : ℂ ↦
      ∫ t in lineKnot μ α k..lineKnot μ α (k + 1), Real.log ‖z - t‖ :=
    continuous_logPotential_volume _ _
  have h3 : LocallyIntegrable (fun z : ℂ ↦ (1 / (2 * Real.pi)) *
      ((∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), Real.log ‖z - t‖ ∂linePull μ) -
        2 * α * ∫ t in lineKnot μ α k..lineKnot μ α (k + 1), Real.log ‖z - t‖)) :=
    (continuous_const.mul (hc1.sub (continuous_const.mul hc2))).locallyIntegrable
  exact ((h1.add h2).sub h3).congr (Eventually.of_forall fun z ↦ rfl)

namespace LineConsts

variable {μ : Measure ℂ} {r C₂ c₀ α₁ : ℝ} (hc : LineConsts μ r C₂ c₀ α₁)
include hc

theorem node_mem_Ioc {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) {s : ℝ} (hs : 0 ≤ s)
    (hs' : s ≤ c₀ / 2) (k : ℤ) (b : Bool) :
    lineNode μ α s k b ∈ Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)) := by
  have hl := hc.hyp hα hα'
  obtain ⟨o, ho, he⟩ := lineNode_eq μ α s k b
  have hob : |o| ≤ c₀ / 2 := by
    rcases ho with rfl | rfl
    · rw [abs_of_nonneg hs]; exact hs'
    · rw [abs_neg, abs_of_nonneg hs]; exact hs'
  obtain ⟨m1, m2⟩ := hc.offset_mem hα hα' k hob
  have hk0 : 0 < c₀ / 2 * lineLength μ α k := by
    have := hl.lineLength_pos k; have := hc.hc₀; positivity
  rw [he]; constructor <;> linarith

theorem node_injective {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) {s : ℝ} (hs : 0 ≤ s)
    (hs' : s ≤ c₀ / 2) (b : Bool) :
    Function.Injective fun k : ℤ ↦ ((lineNode μ α s k b : ℝ) : ℂ) := by
  intro k j hkj
  simp only [ofReal_inj] at hkj
  by_contra hne
  exact Set.disjoint_left.1 ((hc.hyp hα hα').cells_disjoint hne)
    (hc.node_mem_Ioc hα hα' hs hs' k b) (hkj ▸ hc.node_mem_Ioc hα hα' hs hs' j b)

/-- Uniform control of the tail of the series on a ball (§3.7). -/
theorem uniform_tail {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) {s : ℝ} (hs : 0 ≤ s)
    (hs' : s ≤ 1 / 2) {R : ℝ} (hR : 0 ≤ R) : ∃ (F : Finset ℤ) (u : ℤ → ℝ), Summable u ∧
      (∀ k, 0 ≤ u k) ∧ ∀ k ∉ F, (∀ z ∈ closedBall (0 : ℂ) R, |lineTerm μ α s k z| ≤ u k) ∧
        ∀ b : Bool, R + 1 < |lineNode μ α s k b| := by
  have hl := hc.hyp hα hα'
  obtain ⟨Cf, -, hCf⟩ := hc.far_sum
  obtain ⟨hf, -, hf0⟩ := far_summable hCf hα hα' 0
  set A := 52 * r
  have hr := hc.hr
  set M := 2 * R + 4 * A + 2
  obtain ⟨K₀, K₁, hK⟩ := hl.cells_meeting_subset (-M - 1) (M + 1)
  refine ⟨Finset.Icc K₀ K₁, fun k ↦ 32 * (if 2 * lineLength μ α k ≤ ‖(0 : ℂ) - lineCentre μ α k‖
    then (lineLength μ α k / ‖(0 : ℂ) - lineCentre μ α k‖) ^ 2 else 0), hf.mul_left 32,
    fun k ↦ by have := hf0 k; simp only [Pi.zero_apply] at this; positivity, fun k hk ↦ ?_⟩
  have hlamI := hc.centre_mem_Icc hα hα' k
  have hle := hl.lineLength_le k
  have hp := hl.lineLength_pos k
  have hlam : M < |lineCentre μ α k| := by
    by_contra hcon
    push Not at hcon
    rw [abs_le] at hcon
    exact hk (Finset.mem_Icc.2 (hK k (by linarith [hlamI.2]) (by linarith [hlamI.1])))
  have h0 : ‖(0 : ℂ) - lineCentre μ α k‖ = |lineCentre μ α k| := by
    rw [zero_sub, norm_neg, norm_real, Real.norm_eq_abs]
  have hfar0 : 2 * lineLength μ α k ≤ ‖(0 : ℂ) - lineCentre μ α k‖ := by rw [h0]; linarith
  refine ⟨fun z hz ↦ ?_, fun b ↦ ?_⟩
  · rw [mem_closedBall, dist_zero_right] at hz
    have hd : |lineCentre μ α k| / 2 ≤ ‖z - lineCentre μ α k‖ := by
      have := norm_sub_norm_le ((lineCentre μ α k : ℝ) : ℂ) z
      rw [norm_real, Real.norm_eq_abs, norm_sub_rev] at this
      linarith
    have hfar : 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ := by linarith
    refine (hc.far_field hα hα' hs hs' k z hfar).trans ?_
    have hfar0' : 2 * lineLength μ α k ≤ |lineCentre μ α k| := h0 ▸ hfar0
    simp only [h0, hfar0', ite_true]
    have hlpos : 0 < |lineCentre μ α k| := by linarith
    have : lineLength μ α k / ‖z - lineCentre μ α k‖ ≤ 2 * (lineLength μ α k / |lineCentre μ α k|) := by
      calc lineLength μ α k / ‖z - lineCentre μ α k‖ ≤ lineLength μ α k / (|lineCentre μ α k| / 2) :=
            div_le_div_of_nonneg_left hp.le (by positivity) hd
        _ = 2 * (lineLength μ α k / |lineCentre μ α k|) := by field_simp
    have h2 : (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2 ≤
        (2 * (lineLength μ α k / |lineCentre μ α k|)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) this 2
    have h3 : (2 * (lineLength μ α k / |lineCentre μ α k|)) ^ 2 =
        4 * (lineLength μ α k / |lineCentre μ α k|) ^ 2 := by ring
    linarith
  · obtain ⟨o, ho, he⟩ := lineNode_eq μ α s k b
    have : |o * lineLength μ α k| ≤ A := by
      rw [abs_mul, abs_of_pos hp]
      have : |o| ≤ 1 / 2 := by
        rcases ho with rfl | rfl
        · rw [abs_of_nonneg hs]; exact hs'
        · rw [abs_neg, abs_of_nonneg hs]; exact hs'
      nlinarith [abs_nonneg o]
    rw [he]
    have := abs_sub_abs_le_abs_sub (lineCentre μ α k) (-(o * lineLength μ α k))
    rw [sub_neg_eq_add, abs_neg] at this
    linarith

/-- The series is a finite sum plus a tail which is continuous on a ball. -/
theorem decomp {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2)
    {R : ℝ} (hR : 0 ≤ R) : ∃ F : Finset ℤ, (∀ k ∉ F, ∀ b : Bool,
      R + 1 < |lineNode μ α s k b|) ∧
      ContinuousOn (fun z ↦ ∑' k, if k ∈ F then 0 else lineTerm μ α s k z) (closedBall 0 R) ∧
      (∃ B : ℝ, ∀ k ∉ F, ∀ z ∈ closedBall (0 : ℂ) R, |lineTerm μ α s k z| ≤ B) ∧
      ∀ z, linePotential μ α s z = ∑ k ∈ F, lineTerm μ α s k z +
        ∑' k, if k ∈ F then 0 else lineTerm μ α s k z := by
  classical
  obtain ⟨F, u, hu, hu0, hFu⟩ := hc.uniform_tail hα hα' hs hs' hR
  obtain ⟨Cf, -, hCf⟩ := hc.far_sum
  refine ⟨F, fun k hk ↦ (hFu k hk).2, ?_, ⟨∑' k, u k, fun k hk z hz ↦
    ((hFu k hk).1 z hz).trans (hu.le_tsum k (fun j _ ↦ hu0 j))⟩, fun z ↦ ?_⟩
  · refine continuousOn_tsum (u := u) (fun k ↦ ?_) hu (fun k z hz ↦ ?_)
    · by_cases hk : k ∈ F
      · simp only [hk, ite_true]; exact continuousOn_const
      · simp only [hk, ite_false]
        intro z hz
        refine (hc.hμ.continuousAt_lineTerm fun b hb ↦ ?_).continuousWithinAt
        have h1 := (hFu k hk).2 b
        rw [mem_closedBall, dist_zero_right, hb, norm_real, Real.norm_eq_abs] at hz
        linarith
    · by_cases hk : k ∈ F
      · simp only [hk, ite_true, norm_zero]; exact hu0 k
      · simp only [hk, ite_false, Real.norm_eq_abs]; exact (hFu k hk).1 z hz
  · have hT := (hc.lineTerm_split hCf hα hα' hs hs' z).1
    have hg : Summable fun k ↦ if k ∈ F then 0 else lineTerm μ α s k z := by
      refine hT.congr_cofinite ?_
      filter_upwards [F.finite_toSet.compl_mem_cofinite] with k hk
      simp only [mem_compl_iff, Finset.mem_coe] at hk
      simp [hk]
    have hf : Summable fun k ↦ if k ∈ F then lineTerm μ α s k z else 0 :=
      summable_of_ne_finset_zero (s := F) (fun k hk ↦ by simp [hk])
    unfold linePotential
    rw [show (fun k ↦ lineTerm μ α s k z) = fun k ↦ (if k ∈ F then lineTerm μ α s k z else 0) +
      (if k ∈ F then 0 else lineTerm μ α s k z) from funext fun k ↦ by split_ifs <;> simp,
      hf.tsum_add hg, tsum_eq_sum (s := F) (fun k hk ↦ by simp [hk])]
    congr 1
    exact Finset.sum_congr rfl fun k hk ↦ by simp [hk]

end LineConsts

theorem hasCompactSupport_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) : HasCompactSupport (Laplacian.laplacian χ) :=
  IsCompact.of_isClosed_subset hc (isClosed_tsupport _) (laplacian_testFunction hχ).2

/-- The weak Laplacian of the potential of a piece `(ν|_{(a,b]})` of a line measure. -/
theorem IsLineMeasure.integral_logPotential_Ioc_mul_laplacian {ν : Measure ℂ}
    (hν : IsLineMeasure ν) {a b : ℝ} (hab : a ≤ b) (χ : ℂ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    ∫ z : ℂ, (∫ t in Ioc a b, Real.log ‖z - (t : ℂ)‖ ∂linePull ν) * Laplacian.laplacian χ z =
      2 * Real.pi * ∫ t in Ioc a b, χ t ∂linePull ν := by
  have := hν.isFiniteMeasure_restrict_Ioc a b
  set m := Measure.map (fun t : ℝ ↦ (t : ℂ)) ((linePull ν).restrict (Ioc a b))
  have hL : IsCompact ((fun t : ℝ ↦ (t : ℂ)) '' Icc a b) := isCompact_Icc.image continuous_ofReal
  have hmL : m ((fun t : ℝ ↦ (t : ℂ)) '' Icc a b)ᶜ = 0 := by
    rw [Measure.map_apply continuous_ofReal.measurable hL.isClosed.measurableSet.compl,
      Measure.restrict_apply (hL.isClosed.measurableSet.compl.preimage
        continuous_ofReal.measurable)]
    convert measure_empty (μ := linePull ν)
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
    rintro ⟨h, ht⟩
    exact h (mem_image_of_mem _ (Ioc_subset_Icc_self ht))
  have e1 : ∀ z : ℂ, ∫ ζ, Real.log ‖z - ζ‖ ∂m = ∫ t in Ioc a b, Real.log ‖z - t‖ ∂linePull ν :=
    fun z ↦ measurableEmbedding_ofReal'.integral_map _
  have e2 : ∫ ζ, χ ζ ∂m = ∫ t in Ioc a b, χ t ∂linePull ν :=
    measurableEmbedding_ofReal'.integral_map _
  have H := integral_logPotential_mul_laplacian m hL hmL χ hχ hc
  simp_rw [e1, e2] at H
  exact H

/-- The weak Laplacian of one term: `Δ T_k = 2π(δ_{ν₊} + δ_{ν₋}) − σ_α|_{I_k}`. -/
theorem IsLineMeasure.integral_lineTerm_mul_laplacian {μ : Measure ℂ} (hμ : IsLineMeasure μ)
    {α s : ℝ} (k : ℤ) (hab : lineKnot μ α k ≤ lineKnot μ α (k + 1)) (χ : ℂ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    ∫ z, lineTerm μ α s k z * Laplacian.laplacian χ z =
      2 * Real.pi * (χ (lineNode μ α s k true) + χ (lineNode μ α s k false)) -
        (∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), χ t ∂linePull μ) +
        2 * α * ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), χ t := by
  set a := lineKnot μ α k
  set b := lineKnot μ α (k + 1)
  obtain ⟨hΔc, -⟩ := laplacian_testFunction hχ
  have hΔs := hasCompactSupport_laplacian hχ hc
  set Δχ := Laplacian.laplacian χ
  set νp : ℂ := (lineNode μ α s k true : ℂ)
  set νm : ℂ := (lineNode μ α s k false : ℂ)
  set Pμ : ℂ → ℝ := fun z ↦ ∫ t in Ioc a b, Real.log ‖z - t‖ ∂linePull μ
  set Pv : ℂ → ℝ := fun z ↦ ∫ t in Ioc a b, Real.log ‖z - t‖
  have hPμ : Continuous Pμ := hμ.continuous_logPotential_Ioc a b
  have hPv : Continuous Pv := by
    have := isLineMeasure_lebLine.continuous_logPotential_Ioc a b
    rwa [linePull_lebLine] at this
  have i1 : Integrable fun z ↦ Real.log ‖z - νp‖ * Δχ z :=
    (logKernel νp).1.integrable_smul_right_of_hasCompactSupport hΔc hΔs
  have i2 : Integrable fun z ↦ Real.log ‖z - νm‖ * Δχ z :=
    (logKernel νm).1.integrable_smul_right_of_hasCompactSupport hΔc hΔs
  have i3 : Integrable fun z ↦ Pμ z * Δχ z :=
    hPμ.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hΔc hΔs
  have i4 : Integrable fun z ↦ Pv z * Δχ z :=
    hPv.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hΔc hΔs
  have hT : ∀ z, lineTerm μ α s k z * Δχ z = Real.log ‖z - νp‖ * Δχ z +
      Real.log ‖z - νm‖ * Δχ z - (1 / (2 * Real.pi)) * (Pμ z * Δχ z - 2 * α * (Pv z * Δχ z)) := by
    intro z
    simp only [lineTerm, Pμ, Pv, νp, νm, a, b]
    rw [intervalIntegral.integral_of_le hab]
    ring
  have H1 := (logKernel νp).2 χ hχ hc
  have H2 := (logKernel νm).2 χ hχ hc
  have H3 := hμ.integral_logPotential_Ioc_mul_laplacian hab χ hχ hc
  have H4 := isLineMeasure_lebLine.integral_logPotential_Ioc_mul_laplacian hab χ hχ hc
  rw [linePull_lebLine] at H4
  have ia : Integrable fun z ↦ Real.log ‖z - νp‖ * Δχ z + Real.log ‖z - νm‖ * Δχ z := i1.add i2
  have ic : Integrable fun z ↦ 2 * α * (Pv z * Δχ z) := i4.const_mul _
  have ib : Integrable fun z ↦ (1 / (2 * Real.pi)) * (Pμ z * Δχ z - 2 * α * (Pv z * Δχ z)) :=
    (i3.sub ic).const_mul _
  rw [integral_congr_ae (Eventually.of_forall hT), integral_sub ia ib, integral_add i1 i2,
    integral_const_mul, integral_sub i3 ic, integral_const_mul]
  simp only [Pμ, Pv] at H3 H4 ⊢
  rw [H1, H2, H3, H4]
  have hπ := Real.pi_pos
  field_simp
  ring

/-- The counting function of the zeros, summed against a test function. -/
theorem LineConsts.finsum_lineZeroCount {μ : Measure ℂ} {r C₂ c₀ α₁ : ℝ}
    (hc : LineConsts μ r C₂ c₀ α₁) {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) {s : ℝ} (hs : 0 ≤ s)
    (hs' : s ≤ c₀ / 2) (χ : ℂ → ℝ) (G : Finset ℤ)
    (hG : ∀ k ∉ G, ∀ b : Bool, χ (lineNode μ α s k b) = 0) :
    ∑ᶠ ζ, (lineZeroCount μ α s ζ : ℝ) * χ ζ =
      ∑ k ∈ G, (χ (lineNode μ α s k true) + χ (lineNode μ α s k false)) := by
  have hb : ∀ b : Bool, ∑ᶠ ζ, (lineNodeSet μ α s b).indicator χ ζ =
      ∑ k ∈ G, χ (lineNode μ α s k b) := by
    intro b
    rw [← finsum_mem_def, lineNodeSet, finsum_mem_range (hc.node_injective hα hα' hs hs' b)]
    refine finsum_eq_sum_of_support_subset _ (fun k hk ↦ ?_)
    by_contra hkG
    exact hk (hG k hkG b)
  have hfin : ∀ b : Bool, (Function.support ((lineNodeSet μ α s b).indicator χ)).Finite := by
    intro b
    refine ((G.finite_toSet).image fun k ↦ ((lineNode μ α s k b : ℝ) : ℂ)).subset
      (fun ζ hζ ↦ ?_)
    rw [Function.mem_support] at hζ
    have hmem : ζ ∈ lineNodeSet μ α s b := by
      by_contra h; exact hζ (indicator_of_notMem h _)
    have hmem' := hmem
    simp only [lineNodeSet, mem_range] at hmem'
    obtain ⟨k, rfl⟩ := hmem'
    refine ⟨k, ?_, rfl⟩
    by_contra hkG
    rw [indicator_of_mem hmem] at hζ
    exact hζ (hG k hkG b)
  have hpt : ∀ ζ, (lineZeroCount μ α s ζ : ℝ) * χ ζ =
      (lineNodeSet μ α s true).indicator χ ζ + (lineNodeSet μ α s false).indicator χ ζ := by
    intro ζ
    unfold lineZeroCount
    by_cases h1 : ζ ∈ lineNodeSet μ α s true <;> by_cases h2 : ζ ∈ lineNodeSet μ α s false <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2] <;> ring
  rw [finsum_congr hpt, finsum_add_distrib (hfin true) (hfin false), hb true, hb false,
    Finset.sum_add_distrib]

/-! 13.9 `φ − α|Im z| + S` is the log-modulus of an entire function (M07 weak entry) -/
theorem isWeakLogModulus_linePotential {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight univ φ μ) (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 ≤ s → s ≤ s₁ →
      IsWeakLogModulus univ (lineZeroCount μ α s)
        (fun z ↦ φ z - α * |z.im| + linePotential μ α s z) := by
  obtain ⟨r, C₂, c₀, α₁, hc⟩ := hμ.exists_lineConsts
  refine ⟨α₁, c₀ / 2, hc.hα₁, by linarith [hc.hc₀], by linarith [hc.hc₀'],
    fun α hα hα' s hs hs' ↦ ?_⟩
  have hl := hc.hyp hα hα'
  have hs2 : s ≤ 1 / 2 := by linarith [hc.hc₀']
  have hφc : Continuous φ := continuousOn_univ.1 hφ.continuousOn
  have him : Continuous fun z : ℂ ↦ α * |z.im| := continuous_const.mul continuous_im.abs
  have hsupp : Function.support (lineZeroCount μ α s) = lineZeroSet μ α s := by
    ext z
    rw [Function.mem_support, Ne, lineZeroCount_eq_zero_iff, not_not]
  have hZ : ∀ ζ ∈ lineZeroSet μ α s, ∃ (k : ℤ) (b : Bool), ζ = (lineNode μ α s k b : ℂ) := by
    rintro ζ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨k, true, rfl⟩
    · exact ⟨k, false, rfl⟩
  have hZ' : ∀ (k : ℤ) (b : Bool), ((lineNode μ α s k b : ℝ) : ℂ) ∈ lineZeroSet μ α s := by
    intro k b
    cases b
    · exact Or.inr ⟨k, rfl⟩
    · exact Or.inl ⟨k, rfl⟩
  -- cells meeting a ball
  have hcells : ∀ R : ℝ, ∃ G : Finset ℤ, ∀ k ∉ G, ∀ t ∈ Icc (lineKnot μ α k) (lineKnot μ α (k + 1)),
      R < |t| := by
    intro R
    obtain ⟨K₀, K₁, hK⟩ := hl.cells_meeting_subset (-R - 1) (R + 1)
    refine ⟨Finset.Icc K₀ K₁, fun k hk t ht ↦ ?_⟩
    by_contra hcon
    push Not at hcon
    rw [abs_le] at hcon
    exact hk (Finset.mem_Icc.2 (hK k (by linarith [ht.2]) (by linarith [ht.1])))
  -- local integrability of the series
  have hS : LocallyIntegrable (linePotential μ α s) := by
    refine locallyIntegrable_iff.2 fun K hK ↦ ?_
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨F, -, hcont, -, hdec⟩ := hc.decomp hα hα' hs hs2 (le_max_right R 0)
    have h1 : IntegrableOn (fun z ↦ ∑ k ∈ F, lineTerm μ α s k z) (closedBall 0 (max R 0)) :=
      (locallyIntegrable_finsetSum F fun k _ ↦ hμ.locallyIntegrable_lineTerm α s k).integrableOn_isCompact
        (isCompact_closedBall 0 _)
    have h2 := ContinuousOn.integrableOn_compact (μ := volume) (isCompact_closedBall 0 (max R 0))
      hcont
    refine ((h1.add h2).congr_fun (fun z _ ↦ (hdec z).symm) measurableSet_closedBall).mono_set
      (hR.trans (closedBall_subset_closedBall (le_max_left _ _)))
  refine ⟨fun K _ hK ↦ ?_, ?_, ?_, ?_⟩
  · -- finite support
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨G, hG⟩ := hcells R
    rw [hsupp]
    refine (((G.finite_toSet).prod (Set.finite_univ (α := Bool))).image
      fun p : ℤ × Bool ↦ ((lineNode μ α s p.1 p.2 : ℝ) : ℂ)).subset (fun ζ hζ ↦ ?_)
    obtain ⟨k, b, rfl⟩ := hZ ζ hζ.2
    refine ⟨(k, b), ⟨?_, mem_univ _⟩, rfl⟩
    by_contra hkG
    have h1 := hG k hkG _ (Ioc_subset_Icc_self (hc.node_mem_Ioc hα hα' hs hs' k b))
    have h2 := hR hζ.1
    rw [mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs] at h2
    linarith
  · -- local integrability
    rw [locallyIntegrableOn_univ]
    exact (hφc.locallyIntegrable.sub him.locallyIntegrable).add hS
  · -- continuity off the zeros
    intro z₀ hz₀
    have hz₀Z : z₀ ∉ lineZeroSet μ α s := by rw [← hsupp]; exact hz₀.2
    obtain ⟨F, -, hcont, -, hdec⟩ := hc.decomp hα hα' hs hs2 (by positivity : 0 ≤ ‖z₀‖ + 1)
    have hsum : ContinuousAt (fun z ↦ ∑ k ∈ F, lineTerm μ α s k z) z₀ :=
      tendsto_finsetSum F fun k _ ↦ hμ.continuousAt_lineTerm fun b hb ↦ hz₀Z (hb ▸ hZ' k b)
    have htail : ContinuousAt (fun z ↦ ∑' k, if k ∈ F then 0 else lineTerm μ α s k z) z₀ :=
      hcont.continuousAt (closedBall_mem_nhds_of_mem (by
        rw [mem_ball, dist_zero_right]; linarith))
    have hSc : ContinuousAt (linePotential μ α s) z₀ :=
      (hsum.add htail).congr (Eventually.of_forall fun z ↦ (hdec z).symm)
    exact ((hφc.continuousAt.sub him.continuousAt).add hSc).continuousWithinAt
  · -- the weak Laplacian
    intro χ hχ hcχ _
    obtain ⟨hΔc, -⟩ := laplacian_testFunction hχ
    have hΔs := hasCompactSupport_laplacian hχ hcχ
    set Δχ := Laplacian.laplacian χ
    obtain ⟨R₀, hR₀⟩ := hcχ.isBounded.subset_closedBall 0
    set R := max R₀ 0
    have hR : tsupport χ ⊆ closedBall 0 R :=
      hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
    have hχ0 : ∀ z, R < ‖z‖ → χ z = 0 := fun z hz ↦ image_eq_zero_of_notMem_tsupport
      (fun h ↦ by have := hR h; rw [mem_closedBall, dist_zero_right] at this; linarith)
    have hΔ0 : ∀ z, R < ‖z‖ → Δχ z = 0 := fun z hz ↦ image_eq_zero_of_notMem_tsupport
      (fun h ↦ by
        have := hR ((laplacian_testFunction hχ).2 h)
        rw [mem_closedBall, dist_zero_right] at this; linarith)
    -- integrability
    have iφ : Integrable fun z ↦ φ z * Δχ z :=
      hφc.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hΔc hΔs
    have iim : Integrable fun z ↦ α * |z.im| * Δχ z :=
      him.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hΔc hΔs
    have iS : Integrable fun z ↦ linePotential μ α s z * Δχ z :=
      hS.integrable_smul_right_of_hasCompactSupport hΔc hΔs
    have hsplit : ∫ z, (φ z - α * |z.im| + linePotential μ α s z) * Δχ z =
        (∫ z, φ z * Δχ z) - α * (∫ z, |z.im| * Δχ z) + ∫ z, linePotential μ α s z * Δχ z := by
      have iim' : Integrable fun z ↦ α * (|z.im| * Δχ z) := by simpa only [mul_assoc] using iim
      have e : (fun z ↦ (φ z - α * |z.im| + linePotential μ α s z) * Δχ z) =
          fun z ↦ (φ z * Δχ z - α * (|z.im| * Δχ z)) + linePotential μ α s z * Δχ z := by
        funext z; ring
      have isub : Integrable fun z ↦ φ z * Δχ z - α * (|z.im| * Δχ z) := iφ.sub iim'
      rw [e, integral_add isub iS, integral_sub iφ iim', integral_const_mul]
    -- the series
    obtain ⟨F, u, hu, hu0, hFu⟩ := hc.uniform_tail hα hα' hs hs2 (le_max_right R₀ 0)
    have iT : ∀ k, Integrable fun z ↦ lineTerm μ α s k z * Δχ z := fun k ↦
      (hμ.locallyIntegrable_lineTerm α s k).integrable_smul_right_of_hasCompactSupport hΔc hΔs
    have hbound : ∀ k ∉ F, ∫ z, ‖lineTerm μ α s k z * Δχ z‖ ≤ u k * ∫ z, ‖Δχ z‖ := by
      intro k hk
      rw [← integral_const_mul]
      refine integral_mono (iT k).norm ((hΔc.norm.integrable_of_hasCompactSupport
        hΔs.norm).const_mul _) (fun z ↦ ?_)
      by_cases hz : z ∈ closedBall (0 : ℂ) R
      · rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right ((hFu k hk).1 z hz) (norm_nonneg _)
      · rw [mem_closedBall, dist_zero_right, not_le] at hz
        rw [hΔ0 z hz]; simp
    have hsumm : Summable fun k ↦ ∫ z, ‖lineTerm μ α s k z * Δχ z‖ := by
      refine Summable.of_nonneg_of_le (fun k ↦ integral_nonneg fun z ↦ norm_nonneg _)
        (fun k ↦ ?_) ((summable_of_ne_finset_zero (s := F) (f := fun k ↦
          if k ∈ F then ∫ z, ‖lineTerm μ α s k z * Δχ z‖ else 0)
          (fun k hk ↦ by simp [hk])).add (hu.mul_right (∫ z, ‖Δχ z‖)))
      by_cases hk : k ∈ F
      · simp only [hk, ite_true]
        have : 0 ≤ u k * ∫ z, ‖Δχ z‖ := mul_nonneg (hu0 k) (integral_nonneg fun z ↦ norm_nonneg _)
        linarith
      · simp only [hk, ite_false, zero_add]; exact hbound k hk
    have hSΔ : ∫ z, linePotential μ α s z * Δχ z = ∑' k, ∫ z, lineTerm μ α s k z * Δχ z := by
      rw [integral_tsum_of_summable_integral_norm iT hsumm]
      congr 1; ext z
      rw [linePotential, tsum_mul_right]
    -- per cell, and the reduction to finitely many cells
    obtain ⟨G, hG⟩ := hcells R
    have hχcell : ∀ k ∉ G, ∀ t ∈ Icc (lineKnot μ α k) (lineKnot μ α (k + 1)), χ t = 0 :=
      fun k hk t ht ↦ hχ0 _ (by rw [norm_real, Real.norm_eq_abs]; exact hG k hk t ht)
    have hnodeG : ∀ k ∉ G, ∀ b : Bool, χ (lineNode μ α s k b) = 0 := fun k hk b ↦
      hχcell k hk _ (Ioc_subset_Icc_self (hc.node_mem_Ioc hα hα' hs hs' k b))
    have hcellI : ∀ k ∉ G, ∀ m₀ : Measure ℝ,
        ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), χ t ∂m₀ = 0 := by
      intro k hk m₀
      exact setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ hχcell k hk t (Ioc_subset_Icc_self ht)
    have hcellsum : ∑' k, ∫ z, lineTerm μ α s k z * Δχ z =
        ∑ k ∈ G, (2 * Real.pi * (χ (lineNode μ α s k true) + χ (lineNode μ α s k false)) -
          (∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), χ t ∂linePull μ) +
          2 * α * ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), χ t) := by
      rw [tsum_eq_sum (s := G)]
      · exact Finset.sum_congr rfl fun k _ ↦
          hμ.integral_lineTerm_mul_laplacian k (hl.lineKnot_le k) χ hχ hcχ
      · intro k hk
        rw [hμ.integral_lineTerm_mul_laplacian k (hl.lineKnot_le k) χ hχ hcχ, hnodeG k hk true,
          hnodeG k hk false, hcellI k hk, hcellI k hk]
        ring
    -- the cells cover the support
    have hcover : ∀ m₀ : Measure ℝ, (∀ k, IntegrableOn (fun t : ℝ ↦ χ t)
        (Ioc (lineKnot μ α k) (lineKnot μ α (k + 1))) m₀) →
        ∑ k ∈ G, ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), χ t ∂m₀ =
          ∫ t, χ t ∂m₀ := by
      intro m₀ hint
      rw [← integral_biUnion_finset G (fun _ _ ↦ measurableSet_Ioc)
        (fun k _ k' _ hkk' ↦ hl.cells_disjoint hkk') (fun k _ ↦ hint k)]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ ?_
      obtain ⟨k, hk, -⟩ := hl.existsUnique_mem t
      have hkG : k ∉ G := fun hkG ↦ ht (mem_biUnion hkG hk)
      exact hχcell k hkG t (Ioc_subset_Icc_self hk)
    have hχc : Continuous fun t : ℝ ↦ χ t := hχ.continuous.comp continuous_ofReal
    have hμI := hcover (linePull μ) fun k ↦ by
      have := hμ.isFiniteMeasureOnCompacts'
      exact (hχc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hvI := hcover volume fun k ↦ (hχc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    rw [hsplit, hφ.laplacian_eq χ hχ hcχ (subset_univ _), integral_abs_im_mul_laplacian χ hχ hcχ,
      hSΔ, hcellsum, hc.finsum_lineZeroCount hα hα' hs hs' χ G hnodeG, hμ.integral_eq,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, hμI, ← Finset.mul_sum, ← Finset.mul_sum, hvI]
    ring

/-- Nodes with a positive offset are never centres. -/
theorem LineConsts.node_ne_centre {μ : Measure ℂ} {r C₂ c₀ α₁ : ℝ}
    (hc : LineConsts μ r C₂ c₀ α₁) {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) {s : ℝ} (hs : 0 < s)
    (hs' : s ≤ c₀ / 2) (k j : ℤ) (b : Bool) : lineNode μ α s k b ≠ lineCentre μ α j := by
  have hl := hc.hyp hα hα'
  obtain ⟨o, ho, he⟩ := lineNode_eq μ α s k b
  have hob : |o| ≤ c₀ / 2 := by
    rcases ho with rfl | rfl
    · rw [abs_of_pos hs]; exact hs'
    · rw [abs_neg, abs_of_pos hs]; exact hs'
  have hp := hl.lineLength_pos k
  have hc0 := hc.hc₀
  intro heq
  rcases eq_or_ne k j with rfl | hkj
  · rw [he] at heq
    have : o * lineLength μ α k = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · rcases ho with rfl | rfl <;> linarith
    · linarith
  · obtain ⟨m1, m2⟩ := hc.offset_mem hα hα' k hob
    obtain ⟨c1, c2⟩ := hc.offset_mem hα hα' j (o := 0) (by simp; linarith)
    have hpj := hl.lineLength_pos j
    have hk0 : 0 < c₀ / 2 * lineLength μ α k := by positivity
    have hj0 : 0 < c₀ / 2 * lineLength μ α j := by positivity
    have hmem1 : lineNode μ α s k b ∈ Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)) := by
      rw [he]; constructor <;> linarith
    have hmem2 : lineNode μ α s k b ∈ Ioc (lineKnot μ α j) (lineKnot μ α (j + 1)) := by
      rw [heq]; simp only [zero_mul, add_zero] at c1 c2; constructor <;> linarith
    exact Set.disjoint_left.1 (hl.cells_disjoint hkj) hmem1 hmem2

/-! 13.10 main export: two multipliers for `φ − α|Im z|` with disjoint exceptional sets -/
theorem lineMultipliers (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoublingLine μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₀ →
      ∃ (f : Fin 2 → ℂ → ℂ) (ε C : ℝ), 0 < ε ∧ 0 < C ∧
        (∀ i, Differentiable ℂ (f i)) ∧ (∀ i, ∃ z₀, f i z₀ ≠ 0) ∧
        (∀ i (z : ℂ), f i z = 0 → z.im = 0) ∧
        (∀ i (z : ℂ), ‖f i z‖ ≤ C * Real.exp (φ z - α * |z.im|)) ∧
        (∀ z : ℂ, ∃ i, ∀ x : ℝ, f i x = 0 → ε * massRadiusLine μ x ≤ ‖z - x‖) ∧
        ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∀ i (z : ℂ),
          (∀ x : ℝ, f i x = 0 → η * massRadiusLine μ x ≤ ‖z - x‖) →
            c * Real.exp (φ z - α * |z.im|) ≤ ‖f i z‖ := by
  have hμ := IsLineMeasure.of_weight hφ hd hm
  obtain ⟨αW, sW, hαW, hsW, -, HW⟩ := isWeakLogModulus_linePotential hφ hμ
  obtain ⟨αB, sB, CB, hαB, hsB, -, HB⟩ := hμ.linePotential_bounds
  obtain ⟨αS, sS, hαS, hsS, -, HS⟩ := hμ.lineNode_separated
  obtain ⟨r, C₂, c₀, α₁, hc⟩ := hμ.exists_lineConsts
  have hc0 := hc.hc₀
  set α₀ := min (min αW αB) (min αS α₁)
  set s₀ := min (min sW sB) (min sS (c₀ / 2))
  have hα₀ : 0 < α₀ := lt_min (lt_min hαW hαB) (lt_min hαS hc.hα₁)
  have hs₀ : 0 < s₀ := lt_min (lt_min hsW hsB) (lt_min hsS (by linarith))
  have hs₀W : s₀ ≤ sW := (min_le_left _ _).trans (min_le_left _ _)
  have hs₀B : s₀ ≤ sB := (min_le_left _ _).trans (min_le_right _ _)
  have hs₀S : s₀ ≤ sS := (min_le_right _ _).trans (min_le_left _ _)
  have hs₀c : s₀ ≤ c₀ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨α₀, hα₀, fun α hα hα' ↦ ?_⟩
  have hαW' : α ≤ αW := hα'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hαB' : α ≤ αB := hα'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hαS' : α ≤ αS := hα'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hα₁' : α ≤ α₁ := hα'.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the entire function attached to the offset `s`
  have hW : ∀ s : ℝ, 0 ≤ s → s ≤ s₀ → ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      (∀ z, h z = 0 ↔ z ∈ lineZeroSet μ α s) ∧
      (∀ z, z ∉ lineZeroSet μ α s →
        ‖h z‖ = Real.exp (φ z - α * |z.im| + linePotential μ α s z)) := by
    intro s hs hs'
    obtain ⟨h, hA, hnorm, hord⟩ := exists_analytic_norm_eq_exp_of_isWeakLogModulus (c := 0)
      (fun z _ ↦ ⟨dist z 0 + 1, by linarith, subset_univ _⟩)
      (HW α hα hαW' s hs (hs'.trans hs₀W))
    refine ⟨h, differentiableOn_univ.1 hA.differentiableOn, fun z ↦ ?_, fun z hz ↦
      hnorm z (mem_univ z) ((lineZeroCount_eq_zero_iff μ α s z).2 hz)⟩
    have h1 := hord z (mem_univ z)
    have h2 : analyticOrderAt h z = 0 ↔ h z ≠ 0 := by
      rw [analyticOrderAt_eq_zero]
      simp [hA z (mem_univ z)]
    constructor
    · intro hz
      by_contra hn
      have h0 : lineZeroCount μ α s z = 0 := (lineZeroCount_eq_zero_iff μ α s z).2 hn
      have h3 : analyticOrderAt h z = 0 := by rw [h1, h0]; rfl
      exact (h2.1 h3) hz
    · intro hz
      by_contra hn
      have h3 : analyticOrderAt h z = 0 := h2.2 hn
      rw [h1] at h3
      have h0 : lineZeroCount μ α s z = 0 := by exact_mod_cast h3
      exact (lineZeroCount_eq_zero_iff μ α s z).1 h0 hz
  -- common properties
  have props : ∀ s : ℝ, 0 ≤ s → s ≤ s₀ → ∀ h : ℂ → ℂ, (∀ z, h z = 0 ↔ z ∈ lineZeroSet μ α s) →
      (∀ z, z ∉ lineZeroSet μ α s →
        ‖h z‖ = Real.exp (φ z - α * |z.im| + linePotential μ α s z)) →
      (∃ z₀, h z₀ ≠ 0) ∧ (∀ z : ℂ, h z = 0 → z.im = 0) ∧
      (∀ z : ℂ, ‖h z‖ ≤ Real.exp CB * Real.exp (φ z - α * |z.im|)) ∧
      ∀ η : ℝ, 0 < η → ∀ z : ℂ, (∀ x : ℝ, h x = 0 → η * massRadiusLine μ x ≤ ‖z - x‖) →
        Real.exp (-CB * (1 + |Real.log (min η 1)|)) * Real.exp (φ z - α * |z.im|) ≤ ‖h z‖ := by
    intro s hs hs' h hzero hnorm
    obtain ⟨Hup, Hlow⟩ := HB α hα hαB' s hs (hs'.trans hs₀B)
    refine ⟨⟨I, fun hI ↦ ?_⟩, fun z hz ↦ im_eq_zero_of_mem_lineZeroSet ((hzero z).1 hz),
      fun z ↦ ?_, fun η hη z hz ↦ ?_⟩
    · have := im_eq_zero_of_mem_lineZeroSet ((hzero I).1 hI)
      simp at this
    · by_cases hz : z ∈ lineZeroSet μ α s
      · rw [(hzero z).2 hz, norm_zero]; positivity
      · rw [hnorm z hz, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith [Hup z hz])
    · set η' := min η 1
      have hη' : 0 < η' := lt_min hη one_pos
      have hz' : ∀ ν ∈ lineZeroSet μ α s, η' * massRadiusLine μ ν.re ≤ ‖z - ν‖ := by
        intro ν hν
        have hν' := eq_ofReal_re_of_mem_lineZeroSet hν
        have h0 : h (ν.re : ℂ) = 0 := (hzero _).2 (hν' ▸ hν)
        have := hz ν.re h0
        rw [← hν'] at this
        have hρ := (hμ.massRadiusLine_pos ν.re).le
        exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hρ) this
      have hzn : z ∉ lineZeroSet μ α s := by
        intro hzZ
        have := hz' z hzZ
        rw [sub_self, norm_zero] at this
        have := mul_pos hη' (hμ.massRadiusLine_pos z.re)
        linarith
      rw [hnorm z hzn, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith [Hlow η' hη' (min_le_right _ _) z hz'])
  obtain ⟨h0, hd0, hz0, hn0⟩ := hW 0 le_rfl hs₀.le
  obtain ⟨h1, hd1, hz1, hn1⟩ := hW s₀ hs₀.le le_rfl
  obtain ⟨p0a, p0b, p0c, p0d⟩ := props 0 le_rfl hs₀.le h0 hz0 hn0
  obtain ⟨p1a, p1b, p1c, p1d⟩ := props s₀ hs₀.le le_rfl h1 hz1 hn1
  refine ⟨![h0, h1], s₀ / 4, Real.exp CB, by positivity, Real.exp_pos _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simpa
  · intro i; fin_cases i <;> simpa
  · intro i; fin_cases i <;> simpa
  · intro i; fin_cases i <;> simpa
  · -- the cover property
    intro z
    by_cases H : ∀ x : ℝ, h0 x = 0 → s₀ / 4 * massRadiusLine μ x ≤ ‖z - x‖
    · exact ⟨0, by simpa using H⟩
    · push Not at H
      obtain ⟨x₀, hx₀, hzx₀⟩ := H
      refine ⟨1, fun x hx ↦ ?_⟩
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hx
      obtain ⟨k, b, rfl⟩ := ofReal_mem_lineZeroSet.1 ((hz1 _).1 hx)
      obtain ⟨j, b', hj⟩ := ofReal_mem_lineZeroSet.1 ((hz0 _).1 hx₀)
      have hj' : x₀ = lineCentre μ α j := by rw [hj, lineNode_zero]
      have hne : lineNode μ α s₀ k b ≠ x₀ := by
        rw [hj']; exact hc.node_ne_centre hα hα₁' hs₀ hs₀c k j b
      have hsep := HS α hα hαS' s₀ hs₀ hs₀S (lineNode μ α s₀ k b) (Or.inr ⟨(k, b), rfl⟩) x₀
        (Or.inl ⟨(j, b'), hj.symm⟩) hne
      have htri : |lineNode μ α s₀ k b - x₀| ≤ ‖z - lineNode μ α s₀ k b‖ + ‖z - x₀‖ := by
        rw [← norm_ofReal_sub_ofReal]
        calc ‖((lineNode μ α s₀ k b : ℝ) : ℂ) - x₀‖ ≤
            ‖((lineNode μ α s₀ k b : ℝ) : ℂ) - z‖ + ‖z - x₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ = _ := by rw [norm_sub_rev]
      have hρ0 := (hμ.massRadiusLine_pos x₀).le
      have hρ1 := (hμ.massRadiusLine_pos (lineNode μ α s₀ k b)).le
      nlinarith
  · intro η hη
    refine ⟨Real.exp (-CB * (1 + |Real.log (min η 1)|)), Real.exp_pos _, fun i z hz ↦ ?_⟩
    fin_cases i
    · exact p0d η hη z (by simpa using hz)
    · exact p1d η hη z (by simpa using hz)

/-- **Theorem 5** (statement verbatim from `comparator/statements.lean`). -/
theorem theorem5 (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoublingLine μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z₀, f z₀ ≠ 0) ∧ (∀ z, f z = 0 → z.im = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
        (∀ x : ℝ, f x = 0 → ε * massRadiusLine μ x ≤ ‖z - x‖) →
          C⁻¹ * Real.exp (φ z) ≤ ‖f z‖ ∧ ‖f z‖ ≤ C * Real.exp (φ z) := by
  obtain ⟨α₀, hα₀, H⟩ := lineMultipliers φ μ hφ hd hm
  obtain ⟨f, ε₀, C, hε₀, hC, hdiff, hne, hreal, hup, -, hlow⟩ := H 0 le_rfl hα₀.le
  refine ⟨f 0, hdiff 0, hne 0, hreal 0, fun ε hε ↦ ?_⟩
  obtain ⟨c, hc, hlow'⟩ := hlow ε hε
  refine ⟨max C c⁻¹, lt_max_of_lt_left hC, fun z hz ↦ ⟨?_, ?_⟩⟩
  · have h1 := hlow' 0 z hz
    simp only [zero_mul, sub_zero] at h1
    calc (max C c⁻¹)⁻¹ * Real.exp (φ z) ≤ c * Real.exp (φ z) := by
          gcongr
          rw [inv_le_comm₀ (lt_max_of_lt_left hC) hc]
          exact le_max_right _ _
      _ ≤ ‖f 0 z‖ := h1
  · have h2 := hup 0 z
    simp only [zero_mul, sub_zero] at h2
    calc ‖f 0 z‖ ≤ C * Real.exp (φ z) := h2
      _ ≤ max C c⁻¹ * Real.exp (φ z) := by gcongr; exact le_max_left _ _

end OC
