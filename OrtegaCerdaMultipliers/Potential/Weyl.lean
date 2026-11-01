import OrtegaCerdaMultipliers.Potential.Radial
import OrtegaCerdaMultipliers.Potential.Fundamental

/-!
# M02 (Potentials) §2–§3 — Weyl's lemma for `Δ`; weights up to harmonic functions

See `blueprint/M02_Potentials.md` §2–§3.  All statements are proved.

The `bumpKernel` API (stated in the doc's §4.1) is placed here, next to the definition, because
the proof of Weyl's lemma uses it.  The a.e. (`L¹_loc`) form of Weyl's lemma,
`exists_harmonicOnNhd_ae_eq_of_weakHarmonic`, is added for M07's `WeylLaplacianStmt`
(consumed by M08 and M13 through `LogModulusWeak.lean`).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Smooth radial probability density supported in `ball 0 s` (BOC `kernel` with
`a = s²/4`, `b = s²`). -/
def bumpKernel (s : ℝ) (x : ℂ) : ℝ := kernel (s ^ 2 / 4) (s ^ 2) x

/-! ### `bumpKernel` API (doc §4.1) -/

theorem contDiff_bumpKernel {s : ℝ} (hs : 0 < s) : ContDiff ℝ (⊤ : ℕ∞) (bumpKernel s) :=
  contDiff_kernel (bump_pos hs) (bump_lt hs)

theorem bumpKernel_nonneg {s : ℝ} (hs : 0 < s) (x : ℂ) : 0 ≤ bumpKernel s x :=
  kernel_nonneg (bump_pos hs) (bump_lt hs) x

theorem bumpKernel_eq_zero {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : s ≤ ‖x‖) :
    bumpKernel s x = 0 :=
  kernel_bump_eq_zero hs hx

theorem integral_bumpKernel {s : ℝ} (hs : 0 < s) : ∫ x, bumpKernel s x = 1 :=
  integral_kernel (bump_pos hs) (bump_lt hs)

theorem bumpKernel_le {s : ℝ} (hs : 0 < s) (x : ℂ) :
    bumpKernel s x ≤ 4 / (Real.pi * s ^ 2) * (ball (0 : ℂ) s).indicator 1 x := by
  have h := kernel_le_indicator (bump_pos hs) (bump_lt hs) x
  rw [Real.sqrt_sq hs.le] at h
  have e : (Real.pi * (s ^ 2 / 4))⁻¹ = 4 / (Real.pi * s ^ 2) := by field_simp
  rw [e] at h
  exact h

theorem le_bumpKernel {s : ℝ} (hs : 0 < s) (x : ℂ) :
    1 / (Real.pi * s ^ 2) * (ball (0 : ℂ) (s / 2)).indicator 1 x ≤ bumpKernel s x := by
  have h := indicator_le_kernel (bump_pos hs) (bump_lt hs) x
  have e : Real.sqrt (s ^ 2 / 4) = s / 2 := by
    rw [show s ^ 2 / 4 = (s / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [e, ← one_div] at h
  exact h

/-- `profMass (s²/4) s² = s² · profMass (1/4) 1` for every `s` (both sides vanish at `0`). -/
theorem profMass_bump (s : ℝ) :
    profMass (s ^ 2 / 4) (s ^ 2) = s ^ 2 * profMass (1 / 4) 1 := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [profMass]
  · have h := profMass_scale (a := 1 / 4) (b := 1) (by norm_num) (abs_pos.2 hs)
    rw [sq_abs] at h
    rw [show s ^ 2 / 4 = s ^ 2 * (1 / 4) by ring, ← h, mul_one]

theorem measurable_bumpKernel : Measurable (Function.uncurry bumpKernel) := by
  have h : Function.uncurry bumpKernel = fun p : ℝ × ℂ ↦
      (1 - Real.smoothTransition ((‖p.2‖ ^ 2 - p.1 ^ 2 / 4) / (p.1 ^ 2 - p.1 ^ 2 / 4))) /
        (p.1 ^ 2 * profMass (1 / 4) 1) / Real.pi := by
    ext p
    simp only [Function.uncurry, bumpKernel, kernel_eq, cutProfile, profMass_bump]
  rw [h]
  have hst : Measurable Real.smoothTransition := Real.smoothTransition.continuous.measurable
  fun_prop

/-- Radial symmetry: `bumpKernel s (w - y) = bumpKernel s (y - w)`. -/
theorem bumpKernel_sub_comm (s : ℝ) (w y : ℂ) : bumpKernel s (w - y) = bumpKernel s (y - w) := by
  simp only [bumpKernel, kernel_eq, norm_sub_rev]

/-! ### Weyl's lemma -/

/-! #### The two-radii test function -/

/-- `Δ (S_s(‖· − y‖²)) = −4π k_s(· − y)`. -/
theorem laplacian_sFun_normSq_sub {s : ℝ} (hs : 0 < s) (y w : ℂ) :
    Laplacian.laplacian (fun w : ℂ ↦ sFun (s ^ 2 / 4) (s ^ 2) (‖w - y‖ ^ 2)) w =
      -(4 * Real.pi) * bumpKernel s (w - y) := by
  rw [laplacian_eq_four_mul_lap,
    lap_comp_sub (fun w : ℂ ↦ sFun (s ^ 2 / 4) (s ^ 2) (‖w‖ ^ 2)) y w,
    lap_sFun_normSq (bump_pos hs) (bump_lt hs)]
  simp only [bumpKernel]
  ring

theorem contDiff_sFun_normSq_sub {s : ℝ} (hs : 0 < s) (y : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ ↦ sFun (s ^ 2 / 4) (s ^ 2) (‖w - y‖ ^ 2)) :=
  (contDiff_sFun (bump_pos hs) (bump_lt hs)).comp
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

/-- The test function `S_{s₂}(‖w − y‖²) − S_{s₁}(‖w − y‖²)`, smooth, supported in
`closedBall y s₂`, with Laplacian `4π (k_{s₁} − k_{s₂})(· − y)`. -/
def twoRadiiTest (s₁ s₂ : ℝ) (y w : ℂ) : ℝ :=
  sFun (s₂ ^ 2 / 4) (s₂ ^ 2) (‖w - y‖ ^ 2) - sFun (s₁ ^ 2 / 4) (s₁ ^ 2) (‖w - y‖ ^ 2)

section twoRadii

variable {s₁ s₂ : ℝ} {y : ℂ}

theorem contDiff_twoRadiiTest (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    ContDiff ℝ (⊤ : ℕ∞) (twoRadiiTest s₁ s₂ y) :=
  (contDiff_sFun_normSq_sub hs₂ y).sub (contDiff_sFun_normSq_sub hs₁ y)

theorem twoRadiiTest_eq_zero (hs₁ : 0 < s₁) (h12 : s₁ ≤ s₂) {w : ℂ} (hw : s₂ ≤ ‖w - y‖) :
    twoRadiiTest s₁ s₂ y w = 0 := by
  have hs₂ : 0 < s₂ := hs₁.trans_le h12
  have h2 : s₂ ^ 2 ≤ ‖w - y‖ ^ 2 := pow_le_pow_left₀ hs₂.le hw 2
  have h1 : s₁ ^ 2 ≤ ‖w - y‖ ^ 2 := (pow_le_pow_left₀ hs₁.le h12 2).trans h2
  unfold twoRadiiTest
  rw [sFun_of_ge (bump_pos hs₂) (bump_lt hs₂) h2, sFun_of_ge (bump_pos hs₁) (bump_lt hs₁) h1,
    sub_self]

theorem tsupport_twoRadiiTest_subset (hs₁ : 0 < s₁) (h12 : s₁ ≤ s₂) :
    tsupport (twoRadiiTest s₁ s₂ y) ⊆ closedBall y s₂ := by
  refine closure_minimal (fun w hw ↦ ?_) isClosed_closedBall
  by_contra hcon
  rw [mem_closedBall, dist_eq_norm, not_le] at hcon
  exact hw (twoRadiiTest_eq_zero hs₁ h12 hcon.le)

theorem hasCompactSupport_twoRadiiTest (hs₁ : 0 < s₁) (h12 : s₁ ≤ s₂) :
    HasCompactSupport (twoRadiiTest s₁ s₂ y) :=
  (isCompact_closedBall y s₂).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_twoRadiiTest_subset hs₁ h12)

theorem laplacian_twoRadiiTest (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (w : ℂ) :
    Laplacian.laplacian (twoRadiiTest s₁ s₂ y) w =
      4 * Real.pi * (bumpKernel s₁ (w - y) - bumpKernel s₂ (w - y)) := by
  have e : twoRadiiTest s₁ s₂ y = (fun w : ℂ ↦ sFun (s₂ ^ 2 / 4) (s₂ ^ 2) (‖w - y‖ ^ 2)) -
      (fun w : ℂ ↦ sFun (s₁ ^ 2 / 4) (s₁ ^ 2) (‖w - y‖ ^ 2)) := rfl
  rw [e, ((contDiff_sFun_normSq_sub hs₂ y).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt.laplacian_sub
    ((contDiff_sFun_normSq_sub hs₁ y).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt,
    laplacian_sFun_normSq_sub hs₂, laplacian_sFun_normSq_sub hs₁]
  ring

end twoRadii

/-- **Two radii give the same average** (Weyl, Step 1), for a locally integrable weakly
harmonic function. -/
theorem integral_bumpKernel_mul_eq_of_weakHarmonic {U : Set ℂ} {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0)
    {y : ℂ} {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (h12 : s₁ < s₂) (hsub : closedBall y s₂ ⊆ U) :
    ∫ w, bumpKernel s₁ (w - y) * f w = ∫ w, bumpKernel s₂ (w - y) * f w := by
  have hs₂ : 0 < s₂ := hs₁.trans h12
  have hfi : IntegrableOn f (closedBall y s₂) :=
    hf.integrableOn_compact_subset hsub (isCompact_closedBall y s₂)
  have i1 : Integrable (fun w ↦ bumpKernel s₁ (w - y) * f w) :=
    integrable_kernel_bump_mul hs₁ h12.le hfi
  have i2 : Integrable (fun w ↦ bumpKernel s₂ (w - y) * f w) :=
    integrable_kernel_bump_mul hs₂ le_rfl hfi
  have hχ := h (twoRadiiTest s₁ s₂ y) (contDiff_twoRadiiTest hs₁ hs₂)
    (hasCompactSupport_twoRadiiTest hs₁ h12.le)
    ((tsupport_twoRadiiTest_subset hs₁ h12.le).trans hsub)
  simp_rw [laplacian_twoRadiiTest hs₁ hs₂] at hχ
  have e : ∫ z, f z * (4 * Real.pi * (bumpKernel s₁ (z - y) - bumpKernel s₂ (z - y))) =
      4 * Real.pi * ((∫ w, bumpKernel s₁ (w - y) * f w) - ∫ w, bumpKernel s₂ (w - y) * f w) := by
    rw [← integral_sub i1 i2, ← integral_const_mul]
    congr 1; ext z; ring
  rw [e] at hχ
  have hπ : 4 * Real.pi ≠ 0 := by positivity
  have := (mul_eq_zero.1 hχ).resolve_left hπ
  linarith

/-- Two admissible radii (in any order) give the same average. -/
theorem integral_bumpKernel_mul_eq_of_weakHarmonic' {U : Set ℂ} {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0)
    {y : ℂ} {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (h1 : closedBall y s₁ ⊆ U)
    (h2 : closedBall y s₂ ⊆ U) :
    ∫ w, bumpKernel s₁ (w - y) * f w = ∫ w, bumpKernel s₂ (w - y) * f w := by
  rcases lt_trichotomy s₁ s₂ with h12 | rfl | h12
  · exact integral_bumpKernel_mul_eq_of_weakHarmonic hf h hs₁ h12 h2
  · rfl
  · exact (integral_bumpKernel_mul_eq_of_weakHarmonic hf h hs₂ h12 h1).symm

/-- **Lebesgue points.** For a locally integrable `g`, `∫ k_s(w − x) g(w) dw → g(x)` for a.e. `x`. -/
theorem ae_tendsto_integral_bumpKernel_mul {g : ℂ → ℝ} (hg : LocallyIntegrable g) :
    ∀ᵐ x₀, Tendsto (fun s ↦ ∫ w, bumpKernel s (w - x₀) * g w) (𝓝[>] 0) (𝓝 (g x₀)) := by
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure ℂ)).ae_tendsto_average_norm_sub hg]
    with x₀ h₀
  have hlim := h₀.comp (Besicovitch.tendsto_filterAt volume x₀)
  have := tendsto_integral_smul_of_tendsto_average_norm_sub (μ := volume)
    (a := fun s ↦ closedBall x₀ s) (g := fun s w ↦ bumpKernel s (w - x₀)) (f := g) 4 hlim
    (Eventually.of_forall fun s ↦ hg.integrableOn_isCompact (isCompact_closedBall _ _)) ?_ ?_ ?_
  · simpa [smul_eq_mul] using this
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (integral_kernel_bump_sub hs x₀).symm
  · filter_upwards [self_mem_nhdsWithin] with s hs
    intro w hw
    by_contra hcon
    rw [mem_closedBall, dist_eq_norm, not_le] at hcon
    exact hw (bumpKernel_eq_zero hs hcon.le)
  · filter_upwards [self_mem_nhdsWithin] with s hs w
    have hs' : (0 : ℝ) < s := hs
    rw [abs_of_nonneg (bumpKernel_nonneg hs' _), Measure.real, Complex.volume_closedBall,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs'.le, ENNReal.coe_toReal,
      NNReal.coe_real_pi]
    refine (bumpKernel_le hs' (w - x₀)).trans ?_
    have hind : (ball (0 : ℂ) s).indicator (1 : ℂ → ℝ) (w - x₀) ≤ 1 :=
      indicator_le_self' (fun _ _ ↦ zero_le_one) _ |>.trans (le_refl _)
    calc 4 / (Real.pi * s ^ 2) * (ball (0 : ℂ) s).indicator 1 (w - x₀)
        ≤ 4 / (Real.pi * s ^ 2) * 1 := by gcongr
      _ = 4 / (s ^ 2 * Real.pi) := by ring

/-- **Mean-value form of Weyl.** A continuous weakly harmonic function equals its
`bumpKernel`-averages. -/
theorem eq_integral_bumpKernel_of_weakHarmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Ω)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ z, φ z * Laplacian.laplacian χ z = 0)
    {z : ℂ} {s : ℝ} (hs : 0 < s) (hzs : closedBall z s ⊆ Ω) :
    φ z = ∫ w, bumpKernel s (w - z) * φ w := by
  have hz : z ∈ Ω := hzs (mem_closedBall_self hs.le)
  have hfi : LocallyIntegrableOn φ Ω := hφ.locallyIntegrableOn hΩ.measurableSet
  have hlim := tendsto_integral_kernel_bump_mul hs
    ((hφ.mono hzs).integrableOn_compact (isCompact_closedBall z s))
    (hφ.continuousAt (hΩ.mem_nhds hz))
  have hev : (fun s₁ ↦ ∫ w, kernel (s₁ ^ 2 / 4) (s₁ ^ 2) (w - z) * φ w) =ᶠ[𝓝[>] 0]
      fun _ ↦ ∫ w, bumpKernel s (w - z) * φ w := by
    filter_upwards [Ioo_mem_nhdsGT hs] with s₁ hs₁
    exact integral_bumpKernel_mul_eq_of_weakHarmonic hfi h hs₁.1 hs₁.2 hzs
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)

theorem hasCompactSupport_bumpKernel {s : ℝ} (hs : 0 < s) : HasCompactSupport (bumpKernel s) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) s) fun x hx ↦ ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hx
  exact bumpKernel_eq_zero hs hx.le

/-- `∫ k_s(w − y) g(w) dw` only sees `g` on `closedBall y s`. -/
theorem integral_bumpKernel_mul_indicator {s : ℝ} (hs : 0 < s) {g : ℂ → ℝ} {y : ℂ} {K : Set ℂ}
    (hK : closedBall y s ⊆ K) :
    ∫ w, bumpKernel s (w - y) * K.indicator g w = ∫ w, bumpKernel s (w - y) * g w := by
  congr 1; ext w
  by_cases hw : w ∈ closedBall y s
  · rw [indicator_of_mem (hK hw)]
  · rw [mem_closedBall, dist_eq_norm, not_le] at hw
    rw [bumpKernel_eq_zero hs hw.le, zero_mul, zero_mul]

/-- **Local smooth representative** (Weyl, Steps 3–5, `L¹_loc` form): on `ball z₀ R`, the average
`F(y) = ∫ k_R(w − y) f(w) dw` is harmonic and equals `f` a.e. -/
theorem harmonicAt_and_ae_eq_integral_bumpKernel {U : Set ℂ} {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0)
    {z₀ : ℂ} {R : ℝ} (hR : 0 < R) (hsub : closedBall z₀ (2 * R) ⊆ U) :
    (∀ y ∈ ball z₀ R,
        InnerProductSpace.HarmonicAt (fun y ↦ ∫ w, bumpKernel R (w - y) * f w) y) ∧
      ∀ᵐ y, y ∈ ball z₀ R → f y = ∫ w, bumpKernel R (w - y) * f w := by
  set K := closedBall z₀ (2 * R)
  set F : ℂ → ℝ := fun y ↦ ∫ w, bumpKernel R (w - y) * f w with hF
  have hfK : IntegrableOn f K := hf.integrableOn_compact_subset hsub (isCompact_closedBall _ _)
  set f' : ℂ → ℝ := K.indicator f
  have hf'i : Integrable f' := (integrable_indicator_iff measurableSet_closedBall).2 hfK
  have hf'l : LocallyIntegrable f' := hf'i.locallyIntegrable
  set G : ℂ → ℝ := fun y ↦ ∫ w, bumpKernel R (w - y) * f' w with hG
  -- `closedBall y R ⊆ K` near `z₀`
  have hballK : ∀ y ∈ ball z₀ R, ∀ s ≤ R, closedBall y s ⊆ K := by
    intro y hy s hs w hw
    rw [mem_closedBall] at hw ⊢
    rw [mem_ball] at hy
    calc dist w z₀ ≤ dist w y + dist y z₀ := dist_triangle _ _ _
      _ ≤ 2 * R := by linarith
  have hFG : ∀ y ∈ ball z₀ R, F y = G y := fun y hy ↦
    (integral_bumpKernel_mul_indicator hR (hballK y hy R le_rfl)).symm
  -- `G` is smooth
  have hGconv : G = convolution f' (bumpKernel R) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y
    show (∫ w, bumpKernel R (w - y) * f' w) = _
    rw [convolution_def]
    congr 1; funext w
    rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul, bumpKernel_sub_comm, mul_comm]
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [hGconv]
    exact (hasCompactSupport_bumpKernel hR).contDiff_convolution_right _ hf'l
      (contDiff_bumpKernel hR)
  have hG2 : ContDiff ℝ 2 G := hGs.of_le (WithTop.coe_le_coe.2 le_top)
  -- `f = G` a.e. on the ball
  have hae : ∀ᵐ y, y ∈ ball z₀ R → f y = G y := by
    filter_upwards [ae_tendsto_integral_bumpKernel_mul hf'l] with y hy hyb
    have hyK : y ∈ K := hballK y hyb R le_rfl (mem_closedBall_self hR.le)
    have hev : (fun s ↦ ∫ w, bumpKernel s (w - y) * f' w) =ᶠ[𝓝[>] 0] fun _ ↦ G y := by
      filter_upwards [Ioo_mem_nhdsGT hR] with s hs
      rw [integral_bumpKernel_mul_indicator hs.1 (hballK y hyb s hs.2.le),
        integral_bumpKernel_mul_eq_of_weakHarmonic hf h hs.1 hs.2
          ((hballK y hyb R le_rfl).trans hsub), ← hFG y hyb]
    have h1 := tendsto_nhds_unique hy (tendsto_const_nhds.congr' hev.symm)
    rwa [show f' y = f y from indicator_of_mem hyK f] at h1
  -- `ΔG = 0` on the ball
  have hΔc : Continuous (Laplacian.laplacian G) := continuous_laplacian hG2
  have hΔae : ∀ᵐ x, x ∈ ball z₀ R → Laplacian.laplacian G x = 0 := by
    refine isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hΔc.locallyIntegrable.locallyIntegrableOn _) fun β hβ hβc hβs ↦ ?_
    have hβ2 : ContDiff ℝ 2 β := hβ.of_le (WithTop.coe_le_coe.2 le_top)
    have h1 := integral_mul_lap hβ2 hβc hG2
    have h2 : ∫ x, β x • Laplacian.laplacian G x = ∫ x, G x * Laplacian.laplacian β x := by
      simp_rw [smul_eq_mul, laplacian_eq_four_mul_lap]
      calc ∫ x, β x * (4 * lap G x) = 4 * ∫ x, β x * lap G x := by
            rw [← integral_const_mul]; congr 1; ext x; ring
        _ = 4 * ∫ x, lap β x * G x := by rw [h1]
        _ = ∫ x, G x * (4 * lap β x) := by
            rw [← integral_const_mul]; congr 1; ext x; ring
    have h3 : (fun x ↦ G x * Laplacian.laplacian β x) =ᵐ[volume]
        fun x ↦ f x * Laplacian.laplacian β x := by
      filter_upwards [hae] with x hx
      by_cases hxb : x ∈ ball z₀ R
      · rw [hx hxb]
      · have : Laplacian.laplacian β x = 0 :=
          laplacian_eq_zero_of_notMem_tsupport fun h' ↦ hxb (hβs h')
        rw [this, mul_zero, mul_zero]
    rw [h2, integral_congr_ae h3]
    exact h β hβ hβc (hβs.trans (ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith)).trans hsub)))
  have hΔ0 : ∀ x ∈ ball z₀ R, Laplacian.laplacian G x = 0 := by
    have h' : Laplacian.laplacian G =ᵐ[volume.restrict (ball z₀ R)] fun _ ↦ 0 := by
      rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
      exact hΔae
    exact Measure.eqOn_open_of_ae_eq h' isOpen_ball hΔc.continuousOn continuousOn_const
  refine ⟨fun y hy ↦ ?_, ?_⟩
  · have hFG' : F =ᶠ[𝓝 y] G := by
      filter_upwards [isOpen_ball.mem_nhds hy] with x hx using hFG x hx
    refine (InnerProductSpace.harmonicAt_congr_nhds hFG').2 ⟨hG2.contDiffAt, ?_⟩
    filter_upwards [isOpen_ball.mem_nhds hy] with x hx using hΔ0 x hx
  · filter_upwards [hae] with y hy hyb
    rw [hy hyb]
    exact (hFG y hyb).symm

/-- The `L¹_loc` Weyl lemma (proof of `exists_harmonicOnNhd_ae_eq_of_weakHarmonic`): glue the
local representatives `∫ k_r(w − y) f(w) dw`, which do not depend on the admissible radius. -/
theorem exists_harmonicOnNhd_ae_eq_of_weakHarmonic_aux {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0) :
    ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u U ∧ ∀ᵐ z ∂(volume.restrict U), f z = u z := by
  have hrad : ∀ y ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall y r ⊆ U := fun y hy ↦ by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU y hy
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  choose! r hr hrU using hrad
  set u : ℂ → ℝ := fun y ↦ ∫ w, bumpKernel (r y) (w - y) * f w with hu
  have hsub2 : ∀ z₀ ∈ U, closedBall z₀ (2 * (r z₀ / 2)) ⊆ U := fun z₀ hz₀ ↦ by
    rw [mul_div_cancel₀ _ two_ne_zero]; exact hrU z₀ hz₀
  have hloc : ∀ z₀ ∈ U, ∀ y ∈ ball z₀ (r z₀ / 2),
      u y = ∫ w, bumpKernel (r z₀ / 2) (w - y) * f w := by
    intro z₀ hz₀ y hy
    have hyz : closedBall y (r z₀ / 2) ⊆ closedBall z₀ (r z₀) := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      rw [mem_ball] at hy
      calc dist w z₀ ≤ dist w y + dist y z₀ := dist_triangle _ _ _
        _ ≤ r z₀ := by linarith
    have hyU : y ∈ U := hrU z₀ hz₀ (hyz (mem_closedBall_self (half_pos (hr z₀ hz₀)).le))
    exact integral_bumpKernel_mul_eq_of_weakHarmonic' hf h (hr y hyU) (half_pos (hr z₀ hz₀))
      (hrU y hyU) (hyz.trans (hrU z₀ hz₀))
  refine ⟨u, fun z₀ hz₀ ↦ ?_, ?_⟩
  · obtain ⟨hharm, -⟩ :=
      harmonicAt_and_ae_eq_integral_bumpKernel hf h (half_pos (hr z₀ hz₀)) (hsub2 z₀ hz₀)
    have hev : u =ᶠ[𝓝 z₀] fun y ↦ ∫ w, bumpKernel (r z₀ / 2) (w - y) * f w := by
      filter_upwards [ball_mem_nhds z₀ (half_pos (hr z₀ hz₀))] with y hy using hloc z₀ hz₀ y hy
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).2
      (hharm z₀ (mem_ball_self (half_pos (hr z₀ hz₀))))
  · have hnull : volume ({y | f y ≠ u y} ∩ U) = 0 := by
      apply measure_null_of_locally_null
      intro x hx
      obtain ⟨-, hae⟩ :=
        harmonicAt_and_ae_eq_integral_bumpKernel hf h (half_pos (hr x hx.2)) (hsub2 x hx.2)
      refine ⟨({y | f y ≠ u y} ∩ U) ∩ ball x (r x / 2),
        inter_mem_nhdsWithin _ (ball_mem_nhds x (half_pos (hr x hx.2))), ?_⟩
      apply measure_mono_null _ (ae_iff.1 hae)
      rintro y ⟨⟨hyne, -⟩, hyb⟩
      simp only [mem_ofPred_eq, not_imp]
      refine ⟨hyb, fun hfy ↦ hyne ?_⟩
      rw [hfy, hloc x hx.2 y hyb]
    rw [ae_iff, Measure.restrict_apply' hU.measurableSet]
    simpa using hnull

/-- **Weyl's lemma for `Δ`.** A continuous weakly harmonic function is harmonic. -/
theorem harmonicOnNhd_of_weakHarmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Ω)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ z, φ z * Laplacian.laplacian χ z = 0) :
    InnerProductSpace.HarmonicOnNhd φ Ω := by
  obtain ⟨u, hu, hae⟩ := exists_harmonicOnNhd_ae_eq_of_weakHarmonic_aux hΩ
    (hφ.locallyIntegrableOn hΩ.measurableSet) h
  have heq : EqOn φ u Ω := Measure.eqOn_open_of_ae_eq hae hΩ hφ hu.contDiffOn.continuousOn
  intro z hz
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 (hu z hz)
  filter_upwards [hΩ.mem_nhds hz] with y hy using heq hy

/-- **Weyl's lemma for `Δ`, `L¹_loc` form** (the body of M07's `WeylLaplacianStmt`): a locally
integrable weakly harmonic function is a.e. equal to a harmonic function.  (Mollify:
`φ * bumpKernel s` is smooth and weakly, hence classically, harmonic, and equals its own
`bumpKernel`-averages; let `s → 0`.) -/
theorem exists_harmonicOnNhd_ae_eq_of_weakHarmonic {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0) :
    ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u U ∧ ∀ᵐ z ∂(volume.restrict U), f z = u z :=
  exists_harmonicOnNhd_ae_eq_of_weakHarmonic_aux hU hf h

/-! ### Weights up to harmonic functions; calculus of weights (§3) -/

theorem IsSubharmonicWeight.integrable_mul {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) {f : ℂ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    Integrable (fun z ↦ φ z * f z) :=
  integrable_mul_of_tsupport_subset_real hΩ h.continuousOn hf hc hs

theorem IsSubharmonicWeight.sigmaFinite {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) : SigmaFinite μ := by
  have hrad : ∀ z ∈ Ω, ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ Ω := fun z hz ↦ by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hΩ z hz
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  choose! r hr hrU using hrad
  obtain ⟨T, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun z : Ω ↦ ball (z : ℂ) (r z)) fun _ ↦ isOpen_ball
  refine Measure.sigmaFinite_of_countable
    (S := insert Ωᶜ ((fun z : Ω ↦ ball (z : ℂ) (r z)) '' T)) ((hTc.image _).insert _) ?_ ?_
  · rintro s (rfl | ⟨z, -, rfl⟩)
    · rw [h.carried]; exact ENNReal.zero_lt_top
    · exact (measure_mono ball_subset_closedBall).trans_lt
        (h.finite_of_compact _ (hrU z z.2) (isCompact_closedBall _ _))
  · rw [sUnion_insert, sUnion_image, hTU, eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ Ω
    · exact Or.inr (mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hr x hx)⟩)
    · exact Or.inl hx

/-- A continuous function with compact support is integrable for a measure that is finite on its
support. -/
theorem integrable_of_measure_tsupport_lt_top {ν : Measure ℂ} {χ : ℂ → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (hν : ν (tsupport χ) < ∞) : Integrable χ ν := by
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hc
  have hon : IntegrableOn χ (tsupport χ) ν :=
    Measure.integrableOn_of_bounded hν.ne hχ.aestronglyMeasurable
      (Eventually.of_forall fun z ↦ hC z)
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport χ)).1 hon

/-- **Uniqueness.** Two weights with the same Laplacian differ by a harmonic function. -/
theorem IsSubharmonicWeight.harmonicOnNhd_sub {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ₁ φ₂ : ℂ → ℝ}
    {μ : Measure ℂ} (h₁ : IsSubharmonicWeight Ω φ₁ μ) (h₂ : IsSubharmonicWeight Ω φ₂ μ) :
    InnerProductSpace.HarmonicOnNhd (fun z ↦ φ₁ z - φ₂ z) Ω := by
  refine harmonicOnNhd_of_weakHarmonic hΩ (h₁.continuousOn.sub h₂.continuousOn)
    fun χ hχ hc hs ↦ ?_
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (WithTop.coe_le_coe.2 le_top)
  have hΔc := continuous_laplacian hχ2
  have hΔs := hasCompactSupport_laplacian hc
  have hΔsub := (tsupport_laplacian_subset χ).trans hs
  simp_rw [sub_mul]
  rw [integral_sub (h₁.integrable_mul hΩ hΔc hΔs hΔsub) (h₂.integrable_mul hΩ hΔc hΔs hΔsub),
    h₁.laplacian_eq χ hχ hc hs, h₂.laplacian_eq χ hχ hc hs, sub_self]

theorem IsSubharmonicWeight.add_harmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ H : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) (hH : InnerProductSpace.HarmonicOnNhd H Ω) :
    IsSubharmonicWeight Ω (fun z ↦ φ z + H z) μ := by
  refine ⟨h.continuousOn.add hH.contDiffOn.continuousOn, h.finite_of_compact, h.carried,
    fun χ hχ hc hs ↦ ?_⟩
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (WithTop.coe_le_coe.2 le_top)
  have hΔc := continuous_laplacian hχ2
  have hΔs := hasCompactSupport_laplacian hc
  have hΔsub := (tsupport_laplacian_subset χ).trans hs
  simp_rw [add_mul]
  rw [integral_add (h.integrable_mul hΩ hΔc hΔs hΔsub)
    (integrable_mul_of_tsupport_subset_real hΩ hH.contDiffOn.continuousOn hΔc hΔs hΔsub),
    h.laplacian_eq χ hχ hc hs, integral_mul_laplacian_eq_zero_of_harmonicOnNhd hΩ hH hχ2 hc hs,
    add_zero]

theorem continuousOn_laplacian_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) : ContinuousOn (Laplacian.laplacian u) Ω :=
  (continuousOn_const.mul (continuousOn_lap hΩ hu)).congr fun z _ ↦
    laplacian_eq_four_mul_lap u z

theorem measurable_indicator_ofReal_laplacian {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) :
    Measurable (Ω.indicator fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z)) := by
  classical
  have e : (Ω.indicator fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z)) =
      Ω.piecewise (fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z)) (fun _ ↦ 0) := by
    ext z
    by_cases hz : z ∈ Ω <;> simp [hz]
  rw [e]
  exact ContinuousOn.measurable_piecewise
    (ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_laplacian_of_contDiffOn hΩ hu))
    continuousOn_const hΩ.measurableSet

/-- A `C²` function with `Δu ≥ 0` is a weight, with Laplacian `Δu dm` on `Ω`. -/
theorem isSubharmonicWeight_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) (hpos : ∀ z ∈ Ω, 0 ≤ Laplacian.laplacian u z) :
    IsSubharmonicWeight Ω u
      (volume.withDensity (Ω.indicator fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z))) := by
  set g : ℂ → ℝ≥0∞ := Ω.indicator fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z) with hg
  have hΔcont := continuousOn_laplacian_of_contDiffOn hΩ hu
  have hgm : Measurable g := measurable_indicator_ofReal_laplacian hΩ hu
  refine ⟨hu.continuousOn, fun K hKΩ hK ↦ ?_, ?_, fun χ hχ hc hs ↦ ?_⟩
  · rw [withDensity_apply _ hK.measurableSet]
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hΔcont.mono hKΩ)
    calc ∫⁻ x in K, g x ≤ ∫⁻ _ in K, ENNReal.ofReal C :=
          setLIntegral_mono measurable_const fun x hx ↦ by
            rw [hg, indicator_of_mem (hKΩ hx)]
            exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC x hx))
      _ = ENNReal.ofReal C * volume K := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  · rw [withDensity_apply _ hΩ.measurableSet.compl]
    have : ∫⁻ x in Ωᶜ, g x = ∫⁻ _ in Ωᶜ, 0 :=
      setLIntegral_congr_fun hΩ.measurableSet.compl fun x hx ↦ indicator_of_notMem hx _
    rw [this, lintegral_zero]
  · have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (WithTop.coe_le_coe.2 le_top)
    rw [integral_mul_laplacian_of_contDiffOn hΩ hu hχ2 hc hs,
      integral_withDensity_eq_integral_toReal_smul hgm
        (Eventually.of_forall fun z ↦ by
          rw [hg]
          by_cases hz : z ∈ Ω
          · rw [indicator_of_mem hz]; exact ENNReal.ofReal_lt_top
          · rw [indicator_of_notMem hz]; exact ENNReal.zero_lt_top)]
    congr 1; ext z
    rw [smul_eq_mul, hg]
    by_cases hz : z ∈ Ω
    · rw [indicator_of_mem hz, ENNReal.toReal_ofReal (hpos z hz)]
    · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport fun h' ↦ hz (hs h')]
      simp

/-- Subtracting a `C²` function whose Laplacian is dominated by the absolutely continuous part
of the Laplacian (used for `ψ + c log(1−|z|²)` in M11 and `ψ − c|z|²` in M12). -/
theorem IsSubharmonicWeight.sub_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {ψ u : ℂ → ℝ}
    {ν₀ : Measure ℂ} {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (h : IsSubharmonicWeight Ω ψ (ν₀ + volume.withDensity g)) (hu : ContDiffOn ℝ 2 u Ω)
    (hΔ : ∀ z ∈ Ω, 0 ≤ Laplacian.laplacian u z ∧
      ENNReal.ofReal (Laplacian.laplacian u z) ≤ g z) :
    IsSubharmonicWeight Ω (fun z ↦ ψ z - u z)
      (ν₀ + volume.withDensity
        (fun z ↦ g z - Ω.indicator (fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z)) z)) := by
  set a : ℂ → ℝ≥0∞ := Ω.indicator fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z) with ha
  set g' : ℂ → ℝ≥0∞ := fun z ↦ g z - a z with hg'
  have ham : Measurable a := measurable_indicator_ofReal_laplacian hΩ hu
  have hg'm : Measurable g' := hg.sub ham
  have hmono : ν₀ + volume.withDensity g' ≤ ν₀ + volume.withDensity g :=
    add_le_add_right (withDensity_mono (Eventually.of_forall fun z ↦ tsub_le_self)) _
  have hΔcont := continuousOn_laplacian_of_contDiffOn hΩ hu
  refine ⟨h.continuousOn.sub hu.continuousOn,
    fun K hKΩ hK ↦ ((Measure.le_iff'.1 hmono K).trans_lt (h.finite_of_compact K hKΩ hK)),
    nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hmono _).trans h.carried.le),
    fun χ hχ hc hs ↦ ?_⟩
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (WithTop.coe_le_coe.2 le_top)
  have hχc := hχ2.continuous
  have hΔc := continuous_laplacian hχ2
  have hΔs := hasCompactSupport_laplacian hc
  have hΔsub := (tsupport_laplacian_subset χ).trans hs
  set K := tsupport χ
  have hKm : MeasurableSet K := (isClosed_tsupport χ).measurableSet
  have hfin : (ν₀ + volume.withDensity g) K < ∞ := h.finite_of_compact K hs hc
  have hfin' : (ν₀ + volume.withDensity g') K < ∞ := (Measure.le_iff'.1 hmono K).trans_lt hfin
  have hi : Integrable χ (ν₀ + volume.withDensity g) :=
    integrable_of_measure_tsupport_lt_top hχc hc hfin
  have hi' : Integrable χ (ν₀ + volume.withDensity g') :=
    integrable_of_measure_tsupport_lt_top hχc hc hfin'
  -- the lower integrals of `g`, `g'` on `K` are finite
  have hgK : ∫⁻ x in K, g x ≠ ∞ := by
    rw [← withDensity_apply _ hKm]
    exact ((Measure.le_iff'.1 (Measure.le_add_left le_rfl) K).trans_lt hfin).ne
  have hg'K : ∫⁻ x in K, g' x ≠ ∞ :=
    ne_top_of_le_ne_top hgK (lintegral_mono fun x ↦ tsub_le_self)
  have hglt : ∀ᵐ x ∂volume.restrict K, g x < ∞ := ae_lt_top hg hgK
  have hg'lt : ∀ᵐ x ∂volume.restrict K, g' x < ∞ := ae_lt_top hg'm hg'K
  -- `∫ χ d(withDensity f) = ∫_K f.toReal χ`
  have hwd : ∀ f : ℂ → ℝ≥0∞, Measurable f → (∀ᵐ x ∂volume.restrict K, f x < ∞) →
      ∫ x, χ x ∂(volume.withDensity f) = ∫ x in K, (f x).toReal * χ x := by
    intro f hf hflt
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ image_eq_zero_of_notMem_tsupport hx), restrict_withDensity hKm,
      integral_withDensity_eq_integral_toReal_smul hf hflt]
    rfl
  have hχb := hχc.bounded_above_of_compact_support hc
  obtain ⟨C, hC⟩ := hχb
  have hint_f : ∀ f : ℂ → ℝ≥0∞, Measurable f → ∫⁻ x in K, f x ≠ ∞ →
      Integrable (fun x ↦ (f x).toReal * χ x) (volume.restrict K) := by
    intro f hf hfK
    have := (integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfK).bdd_mul
      hχc.aestronglyMeasurable (c := C) (Eventually.of_forall fun x ↦ hC x)
    simpa [mul_comm] using this
  have hint_Δ : Integrable (fun x ↦ Laplacian.laplacian u x * χ x) (volume.restrict K) :=
    ((hΔcont.mono hs).mul hχc.continuousOn).integrableOn_compact hc
  -- assemble
  have hsplit : ∫ z, (ψ z - u z) * Laplacian.laplacian χ z =
      (∫ z, ψ z * Laplacian.laplacian χ z) - ∫ z, u z * Laplacian.laplacian χ z := by
    simp_rw [sub_mul]
    exact integral_sub (h.integrable_mul hΩ hΔc hΔs hΔsub)
      (integrable_mul_of_tsupport_subset_real hΩ hu.continuousOn hΔc hΔs hΔsub)
  have hu' : ∫ z, u z * Laplacian.laplacian χ z = ∫ x in K, Laplacian.laplacian u x * χ x := by
    rw [integral_mul_laplacian_of_contDiffOn hΩ hu hχ2 hc hs,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  rw [hsplit, h.laplacian_eq χ hχ hc hs, hu',
    integral_add_measure (hi.mono_measure (Measure.le_add_right le_rfl))
      (hi.mono_measure (Measure.le_add_left le_rfl)),
    integral_add_measure (hi'.mono_measure (Measure.le_add_right le_rfl))
      (hi'.mono_measure (Measure.le_add_left le_rfl)),
    hwd g hg hglt, hwd g' hg'm hg'lt, add_sub_assoc,
    ← integral_sub (hint_f g hg hgK) hint_Δ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hglt, ae_restrict_mem hKm] with x hx hxK
  have hxΩ : x ∈ Ω := hs hxK
  have hle : a x ≤ g x := by
    rw [ha, indicator_of_mem hxΩ]; exact (hΔ x hxΩ).2
  rw [hg', ENNReal.toReal_sub_of_le hle hx.ne, ha, indicator_of_mem hxΩ,
    ENNReal.toReal_ofReal (hΔ x hxΩ).1]
  ring

end OC
