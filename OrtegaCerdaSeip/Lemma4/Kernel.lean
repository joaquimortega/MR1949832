import OrtegaCerdaSeip.Carleson.Poisson
import OrtegaCerdaSeip.Foundations.HoloKernel
import OrtegaCerdaSeip.Foundations.Weyl

/-!
# M05 (Lemma 4) — the kernel `sin ε w / (π ε w²)` and the operator `u = k * (θ ν)`

See `blueprint/M05_Lemma4.md` (§1.1–§1.2).

`k(w) = sin(εw)/(π ε w²) = (1/(πw)) · sin(εw)/(εw)`: the second factor is entire with value `1` at
`0`, so `∂̄k = δ₀` (`integral_sinKernel_mul_dbar`, via `integral_holo_mul_dbar_div`).  Bounds:
`|k(w)| ≤ e^{ε|Im w|}/(π|w|)` and `|k(w)| ≤ e^{ε|Im w|}/(π ε |w|²)`.

`kerSol ε ν θ z = ∫ k(z - ζ) θ(ζ) dν(ζ)` is the paper's `u₁` (with `ν = |μ₁|`, p. 409) and `u₃`
(with `ν = Lebesgue`, `θ = ∂̄u₂`, p. 410).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-! ## The kernel -/

/-- The kernel `k(w) = sin(εw) / (π ε w²)` of Lemma 4 (p. 409). -/
def sinKernel (ε : ℝ) (w : ℂ) : ℂ :=
  Complex.sin (ε * w) / ((Real.pi : ℂ) * ε * w ^ 2)

/-- The entire factor `z ↦ sin(ε(z - ζ))/(ε(z - ζ))` (value `1` at `ζ`), written with `dslope`. -/
def sinKernelFactor (ε : ℝ) (ζ z : ℂ) : ℂ :=
  dslope (fun z ↦ Complex.sin (ε * (z - ζ))) ζ z / ε

theorem differentiable_sinKernelFactor (ε : ℝ) (ζ : ℂ) :
    Differentiable ℂ (sinKernelFactor ε ζ) := by
  have hf : Differentiable ℂ (fun z ↦ Complex.sin (ε * (z - ζ))) := by fun_prop
  have h := (Complex.differentiableOn_dslope (s := univ) (c := ζ) (f := fun z ↦
    Complex.sin (ε * (z - ζ))) univ_mem).2 hf.differentiableOn
  exact (differentiableOn_univ.1 h).div_const _

theorem sinKernelFactor_self {ε : ℝ} (hε : ε ≠ 0) (ζ : ℂ) : sinKernelFactor ε ζ ζ = 1 := by
  have hd : HasDerivAt (fun z ↦ Complex.sin (ε * (z - ζ))) (Complex.cos (ε * (ζ - ζ)) * ε) ζ :=
    (Complex.hasDerivAt_sin _).comp ζ
      (((hasDerivAt_id ζ).sub_const ζ).const_mul (ε : ℂ) |>.congr_deriv (by simp))
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  rw [sinKernelFactor, dslope_same, hd.deriv]
  simp [hε']

theorem sinKernel_sub_eq (ε : ℝ) (ζ z : ℂ) :
    sinKernel ε (z - ζ) = sinKernelFactor ε ζ z / ((Real.pi : ℂ) * (z - ζ)) := by
  by_cases hε : ε = 0
  · simp [sinKernel, sinKernelFactor, hε]
  by_cases hz : z = ζ
  · subst hz
    simp [sinKernel]
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hzζ : z - ζ ≠ 0 := sub_ne_zero.2 hz
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [sinKernel, sinKernelFactor, dslope_of_ne _ hz, slope_def_field]
  simp only [sub_self, mul_zero, Complex.sin_zero, sub_zero]
  field_simp

theorem measurable_sinKernel (ε : ℝ) : Measurable (sinKernel ε) := by
  unfold sinKernel
  fun_prop

/-! ### Elementary bounds for `sin` and `cos` -/

/-- `|sin a| ≤ e^{|Im a|}`. -/
theorem norm_csin_le_exp (a : ℂ) : ‖Complex.sin a‖ ≤ Real.exp |a.im| := by
  have h1 : ‖Complex.exp (-a * I)‖ ≤ Real.exp |a.im| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (by simp [le_abs_self])
  have h2 : ‖Complex.exp (a * I)‖ ≤ Real.exp |a.im| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (by simp [neg_le_abs])
  calc ‖Complex.sin a‖ = ‖Complex.exp (-a * I) - Complex.exp (a * I)‖ / 2 := by
        simp [Complex.sin]
    _ ≤ (‖Complex.exp (-a * I)‖ + ‖Complex.exp (a * I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (Real.exp |a.im| + Real.exp |a.im|) / 2 := by gcongr
    _ = Real.exp |a.im| := by ring

/-- `|cos a| ≤ e^{|Im a|}`. -/
theorem norm_ccos_le_exp (a : ℂ) : ‖Complex.cos a‖ ≤ Real.exp |a.im| := by
  have h1 : ‖Complex.exp (-a * I)‖ ≤ Real.exp |a.im| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (by simp [le_abs_self])
  have h2 : ‖Complex.exp (a * I)‖ ≤ Real.exp |a.im| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (by simp [neg_le_abs])
  calc ‖Complex.cos a‖ = ‖Complex.exp (a * I) + Complex.exp (-a * I)‖ / 2 := by
        simp [Complex.cos]
    _ ≤ (‖Complex.exp (a * I)‖ + ‖Complex.exp (-a * I)‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ ≤ (Real.exp |a.im| + Real.exp |a.im|) / 2 := by gcongr
    _ = Real.exp |a.im| := by ring

/-- `|sin a| ≤ |a| e^{|Im a|}` (mean value inequality on the strip `|Im ξ| ≤ |Im a|`). -/
theorem norm_csin_le_mul_exp (a : ℂ) : ‖Complex.sin a‖ ≤ ‖a‖ * Real.exp |a.im| := by
  set s : Set ℂ := {ξ | -|a.im| ≤ ξ.im} ∩ {ξ | ξ.im ≤ |a.im|} with hs_def
  have hs : Convex ℝ s := (convex_halfSpace_im_ge _).inter (convex_halfSpace_im_le _)
  have hmem : ∀ ξ ∈ s, |ξ.im| ≤ |a.im| := fun ξ hξ ↦ abs_le.2 hξ
  have h := hs.norm_image_sub_le_of_norm_deriv_le (f := Complex.sin) (C := Real.exp |a.im|)
    (fun _ _ ↦ Complex.differentiableAt_sin)
    (fun ξ hξ ↦ by
      rw [Complex.deriv_sin]
      exact (norm_ccos_le_exp ξ).trans (Real.exp_le_exp.2 (hmem ξ hξ)))
    (x := 0) (y := a) (by simp [hs_def]) (by simp [hs_def, neg_abs_le, le_abs_self])
  simpa [mul_comm] using h

/-! ### Bounds for the kernel -/

theorem norm_sinKernel_eq {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    ‖sinKernel ε w‖ = ‖Complex.sin (ε * w)‖ / (Real.pi * ε * ‖w‖ ^ 2) := by
  rw [sinKernel, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hε.le]

theorem abs_im_ofReal_mul {ε : ℝ} (hε : 0 ≤ ε) (w : ℂ) : |((ε : ℂ) * w).im| = ε * |w.im| := by
  simp [abs_mul, abs_of_nonneg hε]

/-- `|k(w)| ≤ e^{ε|Im w|}/(π|w|)` (from `|sin a| ≤ |a| e^{|Im a|}`). -/
theorem norm_sinKernel_le {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    ‖sinKernel ε w‖ ≤ Real.exp (ε * |w.im|) / (Real.pi * ‖w‖) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [sinKernel]
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [norm_sinKernel_eq hε, div_le_div_iff₀ (by positivity) (by positivity)]
  have h := norm_csin_le_mul_exp (ε * w)
  rw [abs_im_ofReal_mul hε.le, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le] at h
  calc ‖Complex.sin (ε * w)‖ * (Real.pi * ‖w‖)
      ≤ ε * ‖w‖ * Real.exp (ε * |w.im|) * (Real.pi * ‖w‖) := by gcongr
    _ = Real.exp (ε * |w.im|) * (Real.pi * ε * ‖w‖ ^ 2) := by ring

/-- `|k(w)| ≤ e^{ε|Im w|}/(π ε |w|²)` (from `|sin a| ≤ e^{|Im a|}`). -/
theorem norm_sinKernel_le_sq {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    ‖sinKernel ε w‖ ≤ Real.exp (ε * |w.im|) / (Real.pi * ε * ‖w‖ ^ 2) := by
  rw [norm_sinKernel_eq hε]
  gcongr
  have h := norm_csin_le_exp (ε * w)
  rwa [abs_im_ofReal_mul hε.le] at h

/-- **`∂̄k = δ₀`**: `∫ k(z - ζ) ∂̄α(z) dm(z) = -α(ζ)` for every test function `α`. -/
theorem integral_sinKernel_mul_dbar {ε : ℝ} (hε : 0 < ε) {α : ℂ → ℂ}
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hαc : HasCompactSupport α) (ζ : ℂ) :
    ∫ z, sinKernel ε (z - ζ) * dbar α z = -α ζ := by
  have h := integral_holo_mul_dbar_div isOpen_univ (mem_univ ζ)
    (differentiable_sinKernelFactor ε ζ).differentiableOn hα hαc (subset_univ _)
  rw [sinKernelFactor_self hε.ne', one_mul] at h
  rw [← h]
  congr 1
  ext z
  rw [sinKernel_sub_eq]
  ring

/-! ## The operator `kerSol` -/

/-- `u(z) = ∫ k(z - ζ) θ(ζ) dν(ζ)`, the solution of `∂̄u = θ ν`. -/
def kerSol (ε : ℝ) (ν : Measure ℂ) (θ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ ζ, sinKernel ε (z - ζ) * θ ζ ∂ν

/-- Pointwise form of `norm_sinKernel_le` used for local integrals:
`|k(z - ζ)| ≤ (e^{εB}/π) |z - ζ|⁻¹` when `|Im (z - ζ)| ≤ B`. -/
theorem enorm_sinKernel_le_inv {ε : ℝ} (hε : 0 < ε) {w : ℂ} {B : ℝ} (hw : |w.im| ≤ B) :
    ‖sinKernel ε w‖ₑ ≤ ENNReal.ofReal (Real.exp (ε * B) / Real.pi) * ENNReal.ofReal ‖w‖⁻¹ := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ((norm_sinKernel_le hε w).trans ?_)
  rw [← div_div, div_eq_mul_inv]
  gcongr

/-- **Uniform local bound.**  For `|Im ζ| ≤ b` and `Q ⊆ D̄(0, R)`:
`∫_Q |k(z - ζ)| dm(z) ≤ (e^{ε(R+b)}/π)(2π + |Q|)`. -/
theorem lintegral_sinKernel_sub_le {ε : ℝ} (hε : 0 < ε) {Q : Set ℂ} {R : ℝ}
    (hQ : Q ⊆ closedBall 0 R) {b : ℝ} {ζ : ℂ} (hζ : |ζ.im| ≤ b) :
    ∫⁻ z in Q, ‖sinKernel ε (z - ζ)‖ₑ ≤
      ENNReal.ofReal (Real.exp (ε * (R + b)) / Real.pi) *
        (ENNReal.ofReal (2 * Real.pi) + volume Q) := by
  calc ∫⁻ z in Q, ‖sinKernel ε (z - ζ)‖ₑ
      ≤ ∫⁻ z in Q, ENNReal.ofReal (Real.exp (ε * (R + b)) / Real.pi) *
          ENNReal.ofReal ‖z - ζ‖⁻¹ := by
        refine setLIntegral_mono (by fun_prop) fun z hz ↦ enorm_sinKernel_le_inv hε ?_
        have hz' : ‖z‖ ≤ R := by simpa using hQ hz
        rw [Complex.sub_im]
        exact (abs_sub _ _).trans (add_le_add ((Complex.abs_im_le_norm z).trans hz') hζ)
    _ = ENNReal.ofReal (Real.exp (ε * (R + b)) / Real.pi) *
          ∫⁻ z in Q, ENNReal.ofReal ‖z - ζ‖⁻¹ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr; exact lintegral_inv_norm_sub_le_of_set Q ζ

theorem aestronglyMeasurable_sinKernel_prod (ε : ℝ) {μ ν : Measure ℂ} {θ : ℂ → ℂ}
    (hθ : AEStronglyMeasurable θ ν) :
    AEStronglyMeasurable (fun p : ℂ × ℂ ↦ sinKernel ε (p.1 - p.2) * θ p.2) (μ.prod ν) :=
  ((measurable_sinKernel ε).comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul
    hθ.comp_snd

/-- Tonelli bound: `∫_Q ∫ |k(z - ζ) θ(ζ)| dν dm ≤ C_Q ‖θ‖_{L¹(ν)}`, for `θ ν` carried by a strip. -/
theorem lintegral_lintegral_sinKernel_le {ε : ℝ} (hε : 0 < ε) {ν : Measure ℂ} [SFinite ν]
    {θ : ℂ → ℂ} (hθ : AEStronglyMeasurable θ ν) {b : ℝ} (hb : ∀ᵐ ζ ∂ν, θ ζ ≠ 0 → |ζ.im| ≤ b)
    {Q : Set ℂ} {R : ℝ} (hQ : Q ⊆ closedBall 0 R) :
    ∫⁻ z in Q, ∫⁻ ζ, ‖sinKernel ε (z - ζ) * θ ζ‖ₑ ∂ν ≤
      ENNReal.ofReal (Real.exp (ε * (R + b)) / Real.pi) *
        (ENNReal.ofReal (2 * Real.pi) + volume Q) * ∫⁻ ζ, ‖θ ζ‖ₑ ∂ν := by
  rw [lintegral_lintegral_swap (aestronglyMeasurable_sinKernel_prod ε hθ).enorm]
  rw [← lintegral_const_mul' _ _ (by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      -- `volume Q` may be infinite only if `Q` is unbounded
      exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
        (measure_mono hQ |>.trans_lt (isCompact_closedBall 0 R).measure_lt_top).ne⟩))]
  refine lintegral_mono_ae (hb.mono fun ζ hζ ↦ ?_)
  simp_rw [enorm_mul]
  rw [lintegral_mul_const' _ _ enorm_ne_top]
  by_cases h0 : θ ζ = 0
  · simp [h0]
  · gcongr ?_ * _
    exact lintegral_sinKernel_sub_le hε hQ (hζ h0)

/-- **Weak equation.**  If `θ ∈ L¹(ν)` and `θ ν` is carried by a horizontal strip `|Im ζ| ≤ b`,
then `∂̄(kerSol ε ν θ) = θ ν` in the sense of distributions. -/
theorem kerSol_isWeakDbarSolMeasure {ε : ℝ} (hε : 0 < ε) {ν : Measure ℂ} [SFinite ν]
    {θ : ℂ → ℂ} (hθ : Integrable θ ν) {b : ℝ} (hb : ∀ᵐ ζ ∂ν, θ ζ ≠ 0 → |ζ.im| ≤ b) :
    IsWeakDbarSolMeasure (kerSol ε ν θ) ν θ := by
  have hmeas := aestronglyMeasurable_sinKernel_prod ε (μ := volume) hθ.1
  have hum : AEStronglyMeasurable (kerSol ε ν θ) volume := hmeas.integral_prod_right'
  have hloc : ∀ Q : Set ℂ, IsCompact Q →
      ∫⁻ z in Q, ∫⁻ ζ, ‖sinKernel ε (z - ζ) * θ ζ‖ₑ ∂ν < ∞ := by
    intro Q hQ
    obtain ⟨R, hR⟩ := hQ.isBounded.subset_closedBall 0
    refine (lintegral_lintegral_sinKernel_le hε hθ.1 hb hR).trans_lt ?_
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hQ.measure_lt_top⟩)) hθ.2
  have hupt : ∀ z, ‖kerSol ε ν θ z‖ₑ ≤ ∫⁻ ζ, ‖sinKernel ε (z - ζ) * θ ζ‖ₑ ∂ν :=
    fun z ↦ enorm_integral_le_lintegral_enorm _
  refine ⟨?_, fun α hα hαc ↦ ?_⟩
  · rw [locallyIntegrable_iff]
    intro Q hQ
    refine ⟨hum.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact (lintegral_mono hupt).trans_lt (hloc Q hQ)
  -- the identity (Fubini and `∂̄k = δ₀`)
  have hα1 : ContDiff ℝ 1 α := contDiff_one_of_top hα
  obtain ⟨C, hC⟩ := (continuous_dbar hα1).bounded_above_of_compact_support
    (hasCompactSupport_dbar hαc)
  set K := tsupport α
  have hKc : IsCompact K := hαc.isCompact
  set F : ℂ → ℂ → ℂ := fun z ζ ↦ dbar α z * (sinKernel ε (z - ζ) * θ ζ) with hF
  have hint : Integrable (Function.uncurry F) (volume.prod ν) := by
    refine ⟨(continuous_dbar hα1).aestronglyMeasurable.comp_fst.mul hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ p, ‖Function.uncurry F p‖ₑ ∂(volume.prod ν)
        ≤ ∫⁻ z, ∫⁻ ζ, ‖F z ζ‖ₑ ∂ν := lintegral_prod_le _
      _ ≤ ∫⁻ z, K.indicator (fun z ↦ ENNReal.ofReal C *
            ∫⁻ ζ, ‖sinKernel ε (z - ζ) * θ ζ‖ₑ ∂ν) z := by
          refine lintegral_mono fun z ↦ ?_
          by_cases hz : z ∈ K
          · rw [indicator_of_mem hz, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_mono fun ζ ↦ ?_
            simp only [hF]
            rw [enorm_mul]
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hC z)
          · rw [indicator_of_notMem hz]
            have : dbar α z = 0 :=
              image_eq_zero_of_notMem_tsupport (fun h ↦ hz (tsupport_dbar_subset α h))
            simp [hF, this]
      _ = ENNReal.ofReal C * ∫⁻ z in K, ∫⁻ ζ, ‖sinKernel ε (z - ζ) * θ ζ‖ₑ ∂ν := by
          rw [lintegral_indicator hKc.measurableSet,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hloc K hKc)
  have h1 : ∫ z, kerSol ε ν θ z * dbar α z = ∫ z, ∫ ζ, F z ζ ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    simp only [kerSol, hF]
    rw [mul_comm, ← integral_const_mul]
  rw [h1, integral_integral_swap hint]
  have h2 : ∀ ζ, ∫ z, F z ζ = -(α ζ * θ ζ) := by
    intro ζ
    have : ∀ z, F z ζ = θ ζ * (sinKernel ε (z - ζ) * dbar α z) := by
      intro z; simp only [hF]; ring
    simp_rw [this]
    rw [integral_const_mul, integral_sinKernel_mul_dbar hε hα hαc]
    ring
  simp_rw [h2]
  rw [integral_neg]

theorem ofReal_inv_norm_le (v : ℂ) : ENNReal.ofReal ‖v‖⁻¹ ≤ (‖v‖₊ : ℝ≥0∞)⁻¹ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · rw [ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 hv), ofReal_norm, enorm_eq_nnnorm]

theorem enorm_le_coe_of_norm_le {v : ℂ} {M : ℝ≥0} (h : ‖v‖ ≤ M) : ‖v‖ₑ ≤ M := by
  rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
  exact h

/-- **The estimate on the real line** (p. 409, "it is plain that `u₁` has the properties"):
for `θ ν` carried by `|Im ζ| ≤ b`, `|θ| ≤ M` and `ν` large-scale Carleson with constant `K`,
`|u(x)| ≤ M (e^{εb}/π ∫_{|ζ-x|<1} dν(ζ)/|x - ζ| + 6 e^{εb} K/(π ε))`. -/
theorem enorm_kerSol_real_le {ε : ℝ} (hε : 0 < ε) {ν : Measure ℂ} {θ : ℂ → ℂ} {b : ℝ}
    {K M : ℝ≥0} (hC : IsCarlesonLarge ν K) (hθ : ∀ ζ, ‖θ ζ‖ ≤ M)
    (hb : ∀ᵐ ζ ∂ν, θ ζ ≠ 0 → |ζ.im| ≤ b) (x : ℝ) :
    ‖kerSol ε ν θ x‖ₑ ≤
      M * (ENNReal.ofReal (Real.exp (ε * b) / Real.pi) *
          ∫⁻ ζ in ball (x : ℂ) 1, (‖(x : ℂ) - ζ‖₊ : ℝ≥0∞)⁻¹ ∂ν +
        ENNReal.ofReal (6 * Real.exp (ε * b) / (Real.pi * ε)) * K) := by
  -- the two pieces of the pointwise bound: near `x` and away from `x`
  have hpt : ∀ᵐ ζ ∂ν, ‖sinKernel ε ((x : ℂ) - ζ) * θ ζ‖ₑ ≤
      (M : ℝ≥0∞) * ((ball (x : ℂ) 1).indicator (fun ζ ↦
          ENNReal.ofReal (Real.exp (ε * b) / Real.pi) * (‖(x : ℂ) - ζ‖₊ : ℝ≥0∞)⁻¹) ζ +
        (ball (x : ℂ) 1)ᶜ.indicator (fun ζ ↦ ENNReal.ofReal (Real.exp (ε * b) / (Real.pi * ε)) *
          ENNReal.ofReal (1 / ‖(x : ℂ) - ζ‖ ^ 2)) ζ) := by
    filter_upwards [hb] with ζ hζ
    rw [enorm_mul, mul_comm]
    by_cases h0 : θ ζ = 0
    · simp [h0]
    have hθζ : ‖θ ζ‖ₑ ≤ M := enorm_le_coe_of_norm_le (hθ ζ)
    have him : |((x : ℂ) - ζ).im| ≤ b := by simpa using hζ h0
    gcongr
    by_cases hball : ζ ∈ ball (x : ℂ) 1
    · rw [indicator_of_mem hball, indicator_of_notMem (notMem_compl_iff.2 hball), add_zero]
      exact (enorm_sinKernel_le_inv hε him).trans (by gcongr; exact ofReal_inv_norm_le _)
    · rw [indicator_of_notMem hball, indicator_of_mem (mem_compl hball), zero_add]
      rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((norm_sinKernel_le_sq hε _).trans ?_)
      rw [div_mul_div_comm, mul_one]
      gcongr
  have hf₁m : Measurable ((ball (x : ℂ) 1).indicator (fun ζ ↦
      ENNReal.ofReal (Real.exp (ε * b) / Real.pi) * (‖(x : ℂ) - ζ‖₊ : ℝ≥0∞)⁻¹)) :=
    Measurable.indicator (by fun_prop) measurableSet_ball
  have htail : ∫⁻ ζ in (ball (x : ℂ) 1)ᶜ, ENNReal.ofReal (Real.exp (ε * b) / (Real.pi * ε)) *
      ENNReal.ofReal (1 / ‖(x : ℂ) - ζ‖ ^ 2) ∂ν ≤
      ENNReal.ofReal (6 * Real.exp (ε * b) / (Real.pi * ε)) * K := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (Real.exp (ε * b) / (Real.pi * ε)) *
          ∫⁻ ζ in (ball (x : ℂ) 1)ᶜ, ENNReal.ofReal (1 / ‖(x : ℂ) - ζ‖ ^ 2) ∂ν
        ≤ ENNReal.ofReal (Real.exp (ε * b) / (Real.pi * ε)) * (ENNReal.ofReal (6 / 1) * K) := by
          gcongr; exact hC.lintegral_tail_le x le_rfl
      _ = ENNReal.ofReal (6 * Real.exp (ε * b) / (Real.pi * ε)) * K := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
  calc ‖kerSol ε ν θ x‖ₑ ≤ ∫⁻ ζ, ‖sinKernel ε ((x : ℂ) - ζ) * θ ζ‖ₑ ∂ν :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ _ := lintegral_mono_ae hpt
    _ = M * (∫⁻ ζ in ball (x : ℂ) 1, ENNReal.ofReal (Real.exp (ε * b) / Real.pi) *
            (‖(x : ℂ) - ζ‖₊ : ℝ≥0∞)⁻¹ ∂ν +
          ∫⁻ ζ in (ball (x : ℂ) 1)ᶜ, ENNReal.ofReal (Real.exp (ε * b) / (Real.pi * ε)) *
            ENNReal.ofReal (1 / ‖(x : ℂ) - ζ‖ ^ 2) ∂ν) := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_add_left hf₁m,
          lintegral_indicator measurableSet_ball, lintegral_indicator measurableSet_ball.compl]
    _ ≤ _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr

theorem continuousAt_sinKernel {ε : ℝ} (hε : ε ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    ContinuousAt (sinKernel ε) w := by
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold sinKernel
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [hw, hε', hpi])

/-- Continuity off the (compact) support. -/
theorem continuousOn_kerSol {ε : ℝ} (hε : 0 < ε) {ν : Measure ℂ} [IsFiniteMeasure ν]
    {L : Set ℂ} (hL : IsCompact L) (hνL : ν Lᶜ = 0) {θ : ℂ → ℂ}
    (hθ : AEStronglyMeasurable θ ν) {M : ℝ} (hθM : ∀ ζ, ‖θ ζ‖ ≤ M) :
    ContinuousOn (kerSol ε ν θ) Lᶜ := by
  intro z₀ hz₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨δ, hδ, hδL⟩ := Metric.isOpen_iff.1 hL.isClosed.isOpen_compl z₀ hz₀
  obtain ⟨R₀, hR₀⟩ := hL.isBounded.subset_closedBall 0
  have hM : 0 ≤ M := (norm_nonneg _).trans (hθM 0)
  have hLae : ∀ᵐ ζ ∂ν, ζ ∈ L := mem_ae_iff.2 hνL
  set C := Real.exp (ε * (‖z₀‖ + δ + R₀)) / (Real.pi * (δ / 2)) * M
  show ContinuousAt (fun z ↦ ∫ ζ, sinKernel ε (z - ζ) * θ ζ ∂ν) z₀
  refine continuousAt_of_dominated (F := fun z ζ ↦ sinKernel ε (z - ζ) * θ ζ)
    (bound := fun _ ↦ C) ?_ ?_ (integrable_const C) ?_
  · exact Filter.Eventually.of_forall fun z ↦
      ((measurable_sinKernel ε).comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
        hθ
  · filter_upwards [ball_mem_nhds z₀ (half_pos hδ)] with z hz
    filter_upwards [hLae] with ζ hζ
    have h1 : δ ≤ dist ζ z₀ := by
      by_contra h
      exact hδL (mem_ball.2 (lt_of_not_ge h)) hζ
    rw [mem_ball] at hz
    have h2 : δ / 2 ≤ ‖z - ζ‖ := by
      have := dist_triangle ζ z z₀
      rw [dist_comm ζ z, dist_eq_norm z ζ] at this
      linarith
    have hz' : ‖z‖ ≤ ‖z₀‖ + δ := by
      have := norm_sub_norm_le z z₀
      rw [← dist_eq_norm] at this
      linarith
    have hζ' : ‖ζ‖ ≤ R₀ := by simpa using hR₀ hζ
    have him : |(z - ζ).im| ≤ ‖z₀‖ + δ + R₀ :=
      calc |(z - ζ).im| ≤ ‖z - ζ‖ := Complex.abs_im_le_norm _
        _ ≤ ‖z‖ + ‖ζ‖ := norm_sub_le _ _
        _ ≤ ‖z₀‖ + δ + R₀ := by linarith
    rw [norm_mul]
    refine mul_le_mul ((norm_sinKernel_le hε _).trans ?_) (hθM ζ) (norm_nonneg _)
      (by positivity)
    gcongr
  · filter_upwards [hLae] with ζ hζ
    have hne : z₀ - ζ ≠ 0 := sub_ne_zero.2 (fun h ↦ hz₀ (h ▸ hζ))
    have hc : ContinuousAt (fun z ↦ z - ζ) z₀ := continuousAt_id.sub continuousAt_const
    exact (ContinuousAt.comp (g := sinKernel ε) (f := fun z ↦ z - ζ) (x := z₀)
      (continuousAt_sinKernel hε.ne' hne) hc).mul continuousAt_const

/-- Growth: `|u(z)| e^{-ε|Im z|} → 0` as `z → ∞`, for compactly supported `ν`. -/
theorem tendsto_kerSol {ε : ℝ} (hε : 0 < ε) {ν : Measure ℂ} [IsFiniteMeasure ν]
    {L : Set ℂ} (hL : IsCompact L) (hνL : ν Lᶜ = 0) {θ : ℂ → ℂ}
    (hθ : AEStronglyMeasurable θ ν) {M : ℝ} (hθM : ∀ ζ, ‖θ ζ‖ ≤ M) :
    Tendsto (fun z ↦ ‖kerSol ε ν θ z‖ * Real.exp (-ε * |z.im|)) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨R₀, hR₀⟩ := hL.isBounded.subset_closedBall 0
  set R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hM : 0 ≤ M := (norm_nonneg _).trans (hθM 0)
  have hLae : ∀ᵐ ζ ∂ν, ζ ∈ L := mem_ae_iff.2 hνL
  set A := Real.exp (ε * R) * 4 / (Real.pi * ε) * M * ν.real univ
  have hbound : ∀ z : ℂ, 2 * R + 1 ≤ ‖z‖ →
      ‖kerSol ε ν θ z‖ * Real.exp (-ε * |z.im|) ≤ A / ‖z‖ ^ 2 := by
    intro z hz
    have hzpos : 0 < ‖z‖ := by linarith
    have hpt : ∀ᵐ ζ ∂ν, ‖sinKernel ε (z - ζ) * θ ζ‖ ≤
        Real.exp (ε * (|z.im| + R)) / (Real.pi * ε * (‖z‖ / 2) ^ 2) * M := by
      filter_upwards [hLae] with ζ hζ
      have hζR : ‖ζ‖ ≤ R := (by simpa using hR₀ hζ : ‖ζ‖ ≤ R₀).trans (le_max_left _ _)
      have h1 : ‖z‖ / 2 ≤ ‖z - ζ‖ := by have := norm_sub_norm_le z ζ; linarith
      have h2 : |(z - ζ).im| ≤ |z.im| + R := by
        rw [Complex.sub_im]
        exact (abs_sub _ _).trans (by gcongr; exact (Complex.abs_im_le_norm ζ).trans hζR)
      rw [norm_mul]
      refine mul_le_mul ((norm_sinKernel_le_sq hε _).trans ?_) (hθM ζ) (norm_nonneg _)
        (by positivity)
      gcongr
    have hI : ‖kerSol ε ν θ z‖ ≤
        Real.exp (ε * (|z.im| + R)) / (Real.pi * ε * (‖z‖ / 2) ^ 2) * M * ν.real univ :=
      norm_integral_le_of_norm_le_const hpt
    calc ‖kerSol ε ν θ z‖ * Real.exp (-ε * |z.im|)
        ≤ Real.exp (ε * (|z.im| + R)) / (Real.pi * ε * (‖z‖ / 2) ^ 2) * M * ν.real univ *
            Real.exp (-ε * |z.im|) := by gcongr
      _ = A / ‖z‖ ^ 2 := by
        have he : Real.exp (ε * (|z.im| + R)) * Real.exp (-ε * |z.im|) = Real.exp (ε * R) := by
          rw [← Real.exp_add]; congr 1; ring
        simp only [A]
        rw [← he]
        field_simp
        ring
  have hlim : Tendsto (fun z : ℂ ↦ A / ‖z‖ ^ 2) (cocompact ℂ) (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop)
  refine squeeze_zero' (Eventually.of_forall fun z ↦ by positivity) ?_ hlim
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (2 * R + 1)] with z hz
  exact hbound z hz

/-! ## Densities with respect to Lebesgue measure (the correction `u₃`) -/

theorem kerSol_volume_eq_restrict (ε : ℝ) {g : ℂ → ℂ} {S : Set ℂ} (hS : MeasurableSet S)
    (hg : ∀ z ∉ S, g z = 0) : kerSol ε volume g = kerSol ε (volume.restrict S) g := by
  funext z
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun ζ hζ ↦ by simp [hg ζ hζ])).symm

theorem measurableSet_strip (a a' : ℝ) : MeasurableSet {w : ℂ | a ≤ w.im ∧ w.im ≤ a'} :=
  (measurableSet_le measurable_const Complex.measurable_im).inter
    (measurableSet_le Complex.measurable_im measurable_const)

/-- Pointwise form of `norm_sinKernel_le_sq`. -/
theorem enorm_sinKernel_le_inv_sq {ε : ℝ} (hε : 0 < ε) {w : ℂ} {B : ℝ} (hw : |w.im| ≤ B) :
    ‖sinKernel ε w‖ₑ ≤
      ENNReal.ofReal (Real.exp (ε * B) / (Real.pi * ε)) * ENNReal.ofReal (1 / ‖w‖ ^ 2) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ((norm_sinKernel_le_sq hε w).trans ?_)
  rw [div_mul_div_comm, mul_one]
  gcongr

/-- **The kernel on a horizontal strip.**  If `|Im w| ≤ B` on the strip `a ≤ Im w ≤ a'`, then
`∫_{a ≤ Im w ≤ a'} |k(w)| dm(w) ≤ e^{εB} (2 + 12 (a' - a)/(π ε))`: near `0` use
`|k| ≤ e^{εB}/(π|w|)`, away from `0` use `|k| ≤ e^{εB}/(πε|w|²)` and the tail bound for the
Carleson measure `m|_strip` (M03). -/
theorem lintegral_sinKernel_strip_le {ε : ℝ} (hε : 0 < ε) {a a' B : ℝ} (haa' : a ≤ a')
    (hB : ∀ w : ℂ, a ≤ w.im → w.im ≤ a' → |w.im| ≤ B) :
    ∫⁻ w in {w : ℂ | a ≤ w.im ∧ w.im ≤ a'}, ‖sinKernel ε w‖ₑ ≤
      ENNReal.ofReal (Real.exp (ε * B) * (2 + 12 * (a' - a) / (Real.pi * ε))) := by
  have hpt : ∀ w ∈ {w : ℂ | a ≤ w.im ∧ w.im ≤ a'}, ‖sinKernel ε w‖ₑ ≤
      (ball (0 : ℂ) 1).indicator (fun w ↦ ENNReal.ofReal (Real.exp (ε * B) / Real.pi) *
          ENNReal.ofReal ‖w - 0‖⁻¹) w +
        (ball (0 : ℂ) 1)ᶜ.indicator (fun w ↦ ENNReal.ofReal (Real.exp (ε * B) / (Real.pi * ε)) *
          ENNReal.ofReal (1 / ‖w‖ ^ 2)) w := by
    intro w hw
    have him := hB w hw.1 hw.2
    by_cases hball : w ∈ ball (0 : ℂ) 1
    · rw [indicator_of_mem hball, indicator_of_notMem (notMem_compl_iff.2 hball), add_zero,
        sub_zero]
      exact enorm_sinKernel_le_inv hε him
    · rw [indicator_of_notMem hball, indicator_of_mem (mem_compl hball), zero_add]
      exact enorm_sinKernel_le_inv_sq hε him
  have hm1 : Measurable ((ball (0 : ℂ) 1).indicator (fun w ↦
      ENNReal.ofReal (Real.exp (ε * B) / Real.pi) * ENNReal.ofReal ‖w - 0‖⁻¹)) :=
    Measurable.indicator (by fun_prop) measurableSet_ball
  have hm2 : Measurable ((ball (0 : ℂ) 1)ᶜ.indicator (fun w ↦
      ENNReal.ofReal (Real.exp (ε * B) / (Real.pi * ε)) * ENNReal.ofReal (1 / ‖w‖ ^ 2))) :=
    Measurable.indicator (by fun_prop) measurableSet_ball.compl
  have htail := (isCarlesonWith_volume_strip haa').isCarlesonLarge.lintegral_tail_le 0 le_rfl
  simp only [Complex.ofReal_zero, zero_sub, norm_neg] at htail
  have htoNN : ((Real.toNNReal (2 * (a' - a)) : ℝ≥0∞)) = ENNReal.ofReal (2 * (a' - a)) := rfl
  rw [htoNN] at htail
  calc ∫⁻ w in {w : ℂ | a ≤ w.im ∧ w.im ≤ a'}, ‖sinKernel ε w‖ₑ
      ≤ ∫⁻ w in {w : ℂ | a ≤ w.im ∧ w.im ≤ a'},
          ((ball (0 : ℂ) 1).indicator (fun w ↦ ENNReal.ofReal (Real.exp (ε * B) / Real.pi) *
            ENNReal.ofReal ‖w - 0‖⁻¹) w +
          (ball (0 : ℂ) 1)ᶜ.indicator (fun w ↦ ENNReal.ofReal (Real.exp (ε * B) / (Real.pi * ε)) *
            ENNReal.ofReal (1 / ‖w‖ ^ 2)) w) := setLIntegral_mono (hm1.add hm2) hpt
    _ = (∫⁻ w in {w : ℂ | a ≤ w.im ∧ w.im ≤ a'},
          (ball (0 : ℂ) 1).indicator (fun w ↦ ENNReal.ofReal (Real.exp (ε * B) / Real.pi) *
            ENNReal.ofReal ‖w - 0‖⁻¹) w) +
        ∫⁻ w in {w : ℂ | a ≤ w.im ∧ w.im ≤ a'},
          (ball (0 : ℂ) 1)ᶜ.indicator (fun w ↦ ENNReal.ofReal (Real.exp (ε * B) / (Real.pi * ε)) *
            ENNReal.ofReal (1 / ‖w‖ ^ 2)) w := lintegral_add_left hm1 _
    _ ≤ (∫⁻ w, (ball (0 : ℂ) 1).indicator (fun w ↦ ENNReal.ofReal (Real.exp (ε * B) / Real.pi) *
            ENNReal.ofReal ‖w - 0‖⁻¹) w) +
        ∫⁻ w in {w : ℂ | a ≤ w.im ∧ w.im ≤ a'},
          (ball (0 : ℂ) 1)ᶜ.indicator (fun w ↦ ENNReal.ofReal (Real.exp (ε * B) / (Real.pi * ε)) *
            ENNReal.ofReal (1 / ‖w‖ ^ 2)) w := by
        gcongr ?_ + _
        exact setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (Real.exp (ε * B) / Real.pi) * ENNReal.ofReal (2 * Real.pi * 1) +
        ENNReal.ofReal (Real.exp (ε * B) / (Real.pi * ε)) *
          ∫⁻ w in (ball (0 : ℂ) 1)ᶜ, ENNReal.ofReal (1 / ‖w‖ ^ 2)
            ∂(volume.restrict {w : ℂ | a ≤ w.im ∧ w.im ≤ a'}) := by
        rw [lintegral_indicator measurableSet_ball, lintegral_indicator measurableSet_ball.compl,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_inv_norm_sub_ball 0 zero_le_one]
    _ ≤ ENNReal.ofReal (Real.exp (ε * B) / Real.pi) * ENNReal.ofReal (2 * Real.pi * 1) +
        ENNReal.ofReal (Real.exp (ε * B) / (Real.pi * ε)) *
          (ENNReal.ofReal (6 / 1) * ENNReal.ofReal (2 * (a' - a))) := by gcongr
    _ = ENNReal.ofReal (Real.exp (ε * B) * (2 + 12 * (a' - a) / (Real.pi * ε))) := by
        have hpi := Real.pi_pos
        have haa'' : 0 ≤ a' - a := sub_nonneg.2 haa'
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        field_simp
        ring

/-- The strip lemma for the translated kernel `ζ ↦ k(z - ζ)` on `|Im ζ| ≤ b`:
`∫_{|Im ζ| ≤ b} |k(z - ζ)| dm(ζ) ≤ e^{ε(|Im z| + b)} (2 + 24 b/(π ε))`. -/
theorem lintegral_sinKernel_sub_strip_le {ε : ℝ} (hε : 0 < ε) (z : ℂ) {b : ℝ} (hb : 0 ≤ b) :
    ∫⁻ ζ in {ζ : ℂ | |ζ.im| ≤ b}, ‖sinKernel ε (z - ζ)‖ₑ ≤
      ENNReal.ofReal (Real.exp (ε * (|z.im| + b)) * (2 + 24 * b / (Real.pi * ε))) := by
  have hT : MeasurableSet {ζ : ℂ | |ζ.im| ≤ b} := measurableSet_le (by fun_prop) measurable_const
  have hS : MeasurableSet {w : ℂ | z.im - b ≤ w.im ∧ w.im ≤ z.im + b} := measurableSet_strip _ _
  have hmem : ∀ ζ : ℂ, (z - ζ ∈ {w : ℂ | z.im - b ≤ w.im ∧ w.im ≤ z.im + b}) ↔ |ζ.im| ≤ b := by
    intro ζ
    simp only [mem_ofPred_eq, Complex.sub_im, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have key : ∀ ζ, {ζ : ℂ | |ζ.im| ≤ b}.indicator (fun ζ ↦ ‖sinKernel ε (z - ζ)‖ₑ) ζ =
      {w : ℂ | z.im - b ≤ w.im ∧ w.im ≤ z.im + b}.indicator (fun w ↦ ‖sinKernel ε w‖ₑ) (z - ζ) := by
    intro ζ
    simp only [indicator_apply, hmem, mem_ofPred_eq]
  rw [← lintegral_indicator hT]
  simp_rw [key]
  rw [lintegral_sub_left_eq_self (fun w ↦ {w : ℂ | z.im - b ≤ w.im ∧ w.im ≤ z.im + b}.indicator
    (fun w ↦ ‖sinKernel ε w‖ₑ) w) z, lintegral_indicator hS]
  refine (lintegral_sinKernel_strip_le (a := z.im - b) (a' := z.im + b) (B := |z.im| + b) hε
    (by linarith) (fun w h1 h2 ↦ ?_)).trans (le_of_eq ?_)
  · rw [abs_le]
    constructor <;> linarith [neg_abs_le z.im, le_abs_self z.im]
  · congr 2
    ring

/-- `∫ |k(z - ζ) θ(ζ)| dm(ζ) ≤ M e^{ε(|Im z| + b)}(2 + 24b/(πε))` for `|θ| ≤ M` carried by the strip
`|Im ζ| ≤ b`. -/
theorem lintegral_enorm_sinKernel_sub_mul_le {ε : ℝ} (hε : 0 < ε) {θ : ℂ → ℂ} {b M : ℝ}
    (hb : 0 ≤ b) (hθM : ∀ ζ, ‖θ ζ‖ ≤ M) (hθb : ∀ ζ, θ ζ ≠ 0 → |ζ.im| ≤ b) (z : ℂ) :
    ∫⁻ ζ, ‖sinKernel ε (z - ζ) * θ ζ‖ₑ ≤
      ENNReal.ofReal (M * (Real.exp (ε * (|z.im| + b)) * (2 + 24 * b / (Real.pi * ε)))) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hθM 0)
  have hT : MeasurableSet {ζ : ℂ | |ζ.im| ≤ b} := measurableSet_le (by fun_prop) measurable_const
  have hpt : ∀ ζ, ‖sinKernel ε (z - ζ) * θ ζ‖ₑ ≤
      ENNReal.ofReal M * {ζ : ℂ | |ζ.im| ≤ b}.indicator (fun ζ ↦ ‖sinKernel ε (z - ζ)‖ₑ) ζ := by
    intro ζ
    by_cases h0 : θ ζ = 0
    · simp [h0]
    rw [indicator_of_mem (show ζ ∈ {ζ : ℂ | |ζ.im| ≤ b} from hθb ζ h0), enorm_mul, mul_comm]
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hθM ζ)
  calc ∫⁻ ζ, ‖sinKernel ε (z - ζ) * θ ζ‖ₑ
      ≤ ∫⁻ ζ, ENNReal.ofReal M *
          {ζ : ℂ | |ζ.im| ≤ b}.indicator (fun ζ ↦ ‖sinKernel ε (z - ζ)‖ₑ) ζ := lintegral_mono hpt
    _ = ENNReal.ofReal M * ∫⁻ ζ in {ζ : ℂ | |ζ.im| ≤ b}, ‖sinKernel ε (z - ζ)‖ₑ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hT]
    _ ≤ ENNReal.ofReal M *
          ENNReal.ofReal (Real.exp (ε * (|z.im| + b)) * (2 + 24 * b / (Real.pi * ε))) := by
        gcongr
        exact lintegral_sinKernel_sub_strip_le hε z hb
    _ = _ := (ENNReal.ofReal_mul hM).symm

theorem integrable_sinKernel_sub_mul {ε : ℝ} (hε : 0 < ε) {θ : ℂ → ℂ}
    (hθ : AEStronglyMeasurable θ volume) {b M : ℝ} (hb : 0 ≤ b) (hθM : ∀ ζ, ‖θ ζ‖ ≤ M)
    (hθb : ∀ ζ, θ ζ ≠ 0 → |ζ.im| ≤ b) (z : ℂ) :
    Integrable (fun ζ ↦ sinKernel ε (z - ζ) * θ ζ) := by
  refine ⟨((measurable_sinKernel ε).comp
    (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hθ, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (lintegral_enorm_sinKernel_sub_mul_le hε hb hθM hθb z).trans_lt ENNReal.ofReal_lt_top

theorem norm_kerSol_volume_le {ε : ℝ} (hε : 0 < ε) {θ : ℂ → ℂ} {b M : ℝ}
    (hb : 0 ≤ b) (hθM : ∀ ζ, ‖θ ζ‖ ≤ M) (hθb : ∀ ζ, θ ζ ≠ 0 → |ζ.im| ≤ b) (z : ℂ) :
    ‖kerSol ε volume θ z‖ ≤
      M * (Real.exp (ε * (|z.im| + b)) * (2 + 24 * b / (Real.pi * ε))) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hθM 0)
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ofReal_norm]
  exact (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_enorm_sinKernel_sub_mul_le hε hb hθM hθb z)

/-- `k * g` is continuous for `g` continuous, bounded and supported in a horizontal strip. -/
theorem continuous_kerSol_volume {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ} (hg : Continuous g)
    {b M : ℝ} (hgM : ∀ z, ‖g z‖ ≤ M) (hgb : ∀ z, g z ≠ 0 → |z.im| ≤ b) :
    Continuous (kerSol ε volume g) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hgM 0)
  -- change of variables `ζ = z - w`
  have hcv : kerSol ε volume g = fun z ↦ ∫ w, sinKernel ε w * g (z - w) := by
    funext z
    have := integral_sub_left_eq_self (fun w ↦ sinKernel ε w * g (z - w)) volume z
    simp only [sub_sub_cancel] at this
    exact this
  rw [hcv, continuous_iff_continuousAt]
  intro z₀
  set B := |z₀.im| + 1 + b
  have hSm : MeasurableSet {w : ℂ | -B ≤ w.im ∧ w.im ≤ B} := measurableSet_strip _ _
  have hkS : IntegrableOn (sinKernel ε) {w : ℂ | -B ≤ w.im ∧ w.im ≤ B} := by
    by_cases hB : 0 ≤ B
    · refine ⟨(measurable_sinKernel ε).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      exact (lintegral_sinKernel_strip_le hε (by linarith)
        (fun w h1 h2 ↦ abs_le.2 ⟨h1, h2⟩)).trans_lt ENNReal.ofReal_lt_top
    · have : {w : ℂ | -B ≤ w.im ∧ w.im ≤ B} = ∅ := by
        ext w; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
        intro h; linarith
      rw [this]
      exact integrableOn_empty
  have hbound : Integrable (fun w ↦ M * {w : ℂ | -B ≤ w.im ∧ w.im ≤ B}.indicator
      (fun w ↦ ‖sinKernel ε w‖) w) :=
    ((integrable_indicator_iff hSm).2 hkS.norm).const_mul M
  refine continuousAt_of_dominated (F := fun z w ↦ sinKernel ε w * g (z - w)) ?_ ?_ hbound ?_
  · exact Filter.Eventually.of_forall fun z ↦ (measurable_sinKernel ε).aestronglyMeasurable.mul
      (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds z₀ one_pos] with z hz
    refine Filter.Eventually.of_forall fun w ↦ ?_
    by_cases h0 : g (z - w) = 0
    · simp only [h0, mul_zero, norm_zero]
      exact mul_nonneg hM (indicator_nonneg (fun _ _ ↦ norm_nonneg _) _)
    have h1 := hgb _ h0
    have h2 : |z.im - z₀.im| ≤ 1 := by
      rw [mem_ball, dist_eq_norm] at hz
      exact (by simpa using Complex.abs_im_le_norm (z - z₀) : |z.im - z₀.im| ≤ ‖z - z₀‖).trans
        hz.le
    have hw : w ∈ {w : ℂ | -B ≤ w.im ∧ w.im ≤ B} := by
      rw [Complex.sub_im] at h1
      simp only [mem_ofPred_eq, B]
      rw [abs_le] at h1 h2
      constructor <;> linarith [neg_abs_le z₀.im, le_abs_self z₀.im]
    rw [indicator_of_mem hw, norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hgM _) (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun w ↦
      continuousAt_const.mul ((hg.comp (continuous_id.sub continuous_const)).continuousAt)

/-- Growth of `k * g` for `g` bounded, supported in a horizontal strip and `g → 0` at `∞`. -/
theorem tendsto_kerSol_volume {ε : ℝ} (hε : 0 < ε) {g : ℂ → ℂ}
    (hg : AEStronglyMeasurable g volume) {b M : ℝ} (hgM : ∀ z, ‖g z‖ ≤ M)
    (hgb : ∀ z, g z ≠ 0 → |z.im| ≤ b) (hg0 : Tendsto g (cocompact ℂ) (𝓝 0)) :
    Tendsto (fun z ↦ ‖kerSol ε volume g z‖ * Real.exp (-ε * |z.im|)) (cocompact ℂ) (𝓝 0) := by
  set b' := max b 0
  have hb' : 0 ≤ b' := le_max_right _ _
  have hgb' : ∀ z, g z ≠ 0 → |z.im| ≤ b' := fun z hz ↦ (hgb z hz).trans (le_max_left _ _)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hgM 0)
  obtain ⟨C, hC⟩ : ∃ C, C = Real.exp (ε * b') * (2 + 24 * b' / (Real.pi * ε)) := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hC]; positivity
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- `|g| ≤ η` outside a large disc
  obtain ⟨η, hη, hηC⟩ : ∃ η, 0 < η ∧ η * C = δ / 2 := ⟨δ / 2 / C, by positivity, by field_simp⟩
  obtain ⟨R, hR⟩ : ∃ R, ∀ ζ : ℂ, R ≤ ‖ζ‖ → ‖g ζ‖ < η := by
    have h1 : ∀ᶠ ζ in cocompact ℂ, dist (g ζ) 0 < η := Metric.tendsto_nhds.1 hg0 η hη
    rw [← Metric.cobounded_eq_cocompact, hasBasis_cobounded_norm.eventually_iff] at h1
    obtain ⟨R, -, hR⟩ := h1
    exact ⟨R, fun ζ hζ ↦ by simpa using hR hζ⟩
  -- split `g = g₁ + g₂` with `g₁` compactly supported and `|g₂| ≤ η`
  set Kc := closedBall (0 : ℂ) R
  have hKc : MeasurableSet Kc := measurableSet_closedBall
  have hg₁M : ∀ ζ, ‖Kc.indicator g ζ‖ ≤ M := fun ζ ↦ (norm_indicator_le_norm_self _ _).trans (hgM ζ)
  have hg₁b : ∀ ζ, Kc.indicator g ζ ≠ 0 → |ζ.im| ≤ b' := fun ζ h ↦
    hgb' ζ (fun h' ↦ h (by simp [h']))
  have hg₂η : ∀ ζ, ‖Kcᶜ.indicator g ζ‖ ≤ η := by
    intro ζ
    by_cases hζ : ζ ∈ Kc
    · simp [indicator_of_notMem (notMem_compl_iff.2 hζ), hη.le]
    · rw [indicator_of_mem hζ]
      refine (hR ζ ?_).le
      simp only [Kc, mem_closedBall, dist_zero_right, not_le] at hζ
      exact hζ.le
  have hg₂b : ∀ ζ, Kcᶜ.indicator g ζ ≠ 0 → |ζ.im| ≤ b' := fun ζ h ↦
    hgb' ζ (fun h' ↦ h (by simp [h']))
  have hsplit : ∀ z, kerSol ε volume g z =
      kerSol ε (volume.restrict Kc) (Kc.indicator g) z + kerSol ε volume (Kcᶜ.indicator g) z := by
    intro z
    rw [← kerSol_volume_eq_restrict ε hKc (fun ζ hζ ↦ indicator_of_notMem hζ _)]
    simp only [kerSol]
    rw [← integral_add (integrable_sinKernel_sub_mul hε (hg.indicator hKc) hb' hg₁M hg₁b z)
      (integrable_sinKernel_sub_mul hε (hg.indicator hKc.compl) hb' hg₂η hg₂b z)]
    congr 1
    ext ζ
    rw [← mul_add, indicator_self_add_compl_apply]
  -- the compactly supported part
  have : IsFiniteMeasure (volume.restrict Kc) :=
    isFiniteMeasure_restrict.2 (measure_closedBall_lt_top (x := (0 : ℂ)) (r := R)).ne
  have hKc0 : volume.restrict Kc Kcᶜ = 0 := by
    rw [Measure.restrict_apply hKc.compl, compl_inter_self, measure_empty]
  have h1 := Metric.tendsto_nhds.1 (tendsto_kerSol hε (isCompact_closedBall 0 R) hKc0
    ((hg.indicator hKc).restrict) hg₁M) (δ / 2) (half_pos hδ)
  filter_upwards [h1] with z hz
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hz ⊢
  -- the part bounded by `η`
  have h2 : ‖kerSol ε volume (Kcᶜ.indicator g) z‖ * Real.exp (-ε * |z.im|) ≤ η * C := by
    calc ‖kerSol ε volume (Kcᶜ.indicator g) z‖ * Real.exp (-ε * |z.im|)
        ≤ η * (Real.exp (ε * (|z.im| + b')) * (2 + 24 * b' / (Real.pi * ε))) *
            Real.exp (-ε * |z.im|) := by
          gcongr
          exact norm_kerSol_volume_le hε hb' hg₂η hg₂b z
      _ = η * C := by
          rw [hC, show ε * (|z.im| + b') = ε * b' + ε * |z.im| by ring, Real.exp_add, neg_mul,
            Real.exp_neg]
          field_simp
  calc ‖kerSol ε volume g z‖ * Real.exp (-ε * |z.im|)
      ≤ (‖kerSol ε (volume.restrict Kc) (Kc.indicator g) z‖ +
          ‖kerSol ε volume (Kcᶜ.indicator g) z‖) * Real.exp (-ε * |z.im|) := by
        rw [hsplit]
        gcongr
        exact norm_add_le _ _
    _ = ‖kerSol ε (volume.restrict Kc) (Kc.indicator g) z‖ * Real.exp (-ε * |z.im|) +
          ‖kerSol ε volume (Kcᶜ.indicator g) z‖ * Real.exp (-ε * |z.im|) := add_mul _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add_of_lt_of_le hz (h2.trans hηC.le)
    _ = δ := add_halves δ

end OCS
