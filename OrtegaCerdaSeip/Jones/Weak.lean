import OrtegaCerdaSeip.Jones.Estimates
import OrtegaCerdaSeip.Foundations.HoloKernel
import OrtegaCerdaSeip.Foundations.Weyl

/-!
# M04 (Jones) — Jones' formula solves `∂̄v = θ ρ` in the upper half-plane

See `blueprint/M04_Jones.md` (§1.4, §1.7).

For fixed `ζ` with `Im ζ > 0`, Jones' kernel is `H(·, ζ)/(π(z - ζ))` with `H(·, ζ)` holomorphic in
`ℂ⁺` and `H(ζ, ζ) = 1` (`jonesH_self`), so `integral_holo_mul_dbar_div` (Pompeiu) gives
`∫ kernel(z, ζ) ∂̄β(z) dm(z) = -β(ζ)` for test functions `β` supported in `ℂ⁺`; Fubini then gives
the weak equation.  The kernel is `O(1/|z - ζ|)` uniformly (`norm_jonesKernel_le_inv`), which gives
local integrability and the Fubini bound.  Continuity off the support is dominated convergence.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

variable {ρ : Measure ℂ} [IsFiniteMeasure ρ]

/-- For `Im ζ > 0` and `β` a test function supported in `ℂ⁺`:
`∫ kernel(z, ζ) ∂̄β(z) dm(z) = -β(ζ)`. -/
theorem integral_jonesKernel_mul_dbar (h0 : ∀ᵐ w ∂ρ, 0 ≤ w.im) {ζ : ℂ} (hζ : 0 < ζ.im)
    {β : ℂ → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβc : HasCompactSupport β)
    (hβs : tsupport β ⊆ {z | 0 < z.im}) :
    ∫ z, jonesKernel ρ z ζ * dbar β z = -β ζ := by
  have hΩ : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have h := integral_holo_mul_dbar_div hΩ hζ (differentiableOn_jonesH h0 hζ) hβ hβc hβs
  rw [jonesH_self ρ hζ, one_mul] at h
  rw [← h]
  congr 1; ext z
  rw [jonesKernel_eq_jonesH_div]; ring

omit [IsFiniteMeasure ρ] in
theorem measurable_jonesKernel_mul (ρ : Measure ℂ) [SFinite ρ] {θ : ℂ → ℂ} (hθ : Measurable θ) :
    Measurable fun p : ℂ × ℂ ↦ jonesKernel ρ p.1 p.2 * θ p.2 :=
  (measurable_jonesKernel ρ).mul (hθ.comp measurable_snd)

omit [IsFiniteMeasure ρ] in
theorem stronglyMeasurable_jonesSol (ρ : Measure ℂ) [SFinite ρ] {θ : ℂ → ℂ} (hθ : Measurable θ) :
    StronglyMeasurable (jonesSol ρ θ) :=
  (measurable_jonesKernel_mul ρ hθ).stronglyMeasurable.integral_prod_right' (ν := ρ)

/-- The constant `C_ρ = (2/π) e^{ρ(ℂ)/20}` of `norm_jonesKernel_le_inv`. -/
def jonesConst (ρ : Measure ℂ) : ℝ := 2 / Real.pi * Real.exp ((ρ univ).toReal / 20)

omit [IsFiniteMeasure ρ] in
theorem jonesConst_nonneg (ρ : Measure ℂ) : 0 ≤ jonesConst ρ := by
  unfold jonesConst; positivity

/-- `∫_Q |k(z, ζ) θ(ζ)| dm(z) ≤ C_ρ (2π + |Q|)` for `Q` in the closed upper half-plane. -/
theorem setLIntegral_enorm_jonesKernel_le (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {θ : ℂ → ℂ}
    (hθ1 : ∀ z, ‖θ z‖ ≤ 1) {Q : Set ℂ} (hQm : MeasurableSet Q) (hQ : ∀ z ∈ Q, 0 ≤ z.im)
    {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    ∫⁻ z in Q, ‖jonesKernel ρ z ζ * θ ζ‖ₑ ≤
      ENNReal.ofReal (jonesConst ρ) * (ENNReal.ofReal (2 * Real.pi) + volume Q) := by
  calc ∫⁻ z in Q, ‖jonesKernel ρ z ζ * θ ζ‖ₑ
      ≤ ∫⁻ z in Q, ENNReal.ofReal (jonesConst ρ) * ENNReal.ofReal ‖z - ζ‖⁻¹ := by
        refine setLIntegral_mono' hQm fun z hz ↦ ?_
        rw [← ENNReal.ofReal_mul (jonesConst_nonneg ρ), ← ofReal_norm, norm_mul]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖jonesKernel ρ z ζ‖ * ‖θ ζ‖ ≤ ‖jonesKernel ρ z ζ‖ * 1 := by gcongr; exact hθ1 ζ
          _ ≤ jonesConst ρ / ‖z - ζ‖ := by
              rw [mul_one]; exact norm_jonesKernel_le_inv h10 (hQ z hz) hζ
          _ = jonesConst ρ * ‖z - ζ‖⁻¹ := div_eq_mul_inv _ _
    _ = ENNReal.ofReal (jonesConst ρ) * ∫⁻ z in Q, ENNReal.ofReal ‖z - ζ‖⁻¹ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr; exact lintegral_inv_norm_sub_le_of_set Q ζ

/-- The Fubini bound: `∫_ρ ∫_Q |k(z, ζ) θ(ζ)| dm(z) dρ(ζ) ≤ C_ρ (2π + |Q|) ρ(ℂ)`. -/
theorem lintegral_setLIntegral_enorm_jonesKernel_le (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {θ : ℂ → ℂ}
    (hθ1 : ∀ z, ‖θ z‖ ≤ 1) {Q : Set ℂ} (hQm : MeasurableSet Q) (hQ : ∀ z ∈ Q, 0 ≤ z.im) :
    ∫⁻ ζ, (∫⁻ z in Q, ‖jonesKernel ρ z ζ * θ ζ‖ₑ) ∂ρ ≤
      ENNReal.ofReal (jonesConst ρ) * (ENNReal.ofReal (2 * Real.pi) + volume Q) * ρ univ := by
  calc ∫⁻ ζ, (∫⁻ z in Q, ‖jonesKernel ρ z ζ * θ ζ‖ₑ) ∂ρ
      ≤ ∫⁻ _, ENNReal.ofReal (jonesConst ρ) * (ENNReal.ofReal (2 * Real.pi) + volume Q) ∂ρ :=
        lintegral_mono_ae (h10.mono fun ζ hζ ↦
          setLIntegral_enorm_jonesKernel_le h10 hθ1 hQm hQ (ζ := ζ) (by linarith))
    _ = _ := lintegral_const _

/-- Jones' solution is locally integrable on the open upper half-plane. -/
theorem locallyIntegrableOn_jonesSol (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {θ : ℂ → ℂ} (hθ : Measurable θ)
    (hθ1 : ∀ z, ‖θ z‖ ≤ 1) : LocallyIntegrableOn (jonesSol ρ θ) {z | 0 < z.im} := by
  have hΩ : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
  intro Q hQs hQ
  have hQm : MeasurableSet Q := hQ.isClosed.measurableSet
  have hQ0 : ∀ z ∈ Q, 0 ≤ z.im := fun z hz ↦ (hQs hz).le
  have hmeas : Measurable fun p : ℂ × ℂ ↦ ‖jonesKernel ρ p.1 p.2 * θ p.2‖ₑ :=
    (measurable_jonesKernel_mul ρ hθ).enorm
  refine ⟨(stronglyMeasurable_jonesSol ρ hθ).aestronglyMeasurable, ?_⟩
  calc ∫⁻ z in Q, ‖jonesSol ρ θ z‖ₑ
      ≤ ∫⁻ z in Q, ∫⁻ ζ, ‖jonesKernel ρ z ζ * θ ζ‖ₑ ∂ρ :=
        lintegral_mono fun z ↦ enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ζ, (∫⁻ z in Q, ‖jonesKernel ρ z ζ * θ ζ‖ₑ) ∂ρ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ ≤ ENNReal.ofReal (jonesConst ρ) * (ENNReal.ofReal (2 * Real.pi) + volume Q) * ρ univ :=
        lintegral_setLIntegral_enorm_jonesKernel_le h10 hθ1 hQm hQ0
    _ < ∞ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
          (measure_lt_top ρ univ)
        exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hQ.measure_lt_top⟩

/-- The integrand of the weak equation is integrable on `m × ρ`. -/
theorem integrable_jonesKernel_mul_dbar (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {θ : ℂ → ℂ}
    (hθ : Measurable θ) (hθ1 : ∀ z, ‖θ z‖ ≤ 1) {β : ℂ → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβs : tsupport β ⊆ {z | 0 < z.im}) :
    Integrable (fun p : ℂ × ℂ ↦ jonesKernel ρ p.1 p.2 * θ p.2 * dbar β p.1)
      (volume.prod ρ) := by
  have hβ1 := contDiff_one_of_top hβ
  have hdc : Continuous (dbar β) := continuous_dbar hβ1
  obtain ⟨M, hM⟩ := hdc.bounded_above_of_compact_support (hasCompactSupport_dbar hβc)
  set Q := tsupport β
  have hQm : MeasurableSet Q := (isClosed_tsupport β).measurableSet
  have hQ0 : ∀ z ∈ Q, 0 ≤ z.im := fun z hz ↦ (hβs hz).le
  have hmeas : Measurable fun p : ℂ × ℂ ↦ jonesKernel ρ p.1 p.2 * θ p.2 * dbar β p.1 :=
    (measurable_jonesKernel_mul ρ hθ).mul (hdc.measurable.comp measurable_fst)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hpt : ∀ z ζ, ‖jonesKernel ρ z ζ * θ ζ * dbar β z‖ₑ ≤
      Q.indicator (fun z ↦ ENNReal.ofReal M * ‖jonesKernel ρ z ζ * θ ζ‖ₑ) z := by
    intro z ζ
    by_cases hz : z ∈ Q
    · rw [indicator_of_mem hz, enorm_mul, mul_comm, ← ofReal_norm (dbar β z)]
      gcongr
      exact hM z
    · rw [indicator_of_notMem hz,
        image_eq_zero_of_notMem_tsupport (fun h ↦ hz (tsupport_dbar_subset β h)), mul_zero,
        enorm_zero]
  calc ∫⁻ p, ‖jonesKernel ρ p.1 p.2 * θ p.2 * dbar β p.1‖ₑ ∂(volume.prod ρ)
      = ∫⁻ ζ, ∫⁻ z, ‖jonesKernel ρ z ζ * θ ζ * dbar β z‖ₑ ∂volume ∂ρ :=
        lintegral_prod_symm _ hmeas.enorm.aemeasurable
    _ ≤ ∫⁻ ζ, ENNReal.ofReal M * (∫⁻ z in Q, ‖jonesKernel ρ z ζ * θ ζ‖ₑ) ∂ρ := by
        refine lintegral_mono fun ζ ↦ ?_
        calc ∫⁻ z, ‖jonesKernel ρ z ζ * θ ζ * dbar β z‖ₑ
            ≤ ∫⁻ z, Q.indicator (fun z ↦ ENNReal.ofReal M * ‖jonesKernel ρ z ζ * θ ζ‖ₑ) z :=
              lintegral_mono fun z ↦ hpt z ζ
          _ = ENNReal.ofReal M * ∫⁻ z in Q, ‖jonesKernel ρ z ζ * θ ζ‖ₑ := by
              rw [lintegral_indicator hQm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal M * ∫⁻ ζ, (∫⁻ z in Q, ‖jonesKernel ρ z ζ * θ ζ‖ₑ) ∂ρ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal (jonesConst ρ) *
          (ENNReal.ofReal (2 * Real.pi) + volume Q) * ρ univ) := by
        gcongr; exact lintegral_setLIntegral_enorm_jonesKernel_le h10 hθ1 hQm hQ0
    _ < ∞ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
          (measure_lt_top ρ univ))
        exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hβc.isCompact.measure_lt_top⟩

/-- **Jones' formula solves `∂̄v = θ ρ` in `ℂ⁺`** (weak form, test functions supported in `ℂ⁺`). -/
theorem jonesSol_isWeakDbarSol (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {θ : ℂ → ℂ} (hθ : Measurable θ)
    (hθ1 : ∀ z, ‖θ z‖ ≤ 1) :
    LocallyIntegrableOn (jonesSol ρ θ) {z | 0 < z.im} ∧
      ∀ β : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) β → HasCompactSupport β → tsupport β ⊆ {z | 0 < z.im} →
        ∫ z, jonesSol ρ θ z * dbar β z = -∫ z, β z * θ z ∂ρ := by
  refine ⟨locallyIntegrableOn_jonesSol h10 hθ hθ1, fun β hβ hβc hβs ↦ ?_⟩
  have h0 : ∀ᵐ w ∂ρ, 0 ≤ w.im := h10.mono fun w hw ↦ by linarith
  have hint := integrable_jonesKernel_mul_dbar h10 hθ hθ1 hβ hβc hβs
  calc ∫ z, jonesSol ρ θ z * dbar β z
      = ∫ z, ∫ ζ, jonesKernel ρ z ζ * θ ζ * dbar β z ∂ρ := by
        refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
        simp only [jonesSol]
        exact (integral_mul_const _ _).symm
    _ = ∫ ζ, ∫ z, jonesKernel ρ z ζ * θ ζ * dbar β z ∂volume ∂ρ :=
        integral_integral_swap (f := fun z ζ ↦ jonesKernel ρ z ζ * θ ζ * dbar β z) hint
    _ = ∫ ζ, -(β ζ * θ ζ) ∂ρ := by
        refine integral_congr_ae (h10.mono fun ζ hζ ↦ ?_)
        have hζ' : 0 < ζ.im := by linarith
        calc ∫ z, jonesKernel ρ z ζ * θ ζ * dbar β z
            = θ ζ * ∫ z, jonesKernel ρ z ζ * dbar β z := by
              rw [← integral_const_mul]; congr 1; ext z; ring
          _ = -(β ζ * θ ζ) := by
              rw [integral_jonesKernel_mul_dbar h0 hζ' hβ hβc hβs]; ring
    _ = -∫ z, β z * θ z ∂ρ := integral_neg _

/-- For `ζ` in the upper half-plane, `z ↦ k(z, ζ)` is continuous at every `z₀ ∈ ℂ⁺ ∖ {ζ}`. -/
theorem continuousAt_jonesKernel (h0 : ∀ᵐ w ∂ρ, 0 ≤ w.im) {ζ z₀ : ℂ} (hζ : 0 < ζ.im)
    (hz₀ : 0 < z₀.im) (hne : z₀ ≠ ζ) : ContinuousAt (fun z ↦ jonesKernel ρ z ζ) z₀ := by
  have hΩ : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hE : ContinuousAt (fun z ↦ jonesExponent ρ z ζ) z₀ :=
    ((differentiableOn_jonesExponent h0 hζ).differentiableAt (hΩ.mem_nhds hz₀)).continuousAt
  have hne2 : z₀ - conj ζ ≠ 0 := by
    intro h
    have := add_im_le_norm_sub_conj z₀ ζ
    rw [h, norm_zero] at this
    linarith
  have hden : (z₀ - ζ) * (z₀ - conj ζ) ≠ 0 := mul_ne_zero (sub_ne_zero.2 hne) hne2
  have h1 : ContinuousAt (fun z : ℂ ↦ (z - ζ) * (z - conj ζ)) z₀ := by fun_prop
  have h2 : ContinuousAt (fun z : ℂ ↦ (ζ.im : ℂ) / ((z - ζ) * (z - conj ζ))) z₀ :=
    continuousAt_const.div h1 hden
  exact (continuousAt_const.mul h2).mul hE.cexp

/-- Jones' solution is continuous in `ℂ⁺` off a closed set carrying `ρ`. -/
theorem continuousOn_jonesSol (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {L : Set ℂ} (hL : IsClosed L)
    (hρL : ρ Lᶜ = 0) {θ : ℂ → ℂ} (hθ : Measurable θ) (hθ1 : ∀ z, ‖θ z‖ ≤ 1) :
    ContinuousOn (jonesSol ρ θ) ({z | 0 < z.im} ∩ Lᶜ) := by
  rintro z₀ ⟨hz₀, hz₀L⟩
  replace hz₀ : 0 < z₀.im := hz₀
  refine ContinuousAt.continuousWithinAt ?_
  have hL' : ∀ᵐ w ∂ρ, w ∈ L := by
    have : Lᶜᶜ ∈ ae ρ := compl_mem_ae_iff.2 hρL
    rwa [compl_compl] at this
  have h0 : ∀ᵐ w ∂ρ, 0 ≤ w.im := h10.mono fun w hw ↦ by linarith
  obtain ⟨r, hr, hrL⟩ := Metric.isOpen_iff.1 hL.isOpen_compl z₀ hz₀L
  have hΩ : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  refine continuousAt_of_dominated (bound := fun _ ↦ jonesConst ρ / (r / 2)) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun z ↦
      ((measurable_jonesKernel_mul ρ hθ).comp measurable_prodMk_left).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds z₀ (half_pos hr), hΩ.mem_nhds hz₀] with z hz hzim
    filter_upwards [hL', h10] with ζ hζL hζ10
    have hd : r / 2 ≤ ‖z - ζ‖ := by
      have h1 : r ≤ dist ζ z₀ := by
        by_contra h
        exact hrL (mem_ball.2 (not_le.1 h)) hζL
      have h2 := dist_triangle ζ z z₀
      rw [mem_ball] at hz
      rw [← dist_eq_norm, dist_comm]
      linarith
    rw [norm_mul]
    calc ‖jonesKernel ρ z ζ‖ * ‖θ ζ‖ ≤ ‖jonesKernel ρ z ζ‖ * 1 := by gcongr; exact hθ1 ζ
      _ ≤ jonesConst ρ / ‖z - ζ‖ := by
          rw [mul_one]; exact norm_jonesKernel_le_inv h10 (le_of_lt hzim) (by linarith)
      _ ≤ jonesConst ρ / (r / 2) :=
          div_le_div_of_nonneg_left (jonesConst_nonneg ρ) (half_pos hr) hd
  · filter_upwards [hL', h10] with ζ hζL hζ10
    have hne : z₀ ≠ ζ := fun h ↦ hz₀L (h ▸ hζL)
    exact (continuousAt_jonesKernel h0 (by linarith) hz₀ hne).mul continuousAt_const

end OCS
