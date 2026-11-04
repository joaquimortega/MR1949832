import OrtegaCerdaMultipliers.Potential.Weyl

/-!
# M02 (Potentials) §4 — Smoothed point masses and local potentials

See `blueprint/M02_Potentials.md` §4.  All statements are proved except `integral_bumpPot_mul_laplacian`, which is false
as parsed (see the comment there); the corrected form is `integral_bumpPot_mul_laplacian'`.  These replace the paper's global kernels `K[ν]` (doc §0).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The potential `G_s ≥ 0` of `δ₀ − bumpKernel s`: `Δ G_s = bumpKernel s − δ₀`,
`G_s = 0` off `ball 0 s`. -/
def bumpPot (s : ℝ) (x : ℂ) : ℝ := -(4 * Real.pi)⁻¹ * wFun (s ^ 2 / 4) (s ^ 2) x

theorem bumpPot_nonneg {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : x ≠ 0) : 0 ≤ bumpPot s x := by
  unfold bumpPot
  have h1 : -(4 * Real.pi)⁻¹ ≤ 0 := by have := Real.pi_pos; simp only [neg_nonpos]; positivity
  exact mul_nonneg_of_nonpos_of_nonpos h1 (wFun_nonpos (bump_pos hs) (bump_lt hs) hx)

theorem bumpPot_eq_zero {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : s ≤ ‖x‖) : bumpPot s x = 0 := by
  unfold bumpPot
  rw [wFun_eq_zero (bump_pos hs) (bump_lt hs) (pow_le_pow_left₀ hs.le hx 2), mul_zero]

/-- `sFun (s²/4) s² t = sFun (1/4) 1 (t / s²) - log s²` for `s ≠ 0`. -/
theorem sFun_bump_eq {s : ℝ} (hs : s ≠ 0) (t : ℝ) :
    sFun (s ^ 2 / 4) (s ^ 2) t = sFun (1 / 4) 1 (t / s ^ 2) - Real.log (s ^ 2) := by
  have h := sFun_scale (a := 1 / 4) (b := 1) (by norm_num) (by norm_num) (abs_pos.2 hs) t
  rw [sq_abs] at h
  rw [show s ^ 2 / 4 = s ^ 2 * (1 / 4) by ring, ← h, mul_one]

theorem bumpPot_eq {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : x ≠ 0) :
    bumpPot s x = (4 * Real.pi)⁻¹ *
      (Real.log (s ^ 2 / ‖x‖ ^ 2) - sFun (1 / 4) 1 (‖x‖ ^ 2 / s ^ 2)) := by
  have hW : wFun (s ^ 2 / 4) (s ^ 2) x =
      Real.log (‖x‖ ^ 2) + sFun (s ^ 2 / 4) (s ^ 2) (‖x‖ ^ 2) := rfl
  have hx2 : ‖x‖ ^ 2 ≠ 0 := by positivity
  have hs2 : s ^ 2 ≠ 0 := by positivity
  unfold bumpPot
  rw [hW, sFun_bump_eq hs.ne', Real.log_div hs2 hx2]
  ring

theorem exists_bumpPot_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ s : ℝ, 0 < s → ∀ x : ℂ, x ≠ 0 → ‖x‖ < s →
    bumpPot s x ≤ (4 * Real.pi)⁻¹ * (Real.log (s ^ 2 / ‖x‖ ^ 2) + C₀) := by
  obtain ⟨C, hC⟩ := exists_abs_sFun_le (a := 1 / 4) (b := 1) (by norm_num) (by norm_num) 1
  refine ⟨max C 0, le_max_right _ _, fun s hs x hx hxs ↦ ?_⟩
  rw [bumpPot_eq hs hx]
  have ht : ‖x‖ ^ 2 / s ^ 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one (by positivity)]; nlinarith [norm_nonneg x]⟩
  have h1 := (abs_le.1 (hC _ ht)).1
  have h2 := le_max_left C 0
  have hπ : 0 ≤ (4 * Real.pi)⁻¹ := by have := Real.pi_pos; positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hπ

theorem continuousOn_bumpPot_uncurry :
    ContinuousOn (Function.uncurry bumpPot) {p : ℝ × ℂ | 0 < p.1 ∧ p.2 ≠ 0} := by
  have hS : Continuous (sFun (1 / 4) 1) :=
    (contDiff_sFun (a := 1 / 4) (b := 1) (by norm_num) (by norm_num)).continuous
  have h : ContinuousOn (fun p : ℝ × ℂ ↦ (4 * Real.pi)⁻¹ *
      (Real.log (p.1 ^ 2 / ‖p.2‖ ^ 2) - sFun (1 / 4) 1 (‖p.2‖ ^ 2 / p.1 ^ 2)))
      {p : ℝ × ℂ | 0 < p.1 ∧ p.2 ≠ 0} := by
    refine continuousOn_const.mul (ContinuousOn.sub ?_ ?_)
    · refine ContinuousOn.log ?_ fun p hp ↦ ?_
      · exact ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp ↦ by
          have := hp.2; positivity
      · have := hp.1; have := hp.2; positivity
    · exact hS.comp_continuousOn (ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp ↦ by
        have := hp.1; positivity)
  refine h.congr fun p hp ↦ ?_
  exact bumpPot_eq hp.1 hp.2

theorem measurable_bumpPot : Measurable (Function.uncurry bumpPot) := by
  have hS : Continuous (sFun (1 / 4) 1) :=
    (contDiff_sFun (a := 1 / 4) (b := 1) (by norm_num) (by norm_num)).continuous
  have h0 : ∀ t, sFun (0 ^ 2 / 4) (0 ^ 2) t = 0 := fun t ↦ by
    simp [sFun, sFn, gFn, planeProfile, profMass]
  have e : Function.uncurry bumpPot = fun p : ℝ × ℂ ↦ -(4 * Real.pi)⁻¹ *
      (Real.log (‖p.2‖ ^ 2) + (if p.1 = 0 then 0 else
        sFun (1 / 4) 1 (‖p.2‖ ^ 2 / p.1 ^ 2) - Real.log (p.1 ^ 2))) := by
    ext p
    simp only [Function.uncurry, bumpPot]
    have hW : wFun (p.1 ^ 2 / 4) (p.1 ^ 2) p.2 =
        Real.log (‖p.2‖ ^ 2) + sFun (p.1 ^ 2 / 4) (p.1 ^ 2) (‖p.2‖ ^ 2) := rfl
    rw [hW]
    split_ifs with hp
    · rw [hp, h0]
    · rw [sFun_bump_eq hp]
  rw [e]
  refine measurable_const.mul ((Real.measurable_log.comp (by fun_prop)).add ?_)
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const ?_
  exact (hS.measurable.comp (by fun_prop)).sub (Real.measurable_log.comp (by fun_prop))

theorem measurable_bumpPot_apply (s : ℝ) : Measurable (bumpPot s) := by
  have h : Measurable (fun x : ℂ ↦ Function.uncurry bumpPot (s, x)) :=
    measurable_bumpPot.comp (measurable_const.prodMk measurable_id)
  exact h

/-- Scaling: `bumpPot s x = bumpPot 1 (s⁻¹ • x)` for `x ≠ 0`. -/
theorem bumpPot_eq_bumpPot_one {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : x ≠ 0) :
    bumpPot s x = bumpPot 1 (s⁻¹ • x) := by
  have hx' : s⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero hs.ne') hx
  rw [bumpPot_eq hs hx, bumpPot_eq one_pos hx']
  have hn : ‖s⁻¹ • x‖ = ‖x‖ / s := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_eq_div]
  rw [hn]
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  congr 2
  · congr 1; field_simp
  · congr 1; field_simp

theorem integrable_bumpPot_one : Integrable (bumpPot 1) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_bumpPot_le
  set g : ℂ → ℝ := (closedBall (0 : ℂ) 1).indicator
    fun x ↦ (4 * Real.pi)⁻¹ * (2 * |Real.log ‖x‖| + C₀) with hg
  have hgi : Integrable g := by
    refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
    have h1 : IntegrableOn (fun x : ℂ ↦ Real.log ‖x‖) (closedBall 0 1) := by
      have := integrableOn_log_norm_sub_closedBall (0 : ℂ) zero_le_one
      simp only [sub_zero] at this
      exact this
    have h2 : IntegrableOn (fun _ : ℂ ↦ C₀) (closedBall 0 1) :=
      integrableOn_const (measure_closedBall_lt_top).ne
    exact ((h1.abs.const_mul 2).add h2).const_mul _
  have hm : Measurable (bumpPot 1) := measurable_bumpPot_apply 1
  refine Integrable.mono' hgi hm.aestronglyMeasurable ?_
  filter_upwards [Measure.ae_ne volume 0] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (bumpPot_nonneg one_pos hx)]
  rcases le_or_gt 1 ‖x‖ with h1 | h1
  · rw [bumpPot_eq_zero one_pos h1]
    by_cases hxb : x ∈ closedBall (0 : ℂ) 1
    · rw [hg, indicator_of_mem hxb]
      have hπ : 0 ≤ (4 * Real.pi)⁻¹ := by have := Real.pi_pos; positivity
      have : 0 ≤ 2 * |Real.log ‖x‖| + C₀ := by have := abs_nonneg (Real.log ‖x‖); linarith
      exact mul_nonneg hπ this
    · rw [hg, indicator_of_notMem hxb]
  · have hxb : x ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right]; exact h1.le
    rw [hg, indicator_of_mem hxb]
    refine (hC 1 one_pos x hx h1).trans ?_
    have hπ : 0 ≤ (4 * Real.pi)⁻¹ := by have := Real.pi_pos; positivity
    refine mul_le_mul_of_nonneg_left ?_ hπ
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [one_pow, Real.log_div one_ne_zero (by positivity), Real.log_one, zero_sub, Real.log_pow]
    have := neg_abs_le (Real.log ‖x‖)
    push_cast
    linarith

theorem exists_integral_abs_bumpPot_le : ∃ C₁ : ℝ, ∀ s : ℝ, 0 < s →
    Integrable (bumpPot s) ∧ ∫ x, |bumpPot s x| ≤ C₁ * s ^ 2 := by
  refine ⟨∫ x, |bumpPot 1 x|, fun s hs ↦ ?_⟩
  have hae : (fun x ↦ bumpPot 1 (s⁻¹ • x)) =ᵐ[volume] bumpPot s := by
    filter_upwards [Measure.ae_ne volume 0] with x hx
    exact (bumpPot_eq_bumpPot_one hs hx).symm
  have hint : Integrable (bumpPot s) :=
    (integrable_bumpPot_one.comp_smul (inv_ne_zero hs.ne')).congr hae
  refine ⟨hint, le_of_eq ?_⟩
  have hae' : (fun x ↦ |bumpPot 1 (s⁻¹ • x)|) =ᵐ[volume] fun x ↦ |bumpPot s x| := by
    filter_upwards [hae] with x hx
    rw [hx]
  rw [← integral_congr_ae hae', Measure.integral_comp_smul volume (fun x ↦ |bumpPot 1 x|),
    Complex.finrank_real_complex, smul_eq_mul, inv_pow, inv_inv, abs_of_pos (by positivity),
    mul_comm]

/-- **The smoothed point mass** (corrected form of `integral_bumpPot_mul_laplacian`, with the
parentheses that the statement needs): `Δ_z G_s(z − ζ) = bumpKernel s (· − ζ) − δ_ζ` weakly. -/
theorem integral_bumpPot_mul_laplacian' {s : ℝ} (hs : 0 < s) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (ζ : ℂ) :
    ∫ z, bumpPot s (z - ζ) * Laplacian.laplacian χ z =
      (∫ z, bumpKernel s (z - ζ) * χ z) - χ ζ := by
  have hΔc := continuous_laplacian hχ
  have hΔs := hasCompactSupport_laplacian hc
  have hlogint : Integrable (fun z ↦ Real.log (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z) := by
    simpa [smul_eq_mul] using
      (locallyIntegrable_log_normSq_sub ζ).integrable_smul_right_of_hasCompactSupport hΔc hΔs
  have hSint : Integrable
      (fun z ↦ sFun (s ^ 2 / 4) (s ^ 2) (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z) :=
    (((contDiff_sFun (bump_pos hs) (bump_lt hs)).continuous.comp
      ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2)).mul
        hΔc).integrable_of_hasCompactSupport hΔs.mul_left
  have e : (fun z ↦ bumpPot s (z - ζ) * Laplacian.laplacian χ z) = fun z ↦
      -(4 * Real.pi)⁻¹ * (Real.log (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z +
        sFun (s ^ 2 / 4) (s ^ 2) (‖z - ζ‖ ^ 2) * Laplacian.laplacian χ z) := by
    ext z
    simp only [bumpPot]
    rw [show wFun (s ^ 2 / 4) (s ^ 2) (z - ζ) =
      Real.log (‖z - ζ‖ ^ 2) + sFun (s ^ 2 / 4) (s ^ 2) (‖z - ζ‖ ^ 2) from rfl]
    ring
  rw [e, integral_const_mul, integral_add hlogint hSint,
    integral_log_normSq_sub_mul_laplacian hχ hc ζ, integral_sFun_mul_laplacian hs hχ hc ζ]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [bumpKernel]
  field_simp
  ring


-- (`integral_bumpPot_mul_laplacian` was removed by the coordinator: as written, `∫ z, a - b`
-- parses as `∫ z, (a - b)`, which made it false; the intended statement is
-- `integral_bumpPot_mul_laplacian'`. NOTEBOOK I-03.)

/-- Density of the smoothed measure `σ̃ = ∫ bumpKernel_{s(ζ)}(· − ζ) dσ(ζ)`. -/
def smoothedDensity (σ : Measure ℂ) (s : ℂ → ℝ) (x : ℂ) : ℝ≥0∞ :=
  ∫⁻ ζ, ENNReal.ofReal (bumpKernel (s ζ) (x - ζ)) ∂σ

/-- The local potential `V(z) = ∫ G_{s(ζ)}(z − ζ) dσ(ζ)`, with `ΔV = σ̃ − σ`. -/
def localPot (σ : Measure ℂ) (s : ℂ → ℝ) (z : ℂ) : ℝ :=
  ∫ ζ, bumpPot (s ζ) (z - ζ) ∂σ

/-- Standing hypotheses for a local potential on the open set `Ω`. -/
structure IsLocalPotData (Ω : Set ℂ) (σ : Measure ℂ) (s : ℂ → ℝ) : Prop where
  isOpen : IsOpen Ω
  measurable : Measurable s
  pos : ∀ ζ ∈ Ω, 0 < s ζ
  bdd : ∃ S : ℝ, ∀ ζ, s ζ ≤ S
  ball_subset : ∀ ζ ∈ Ω, ball ζ (s ζ) ⊆ Ω
  carried : σ Ωᶜ = 0
  sFinite : SFinite σ
  noAtoms : ∀ z, σ {z} = 0
  locFin : ∀ K ⊆ Ω, IsCompact K → σ {ζ | ∃ z ∈ K, dist z ζ < s ζ} < ∞
  logSmall : ∀ K ⊆ Ω, IsCompact K → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
    ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂σ ≤ ENNReal.ofReal η

namespace IsLocalPotData
variable {Ω : Set ℂ} {σ : Measure ℂ} {s : ℂ → ℝ}

theorem ae_mem (h : IsLocalPotData Ω σ s) : ∀ᵐ ζ ∂σ, ζ ∈ Ω := by
  rw [ae_iff]; exact h.carried

theorem ae_ne (h : IsLocalPotData Ω σ s) (z : ℂ) : ∀ᵐ ζ ∂σ, ζ ≠ z := by
  rw [ae_iff]
  simpa using h.noAtoms z

/-- The set `A_K = {ζ | ∃ z ∈ K, dist z ζ < s ζ}` is measurable for compact `K`. -/
theorem measurableSet_nbhd (h : IsLocalPotData Ω σ s) {K : Set ℂ} (hKc : IsCompact K) :
    MeasurableSet {ζ | ∃ z ∈ K, dist z ζ < s ζ} := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have e : {ζ | ∃ z ∈ K, dist z ζ < s ζ} = {ζ | infDist ζ K < s ζ} := by
    ext ζ
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨z, hz, hd⟩
      exact (infDist_le_dist_of_mem hz).trans_lt (by rwa [dist_comm])
    · intro hd
      obtain ⟨z, hz, hzd⟩ := hKc.exists_infDist_eq_dist hne ζ
      exact ⟨z, hz, by rwa [dist_comm, ← hzd]⟩
  rw [e]
  exact measurableSet_lt (continuous_infDist_pt K).measurable h.measurable

theorem measurable_kernel_prod (h : IsLocalPotData Ω σ s) :
    Measurable (fun p : ℂ × ℂ ↦ bumpKernel (s p.2) (p.1 - p.2)) := by
  have : Measurable (fun p : ℂ × ℂ ↦ Function.uncurry bumpKernel (s p.2, p.1 - p.2)) :=
    measurable_bumpKernel.comp
      ((h.measurable.comp measurable_snd).prodMk (measurable_fst.sub measurable_snd))
  exact this

theorem measurable_bumpPot_prod (h : IsLocalPotData Ω σ s) :
    Measurable (fun p : ℂ × ℂ ↦ bumpPot (s p.2) (p.1 - p.2)) := by
  have : Measurable (fun p : ℂ × ℂ ↦ Function.uncurry bumpPot (s p.2, p.1 - p.2)) :=
    measurable_bumpPot.comp
      ((h.measurable.comp measurable_snd).prodMk (measurable_fst.sub measurable_snd))
  exact this

theorem measurable_smoothedDensity (h : IsLocalPotData Ω σ s) :
    Measurable (smoothedDensity σ s) := by
  have := h.sFinite
  exact (ENNReal.measurable_ofReal.comp h.measurable_kernel_prod).lintegral_prod_right'

theorem smoothedDensity_eq_zero (h : IsLocalPotData Ω σ s) {x : ℂ} (hx : x ∉ Ω) :
    smoothedDensity σ s x = 0 := by
  unfold smoothedDensity
  rw [lintegral_congr_ae (g := fun _ ↦ 0) ?_, lintegral_zero]
  filter_upwards [h.ae_mem] with ζ hζ
  have hd : s ζ ≤ ‖x - ζ‖ := by
    by_contra hcon
    push Not at hcon
    exact hx (h.ball_subset ζ hζ (by rw [mem_ball, dist_eq_norm]; exact hcon))
  simp [bumpKernel_eq_zero (h.pos ζ hζ) hd]

/-- `∫⁻_S k_r(x − ζ) dx ≤ 1`. -/
theorem lintegral_ofReal_bumpKernel_le_one {r : ℝ} (hr : 0 < r) (ζ : ℂ) (S : Set ℂ) :
    ∫⁻ x in S, ENNReal.ofReal (bumpKernel r (x - ζ)) ≤ 1 := by
  have hint : Integrable (fun x ↦ bumpKernel r (x - ζ)) :=
    ((contDiff_bumpKernel r).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_bumpKernel hr)).comp_sub_right ζ
  calc ∫⁻ x in S, ENNReal.ofReal (bumpKernel r (x - ζ))
      ≤ ∫⁻ x, ENNReal.ofReal (bumpKernel r (x - ζ)) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ x, bumpKernel r (x - ζ)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun x ↦ bumpKernel_nonneg hr _)).symm
    _ = 1 := by
        rw [show (∫ x, bumpKernel r (x - ζ)) = 1 from integral_kernel_bump_sub hr ζ]
        simp

theorem lintegral_smoothedDensity_lt_top (h : IsLocalPotData Ω σ s) {K : Set ℂ} (hK : K ⊆ Ω)
    (hKc : IsCompact K) : ∫⁻ x in K, smoothedDensity σ s x < ∞ := by
  have := h.sFinite
  set A := {ζ | ∃ z ∈ K, dist z ζ < s ζ}
  have hm := ENNReal.measurable_ofReal.comp h.measurable_kernel_prod
  calc ∫⁻ x in K, smoothedDensity σ s x
      = ∫⁻ x in K, ∫⁻ ζ, ENNReal.ofReal (bumpKernel (s ζ) (x - ζ)) ∂σ := rfl
    _ = ∫⁻ ζ, (∫⁻ x in K, ENNReal.ofReal (bumpKernel (s ζ) (x - ζ))) ∂σ :=
        lintegral_lintegral_swap (f := fun x ζ ↦ ENNReal.ofReal (bumpKernel (s ζ) (x - ζ)))
          (μ := volume.restrict K) (ν := σ) hm.aemeasurable
    _ ≤ ∫⁻ ζ, A.indicator 1 ζ ∂σ := by
        refine lintegral_mono_ae ?_
        filter_upwards [h.ae_mem] with ζ hζ
        by_cases hA : ζ ∈ A
        · rw [indicator_of_mem hA, Pi.one_apply]
          exact lintegral_ofReal_bumpKernel_le_one (h.pos ζ hζ) ζ K
        · rw [indicator_of_notMem hA]
          refine le_of_eq ?_
          rw [← lintegral_zero (μ := volume.restrict K)]
          refine setLIntegral_congr_fun hKc.measurableSet fun x hx ↦ ?_
          have hd : s ζ ≤ ‖x - ζ‖ := by
            by_contra hcon
            push Not at hcon
            exact hA ⟨x, hx, by rwa [dist_eq_norm]⟩
          simp [bumpKernel_eq_zero (h.pos ζ hζ) hd]
    _ ≤ ∫⁻ ζ in A, 1 ∂σ := lintegral_indicator_le _ _
    _ = σ A := by rw [setLIntegral_const, one_mul]
    _ < ∞ := h.locFin K hK hKc

theorem measure_lt_top (h : IsLocalPotData Ω σ s) {K : Set ℂ} (hK : K ⊆ Ω)
    (hKc : IsCompact K) : σ K < ∞ :=
  (measure_mono (show K ⊆ {ζ | ∃ z ∈ K, dist z ζ < s ζ} from
    fun ζ hζ ↦ ⟨ζ, hζ, by rw [dist_self]; exact h.pos ζ (hK hζ)⟩)).trans_lt (h.locFin K hK hKc)

theorem localPot_nonneg (h : IsLocalPotData Ω σ s) (z : ℂ) : 0 ≤ localPot σ s z := by
  unfold localPot
  refine integral_nonneg_of_ae ?_
  filter_upwards [h.ae_mem, h.ae_ne z] with ζ hζ hζz
  exact bumpPot_nonneg (h.pos ζ hζ) (sub_ne_zero.2 hζz.symm)

/-- Pointwise bound on the singular part: for `‖z − ζ‖ < ρ ≤ 1`,
`G_{s ζ}(z − ζ) ≤ Λ (1 + log (1/‖z − ζ‖))`. -/
theorem bumpPot_le_log_bound {C₀ S r : ℝ} (hC : ∀ s : ℝ, 0 < s → ∀ x : ℂ, x ≠ 0 → ‖x‖ < s →
      bumpPot s x ≤ (4 * Real.pi)⁻¹ * (Real.log (s ^ 2 / ‖x‖ ^ 2) + C₀))
    (hC₀ : 0 ≤ C₀) (hr : 0 < r) (hrS : r ≤ S) {x : ℂ} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    bumpPot r x ≤ (4 * Real.pi)⁻¹ * (|Real.log (S ^ 2)| + C₀ + 2) *
      (1 + Real.log (1 / ‖x‖)) := by
  have hd : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hL : 0 ≤ Real.log (1 / ‖x‖) :=
    Real.log_nonneg (by rw [le_div_iff₀ hd, one_mul]; exact hx1.le)
  have hπ : 0 ≤ (4 * Real.pi)⁻¹ := by have := Real.pi_pos; positivity
  rcases le_or_gt r ‖x‖ with hrx | hrx
  · rw [bumpPot_eq_zero hr hrx]
    have : 0 ≤ |Real.log (S ^ 2)| + C₀ + 2 := by positivity
    positivity
  · refine (hC r hr x hx hrx).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hπ
    have h1 : Real.log (r ^ 2 / ‖x‖ ^ 2) = Real.log (r ^ 2) + 2 * Real.log (1 / ‖x‖) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, one_div,
        Real.log_inv]
      push_cast; ring
    have h2 : Real.log (r ^ 2) ≤ Real.log (S ^ 2) :=
      Real.log_le_log (by positivity) (pow_le_pow_left₀ hr.le hrS 2)
    have h3 := le_abs_self (Real.log (S ^ 2))
    rw [h1]
    nlinarith [abs_nonneg (Real.log (S ^ 2))]

theorem continuousOn_localPot (h : IsLocalPotData Ω σ s) : ContinuousOn (localPot σ s) Ω := by
  have := h.sFinite
  intro z₀ hz₀
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨C₀, hC₀, hC⟩ := exists_bumpPot_le
  obtain ⟨S, hS⟩ := h.bdd
  obtain ⟨r₀, hr₀, hr₀Ω⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ closedBall z₀ r₀ ⊆ Ω := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 h.isOpen z₀ hz₀
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  set K₀ := closedBall z₀ r₀ with hK₀
  have hK₀c : IsCompact K₀ := isCompact_closedBall _ _
  set A := {ζ | ∃ z ∈ K₀, dist z ζ < s ζ} with hAdef
  have hA : MeasurableSet A := h.measurableSet_nbhd hK₀c
  have hσA : σ A < ∞ := h.locFin K₀ hr₀Ω hK₀c
  set f : ℂ → ℂ → ℝ := fun z ζ ↦ bumpPot (s ζ) (z - ζ) with hfdef
  have hfm : ∀ z, Measurable (f z) := fun z ↦ by
    have : Measurable (fun ζ : ℂ ↦ (fun p : ℂ × ℂ ↦ bumpPot (s p.2) (p.1 - p.2)) (z, ζ)) :=
      h.measurable_bumpPot_prod.comp (measurable_const.prodMk measurable_id)
    exact this
  rw [Metric.continuousAt_iff]
  intro ε hε
  set Λ := (4 * Real.pi)⁻¹ * (|Real.log (S ^ 2)| + C₀ + 2) with hΛdef
  have hΛ : 0 ≤ Λ := by have := Real.pi_pos; positivity
  set η := ε / (3 * (Λ + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hΛη : Λ * η < ε / 3 := by
    rw [hηdef, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨ρ, hρ, hρ1, hlog⟩ := h.logSmall K₀ hr₀Ω hK₀c η hη
  set T := max 0 ((4 * Real.pi)⁻¹ * (Real.log (S ^ 2 / ρ ^ 2) + C₀)) with hTdef
  have hT0 : 0 ≤ T := le_max_left _ _
  set g : ℂ → ℂ → ℝ := fun z ζ ↦ min (f z ζ) T with hgdef
  set t : ℂ → ℂ → ℝ := fun z ζ ↦ f z ζ - min (f z ζ) T with htdef
  set φ : ℂ → ℂ → ℝ := fun z ↦ (ball z ρ).indicator fun ζ ↦ Λ * (1 + Real.log (1 / ‖z - ζ‖))
    with hφdef
  -- basic a.e. facts
  have hae : ∀ z, ∀ᵐ ζ ∂σ, ζ ∈ Ω ∧ ζ ≠ z := fun z ↦ by
    filter_upwards [h.ae_mem, h.ae_ne z] with ζ h1 h2 using ⟨h1, h2⟩
  have hf0 : ∀ z ζ, ζ ∈ Ω → ζ ≠ z → 0 ≤ f z ζ := fun z ζ hζ hne ↦
    bumpPot_nonneg (h.pos ζ hζ) (sub_ne_zero.2 hne.symm)
  -- bound for `g`
  have hg_bound : ∀ z ∈ K₀, ∀ᵐ ζ ∂σ, ‖g z ζ‖ ≤ A.indicator (fun _ ↦ T) ζ := by
    intro z hz
    filter_upwards [hae z] with ζ ⟨hζ, hne⟩
    have hmin0 : 0 ≤ g z ζ := le_min (hf0 z ζ hζ hne) hT0
    rw [Real.norm_eq_abs, abs_of_nonneg hmin0]
    by_cases hζA : ζ ∈ A
    · rw [indicator_of_mem hζA]; exact min_le_right _ _
    · rw [indicator_of_notMem hζA]
      have hd : s ζ ≤ ‖z - ζ‖ := by
        rw [← dist_eq_norm]; by_contra hcon; exact hζA ⟨z, hz, not_le.1 hcon⟩
      simp only [hgdef, hfdef]
      rw [bumpPot_eq_zero (h.pos ζ hζ) hd, min_eq_left hT0]
  -- bound for the tail `t`
  have ht_bound : ∀ z ∈ K₀, ∀ᵐ ζ ∂σ, 0 ≤ t z ζ ∧ t z ζ ≤ φ z ζ := by
    intro z hz
    filter_upwards [hae z] with ζ ⟨hζ, hne⟩
    have hf0' := hf0 z ζ hζ hne
    have hsζ := h.pos ζ hζ
    have hne' : z - ζ ≠ 0 := sub_ne_zero.2 hne.symm
    refine ⟨sub_nonneg.2 (min_le_left _ _), ?_⟩
    by_cases hb : ‖z - ζ‖ < ρ
    · have hmem : ζ ∈ ball z ρ := by rw [mem_ball, dist_comm, dist_eq_norm]; exact hb
      simp only [hφdef, indicator_of_mem hmem]
      calc t z ζ ≤ f z ζ := sub_le_self _ (le_min hf0' hT0)
        _ ≤ Λ * (1 + Real.log (1 / ‖z - ζ‖)) :=
          bumpPot_le_log_bound hC hC₀ hsζ (hS ζ) hne' (hb.trans_le hρ1)
    · have hnmem : ζ ∉ ball z ρ := by
        rw [mem_ball, dist_comm, dist_eq_norm]; exact hb
      simp only [hφdef, indicator_of_notMem hnmem]
      have hfT : f z ζ ≤ T := by
        rcases le_or_gt (s ζ) ‖z - ζ‖ with hd | hd
        · simp only [hfdef]; rw [bumpPot_eq_zero hsζ hd]; exact hT0
        · refine ((hC (s ζ) hsζ (z - ζ) hne' hd).trans ?_).trans (le_max_right _ _)
          have hπ : 0 ≤ (4 * Real.pi)⁻¹ := by have := Real.pi_pos; positivity
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hπ
          have hd0 : 0 < ‖z - ζ‖ := norm_pos_iff.2 hne'
          refine Real.log_le_log (by positivity) ?_
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : s ζ ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hsζ.le (hS ζ) 2
          have h2 : ρ ^ 2 ≤ ‖z - ζ‖ ^ 2 := pow_le_pow_left₀ hρ.le (not_lt.1 hb) 2
          nlinarith [pow_pos hρ 2, pow_pos hsζ 2]
      simp only [htdef, min_eq_left hfT, sub_self, le_refl]
  -- the dominating function of the tail
  have hφ_nonneg : ∀ z ζ, 0 ≤ φ z ζ := by
    intro z ζ
    simp only [hφdef]
    by_cases hmem : ζ ∈ ball z ρ
    · rw [indicator_of_mem hmem]
      refine mul_nonneg hΛ ?_
      by_cases hzζ : z - ζ = 0
      · simp [hzζ]
      · have hd : 0 < ‖z - ζ‖ := norm_pos_iff.2 hzζ
        have hd1 : ‖z - ζ‖ < 1 := by
          rw [mem_ball, dist_comm, dist_eq_norm] at hmem; linarith
        have : 0 ≤ Real.log (1 / ‖z - ζ‖) :=
          Real.log_nonneg (by rw [le_div_iff₀ hd, one_mul]; exact hd1.le)
        linarith
    · rw [indicator_of_notMem hmem]
  have hφm : ∀ z, Measurable (φ z) := fun z ↦ by
    refine Measurable.indicator ?_ measurableSet_ball
    exact measurable_const.mul (measurable_const.add (Real.measurable_log.comp (by fun_prop)))
  have hφ_lint : ∀ z ∈ K₀, ∫⁻ ζ, ENNReal.ofReal (φ z ζ) ∂σ ≤ ENNReal.ofReal (Λ * η) := by
    intro z hz
    have e : (fun ζ ↦ ENNReal.ofReal (φ z ζ)) = (ball z ρ).indicator
        (fun ζ ↦ ENNReal.ofReal Λ * ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖))) := by
      ext ζ
      simp only [hφdef]
      by_cases hmem : ζ ∈ ball z ρ
      · rw [indicator_of_mem hmem, indicator_of_mem hmem, ENNReal.ofReal_mul hΛ]
      · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, ENNReal.ofReal_zero]
    rw [e, lintegral_indicator measurableSet_ball, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ENNReal.ofReal_mul hΛ]
    gcongr
    exact hlog z hz
  have hφi : ∀ z ∈ K₀, Integrable (φ z) σ := fun z hz ↦
    ⟨(hφm z).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall (hφ_nonneg z))).2 ((hφ_lint z hz).trans_lt ENNReal.ofReal_lt_top)⟩
  have hφ_int : ∀ z ∈ K₀, ∫ ζ, φ z ζ ∂σ ≤ Λ * η := by
    intro z hz
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (hφ_nonneg z))
      (hφm z).aestronglyMeasurable]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hφ_lint z hz)
    rwa [ENNReal.toReal_ofReal (mul_nonneg hΛ hη.le)] at this
  -- integrability of `g z`, `t z`
  have hAi : Integrable (A.indicator fun _ ↦ T) σ :=
    (integrable_indicator_iff hA).2 (integrableOn_const hσA.ne)
  have hgm : ∀ z, Measurable (g z) := fun z ↦ (hfm z).min measurable_const
  have hgi : ∀ z ∈ K₀, Integrable (g z) σ := fun z hz ↦
    Integrable.mono' hAi (hgm z).aestronglyMeasurable (hg_bound z hz)
  have hti : ∀ z ∈ K₀, Integrable (t z) σ := fun z hz ↦ by
    refine Integrable.mono' (hφi z hz) ((hfm z).sub (hgm z)).aestronglyMeasurable ?_
    filter_upwards [ht_bound z hz] with ζ ⟨h1, h2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg h1]; exact h2
  have ht_int : ∀ z ∈ K₀, 0 ≤ ∫ ζ, t z ζ ∂σ ∧ ∫ ζ, t z ζ ∂σ ≤ Λ * η := by
    intro z hz
    refine ⟨integral_nonneg_of_ae ?_, (integral_mono_ae (hti z hz) (hφi z hz) ?_).trans
      (hφ_int z hz)⟩
    · filter_upwards [ht_bound z hz] with ζ hζ using hζ.1
    · filter_upwards [ht_bound z hz] with ζ hζ using hζ.2
  have hsplit : ∀ z ∈ K₀, localPot σ s z = (∫ ζ, g z ζ ∂σ) + ∫ ζ, t z ζ ∂σ := by
    intro z hz
    rw [← integral_add (hgi z hz) (hti z hz)]
    simp only [localPot, hgdef, htdef, hfdef]
    congr 1; ext ζ; ring
  -- continuity of the truncated part
  have hcont : Tendsto (fun z ↦ ∫ ζ, g z ζ ∂σ) (𝓝 z₀) (𝓝 (∫ ζ, g z₀ ζ ∂σ)) := by
    refine tendsto_integral_filter_of_dominated_convergence _
      (Eventually.of_forall fun z ↦ (hgm z).aestronglyMeasurable) ?_ hAi ?_
    · filter_upwards [closedBall_mem_nhds z₀ hr₀] with z hz using hg_bound z hz
    · filter_upwards [hae z₀] with ζ ⟨hζ, hne⟩
      have hopen : IsOpen {p : ℝ × ℂ | 0 < p.1 ∧ p.2 ≠ 0} :=
        (isOpen_lt continuous_const continuous_fst).inter
          (isOpen_ne_fun continuous_snd continuous_const)
      have hmem : (s ζ, z₀ - ζ) ∈ {p : ℝ × ℂ | 0 < p.1 ∧ p.2 ≠ 0} :=
        ⟨h.pos ζ hζ, sub_ne_zero.2 hne.symm⟩
      have hca : ContinuousAt (Function.uncurry bumpPot) (s ζ, z₀ - ζ) :=
        continuousOn_bumpPot_uncurry.continuousAt (hopen.mem_nhds hmem)
      have hc2 : ContinuousAt (fun z : ℂ ↦ bumpPot (s ζ) (z - ζ)) z₀ :=
        hca.comp (f := fun z : ℂ ↦ (s ζ, z - ζ))
          (continuousAt_const.prodMk (continuousAt_id.sub continuousAt_const))
      exact Filter.Tendsto.min hc2.tendsto (tendsto_const_nhds (x := T))
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.tendsto_nhds_nhds.1 hcont (ε / 3) (by positivity)
  refine ⟨min δ₂ r₀, lt_min hδ₂ hr₀, fun z hz ↦ ?_⟩
  have hzK : z ∈ K₀ := by
    rw [hK₀, mem_closedBall]; exact (hz.trans_le (min_le_right _ _)).le
  have hz₀K : z₀ ∈ K₀ := mem_closedBall_self hr₀.le
  have h1 := hδ₂' (hz.trans_le (min_le_left _ _))
  rw [Real.dist_eq] at h1 ⊢
  rw [hsplit z hzK, hsplit z₀ hz₀K]
  obtain ⟨a1, a2⟩ := ht_int z hzK
  obtain ⟨b1, b2⟩ := ht_int z₀ hz₀K
  rw [abs_lt] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

/-- **`ΔV = σ̃ − σ` weakly.** -/
theorem integral_localPot_mul_laplacian (h : IsLocalPotData Ω σ s) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ Ω) :
    ∫ z, localPot σ s z * Laplacian.laplacian χ z =
      ∫ z, χ z ∂(volume.withDensity (smoothedDensity σ s)) - ∫ z, χ z ∂σ := by
  have := h.sFinite
  set K := tsupport χ with hKdef
  set A := {ζ | ∃ z ∈ K, dist z ζ < s ζ} with hAdef
  have hA : MeasurableSet A := h.measurableSet_nbhd hc
  have hσA : σ A < ∞ := h.locFin K hs hc
  have hKm : MeasurableSet K := (isClosed_tsupport χ).measurableSet
  obtain ⟨S, hS⟩ := h.bdd
  obtain ⟨C₁, hC₁⟩ := exists_integral_abs_bumpPot_le
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := (hC₁ 1 one_pos).2
    have h2 : 0 ≤ ∫ x, |bumpPot 1 x| := integral_nonneg fun _ ↦ abs_nonneg _
    nlinarith
  have hχc := hχ.continuous
  have hΔc := continuous_laplacian hχ
  have hΔs := hasCompactSupport_laplacian hc
  obtain ⟨M, hM⟩ := hΔc.bounded_above_of_compact_support hΔs
  obtain ⟨Mχ, hMχ⟩ := hχc.bounded_above_of_compact_support hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hfar : ∀ ζ ∈ Ω, ζ ∉ A → ∀ z ∈ K, s ζ ≤ ‖z - ζ‖ := fun ζ _ hζA z hz ↦ by
    by_contra hcon
    exact hζA ⟨z, hz, by rw [dist_eq_norm]; exact not_le.1 hcon⟩
  have hΔK : ∀ z, z ∉ K → Laplacian.laplacian χ z = 0 := fun z hz ↦
    laplacian_eq_zero_of_notMem_tsupport hz
  have hχK : ∀ z, z ∉ K → χ z = 0 := fun z hz ↦ image_eq_zero_of_notMem_tsupport hz
  -- the potential part: `F z ζ = G_{s ζ}(z − ζ) Δχ(z)`
  set F : ℂ → ℂ → ℝ := fun z ζ ↦ bumpPot (s ζ) (z - ζ) * Laplacian.laplacian χ z with hFdef
  have hFm : StronglyMeasurable (Function.uncurry F) :=
    (h.measurable_bumpPot_prod.mul (hΔc.measurable.comp measurable_fst)).stronglyMeasurable
  have hFint : ∀ ζ ∈ Ω, Integrable (fun z ↦ F z ζ) := fun ζ hζ ↦
    ((hC₁ (s ζ) (h.pos ζ hζ)).1.comp_sub_right ζ).mul_bdd hΔc.aestronglyMeasurable
      (Eventually.of_forall hM)
  have hFnorm : ∀ ζ ∈ Ω, ∫ z, ‖F z ζ‖ ≤ A.indicator (fun _ ↦ M * (C₁ * S ^ 2)) ζ := by
    intro ζ hζ
    have hsζ := h.pos ζ hζ
    by_cases hζA : ζ ∈ A
    · rw [indicator_of_mem hζA]
      calc ∫ z, ‖F z ζ‖ ≤ ∫ z, M * |bumpPot (s ζ) (z - ζ)| := by
            refine integral_mono (hFint ζ hζ).norm
              (((hC₁ (s ζ) hsζ).1.comp_sub_right ζ).abs.const_mul M) fun z ↦ ?_
            rw [hFdef, norm_mul, Real.norm_eq_abs, mul_comm]
            exact mul_le_mul_of_nonneg_right (hM z) (abs_nonneg _)
        _ = M * ∫ z, |bumpPot (s ζ) z| := by
            rw [integral_const_mul,
              integral_sub_right_eq_self (fun z ↦ |bumpPot (s ζ) z|) ζ]
        _ ≤ M * (C₁ * S ^ 2) := by
            refine mul_le_mul_of_nonneg_left ((hC₁ (s ζ) hsζ).2.trans ?_) hM0
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ hsζ.le (hS ζ) 2) hC₁0
    · rw [indicator_of_notMem hζA]
      refine le_of_eq ?_
      rw [← integral_zero ℂ ℝ]
      congr 1; ext z
      by_cases hz : z ∈ K
      · simp [hFdef, bumpPot_eq_zero hsζ (hfar ζ hζ hζA z hz)]
      · simp [hFdef, hΔK z hz]
  have hFint2 : Integrable (Function.uncurry F) (volume.prod σ) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [h.ae_mem] with ζ hζ using hFint ζ hζ
    · refine Integrable.mono' (g := A.indicator fun _ ↦ M * (C₁ * S ^ 2))
        ((integrable_indicator_iff hA).2 (integrableOn_const hσA.ne))
        (hFm.norm.integral_prod_left' (μ := volume)).aestronglyMeasurable ?_
      filter_upwards [h.ae_mem] with ζ hζ
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
      exact hFnorm ζ hζ
  -- the smoothed part: `H z ζ = k_{s ζ}(z − ζ) χ(z)`
  set H : ℂ → ℂ → ℝ := fun z ζ ↦ bumpKernel (s ζ) (z - ζ) * χ z with hHdef
  have hHm : StronglyMeasurable (Function.uncurry H) :=
    (h.measurable_kernel_prod.mul (hχc.measurable.comp measurable_fst)).stronglyMeasurable
  have hHint : ∀ ζ, Integrable (fun z ↦ H z ζ) := fun ζ ↦
    (((contDiff_bumpKernel _).continuous.comp
      (continuous_id.sub continuous_const)).mul hχc).integrable_of_hasCompactSupport hc.mul_left
  have hHnorm : ∀ ζ ∈ Ω, ∫ z, ‖H z ζ‖ ≤ A.indicator (fun _ ↦ Mχ) ζ := by
    intro ζ hζ
    have hsζ := h.pos ζ hζ
    by_cases hζA : ζ ∈ A
    · rw [indicator_of_mem hζA]
      calc ∫ z, ‖H z ζ‖ ≤ ∫ z, bumpKernel (s ζ) (z - ζ) * Mχ := by
            refine integral_mono (hHint ζ).norm
              ((((contDiff_bumpKernel _).continuous.integrable_of_hasCompactSupport
                (hasCompactSupport_bumpKernel hsζ)).comp_sub_right ζ).mul_const Mχ) fun z ↦ ?_
            rw [hHdef, norm_mul, Real.norm_eq_abs, abs_of_nonneg (bumpKernel_nonneg hsζ _)]
            exact mul_le_mul_of_nonneg_left (hMχ z) (bumpKernel_nonneg hsζ _)
        _ = Mχ := by
            rw [integral_mul_const,
              show (∫ z, bumpKernel (s ζ) (z - ζ)) = 1 from integral_kernel_bump_sub hsζ ζ,
              one_mul]
    · rw [indicator_of_notMem hζA]
      refine le_of_eq ?_
      rw [← integral_zero ℂ ℝ]
      congr 1; ext z
      by_cases hz : z ∈ K
      · simp [hHdef, bumpKernel_eq_zero hsζ (hfar ζ hζ hζA z hz)]
      · simp [hHdef, hχK z hz]
  have hHint2 : Integrable (Function.uncurry H) (volume.prod σ) := by
    rw [integrable_prod_iff' hHm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · exact ae_of_all _ hHint
    · refine Integrable.mono' (g := A.indicator fun _ ↦ Mχ)
        ((integrable_indicator_iff hA).2 (integrableOn_const hσA.ne))
        (hHm.norm.integral_prod_left' (μ := volume)).aestronglyMeasurable ?_
      filter_upwards [h.ae_mem] with ζ hζ
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
      exact hHnorm ζ hζ
  have hχσ : Integrable χ σ :=
    integrable_of_measure_tsupport_lt_top hχc hc (h.measure_lt_top hs hc)
  -- the density side
  set ρ := smoothedDensity σ s with hρ
  have hρm : Measurable ρ := h.measurable_smoothedDensity
  have hρlt : ∀ᵐ x ∂volume.restrict K, ρ x < ∞ :=
    ae_lt_top hρm (h.lintegral_smoothedDensity_lt_top hs hc).ne
  have hwd : ∫ z, χ z ∂(volume.withDensity ρ) = ∫ z, (ρ z).toReal * χ z := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ hχK x hx),
      restrict_withDensity hKm, integral_withDensity_eq_integral_toReal_smul hρm hρlt,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rfl
    · intro x hx
      rw [hχK x hx, smul_zero]
  have hinner : ∀ z, ∫ ζ, H z ζ ∂σ = (ρ z).toReal * χ z := by
    intro z
    rw [hHdef]
    simp only
    rw [integral_mul_const, integral_eq_lintegral_of_nonneg_ae]
    · rfl
    · filter_upwards [h.ae_mem] with ζ hζ using bumpKernel_nonneg (h.pos ζ hζ) _
    · exact (h.measurable_kernel_prod.comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  -- assemble
  calc ∫ z, localPot σ s z * Laplacian.laplacian χ z = ∫ z, ∫ ζ, F z ζ ∂σ := by
        congr 1; ext z
        rw [hFdef]
        simp only [localPot]
        rw [integral_mul_const]
    _ = ∫ ζ, (∫ z, F z ζ) ∂σ := integral_integral_swap hFint2
    _ = ∫ ζ, ((∫ z, H z ζ) - χ ζ) ∂σ := by
        refine integral_congr_ae ?_
        filter_upwards [h.ae_mem] with ζ hζ
        exact integral_bumpPot_mul_laplacian' (h.pos ζ hζ) hχ hc ζ
    _ = (∫ ζ, (∫ z, H z ζ) ∂σ) - ∫ ζ, χ ζ ∂σ :=
        integral_sub hHint2.integral_prod_right hχσ
    _ = (∫ z, ∫ ζ, H z ζ ∂σ) - ∫ ζ, χ ζ ∂σ := by rw [integral_integral_swap hHint2]
    _ = _ := by simp_rw [hinner, hwd]

end IsLocalPotData

/-- **Pointwise bound** (`C₀` from `exists_bumpPot_le`; universal). -/
theorem exists_localPot_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (Ω : Set ℂ) (σ : Measure ℂ) (s : ℂ → ℝ),
    IsLocalPotData Ω σ s → ∀ z : ℂ,
      ENNReal.ofReal (localPot σ s z) ≤
        ∫⁻ ζ in {ζ | dist z ζ < s ζ},
          ENNReal.ofReal ((4 * Real.pi)⁻¹ * (Real.log (s ζ ^ 2 / ‖z - ζ‖ ^ 2) + C₀)) ∂σ := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_bumpPot_le
  refine ⟨C₀, hC₀, fun Ω σ s h z ↦ ?_⟩
  set B := {ζ | dist z ζ < s ζ}
  have hB : MeasurableSet B := measurableSet_lt (measurable_const.dist measurable_id) h.measurable
  have hnn : 0 ≤ᵐ[σ] fun ζ ↦ bumpPot (s ζ) (z - ζ) := by
    filter_upwards [h.ae_mem, h.ae_ne z] with ζ hζ hζz
    exact bumpPot_nonneg (h.pos ζ hζ) (sub_ne_zero.2 hζz.symm)
  have h1 : ENNReal.ofReal (localPot σ s z) ≤ ∫⁻ ζ, ENNReal.ofReal (bumpPot (s ζ) (z - ζ)) ∂σ := by
    unfold localPot
    by_cases hint : Integrable (fun ζ ↦ bumpPot (s ζ) (z - ζ)) σ
    · rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
    · rw [integral_undef hint, ENNReal.ofReal_zero]
      exact bot_le
  refine h1.trans ?_
  rw [← lintegral_indicator hB]
  refine lintegral_mono_ae ?_
  filter_upwards [h.ae_mem, h.ae_ne z] with ζ hζ hζz
  have hne : z - ζ ≠ 0 := sub_ne_zero.2 hζz.symm
  by_cases hζB : ζ ∈ B
  · rw [indicator_of_mem hζB]
    have hlt : ‖z - ζ‖ < s ζ := by rw [← dist_eq_norm]; exact hζB
    exact ENNReal.ofReal_le_ofReal (hC (s ζ) (h.pos ζ hζ) (z - ζ) hne hlt)
  · rw [indicator_of_notMem hζB]
    have hge : s ζ ≤ ‖z - ζ‖ := by
      rw [← dist_eq_norm]; exact not_lt.1 hζB
    rw [bumpPot_eq_zero (h.pos ζ hζ) hge, ENNReal.ofReal_zero]

end OC
