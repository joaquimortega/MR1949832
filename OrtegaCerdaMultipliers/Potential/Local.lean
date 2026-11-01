import OrtegaCerdaMultipliers.Potential.Weyl

/-!
# M02 (Potentials) §4 — Smoothed point masses and local potentials

See `blueprint/M02_Potentials.md` §4.  Scaffold: statements, proofs `sorry`; the definitions are
real.  These replace the paper's global kernels `K[ν]` (doc §0).
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


/-- **The smoothed point mass.** `Δ_z G_s(z − ζ) = bumpKernel s (· − ζ) − δ_ζ` weakly. -/
-- FALSE?: the right-hand side parses as `∫ z, (bumpKernel s (z - ζ) * χ z - χ ζ)` (the body of
-- `∫` extends over `- χ ζ`).  That integrand is not integrable when `χ ζ ≠ 0`, so the right side
-- is `0`.  Counterexample: `ζ = 0`, `s = 1`, `χ` a smooth bump with `χ 0 = 1` supported in
-- `ball 0 (1/10)`; then the left side is `∫ k₁ χ - 1 ≤ 4/100 - 1 < 0`.  The intended statement,
-- with parentheses, is `integral_bumpPot_mul_laplacian'` (proved above).
theorem integral_bumpPot_mul_laplacian {s : ℝ} (hs : 0 < s) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (ζ : ℂ) :
    ∫ z, bumpPot s (z - ζ) * Laplacian.laplacian χ z =
      ∫ z, bumpKernel s (z - ζ) * χ z - χ ζ := sorry

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

theorem measurable_smoothedDensity (h : IsLocalPotData Ω σ s) :
    Measurable (smoothedDensity σ s) := sorry
theorem smoothedDensity_eq_zero (h : IsLocalPotData Ω σ s) {x : ℂ} (hx : x ∉ Ω) :
    smoothedDensity σ s x = 0 := sorry
theorem lintegral_smoothedDensity_lt_top (h : IsLocalPotData Ω σ s) {K : Set ℂ} (hK : K ⊆ Ω)
    (hKc : IsCompact K) : ∫⁻ x in K, smoothedDensity σ s x < ∞ := sorry
theorem measure_lt_top (h : IsLocalPotData Ω σ s) {K : Set ℂ} (hK : K ⊆ Ω)
    (hKc : IsCompact K) : σ K < ∞ := sorry
theorem localPot_nonneg (h : IsLocalPotData Ω σ s) (z : ℂ) : 0 ≤ localPot σ s z := sorry
theorem continuousOn_localPot (h : IsLocalPotData Ω σ s) : ContinuousOn (localPot σ s) Ω := sorry

/-- **`ΔV = σ̃ − σ` weakly.** -/
theorem integral_localPot_mul_laplacian (h : IsLocalPotData Ω σ s) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ Ω) :
    ∫ z, localPot σ s z * Laplacian.laplacian χ z =
      ∫ z, χ z ∂(volume.withDensity (smoothedDensity σ s)) - ∫ z, χ z ∂σ := sorry

end IsLocalPotData

/-- **Pointwise bound** (`C₀` from `exists_bumpPot_le`; universal). -/
theorem exists_localPot_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (Ω : Set ℂ) (σ : Measure ℂ) (s : ℂ → ℝ),
    IsLocalPotData Ω σ s → ∀ z : ℂ,
      ENNReal.ofReal (localPot σ s z) ≤
        ∫⁻ ζ in {ζ | dist z ζ < s ζ},
          ENNReal.ofReal ((4 * Real.pi)⁻¹ * (Real.log (s ζ ^ 2 / ‖z - ζ‖ ^ 2) + C₀)) ∂σ := sorry

end OC
