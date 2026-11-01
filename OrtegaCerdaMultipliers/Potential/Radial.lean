import OrtegaCerdaMultipliers.Foundations.Basic
import OrtegaCerdaMultipliers.Foundations.Wirtinger
import OrtegaCerdaMultipliers.Foundations.Polar

/-!
# M02 (Potentials) — Smooth radial kernels and their logarithmic potentials

See `blueprint/M02_Potentials.md`.

**Provenance.** Copied from `BerndtssonOrtegaCerda/Potential/Radial.lean`
(BOC module M10, blueprint `M10_RadialPotential.md`) of the companion project
`../MR1340337` at commit `22104d9` (same author, Apache-2.0).  Changes: namespace
`BOC` → `OC`, imports adjusted.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate Topology

noncomputable section

namespace OC

/-! ## Generic profiles -/

/-- Mass function `m_p(t) = ∫₀ᵗ p` (mass of the radial measure in `{|z|² < t}`). -/
def massFn (p : ℝ → ℝ) (t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, p τ
/-- `g_p(t) = m_p(t)/t`, written smoothly: `∫₀¹ p(tu) du`. -/
def gFn (p : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..1, p (t * u)
/-- `S_p(t) = −log b + ∫ₜᵇ g_p`; equals `−log t` for `t ≥ b`. -/
def sFn (p : ℝ → ℝ) (b t : ℝ) : ℝ := -Real.log b + ∫ τ in t..b, gFn p τ
/-- The singular potential `w_p(z) = log|z|² + S_p(|z|²)`, with `Δ w_p = πδ₀ − p(|z|²)`. -/
def wFn (p : ℝ → ℝ) (b : ℝ) (z : ℂ) : ℝ := Real.log (‖z‖ ^ 2) + sFn p b (‖z‖ ^ 2)

/-- A profile: the standing hypotheses. -/
structure IsProfile (p : ℝ → ℝ) (b : ℝ) : Prop where
  pos : 0 < b
  smooth : ContDiff ℝ (⊤ : ℕ∞) p
  nonneg : ∀ t, 0 ≤ p t
  vanish : ∀ t, b ≤ t → p t = 0
  /-- `p` is constant near and below `0` (so `z ↦ p(|z|²)` and `gFn p` are smooth). -/
  const_near_zero : ∃ c > 0, ∀ t < c, p t = p 0
  mass : ∫ t in (0 : ℝ)..b, p t = 1

/-! ## Plane instance (parameters `0 < a < b`; `t` stands for `|z|²`) -/

/-- Smooth cut-off: `1` on `(-∞, a]`, `0` on `[b, ∞)`, nonincreasing. -/
def cutProfile (a b t : ℝ) : ℝ := 1 - Real.smoothTransition ((t - a) / (b - a))
/-- `∫₀ᵇ σ ∈ [a, b]`. -/
def profMass (a b : ℝ) : ℝ := ∫ t in (0 : ℝ)..b, cutProfile a b t
def planeProfile (a b : ℝ) (t : ℝ) : ℝ := cutProfile a b t / profMass a b
/-- The smooth radial kernel `ρ(z) = σ(|z|²)/(π ∫σ)`, of total mass 1. -/
def kernel (a b : ℝ) (z : ℂ) : ℝ := planeProfile a b (‖z‖ ^ 2) / Real.pi
def gFun (a b : ℝ) : ℝ → ℝ := gFn (planeProfile a b)
def sFun (a b : ℝ) : ℝ → ℝ := sFn (planeProfile a b) b
def wFun (a b : ℝ) : ℂ → ℝ := wFn (planeProfile a b) b

/-! ## Statements -/

variable {a b : ℝ}

theorem contDiff_cutProfile (hab : a < b) : ContDiff ℝ (⊤ : ℕ∞) (cutProfile a b) := by
  unfold cutProfile
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _))
theorem cutProfile_of_le (hab : a < b) {t : ℝ} (ht : t ≤ a) : cutProfile a b t = 1 := by
  unfold cutProfile
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by linarith)), sub_zero]
theorem cutProfile_of_ge (hab : a < b) {t : ℝ} (ht : b ≤ t) : cutProfile a b t = 0 := by
  unfold cutProfile
  rw [Real.smoothTransition.one_of_one_le, sub_self]
  rw [le_div_iff₀ (by linarith)]; linarith
theorem cutProfile_mem_Icc (hab : a < b) (t : ℝ) : cutProfile a b t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold cutProfile
  have h1 := Real.smoothTransition.nonneg ((t - a) / (b - a))
  have h2 := Real.smoothTransition.le_one ((t - a) / (b - a))
  constructor <;> linarith
theorem antitone_cutProfile (hab : a < b) : Antitone (cutProfile a b) := by
  intro s t hst
  unfold cutProfile
  have : (s - a) / (b - a) ≤ (t - a) / (b - a) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  linarith [Real.smoothTransition.monotone this]
theorem continuous_cutProfile (hab : a < b) : Continuous (cutProfile a b) :=
  (contDiff_cutProfile hab).continuous

theorem le_profMass (ha : 0 < a) (hab : a < b) : a ≤ profMass a b := by
  unfold profMass
  have hc := continuous_cutProfile hab
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ t in (0 : ℝ)..a, cutProfile a b t = a := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (1 : ℝ))]
    · simp
    · intro t ht
      rw [uIcc_of_le ha.le] at ht
      exact cutProfile_of_le hab ht.2
  have h2 : 0 ≤ ∫ t in a..b, cutProfile a b t :=
    intervalIntegral.integral_nonneg hab.le (fun t _ ↦ (cutProfile_mem_Icc hab t).1)
  linarith
theorem profMass_le (ha : 0 < a) (hab : a < b) : profMass a b ≤ b := by
  unfold profMass
  have hc := continuous_cutProfile hab
  calc ∫ t in (0 : ℝ)..b, cutProfile a b t ≤ ∫ t in (0 : ℝ)..b, (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
          intervalIntegrable_const (fun t _ ↦ (cutProfile_mem_Icc hab t).2)
    _ = b := by simp

theorem profMass_pos (ha : 0 < a) (hab : a < b) : 0 < profMass a b :=
  ha.trans_le (le_profMass ha hab)

theorem kernel_eq (a b : ℝ) (z : ℂ) :
    kernel a b z = cutProfile a b (‖z‖ ^ 2) / profMass a b / Real.pi := rfl

theorem contDiff_kernel (ha : 0 < a) (hab : a < b) : ContDiff ℝ (⊤ : ℕ∞) (kernel a b) :=
  (((contDiff_cutProfile hab).div_const _).comp (contDiff_norm_sq ℝ)).div_const _
theorem kernel_nonneg (ha : 0 < a) (hab : a < b) (z : ℂ) : 0 ≤ kernel a b z := by
  rw [kernel_eq]
  exact div_nonneg (div_nonneg (cutProfile_mem_Icc hab _).1 (profMass_pos ha hab).le)
    Real.pi_pos.le
theorem kernel_eq_zero (ha : 0 < a) (hab : a < b) {z : ℂ} (hz : b ≤ ‖z‖ ^ 2) :
    kernel a b z = 0 := by
  rw [kernel_eq, cutProfile_of_ge hab hz, zero_div, zero_div]
theorem integral_kernel (ha : 0 < a) (hab : a < b) : ∫ z, kernel a b z = 1 := by
  have hb : 0 < b := ha.trans hab
  have hc := (contDiff_cutProfile hab).continuous
  set f : ℝ → ℝ := fun y ↦ cutProfile a b (y ^ 2) / profMass a b / Real.pi with hf
  have h1 : ∫ z : ℂ, kernel a b z = ∫ z : ℂ, f ‖z‖ := rfl
  rw [h1, integral_fun_norm_addHaar volume f, finrank_real_complex]
  have hvol : volume.real (Metric.ball (0 : ℂ) 1) = Real.pi := by
    simp [Measure.real]
  rw [hvol]
  have h2 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • f y =
      ∫ y in (0 : ℝ)..Real.sqrt b, y ^ (2 - 1) • f y := by
    rw [intervalIntegral.integral_of_le (Real.sqrt_nonneg b)]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Ioc_subset_Ioi_self ?_
    intro y hy
    simp only [mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hy
    have hy' : Real.sqrt b < y := hy.2 hy.1
    have : b ≤ y ^ 2 := by
      calc b = Real.sqrt b ^ 2 := (Real.sq_sqrt hb.le).symm
        _ ≤ y ^ 2 := by gcongr
    simp [hf, cutProfile_of_ge hab this]
  rw [h2]
  have h3 : ∫ y in (0 : ℝ)..Real.sqrt b, y ^ (2 - 1) • f y =
      (∫ y in (0 : ℝ)..Real.sqrt b,
        ((fun t ↦ cutProfile a b t) ∘ (fun y ↦ y ^ 2)) y * (2 * y))
        / (2 * profMass a b * Real.pi) := by
    rw [← intervalIntegral.integral_div]
    congr 1
    funext y
    simp only [hf, Function.comp, smul_eq_mul]
    field_simp
    ring
  rw [h3, intervalIntegral.integral_comp_mul_deriv (f := fun y ↦ y ^ 2) (f' := fun y ↦ 2 * y)
    (fun y _ ↦ by simpa using hasDerivAt_pow 2 y) (by fun_prop) hc]
  rw [Real.sq_sqrt hb.le, zero_pow two_ne_zero]
  change 2 • (Real.pi • (profMass a b / (2 * profMass a b * Real.pi))) = 1
  have hM := profMass_pos ha hab
  rw [smul_eq_mul, nsmul_eq_mul]
  field_simp
  norm_num
/-- Pointwise bound `ρ ≤ (π a)⁻¹` (used before `kernel_le`, which restates it). -/
theorem kernel_le_inv_pi_mul (ha : 0 < a) (hab : a < b) (z : ℂ) :
    kernel a b z ≤ (Real.pi * a)⁻¹ := by
  rw [kernel_eq, mul_inv, mul_comm, ← div_eq_mul_inv, ← one_div]
  have hM := le_profMass ha hab
  have hσ := (cutProfile_mem_Icc hab (‖z‖ ^ 2))
  have h : cutProfile a b (‖z‖ ^ 2) / profMass a b ≤ 1 / a := by
    rw [div_le_div_iff₀ (profMass_pos ha hab) ha]; nlinarith [hσ.1, hσ.2]
  exact div_le_div_of_nonneg_right h Real.pi_pos.le

theorem kernel_le_indicator (ha : 0 < a) (hab : a < b) (z : ℂ) :
    kernel a b z ≤ (Real.pi * a)⁻¹ * (Metric.ball (0 : ℂ) (Real.sqrt b)).indicator 1 z := by
  by_cases hz : z ∈ Metric.ball (0 : ℂ) (Real.sqrt b)
  · rw [indicator_of_mem hz, Pi.one_apply, mul_one]
    exact kernel_le_inv_pi_mul ha hab z
  · rw [indicator_of_notMem hz, mul_zero]
    apply le_of_eq
    apply kernel_eq_zero ha hab
    rw [mem_ball_zero_iff, not_lt] at hz
    calc b = Real.sqrt b ^ 2 := (Real.sq_sqrt (by linarith)).symm
      _ ≤ ‖z‖ ^ 2 := by gcongr
theorem indicator_le_kernel (ha : 0 < a) (hab : a < b) (z : ℂ) :
    (Real.pi * b)⁻¹ * (Metric.ball (0 : ℂ) (Real.sqrt a)).indicator 1 z ≤ kernel a b z := by
  by_cases hz : z ∈ Metric.ball (0 : ℂ) (Real.sqrt a)
  · rw [indicator_of_mem hz, Pi.one_apply, mul_one]
    rw [mem_ball_zero_iff] at hz
    have hz2 : ‖z‖ ^ 2 ≤ a := by
      calc ‖z‖ ^ 2 ≤ Real.sqrt a ^ 2 := by gcongr
        _ = a := Real.sq_sqrt ha.le
    rw [kernel_eq, cutProfile_of_le hab hz2, mul_inv, mul_comm, ← div_eq_mul_inv, ← one_div]
    have := profMass_le ha hab
    gcongr
    exact profMass_pos ha hab
  · rw [indicator_of_notMem hz, mul_zero]
    exact kernel_nonneg ha hab z
theorem kernel_le (ha : 0 < a) (hab : a < b) (z : ℂ) : kernel a b z ≤ (Real.pi * a)⁻¹ :=
  kernel_le_inv_pi_mul ha hab z

-- generic profile API
/-! ### Auxiliary lemmas for generic profiles -/

section generic

variable {p : ℝ → ℝ}

/-- `t · g_p(t) = m_p(t)` for every `t` (substitution `τ = t u`). -/
theorem mul_gFn_eq_massFn (p : ℝ → ℝ) (t : ℝ) : t * gFn p t = massFn p t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [massFn]
  · unfold gFn massFn
    rw [intervalIntegral.integral_comp_mul_left (fun x ↦ p x) ht, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ ht, one_mul, mul_zero, mul_one]

theorem gFn_eq_inv_mul_massFn (p : ℝ → ℝ) {t : ℝ} (ht : t ≠ 0) :
    gFn p t = t⁻¹ * massFn p t := by
  rw [← mul_gFn_eq_massFn, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]

/-- If `p = p 0` on `(-∞, c)`, then `g_p = p 0` on `(-∞, c)`. -/
theorem gFn_eq_of_lt {c : ℝ} (hc : 0 < c) (hpc : ∀ s < c, p s = p 0) {t : ℝ} (ht : t < c) :
    gFn p t = p 0 := by
  unfold gFn
  rw [intervalIntegral.integral_congr (g := fun _ ↦ p 0)]
  · simp
  · intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    apply hpc
    rcases le_or_gt t 0 with h | h
    · nlinarith [hu.1]
    · nlinarith [hu.2]

theorem contDiff_integral_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ ∫ x in a..t, f x) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t ↦ (hf.continuous.integral_hasStrictDerivAt a t).hasDerivAt.differentiableAt, ?_⟩
  have : deriv (fun t ↦ ∫ x in a..t, f x) = f :=
    funext fun t ↦ hf.continuous.deriv_integral f a t
  rw [this]; exact hf

/-- `g_p` is nonincreasing when `p` is. -/
theorem antitone_gFn (hpa : Antitone p) (hpc : Continuous p) : Antitone (gFn p) := by
  intro s t hst
  unfold gFn
  apply intervalIntegral.integral_mono_on zero_le_one
    ((hpc.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    ((hpc.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
  intro u hu
  exact hpa (mul_le_mul_of_nonneg_right hst hu.1)

theorem IsProfile.continuous (hp : IsProfile p b) : Continuous p := hp.smooth.continuous

theorem IsProfile.contDiff_massFn (hp : IsProfile p b) : ContDiff ℝ (⊤ : ℕ∞) (massFn p) :=
  contDiff_integral_of_contDiff hp.smooth 0

theorem IsProfile.hasDerivAt_massFn (hp : IsProfile p b) (t : ℝ) :
    HasDerivAt (massFn p) (p t) t :=
  (hp.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem IsProfile.massFn_of_ge (hp : IsProfile p b) {t : ℝ} (ht : b ≤ t) : massFn p t = 1 := by
  unfold massFn
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := b)
    (hp.continuous.intervalIntegrable _ _) (hp.continuous.intervalIntegrable _ _), hp.mass,
    intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ))]
  · simp
  · intro τ hτ
    rw [uIcc_of_le ht] at hτ
    exact hp.vanish τ hτ.1

theorem IsProfile.massFn_le_one (hp : IsProfile p b) {t : ℝ} (ht : 0 ≤ t) : massFn p t ≤ 1 := by
  rcases le_total t b with h | h
  · rw [← hp.mass]
    exact intervalIntegral.integral_mono_interval le_rfl ht h (ae_of_all _ hp.nonneg)
      (hp.continuous.intervalIntegrable _ _)
  · rw [hp.massFn_of_ge h]

theorem IsProfile.massFn_nonneg (hp : IsProfile p b) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ massFn p t :=
  intervalIntegral.integral_nonneg ht (fun τ _ ↦ hp.nonneg τ)

end generic

theorem IsProfile.contDiff_gFn {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) :
    ContDiff ℝ (⊤ : ℕ∞) (gFn p) := by
  obtain ⟨c, hc, hpc⟩ := hp.const_near_zero
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge t c with htc | htc
  · apply (contDiffAt_const (c := p 0)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds htc] with s hs
    exact gFn_eq_of_lt hc hpc hs
  · have ht : 0 < t := hc.trans_le htc
    have : ContDiffAt ℝ (⊤ : ℕ∞) (fun s ↦ s⁻¹ * massFn p s) t :=
      (contDiffAt_inv ℝ ht.ne').mul hp.contDiff_massFn.contDiffAt
    apply this.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact gFn_eq_inv_mul_massFn p hs.ne'
theorem IsProfile.gFn_of_ge {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) {t : ℝ} (ht : b ≤ t) :
    gFn p t = t⁻¹ := by
  rw [gFn_eq_inv_mul_massFn p (hp.pos.trans_le ht).ne', hp.massFn_of_ge ht, mul_one]
theorem IsProfile.continuous_gFn {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) :
    Continuous (gFn p) :=
  hp.contDiff_gFn.continuous

/-- `0 ≤ g_p(t) ≤ 1/t` for `t > 0`. -/
theorem IsProfile.gFn_le_inv {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) {t : ℝ} (ht : 0 < t) :
    gFn p t ≤ t⁻¹ := by
  rw [gFn_eq_inv_mul_massFn p ht.ne']
  calc t⁻¹ * massFn p t ≤ t⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (hp.massFn_le_one ht.le) (inv_nonneg.2 ht.le)
    _ = t⁻¹ := mul_one _

theorem IsProfile.gFn_nonneg {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ gFn p t := by
  rcases ht.eq_or_lt with rfl | ht
  · obtain ⟨c, hc, hpc⟩ := hp.const_near_zero
    rw [gFn_eq_of_lt hc hpc hc]; exact hp.nonneg 0
  · rw [gFn_eq_inv_mul_massFn p ht.ne']
    exact mul_nonneg (inv_nonneg.2 ht.le) (hp.massFn_nonneg ht.le)

/-- `S_p' = -g_p`. -/
theorem IsProfile.hasDerivAt_sFn {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) (t : ℝ) :
    HasDerivAt (sFn p b) (-gFn p t) t := by
  have h : sFn p b = fun s ↦ -Real.log b - ∫ τ in b..s, gFn p τ := by
    funext s; simp only [sFn]; rw [intervalIntegral.integral_symm]; ring
  rw [h]
  exact (hp.continuous_gFn.integral_hasStrictDerivAt b t).hasDerivAt.const_sub _

theorem IsProfile.deriv_sFn {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) :
    deriv (sFn p b) = fun t ↦ -gFn p t :=
  funext fun t ↦ (hp.hasDerivAt_sFn t).deriv

theorem IsProfile.contDiff_sFn {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) :
    ContDiff ℝ (⊤ : ℕ∞) (sFn p b) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t ↦ (hp.hasDerivAt_sFn t).differentiableAt, ?_⟩
  rw [hp.deriv_sFn]
  exact hp.contDiff_gFn.neg
/-- For any `T ≥ b`, `S_p(t) = −log T + ∫ₜᵀ g_p`. -/
theorem IsProfile.sFn_eq_of_le {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) {T : ℝ} (hT : b ≤ T)
    (t : ℝ) : sFn p b t = -Real.log T + ∫ τ in t..T, gFn p τ := by
  have hb := hp.pos
  have hg := hp.continuous_gFn
  unfold sFn
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := t) (b := T) (c := b)
    (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have : ∫ τ in T..b, gFn p τ = Real.log (b / T) := by
    rw [intervalIntegral.integral_congr (g := fun τ ↦ τ⁻¹)]
    · exact integral_inv_of_pos (hb.trans_le hT) hb
    · intro τ hτ
      rw [uIcc_of_ge hT] at hτ
      exact hp.gFn_of_ge hτ.1
  rw [this, Real.log_div hb.ne' (hb.trans_le hT).ne']
  ring

theorem IsProfile.sFn_of_ge {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) {t : ℝ} (ht : b ≤ t) :
    sFn p b t = -Real.log t := by
  rw [hp.sFn_eq_of_le ht t, intervalIntegral.integral_same, add_zero]
/-- `(t · g_p(t))' = p(t)`, i.e. `g_p + t g_p' = p`. -/
theorem IsProfile.gFn_add_mul_deriv {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) (t : ℝ) :
    gFn p t + t * deriv (gFn p) t = p t := by
  have h1 : HasDerivAt (fun s ↦ s * gFn p s) (1 * gFn p t + t * deriv (gFn p) t) t :=
    (hasDerivAt_id' t).mul (hp.contDiff_gFn.differentiable (by simp) t).hasDerivAt
  have h2 : HasDerivAt (fun s ↦ s * gFn p s) (p t) t := by
    have : (fun s ↦ s * gFn p s) = massFn p := funext (mul_gFn_eq_massFn p)
    rw [this]; exact hp.hasDerivAt_massFn t
  have := h1.unique h2
  linarith

theorem IsProfile.lap_sFn_normSq {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) (z : ℂ) :
    lap (fun w ↦ sFn p b (‖w‖ ^ 2)) z = -p (‖z‖ ^ 2) := by
  rw [lap_comp_normSq (hp.contDiff_sFn.contDiffAt.of_le (by simp)), hp.deriv_sFn]
  have h : deriv (fun t ↦ -gFn p t) (‖z‖ ^ 2) = -deriv (gFn p) (‖z‖ ^ 2) := deriv.fun_neg
  rw [h]
  have := hp.gFn_add_mul_deriv (‖z‖ ^ 2)
  linarith
/-- `S_p(t) ≤ −log t` for `t > 0` (since `g_p(τ) ≤ 1/τ`). -/
theorem IsProfile.sFn_le_neg_log {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) {t : ℝ} (ht : 0 < t) :
    sFn p b t ≤ -Real.log t := by
  have htT : t ≤ max b t := le_max_right b t
  have hT : 0 < max b t := ht.trans_le htT
  rw [hp.sFn_eq_of_le (le_max_left b t) t]
  have : ∫ τ in t..max b t, gFn p τ ≤ ∫ τ in t..max b t, τ⁻¹ :=
    intervalIntegral.integral_mono_on htT (hp.continuous_gFn.intervalIntegrable _ _)
      (intervalIntegral.intervalIntegrable_inv
        (fun x hx ↦ by rw [uIcc_of_le htT] at hx; exact (ht.trans_le hx.1).ne')
        continuousOn_id)
      (fun τ hτ ↦ hp.gFn_le_inv (ht.trans_le hτ.1))
  rw [integral_inv_of_pos ht hT, Real.log_div hT.ne' ht.ne'] at this
  linarith

theorem IsProfile.wFn_nonpos {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) {z : ℂ} (hz : z ≠ 0) :
    wFn p b z ≤ 0 := by
  have : 0 < ‖z‖ ^ 2 := by positivity
  unfold wFn
  linarith [hp.sFn_le_neg_log this]
theorem IsProfile.wFn_eq_zero {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) {z : ℂ}
    (hz : b ≤ ‖z‖ ^ 2) : wFn p b z = 0 := by
  unfold wFn
  rw [hp.sFn_of_ge hz, add_neg_cancel]
theorem IsProfile.contDiffOn_wFn {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) :
    ContDiffOn ℝ (⊤ : ℕ∞) (wFn p b) {0}ᶜ := by
  intro z hz
  have hz : z ≠ 0 := hz
  apply ContDiffAt.contDiffWithinAt
  have hn : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ ↦ ‖w‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ ↦ Real.log (‖w‖ ^ 2)) z :=
    (Real.contDiffAt_log.2 (by positivity)).comp z hn
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ ↦ sFn p b (‖w‖ ^ 2)) z :=
    hp.contDiff_sFn.contDiffAt.comp z hn
  exact h1.add h2
theorem IsProfile.exists_abs_sFn_le {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) (B : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) B, |sFn p b t| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := B)).exists_bound_of_continuousOn
    hp.contDiff_sFn.continuous.continuousOn
  exact ⟨C, fun t ht ↦ by simpa [Real.norm_eq_abs] using hC t ht⟩
theorem IsProfile.exists_wFn_ge {p : ℝ → ℝ} {b : ℝ} (hp : IsProfile p b) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ z : ℂ, η ≤ ‖z‖ → -C ≤ wFn p b z := by
  have hη2 : 0 < η ^ 2 := by positivity
  have hcont : ContinuousOn (fun t ↦ Real.log t + sFn p b t) (Icc (η ^ 2) b) :=
    (Real.continuousOn_log.mono (fun t ht ↦ (hη2.trans_le ht.1).ne')).add
      hp.contDiff_sFn.continuous.continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, fun z hz ↦ ?_⟩
  have ht : η ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hη.le hz 2
  rcases le_or_gt b (‖z‖ ^ 2) with h | h
  · rw [hp.wFn_eq_zero h]; simp
  · have h' := hC _ ⟨ht, h.le⟩
    rw [Real.norm_eq_abs] at h'
    unfold wFn
    linarith [le_max_left C 0, neg_abs_le (Real.log (‖z‖ ^ 2) + sFn p b (‖z‖ ^ 2))]
/-- Comparison of potentials, assuming `g_{p₂} ≤ g_{p₁}` on `[t, ∞)`. -/
theorem sFn_le_sFn_of_gFn_le_of_le {p₁ p₂ : ℝ → ℝ} {b₁ b₂ : ℝ} (h₁ : IsProfile p₁ b₁)
    (h₂ : IsProfile p₂ b₂) {t : ℝ} (hg : ∀ τ, t ≤ τ → gFn p₂ τ ≤ gFn p₁ τ) :
    sFn p₂ b₂ t ≤ sFn p₁ b₁ t := by
  have hT : t ≤ max (max b₁ b₂) t := le_max_right _ _
  rw [h₁.sFn_eq_of_le (le_max_of_le_left (le_max_left _ _)) t,
    h₂.sFn_eq_of_le (le_max_of_le_left (le_max_right _ _)) t]
  have : ∫ τ in t..max (max b₁ b₂) t, gFn p₂ τ ≤ ∫ τ in t..max (max b₁ b₂) t, gFn p₁ τ :=
    intervalIntegral.integral_mono_on hT (h₂.continuous_gFn.intervalIntegrable _ _)
      (h₁.continuous_gFn.intervalIntegrable _ _) (fun τ hτ ↦ hg τ hτ.1)
  linarith

theorem sFn_le_sFn_of_gFn_le {p₁ p₂ : ℝ → ℝ} {b₁ b₂ : ℝ} (h₁ : IsProfile p₁ b₁)
    (h₂ : IsProfile p₂ b₂) (hg : ∀ τ, 0 ≤ τ → gFn p₂ τ ≤ gFn p₁ τ) {t : ℝ} (ht : 0 ≤ t) :
    sFn p₂ b₂ t ≤ sFn p₁ b₁ t :=
  sFn_le_sFn_of_gFn_le_of_le h₁ h₂ fun τ hτ ↦ hg τ (ht.trans hτ)
-- plane instance
theorem isProfile_planeProfile (ha : 0 < a) (hab : a < b) : IsProfile (planeProfile a b) b := by
  refine ⟨ha.trans hab, (contDiff_cutProfile hab).div_const _,
    fun t ↦ div_nonneg (cutProfile_mem_Icc hab t).1 (profMass_pos ha hab).le,
    fun t ht ↦ by simp [planeProfile, cutProfile_of_ge hab ht], ⟨a, ha, fun t ht ↦ ?_⟩, ?_⟩
  · simp only [planeProfile]
    rw [cutProfile_of_le hab ht.le, cutProfile_of_le hab ha.le]
  · simp only [planeProfile]
    rw [intervalIntegral.integral_div]
    exact div_self (profMass_pos ha hab).ne'
theorem antitone_planeProfile (ha : 0 < a) (hab : a < b) : Antitone (planeProfile a b) :=
  fun _ _ h ↦ div_le_div_of_nonneg_right (antitone_cutProfile hab h) (profMass_pos ha hab).le

/-- `g = 1 / profMass` on `(-∞, a)`. -/
theorem gFun_of_lt (ha : 0 < a) (hab : a < b) {t : ℝ} (ht : t < a) :
    gFun a b t = (profMass a b)⁻¹ := by
  have hpc : ∀ s < a, planeProfile a b s = planeProfile a b 0 := fun s hs ↦ by
    simp only [planeProfile]; rw [cutProfile_of_le hab hs.le, cutProfile_of_le hab ha.le]
  rw [gFun, gFn_eq_of_lt ha hpc ht, planeProfile, cutProfile_of_le hab ha.le, one_div]

theorem contDiff_gFun (ha : 0 < a) (hab : a < b) : ContDiff ℝ (⊤ : ℕ∞) (gFun a b) :=
  (isProfile_planeProfile ha hab).contDiff_gFn
theorem gFun_of_ge (ha : 0 < a) (hab : a < b) {t : ℝ} (ht : b ≤ t) : gFun a b t = t⁻¹ :=
  (isProfile_planeProfile ha hab).gFn_of_ge ht
theorem contDiff_sFun (ha : 0 < a) (hab : a < b) : ContDiff ℝ (⊤ : ℕ∞) (sFun a b) :=
  (isProfile_planeProfile ha hab).contDiff_sFn
theorem sFun_of_ge (ha : 0 < a) (hab : a < b) {t : ℝ} (ht : b ≤ t) :
    sFun a b t = -Real.log t :=
  (isProfile_planeProfile ha hab).sFn_of_ge ht
theorem lap_sFun_normSq (ha : 0 < a) (hab : a < b) (z : ℂ) :
    lap (fun w ↦ sFun a b (‖w‖ ^ 2)) z = -Real.pi * kernel a b z := by
  rw [show (fun w : ℂ ↦ sFun a b (‖w‖ ^ 2)) = fun w ↦ sFn (planeProfile a b) b (‖w‖ ^ 2) from
    rfl, (isProfile_planeProfile ha hab).lap_sFn_normSq, kernel]
  field_simp
theorem exists_abs_sFun_le (ha : 0 < a) (hab : a < b) (B : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) B, |sFun a b t| ≤ C :=
  (isProfile_planeProfile ha hab).exists_abs_sFn_le B

theorem contDiffOn_wFun (ha : 0 < a) (hab : a < b) :
    ContDiffOn ℝ (⊤ : ℕ∞) (wFun a b) {0}ᶜ :=
  (isProfile_planeProfile ha hab).contDiffOn_wFn
theorem wFun_nonpos (ha : 0 < a) (hab : a < b) {z : ℂ} (hz : z ≠ 0) : wFun a b z ≤ 0 :=
  (isProfile_planeProfile ha hab).wFn_nonpos hz
theorem wFun_eq_zero (ha : 0 < a) (hab : a < b) {z : ℂ} (hz : b ≤ ‖z‖ ^ 2) :
    wFun a b z = 0 :=
  (isProfile_planeProfile ha hab).wFn_eq_zero hz
theorem lap_wFun (ha : 0 < a) (hab : a < b) {z : ℂ} (hz : z ≠ 0) :
    lap (wFun a b) z = -Real.pi * kernel a b z := by
  have hp := isProfile_planeProfile ha hab
  have hn : ContDiffAt ℝ 2 (fun w : ℂ ↦ ‖w‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt
  have h1 : ContDiffAt ℝ 2 (fun w : ℂ ↦ Real.log (‖w‖ ^ 2)) z :=
    (Real.contDiffAt_log.2 (by positivity)).comp z hn
  have h2 : ContDiffAt ℝ 2 (fun w : ℂ ↦ sFn (planeProfile a b) b (‖w‖ ^ 2)) z :=
    (hp.contDiff_sFn.contDiffAt.of_le (by simp)).comp z hn
  show lap (fun w ↦ Real.log (‖w‖ ^ 2) + sFn (planeProfile a b) b (‖w‖ ^ 2)) z = _
  rw [lap_add h1 h2, lap_log_normSq hz, zero_add]
  exact lap_sFun_normSq ha hab z
theorem exists_wFun_ge (ha : 0 < a) (hab : a < b) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ z : ℂ, η ≤ ‖z‖ → -C ≤ wFun a b z :=
  (isProfile_planeProfile ha hab).exists_wFn_ge hη

theorem sFun_le_sFun {a₁ b₁ a₂ b₂ : ℝ} (h₁ : 0 < a₁) (h₁' : a₁ < b₁) (h₂' : a₂ < b₂)
    (hb : b₁ ≤ a₂) (t : ℝ) : sFun a₂ b₂ t ≤ sFun a₁ b₁ t := by
  have h₂ : 0 < a₂ := by linarith
  have hp₁ := isProfile_planeProfile h₁ h₁'
  have hp₂ := isProfile_planeProfile h₂ h₂'
  apply sFn_le_sFn_of_gFn_le_of_le hp₁ hp₂
  intro τ _
  rcases le_or_gt b₁ τ with hτ | hτ
  · rw [hp₁.gFn_of_ge hτ]; exact hp₂.gFn_le_inv (by linarith)
  · change gFun a₂ b₂ τ ≤ gFun a₁ b₁ τ
    rw [gFun_of_lt h₂ h₂' (by linarith)]
    calc (profMass a₂ b₂)⁻¹ ≤ a₂⁻¹ := inv_anti₀ h₂ (le_profMass h₂ h₂')
      _ ≤ b₁⁻¹ := inv_anti₀ (by linarith) hb
      _ = gFun a₁ b₁ b₁ := (gFun_of_ge h₁ h₁' le_rfl).symm
      _ ≤ gFun a₁ b₁ τ := antitone_gFn (antitone_planeProfile h₁ h₁') hp₁.continuous hτ.le
theorem cutProfile_scale (hab : a < b) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    cutProfile (ε ^ 2 * a) (ε ^ 2 * b) t = cutProfile a b (t / ε ^ 2) := by
  unfold cutProfile
  have h1 : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  have hε2 : ε ^ 2 ≠ 0 := by positivity
  rw [← mul_sub]
  congr 2
  field_simp

theorem profMass_scale (hab : a < b) {ε : ℝ} (hε : 0 < ε) :
    profMass (ε ^ 2 * a) (ε ^ 2 * b) = ε ^ 2 * profMass a b := by
  have hε2 : ε ^ 2 ≠ 0 := by positivity
  unfold profMass
  simp_rw [cutProfile_scale hab hε]
  rw [intervalIntegral.integral_comp_div (fun t ↦ cutProfile a b t) hε2, zero_div,
    mul_div_cancel_left₀ b hε2, smul_eq_mul]

theorem planeProfile_scale (hab : a < b) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    planeProfile (ε ^ 2 * a) (ε ^ 2 * b) t = planeProfile a b (t / ε ^ 2) / ε ^ 2 := by
  unfold planeProfile
  rw [cutProfile_scale hab hε, profMass_scale hab hε, div_div, mul_comm (profMass a b)]

theorem gFun_scale (hab : a < b) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gFun (ε ^ 2 * a) (ε ^ 2 * b) t = gFun a b (t / ε ^ 2) / ε ^ 2 := by
  unfold gFun gFn
  rw [← intervalIntegral.integral_div]
  congr 1
  funext u
  rw [planeProfile_scale hab hε, mul_div_right_comm]

theorem sFun_scale (ha : 0 < a) (hab : a < b) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    sFun (ε ^ 2 * a) (ε ^ 2 * b) t = sFun a b (t / ε ^ 2) - Real.log (ε ^ 2) := by
  have hε2 : ε ^ 2 ≠ 0 := by positivity
  have hb : 0 < b := ha.trans hab
  have hg : ∀ τ, gFn (planeProfile (ε ^ 2 * a) (ε ^ 2 * b)) τ = gFun a b (τ / ε ^ 2) / ε ^ 2 :=
    gFun_scale hab hε
  have : ∫ τ in t..ε ^ 2 * b, gFn (planeProfile (ε ^ 2 * a) (ε ^ 2 * b)) τ =
      ∫ τ in t / ε ^ 2..b, gFun a b τ := by
    simp_rw [hg]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_comp_div (fun τ ↦ gFun a b τ) hε2,
      mul_div_cancel_left₀ _ hε2, smul_eq_mul, mul_div_cancel_left₀ _ hε2]
  unfold sFun sFn
  rw [this, Real.log_mul hε2 hb.ne']
  simp only [gFun]
  ring
theorem kernel_scale (ha : 0 < a) (hab : a < b) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    kernel (ε ^ 2 * a) (ε ^ 2 * b) z = kernel a b (z / ε) / ε ^ 2 := by
  unfold kernel
  rw [planeProfile_scale hab hε]
  have : ‖z / (ε : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / ε ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, div_pow]
  rw [this, div_right_comm]

end OC
