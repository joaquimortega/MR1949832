import OrtegaCerdaSeip.Carleson.Poisson

/-!
# M04 (Jones) — Jones' formula: definitions and the modulus of the exponential factor

See `blueprint/M04_Jones.md` (§1.2–§1.3).

Jones' solution of `∂̄v = θ ρ` in the upper half-plane (paper, p. 410, with the denominator
`(z - ζ)(z - ζ̄)`; the printed `(z - ζ)(z - ζ)` is a typo):

`v(z) = (2i/π) ∫ Im ζ / ((z - ζ)(z - ζ̄)) · exp(∫_{Im w ≤ Im ζ} (i/(ζ - w̄) - i/(z - w̄)) dρ(w)) θ(ζ) dρ(ζ)`.

Standing assumptions in M04: `ρ` is a finite positive measure carried by `{Im w ≥ 10}` (the paper's
`|σ|`, `σ = θ ρ` with `|θ| ≤ 1`).  Then all inner integrals are integrals of bounded functions.

`|exp(…)| = exp(A(ζ) - P(z, Im ζ))` with `P(z, t) = jonesPot ρ z t = ∫_{Im w ≤ t} (Im z + Im w)/|z - w̄|²`
and `A(ζ) = P(ζ, Im ζ) ≤ 12K` for a Carleson constant `K` of `ρ`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-! ## Definitions -/

/-- The exponent of Jones' formula: `∫_{Im w ≤ Im ζ} (i/(ζ - w̄) - i/(z - w̄)) dρ(w)`. -/
def jonesExponent (ρ : Measure ℂ) (z ζ : ℂ) : ℂ :=
  ∫ w in {w : ℂ | w.im ≤ ζ.im}, (I / (ζ - conj w) - I / (z - conj w)) ∂ρ

/-- The holomorphic factor of Jones' kernel, `H(z, ζ) = 2i Im ζ e^{(…)} / (z - ζ̄)`, so that the
kernel is `H(z, ζ)/(π(z - ζ))` and `H(ζ, ζ) = 1`. -/
def jonesH (ρ : Measure ℂ) (z ζ : ℂ) : ℂ :=
  2 * I * (ζ.im : ℂ) * Complex.exp (jonesExponent ρ z ζ) / (z - conj ζ)

/-- Jones' kernel `(2i/π) · Im ζ / ((z - ζ)(z - ζ̄)) · e^{(…)}`. -/
def jonesKernel (ρ : Measure ℂ) (z ζ : ℂ) : ℂ :=
  2 * I / (Real.pi : ℂ) * ((ζ.im : ℂ) / ((z - ζ) * (z - conj ζ))) *
    Complex.exp (jonesExponent ρ z ζ)

/-- **Jones' solution** of `∂̄v = θ ρ` in the upper half-plane. -/
def jonesSol (ρ : Measure ℂ) (θ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ ζ, jonesKernel ρ z ζ * θ ζ ∂ρ

/-- The real weight `(Im z + Im w)/|z - w̄|²`, i.e. `Re (i/(z - w̄))`. -/
def jonesWeight (z w : ℂ) : ℝ :=
  (z.im + w.im) / ‖z - conj w‖ ^ 2

/-- `P(z, t) = ∫_{Im w ≤ t} (Im z + Im w)/|z - w̄|² dρ(w)`. -/
def jonesPot (ρ : Measure ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  ∫ w in {w : ℂ | w.im ≤ t}, jonesWeight z w ∂ρ

/-! ## Algebraic identities -/

theorem jonesExponent_self (ρ : Measure ℂ) (ζ : ℂ) : jonesExponent ρ ζ ζ = 0 := by
  simp [jonesExponent]

theorem jonesKernel_eq_jonesH_div (ρ : Measure ℂ) (z ζ : ℂ) :
    jonesKernel ρ z ζ = jonesH ρ z ζ / ((Real.pi : ℂ) * (z - ζ)) := by
  simp only [jonesKernel, jonesH, div_eq_mul_inv, mul_inv]
  ring

theorem jonesH_self (ρ : Measure ℂ) {ζ : ℂ} (hζ : 0 < ζ.im) : jonesH ρ ζ ζ = 1 := by
  rw [jonesH, jonesExponent_self, Complex.exp_zero, Complex.sub_conj]
  have : (ζ.im : ℂ) ≠ 0 := by exact_mod_cast hζ.ne'
  push_cast
  field_simp

theorem re_I_div (a : ℂ) : (I / a).re = a.im / ‖a‖ ^ 2 := by
  simp [Complex.div_re, Complex.normSq_eq_norm_sq]

theorem jonesWeight_nonneg {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) : 0 ≤ jonesWeight z w :=
  div_nonneg (add_nonneg hz hw) (sq_nonneg _)

theorem im_sub_conj_eq_add (z w : ℂ) : (z - conj w).im = z.im + w.im := by simp

/-- `|z - w̄| ≥ Im (z - w̄) = Im z + Im w`. -/
theorem add_im_le_norm_sub_conj (z w : ℂ) : z.im + w.im ≤ ‖z - conj w‖ := by
  rw [← im_sub_conj_eq_add]; exact Complex.im_le_norm _

/-- `(Im z + Im w)/|z - w̄|² ≤ 1/(Im z + Im w)`. -/
theorem jonesWeight_le_inv {z w : ℂ} (hzw : 0 < z.im + w.im) :
    jonesWeight z w ≤ 1 / (z.im + w.im) := by
  have h := add_im_le_norm_sub_conj z w
  rw [jonesWeight, div_le_div_iff₀ (pow_pos (hzw.trans_le h) 2) hzw]
  nlinarith

/-- `|ω_z(w)| ≤ 1/c` when `Im z + Im w ≥ c > 0`. -/
theorem norm_jonesWeight_le {z w : ℂ} {c : ℝ} (hc : 0 < c) (h : c ≤ z.im + w.im) :
    ‖jonesWeight z w‖ ≤ 1 / c := by
  have hpos : 0 < z.im + w.im := hc.trans_le h
  rw [Real.norm_of_nonneg (show 0 ≤ jonesWeight z w from div_nonneg hpos.le (sq_nonneg _))]
  exact (jonesWeight_le_inv hpos).trans (one_div_le_one_div_of_le hc h)

/-- `|i/(z - w̄)| ≤ 1/c` when `Im z + Im w ≥ c > 0`. -/
theorem norm_I_div_sub_conj_le {z w : ℂ} {c : ℝ} (hc : 0 < c) (h : c ≤ z.im + w.im) :
    ‖I / (z - conj w)‖ ≤ 1 / c := by
  rw [norm_div, Complex.norm_I]
  exact one_div_le_one_div_of_le hc (h.trans (add_im_le_norm_sub_conj z w))

/-- Pointwise Poisson bound: for `10 ≤ Im w ≤ Im ζ`, `ω_ζ(w) ≤ 4 · t/(|w - s|² + t²)` with
`s = Re ζ`, `t = Im ζ` (blueprint §1.3.4). -/
theorem jonesWeight_le_poisson {ζ w : ℂ} (hw : 10 ≤ w.im) (hwζ : w.im ≤ ζ.im) :
    jonesWeight ζ w ≤ 4 * (ζ.im / (‖w - (ζ.re : ℂ)‖ ^ 2 + ζ.im ^ 2)) := by
  have h1 : ‖ζ - conj w‖ ^ 2 = (ζ.re - w.re) ^ 2 + (ζ.im + w.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : ‖w - (ζ.re : ℂ)‖ ^ 2 = (w.re - ζ.re) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hp1 : 0 < (ζ.re - w.re) ^ 2 + (ζ.im + w.im) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (by linarith) 2)
  have hp2 : 0 < (w.re - ζ.re) ^ 2 + w.im ^ 2 + ζ.im ^ 2 :=
    add_pos_of_nonneg_of_pos (by positivity) (pow_pos (by linarith) 2)
  rw [jonesWeight, h1, h2, mul_div_assoc', div_le_div_iff₀ hp1 hp2]
  have hd : 0 ≤ (w.re - ζ.re) ^ 2 := sq_nonneg _
  have hd' : (ζ.re - w.re) ^ 2 = (w.re - ζ.re) ^ 2 := by ring
  rw [hd']
  nlinarith [mul_nonneg hd (by linarith : (0:ℝ) ≤ 4 * ζ.im - (ζ.im + w.im)),
    mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ ζ.im) (by linarith : (0:ℝ) ≤ ζ.im - w.im))
      (by linarith : (0:ℝ) ≤ ζ.im + w.im)]

/-! ## Measurability and integrability of the integrands -/

theorem measurableSet_im_le (t : ℝ) : MeasurableSet {w : ℂ | w.im ≤ t} :=
  measurableSet_le Complex.measurable_im measurable_const

theorem measurable_jonesWeight (z : ℂ) : Measurable (jonesWeight z) := by
  unfold jonesWeight; fun_prop

/-- If `ρ`-a.e. `Im w ≥ 10`, then a.e. on `{Im w ≤ t}` we have `10 ≤ Im w ≤ t`. -/
theorem ae_restrict_im_le {ρ : Measure ℂ} (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) (t : ℝ) :
    ∀ᵐ w ∂ρ.restrict {w : ℂ | w.im ≤ t}, 10 ≤ w.im ∧ w.im ≤ t := by
  filter_upwards [ae_restrict_of_ae h10, ae_restrict_mem (measurableSet_im_le t)] with w hw hwt
  exact ⟨hw, hwt⟩

theorem restrict_im_le_eq_zero {ρ : Measure ℂ} (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {t : ℝ}
    (ht : t < 10) : ρ.restrict {w : ℂ | w.im ≤ t} = 0 := by
  rw [← ae_eq_bot, eq_bot_iff]
  intro s _
  filter_upwards [ae_restrict_im_le h10 t] with w hw
  exact absurd (hw.1.trans hw.2) (not_le.2 ht)

theorem integrable_I_div_sub_conj {μ : Measure ℂ} [IsFiniteMeasure μ] {z : ℂ} {c : ℝ}
    (hc : 0 < c) (h : ∀ᵐ w ∂μ, c ≤ z.im + w.im) :
    Integrable (fun w ↦ I / (z - conj w)) μ :=
  Integrable.of_bound (by fun_prop : Measurable fun w : ℂ ↦ I / (z - conj w)).aestronglyMeasurable
    (1 / c) (h.mono fun _ hw ↦ norm_I_div_sub_conj_le hc hw)

theorem integrable_jonesWeight {μ : Measure ℂ} [IsFiniteMeasure μ] {z : ℂ} {c : ℝ}
    (hc : 0 < c) (h : ∀ᵐ w ∂μ, c ≤ z.im + w.im) :
    Integrable (jonesWeight z) μ :=
  Integrable.of_bound (measurable_jonesWeight z).aestronglyMeasurable (1 / c)
    (h.mono fun _ hw ↦ norm_jonesWeight_le hc hw)

/-! ## The modulus of the exponential factor -/

section Measure

variable {ρ : Measure ℂ} [IsFiniteMeasure ρ]

theorem re_jonesExponent (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {z : ℂ} (hz : 0 ≤ z.im) (ζ : ℂ) :
    (jonesExponent ρ z ζ).re = jonesPot ρ ζ ζ.im - jonesPot ρ z ζ.im := by
  set S := {w : ℂ | w.im ≤ ζ.im}
  have hae := ae_restrict_im_le h10 ζ.im
  have hζ : ∀ᵐ w ∂ρ.restrict S, (20 : ℝ) ≤ ζ.im + w.im :=
    hae.mono fun w hw ↦ by linarith [hw.1, hw.2]
  have hz' : ∀ᵐ w ∂ρ.restrict S, (10 : ℝ) ≤ z.im + w.im :=
    hae.mono fun w hw ↦ by linarith [hw.1]
  have i3 : Integrable (fun w ↦ I / (ζ - conj w) - I / (z - conj w)) (ρ.restrict S) :=
    (integrable_I_div_sub_conj (by norm_num) hζ).sub (integrable_I_div_sub_conj (by norm_num) hz')
  have hre := integral_re i3
  simp only [RCLike.re_to_complex] at hre
  rw [jonesExponent, ← hre, jonesPot, jonesPot,
    ← integral_sub (integrable_jonesWeight (by norm_num) hζ)
      (integrable_jonesWeight (by norm_num) hz')]
  refine integral_congr_ae (Eventually.of_forall fun w ↦ ?_)
  simp only [Complex.sub_re, re_I_div, im_sub_conj_eq_add, jonesWeight]

theorem norm_exp_jonesExponent (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {z : ℂ} (hz : 0 ≤ z.im) (ζ : ℂ) :
    ‖Complex.exp (jonesExponent ρ z ζ)‖ = Real.exp (jonesPot ρ ζ ζ.im - jonesPot ρ z ζ.im) := by
  rw [Complex.norm_exp, re_jonesExponent h10 hz]

omit [IsFiniteMeasure ρ] in
theorem jonesPot_nonneg (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {z : ℂ} (hz : 0 ≤ z.im) (t : ℝ) :
    0 ≤ jonesPot ρ z t :=
  integral_nonneg_of_ae <| (ae_restrict_of_ae h10).mono fun w hw ↦
    div_nonneg (by linarith) (sq_nonneg _)

/-- Crude bound, no Carleson condition: `A(ζ) = P(ζ, Im ζ) ≤ ρ(ℂ)/20`. -/
theorem jonesPot_self_le_mass (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) (ζ : ℂ) :
    jonesPot ρ ζ ζ.im ≤ (ρ univ).toReal / 20 := by
  have hb : ∀ᵐ w ∂ρ.restrict {w : ℂ | w.im ≤ ζ.im}, ‖jonesWeight ζ w‖ ≤ 1 / 20 :=
    (ae_restrict_im_le h10 ζ.im).mono fun w hw ↦
      norm_jonesWeight_le (by norm_num) (by linarith [hw.1, hw.2])
  calc jonesPot ρ ζ ζ.im ≤ ‖jonesPot ρ ζ ζ.im‖ := Real.le_norm_self _
    _ ≤ 1 / 20 * (ρ.restrict {w : ℂ | w.im ≤ ζ.im}).real univ :=
        norm_integral_le_of_norm_le_const hb
    _ ≤ 1 / 20 * ρ.real univ := by
        gcongr
        rw [measureReal_def, measureReal_def]
        exact ENNReal.toReal_mono (measure_ne_top ρ univ) (Measure.restrict_le_self _)
    _ = (ρ univ).toReal / 20 := by rw [measureReal_def]; ring

omit [IsFiniteMeasure ρ] in
/-- **Carleson bound** for the positive part of the exponent: `A(ζ) = P(ζ, Im ζ) ≤ 12K`. -/
theorem jonesPot_self_le (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {K : ℝ≥0} (hC : IsCarlesonLarge ρ K)
    (ζ : ℂ) : jonesPot ρ ζ ζ.im ≤ 12 * K := by
  by_cases ht : ζ.im < 10
  · rw [jonesPot, restrict_im_le_eq_zero h10 ht, integral_zero_measure]; positivity
  replace ht := not_lt.1 ht
  set S := {w : ℂ | w.im ≤ ζ.im}
  have hae := ae_restrict_im_le h10 ζ.im
  have hnn : ∀ᵐ w ∂ρ.restrict S, 0 ≤ jonesWeight ζ w :=
    hae.mono fun w hw ↦ div_nonneg (by linarith [hw.1, hw.2]) (sq_nonneg _)
  rw [jonesPot, integral_eq_lintegral_of_nonneg_ae hnn
    (measurable_jonesWeight ζ).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc ∫⁻ w in S, ENNReal.ofReal (jonesWeight ζ w) ∂ρ
      ≤ ∫⁻ w in S, ENNReal.ofReal 4 *
          ENNReal.ofReal (ζ.im / (‖w - (ζ.re : ℂ)‖ ^ 2 + ζ.im ^ 2)) ∂ρ := by
        refine lintegral_mono_ae (hae.mono fun w hw ↦ ?_)
        rw [← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (jonesWeight_le_poisson hw.1 hw.2)
    _ ≤ ∫⁻ w, ENNReal.ofReal 4 *
          ENNReal.ofReal (ζ.im / (‖w - (ζ.re : ℂ)‖ ^ 2 + ζ.im ^ 2)) ∂ρ :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal 4 * ∫⁻ w, ENNReal.ofReal (ζ.im / (‖w - (ζ.re : ℂ)‖ ^ 2 + ζ.im ^ 2)) ∂ρ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal 4 * (3 * K) := by
        gcongr; exact hC.lintegral_poisson_le ζ.re (by linarith)
    _ = ENNReal.ofReal (12 * K) := by
        rw [ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
        congr 1
        · rw [show (12 : ℝ) = 4 * 3 by norm_num, ENNReal.ofReal_mul (by norm_num)]; simp
        · simp

omit [IsFiniteMeasure ρ] in
/-- `P(z, t)` is the mass of `{Im w ≤ t}` for the measure `ρ_z = (Im z + Im w)/|z - w̄|² dρ(w)`. -/
theorem jonesPot_eq_toReal (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {z : ℂ} (hz : 0 ≤ z.im) (t : ℝ) :
    jonesPot ρ z t =
      ((ρ.withDensity fun w ↦ ENNReal.ofReal (jonesWeight z w)) {w | w.im ≤ t}).toReal := by
  rw [withDensity_apply _ (measurableSet_im_le t), jonesPot,
    integral_eq_lintegral_of_nonneg_ae _ (measurable_jonesWeight z).aestronglyMeasurable]
  exact (ae_restrict_of_ae h10).mono fun w hw ↦ div_nonneg (by linarith) (sq_nonneg _)

theorem isFiniteMeasure_withDensity_jonesWeight (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {z : ℂ}
    (hz : 0 ≤ z.im) :
    IsFiniteMeasure (ρ.withDensity fun w ↦ ENNReal.ofReal (jonesWeight z w)) :=
  isFiniteMeasure_withDensity_ofReal
    (integrable_jonesWeight (c := 10) (by norm_num) (h10.mono fun w hw ↦ by linarith)).2

end Measure

/-! ## Measurability and holomorphy in `z` -/

/-- `(z, ζ) ↦ E(z, ζ)` is measurable: it is a parametric integral of the indicator of the
measurable set `{((z, ζ), w) | Im w ≤ Im ζ}`. -/
theorem measurable_jonesExponent (ρ : Measure ℂ) [SFinite ρ] :
    Measurable fun p : ℂ × ℂ ↦ jonesExponent ρ p.1 p.2 := by
  set g : (ℂ × ℂ) × ℂ → ℂ := {q | q.2.im ≤ q.1.2.im}.indicator
    fun q ↦ I / (q.1.2 - conj q.2) - I / (q.1.1 - conj q.2) with hg
  have hgm : StronglyMeasurable g :=
    ((by fun_prop : Measurable fun q : (ℂ × ℂ) × ℂ ↦
      I / (q.1.2 - conj q.2) - I / (q.1.1 - conj q.2)).indicator
      (measurableSet_le (by fun_prop) (by fun_prop))).stronglyMeasurable
  have hE : (fun p : ℂ × ℂ ↦ jonesExponent ρ p.1 p.2) = fun p ↦ ∫ w, g (p, w) ∂ρ := by
    ext p
    rw [jonesExponent, ← integral_indicator (measurableSet_im_le _)]
    rfl
  rw [hE]
  exact (hgm.integral_prod_right' (ν := ρ)).measurable

theorem measurable_jonesKernel (ρ : Measure ℂ) [SFinite ρ] :
    Measurable (Function.uncurry (jonesKernel ρ)) := by
  have hEm := measurable_jonesExponent ρ
  unfold Function.uncurry jonesKernel
  fun_prop

/-- The `z`-derivative of the integrand of `E(·, ζ)`. -/
theorem hasDerivAt_jonesExponent_integrand (ζ w : ℂ) {z : ℂ} (hne : z - conj w ≠ 0) :
    HasDerivAt (fun z ↦ I / (ζ - conj w) - I / (z - conj w)) (I / (z - conj w) ^ 2) z := by
  have h1 := ((hasDerivAt_id z).sub_const (conj w)).inv hne
  have h2 := (h1.const_mul I).const_sub (I / (ζ - conj w))
  convert h2 using 1
  · ext y; simp [div_eq_mul_inv]
  · simp only [id_eq]; field_simp

/-- For `z` in the disc `D(z₀, Im z₀/2)` and `Im w ≥ 0`: `Im z + Im w ≥ Im z₀/2`. -/
theorem half_im_le_of_mem_ball {z₀ z w : ℂ} (hz : z ∈ ball z₀ (z₀.im / 2)) (hw : 0 ≤ w.im) :
    z₀.im / 2 ≤ z.im + w.im := by
  have h1 : |z.im - z₀.im| < z₀.im / 2 := by
    rw [mem_ball, dist_eq_norm] at hz
    have h0 : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h0
    exact h0.trans_lt hz
  linarith [neg_abs_le (z.im - z₀.im)]

theorem differentiableOn_jonesExponent {ρ : Measure ℂ} [IsFiniteMeasure ρ]
    (h0 : ∀ᵐ w ∂ρ, 0 ≤ w.im) {ζ : ℂ} (hζ : 0 < ζ.im) :
    DifferentiableOn ℂ (fun z ↦ jonesExponent ρ z ζ) {z | 0 < z.im} := by
  intro z₀ hz₀
  replace hz₀ : 0 < z₀.im := hz₀
  set S := {w : ℂ | w.im ≤ ζ.im}
  have h0S : ∀ᵐ w ∂ρ.restrict S, 0 ≤ w.im := ae_restrict_of_ae h0
  have hc : 0 < z₀.im / 2 := by linarith
  have i1 := integrable_I_div_sub_conj (z := ζ) hζ (h0S.mono fun w hw ↦ by linarith)
  have i2 := integrable_I_div_sub_conj (z := z₀) hz₀ (h0S.mono fun w hw ↦ by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ρ.restrict S) (F := fun z w ↦ I / (ζ - conj w) - I / (z - conj w))
    (F' := fun z w ↦ I / (z - conj w) ^ 2) (x₀ := z₀) (bound := fun _ ↦ 1 / (z₀.im / 2) ^ 2)
    (ball_mem_nhds z₀ hc)
    (Eventually.of_forall fun z ↦ (by fun_prop :
      Measurable fun w : ℂ ↦ I / (ζ - conj w) - I / (z - conj w)).aestronglyMeasurable)
    (i1.sub i2)
    ((by fun_prop : Measurable fun w : ℂ ↦ I / (z₀ - conj w) ^ 2).aestronglyMeasurable)
    (h0S.mono fun w hw z hz ↦ ?_) (integrable_const _)
    (h0S.mono fun w hw z hz ↦ ?_)
  · exact key.2.differentiableAt.differentiableWithinAt
  · have h1 := half_im_le_of_mem_ball hz hw
    have h2 := (add_im_le_norm_sub_conj z w)
    rw [norm_div, Complex.norm_I, norm_pow]
    exact one_div_le_one_div_of_le (pow_pos hc 2) (pow_le_pow_left₀ hc.le (h1.trans h2) 2)
  · have h1 := half_im_le_of_mem_ball hz hw
    have hne : z - conj w ≠ 0 := by
      intro h
      have := add_im_le_norm_sub_conj z w
      rw [h, norm_zero] at this
      linarith
    exact hasDerivAt_jonesExponent_integrand ζ w hne

theorem differentiableOn_jonesH {ρ : Measure ℂ} [IsFiniteMeasure ρ] (h0 : ∀ᵐ w ∂ρ, 0 ≤ w.im)
    {ζ : ℂ} (hζ : 0 < ζ.im) : DifferentiableOn ℂ (fun z ↦ jonesH ρ z ζ) {z | 0 < z.im} := by
  unfold jonesH
  refine DifferentiableOn.div ?_ (by fun_prop) fun z hz h ↦ ?_
  · exact (differentiableOn_jonesExponent h0 hζ).cexp.const_mul _
  · have := add_im_le_norm_sub_conj z ζ
    rw [h, norm_zero] at this
    have hz' : 0 < z.im := hz
    linarith

end OCS
