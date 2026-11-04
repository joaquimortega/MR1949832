import OrtegaCerdaSeip.Carleson.Basic

/-!
# M03 (Carleson) — Poisson integrals and tails of Carleson measures

See `blueprint/M03_Carleson.md` (§1.5).

For a large-scale Carleson measure `ν` (`ν(D(x,r)) ≤ K r` for `r ≥ 1`, `x ∈ ℝ`):
* `IsCarlesonLarge.lintegral_poisson_le`: `∫ t/(|w - s|² + t²) dν(w) ≤ 3K` for `s ∈ ℝ`, `t ≥ 1`
  (layer-cake formula: the super-level sets of the integrand are discs centred at `s`);
* `IsCarlesonLarge.lintegral_tail_le`: `∫_{|x - w| ≥ R} dν(w)/|x - w|² ≤ 6K/R` for `R ≥ 1`.

These replace the dyadic decompositions usually used for Carleson measures.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-- `∫_0^{1/t} √(t/s) ds = 2`. -/
theorem lintegral_sqrt_div_eq {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Ioo 0 (1 / t), ENNReal.ofReal (Real.sqrt (t / s)) = 2 := by
  have hcongr : EqOn (fun s ↦ ENNReal.ofReal (Real.sqrt (t / s)))
      (fun s ↦ ENNReal.ofReal (Real.sqrt t * s ^ (-(1 / 2 : ℝ)))) (Ioo 0 (1 / t)) := by
    intro s hs
    simp only
    rw [Real.sqrt_div ht.le, Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have hint : IntegrableOn (fun s : ℝ ↦ Real.sqrt t * s ^ (-(1 / 2 : ℝ))) (Ioo 0 (1 / t)) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 / t)
      (by norm_num : (-1 : ℝ) < -(1 / 2))).1.mono_set Ioo_subset_Ioc_self).const_mul _
  rw [setLIntegral_congr_fun measurableSet_Ioo hcongr, ← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioo).mono fun s hs ↦
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hs.1.le _)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by positivity),
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
  have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have : Real.sqrt t * (((1 / t) ^ (-(1 / 2 : ℝ) + 1) - (0 : ℝ) ^ (-(1 / 2 : ℝ) + 1)) /
      (-(1 / 2 : ℝ) + 1)) = 2 := by
    rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num, Real.zero_rpow (by norm_num), sub_zero,
      ← Real.sqrt_eq_rpow, Real.sqrt_div' _ ht.le, Real.sqrt_one]
    field_simp
  rw [this, ENNReal.ofReal_ofNat]

/-- The one-dimensional integral of the layer-cake argument:
`∫_0^{1/t} (√(t/s) + 1) ds = 2 + 1/t ≤ 3` for `t ≥ 1`. -/
theorem lintegral_sqrt_div_add_one_le {t : ℝ} (ht : 1 ≤ t) :
    ∫⁻ s in Ioo 0 (1 / t), ENNReal.ofReal (Real.sqrt (t / s) + 1) ≤ 3 := by
  have ht0 : 0 < t := by linarith
  have hsplit : ∀ s, ENNReal.ofReal (Real.sqrt (t / s) + 1) = ENNReal.ofReal (Real.sqrt (t / s)) + 1 :=
    fun s ↦ by rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) zero_le_one, ENNReal.ofReal_one]
  simp_rw [hsplit]
  rw [lintegral_add_right _ measurable_const, setLIntegral_const, one_mul, Real.volume_Ioo,
    lintegral_sqrt_div_eq ht0]
  have h1 : ENNReal.ofReal (1 / t - 0) ≤ 1 := by
    rw [sub_zero, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((div_le_one ht0).2 ht)
  calc (2 : ℝ≥0∞) + ENNReal.ofReal (1 / t - 0) ≤ 2 + 1 := add_le_add_right h1 _
    _ = 3 := by norm_num

/-- The super-level sets of the Poisson-type integrand are discs:
for `0 < λ`, `t/(|w - s|² + t²) > λ ↔ |w - s| < √(t/λ - t²)` (for `λ ≥ 1/t` both sides are
empty). -/
theorem setOf_lt_poisson_eq_ball {t : ℝ} (ht : 0 < t) (s : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    {w : ℂ | lam < t / (‖w - s‖ ^ 2 + t ^ 2)} = ball (s : ℂ) (Real.sqrt (t / lam - t ^ 2)) := by
  ext w
  have hpos : 0 < ‖w - s‖ ^ 2 + t ^ 2 := by positivity
  simp only [mem_ofPred_eq, mem_ball, dist_eq_norm]
  rw [lt_div_iff₀ hpos, Real.lt_sqrt (norm_nonneg _), lt_sub_iff_add_lt, lt_div_iff₀ hlam]
  constructor <;> intro h <;> linarith

/-- **Poisson bound.**  `∫ t/(|w - s|² + t²) dν(w) ≤ 3K` for `s ∈ ℝ` and `t ≥ 1`. -/
theorem IsCarlesonLarge.lintegral_poisson_le {ν : Measure ℂ} {K : ℝ≥0} (h : IsCarlesonLarge ν K)
    (s : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    ∫⁻ w, ENNReal.ofReal (t / (‖w - s‖ ^ 2 + t ^ 2)) ∂ν ≤ 3 * K := by
  have ht0 : 0 < t := by linarith
  set f : ℂ → ℝ := fun w ↦ t / (‖w - s‖ ^ 2 + t ^ 2) with hf
  have hf_nn : 0 ≤ᵐ[ν] f := ae_of_all _ fun w ↦ by positivity
  have hf_meas : AEMeasurable f ν := by
    have : Continuous f := by
      refine continuous_const.div (by fun_prop) fun w ↦ by positivity
    exact this.aemeasurable
  have hf_le : ∀ w, f w ≤ 1 / t := by
    intro w
    calc f w ≤ t / t ^ 2 :=
          div_le_div_of_nonneg_left ht0.le (by positivity) (by nlinarith [norm_nonneg (w - s)])
      _ = 1 / t := by field_simp
  rw [lintegral_eq_lintegral_meas_lt ν hf_nn hf_meas,
    ← Ioo_union_Ici_eq_Ioi (one_div_pos.2 ht0), lintegral_union measurableSet_Ici
      (disjoint_left.2 fun _ hx hx' ↦ absurd hx' (not_le.2 hx.2))]
  have h2 : ∫⁻ lam in Ici (1 / t), ν {w | lam < f w} = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ici (g := fun _ ↦ 0), lintegral_zero]
    intro lam hlam
    have : {w | lam < f w} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (hf_le w).trans hlam
    simp only [this, measure_empty]
  have h1 : ∫⁻ lam in Ioo 0 (1 / t), ν {w | lam < f w} ≤
      ∫⁻ lam in Ioo 0 (1 / t), K * ENNReal.ofReal (Real.sqrt (t / lam) + 1) := by
    refine setLIntegral_mono' measurableSet_Ioo fun lam hlam ↦ ?_
    rw [hf, setOf_lt_poisson_eq_ball ht0 s hlam.1]
    refine (h.measure_ball_le s _).trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _)
    refine max_le ?_ (by linarith [Real.sqrt_nonneg (t / lam)])
    have := Real.sqrt_le_sqrt (show t / lam - t ^ 2 ≤ t / lam by nlinarith)
    linarith
  rw [h2, add_zero]
  refine h1.trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, mul_comm]
  exact mul_le_mul_left (lintegral_sqrt_div_add_one_le ht) _

/-- **Tail bound.**  `∫_{|x - w| ≥ R} dν(w)/|x - w|² ≤ 6K/R` for `x ∈ ℝ` and `R ≥ 1`. -/
theorem IsCarlesonLarge.lintegral_tail_le {ν : Measure ℂ} {K : ℝ≥0} (h : IsCarlesonLarge ν K)
    (x : ℝ) {R : ℝ} (hR : 1 ≤ R) :
    ∫⁻ w in (ball (x : ℂ) R)ᶜ, ENNReal.ofReal (1 / ‖(x : ℂ) - w‖ ^ 2) ∂ν ≤
      ENNReal.ofReal (6 / R) * K := by
  have hR0 : 0 < R := by linarith
  have hpt : ∀ w ∈ (ball (x : ℂ) R)ᶜ, ENNReal.ofReal (1 / ‖(x : ℂ) - w‖ ^ 2) ≤
      ENNReal.ofReal (2 / R) * ENNReal.ofReal (R / (‖w - x‖ ^ 2 + R ^ 2)) := by
    intro w hw
    rw [mem_compl_iff, mem_ball, not_lt, dist_eq_norm] at hw
    rw [← ENNReal.ofReal_mul (by positivity), norm_sub_rev]
    apply ENNReal.ofReal_le_ofReal
    have hd : 0 < ‖w - x‖ := hR0.trans_le hw
    have : 2 / R * (R / (‖w - x‖ ^ 2 + R ^ 2)) = 2 / (‖w - x‖ ^ 2 + R ^ 2) := by
      field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ∫⁻ w in (ball (x : ℂ) R)ᶜ, ENNReal.ofReal (1 / ‖(x : ℂ) - w‖ ^ 2) ∂ν
      ≤ ∫⁻ w in (ball (x : ℂ) R)ᶜ,
          ENNReal.ofReal (2 / R) * ENNReal.ofReal (R / (‖w - x‖ ^ 2 + R ^ 2)) ∂ν :=
        setLIntegral_mono' measurableSet_ball.compl hpt
    _ = ENNReal.ofReal (2 / R) *
          ∫⁻ w in (ball (x : ℂ) R)ᶜ, ENNReal.ofReal (R / (‖w - x‖ ^ 2 + R ^ 2)) ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 / R) * ∫⁻ w, ENNReal.ofReal (R / (‖w - x‖ ^ 2 + R ^ 2)) ∂ν :=
        mul_le_mul_right (setLIntegral_le_lintegral _ _) _
    _ ≤ ENNReal.ofReal (2 / R) * (3 * K) := mul_le_mul_right (h.lintegral_poisson_le x hR) _
    _ = ENNReal.ofReal (6 / R) * K := by
      rw [← mul_assoc, ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

/-- **Vertical tail.**  `∫_{|Im w| ≥ A} dν(w)/|x - w|² ≤ 6K/A` for `x ∈ ℝ`, `A ≥ 1` (since
`|x - w| ≥ |Im w|`).  For `ν = Σ_λ |Im λ| δ_λ` the left side is `π δ_A(x)` of p. 407, so
`‖δ_A‖_∞ → 0` as `A → ∞`.  (The paper derives this from the separation of `Λ`, which also works
with its `σ` by an area argument, blueprint M03 §1.5.5; the Carleson route is used here.) -/
theorem IsCarlesonLarge.lintegral_abs_im_ge_le {ν : Measure ℂ} {K : ℝ≥0}
    (h : IsCarlesonLarge ν K) (x : ℝ) {A : ℝ} (hA : 1 ≤ A) :
    ∫⁻ w in {w : ℂ | A ≤ |w.im|}, ENNReal.ofReal (1 / ‖(x : ℂ) - w‖ ^ 2) ∂ν ≤
      ENNReal.ofReal (6 / A) * K := by
  have hsub : {w : ℂ | A ≤ |w.im|} ⊆ (ball (x : ℂ) A)ᶜ := by
    intro w hw
    rw [mem_ofPred_eq] at hw
    rw [mem_compl_iff, mem_ball, not_lt, dist_eq_norm]
    calc A ≤ |w.im| := hw
      _ = |(w - x).im| := by simp
      _ ≤ ‖w - x‖ := Complex.abs_im_le_norm _
  exact (lintegral_mono_set hsub).trans (h.lintegral_tail_le x hA)

end OCS
