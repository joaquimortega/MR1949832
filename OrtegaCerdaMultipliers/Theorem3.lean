import OrtegaCerdaMultipliers.Theorem5
import OrtegaCerdaMultipliers.Foundations.Weyl

/-!
# M14 (Theorem3) — Theorem 3 (degenerate weights), from Theorem 5 and [OCS99]

See `blueprint/M14_Theorem3.md`.  Scaffold: statements, proofs `sorry`; definitions are real.

`theorem3_weighted` is the corrected Theorem 3 (proposed main statement): hypothesis
`TheoremOCS`, conclusion with the weighted integral `∫_{|z-x|<1} e^{-φ(z)} d|μ|(z) / |x − z|`.
The printed `theorem3` of `comparator/statements.lean` is false (`not_theorem3_printed`); it is
kept below only as a comment.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The measure `|χ_Ω ν / f|`. -/
def divMeasure (ν : Measure ℂ) (Ω : Set ℂ) (f : ℂ → ℂ) : Measure ℂ :=
  (ν.restrict Ω).withDensity fun z ↦ ENNReal.ofReal (1 / ‖f z‖)

/-- The phase of `σ / f` (junk value `1` at the zeros of `f`). -/
def divPhase (σ f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if f z = 0 then 1 else σ z * ((‖f z‖ : ℂ) / f z)

theorem norm_divPhase (σ f : ℂ → ℂ) (hσ : ∀ z, ‖σ z‖ = 1) (z : ℂ) : ‖divPhase σ f z‖ = 1 := by
  unfold divPhase
  split_ifs with h
  · simp
  · rw [norm_mul, hσ, norm_div, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.2 h), one_mul]

theorem measurable_divPhase {σ f : ℂ → ℂ} (hσ : Measurable σ) (hf : Continuous f) :
    Measurable (divPhase σ f) := by
  unfold divPhase
  refine Measurable.ite ?_ measurable_const ?_
  · exact (isClosed_eq hf continuous_const).measurableSet
  · exact hσ.mul ((Complex.measurable_ofReal.comp hf.measurable.norm).div hf.measurable)

/-- The density `ofReal (1 / ‖f‖)` of `divMeasure` is measurable. -/
theorem measurable_ofReal_one_div_norm {f : ℂ → ℂ} (hf : Continuous f) :
    Measurable fun z ↦ ENNReal.ofReal (1 / ‖f z‖) :=
  (measurable_const.div hf.measurable.norm).ennreal_ofReal

/-- Pointwise core of the Carleson transfer: `1/‖f‖ ≤ c⁻¹ e^{-φ} e^{α|y|}` where
`‖f‖ ≥ c e^{φ - α|y|}`. -/
theorem one_div_norm_le_of_lowerBound {f : ℂ → ℂ} {φ : ℂ → ℝ} {α c : ℝ} (hc : 0 < c) {z : ℂ}
    (h : c * Real.exp (φ z - α * |z.im|) ≤ ‖f z‖) :
    1 / ‖f z‖ ≤ c⁻¹ * Real.exp (-φ z) * Real.exp (α * |z.im|) := by
  have hpos : 0 < c * Real.exp (φ z - α * |z.im|) := by positivity
  calc 1 / ‖f z‖ ≤ 1 / (c * Real.exp (φ z - α * |z.im|)) := one_div_le_one_div_of_le hpos h
    _ = c⁻¹ * Real.exp (-φ z) * Real.exp (α * |z.im|) := by
      rw [one_div, mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
      ring_nf

/-! 14.1 finiteness and Carleson transfer -/
theorem isFiniteMeasure_divMeasure {ν : Measure ℂ} [IsFiniteMeasure ν] {L Ω : Set ℂ}
    (hL : IsCompact L) (hνL : ν Lᶜ = 0) {f : ℂ → ℂ} {g : ℂ → ℝ} (hg : Continuous g)
    (hfg : ∀ z ∈ Ω, g z ≤ ‖f z‖) (hg0 : ∀ z, 0 < g z) :
    IsFiniteMeasure (divMeasure ν Ω f) := by
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn
    ((continuous_const.div hg fun z ↦ (hg0 z).ne').continuousOn (f := fun z ↦ 1 / g z))
  have hmg : Measurable fun z ↦ ENNReal.ofReal (1 / g z) :=
    (measurable_const.div hg.measurable).ennreal_ofReal
  constructor
  rw [divMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  -- neither `f` nor `Ω` is measurable: pass to a measurable minorant with the same integral
  obtain ⟨h, hhm, hhle, hheq⟩ :=
    exists_measurable_le_lintegral_eq (ν.restrict Ω) fun z ↦ ENNReal.ofReal (1 / ‖f z‖)
  rw [hheq]
  -- on `Ω`, `h ≤ 1/‖f‖ ≤ 1/g`; the bad set is measurable, so this holds `ν.restrict Ω`-a.e.
  have hae : ∀ᵐ z ∂ν.restrict Ω, h z ≤ ENNReal.ofReal (1 / g z) := by
    rw [ae_restrict_iff (measurableSet_le hhm hmg)]
    exact ae_of_all _ fun z hz ↦ (hhle z).trans
      (ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (hg0 z) (hfg z hz)))
  have hL' : ∀ᵐ z ∂ν, ENNReal.ofReal (1 / g z) ≤ ENNReal.ofReal M := by
    have : ∀ᵐ z ∂ν, z ∈ L := ae_iff.2 hνL
    filter_upwards [this] with z hz
    refine ENNReal.ofReal_le_ofReal ?_
    have := hM z hz
    rwa [Real.norm_of_nonneg (one_div_pos.2 (hg0 z)).le] at this
  calc ∫⁻ z, h z ∂ν.restrict Ω
      ≤ ∫⁻ z, ENNReal.ofReal (1 / g z) ∂ν.restrict Ω := lintegral_mono_ae hae
    _ ≤ ∫⁻ z, ENNReal.ofReal (1 / g z) ∂ν := lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ ∫⁻ _, ENNReal.ofReal M ∂ν := lintegral_mono_ae hL'
    _ < ∞ := by rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
                  (measure_lt_top ν univ)
theorem divMeasure_withDensity_le {ν : Measure ℂ} {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    {f : ℂ → ℂ} {φ : ℂ → ℝ} {α c : ℝ} (hf : Continuous f) (hφ : Continuous φ) (hc : 0 < c)
    (hlow : ∀ z ∈ Ω, c * Real.exp (φ z - α * |z.im|) ≤ ‖f z‖) (s : Set ℂ) (hs : MeasurableSet s) :
    ((divMeasure ν Ω f).withDensity fun z ↦ ENNReal.ofReal (Real.exp (-α * |z.im|))) s ≤
      ENNReal.ofReal c⁻¹ * (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) s := by
  have hm1 := measurable_ofReal_one_div_norm hf
  have hm2 : Measurable fun z : ℂ ↦ ENNReal.ofReal (Real.exp (-α * |z.im|)) := by fun_prop
  have hm3 : Measurable fun z : ℂ ↦ ENNReal.ofReal (Real.exp (-φ z)) :=
    (hφ.measurable.neg.exp).ennreal_ofReal
  rw [divMeasure, ← withDensity_mul _ hm1 hm2, withDensity_apply _ hs,
    Measure.restrict_restrict hs, withDensity_apply _ hs, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
  calc ∫⁻ z in s ∩ Ω, ((fun z ↦ ENNReal.ofReal (1 / ‖f z‖)) *
        fun z : ℂ ↦ ENNReal.ofReal (Real.exp (-α * |z.im|))) z ∂ν
      ≤ ∫⁻ z in s ∩ Ω, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (Real.exp (-φ z)) ∂ν := by
        refine setLIntegral_mono' (hs.inter hΩ) fun z hz ↦ ?_
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := one_div_norm_le_of_lowerBound hc (hlow z hz.2)
        calc 1 / ‖f z‖ * Real.exp (-α * |z.im|)
            ≤ c⁻¹ * Real.exp (-φ z) * Real.exp (α * |z.im|) * Real.exp (-α * |z.im|) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ = c⁻¹ * Real.exp (-φ z) := by
              rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
    _ ≤ ∫⁻ z in s, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (Real.exp (-φ z)) ∂ν :=
        lintegral_mono_set inter_subset_left
theorem lintegral_ball_divMeasure_le {ν : Measure ℂ} {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    {f : ℂ → ℂ} {φ : ℂ → ℝ} {α c : ℝ} (hf : Continuous f) (hφ : Continuous φ) (hc : 0 < c)
    (hα : 0 ≤ α)
    (hlow : ∀ z ∈ Ω, c * Real.exp (φ z - α * |z.im|) ≤ ‖f z‖) (x : ℝ) :
    ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂divMeasure ν Ω f ≤
      ENNReal.ofReal (c⁻¹ * Real.exp α) *
        ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν := by
  have hm1 := measurable_ofReal_one_div_norm hf
  have hk : Measurable fun z : ℂ ↦ ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) := by fun_prop
  rw [divMeasure, restrict_withDensity measurableSet_ball,
    lintegral_withDensity_eq_lintegral_mul _ hm1 hk, Measure.restrict_restrict measurableSet_ball,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ z in ball (x : ℂ) 1 ∩ Ω, ((fun z ↦ ENNReal.ofReal (1 / ‖f z‖)) *
        fun z ↦ ENNReal.ofReal (1 / ‖(x : ℂ) - z‖)) z ∂ν
      ≤ ∫⁻ z in ball (x : ℂ) 1 ∩ Ω, ENNReal.ofReal (c⁻¹ * Real.exp α) *
          ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν := by
        refine setLIntegral_mono' (measurableSet_ball.inter hΩ) fun z hz ↦ ?_
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := one_div_norm_le_of_lowerBound hc (hlow z hz.2)
        have hy : |z.im| ≤ 1 := by
          have := abs_im_le_norm (z - x)
          rw [sub_im, Complex.ofReal_im, sub_zero] at this
          have h2 : ‖z - x‖ < 1 := by rw [← dist_eq]; exact hz.1
          linarith
        have h3 : Real.exp (α * |z.im|) ≤ Real.exp α :=
          Real.exp_le_exp.2 (by nlinarith [abs_nonneg z.im])
        have h4 : 1 / ‖f z‖ ≤ c⁻¹ * Real.exp α * Real.exp (-φ z) := by
          calc 1 / ‖f z‖ ≤ c⁻¹ * Real.exp (-φ z) * Real.exp (α * |z.im|) := h1
            _ ≤ c⁻¹ * Real.exp (-φ z) * Real.exp α :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = c⁻¹ * Real.exp α * Real.exp (-φ z) := by ring
        calc 1 / ‖f z‖ * (1 / ‖(x : ℂ) - z‖)
            ≤ c⁻¹ * Real.exp α * Real.exp (-φ z) * (1 / ‖(x : ℂ) - z‖) :=
              mul_le_mul_of_nonneg_right h4 (by positivity)
          _ = c⁻¹ * Real.exp α * (Real.exp (-φ z) / ‖(x : ℂ) - z‖) := by ring
    _ ≤ ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (c⁻¹ * Real.exp α) *
          ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν :=
        lintegral_mono_set inter_subset_left

/-! 14.2 gluing: `u = Σ f_i v_i` solves `∂̄u = σν` -/
theorem isWeakDbarSolMeasure_sum_mul {ι : Type*} [Fintype ι] {ν : Measure ℂ}
    [IsFiniteMeasure ν] {σ : ℂ → ℂ} (hσ : Measurable σ) (hσ1 : ∀ z, ‖σ z‖ = 1)
    (Ω : ι → Set ℂ) (hΩm : ∀ i, MeasurableSet (Ω i)) (hΩd : Pairwise (Function.onFun Disjoint Ω))
    (hΩc : ⋃ i, Ω i = univ) (f : ι → ℂ → ℂ) (hf : ∀ i, Differentiable ℂ (f i))
    (hf0 : ∀ i, ∀ z ∈ Ω i, f i z ≠ 0) (hfin : ∀ i, IsFiniteMeasure (divMeasure ν (Ω i) (f i)))
    (v : ι → ℂ → ℂ) (hv : ∀ i, IsWeakDbarSolMeasure (v i) (divMeasure ν (Ω i) (f i))
      (divPhase σ (f i))) :
    IsWeakDbarSolMeasure (fun z ↦ ∑ i, f i z * v i z) ν σ := sorry

/-! 14.3 Theorem 3, corrected (weight inside the integral) -/
theorem theorem3_weighted (hOCS : TheoremOCS) (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingLine μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) (ball (x : ℂ) r) ≤
          K * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-φ z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-φ x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1,
              ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν) := sorry

/-! 14.4 the printed form, under a lower bound for `φ` on the strip `|Im z| < 1` -/
theorem theorem3_of_lowerBound (hOCS : TheoremOCS) (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingLine μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r))
    (hlow : ∃ B : ℝ, ∀ z : ℂ, |z.im| < 1 → -B ≤ φ z) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) (ball (x : ℂ) r) ≤
          K * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-φ z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-φ x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν) := sorry

/-! 14.5 the counterexample to the printed Theorem 3 (documentation; optional) -/
/-- `φ₀(z) = |Im z| + Re z · Im z`. -/
def cexWeight (z : ℂ) : ℝ := |z.im| + z.re * z.im
/-- `μ₀ = 2 · (Lebesgue measure on ℝ)`. -/
def cexMeasure : Measure ℂ := (2 : ℝ≥0∞) • (volume : Measure ℝ).map (fun t : ℝ ↦ (t : ℂ))

theorem cex_isSubharmonicWeight : IsSubharmonicWeight univ cexWeight cexMeasure := sorry
theorem cex_doubling : IsLocallyDoublingLine cexMeasure := sorry
theorem cex_mass : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < cexMeasure (lineInterval x r) := sorry

/-- The conclusion of the printed Theorem 3 fails for `(φ₀, μ₀, K = 2)`; hence `theorem3` in
`comparator/statements.lean` is equivalent to `¬ TheoremOCS`. -/
theorem not_theorem3_printed :
    ¬ ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-cexWeight z))) (ball (x : ℂ) r) ≤
          (2 : ℝ≥0) * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-cexWeight z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-cexWeight x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν) := sorry

/-! ### The printed Theorem 3 (comparator statement `theorem3`): FALSE, kept out of the build

The printed statement (paper, p. 358), as in `comparator/statements.lean`, is false: for the
weight `cexWeight` and `cexMeasure` (§4 of `blueprint/M14_Theorem3.md`) its conclusion fails
(`not_theorem3_printed`), so `theorem3` is equivalent to `¬ TheoremOCS`.  The corrected
statement is `theorem3_weighted` above (weight `e^{-φ}` inside the integral).  The printed form
is recorded here as a comment only, so that no known-false `sorry` theorem is in the build:

```
/-- **Theorem 3** (paper, p. 358), conditional on the Ortega-Cerdà–Seip theorem [OCS99]
(`TheoremOCS`), which the paper uses as a black box. -/
theorem theorem3 (hOCS : TheoremOCS) (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingLine μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) (ball (x : ℂ) r) ≤
          K * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-φ z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-φ x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν) := sorry
```
-/

end OC
