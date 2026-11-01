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

theorem norm_divPhase (σ f : ℂ → ℂ) (hσ : ∀ z, ‖σ z‖ = 1) (z : ℂ) : ‖divPhase σ f z‖ = 1 := sorry
theorem measurable_divPhase {σ f : ℂ → ℂ} (hσ : Measurable σ) (hf : Continuous f) :
    Measurable (divPhase σ f) := sorry

/-! 14.1 finiteness and Carleson transfer -/
theorem isFiniteMeasure_divMeasure {ν : Measure ℂ} [IsFiniteMeasure ν] {L Ω : Set ℂ}
    (hL : IsCompact L) (hνL : ν Lᶜ = 0) {f : ℂ → ℂ} {g : ℂ → ℝ} (hg : Continuous g)
    (hfg : ∀ z ∈ Ω, g z ≤ ‖f z‖) (hg0 : ∀ z, 0 < g z) :
    IsFiniteMeasure (divMeasure ν Ω f) := sorry
theorem divMeasure_withDensity_le {ν : Measure ℂ} {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    {f : ℂ → ℂ} {φ : ℂ → ℝ} {α c : ℝ} (hf : Continuous f) (hφ : Continuous φ) (hc : 0 < c)
    (hlow : ∀ z ∈ Ω, c * Real.exp (φ z - α * |z.im|) ≤ ‖f z‖) (s : Set ℂ) (hs : MeasurableSet s) :
    ((divMeasure ν Ω f).withDensity fun z ↦ ENNReal.ofReal (Real.exp (-α * |z.im|))) s ≤
      ENNReal.ofReal c⁻¹ * (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) s := sorry
theorem lintegral_ball_divMeasure_le {ν : Measure ℂ} {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    {f : ℂ → ℂ} {φ : ℂ → ℝ} {α c : ℝ} (hf : Continuous f) (hφ : Continuous φ) (hc : 0 < c)
    (hα : 0 ≤ α)
    (hlow : ∀ z ∈ Ω, c * Real.exp (φ z - α * |z.im|) ≤ ‖f z‖) (x : ℝ) :
    ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂divMeasure ν Ω f ≤
      ENNReal.ofReal (c⁻¹ * Real.exp α) *
        ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν := sorry

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
