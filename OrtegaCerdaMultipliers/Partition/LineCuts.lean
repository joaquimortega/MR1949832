import OrtegaCerdaMultipliers.Doubling.Quant

/-!
# M05 (Partition) — Lemma 4 on the line: cutting `ℝ` into intervals of mass `N`

See `blueprint/M05_Partition.md` §3.9.  This file is imported by `Partition/Lemma4.lean`, where
`IsMassPartition` is defined, so the fields of `IsMassPartition` are spelled out here; the glue
`lemma4_line`, `lemma4_line_quant` is in `Lemma4.lean`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The per-measure hypotheses of `lemma4_line` place `μ` in some class `MeasClassLine μ Cd R₀`. -/
theorem lineCut_measClassLine_of {μ : Measure ℂ} (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) :
    ∃ (Cd : ℝ≥0) (R₀ : ℝ), MeasClassLine μ Cd R₀ := sorry

/-- **Lemma 4 (line)**, uniform form with the fields of `IsMassPartition` spelled out: intervals
`[s, t)` of mass `N`, with constants depending only on `(Cd, R₀, N)`. -/
theorem lineCut_partition_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ μ : Measure ℂ, MeasClassLine μ Cd R₀ →
      ∃ R : ℕ → Set ℂ, (∀ i, MeasurableSet (R i)) ∧ Pairwise (Function.onFun Disjoint R) ∧
        ⋃ i, R i = range (fun t : ℝ ↦ (t : ℂ)) ∧ (∀ i, μ (R i) = N) ∧
        (∀ i, ∀ z ∈ R i, ∀ w ∈ R i, dist z w ≤ A * massRadiusLine μ z.re) ∧
        (∀ i, ∃ c ∈ R i, {w | w ∈ range (fun t : ℝ ↦ (t : ℂ)) ∧
          dist c w < a * massRadiusLine μ c.re} ⊆ R i) ∧
        ∀ i, ∃ s t : ℝ, s < t ∧ R i = (fun u : ℝ ↦ (u : ℂ)) '' Ico s t := sorry

end OC
