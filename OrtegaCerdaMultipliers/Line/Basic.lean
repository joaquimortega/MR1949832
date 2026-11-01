import OrtegaCerdaMultipliers.Doubling.LineMeasure

/-!
# M13 (Theorem5) — Bridge between `μ` on `ℂ` and its pull-back to `ℝ`

See `blueprint/M13_Theorem5.md` §3.1.  Scaffold: statements, proofs `sorry`.

Reconciliation: M13's `lineMeasure μ = μ.comap ofReal` is M03's `linePull μ` (same definition),
so M13 uses `linePull`; `lineMeasure_apply` is M03's `linePull_apply` (no measurability
hypothesis needed).  `IsLineMeasure` and the line forms L1–L8 of M03 lemmas are in M03
(`Doubling/LineMeasure.lean`).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

theorem map_linePull {μ : Measure ℂ} (hμ : μ {z : ℂ | z.im ≠ 0} = 0) :
    (linePull μ).map (fun t : ℝ ↦ (t : ℂ)) = μ := sorry
theorem IsLineMeasure.linePull_Ioc_lt_top {μ : Measure ℂ} (hμ : IsLineMeasure μ) (a b : ℝ) :
    linePull μ (Ioc a b) < ∞ := sorry

end OC
