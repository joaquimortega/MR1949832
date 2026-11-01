import OrtegaCerdaMultipliers.Doubling.Export

/-!
# M03 (Doubling) — Line forms requested by M13 (`IsLineMeasure`, L1–L8)

See `blueprint/M13_Theorem5.md` §4.2 and `blueprint/M03_Doubling.md` §4.  Scaffold: statements,
proofs `sorry` (a few are short term proofs from `Doubling/Export.lean`); the structure is real.

M13 bundles the standing hypotheses on the Riesz measure `μ` of a weight whose Laplacian is
carried by `ℝ` (`IsLineMeasure`) and needs the line forms of Lemma 1, Claim 1, Claim 2,
[Chr91, Lemma 2.3], reverse doubling and no atoms (L1–L8).  They are stated here, upstream of
M13, as the reconciliation asked for.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Standing hypotheses of §4.3 on the Riesz measure `μ` (bundled for brevity). -/
structure IsLineMeasure (μ : Measure ℂ) : Prop where
  finite_of_compact : ∀ K : Set ℂ, IsCompact K → μ K < ∞
  doubling : IsLocallyDoublingLine μ
  mass : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)

/-- From the hypotheses of `theorem5` (proved). -/
theorem IsLineMeasure.of_weight {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoublingLine μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) :
    IsLineMeasure μ :=
  ⟨fun K hK ↦ hφ.finite_of_compact K (subset_univ K) hK, hd, hm⟩

/-! (L1) local doubling at every bounded scale. -/
theorem IsLineMeasure.doubling_le {μ : Measure ℂ} (hμ : IsLineMeasure μ) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x r : ℝ, 0 < r → r ≤ A →
      μ (lineInterval x (2 * r)) ≤ C * μ (lineInterval x r) :=
  doubling_upTo_line hμ.doubling A

/-! (L2) intervals have positive finite mass; no atoms. -/
theorem IsLineMeasure.lineInterval_pos {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) {r : ℝ}
    (hr : 0 < r) : 0 < μ (lineInterval x r) := sorry
theorem IsLineMeasure.lineInterval_lt_top {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x r : ℝ) :
    μ (lineInterval x r) < ∞ := sorry
theorem IsLineMeasure.measure_singleton {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) :
    μ {(x : ℂ)} = 0 := sorry

/-! (L3) reverse doubling at every bounded scale. -/
theorem IsLineMeasure.reverse_doubling {μ : Measure ℂ} (hμ : IsLineMeasure μ) {A : ℝ}
    (hA : 0 < A) :
    ∃ q : ℝ≥0, q < 1 ∧ ∀ x r : ℝ, 0 < r → r ≤ A →
      μ (lineInterval x (r / 2)) ≤ q * μ (lineInterval x r) := sorry

/-! (L4) the mass radius `ρ` on the line. -/
theorem IsLineMeasure.massRadiusLine_pos {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) :
    0 < massRadiusLine μ x := sorry
theorem massRadiusLine_le_of_mass {μ : Measure ℂ} {r : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (x : ℝ) : massRadiusLine μ x ≤ r :=
  massRadiusLine_le hr (fun y ↦ (hmr y).le) x
theorem IsLineMeasure.measure_massRadiusLine {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) :
    μ (lineInterval x (massRadiusLine μ x)) = 1 := sorry

/-! (L5) Claim 1 on the line. -/
theorem IsLineMeasure.massRadiusLine_comparable {μ : Measure ℂ} (hμ : IsLineMeasure μ) {K : ℝ}
    (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x t : ℝ, |x - t| ≤ K * max (massRadiusLine μ x) (massRadiusLine μ t) →
      massRadiusLine μ t ≤ C * massRadiusLine μ x := sorry

/-! (L6) Lemma 1 on the line: sublinear growth of `ρ`. -/
theorem IsLineMeasure.massRadiusLine_le_rpow {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ γ C : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < C ∧ ∀ x t : ℝ, massRadiusLine μ x ≤ |x - t| → |x - t| ≤ 1 →
      massRadiusLine μ t ≤ C * massRadiusLine μ x ^ γ * |x - t| ^ (1 - γ) := sorry

/-! (L7) Claim 2 on the line: an interval of mass in `[m₁, m₂]`, `m₁ ≥ 1`, has length `≃ ρ`. -/
theorem IsLineMeasure.length_comparable {μ : Measure ℂ} (hμ : IsLineMeasure μ) {m₁ m₂ : ℝ}
    (hm₁ : 1 ≤ m₁) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : ℝ, a < b →
      ENNReal.ofReal m₁ ≤ μ ((fun t : ℝ ↦ (t : ℂ)) '' Ioc a b) →
      μ ((fun t : ℝ ↦ (t : ℂ)) '' Ioc a b) ≤ ENNReal.ofReal m₂ →
      ∀ t ∈ Icc a b, massRadiusLine μ t ≤ b - a ∧ b - a ≤ C * massRadiusLine μ t := sorry

/-! (L8) [Chr91, Lemma 2.3] on the line: uniform logarithmic integrability. -/
theorem IsLineMeasure.lintegral_log_le {μ : Measure ℂ} (hμ : IsLineMeasure μ) {A : ℝ}
    (hA : 0 < A) :
    ∃ C : ℝ≥0, ∀ x R : ℝ, 0 < R → R ≤ A →
      ∫⁻ ζ in lineInterval x R, ENNReal.ofReal (Real.log (R / ‖ζ - (x : ℂ)‖)) ∂μ ≤
        C * μ (lineInterval x R) := sorry

end OC
