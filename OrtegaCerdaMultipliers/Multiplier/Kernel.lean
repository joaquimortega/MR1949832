import OrtegaCerdaMultipliers.Multiplier.Defs

/-!
# M08 (Multiplier) — Taylor remainders, polynomial form, moment cancellation

See `blueprint/M08_Multiplier.md` §2.2.  Scaffold: statements, proofs `sorry`.

Reconciliation: the disc geometry lemmas of §2.2 (`norm_sub_le_of_hypDist_le`,
`norm_one_sub_conj_mul_comparable`, `convex_closedHypBall`) are in M01
(`Foundations/HyperbolicExtra.lean`); the Forelli–Rudin bound
`integral_one_sub_conj_mul_rpow_neg_three_le` is in M10 (`ModelKernels.lean`).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

theorem abs_kerPlane_sub_taylorPlane_le {m : ℕ} (hm : 1 ≤ m) {z c ζ : ℂ} (hzc : z ≠ c)
    (hζ : 2 * ‖ζ - c‖ ≤ ‖z - c‖) :
    |kerPlane z ζ - taylorPlane m z c ζ| ≤ 2 * (‖ζ - c‖ / ‖z - c‖) ^ m := sorry

theorem abs_kerDisc_sub_taylorDisc_le {m : ℕ} (hm : 1 ≤ m) {z c ζ : ℂ} (hz : z ∈ 𝔻)
    (hc : c ∈ 𝔻) (hzc : z ≠ c) (hζ : 2 * ‖ζ - c‖ ≤ ‖z - c‖) :
    |kerDisc z ζ - taylorDisc m z c ζ| ≤
      2 * (1 - ‖z‖ ^ 2) * ‖ζ - c‖ ^ m / (‖z - c‖ ^ m * ‖1 - conj z * c‖) := sorry

/-- First-order remainder along a segment (disc far field, no convergent series needed). -/
theorem abs_kerDisc_sub_taylorDisc_two_le {z c ζ : ℂ} (hz : z ∈ 𝔻) {Bd : ℝ}
    (hseg : ∀ ξ ∈ segment ℝ c ζ, ξ ∈ 𝔻 ∧ ξ ≠ z)
    (hB : ∀ ξ ∈ segment ℝ c ζ, 2 * (1 - ‖z‖ ^ 2) / (‖z - ξ‖ ^ 2 * ‖1 - conj z * ξ‖) ≤ Bd) :
    |kerDisc z ζ - taylorDisc 2 z c ζ| ≤ Bd * ‖ζ - c‖ ^ 2 := sorry

theorem exists_poly_taylorPlane {m : ℕ} (hm : 1 ≤ m) (z c : ℂ) :
    ∃ p : Polynomial ℂ, p.natDegree < m ∧ ∀ ζ, taylorPlane m z c ζ = (p.eval ζ).re := sorry

theorem exists_poly_taylorDisc {m : ℕ} (hm : 1 ≤ m) (z c : ℂ) :
    ∃ p : Polynomial ℂ, p.natDegree < m ∧ ∀ ζ, taylorDisc m z c ζ = (p.eval ζ).re := sorry

/-- Moment cancellation. -/
theorem cellPot_eq_sub_poly {ν : Measure ℂ} {R : ℕ → Set ℂ} {Λ : ℕ → Multiset ℂ} {i m : ℕ}
    (hR : MeasurableSet (R i)) (hfin : ν (R i) < ∞) (hb : Bornology.IsBounded (R i))
    (hmom : ∀ j < m, ∫ ζ in R i, ζ ^ j ∂ν = ((Λ i).map (· ^ j)).sum)
    {k : ℂ → ℂ → ℝ} {z : ℂ} (hint : IntegrableOn (k z) (R i) ν)
    {T : ℂ → ℝ} {p : Polynomial ℂ} (hp : p.natDegree < m) (hT : ∀ ζ, T ζ = (p.eval ζ).re) :
    cellPot k ν R Λ i z =
      ((Λ i).map fun w ↦ k z w - T w).sum - ∫ ζ in R i, (k z ζ - T ζ) ∂ν := sorry

end OC
