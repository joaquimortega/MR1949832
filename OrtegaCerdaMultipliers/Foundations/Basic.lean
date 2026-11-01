import OrtegaCerdaMultipliers.Defs

/-!
# M01 (Foundations) — Auxiliary definitions copied from BOC

See `blueprint/M01_Foundations.md`.

The files in `OrtegaCerdaMultipliers/Foundations/` are copied from the companion project
`BerndtssonOrtegaCerda` (directory `../MR1340337`, commit `22104d9`), so that this project
does not depend on it.  The copied files use some definitions of the BOC file `Defs.lean` that are
not in `OrtegaCerdaMultipliers/Defs.lean`.  They are collected here, with the *same* definitions as
in BOC (`BerndtssonOrtegaCerda/Defs.lean`, commit `22104d9`).

Definitions present in both projects:

* `dbar`, `IsWeakDbarSol` and `𝔻` are textually identical in the two `Defs.lean` files.
* `pseudoHyp` differs: BOC sets `pseudoHyp z ζ = ‖mobius z ζ‖ = ‖(z - ζ) / (1 - z̄ ζ)‖`, while RMI
  sets `pseudoHyp z w = ‖z - w‖ / ‖1 - z̄ w‖`.  They agree by `norm_div`
  (`pseudoHyp_eq_norm_mobius`), and the copied proofs are adapted with this lemma.

Laplacian conventions: RMI's `Defs.lean` uses the standard Laplacian `Laplacian.laplacian`
(`Δ log |z| = 2π δ₀`), whereas the copied Wirtinger calculus is written in terms of BOC's
`lap φ = ¼ Δφ = ∂²φ/∂z∂z̄`.  The bridge is `laplacian_eq_four_mul_lap`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- BOC's Laplacian `∂²/∂z∂z̄`, i.e. `1/4` of the standard Laplacian `∂²/∂x² + ∂²/∂y²`
(copied from `BerndtssonOrtegaCerda/Defs.lean`). -/
def lap (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  (1 / 4 : ℝ) * Laplacian.laplacian φ z

/-- The standard Laplacian is `4 lap`. -/
theorem laplacian_eq_four_mul_lap (φ : ℂ → ℝ) (z : ℂ) :
    Laplacian.laplacian φ z = 4 * lap φ z := by
  unfold lap
  ring

/-- `Γ` is *uniformly separated*: the distances between distinct points are bounded below by a
positive constant (copied from `BerndtssonOrtegaCerda/Defs.lean`). -/
def IsSeparated (Γ : Set ℂ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b

/-- The disc automorphism `φ_z(ζ) = (z - ζ) / (1 - z̄ ζ)` (copied from
`BerndtssonOrtegaCerda/Defs.lean`). -/
def mobius (z ζ : ℂ) : ℂ :=
  (z - ζ) / (1 - conj z * ζ)

/-- RMI's `pseudoHyp` is the modulus of the Möbius map, which is BOC's definition of `pseudoHyp`. -/
theorem pseudoHyp_eq_norm_mobius (z ζ : ℂ) : pseudoHyp z ζ = ‖mobius z ζ‖ := by
  rw [pseudoHyp, mobius, norm_div]

/-- `Γ ⊆ 𝔻` is uniformly separated in the pseudo-hyperbolic distance (copied from
`BerndtssonOrtegaCerda/Defs.lean`; `pseudoHyp` is RMI's, equal to BOC's by
`pseudoHyp_eq_norm_mobius`). -/
def IsDiskSeparated (Γ : Set ℂ) : Prop :=
  Γ ⊆ 𝔻 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ pseudoHyp a b

/-- The invariant Laplacian `Δ̃ = (1 - |z|²)² ∂²/∂z∂z̄` (copied from
`BerndtssonOrtegaCerda/Defs.lean`). -/
def invLap (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  (1 - ‖z‖ ^ 2) ^ 2 * lap φ z

/-- Density of the invariant measure: `dλ = dm / (π (1 - |z|²)²)` (copied from
`BerndtssonOrtegaCerda/Defs.lean`). -/
def invDensity (ζ : ℂ) : ℝ :=
  (Real.pi * (1 - ‖ζ‖ ^ 2) ^ 2)⁻¹

end OC
