import OrtegaCerdaSeip.Defs

/-!
# M01 (Foundations) — Auxiliary definitions for the copied foundation files

See `blueprint/M01_Foundations.md`.

The files `Foundations/{Wirtinger,Polar,Pompeiu,LocalEstimates,Weyl}.lean` are copied from the
companion project `../MR1949832` (github.com/joaquimortega/MR1949832, commit `4aa833e`), which
copied them in turn from `../MR1340337`.  They use two definitions that are not statement-level in
this project, so they are not in `Defs.lean`; they are collected here, with the *same* definitions as
in MR1949832 (`OC.lap` in `Foundations/Basic.lean`, `OC.IsWeakDbarSol` in `Defs.lean`).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-- The Laplacian `∂²/∂z∂z̄`, i.e. `1/4` of the standard Laplacian `∂²/∂x² + ∂²/∂y²` (copied from
MR1949832, `OC.lap`). -/
def lap (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  (1 / 4 : ℝ) * Laplacian.laplacian φ z

/-- The standard Laplacian is `4 lap`. -/
theorem laplacian_eq_four_mul_lap (φ : ℂ → ℝ) (z : ℂ) :
    Laplacian.laplacian φ z = 4 * lap φ z := by
  unfold lap
  ring

/-- `u` solves `∂̄u = g` on the open set `Ω` in the sense of distributions: `u, g` are locally
integrable on `Ω` and `∫ u ∂̄α = -∫ g α` for every smooth `α` with compact support in `Ω` (copied
from MR1949832, `OC.IsWeakDbarSol`). -/
def IsWeakDbarSol (Ω : Set ℂ) (u g : ℂ → ℂ) : Prop :=
  LocallyIntegrableOn u Ω ∧ LocallyIntegrableOn g Ω ∧
    ∀ α : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) α → HasCompactSupport α → tsupport α ⊆ Ω →
      ∫ z, u z * dbar α z = -∫ z, g z * α z

end OCS
