module

public import Mathlib

/-!
# Statement-level definitions

J. Ortega-Cerdà, *Multipliers and weighted ∂̄-estimates*, Rev. Mat. Iberoamericana **18** (2002),
355–377.

This file imports only `Mathlib` and contains every definition that appears in the statements of
the main theorems.  It is copied verbatim into `Challenge.lean` (the self-contained file checked by
`comparator`), so it must stay free of project imports.

Conventions (see `blueprint/M00_Defs.md`):

* `Δ` is the *standard* Laplacian `∂²/∂x² + ∂²/∂y²` (`Laplacian.laplacian`), as in the paper:
  `Δ log |z| = 2π δ₀`.
* Mathlib has no theory of subharmonic functions and their Riesz measures.  A weight is therefore a
  pair `(φ, μ)`: `φ` is continuous on the domain `Ω` and `Δφ = μ` in the sense of distributions,
  with `μ` a (positive) locally finite Borel measure carried by `Ω` (`IsSubharmonicWeight`).  Such
  a `φ` is exactly a continuous subharmonic function whose Riesz measure is `μ`.  The paper's
  weights (subharmonic, `Δφ` locally doubling) are automatically continuous ([Chr91, Lemma 2.3]),
  so assuming continuity loses nothing; this is recorded as a divergence.
* Distances: Euclidean in `ℂ`; in the disc the hyperbolic distance
  `β(z, w) = artanh ρ(z, w)`, where `ρ(z, w) = |z - w| / |1 - z̄ w|` is the pseudo-hyperbolic
  distance.
* All weighted norms are `ℝ≥0∞`-valued (`∫⁻`, `eLpNorm`), so that infinite quantities are `∞` and
  never silently become `0`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

@[expose] public noncomputable section

namespace OC

/-! ## Calculus -/

/-- The Cauchy–Riemann operator `∂̄f = ½(∂f/∂x + i ∂f/∂y)`. -/
def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 + I * fderiv ℝ f z I)

/-- `u` solves `∂̄u = g` on the open set `Ω` in the sense of distributions: `u, g` are locally
integrable on `Ω` and `∫ u ∂̄α = -∫ g α` for every smooth `α` with compact support in `Ω`. -/
def IsWeakDbarSol (Ω : Set ℂ) (u g : ℂ → ℂ) : Prop :=
  LocallyIntegrableOn u Ω ∧ LocallyIntegrableOn g Ω ∧
    ∀ α : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) α → HasCompactSupport α → tsupport α ⊆ Ω →
      ∫ z, u z * dbar α z = -∫ z, g z * α z

/-- `φ` is a *continuous subharmonic weight on `Ω` with Laplacian `μ`*: `φ` is continuous on `Ω`,
`μ` is a locally finite measure carried by `Ω`, and `Δφ = μ` on `Ω` in the sense of distributions,
`∫ φ Δχ dm = ∫ χ dμ` for every smooth real `χ` with compact support in `Ω` (standard Laplacian). -/
structure IsSubharmonicWeight (Ω : Set ℂ) (φ : ℂ → ℝ) (μ : Measure ℂ) : Prop where
  continuousOn : ContinuousOn φ Ω
  finite_of_compact : ∀ K ⊆ Ω, IsCompact K → μ K < ∞
  carried : μ Ωᶜ = 0
  laplacian_eq : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
    ∫ z, φ z * Laplacian.laplacian χ z = ∫ z, χ z ∂μ

/-! ## The disc and its hyperbolic geometry -/

/-- The open unit disc `𝔻`. -/
abbrev 𝔻 : Set ℂ := ball (0 : ℂ) 1

/-- The pseudo-hyperbolic distance `ρ(z, w) = |z - w| / |1 - z̄ w|`. -/
def pseudoHyp (z w : ℂ) : ℝ :=
  ‖z - w‖ / ‖1 - conj z * w‖

/-- The hyperbolic distance in `𝔻`, `β(z, w) = artanh ρ(z, w)`. -/
def hypDist (z w : ℂ) : ℝ :=
  Real.artanh (pseudoHyp z w)

/-- The hyperbolic disc `D(z, r) = {w ∈ 𝔻 : β(z, w) < r}`. -/
def hypBall (z : ℂ) (r : ℝ) : Set ℂ :=
  {w | w ∈ 𝔻 ∧ hypDist z w < r}

/-! ## Locally doubling measures (paper, §2) -/

/-- `μ` is *locally doubling* in `ℂ` (Euclidean distance): `μ(B(z, 2r)) ≤ C μ(B(z, r))` for every
ball `B(z, 2r)` of radius smaller than `1`. -/
def IsLocallyDoubling (μ : Measure ℂ) : Prop :=
  ∃ C : ℝ≥0, ∀ z : ℂ, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball z (2 * r)) ≤ C * μ (ball z r)

/-- `μ` is *doubling* in `ℂ`: `μ(B(z, 2r)) ≤ C μ(B(z, r))` for every ball. -/
def IsDoubling (μ : Measure ℂ) : Prop :=
  ∃ C : ℝ≥0, ∀ z : ℂ, ∀ r : ℝ, 0 < r → μ (ball z (2 * r)) ≤ C * μ (ball z r)

/-- `μ` is *locally doubling* in `𝔻` with respect to the hyperbolic distance. -/
def IsLocallyDoublingDisc (μ : Measure ℂ) : Prop :=
  ∃ C : ℝ≥0, ∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → 2 * r < 1 →
    μ (hypBall z (2 * r)) ≤ C * μ (hypBall z r)

/-- The interval `I(x, r) ⊆ ℝ ⊆ ℂ` of centre `x` and radius `r`. -/
def lineInterval (x r : ℝ) : Set ℂ :=
  (fun t : ℝ ↦ (t : ℂ)) '' Set.Ioo (x - r) (x + r)

/-- `μ` is carried by the real line and is *locally doubling* there (with respect to intervals). -/
def IsLocallyDoublingLine (μ : Measure ℂ) : Prop :=
  μ {z : ℂ | z.im ≠ 0} = 0 ∧ ∃ C : ℝ≥0, ∀ x : ℝ, ∀ r : ℝ, 0 < r → 2 * r < 1 →
    μ (lineInterval x (2 * r)) ≤ C * μ (lineInterval x r)

/-- The radius `ρ(z)` of the Euclidean disc of `μ`-mass one centred at `z` (paper, §2):
`ρ(z) = inf {r > 0 : μ(B(z, r)) ≥ 1}`. -/
def massRadius (μ : Measure ℂ) (z : ℂ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ 1 ≤ μ (ball z r)}

/-- The radius `ρ(z)` of the hyperbolic disc of `μ`-mass one centred at `z ∈ 𝔻`. -/
def massRadiusDisc (μ : Measure ℂ) (z : ℂ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ 1 ≤ μ (hypBall z r)}

/-- The radius `ρ(x)` of the interval of `μ`-mass one centred at `x ∈ ℝ`. -/
def massRadiusLine (μ : Measure ℂ) (x : ℝ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ 1 ≤ μ (lineInterval x r)}

/-- Euclidean distance from `z` to the set `Λ`, in `ℝ≥0∞` (`∞` if `Λ = ∅`). -/
def edistSet (z : ℂ) (Λ : Set ℂ) : ℝ≥0∞ :=
  ⨅ w ∈ Λ, edist z w

/-- Hyperbolic distance from `z` to `Λ ⊆ 𝔻`, in `ℝ≥0∞` (`∞` if `Λ = ∅`). -/
def hypDistSet (z : ℂ) (Λ : Set ℂ) : ℝ≥0∞ :=
  ⨅ w ∈ Λ, ENNReal.ofReal (hypDist z w)

/-! ## Weighted norms -/

/-- The measure `dm(z) / (1 - |z|²)` on `𝔻` used in Theorem 2. -/
def discMeasure : Measure ℂ :=
  (volume.restrict 𝔻).withDensity fun z ↦ ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2))

/-! ## The external theorem used for Theorem 3 -/

/-- A positive measure `ν` on `ℂ` is a *two-sided Carleson measure* (paper, p. 358) if
`ν(D(x, r)) ≤ C r` for all discs centred on the real line. -/
def IsTwoSidedCarleson (ν : Measure ℂ) : Prop :=
  ∃ C : ℝ≥0, ∀ x : ℝ, ∀ r : ℝ, 0 < r → ν (ball (x : ℂ) r) ≤ C * ENNReal.ofReal r

/-- `u` solves `∂̄u = μ` on `ℂ` in the sense of distributions, for the complex measure
`μ = σ ν` given by a positive measure `ν` and a density `σ` with `|σ| = 1` (so `|μ| = ν`):
`∫ u ∂̄α dm = -∫ α σ dν` for every smooth `α` with compact support. -/
def IsWeakDbarSolMeasure (u : ℂ → ℂ) (ν : Measure ℂ) (σ : ℂ → ℂ) : Prop :=
  LocallyIntegrable u ∧
    ∀ α : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) α → HasCompactSupport α →
      ∫ z, u z * dbar α z = -∫ z, α z * σ z ∂ν

/-- **The Ortega-Cerdà–Seip theorem** ([OCS99]; paper, p. 375), used as a black box in the proof
of Theorem 3, stated as a hypothesis.  Let `α > 0` and let `μ = σ ν` be a complex measure with
`ν = |μ|` finite and carried by a compact set `L`, such that `e^{-α|Im z|} d|μ|` is a two-sided
Carleson measure with constant `K`.  Then `∂̄u = μ` has a solution `u`, holomorphic off `L`, with
`|u(z)| e^{-α|Im z|} → 0` as `z → ∞` and `|u(x)| ≤ C (1 + ∫_{|z-x|<1} d|μ|(z) / |x - z|)` for
`x ∈ ℝ \ L`, where `C` depends only on `α` and `K`. -/
def TheoremOCS : Prop :=
  ∀ α : ℝ, 0 < α → ∀ K : ℝ≥0, ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
    IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
    (∀ x : ℝ, ∀ r : ℝ, 0 < r →
      (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-α * |z.im|))) (ball (x : ℂ) r) ≤
        K * ENNReal.ofReal r) →
    ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
      Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-α * |z.im|)) (Filter.cocompact ℂ) (nhds 0) ∧
      ∀ x : ℝ, (x : ℂ) ∉ L →
        ENNReal.ofReal ‖u x‖ ≤
          C * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν)

end OC
