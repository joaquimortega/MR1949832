module

public import Mathlib

/-!
# Statement-level definitions

J. Ortega-Cerdà and K. Seip, *Multipliers for entire functions and an interpolation problem of
Beurling*, J. Funct. Anal. **162** (1999), 400–415.

This file imports only `Mathlib` and contains every definition that appears in the statements of
the main theorems.  It is copied verbatim into `OCSChallenge.lean` (the self-contained file checked
by `comparator`), so it must stay free of project imports.

Conventions (see `blueprint/M00_Defs.md`):

* A "sequence" `Λ` of distinct points is a subset of `ℂ`; the paper never uses the enumeration.
* Data to interpolate are functions `a : ℂ → ℂ`, of which only the values on `Λ` matter.
* `∂̄ = ½(∂/∂x + i ∂/∂y)` (`dbar`), so that `∂̄ (1/(π z)) = δ₀`.
* Sums, counts and suprema that may be infinite are `ℝ≥0∞`-valued, so that they never silently
  become `0`.
* The densities `D⁺`, `D⁻` are defined with `limsup`/`liminf` in `r` and `⨆` in `A`.  The paper
  writes `lim_{A→∞} lim_{r→∞}`; the counting functions are monotone in `A`, so `lim_{A→∞} = ⨆_A`,
  and the inner limits exist for separated sequences, where they equal the `limsup`/`liminf`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

@[expose] public noncomputable section

namespace OCS

/-! ## The `∂̄` operator -/

/-- The Cauchy–Riemann operator `∂̄f = ½(∂f/∂x + i ∂f/∂y)`. -/
def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 + I * fderiv ℝ f z I)

/-- `u` solves `∂̄u = μ` on `ℂ` in the sense of distributions, for the complex measure `μ = σ ν`
given by a positive measure `ν` and a density `σ` with `|σ| = 1` (so `|μ| = ν`):
`∫ u ∂̄α dm = -∫ α σ dν` for every smooth `α` with compact support.  (Identical to the definition
of the companion project MR1949832, `OC.IsWeakDbarSolMeasure`.) -/
def IsWeakDbarSolMeasure (u : ℂ → ℂ) (ν : Measure ℂ) (σ : ℂ → ℂ) : Prop :=
  LocallyIntegrable u ∧
    ∀ α : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) α → HasCompactSupport α →
      ∫ z, u z * dbar α z = -∫ z, α z * σ z ∂ν

/-! ## Carleson measures and sequences (paper, pp. 401 and 409) -/

/-- A positive measure `ν` on `ℂ` is a *two-sided Carleson measure* (p. 409) if
`ν(D(x, r)) ≤ K r` for every disc centred on the real line.  (Identical to `OC.IsTwoSidedCarleson`
of MR1949832.) -/
def IsTwoSidedCarleson (ν : Measure ℂ) : Prop :=
  ∃ C : ℝ≥0, ∀ x : ℝ, ∀ r : ℝ, 0 < r → ν (ball (x : ℂ) r) ≤ C * ENNReal.ofReal r

/-- The distance function `σ(z, ζ) = |z - ζ| / (1 + |z - ζ̄|)` (p. 401).  Near the real axis it is
comparable to the Euclidean distance; far from it, within a half-plane, to the pseudo-hyperbolic
distance `|z - ζ|/|z - ζ̄|`. -/
def sigmaDist (z ζ : ℂ) : ℝ :=
  ‖z - ζ‖ / (1 + ‖z - conj ζ‖)

/-- `Λ` is *separated* (p. 401): `σ(λ, λ') ≥ δ` for distinct `λ, λ' ∈ Λ`, for some `δ > 0`.  This is
Euclidean separation together with pseudo-hyperbolic separation within each half-plane. -/
def IsSeparated (Λ : Set ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → δ ≤ sigmaDist a b

/-- `Λ` satisfies the *two-sided Carleson condition* (p. 401): for every disc `D` centred on the
real axis, `∑_{λ ∈ D ∩ Λ} |Im λ| ≤ C r(D)`. -/
def IsTwoSidedCarlesonSeq (Λ : Set ℂ) : Prop :=
  ∃ C : ℝ≥0, ∀ x : ℝ, ∀ r : ℝ, 0 < r →
    (∑' w : ↥(Λ ∩ ball (x : ℂ) r), ENNReal.ofReal |(w : ℂ).im|) ≤ C * ENNReal.ofReal r

/-! ## The Bernstein space `𝓑_τ` (p. 401) -/

/-- `f` has *exponential type at most `τ`*: for every `ε > 0`, `|f(z)| ≤ C_ε e^{(τ+ε)|z|}`. -/
def IsExpTypeLE (τ : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp ((τ + ε) * ‖z‖)

/-- The *Bernstein space* `𝓑_τ`: entire functions of exponential type at most `τ` whose
restriction to the real line is bounded. -/
def MemBernstein (τ : ℝ) (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ IsExpTypeLE τ f ∧ ∃ M : ℝ, ∀ x : ℝ, ‖f x‖ ≤ M

/-- `Λ` is an *interpolating sequence for `𝓑_τ`* (p. 401): every datum with
`sup_λ |a(λ)| e^{-τ|Im λ|} < ∞` is the restriction to `Λ` of some `f ∈ 𝓑_τ`. -/
def IsInterpolating (τ : ℝ) (Λ : Set ℂ) : Prop :=
  ∀ a : ℂ → ℂ, (∃ M : ℝ, ∀ w ∈ Λ, ‖a w‖ * Real.exp (-τ * |w.im|) ≤ M) →
    ∃ f : ℂ → ℂ, MemBernstein τ f ∧ ∀ w ∈ Λ, f w = a w

/-- `Λ` is interpolating for `𝓑_τ` *with constant `K`* (p. 403): every datum with
`|a(λ)| e^{-τ|Im λ|} ≤ M` on `Λ` is interpolated by some `f ∈ 𝓑_τ` with `‖f‖_{L^∞(ℝ)} ≤ K M`. -/
def IsInterpolatingWithConst (τ : ℝ) (Λ : Set ℂ) (K : ℝ) : Prop :=
  ∀ a : ℂ → ℂ, ∀ M : ℝ, (∀ w ∈ Λ, ‖a w‖ * Real.exp (-τ * |w.im|) ≤ M) →
    ∃ f : ℂ → ℂ, MemBernstein τ f ∧ (∀ w ∈ Λ, f w = a w) ∧ ∀ x : ℝ, ‖f x‖ ≤ K * M

/-- `Λ` is a *sampling sequence for `𝓑_τ`* (p. 412):
`sup_{z ∈ ℂ} |f(z)| e^{-τ|Im z|} ≲ sup_{λ ∈ Λ} |f(λ)| e^{-τ|Im λ|}` for all `f ∈ 𝓑_τ`. -/
def IsSampling (τ : ℝ) (Λ : Set ℂ) : Prop :=
  ∃ C : ℝ≥0, ∀ f : ℂ → ℂ, MemBernstein τ f →
    (⨆ z : ℂ, ENNReal.ofReal (‖f z‖ * Real.exp (-τ * |z.im|))) ≤
      C * ⨆ w ∈ Λ, ENNReal.ofReal (‖f w‖ * Real.exp (-τ * |w.im|))

/-! ## Uniform densities (pp. 401 and 413) -/

/-- The open rectangle `{z = x + iy : t < x < t + r, |y| < A}`. -/
def rect (t r A : ℝ) : Set ℂ :=
  {z : ℂ | t < z.re ∧ z.re < t + r ∧ |z.im| < A}

/-- `n⁺_A(r)`: the maximal number of points of `Λ` in a rectangle `{t < x < t + r, |y| < A}`. -/
def nPlus (Λ : Set ℂ) (A r : ℝ) : ℝ≥0∞ :=
  ⨆ t : ℝ, ((Λ ∩ rect t r A).encard : ℝ≥0∞)

/-- `n⁻_A(r)`: the minimal number of points of `Λ` in a rectangle `{t < x < t + r, |y| < A}`. -/
def nMinus (Λ : Set ℂ) (A r : ℝ) : ℝ≥0∞ :=
  ⨅ t : ℝ, ((Λ ∩ rect t r A).encard : ℝ≥0∞)

/-- The *upper uniform density* `D⁺(Λ) = lim_{A→∞} lim_{r→∞} n⁺_A(r)/r` (p. 401). -/
def upperDensity (Λ : Set ℂ) : ℝ≥0∞ :=
  ⨆ A : ℝ, limsup (fun r : ℝ ↦ nPlus Λ A r / ENNReal.ofReal r) atTop

/-- The *lower uniform density* `D⁻(Λ) = lim_{A→∞} lim_{r→∞} n⁻_A(r)/r` (p. 413). -/
def lowerDensity (Λ : Set ℂ) : ℝ≥0∞ :=
  ⨆ A : ℝ, liminf (fun r : ℝ ↦ nMinus Λ A r / ENNReal.ofReal r) atTop

/-! ## The multiplier lemma (Lemma 3, p. 405) -/

/-- The subharmonic function of Lemma 3,
`U(z) = ∫_ℝ [log|1 - z/t| + (1 - χ_{[-1,1]}(t)) Re(z/t)] m(t) dt + C`. -/
def multU (m : ℝ → ℝ) (C : ℝ) (z : ℂ) : ℝ :=
  (∫ t : ℝ, (Real.log ‖1 - z / t‖ + (1 - (Icc (-1 : ℝ) 1).indicator 1 t) * (z / t).re) * m t)
    + C

/-! ## External results used as black boxes

The paper quotes the following results of Beurling [B] without proof.  They enter the formal
statements as explicit hypotheses, never as axioms.  Each `Prop` below is implied by the statement in
the source (see `blueprint/M00_Defs.md`). -/

/-- **Beurling's Lemma 2** ([B, p. 353]; paper, p. 403), in the form used on p. 404: given
`τ, δ, k > 0` there is `C > 0` such that, if `Λ` is interpolating for `𝓑_τ` with constant `k` and
`x ∈ ℝ` has distance at least `δ` from `Λ`, then some `φ ∈ 𝓑_τ` vanishing on `Λ` with
`|φ| ≤ 1` on `ℝ` has `|φ(x)| ≥ C` (i.e. `ρ(x, Λ) ≥ C`). -/
def BeurlingLemma2 : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ δ : ℝ, 0 < δ → ∀ k : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ (Λ : Set ℂ) (x : ℝ), IsInterpolatingWithConst τ Λ k → (∀ w ∈ Λ, δ ≤ ‖(x : ℂ) - w‖) →
      ∃ φ : ℂ → ℂ, MemBernstein τ φ ∧ (∀ w ∈ Λ, φ w = 0) ∧ (∀ y : ℝ, ‖φ y‖ ≤ 1) ∧
        C ≤ ‖φ x‖

/-- **Beurling's stability theorem** in the form used on p. 413 (the paper's extension to complex
sequences of [B, Theorem 4, p. 345], quoted without proof): a separated sampling
sequence for `𝓑_τ` is also sampling for `𝓑_{τ+δ}` for some `δ > 0`. -/
def BeurlingStability : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ Λ : Set ℂ, IsSeparated Λ → IsSampling τ Λ →
    ∃ δ : ℝ, 0 < δ ∧ IsSampling (τ + δ) Λ

/-! ## The form of Lemma 4 quoted in MR1949832

The companion formalization of Ortega-Cerdà, *Multipliers and weighted ∂̄-estimates* (MR1949832)
uses Lemma 4 of this paper, in the form quoted on p. 375 of that paper, as the hypothesis
`OC.TheoremOCS`.  `TheoremOCS` below is a verbatim copy (namespace `OCS`); it is *proved* here
(`OCS.theoremOCS`).  It differs from Lemma 4 as printed by `limsup = 0` instead of `< ∞`, and by
asking `u` to be holomorphic off the support. -/

/-- **Lemma 4 as quoted in MR1949832** (verbatim copy of `OC.TheoremOCS`).  Let `α > 0` and let
`μ = σ ν` be a complex measure with `ν = |μ|` finite and carried by a compact set `L`, such that
`e^{-α|Im z|} d|μ|` is a two-sided Carleson measure with constant `K`.  Then `∂̄u = μ` has a
solution `u`, holomorphic off `L`, with `|u(z)| e^{-α|Im z|} → 0` as `z → ∞` and
`|u(x)| ≤ C (1 + ∫_{|z-x|<1} d|μ|(z) / |x - z|)` for `x ∈ ℝ \ L`, where `C` depends only on `α`
and `K`. -/
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

end OCS
