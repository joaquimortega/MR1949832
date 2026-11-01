import OrtegaCerdaMultipliers.Potential.Radial
import OrtegaCerdaMultipliers.Potential.Fundamental

/-!
# M02 (Potentials) §2–§3 — Weyl's lemma for `Δ`; weights up to harmonic functions

See `blueprint/M02_Potentials.md` §2–§3.  Scaffold: statements, proofs `sorry`.

The `bumpKernel` API (stated in the doc's §4.1) is placed here, next to the definition, because
the proof of Weyl's lemma uses it.  The a.e. (`L¹_loc`) form of Weyl's lemma,
`exists_harmonicOnNhd_ae_eq_of_weakHarmonic`, is added for M07's `WeylLaplacianStmt`
(consumed by M08 and M13 through `LogModulusWeak.lean`).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Smooth radial probability density supported in `ball 0 s` (BOC `kernel` with
`a = s²/4`, `b = s²`). -/
def bumpKernel (s : ℝ) (x : ℂ) : ℝ := kernel (s ^ 2 / 4) (s ^ 2) x

/-! ### `bumpKernel` API (doc §4.1) -/

theorem contDiff_bumpKernel {s : ℝ} (hs : 0 < s) : ContDiff ℝ (⊤ : ℕ∞) (bumpKernel s) := sorry
theorem bumpKernel_nonneg {s : ℝ} (hs : 0 < s) (x : ℂ) : 0 ≤ bumpKernel s x := sorry
theorem bumpKernel_eq_zero {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : s ≤ ‖x‖) :
    bumpKernel s x = 0 := sorry
theorem integral_bumpKernel {s : ℝ} (hs : 0 < s) : ∫ x, bumpKernel s x = 1 := sorry
theorem bumpKernel_le {s : ℝ} (hs : 0 < s) (x : ℂ) :
    bumpKernel s x ≤ 4 / (Real.pi * s ^ 2) * (ball (0 : ℂ) s).indicator 1 x := sorry
theorem le_bumpKernel {s : ℝ} (hs : 0 < s) (x : ℂ) :
    1 / (Real.pi * s ^ 2) * (ball (0 : ℂ) (s / 2)).indicator 1 x ≤ bumpKernel s x := sorry
theorem measurable_bumpKernel : Measurable (Function.uncurry bumpKernel) := sorry

/-! ### Weyl's lemma -/

/-- **Mean-value form of Weyl.** A continuous weakly harmonic function equals its
`bumpKernel`-averages. -/
theorem eq_integral_bumpKernel_of_weakHarmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Ω)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ z, φ z * Laplacian.laplacian χ z = 0)
    {z : ℂ} {s : ℝ} (hs : 0 < s) (hzs : closedBall z s ⊆ Ω) :
    φ z = ∫ w, bumpKernel s (w - z) * φ w := sorry

/-- **Weyl's lemma for `Δ`.** A continuous weakly harmonic function is harmonic. -/
theorem harmonicOnNhd_of_weakHarmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Ω)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ z, φ z * Laplacian.laplacian χ z = 0) :
    InnerProductSpace.HarmonicOnNhd φ Ω := sorry

/-- **Weyl's lemma for `Δ`, `L¹_loc` form** (the body of M07's `WeylLaplacianStmt`): a locally
integrable weakly harmonic function is a.e. equal to a harmonic function.  (Mollify:
`φ * bumpKernel s` is smooth and weakly, hence classically, harmonic, and equals its own
`bumpKernel`-averages; let `s → 0`.) -/
theorem exists_harmonicOnNhd_ae_eq_of_weakHarmonic {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0) :
    ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u U ∧ ∀ᵐ z ∂(volume.restrict U), f z = u z :=
  sorry

/-! ### Weights up to harmonic functions; calculus of weights (§3) -/

theorem IsSubharmonicWeight.integrable_mul {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) {f : ℂ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    Integrable (fun z ↦ φ z * f z) := sorry

theorem IsSubharmonicWeight.sigmaFinite {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) : SigmaFinite μ := sorry

/-- **Uniqueness.** Two weights with the same Laplacian differ by a harmonic function. -/
theorem IsSubharmonicWeight.harmonicOnNhd_sub {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ₁ φ₂ : ℂ → ℝ}
    {μ : Measure ℂ} (h₁ : IsSubharmonicWeight Ω φ₁ μ) (h₂ : IsSubharmonicWeight Ω φ₂ μ) :
    InnerProductSpace.HarmonicOnNhd (fun z ↦ φ₁ z - φ₂ z) Ω := sorry

theorem IsSubharmonicWeight.add_harmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ H : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) (hH : InnerProductSpace.HarmonicOnNhd H Ω) :
    IsSubharmonicWeight Ω (fun z ↦ φ z + H z) μ := sorry

/-- A `C²` function with `Δu ≥ 0` is a weight, with Laplacian `Δu dm` on `Ω`. -/
theorem isSubharmonicWeight_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) (hpos : ∀ z ∈ Ω, 0 ≤ Laplacian.laplacian u z) :
    IsSubharmonicWeight Ω u
      (volume.withDensity (Ω.indicator fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z))) :=
  sorry

/-- Subtracting a `C²` function whose Laplacian is dominated by the absolutely continuous part
of the Laplacian (used for `ψ + c log(1−|z|²)` in M11 and `ψ − c|z|²` in M12). -/
theorem IsSubharmonicWeight.sub_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {ψ u : ℂ → ℝ}
    {ν₀ : Measure ℂ} {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (h : IsSubharmonicWeight Ω ψ (ν₀ + volume.withDensity g)) (hu : ContDiffOn ℝ 2 u Ω)
    (hΔ : ∀ z ∈ Ω, 0 ≤ Laplacian.laplacian u z ∧
      ENNReal.ofReal (Laplacian.laplacian u z) ≤ g z) :
    IsSubharmonicWeight Ω (fun z ↦ ψ z - u z)
      (ν₀ + volume.withDensity
        (fun z ↦ g z - Ω.indicator (fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z)) z)) :=
  sorry

end OC
