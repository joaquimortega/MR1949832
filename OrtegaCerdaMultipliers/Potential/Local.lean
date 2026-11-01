import OrtegaCerdaMultipliers.Potential.Weyl

/-!
# M02 (Potentials) §4 — Smoothed point masses and local potentials

See `blueprint/M02_Potentials.md` §4.  Scaffold: statements, proofs `sorry`; the definitions are
real.  These replace the paper's global kernels `K[ν]` (doc §0).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The potential `G_s ≥ 0` of `δ₀ − bumpKernel s`: `Δ G_s = bumpKernel s − δ₀`,
`G_s = 0` off `ball 0 s`. -/
def bumpPot (s : ℝ) (x : ℂ) : ℝ := -(4 * Real.pi)⁻¹ * wFun (s ^ 2 / 4) (s ^ 2) x

theorem bumpPot_nonneg {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : x ≠ 0) : 0 ≤ bumpPot s x := sorry
theorem bumpPot_eq_zero {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : s ≤ ‖x‖) : bumpPot s x = 0 := sorry
theorem bumpPot_eq {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : x ≠ 0) :
    bumpPot s x = (4 * Real.pi)⁻¹ *
      (Real.log (s ^ 2 / ‖x‖ ^ 2) - sFun (1 / 4) 1 (‖x‖ ^ 2 / s ^ 2)) := sorry
theorem exists_bumpPot_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ s : ℝ, 0 < s → ∀ x : ℂ, x ≠ 0 → ‖x‖ < s →
    bumpPot s x ≤ (4 * Real.pi)⁻¹ * (Real.log (s ^ 2 / ‖x‖ ^ 2) + C₀) := sorry
theorem continuousOn_bumpPot_uncurry :
    ContinuousOn (Function.uncurry bumpPot) {p : ℝ × ℂ | 0 < p.1 ∧ p.2 ≠ 0} := sorry
theorem measurable_bumpPot : Measurable (Function.uncurry bumpPot) := sorry
theorem exists_integral_abs_bumpPot_le : ∃ C₁ : ℝ, ∀ s : ℝ, 0 < s →
    Integrable (bumpPot s) ∧ ∫ x, |bumpPot s x| ≤ C₁ * s ^ 2 := sorry

/-- **The smoothed point mass.** `Δ_z G_s(z − ζ) = bumpKernel s (· − ζ) − δ_ζ` weakly. -/
theorem integral_bumpPot_mul_laplacian {s : ℝ} (hs : 0 < s) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (ζ : ℂ) :
    ∫ z, bumpPot s (z - ζ) * Laplacian.laplacian χ z =
      ∫ z, bumpKernel s (z - ζ) * χ z - χ ζ := sorry

/-- Density of the smoothed measure `σ̃ = ∫ bumpKernel_{s(ζ)}(· − ζ) dσ(ζ)`. -/
def smoothedDensity (σ : Measure ℂ) (s : ℂ → ℝ) (x : ℂ) : ℝ≥0∞ :=
  ∫⁻ ζ, ENNReal.ofReal (bumpKernel (s ζ) (x - ζ)) ∂σ

/-- The local potential `V(z) = ∫ G_{s(ζ)}(z − ζ) dσ(ζ)`, with `ΔV = σ̃ − σ`. -/
def localPot (σ : Measure ℂ) (s : ℂ → ℝ) (z : ℂ) : ℝ :=
  ∫ ζ, bumpPot (s ζ) (z - ζ) ∂σ

/-- Standing hypotheses for a local potential on the open set `Ω`. -/
structure IsLocalPotData (Ω : Set ℂ) (σ : Measure ℂ) (s : ℂ → ℝ) : Prop where
  isOpen : IsOpen Ω
  measurable : Measurable s
  pos : ∀ ζ ∈ Ω, 0 < s ζ
  bdd : ∃ S : ℝ, ∀ ζ, s ζ ≤ S
  ball_subset : ∀ ζ ∈ Ω, ball ζ (s ζ) ⊆ Ω
  carried : σ Ωᶜ = 0
  sFinite : SFinite σ
  noAtoms : ∀ z, σ {z} = 0
  locFin : ∀ K ⊆ Ω, IsCompact K → σ {ζ | ∃ z ∈ K, dist z ζ < s ζ} < ∞
  logSmall : ∀ K ⊆ Ω, IsCompact K → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
    ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂σ ≤ ENNReal.ofReal η

namespace IsLocalPotData
variable {Ω : Set ℂ} {σ : Measure ℂ} {s : ℂ → ℝ}

theorem measurable_smoothedDensity (h : IsLocalPotData Ω σ s) :
    Measurable (smoothedDensity σ s) := sorry
theorem smoothedDensity_eq_zero (h : IsLocalPotData Ω σ s) {x : ℂ} (hx : x ∉ Ω) :
    smoothedDensity σ s x = 0 := sorry
theorem lintegral_smoothedDensity_lt_top (h : IsLocalPotData Ω σ s) {K : Set ℂ} (hK : K ⊆ Ω)
    (hKc : IsCompact K) : ∫⁻ x in K, smoothedDensity σ s x < ∞ := sorry
theorem measure_lt_top (h : IsLocalPotData Ω σ s) {K : Set ℂ} (hK : K ⊆ Ω)
    (hKc : IsCompact K) : σ K < ∞ := sorry
theorem localPot_nonneg (h : IsLocalPotData Ω σ s) (z : ℂ) : 0 ≤ localPot σ s z := sorry
theorem continuousOn_localPot (h : IsLocalPotData Ω σ s) : ContinuousOn (localPot σ s) Ω := sorry

/-- **`ΔV = σ̃ − σ` weakly.** -/
theorem integral_localPot_mul_laplacian (h : IsLocalPotData Ω σ s) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ Ω) :
    ∫ z, localPot σ s z * Laplacian.laplacian χ z =
      ∫ z, χ z ∂(volume.withDensity (smoothedDensity σ s)) - ∫ z, χ z ∂σ := sorry

end IsLocalPotData

/-- **Pointwise bound** (`C₀` from `exists_bumpPot_le`; universal). -/
theorem exists_localPot_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (Ω : Set ℂ) (σ : Measure ℂ) (s : ℂ → ℝ),
    IsLocalPotData Ω σ s → ∀ z : ℂ,
      ENNReal.ofReal (localPot σ s z) ≤
        ∫⁻ ζ in {ζ | dist z ζ < s ζ},
          ENNReal.ofReal ((4 * Real.pi)⁻¹ * (Real.log (s ζ ^ 2 / ‖z - ζ‖ ^ 2) + C₀)) ∂σ := sorry

end OC
