import OrtegaCerdaMultipliers.Doubling.Export

/-!
# M03 (Doubling) — Quantitative forms: constants depending only on `(C_d, R₀)`

See `blueprint/M03_Doubling.md` §4 and `blueprint/M08_Multiplier.md` §1.1, §4.1.  Scaffold:
statements, proofs `sorry`; definitions are real.

M08 and M09 prove Theorem 4 and Proposition 2 with constants depending only on the doubling
constant `C_d` and the mass radius `R₀` (README §3a.6).  The classes `MeasClassPlane`,
`MeasClassDisc`, the explicit-constant doubling predicates and the normalisation `lapNorm`
(written in the M08 doc) are defined here, because the quantitative M03 lemmas below and M05's
`lemma4_*_quant` are stated with them.  Each lemma is the uniform version of a qualitative
`Doubling/Export.lean` statement: `∀ Cd R₀, ∃ C, ∀ μ in the class, …`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- `Δψ/(2π)`.  With this normalisation a zero of `h` contributes exactly one unit of mass:
`Δ log|h| = 2π Σ δ_λ` and `Δψ = 2π · lapNorm μ`. -/
def lapNorm (μ : Measure ℂ) : Measure ℂ := (ENNReal.ofReal (2 * Real.pi))⁻¹ • μ

/-- Local doubling with an explicit constant (plane). -/
def IsLocallyDoublingWith (μ : Measure ℂ) (Cd : ℝ≥0) : Prop :=
  ∀ z : ℂ, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball z (2 * r)) ≤ Cd * μ (ball z r)

/-- Local doubling with an explicit constant (disc, hyperbolic balls). -/
def IsLocallyDoublingDiscWith (μ : Measure ℂ) (Cd : ℝ≥0) : Prop :=
  ∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (hypBall z (2 * r)) ≤ Cd * μ (hypBall z r)

/-- The class of measures with parameters `(Cd, R₀)` (plane). -/
structure MeasClassPlane (ν : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocallyDoublingWith ν Cd
  mass : ∀ z : ℂ, 1 < ν (ball z R₀)
  finite : ∀ K : Set ℂ, IsCompact K → ν K < ∞

/-- The class of measures with parameters `(Cd, R₀)` (disc). -/
structure MeasClassDisc (ν : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocallyDoublingDiscWith ν Cd
  mass : ∀ z ∈ 𝔻, 1 < ν (hypBall z R₀)
  finite : ∀ K ⊆ 𝔻, IsCompact K → ν K < ∞

/-- Local doubling with an explicit constant (line; `μ` carried by `ℝ`). -/
def IsLocallyDoublingLineWith (μ : Measure ℂ) (Cd : ℝ≥0) : Prop :=
  μ {z : ℂ | z.im ≠ 0} = 0 ∧ ∀ x : ℝ, ∀ r : ℝ, 0 < r → 2 * r < 1 →
    μ (lineInterval x (2 * r)) ≤ Cd * μ (lineInterval x r)

/-- The class of measures with parameters `(Cd, R₀)` (line). -/
structure MeasClassLine (ν : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocallyDoublingLineWith ν Cd
  mass : ∀ x : ℝ, 1 < ν (lineInterval x R₀)
  finite : ∀ K : Set ℂ, IsCompact K → ν K < ∞

/-! ### The abstract theory with explicit constants

Each lemma is the uniform version of the corresponding `Doubling/Abstract.lean` statement: the
constants are chosen after the doubling constant `Cd` and the mass radius `R₀` (and the displayed
auxiliary parameters), and before the measure.  The `ℂ`-level forms below are thin wrappers
through `ℂ` itself, `discPull` and `linePull` (`MeasClassPlane.measClassM`,
`MeasClassDisc.measClassM_discPull`, `MeasClassLine.measClassM_linePull`). -/

section AbstractQuant

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Local doubling on a metric space with an explicit constant. -/
def IsLocDoublingMWith (μ : Measure X) (Cd : ℝ≥0) : Prop :=
  ∀ x : X, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball x (2 * r)) ≤ Cd * μ (ball x r)

/-- The abstract class with parameters `(Cd, R₀)`: explicit doubling constant, every ball of
radius `R₀` has mass `≥ 1`, balls have finite mass. -/
structure MeasClassM (μ : Measure X) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocDoublingMWith μ Cd
  mass : ∀ x : X, 1 ≤ μ (ball x R₀)
  finite : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞

omit [OpensMeasurableSpace X] in
theorem IsLocDoublingMWith.isLocDoublingM {μ : Measure X} {Cd : ℝ≥0}
    (h : IsLocDoublingMWith μ Cd) : IsLocDoublingM μ :=
  ⟨Cd, h⟩

theorem doubling_upTo_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ μ : Measure X, IsLocDoublingMWith μ Cd → ∀ x : X, ∀ r : ℝ, 0 < r →
      r ≤ R₁ → μ (ball x (2 * r)) ≤ C * μ (ball x r) := sorry

theorem measure_ball_le_rpow_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ μ : Measure X, IsLocDoublingMWith μ Cd →
      ∀ (x x' : X) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ → dist x x' ≤ r →
        μ (ball x r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (ball x' r') := sorry

theorem rpow_le_measure_ball_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ μ : Measure X, IsLocDoublingMWith μ Cd →
      ∀ (x x' : X) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ → dist x x' ≤ r →
        ENNReal.ofReal (c * (r / r') ^ δ) * μ (ball x' r') ≤ μ (ball x r) := sorry

/-- **Lemma 1**, uniform form. -/
theorem lemma1_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ γ A : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < A ∧ ∀ μ : Measure X, IsLocDoublingMWith μ Cd →
      ∀ (x x' : X) (r r' : ℝ), 0 < r' → r ≤ R₁ → dist x x' + r' ≤ r →
        0 < μ (ball x' r') → μ (ball x r) < ∞ →
        ((μ (ball x r)).toReal / (μ (ball x' r')).toReal) ^ γ ≤ A * (r / r') ∧
        r / r' ≤ A * ((μ (ball x r)).toReal / (μ (ball x' r')).toReal) ^ (1 / γ) := sorry

theorem measure_ball_massRadiusM_bounds_quant [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] (Cd : ℝ≥0) (R₀ R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ →
      ∀ (x : X) (r : ℝ), massRadiusM μ x ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusM μ x) ^ δ) ≤ μ (ball x r) ∧
        μ (ball x r) ≤ ENNReal.ofReal (C * (r / massRadiusM μ x) ^ s) := sorry

theorem measure_ball_massRadiusM_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ K : ℝ) :
    ∃ C : ℝ≥0, ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ x : X,
      μ (ball x (K * massRadiusM μ x)) ≤ C := sorry

/-- **Claim 1**, uniform form, with `0 < ρ ≤ R₀`. -/
theorem claim1_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ K : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ x y : X,
      0 < massRadiusM μ x ∧ massRadiusM μ x ≤ R₀ ∧
      (dist x y ≤ K * max (massRadiusM μ x) (massRadiusM μ y) →
        massRadiusM μ x ≤ C * massRadiusM μ y) := sorry

/-- **Decay**, power form, uniform. -/
theorem massRadiusM_div_dist_le_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ M₀ : ℝ) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α ≤ 1 ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ z ζ : X,
      massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * (massRadiusM μ z / dist z ζ) ^ α := sorry

/-- **Decay**, geometric form, uniform. -/
theorem decay_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ →
      ∀ (z ζ : X) (n : ℕ), 2 ^ n * massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * θ ^ n := sorry

/-- **Lemma 3**, truncated form, uniform. -/
theorem lemma3_quant [BallGeometry X] [TopologicalSpace.SeparableSpace X] (Cd : ℝ≥0) (R₀ : ℝ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0,
      ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ w : X,
        ∫⁻ z in ball w R₁,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ ≤ C :=
  sorry

/-- **[Chr91, Lemma 2.3]**, uniform form. -/
theorem christ_lemma23_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ μ : Measure X, IsLocDoublingMWith μ Cd → ∀ (x : X) (R : ℝ), 0 < R → R ≤ R₁ →
      ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ ≤ C * μ (ball x R) := sorry

/-- Mass radius of `N⁻¹ μ` versus `μ`, uniform. -/
theorem massRadiusM_inv_smul_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ x : X,
      massRadiusM μ x ≤ massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ∧
        massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ≤ C * massRadiusM μ x := sorry

end AbstractQuant

/-! ### Transfer of the classes to the abstract setting -/

theorem MeasClassPlane.measClassM {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (h : MeasClassPlane μ Cd R₀) : MeasClassM μ Cd R₀ :=
  ⟨h.doubling, fun z ↦ (h.mass z).le, fun z r ↦
    (measure_mono ball_subset_closedBall).trans_lt (h.finite _ (isCompact_closedBall z r))⟩

theorem MeasClassDisc.measClassM_discPull {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (h : MeasClassDisc μ Cd R₀) : MeasClassM (discPull μ) Cd R₀ := sorry

theorem MeasClassLine.measClassM_linePull {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (h : MeasClassLine μ Cd R₀) : MeasClassM (linePull μ) Cd R₀ := sorry

theorem MeasClassPlane.of_weight {φ : ℂ → ℝ} {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingWith μ Cd)
    (hm : ∀ z : ℂ, 1 < μ (ball z R₀)) : MeasClassPlane μ Cd R₀ :=
  ⟨hd, hm, fun K hK ↦ hφ.finite_of_compact K (subset_univ K) hK⟩

theorem MeasClassDisc.of_weight {φ : ℂ → ℝ} {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hφ : IsSubharmonicWeight 𝔻 φ μ) (hd : IsLocallyDoublingDiscWith μ Cd)
    (hm : ∀ z ∈ 𝔻, 1 < μ (hypBall z R₀)) : MeasClassDisc μ Cd R₀ :=
  ⟨hd, hm, fun K hK hKc ↦ hφ.finite_of_compact K hK hKc⟩

/-! ### Quantitative lemmas (requested by M08 §4.1) -/

/-- (M03, growth + scaling) `lapNorm` stays in a class; `ρ` and `ρ̃` are comparable. -/
theorem MeasClassPlane.lapNorm {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} (h : MeasClassPlane μ Cd R₀) :
    MeasClassPlane (lapNorm μ) Cd (15 * R₀) := sorry
theorem MeasClassDisc.lapNorm {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} (h : MeasClassDisc μ Cd R₀) :
    MeasClassDisc (lapNorm μ) Cd (15 * R₀) := sorry
theorem massRadius_lapNorm_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure ℂ, MeasClassPlane μ Cd R₀ → ∀ z,
      massRadius μ z ≤ massRadius (lapNorm μ) z ∧ massRadius (lapNorm μ) z ≤ C * massRadius μ z :=
  sorry
theorem massRadiusDisc_lapNorm_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure ℂ, MeasClassDisc μ Cd R₀ → ∀ z ∈ 𝔻,
      massRadiusDisc μ z ≤ massRadiusDisc (lapNorm μ) z ∧
        massRadiusDisc (lapNorm μ) z ≤ C * massRadiusDisc μ z := sorry

/-- (M03, quantitative Claim 1 + positivity/upper bound of `ρ`). -/
theorem claim1_plane_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z w : ℂ,
      0 < massRadius ν z ∧ massRadius ν z ≤ R₀ ∧
      (dist z w ≤ K * max (massRadius ν z) (massRadius ν w) →
        massRadius ν z ≤ C * massRadius ν w) := sorry
theorem claim1_disc_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ w ∈ 𝔻,
      0 < massRadiusDisc ν z ∧ massRadiusDisc ν z ≤ R₀ ∧
      (hypDist z w ≤ K * max (massRadiusDisc ν z) (massRadiusDisc ν w) →
        massRadiusDisc ν z ≤ C * massRadiusDisc ν w) := sorry

/-- (M03, quantitative) mass of comparable balls. -/
theorem measure_ball_massRadius_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z, ν (ball z (K * massRadius ν z)) ≤ C := sorry
theorem measure_hypBall_massRadius_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻,
      ν (hypBall z (K * massRadiusDisc ν z)) ≤ C := sorry

/-- (M03, quantitative decay; `massRadiusM_div_dist_le` with `M₀ = 1/4`). -/
theorem decay_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z ζ : ℂ,
      massRadius ν z ≤ dist z ζ → dist z ζ ≤ 1 / 4 →
        massRadius ν ζ / dist z ζ ≤ C * (massRadius ν z / dist z ζ) ^ α := sorry
theorem decay_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻,
      massRadiusDisc ν z ≤ hypDist z ζ → hypDist z ζ ≤ 1 / 4 →
        massRadiusDisc ν ζ / hypDist z ζ ≤ C * (massRadiusDisc ν z / hypDist z ζ) ^ α := sorry

/-- (M03, quantitative [Chr91, Lemma 2.3]). -/
theorem christ_plane_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z : ℂ, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ ζ in ball z s, ENNReal.ofReal (Real.log (s / dist z ζ)) ∂ν ≤ C * ν (ball z s) := sorry
theorem christ_disc_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ ζ in hypBall z s, ENNReal.ofReal (Real.log (s / hypDist z ζ)) ∂ν ≤
        C * ν (hypBall z s) := sorry


/-! ### Line forms (uniform) -/

theorem claim1_line_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ → ∀ x y : ℝ,
      0 < massRadiusLine ν x ∧ massRadiusLine ν x ≤ R₀ ∧
      (|x - y| ≤ K * max (massRadiusLine ν x) (massRadiusLine ν y) →
        massRadiusLine ν x ≤ C * massRadiusLine ν y) := sorry

theorem decay_line_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ → ∀ x y : ℝ,
      massRadiusLine ν x ≤ |x - y| → |x - y| ≤ 1 / 4 →
        massRadiusLine ν y / |x - y| ≤ C * (massRadiusLine ν x / |x - y|) ^ α := sorry

theorem christ_line_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ → ∀ x : ℝ, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ z in lineInterval x s, ENNReal.ofReal (Real.log (s / |z.re - x|)) ∂ν ≤
        C * ν (lineInterval x s) := sorry

end OC
