import OrtegaCerdaMultipliers.Potential.Local
import OrtegaCerdaMultipliers.Doubling.Quant
import OrtegaCerdaMultipliers.Foundations.HyperbolicExtra

/-!
# M04 (Regularization) — Lemma 6: regularization of the weight

See `blueprint/M04_Regularization.md`.  Scaffold: statements, proofs `sorry`; the definitions are
real.

Lemma 6 in `ℂ` and `𝔻`, via the compactly supported local potentials of M02 §4 applied to
`σ = w·μ` with `w(ζ) = 1/(2μ(B(ζ,R)))`.  Reconciliation: `logSmall_plane`, `logSmall_disc` moved
to M03 (`Doubling/Export.lean`); M03's names are used for (A1)–(A4) (`doubling_upTo_*`,
`christ_lemma23_*`, `rpow_le_measure_*`, `measure_singleton_*`); the forms of Lemma 6 consumed by
M11/M12 are the corollaries `lemma6_disc_hypArea`, `lemma6_plane_volume`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The weight `w(ζ) = 1/(2 μ(B(ζ,R)))` (plane). -/
def massWeight (μ : Measure ℂ) (R : ℝ) (ζ : ℂ) : ℝ≥0∞ := (2 * μ (ball ζ R))⁻¹
/-- The weight `w(ζ) = 1/(2 μ(D(ζ,R)))` (disc, hyperbolic balls). -/
def massWeightDisc (μ : Measure ℂ) (R : ℝ) (ζ : ℂ) : ℝ≥0∞ := (2 * μ (hypBall ζ R))⁻¹
/-- Smoothing radius in the disc: `s(ζ) = (1 − |ζ|²)/4`. -/
def discRadius (ζ : ℂ) : ℝ := (1 - ‖ζ‖ ^ 2) / 4

theorem measurable_massWeight {μ : Measure ℂ} [SFinite μ] (R : ℝ) :
    Measurable (massWeight μ R) := sorry
theorem measurable_massWeightDisc {μ : Measure ℂ} [SFinite μ] (R : ℝ) :
    Measurable (massWeightDisc μ R) := sorry

theorem isLocalPotData_plane {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    IsLocalPotData univ (μ.withDensity (massWeight μ R)) (fun _ ↦ R) := sorry

theorem isLocalPotData_disc {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    IsLocalPotData 𝔻 (μ.withDensity (massWeightDisc μ R)) discRadius := sorry

theorem smoothedDensity_plane_bounds {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoubling μ) {R : ℝ} (hR : 0 < R)
    (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ ε K : ℝ, 0 < ε ∧ ∀ x : ℂ,
      ENNReal.ofReal ε ≤ smoothedDensity (μ.withDensity (massWeight μ R)) (fun _ ↦ R) x ∧
      smoothedDensity (μ.withDensity (massWeight μ R)) (fun _ ↦ R) x ≤ ENNReal.ofReal K := sorry

theorem smoothedDensity_disc_bounds {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight 𝔻 φ μ) (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R)
    (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ ε K : ℝ, 0 < ε ∧ ∀ x ∈ 𝔻,
      ENNReal.ofReal (ε / (1 - ‖x‖ ^ 2) ^ 2) ≤
        smoothedDensity (μ.withDensity (massWeightDisc μ R)) discRadius x ∧
      smoothedDensity (μ.withDensity (massWeightDisc μ R)) discRadius x ≤
        ENNReal.ofReal (K / (1 - ‖x‖ ^ 2) ^ 2) := sorry

theorem localPot_plane_le {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ M : ℝ, ∀ z : ℂ, localPot (μ.withDensity (massWeight μ R)) (fun _ ↦ R) z ≤ M := sorry

theorem localPot_disc_le {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ M : ℝ, ∀ z ∈ 𝔻, localPot (μ.withDensity (massWeightDisc μ R)) discRadius z ≤ M := sorry

/-- **Lemma 6 (plane)** (paper, p. 370). -/
theorem lemma6_plane {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ (ψ : ℂ → ℝ) (ν₀ : Measure ℂ) (g : ℂ → ℝ≥0∞) (ε K M : ℝ), 0 < ε ∧ Measurable g ∧
      IsSubharmonicWeight univ ψ (ν₀ + volume.withDensity g) ∧
      IsLocallyDoubling (ν₀ + volume.withDensity g) ∧
      (∀ z, |ψ z - φ z| ≤ M) ∧
      (∀ z, ENNReal.ofReal ε ≤ g z ∧ g z ≤ ENNReal.ofReal K) ∧
      ν₀ ≤ μ ∧ μ ≤ (2 : ℝ≥0∞) • ν₀ := sorry

/-- **Lemma 6 (disc)** (paper, p. 370). -/
theorem lemma6_disc {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ (ψ : ℂ → ℝ) (ν₀ : Measure ℂ) (g : ℂ → ℝ≥0∞) (ε K M : ℝ), 0 < ε ∧ Measurable g ∧
      IsSubharmonicWeight 𝔻 ψ (ν₀ + volume.withDensity g) ∧
      IsLocallyDoublingDisc (ν₀ + volume.withDensity g) ∧
      (∀ z ∈ 𝔻, |ψ z - φ z| ≤ M) ∧
      (∀ z ∈ 𝔻, ENNReal.ofReal (ε / (1 - ‖z‖ ^ 2) ^ 2) ≤ g z ∧
        g z ≤ ENNReal.ofReal (K / (1 - ‖z‖ ^ 2) ^ 2)) ∧
      (∀ z ∉ 𝔻, g z = 0) ∧
      ν₀ ≤ μ ∧ μ ≤ (2 : ℝ≥0∞) • ν₀ := sorry

/-! ### Corollaries in the form consumed by M11 and M12 (reconciliation) -/

/-- Lemma 6 (disc) in the form M11 consumes: `μ' ≥ ε · hypArea` and `|φ − φ'| ≤ B`.  Follows
from `lemma6_disc` (`μ' = ν₀ + volume.withDensity g`, `g ≥ ε/(1-|z|²)²` on `𝔻`; `1 < ·`
implies the hypothesis `1 ≤ ·` of `lemma6_disc`). -/
theorem lemma6_disc_hypArea (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ) (ε B : ℝ), 0 < ε ∧ IsSubharmonicWeight 𝔻 φ' μ' ∧
      IsLocallyDoublingDisc μ' ∧ ENNReal.ofReal ε • hypArea ≤ μ' ∧
      ∀ z ∈ 𝔻, |φ z - φ' z| ≤ B := sorry

/-- Lemma 6 (plane) in the form M12 consumes: `μ' ≥ ε · dm` and `|φ − φ'| ≤ B`.  Follows from
`lemma6_plane`. -/
theorem lemma6_plane_volume (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 < μ (ball z r)) :
    ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ) (ε B : ℝ), 0 < ε ∧ IsSubharmonicWeight univ φ' μ' ∧
      IsLocallyDoubling μ' ∧ ENNReal.ofReal ε • volume ≤ μ' ∧ ∀ z, |φ z - φ' z| ≤ B := sorry

/-- **Lemma 6 (disc), uniform form** (requested for `theorem2_uniform`): the constants `ε`, `B`
and the class `(Cd', R')` of the regularized measure depend only on the class `(Cd, R)` of `μ`,
not on the weight.  (The construction of `lemma6_disc` is uniform: the bounds come from
[Chr91, Lemma 2.3] and doubling at bounded scales, `christ_disc_quant`, `doubling_upTo_disc`.) -/
theorem lemma6_disc_quant (Cd : ℝ≥0) (R : ℝ) (hR : 0 < R) :
    ∃ (ε B : ℝ) (Cd' : ℝ≥0) (R' : ℝ), 0 < ε ∧ 0 ≤ B ∧ 0 < R' ∧
      ∀ (φ : ℂ → ℝ) (μ : Measure ℂ), IsSubharmonicWeight 𝔻 φ μ → MeasClassDisc μ Cd R →
        ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ), IsSubharmonicWeight 𝔻 φ' μ' ∧
          MeasClassDisc μ' Cd' R' ∧ ENNReal.ofReal ε • hypArea ≤ μ' ∧
          ∀ z ∈ 𝔻, |φ z - φ' z| ≤ B := sorry

/-- Splitting a σ-finite measure dominating another (used by M11 and M12 to write `μ' = ν + ε·m`;
moved here from M11 so that M12 need not import M11). -/
theorem Measure.exists_add_eq_of_le {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [SigmaFinite μ] (h : ν ≤ μ) : ∃ d : Measure X, d + ν = μ := sorry

end OC
