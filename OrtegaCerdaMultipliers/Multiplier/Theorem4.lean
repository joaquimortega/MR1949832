import OrtegaCerdaMultipliers.Multiplier.Potential
import OrtegaCerdaMultipliers.Multiplier.Estimates
import OrtegaCerdaMultipliers.Multiplier.Nodes

/-!
# M08 (Multiplier) — Theorem 4: multipliers in `𝔻` and `ℂ`

See `blueprint/M08_Multiplier.md` §2.8.  Scaffold: the core `multiplier_of_nodes_*` and the
quantitative `theorem4_*_quant` are `sorry`; the comparator statements `theorem4_disc`,
`theorem4_plane` (verbatim from `comparator/statements.lean`) are proved from them.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Core: multiplier from an arbitrary admissible node configuration (plane). -/
theorem multiplier_of_nodes_plane (Cd : ℝ≥0) (R₀ η A B : ℝ) (N : ℕ) (hR₀ : 0 < R₀)
    (hη : 0 < η) (hA : 0 < A) (hB : 0 ≤ B) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassPlane ψ μ Cd R₀ → ∀ (R : ℕ → Set ℂ) (c : ℕ → ℂ) (m : ℕ → ℕ)
      (Λ : ℕ → Multiset ℂ),
      IsCells univ dist (massRadius (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes univ dist (massRadius (lapNorm μ)) (lapNorm μ) N B R c m Λ → (∀ i, 3 ≤ m i) →
      ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ w, h w = 0 ↔ w ∈ nodeSet Λ) ∧
        (∀ w, analyticOrderAt h w = (nodeCount Λ w : ℕ∞)) ∧ Thm4BoundsPlane ψ μ h M C := sorry

/-- Core: multiplier from an arbitrary admissible node configuration (disc). -/
theorem multiplier_of_nodes_disc (Cd : ℝ≥0) (R₀ η A B ρ₀ : ℝ) (N : ℕ) (hR₀ : 0 < R₀)
    (hη : 0 < η) (hA : 0 < A) (hB : 0 ≤ B) (hρ₀ : 0 < ρ₀) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassDisc ψ μ Cd R₀ → ∀ (R : ℕ → Set ℂ) (c : ℕ → ℂ) (m : ℕ → ℕ)
      (Λ : ℕ → Multiset ℂ),
      IsCells 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N B R c m Λ →
      (∀ i, 2 ≤ m i) → (∀ i, massRadiusDisc (lapNorm μ) (c i) ≤ ρ₀ → 3 ≤ m i) →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h 𝔻 ∧ (∀ w ∈ 𝔻, h w = 0 ↔ w ∈ nodeSet Λ) ∧
        (∀ w ∈ 𝔻, analyticOrderAt h w = (nodeCount Λ w : ℕ∞)) ∧
        Thm4BoundsDisc ψ μ h M C := sorry

theorem theorem4_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassPlane ψ μ Cd R₀ →
        ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∃ z₀, h z₀ ≠ 0) ∧ Thm4BoundsPlane ψ μ h M C := sorry

theorem theorem4_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassDisc ψ μ Cd R₀ →
        ∃ h : ℂ → ℂ, DifferentiableOn ℂ h 𝔻 ∧ (∃ z₀ ∈ 𝔻, h z₀ ≠ 0) ∧
          Thm4BoundsDisc ψ μ h M C := sorry

/-- The fixed statement (comparator), from `theorem4_disc_quant`. -/
theorem theorem4_disc (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight 𝔻 ψ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z R)) :
    ∃ (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0), DifferentiableOn ℂ h 𝔻 ∧ (∃ z₀ ∈ 𝔻, h z₀ ≠ 0) ∧
      ∀ z ∈ 𝔻,
        C⁻¹ * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) ^ M ≤
          ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
          C * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) := by
  obtain ⟨R, hR, hmR⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  have hw : WeightClassDisc ψ μ Cd R :=
    ⟨hψ, ⟨fun z hz r hr h2 ↦ hCd z hz r hr h2, hmR, fun K hK hKc ↦ hψ.finite_of_compact K hK hKc⟩⟩
  obtain ⟨M, C, -, -, hall⟩ := theorem4_disc_quant Cd R hR
  obtain ⟨h, hh, hz₀, hb⟩ := hall ψ μ hw
  exact ⟨h, M, C, hh, hz₀, fun z hz ↦ ⟨(hb z hz).1, (hb z hz).2.1⟩⟩

/-- The fixed statement (comparator), from `theorem4_plane_quant`. -/
theorem theorem4_plane (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight univ ψ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 < μ (ball z R)) :
    ∃ (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0), Differentiable ℂ h ∧ (∃ z₀, h z₀ ≠ 0) ∧
      ∀ z : ℂ,
        C⁻¹ * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) ^ M ≤
          ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
          C * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) := by
  obtain ⟨R, hR, hmR⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  have hw : WeightClassPlane ψ μ Cd R :=
    ⟨hψ, ⟨fun z r hr h2 ↦ hCd z r hr h2, hmR,
      fun K hKc ↦ hψ.finite_of_compact K (subset_univ K) hKc⟩⟩
  obtain ⟨M, C, -, -, hall⟩ := theorem4_plane_quant Cd R hR
  obtain ⟨h, hh, hz₀, hb⟩ := hall ψ μ hw
  exact ⟨h, M, C, hh, hz₀, fun z ↦ ⟨(hb z).1, (hb z).2.1⟩⟩

end OC
