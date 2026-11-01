import OrtegaCerdaMultipliers.Multiplier.Theorem4

/-!
# M09 (SeveralMultipliers) — Proposition 2: several multipliers with disjoint exceptional sets

See `blueprint/M09_SeveralMultipliers.md`.  Scaffold: statements, proofs `sorry`; `colorSel` is a
real definition.  The comparator statements `prop2_disc`, `prop2_plane` (verbatim from
`comparator/statements.lean`, which now contain the Theorem-4 bounds for each multiplier) and the
forms `prop2_*_full` consumed by M11/M12 are proved from `prop2_*_quant`.

Reconciliation: the former `prop2_*_strong` coincide with the comparator `prop2_*` (up to the order
of the existential binders) and are dropped; the former weak `prop2_*` are corollaries of
`prop2_*_full`.  `exists_measurable_partition` is moved here from M11.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Greedy colouring of a symmetric graph on `ℕ` of degree `≤ D`. -/
theorem exists_coloring_nat (adj : ℕ → ℕ → Prop) (hsymm : ∀ i j, adj i j → adj j i) (D : ℕ)
    (hdeg : ∀ i, {j | adj i j}.encard ≤ D) :
    ∃ col : ℕ → Fin (D + 1), ∀ i j, i ≠ j → adj i j → col i ≠ col j := sorry

/-- Separated colouring of the cells (plane): same colour ⟹ `L`-separated centres. -/
theorem exists_separated_coloring_plane (Cd : ℝ≥0) (R₀ η A L : ℝ) (hη : 0 < η) :
    ∃ n : ℕ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c →
      ∃ col : ℕ → Fin n, ∀ i j, i ≠ j → col i = col j →
        L * (massRadius ν (c i) + massRadius ν (c j)) ≤ dist (c i) (c j) := sorry

/-- Separated colouring of the cells (disc). -/
theorem exists_separated_coloring_disc (Cd : ℝ≥0) (R₀ η A L : ℝ) (hη : 0 < η) :
    ∃ n : ℕ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassDisc ν Cd R₀ → IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c →
      ∃ col : ℕ → Fin n, ∀ i j, i ≠ j → col i = col j →
        L * (massRadiusDisc ν (c i) + massRadiusDisc ν (c j)) ≤ hypDist (c i) (c j) := sorry

/-- The selection for colour `l`: cells of colour `l` and their `K`-neighbours. -/
def colorSel (d : ℂ → ℂ → ℝ) (ρ : ℂ → ℝ) (R : ℕ → Set ℂ) (c : ℕ → ℂ) {n : ℕ}
    (col : ℕ → Fin n) (K : ℝ) (l : Fin n) (j : ℕ) : Prop :=
  ∃ k, col k = l ∧ (j = k ∨ ∃ z ∈ R k, d z (c j) < K * ρ (c j))

/-- Key separation lemma (plane): for `z` in a cell of colour `l`, every node of the colour-`l`
configuration is at distance `≥ c₅ ρ(z)`.  `Bl`: spread of the ordinary nodes; selected cells
carry nodes in the annulus `[Bk, Bk'] · ρ(c j)`. -/
theorem nodes_far_of_color_plane (Cd : ℝ≥0) (R₀ η A Bl : ℝ) (hη : 0 < η) (hA : 0 < A)
    (hBl : 0 ≤ Bl) :
    ∃ Bk₀ : ℝ, ∀ Bk Bk' : ℝ, Bk₀ ≤ Bk → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∃ c₅ : ℝ, 0 < c₅ ∧
      ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ) {n : ℕ} (col : ℕ → Fin n)
        (l : Fin n) (Λ : ℕ → Multiset ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c →
      (∀ i j, i ≠ j → col i = col j →
        L * (massRadius ν (c i) + massRadius ν (c j)) ≤ dist (c i) (c j)) →
      (∀ j, ¬ colorSel dist (massRadius ν) R c col (Bl + 2) l j →
        ∀ w ∈ Λ j, dist (c j) w ≤ Bl * massRadius ν (c j)) →
      (∀ j, colorSel dist (massRadius ν) R c col (Bl + 2) l j →
        ∀ w ∈ Λ j, Bk * massRadius ν (c j) ≤ dist (c j) w ∧
          dist (c j) w ≤ Bk' * massRadius ν (c j)) →
      ∀ i, col i = l → ∀ z ∈ R i, ∀ j, ∀ w ∈ Λ j, c₅ * massRadius ν z ≤ dist z w := sorry

/-- Key separation lemma (disc). -/
theorem nodes_far_of_color_disc (Cd : ℝ≥0) (R₀ η A Bl : ℝ) (hη : 0 < η) (hA : 0 < A)
    (hBl : 0 ≤ Bl) :
    ∃ Bk₀ : ℝ, ∀ Bk Bk' : ℝ, Bk₀ ≤ Bk → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∃ c₅ : ℝ, 0 < c₅ ∧
      ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ) {n : ℕ} (col : ℕ → Fin n)
        (l : Fin n) (Λ : ℕ → Multiset ℂ),
      MeasClassDisc ν Cd R₀ → IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c →
      (∀ j, ∀ w ∈ Λ j, w ∈ 𝔻) →
      (∀ i j, i ≠ j → col i = col j →
        L * (massRadiusDisc ν (c i) + massRadiusDisc ν (c j)) ≤ hypDist (c i) (c j)) →
      (∀ j, ¬ colorSel hypDist (massRadiusDisc ν) R c col (Bl + 2) l j →
        ∀ w ∈ Λ j, hypDist (c j) w ≤ Bl * massRadiusDisc ν (c j)) →
      (∀ j, colorSel hypDist (massRadiusDisc ν) R c col (Bl + 2) l j →
        ∀ w ∈ Λ j, Bk * massRadiusDisc ν (c j) ≤ hypDist (c j) w ∧
          hypDist (c j) w ≤ Bk' * massRadiusDisc ν (c j)) →
      ∀ i, col i = l → ∀ z ∈ R i, ∀ j, ∀ w ∈ Λ j, c₅ * massRadiusDisc ν z ≤ hypDist z w :=
  sorry

/-- **Proposition 2, quantitative, full form (plane).** -/
theorem prop2_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ (n M : ℕ) (C : ℝ≥0) (ε : ℝ), 1 ≤ M ∧ 1 ≤ C ∧ 0 < ε ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassPlane ψ μ Cd R₀ →
      ∃ h : Fin n → ℂ → ℂ, (∀ i, Differentiable ℂ (h i)) ∧ (∀ i, ∃ z₀, h i z₀ ≠ 0) ∧
        (∀ i, Thm4BoundsPlane ψ μ (h i) M C) ∧
        (∀ z : ℂ, ∃ i, ∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) ∧
        (∀ i, ∀ z : ℂ, (∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) →
          (C : ℝ)⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ ∧ ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
        (∀ i, ∀ z : ℂ, ‖h i z‖ ≤ C * Real.exp (ψ z)) := sorry

/-- **Proposition 2, quantitative, full form (disc).** -/
theorem prop2_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ (n M : ℕ) (C : ℝ≥0) (ε : ℝ), 1 ≤ M ∧ 1 ≤ C ∧ 0 < ε ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassDisc ψ μ Cd R₀ →
      ∃ h : Fin n → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (h i) 𝔻) ∧ (∀ i, ∃ z₀ ∈ 𝔻, h i z₀ ≠ 0) ∧
        (∀ i, Thm4BoundsDisc ψ μ (h i) M C) ∧
        (∀ z ∈ 𝔻, ∃ i, ∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) ∧
        (∀ i, ∀ z ∈ 𝔻, (∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) →
          (C : ℝ)⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ ∧ ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
        (∀ i, ∀ z ∈ 𝔻, ‖h i z‖ ≤ C * Real.exp (ψ z)) := sorry

/-- **Proposition 2 (disc)** (paper, p. 369): finitely many multipliers `h₁, …, h_n`, each
satisfying the conclusion of Theorem 4, whose exceptional sets
`E_{h_i} = ⋃_{λ ∈ Z(h_i)} D(λ, ε ρ(λ))` have empty intersection; outside `E_{h_i}`,
`|h_i| ≃ e^ψ` (the remark after Theorem 4). -/
theorem prop2_disc (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight 𝔻 ψ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z R)) :
    ∃ (n : ℕ) (h : Fin n → ℂ → ℂ) (M : ℕ) (ε : ℝ) (C : ℝ≥0), 0 < ε ∧ 0 < C ∧
      (∀ i, DifferentiableOn ℂ (h i) 𝔻 ∧ (∃ z₀ ∈ 𝔻, h i z₀ ≠ 0) ∧ ∀ z ∈ 𝔻,
        C⁻¹ * (hypDistSet z {w | w ∈ 𝔻 ∧ h i w = 0} /
            ENNReal.ofReal (massRadiusDisc μ z)) ^ M ≤
          ENNReal.ofReal (‖h i z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h i z‖ * Real.exp (-ψ z)) ≤
          C * (hypDistSet z {w | w ∈ 𝔻 ∧ h i w = 0} / ENNReal.ofReal (massRadiusDisc μ z))) ∧
      (∀ z ∈ 𝔻, ∃ i, ∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) ∧
      ∀ i, ∀ z ∈ 𝔻, (∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) →
        (C : ℝ)⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ ∧ ‖h i z‖ ≤ C * Real.exp (ψ z) := by
  obtain ⟨R, hR, hmR⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  have hw : WeightClassDisc ψ μ Cd R :=
    ⟨hψ, ⟨fun z hz r hr h2 ↦ hCd z hz r hr h2, hmR, fun K hK hKc ↦ hψ.finite_of_compact K hK hKc⟩⟩
  obtain ⟨n, M, C, ε, -, hC, hε, hall⟩ := prop2_disc_quant Cd R hR
  obtain ⟨h, hh, hz₀, hb, hcov, hgood, -⟩ := hall ψ μ hw
  exact ⟨n, h, M, ε, C, hε, zero_lt_one.trans_le hC,
    fun i ↦ ⟨hh i, hz₀ i, fun z hz ↦ ⟨(hb i z hz).1, (hb i z hz).2.1⟩⟩, hcov, hgood⟩

/-- **Proposition 2 (plane)** (paper, p. 369). -/
theorem prop2_plane (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight univ ψ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 < μ (ball z R)) :
    ∃ (n : ℕ) (h : Fin n → ℂ → ℂ) (M : ℕ) (ε : ℝ) (C : ℝ≥0), 0 < ε ∧ 0 < C ∧
      (∀ i, Differentiable ℂ (h i) ∧ (∃ z₀, h i z₀ ≠ 0) ∧ ∀ z : ℂ,
        C⁻¹ * (edistSet z {w | h i w = 0} / ENNReal.ofReal (massRadius μ z)) ^ M ≤
          ENNReal.ofReal (‖h i z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h i z‖ * Real.exp (-ψ z)) ≤
          C * (edistSet z {w | h i w = 0} / ENNReal.ofReal (massRadius μ z))) ∧
      (∀ z : ℂ, ∃ i, ∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) ∧
      ∀ i, ∀ z : ℂ, (∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) →
        (C : ℝ)⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ ∧ ‖h i z‖ ≤ C * Real.exp (ψ z) := by
  obtain ⟨R, hR, hmR⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  have hw : WeightClassPlane ψ μ Cd R :=
    ⟨hψ, ⟨fun z r hr h2 ↦ hCd z r hr h2, hmR,
      fun K hKc ↦ hψ.finite_of_compact K (subset_univ K) hKc⟩⟩
  obtain ⟨n, M, C, ε, -, hC, hε, hall⟩ := prop2_plane_quant Cd R hR
  obtain ⟨h, hh, hz₀, hb, hcov, hgood, -⟩ := hall ψ μ hw
  exact ⟨n, h, M, ε, C, hε, zero_lt_one.trans_le hC,
    fun i ↦ ⟨hh i, hz₀ i, fun z ↦ ⟨(hb i z).1, (hb i z).2.1⟩⟩, hcov, hgood⟩

/-- M11's required form (disc). -/
theorem prop2_disc_full (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight 𝔻 ψ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z R)) :
    ∃ (n : ℕ) (h : Fin n → ℂ → ℂ) (ε : ℝ) (C : ℝ), 0 < ε ∧ 0 < C ∧
      (∀ i, DifferentiableOn ℂ (h i) 𝔻) ∧
      (∀ z ∈ 𝔻, ∃ i, ∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) ∧
      (∀ i, ∀ z ∈ 𝔻, ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
      ∀ i, ∀ z ∈ 𝔻, (∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) →
        C⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ := by
  obtain ⟨R, hR, hmR⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  have hw : WeightClassDisc ψ μ Cd R :=
    ⟨hψ, ⟨fun z hz r hr h2 ↦ hCd z hz r hr h2, hmR, fun K hK hKc ↦ hψ.finite_of_compact K hK hKc⟩⟩
  obtain ⟨n, M, C, ε, -, hC, hε, hall⟩ := prop2_disc_quant Cd R hR
  obtain ⟨h, hh, -, -, hcov, hgood, hup⟩ := hall ψ μ hw
  have hC0 : (0 : ℝ) < C := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  exact ⟨n, h, ε, C, hε, hC0, hh, hcov, hup, fun i z hz hg ↦ (hgood i z hz hg).1⟩

/-- M12's required form (plane). -/
theorem prop2_plane_full (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight univ ψ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 < μ (ball z R)) :
    ∃ (n : ℕ) (h : Fin n → ℂ → ℂ) (ε : ℝ) (C : ℝ), 0 < ε ∧ 0 < C ∧
      (∀ i, Differentiable ℂ (h i)) ∧
      (∀ z : ℂ, ∃ i, ∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) ∧
      (∀ i, ∀ z, ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
      ∀ i, ∀ z : ℂ, (∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) →
        C⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ := by
  obtain ⟨R, hR, hmR⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  have hw : WeightClassPlane ψ μ Cd R :=
    ⟨hψ, ⟨fun z r hr h2 ↦ hCd z r hr h2, hmR,
      fun K hKc ↦ hψ.finite_of_compact K (subset_univ K) hKc⟩⟩
  obtain ⟨n, M, C, ε, -, hC, hε, hall⟩ := prop2_plane_quant Cd R hR
  obtain ⟨h, hh, -, -, hcov, hgood, hup⟩ := hall ψ μ hw
  have hC0 : (0 : ℝ) < C := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  exact ⟨n, h, ε, C, hε, hC0, hh, hcov, hup, fun i z hg ↦ (hgood i z hg).1⟩

/-- A finite cover by measurable sets refines to a measurable partition (moved here from M11, so
that both M11 and M12 can use it without M12 importing M11). -/
theorem exists_measurable_partition {X : Type*} [MeasurableSpace X] {n : ℕ} {S : Set X}
    (hS : MeasurableSet S) (G : Fin n → Set X) (hG : ∀ i, MeasurableSet (G i))
    (hcov : ∀ z ∈ S, ∃ i, z ∈ G i) :
    ∃ Ω : Fin n → Set X, (∀ i, MeasurableSet (Ω i)) ∧ (∀ i, Ω i ⊆ G i ∩ S) ∧
      ∀ z ∈ S, ∃! i, z ∈ Ω i := sorry

/-- The partition form used by M11 (disc). -/
theorem prop2_disc_partition (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight 𝔻 ψ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z R)) :
    ∃ (n : ℕ) (h : Fin n → ℂ → ℂ) (Ω : Fin n → Set ℂ) (C : ℝ), 0 < C ∧
      (∀ i, DifferentiableOn ℂ (h i) 𝔻) ∧ (∀ i, MeasurableSet (Ω i)) ∧
      Pairwise (Function.onFun Disjoint Ω) ∧ (⋃ i, Ω i) = 𝔻 ∧
      (∀ i, ∀ z ∈ Ω i, h i z ≠ 0 ∧ C⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖) ∧
      (∀ i, ∀ z ∈ 𝔻, ‖h i z‖ ≤ C * Real.exp (ψ z)) := sorry

/-- The partition form used by M12 (plane). -/
theorem prop2_plane_partition (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight univ ψ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 < μ (ball z R)) :
    ∃ (n : ℕ) (h : Fin n → ℂ → ℂ) (Ω : Fin n → Set ℂ) (C : ℝ), 0 < C ∧
      (∀ i, Differentiable ℂ (h i)) ∧ (∀ i, MeasurableSet (Ω i)) ∧
      Pairwise (Function.onFun Disjoint Ω) ∧ (⋃ i, Ω i) = univ ∧
      (∀ i, ∀ z ∈ Ω i, h i z ≠ 0 ∧ C⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖) ∧
      (∀ i z, ‖h i z‖ ≤ C * Real.exp (ψ z)) := sorry

/-- Uniform version for BOC (M11 §8.3): constants depend only on `a ≤ b`. -/
theorem prop2_disc_unif {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ (n : ℕ) (ε C : ℝ), 0 < ε ∧ 0 < C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      IsSubharmonicWeight 𝔻 ψ μ → ENNReal.ofReal a • hypArea ≤ μ →
      μ ≤ ENNReal.ofReal b • hypArea →
      ∃ h : Fin n → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (h i) 𝔻) ∧
        (∀ z ∈ 𝔻, ∃ i, ∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) ∧
        (∀ i, ∀ z ∈ 𝔻, ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
        ∀ i, ∀ z ∈ 𝔻, (∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) →
          C⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ := sorry

/-- Class membership of hyperbolic-area-comparable measures (used for `prop2_disc_unif`). -/
theorem measClassDisc_of_hypArea {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ (Cd : ℝ≥0) (R₀ : ℝ), 0 < R₀ ∧ ∀ μ : Measure ℂ, μ 𝔻ᶜ = 0 →
      ENNReal.ofReal a • hypArea ≤ μ → μ ≤ ENNReal.ofReal b • hypArea →
      MeasClassDisc μ Cd R₀ := sorry

end OC
