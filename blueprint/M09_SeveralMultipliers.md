# M09 — Proposition 2: several multipliers with disjoint exceptional sets

**Lean file:** `OrtegaCerdaMultipliers/SeveralMultipliers.lean` (namespace `OC`). It could be split into `SeveralMultipliers/Coloring.lean` (§3.1–§3.2) and the rest.

**Paper:** Proposition 2 and its proof (pp. 369–370); the Remark after Theorem 4 (p. 363) defines `E_h`.

**Depends on:**
- **M08:** `IsCells`, `IsNodes`, `lapNorm`, the classes, `IsMassPartition.exists_cells`, `exists_nodes_plane/disc` (with selection), `multiplier_of_nodes_plane/disc`, `Thm4BoundsPlane/Disc`.
- **M03:** quantitative Claim 1 (`claim1_*_quant`), `massRadius_lapNorm_quant`, `MeasClass*.lapNorm` (as listed in M08 §4.1).
- **M05:** `lemma4_*_quant`.
- **M01/M11:** `hypArea`, `hypArea_hypBall`.
- **Mathlib:** `Set.encard`, `Finset.exists_mem_notMem_of_card_lt_card` (pigeonhole), `Nat.strongRecOn`, `IsClosed.measurableSet`, `isClosed_biInter`, `Real.arsinh`, `Real.cosh`.

Statements: in `scratchpad/m0809_check.lean` (shared with M08), **all typecheck**. The following are **proved** there from `prop2_*_quant`:
- `prop2_disc`, `prop2_plane`: the current comparator statements;
- `prop2_disc_full`, `prop2_plane_full`: the forms M11/M12 require;
- `prop2_disc_strong`, `prop2_plane_strong`: the coordinator's strengthened form, with the Theorem-4 bounds inlined exactly as in `theorem4_*`, plus `h i ≢ 0`.

---

## 0. The paper and what changes

> **Proposition 2.** Given `ψ` as in the statement of Theorem 4 there is a collection of multipliers `h₁, …, h_n` satisfying the conclusion of Theorem 4. Moreover their exceptional sets are disjoint; i.e. `E_{h₁} ∩ ⋯ ∩ E_{h_n} = ∅`.

**Proof (paper).**
1. Distribute the rectangles of Lemma 4 into finitely many families such that two rectangles of the same family are very far apart (`MR_i^l ∩ MR_j^l = ∅`), "with the Besicovitch covering lemma".
2. For family `l`, build `h_l` with the alternative points `κ(R)` (Lemma 5) on the rectangles of the family and their immediate neighbours, and with `λ(R)` elsewhere.
3. Then `h_l` has no zeros in the family's rectangles and their neighbours. Hence `E_{h_l}` contains no rectangle of family `l`, so `⋂_l E_{h_l} = ∅`.

**What changes.**
- **Colouring.** Besicovitch is not needed. We use a greedy colouring of the bounded-degree "conflict graph" on the countable set of cells (§3.1–§3.2).
- **"Neighbours".** The paper's κ placement ("outside `CR`, inside `4CKR`", and "not so far that they reach another rectangle of the family") has to avoid both the cell and the cells whose *ordinary* nodes come close to it. We use the neighbour notion `colorSel` (with the ordinary-node spread `Bl`), *not* M08's near-field radius `K₀`. Otherwise the constants are circular: `K₀` depends on the κ spread (§3.4, §5 item 3).
- **The conclusion is the full one.** Each `h_l` satisfies the Theorem-4 bounds (`Thm4Bounds*`, including `d(z,Λ) ≲ ρ(z)`), `h_l ≢ 0`, every point is good for some `h_l`, `|h_l| ≃ e^ψ` on its good set, and `|h_l| ≲ e^ψ` everywhere. This is the strengthened `prop2_*` announced by the coordinator. The present comparator `prop2_*` and M11/M12's `prop2_*_full` are corollaries (proved).
- **Uniform constants** (`prop2_*_quant`), and `prop2_disc_unif` for BOC (M11 §8.3).
- **A measurable partition** `Ω = ⊔ Ω_i` with `h_i ≠ 0`, `|h_i| ≳ e^ψ` on `Ω_i`, and `|h_i| ≲ e^ψ` everywhere (`prop2_*_partition`). This is the form M11/M12 consume.

**Reading `E_{h₁} ∩ ⋯ ∩ E_{h_n} = ∅`.** Here `E_h = ⋃_{λ∈Z(h)} D(λ, ερ(λ))`, so `z ∉ E_{h_i}` ⟺ `∀ λ ∈ Z(h_i), ερ(λ) ≤ d(z,λ)`. The formal "`∀ z, ∃ i, ∀ w, h i w = 0 → ε ρ(w) ≤ d(z,w)`" is exactly `⋂ E_{h_i} = ∅`, with closed rather than open discs, which only strengthens it.

---

## 1. Formal statements

```lean
/-- Greedy colouring of a symmetric graph on `ℕ` of degree `≤ D`. -/
theorem exists_coloring_nat (adj : ℕ → ℕ → Prop) (hsymm : ∀ i j, adj i j → adj j i) (D : ℕ)
    (hdeg : ∀ i, {j | adj i j}.encard ≤ D) :
    ∃ col : ℕ → Fin (D + 1), ∀ i j, i ≠ j → adj i j → col i ≠ col j := sorry

/-- Separated colouring of the cells (plane): same colour ⟹ `L`-separated centres. -/
theorem exists_separated_coloring_plane (Cd : ℝ≥0) (R₀ η A L : ℝ) :
    ∃ n : ℕ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c →
      ∃ col : ℕ → Fin n, ∀ i j, i ≠ j → col i = col j →
        L * (massRadius ν (c i) + massRadius ν (c j)) ≤ dist (c i) (c j) := sorry

/-- Separated colouring of the cells (disc). -/
theorem exists_separated_coloring_disc (Cd : ℝ≥0) (R₀ η A L : ℝ) :
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
theorem nodes_far_of_color_plane (Cd : ℝ≥0) (R₀ η A Bl : ℝ) (hA : 0 < A)
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
theorem nodes_far_of_color_disc (Cd : ℝ≥0) (R₀ η A Bl : ℝ) (hA : 0 < A)
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
theorem prop2_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) :
    ∃ (n M : ℕ) (C : ℝ≥0) (ε : ℝ), 1 ≤ M ∧ 1 ≤ C ∧ 0 < ε ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassPlane ψ μ Cd R₀ →
      ∃ h : Fin n → ℂ → ℂ, (∀ i, Differentiable ℂ (h i)) ∧ (∀ i, ∃ z₀, h i z₀ ≠ 0) ∧
        (∀ i, Thm4BoundsPlane ψ μ (h i) M C) ∧
        (∀ z : ℂ, ∃ i, ∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) ∧
        (∀ i, ∀ z : ℂ, (∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) →
          (C : ℝ)⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ ∧ ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
        (∀ i, ∀ z : ℂ, ‖h i z‖ ≤ C * Real.exp (ψ z)) := sorry

/-- **Proposition 2, quantitative, full form (disc).** -/
theorem prop2_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) :
    ∃ (n M : ℕ) (C : ℝ≥0) (ε : ℝ), 1 ≤ M ∧ 1 ≤ C ∧ 0 < ε ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassDisc ψ μ Cd R₀ →
      ∃ h : Fin n → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (h i) 𝔻) ∧ (∀ i, ∃ z₀ ∈ 𝔻, h i z₀ ≠ 0) ∧
        (∀ i, Thm4BoundsDisc ψ μ (h i) M C) ∧
        (∀ z ∈ 𝔻, ∃ i, ∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) ∧
        (∀ i, ∀ z ∈ 𝔻, (∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) →
          (C : ℝ)⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ ∧ ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
        (∀ i, ∀ z ∈ 𝔻, ‖h i z‖ ≤ C * Real.exp (ψ z)) := sorry

-- (reconciled) `prop2_disc`, `prop2_plane` are now the comparator statements (Theorem-4 bounds
-- for each multiplier); proved from `prop2_*_quant`.
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

-- (reconciled) `prop2_disc_strong`, `prop2_plane_strong` are dropped: they coincide with the
-- comparator `prop2_disc`, `prop2_plane` above up to the order of the existential binders.

/-- A finite cover by measurable sets refines to a measurable partition (moved here from M11, so
that both M11 and M12 can use it without M12 importing M11). -/
theorem exists_measurable_partition {X : Type*} [MeasurableSpace X] {n : ℕ} {S : Set X}
    (hS : MeasurableSet S) (G : Fin n → Set X) (hG : ∀ i, MeasurableSet (G i))
    (hcov : ∀ z ∈ S, ∃ i, z ∈ G i) :
    ∃ Ω : Fin n → Set X, (∀ i, MeasurableSet (Ω i)) ∧ (∀ i, Ω i ⊆ G i ∩ S) ∧
      ∀ z ∈ S, ∃! i, z ∈ Ω i

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
```

**Count:** 1 definition (`colorSel`) and 17 theorems. All typecheck. 6 are proved in the scratch file: `prop2_disc`, `prop2_plane`, `prop2_*_full` and `prop2_*_strong`.

**Notes.**
- `prop2_*_quant` lists, for each `i`: `Thm4Bounds* ψ μ (h i) M C` (the conclusion of Theorem 4 with the Remark), `h i ≢ 0`, the covering, the two-sided bound on good points, and the global upper bound. The global upper bound also follows from `Thm4Bounds*` (§3.5); it is listed separately for convenience.
- In `𝔻`, `h i` is only constrained on `𝔻`. M11 must use `𝔻.indicator (h i)` for measurability, as it already does.
- `prop2_*_partition`: `Ω i` measurable, pairwise disjoint, covering `Ω`; on `Ω i`, `h i ≠ 0` and `|h i| ≥ C⁻¹ e^ψ`; `|h i| ≤ C e^ψ` everywhere. M11/M12 currently build this partition themselves from `prop2_*_full` (`exists_measurable_partition`). They may switch to `prop2_*_partition`.

---
## 2. Notation and constants

As in M08:
- `ν = lapNorm μ`, in the class `(Cd, R̃₀ := 15R₀)`;
- `ρ̃ = massRadius ν` (resp. `massRadiusDisc ν`), `ρ = massRadius μ`, `ρ ≤ ρ̃ ≤ C_ρ ρ`;
- `d = dist` or `hypDist`, cells `(R, c)` with `B(c_i, ηρ_i) ⊆ R_i ⊆ B̄(c_i, Aρ_i)`, `ρ_i := ρ̃(c_i)`, `N = 12`.

**Neighbours.** For a colouring `col : ℕ → Fin n` and a colour `l`, `colorSel d ρ̃ R c col (Bl+2) l j` holds iff there is `k` with `col k = l` and either `j = k`, or `d(z, c_j) < (Bl+2)ρ_j` for some `z ∈ R_k`. The latter means `j ∈ Nbr(k)`: an ordinary node of `R_j` can come within `2ρ_j` of `R_k`.

**Constants, in order** (all depend only on `(Cd, R₀)`):
1. M05: `η, A`.
2. `Bl`, the ordinary-node spread: `6A` (plane); from `exists_nodes_disc A` (disc, independent of `B`).
3. `Bk₀ := max(A + 1, 2AC₂ + Bl + 3)`, where `C₂` is the Claim-1 constant (for `ν`) with `K = A + Bl + 2`.
4. κ parameter: `B := Bk₀/A`, so κ nodes satisfy `d(c_j, w) ≥ BAρ_j = Bk₀ρ_j`. Their outer spread `Bk'` is `(B+12)A` (plane) or `B'` from `exists_nodes_disc A` at `B` (disc). The disc also gives `ρ₀`.
5. `L := max(A + 1, A + (Bl + 2 + Bk')C₂)`.
6. `n` from `exists_separated_coloring_*` with this `L`.
7. `(M, C)` from `multiplier_of_nodes_*` with spread `Bk'` (and `ρ₀` in the disc).
8. `c₅` from `nodes_far_of_color_*`; then `ε`, `c₆`, `C_P` (§3.5).

---

## 3. Proofs

### 3.1 Greedy colouring (`exists_coloring_nat`)

Let `adj` be symmetric with `#{j : adj i j} ≤ D` for every `i`. Define `col i` by strong recursion on `i` (`Nat.strongRecOn`, classical):
`col i := some c ∈ Fin (D+1) with c ∉ U_i`, where `U_i := {col j : j < i, adj i j}`.

- `U_i` is the image of `{j < i : adj i j}` (a finite set, of size `≤ D`), so `#U_i ≤ D < D + 1 = #Fin (D+1)` and a free colour exists (`Finset.exists_mem_notMem_of_card_lt_card`, or `Fintype.exists_not_mem_finset`).
- **Correctness.** Let `i ≠ j` with `adj i j`; WLOG `j < i` (else use `hsymm`). Then `col j ∈ U_i` and `col i ∉ U_i`, so `col i ≠ col j`.
- **Lean.** `Classical.choose` on `∃ c, c ∉ (((Finset.range i).filter (adj i ·)).attach.image (fun j ↦ prev j _))`. Use `Classical.decRel` for the filter. `encard ≤ D` converts to a `Finset.card` bound via `Set.encard_coe_eq_coe_finsetCard` and monotonicity.

### 3.2 Separated colouring (`exists_separated_coloring_*`)

Let `adj i j :⟺ i ≠ j ∧ d(c_i, c_j) < L(ρ_i + ρ_j)`; it is symmetric.

**Degree bound.** If `adj i j`, then `d(c_i,c_j) < 2L max(ρ_i, ρ_j)`, so Claim 1 (`K = 2L`, constant `C_L`) gives `ρ_i/C_L ≤ ρ_j ≤ C_Lρ_i`.
- The inner balls `B(c_j, ηρ_j) ⊆ R_j` are pairwise disjoint (cells are), have radius `≥ ηρ_i/C_L`, and lie in `B(c_i, r_i')` with `r_i' := (L(1 + C_L) + ηC_L)ρ_i`.
- **Plane:** `#{j : adj i j} ≤ (r_i'/(ηρ_i/C_L))² = ((L(1+C_L) + ηC_L)C_L/η)²`.
- **Disc:** with `hypArea` (`hypArea_hypBall`), `#{j : adj i j} ≤ sinh²(r_i')/sinh²(ηρ_i/C_L)`. Use `sinh(ax) ≤ ax e^{ax}`, `sinh(bx) ≥ bx` and `ρ_i ≤ R̃₀`: `#{j : adj i j} ≤ ((L(1+C_L)+ηC_L)C_L/η)² e^{2(L(1+C_L)+ηC_L)R̃₀}`.
- Let `D` be the ceiling of the bound. For the count: `Σ_j area(B(c_j, ηρ_j)) ≤ area(B(c_i, r_i'))` for every finite subfamily (`measure_biUnion_finset`), so `encard ≤ D`.

**Conclusion.** `n := D + 1`, and §3.1 gives `col` with `col i = col j, i ≠ j ⟹ ¬adj i j ⟹ L(ρ_i + ρ_j) ≤ d(c_i, c_j)`. ∎

### 3.3 The colour-`l` configuration

For `l : Fin n`, let `sel_l j := decide (colorSel d ρ̃ R c col (Bl+2) l j)` (classical). `exists_nodes_plane (B := Bk₀/A) sel_l` (resp. `exists_nodes_disc A` at `B`, then `sel_l`) gives `Λ^l` with:
- `IsNodes … 12 Bk' R c m Λ^l` (orders `m ≡ 3` in the plane; disc: `≥ 2`, and `≥ 3` on cells with `ρ_j ≤ ρ₀`);
- `sel_l j = false` ⟹ `d(c_j, w) ≤ Blρ_j` for `w ∈ Λ^l_j`;
- `sel_l j = true` ⟹ `Bk₀ρ_j ≤ d(c_j, w) ≤ Bk'ρ_j`.

The spread, orders and `N` are the same for every `l`. So `multiplier_of_nodes_*` gives `h_l` with **the same** `(M, C)` for all `l`. The node sets differ only in *which* cells are shifted, and M08's estimates are uniform over admissible configurations. This answers "check that the estimates of M08 still hold uniformly": they hold because the core theorem quantifies over all configurations with spread `Bk'`.

### 3.4 Nodes avoid the cells of their colour (`nodes_far_of_color_*`)

Let `col i = l` and `z ∈ R_i`, so `d(z,c_i) ≤ Aρ_i`. Claim 1 (`K = A`, constant `C_A`) gives `ρ̃(z) ≤ C_Aρ_i`. Let `w ∈ Λ^l_j`. There are four cases.

**Case 1: `j` not selected.** Taking `k = i` in `colorSel`: `j ≠ i` and `d(z', c_j) ≥ (Bl+2)ρ_j` for all `z' ∈ R_i`, in particular for `z`. Then:
- `d(z,w) ≥ d(z,c_j) − Blρ_j ≥ 2ρ_j`;
- `d(z,w) ≥ d(z,c_j)·2/(Bl+2)`.

If `d(z,c_j) ≤ max(ρ̃(z), ρ_j)`, Claim 1 (`K = 1`, `C_1`) gives `ρ̃(z) ≤ C_1ρ_j`, so `d(z,w) ≥ (2/C_1)ρ̃(z)`. Otherwise `d(z,c_j) > ρ̃(z)`, so `d(z,w) ≥ (2/(Bl+2))ρ̃(z)`.

**Case 2: `j` selected through `k = i`, `j = i`.** `d(z,w) ≥ d(c_i,w) − d(c_i,z) ≥ (Bk₀ − A)ρ_i ≥ ρ_i ≥ ρ̃(z)/C_A`.

**Case 3: `j` selected through `k = i`, `j ∈ Nbr(i)`.** There is `z' ∈ R_i` with `d(z',c_j) < (Bl+2)ρ_j`.
- `d(c_i,c_j) ≤ Aρ_i + (Bl+2)ρ_j ≤ (A + Bl + 2)max(ρ_i,ρ_j)`, so `ρ_i ≤ C₂ρ_j` and `ρ_j ≤ C₂ρ_i`.
- `d(z,c_j) ≤ d(z,c_i) + d(c_i,c_j) ≤ 2Aρ_i + (Bl+2)ρ_j ≤ (2AC₂ + Bl + 2)ρ_j`.
- So `d(z,w) ≥ Bk₀ρ_j − d(z,c_j) ≥ ρ_j ≥ ρ_i/C₂ ≥ ρ̃(z)/(C₂C_A)`.

**Case 4: `j` selected through some `k ≠ i` with `col k = l`.** By separation, `d(c_i,c_k) ≥ L(ρ_i + ρ_k)`.
- If `j = k`: `d(c_k,w) ≤ Bk'ρ_k`.
- If `j ∈ Nbr(k)`: as in Case 3, `ρ_j ≤ C₂ρ_k` and `d(c_k,c_j) ≤ Aρ_k + (Bl+2)ρ_j`, so `d(c_k,w) ≤ (A + (Bl+2+Bk')C₂)ρ_k ≤ Lρ_k`.
- Hence `d(z,w) ≥ d(c_i,c_k) − d(z,c_i) − d(c_k,w) ≥ (L − A)ρ_i ≥ ρ_i ≥ ρ̃(z)/C_A`.

If `j` is selected through several `k`, any witness works.

**Conclusion.** `c₅ := min(2/C_1, 2/(Bl+2), 1/C_A, 1/(C₂C_A))`. In `𝔻` all triangle inequalities are `hypDist_triangle`; this is where the hypothesis that the nodes lie in `𝔻` is used. ∎

This is the paper's "`h_l` has no zeros in the rectangles from the family `{R_i^l}` and its adjacents", in quantitative form: the zeros stay at distance `≥ c₅ρ̃(z)` from every point of a colour-`l` cell.

### 3.5 `prop2_*_quant`

Let `(ψ, μ)` be in the class. Build `ν`, the cells, `col` and, for each `l`, `Λ^l` and `h_l` (§3.3). Index `h : Fin n → ℂ → ℂ`, `h l := h_l`. Then:

1. **Holomorphy, `h_l ≢ 0`, `Thm4Bounds*`:** from `multiplier_of_nodes_*`, plus the countability argument of M08 §3.11.
2. **Covering** (`⋂_l E_{h_l} = ∅`). Let `z ∈ Ω`; it lies in some `R_i` (`iUnion_eq`). Take `l := col i`. The zeros of `h_l` in `Ω` are exactly `nodeSet Λ^l`. For a zero `w`, §3.4 gives `d(z,w) ≥ c₅ρ̃(z)`.
   - If `d(z,w) ≤ max(ρ̃(z), ρ̃(w))`, Claim 1 for `ν` (`K = 1`, `C_1`) gives `ρ̃(w) ≤ C_1ρ̃(z) ≤ (C_1/c₅)d(z,w)`.
   - Otherwise `ρ̃(w) < d(z,w)`.
   - So `ρ(w) ≤ ρ̃(w) ≤ max(C_1/c₅, 1)d(z,w)`, and `ε := 1/max(C_1/c₅, 1)` works.
3. **Two-sided bound on the good set.** Let `z` satisfy `∀ w ∈ Z(h_l) ∩ Ω, ερ(w) ≤ d(z,w)`.
   - **Distance to the zeros.** For each such `w`: if `d(z,w) ≤ max(ρ(z),ρ(w))`, Claim 1 for **`μ`** (class `(Cd,R₀)`, `K = 1`, `C_1'`) gives `ρ(z) ≤ C_1'ρ(w) ≤ (C_1'/ε)d(z,w)`; otherwise `d(z,w) > ρ(z)`. So `d(z, Z) ≥ c₆ρ(z)` with `c₆ := min(ε/C_1', 1)`, and `d(z,Z)` is finite (`Z ≠ ∅`).
   - **Lower bound.** In `Thm4Bounds*`, `C⁻¹(d/ρ)^M ≤ ofReal(|h_l(z)|e^{−ψ(z)})` with `d/ρ ≥ c₆` gives `|h_l(z)|e^{−ψ(z)} ≥ C⁻¹c₆^M`.
   - **Upper bound.** The middle and third conjuncts give `|h_l(z)|e^{−ψ(z)} ≤ C·d/ρ ≤ C·C`.
   - **ENNReal to real.** Use `ENNReal.ofReal_le_ofReal_iff`, `ENNReal.toReal_ofReal`, `ENNReal.div_le_iff`. `ρ(z) > 0` (`claim1_*_quant`) and `d < ∞`.
4. **Global upper bound.** For every `z`, `|h_l(z)|e^{−ψ(z)} ≤ C·(d/ρ) ≤ C·C`, by the second and third conjuncts. At a zero it is trivial.

Set `C_P := max(C², C c₆^{−M})`, rounded up in `ℝ≥0`. Then the `_quant` constants are `(n, M, max(C, C_P), ε)`.

### 3.6 Corollaries

- **`prop2_disc`, `prop2_plane`, `prop2_disc_full`, `prop2_plane_full`:** proved in the scratch file: obtain `R₀, Cd`; form the class; apply `_quant`; project conjuncts; `0 < C` from `1 ≤ C`.
- **`prop2_*_partition`.**
  - Let `G_i := {z ∈ Ω : ∀ w ∈ Ω, h_i w = 0 → ερ(w) ≤ d(z,w)} = Ω ∩ ⋂_{w ∈ Z_i} {z : ερ(w) ≤ d(z,w)}`.
  - Each `{z : ερ(w) ≤ d(z,w)}` is closed: `d(·,w)` is continuous on `ℂ`, and on `𝔻` for `hypDist`, where we intersect with `𝔻` (`continuousOn_pseudoHyp`, `Real.continuousOn_artanh`). So `G_i` is relatively closed in the open `Ω`, hence measurable (`IsClosed.measurableSet`, `isClosed_biInter`; in `𝔻`, `ContinuousOn.isClosed_inter_preimage`-type lemmas, or write `G_i = 𝔻 ∩ F_i` with `F_i` closed).
  - `Ω_i := G_i ∖ ⋃_{j<i} G_j` (`Fin n` order) is measurable and pairwise disjoint. `⋃ Ω_i = ⋃ G_i = Ω` by the covering conjunct.
  - On `Ω_i ⊆ G_i`: `C⁻¹e^ψ ≤ |h_i|`, so `h_i ≠ 0`. The upper bound holds everywhere.
- **`measClassDisc_of_hypArea`.** For `z ∈ 𝔻`, `hypArea(hypBall z r) = π sinh² r` (M01). With `a hypArea ≤ μ ≤ b hypArea`:
  - **Doubling:** for `2r < 1`, `μ(D(z,2r)) ≤ bπ sinh²(2r) = 4bπ sinh²r cosh²r ≤ 4cosh²(½)(b/a)μ(D(z,r))`. So `Cd := ⌈5b/a⌉₊` works, since `4cosh²(½) < 5`.
  - **Mass:** `μ(D(z,R₀)) ≥ aπ sinh²R₀ > 1` for `R₀ := arsinh((aπ)^{−1/2}) + 1`.
  - **Finite on compacts of `𝔻`:** `μ ≤ b·hypArea`, and the density `(1−|z|²)^{−2}` is bounded on compacts.
- **`prop2_disc_unif`.** Apply `measClassDisc_of_hypArea` (with `μ 𝔻ᶜ = 0` from `IsSubharmonicWeight.carried`), then `prop2_disc_quant`, and project as in `prop2_disc_full`. The constants depend only on `(a, b)`.

---

## 4. Interface

**Consumed:**
- M08: core, builders, cells, classes, `Thm4Bounds*`.
- M03: `claim1_*_quant` for both `μ` and `ν`; `massRadius*_lapNorm_quant`; `MeasClass*.lapNorm`.
- M05: `lemma4_*_quant`.
- M01: `hypArea`, `hypArea_hypBall`, `hypDist_triangle`, continuity of `hypDist`.

**Provided:**
- **M11:** `prop2_disc_full` (exact form of M11 §2.1), `prop2_disc_partition`, `prop2_disc_unif` (exact form of M11 §2.4, for `dbar_sup_estimate_C2_uniform`), `prop2_disc_quant`.
- **M12:** `prop2_plane_full` (exact form of M12 §2.1), `prop2_plane_partition`, `prop2_plane_quant`.
- **Comparator:**
  - the fixed `prop2_disc`, `prop2_plane` are corollaries;
  - the coordinator's strengthened statements ("each `h_i` satisfies the conclusion of Theorem 4", plus `h_i ≢ 0`, plus disjoint exceptional sets) are the projections of `prop2_*_quant` that drop the `_quant` quantifier order: `∃ n M C ε, … ∀ i, Thm4Bounds* ψ μ (h i) M C ∧ …`;
  - **`prop2_*_strong`** is that statement written out with the Theorem-4 inequalities inlined. It is proved from `_quant` in the scratch file. If the comparator adopts it verbatim, nothing else is needed.

---

### 4a. Interface (reconciled)

Lean file `SeveralMultipliers.lean`. Changes from the §1 block:
- **`prop2_disc`, `prop2_plane`.** They are verbatim the current comparator statements, which already contain the Theorem-4 bounds and `h i ≢ 0` for each multiplier. They are proved from `prop2_*_quant`. The former weak forms follow from `prop2_*_full`.
- **`prop2_*_strong`.** Dropped as duplicates.
- **`exists_measurable_partition`.** Moved here from M11, so that both M11 and M12 get it without M12 importing M11.
- **Upstream owners.** `lapNorm`, the classes and `claim1_*_quant` are M03's (`Doubling/Quant.lean`); `lemma4_*_quant` and `IsMassPartition` are M05's; `hypArea`, `hypArea_hypBall` are M01's.
- **`measClassDisc_of_hypArea`: the constant.** The statement has `∃ Cd`, so it is unaffected. In the proof (§3.6), `4cosh²(½) ≈ 5.086 > 5`, so `⌈5b/a⌉₊` is not enough. Take `Cd := ⌈6b/a⌉₊`.

## 5. Issues found (for NOTEBOOK)

1. **p. 369, Besicovitch.** A greedy colouring of the bounded-degree conflict graph suffices (§3.1–§3.2). No covering lemma is needed.
2. **p. 369, "satisfying the conclusion of Theorem 4".** The current comparator `prop2_*` only state `|h_i| ≃ e^ψ` on good points. The proof of Theorem 2 (p. 372) needs `|h_i| ≲ e^ψ` *everywhere*: it follows from Theorem 4's upper bound plus the Remark `d ≲ ρ`, not from the comparator statement. Hence `prop2_*_full` / the strengthened statement.
3. **p. 369, κ placement.** "We can choose a constant `C` in Lemma 5 so that the points `κ(R)` are neither in `R` nor in its immediate neighbours … and not so far that they reach another rectangle of the family" is right in spirit. With nodes *near* `R` (M06), "neighbours" must be the cells whose ordinary nodes come within `O(ρ)` of `R` (`colorSel` with `Bl + 2`), and the κ inner radius `Bk₀` must exceed that neighbourhood. This must be defined with the *ordinary*-node spread `Bl` only. Using M08's near-field radius `K₀` (which depends on the κ spread) would make the choice circular.
4. **p. 370, "the exceptional set for `h_l` does not include any rectangle from the family".** True in the quantitative form of §3.4: every zero is at distance `≥ c₅ρ(z)` from each point `z` of such a rectangle, which gives `z ∉ E_{h_l}` for `ε ≤ ε(c₅)`.
5. **Disc, sparse `Δψ`.** The κ sets of large cells cannot come from Lemma 5 (they would leave `𝔻`). We use `6` copies each of `b ± v`, with `v` tangential and `hypDist(b, b±v)` prescribed (M08 §3.10). This needs `N` even; we take `N = 12`.

**Formalization risks.**
- The greedy colouring by strong recursion (moderate).
- The measurability of `G_i` in `𝔻` (`hypDist` is only continuous on `𝔻 × 𝔻`; intersect with `𝔻` first).
- Bookkeeping of the many constants in §2. It is safest to formalize `nodes_far_of_color_*` exactly as stated: `∃ Bk₀, ∀ Bk Bk', Bk₀ ≤ Bk → ∃ L₀, ∀ L ≥ L₀, ∃ c₅ …`. It fixes the order of choices.
