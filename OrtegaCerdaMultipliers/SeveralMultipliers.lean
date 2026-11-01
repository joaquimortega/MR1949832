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

namespace Prop2

/-- A free colour for vertex `i`, given the colours `g` of the earlier vertices. -/
theorem exists_free_colour (adj : ℕ → ℕ → Prop) (D : ℕ) (hdeg : ∀ i, {j | adj i j}.encard ≤ D)
    (i : ℕ) (g : ℕ → Fin (D + 1)) :
    ∃ c : Fin (D + 1), ∀ j < i, adj i j → g j ≠ c := by
  classical
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ((Finset.range i).filter (adj i ·)).image g) (t := Finset.univ) (by
      refine (Finset.card_image_le).trans_lt ?_
      rw [Finset.card_univ, Fintype.card_fin]
      have h1 : (((Finset.range i).filter (adj i ·) : Finset ℕ) : Set ℕ).encard ≤ D :=
        (Set.encard_le_encard fun j hj ↦ by simpa using (Finset.mem_filter.1 hj).2).trans (hdeg i)
      rw [Set.encard_coe_eq_coe_finsetCard] at h1
      exact Nat.lt_succ_of_le (by exact_mod_cast h1))
  refine ⟨c, fun j hj hadj hgc ↦ hc ?_⟩
  exact Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hadj⟩, hgc⟩

/-- The greedy colouring. -/
def greedy (adj : ℕ → ℕ → Prop) (D : ℕ) (hdeg : ∀ i, {j | adj i j}.encard ≤ D) :
    ℕ → Fin (D + 1) :=
  Nat.strongRec fun i prev ↦ Classical.choose
    (exists_free_colour adj D hdeg i fun j ↦ if h : j < i then prev j h else 0)

theorem greedy_spec (adj : ℕ → ℕ → Prop) (D : ℕ) (hdeg : ∀ i, {j | adj i j}.encard ≤ D)
    (i : ℕ) : ∀ j < i, adj i j → greedy adj D hdeg j ≠ greedy adj D hdeg i := by
  intro j hj hadj
  have hspec := Classical.choose_spec (exists_free_colour adj D hdeg i
    fun j ↦ if h : j < i then greedy adj D hdeg j else 0) j hj hadj
  simp only [hj, dite_true] at hspec
  convert hspec using 1
  rw [greedy, Nat.strongRec_eq]
  rfl

end Prop2

/-- Greedy colouring of a symmetric graph on `ℕ` of degree `≤ D`. -/
theorem exists_coloring_nat (adj : ℕ → ℕ → Prop) (hsymm : ∀ i j, adj i j → adj j i) (D : ℕ)
    (hdeg : ∀ i, {j | adj i j}.encard ≤ D) :
    ∃ col : ℕ → Fin (D + 1), ∀ i j, i ≠ j → adj i j → col i ≠ col j := by
  refine ⟨Prop2.greedy adj D hdeg, fun i j hij hadj ↦ ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact Prop2.greedy_spec adj D hdeg j i h (hsymm i j hadj)
  · exact (Prop2.greedy_spec adj D hdeg i j h hadj).symm

namespace Prop2

/-- Bounded degree from a uniform bound on finite neighbourhoods. -/
theorem encard_le_of_finset {S : Set ℕ} {D : ℕ} (h : ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ S → F.card ≤ D) :
    S.encard ≤ D := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hcon)
  have htf : t.Finite := Set.finite_of_encard_eq_coe htc
  have hF := h htf.toFinset (by simpa using hts)
  have : (htf.toFinset.card : ℕ∞) = D + 1 := by
    rw [← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset, htc]
  have : htf.toFinset.card = D + 1 := by exact_mod_cast this
  omega

/-- Generic separated colouring. -/
theorem sepColoring_generic {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {A L CL : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} (Cm : ℝ≥0)
    (hRm : ∀ i, MeasurableSet (R i)) (hdisj : Pairwise (Function.onFun Disjoint R))
    (hRN : ∀ i, ν (R i) = N) (hN : 1 ≤ N) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hsymm : ∀ x ∈ Ω, ∀ y ∈ Ω, d x y = d y x)
    (htri : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ z ∈ Ω, d x z ≤ d x y + d y z)
    (hρ : ∀ x ∈ Ω, 0 < ρ x)
    (hcl : ∀ x ∈ Ω, ∀ y ∈ Ω, d x y ≤ (2 * L) * max (ρ x) (ρ y) → ρ x ≤ CL * ρ y)
    (hRΩ : ∀ i, R i ⊆ Ω) (hcR : ∀ i, c i ∈ R i) (hsub : ∀ i, ∀ w ∈ R i, d (c i) w ≤ A * ρ (c i))
    (hmass : ∀ i, ν {w | w ∈ Ω ∧ d (c i) w < (L + (L + A) * CL) * ρ (c i)} ≤ Cm) :
    ∃ col : ℕ → Fin (⌊(Cm : ℝ)⌋₊ + 1), ∀ i j, i ≠ j → col i = col j →
      L * (ρ (c i) + ρ (c j)) ≤ d (c i) (c j) := by
  classical
  have hcΩ : ∀ k, c k ∈ Ω := fun k ↦ hRΩ k (hcR k)
  set adj : ℕ → ℕ → Prop := fun i j ↦ i ≠ j ∧ d (c i) (c j) < L * (ρ (c i) + ρ (c j))
  have hsymm' : ∀ i j, adj i j → adj j i := fun i j ⟨hij, h⟩ ↦
    ⟨hij.symm, by rw [hsymm _ (hcΩ j) _ (hcΩ i), add_comm]; exact h⟩
  have hdeg : ∀ i, {j | adj i j}.encard ≤ ⌊(Cm : ℝ)⌋₊ := by
    intro i
    apply encard_le_of_finset
    intro F hF
    have hsubF : (⋃ j ∈ F, R j) ⊆
        {w | w ∈ Ω ∧ d (c i) w < (L + (L + A) * CL) * ρ (c i)} := by
      intro w hw
      simp only [mem_iUnion] at hw
      obtain ⟨j, hjF, hwj⟩ := hw
      obtain ⟨-, hij⟩ := hF hjF
      have hρi := hρ _ (hcΩ i)
      have hρj := hρ _ (hcΩ j)
      have hji : ρ (c j) ≤ CL * ρ (c i) := by
        apply hcl _ (hcΩ j) _ (hcΩ i)
        rw [hsymm _ (hcΩ j) _ (hcΩ i)]
        have h1 : L * ρ (c i) ≤ L * max (ρ (c j)) (ρ (c i)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hL
        have h2 : L * ρ (c j) ≤ L * max (ρ (c j)) (ρ (c i)) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hL
        linarith only [hij, h1, h2]
      refine ⟨hRΩ j hwj, ?_⟩
      have h1 := htri _ (hcΩ i) _ (hcΩ j) _ (hRΩ j hwj)
      have h2 := hsub j w hwj
      have h3 : (L + A) * ρ (c j) ≤ (L + A) * (CL * ρ (c i)) :=
        mul_le_mul_of_nonneg_left hji (by linarith)
      linarith only [h1, h2, h3, hij]
    have hmeas := (measure_mono hsubF).trans (hmass i)
    rw [measure_biUnion_finset (fun j _ k _ hjk ↦ hdisj hjk) (fun j _ ↦ hRm j)] at hmeas
    simp only [hRN, Finset.sum_const, nsmul_eq_mul] at hmeas
    have : ((F.card : ℝ≥0) : ℝ≥0∞) ≤ Cm := by
      refine le_trans ?_ hmeas
      rw [ENNReal.coe_natCast]
      calc (F.card : ℝ≥0∞) = F.card * 1 := (mul_one _).symm
        _ ≤ F.card * N := by gcongr; exact_mod_cast hN
    rw [ENNReal.coe_le_coe] at this
    exact Nat.le_floor (by exact_mod_cast this)
  obtain ⟨col, hcol⟩ := exists_coloring_nat adj hsymm' _ hdeg
  refine ⟨col, fun i j hij hcij ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  exact hcol i j hij ⟨hij, hlt⟩ hcij

end Prop2

namespace Prop2

/-- Cells of a measure in the class have positive mass (plane). -/
theorem one_le_N_plane {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ} {R : ℕ → Set ℂ}
    {c : ℕ → ℂ} (hν : MeasClassPlane ν Cd R₀)
    (hC : IsCells univ dist (massRadius ν) ν N η A R c) : 1 ≤ N := by
  by_contra h
  have hN0 : N = 0 := by omega
  have h1 := hν.mass 0
  have h2 : ν univ = 0 := by
    rw [← hC.iUnion_eq]
    exact measure_iUnion_null fun i ↦ by rw [hC.measure_eq, hN0]; simp
  rw [measure_mono_null (subset_univ _) h2] at h1
  simp at h1

/-- Cells of a measure in the class have positive mass (disc). -/
theorem one_le_N_disc {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ} {R : ℕ → Set ℂ}
    {c : ℕ → ℂ} (hν : MeasClassDisc ν Cd R₀)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c) : 1 ≤ N := by
  by_contra h
  have hN0 : N = 0 := by omega
  have h1 := hν.mass 0 (mem_ball_self one_pos)
  have h2 : ν 𝔻 = 0 := by
    rw [← hC.iUnion_eq]
    exact measure_iUnion_null fun i ↦ by rw [hC.measure_eq, hN0]; simp
  rw [measure_mono_null (hypBall_subset_disc 0 R₀) h2] at h1
  simp at h1

end Prop2

/-- Separated colouring of the cells (plane): same colour ⟹ `L`-separated centres. -/
theorem exists_separated_coloring_plane (Cd : ℝ≥0) (R₀ η A L : ℝ) (hη : 0 < η) :
    ∃ n : ℕ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c →
      ∃ col : ℕ → Fin n, ∀ i j, i ≠ j → col i = col j →
        L * (massRadius ν (c i) + massRadius ν (c j)) ≤ dist (c i) (c j) := by
  set L' := max L 0
  set A' := max A 0
  obtain ⟨CL, -, hcl⟩ := claim1_plane_quant Cd R₀ (2 * L')
  obtain ⟨Cm, hCm⟩ := measure_ball_massRadius_quant Cd R₀ (L' + (L' + A') * CL)
  refine ⟨⌊(Cm : ℝ)⌋₊ + 1, fun ν N R c hν hC ↦ ?_⟩
  have hρ : ∀ x, 0 < massRadius ν x := fun x ↦ (hcl ν hν x x).1
  obtain ⟨col, hcol⟩ := Prop2.sepColoring_generic (Ω := univ) (d := dist) (ρ := massRadius ν)
    (L := L') (A := A') (CL := CL) Cm hC.measurableSet hC.pairwise_disjoint hC.measure_eq
    (Prop2.one_le_N_plane hν hC) (le_max_right _ _) (le_max_right _ _)
    (fun x _ y _ ↦ dist_comm x y) (fun x _ y _ z _ ↦ dist_triangle x y z)
    (fun x _ ↦ hρ x) (fun x _ y _ ↦ (hcl ν hν x y).2.2) (fun _ ↦ subset_univ _) hC.center_mem
    (fun i w hw ↦ (hC.subset i w hw).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hρ _).le))
    (fun i ↦ by
      convert hCm ν hν (c i) using 2
      ext w
      simp [mem_ball, dist_comm])
  refine ⟨col, fun i j hij hcij ↦ le_trans ?_ (hcol i j hij hcij)⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg (hρ _).le (hρ _).le)

/-- Separated colouring of the cells (disc). -/
theorem exists_separated_coloring_disc (Cd : ℝ≥0) (R₀ η A L : ℝ) (hη : 0 < η) :
    ∃ n : ℕ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassDisc ν Cd R₀ → IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c →
      ∃ col : ℕ → Fin n, ∀ i j, i ≠ j → col i = col j →
        L * (massRadiusDisc ν (c i) + massRadiusDisc ν (c j)) ≤ hypDist (c i) (c j) := by
  set L' := max L 0
  set A' := max A 0
  obtain ⟨CL, -, hcl⟩ := claim1_disc_quant Cd R₀ (2 * L')
  obtain ⟨Cm, hCm⟩ := measure_hypBall_massRadius_quant Cd R₀ (L' + (L' + A') * CL)
  refine ⟨⌊(Cm : ℝ)⌋₊ + 1, fun ν N R c hν hC ↦ ?_⟩
  have hRΩ : ∀ i, R i ⊆ 𝔻 := fun i ↦ hC.iUnion_eq ▸ subset_iUnion R i
  have hcD : ∀ i, c i ∈ 𝔻 := fun i ↦ hRΩ i (hC.center_mem i)
  have hρ : ∀ x ∈ 𝔻, 0 < massRadiusDisc ν x := fun x hx ↦ (hcl ν hν x hx x hx).1
  obtain ⟨col, hcol⟩ := Prop2.sepColoring_generic (Ω := 𝔻) (d := hypDist)
    (ρ := massRadiusDisc ν) (L := L') (A := A') (CL := CL) Cm hC.measurableSet
    hC.pairwise_disjoint hC.measure_eq (Prop2.one_le_N_disc hν hC) (le_max_right _ _)
    (le_max_right _ _) (fun x _ y _ ↦ hypDist_comm x y)
    (fun x hx y hy z hz ↦ hypDist_triangle hx hy hz) hρ
    (fun x hx y hy ↦ (hcl ν hν x hx y hy).2.2) hRΩ hC.center_mem
    (fun i w hw ↦ (hC.subset i w hw).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hρ _ (hcD i)).le))
    (fun i ↦ hCm ν hν (c i) (hcD i))
  refine ⟨col, fun i j hij hcij ↦ le_trans ?_ (hcol i j hij hcij)⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _)
    (add_nonneg (hρ _ (hcD i)).le (hρ _ (hcD j)).le)

/-- The selection for colour `l`: cells of colour `l` and their `K`-neighbours. -/
def colorSel (d : ℂ → ℂ → ℝ) (ρ : ℂ → ℝ) (R : ℕ → Set ℂ) (c : ℕ → ℂ) {n : ℕ}
    (col : ℕ → Fin n) (K : ℝ) (l : Fin n) (j : ℕ) : Prop :=
  ∃ k, col k = l ∧ (j = k ∨ ∃ z ∈ R k, d z (c j) < K * ρ (c j))

namespace Prop2

theorem nodesFar_generic {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ}
    {n : ℕ} {col : ℕ → Fin n} {l : Fin n} {Λ : ℕ → Multiset ℂ}
    {A Bl Bk Bk' L C1 CA C2 : ℝ}
    (hA : 0 ≤ A) (hBl : 0 ≤ Bl) (hC1 : 1 ≤ C1) (hCA : 1 ≤ CA) (hC2 : 1 ≤ C2)
    (hBk1 : A + 1 ≤ Bk) (hBk2 : 2 * A * C2 + Bl + 3 ≤ Bk)
    (hL1 : A + 1 ≤ L) (hL2 : A + (Bl + 2 + max Bk' 0) * C2 ≤ L)
    (hsymm : ∀ x ∈ Ω, ∀ y ∈ Ω, d x y = d y x)
    (htri : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ z ∈ Ω, d x z ≤ d x y + d y z)
    (hρ : ∀ x ∈ Ω, 0 < ρ x)
    (hcl1 : ∀ x ∈ Ω, ∀ y ∈ Ω, d x y ≤ 1 * max (ρ x) (ρ y) → ρ x ≤ C1 * ρ y)
    (hclA : ∀ x ∈ Ω, ∀ y ∈ Ω, d x y ≤ A * max (ρ x) (ρ y) → ρ x ≤ CA * ρ y)
    (hcl2 : ∀ x ∈ Ω, ∀ y ∈ Ω, d x y ≤ (A + Bl + 2) * max (ρ x) (ρ y) → ρ x ≤ C2 * ρ y)
    (hRΩ : ∀ i, R i ⊆ Ω) (hcR : ∀ i, c i ∈ R i) (hsub : ∀ i, ∀ w ∈ R i, d (c i) w ≤ A * ρ (c i))
    (hΛΩ : ∀ j, ∀ w ∈ Λ j, w ∈ Ω)
    (hsep : ∀ i j, i ≠ j → col i = col j → L * (ρ (c i) + ρ (c j)) ≤ d (c i) (c j))
    (hns : ∀ j, ¬ colorSel d ρ R c col (Bl + 2) l j → ∀ w ∈ Λ j, d (c j) w ≤ Bl * ρ (c j))
    (hs : ∀ j, colorSel d ρ R c col (Bl + 2) l j →
      ∀ w ∈ Λ j, Bk * ρ (c j) ≤ d (c j) w ∧ d (c j) w ≤ Bk' * ρ (c j)) :
    ∀ i, col i = l → ∀ z ∈ R i, ∀ j, ∀ w ∈ Λ j,
      (C1 * (Bl + 2) * C2 * CA)⁻¹ * ρ z ≤ d z w := by
  intro i hi z hz j w hw
  have hcΩ : ∀ k, c k ∈ Ω := fun k ↦ hRΩ k (hcR k)
  have hzΩ : z ∈ Ω := hRΩ i hz
  have hwΩ : w ∈ Ω := hΛΩ j w hw
  set P := C1 * (Bl + 2) * C2 * CA with hP
  have hρz := hρ z hzΩ
  have hρi := hρ (c i) (hcΩ i)
  have hρj := hρ (c j) (hcΩ j)
  have hC2CA : 1 ≤ C2 * CA := one_le_mul_of_one_le_of_one_le hC2 hCA
  have hP0 : 0 < P := by positivity
  have hPC1 : C1 ≤ P := by
    have : 1 ≤ (Bl + 2) * C2 * CA := by nlinarith
    calc C1 = C1 * 1 := (mul_one _).symm
      _ ≤ C1 * ((Bl + 2) * C2 * CA) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = P := by rw [hP]; ring
  have hPBl : Bl + 2 ≤ P := by
    have : 1 ≤ C1 * C2 * CA := by nlinarith
    calc Bl + 2 = (Bl + 2) * 1 := (mul_one _).symm
      _ ≤ (Bl + 2) * (C1 * C2 * CA) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = P := by rw [hP]; ring
  have hPC : C2 * CA ≤ P := by
    have : 1 ≤ C1 * (Bl + 2) := by nlinarith
    calc C2 * CA = 1 * (C2 * CA) := (one_mul _).symm
      _ ≤ (C1 * (Bl + 2)) * (C2 * CA) := mul_le_mul_of_nonneg_right this (by linarith)
      _ = P := by rw [hP]; ring
  have hPA : CA ≤ P := le_trans (by nlinarith) hPC
  -- it suffices to show `ρ z ≤ P * d z w`
  suffices hsuff : ρ z ≤ P * d z w by
    rw [inv_mul_le_iff₀ hP0]; exact hsuff
  -- `ρ z ≤ CA ρ_i`
  have hdzi : d z (c i) ≤ A * ρ (c i) := by
    rw [hsymm _ hzΩ _ (hcΩ i)]; exact hsub i z hz
  have hzi : ρ z ≤ CA * ρ (c i) :=
    hclA z hzΩ (c i) (hcΩ i) (hdzi.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hA))
  -- generic conclusion from `ρ_i ≤ d z w`
  have hfromi : ρ (c i) ≤ d z w → ρ z ≤ P * d z w := fun h ↦ by
    have : 0 ≤ d z w := hρi.le.trans h
    calc ρ z ≤ CA * ρ (c i) := hzi
      _ ≤ CA * d z w := mul_le_mul_of_nonneg_left h (by linarith)
      _ ≤ P * d z w := mul_le_mul_of_nonneg_right hPA this
  by_cases hsel : colorSel d ρ R c col (Bl + 2) l j
  · obtain ⟨hwlo, hwhi⟩ := hs j hsel w hw
    obtain ⟨k, hk, hjk⟩ := hsel
    by_cases hki : k = i
    · subst hki
      rcases hjk with rfl | ⟨z', hz', hz'j⟩
      · -- Case 2: `j = i`
        apply hfromi
        have h1 := htri (c j) (hcΩ j) z hzΩ w hwΩ
        have h2 := hsub j z hz
        nlinarith
      · -- Case 3: `j` is a neighbour of `i`
        have hz'Ω := hRΩ k hz'
        have hdij : d (c k) (c j) ≤ (A + Bl + 2) * max (ρ (c k)) (ρ (c j)) := by
          have h1 := htri (c k) (hcΩ k) z' hz'Ω (c j) (hcΩ j)
          have h2 := hsub k z' hz'
          have h3 : A * ρ (c k) ≤ A * max (ρ (c k)) (ρ (c j)) :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) hA
          have h4 : (Bl + 2) * ρ (c j) ≤ (Bl + 2) * max (ρ (c k)) (ρ (c j)) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
          nlinarith
        have hkj : ρ (c k) ≤ C2 * ρ (c j) := hcl2 _ (hcΩ k) _ (hcΩ j) hdij
        have hdzj : d z (c j) ≤ (2 * A * C2 + Bl + 2) * ρ (c j) := by
          have h1 := htri z hzΩ (c k) (hcΩ k) (c j) (hcΩ j)
          have h1' := htri (c k) (hcΩ k) z' hz'Ω (c j) (hcΩ j)
          have h2 := hsub k z' hz'
          have h3 : A * ρ (c k) ≤ A * (C2 * ρ (c j)) := mul_le_mul_of_nonneg_left hkj hA
          nlinarith
        have hjw : ρ (c j) ≤ d z w := by
          have h1 := htri (c j) (hcΩ j) z hzΩ w hwΩ
          rw [hsymm _ (hcΩ j) _ hzΩ] at h1
          have h2 : (2 * A * C2 + Bl + 3) * ρ (c j) ≤ Bk * ρ (c j) :=
            mul_le_mul_of_nonneg_right hBk2 hρj.le
          nlinarith
        have h0 : 0 ≤ d z w := hρj.le.trans hjw
        calc ρ z ≤ CA * ρ (c k) := hzi
          _ ≤ CA * (C2 * ρ (c j)) := mul_le_mul_of_nonneg_left hkj (by linarith)
          _ = (C2 * CA) * ρ (c j) := by ring
          _ ≤ (C2 * CA) * d z w := mul_le_mul_of_nonneg_left hjw (by linarith)
          _ ≤ P * d z w := mul_le_mul_of_nonneg_right hPC h0
    · -- Case 4: `j` selected through another cell `k` of colour `l`
      apply hfromi
      have hρk := hρ (c k) (hcΩ k)
      have hsepik := hsep i k (Ne.symm hki) (hi.trans hk.symm)
      set L' := A + (Bl + 2 + max Bk' 0) * C2
      have hBk'0 : 0 ≤ max Bk' 0 := le_max_right _ _
      have hkw : d (c k) w ≤ L' * ρ (c k) := by
        rcases hjk with rfl | ⟨z', hz', hz'j⟩
        · have h1 : Bk' * ρ (c j) ≤ max Bk' 0 * ρ (c j) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hρj.le
          have h2 : max Bk' 0 ≤ L' := by
            have : max Bk' 0 ≤ max Bk' 0 * C2 := le_mul_of_one_le_right hBk'0 hC2
            nlinarith
          nlinarith
        · have hz'Ω := hRΩ k hz'
          have hdkj : d (c j) (c k) ≤ (A + Bl + 2) * max (ρ (c j)) (ρ (c k)) := by
            rw [hsymm _ (hcΩ j) _ (hcΩ k)]
            have h1 := htri (c k) (hcΩ k) z' hz'Ω (c j) (hcΩ j)
            have h2 := hsub k z' hz'
            have h3 : A * ρ (c k) ≤ A * max (ρ (c j)) (ρ (c k)) :=
              mul_le_mul_of_nonneg_left (le_max_right _ _) hA
            have h4 : (Bl + 2) * ρ (c j) ≤ (Bl + 2) * max (ρ (c j)) (ρ (c k)) :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
            nlinarith
          have hjk' : ρ (c j) ≤ C2 * ρ (c k) := hcl2 _ (hcΩ j) _ (hcΩ k) hdkj
          have h1 := htri (c k) (hcΩ k) (c j) (hcΩ j) w hwΩ
          have h1' := htri (c k) (hcΩ k) z' hz'Ω (c j) (hcΩ j)
          have h2 := hsub k z' hz'
          have h3 : Bk' * ρ (c j) ≤ max Bk' 0 * ρ (c j) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hρj.le
          have h4 : (Bl + 2 + max Bk' 0) * ρ (c j) ≤ (Bl + 2 + max Bk' 0) * (C2 * ρ (c k)) :=
            mul_le_mul_of_nonneg_left hjk' (by linarith)
          nlinarith
      have h1 := htri (c i) (hcΩ i) z hzΩ (c k) (hcΩ k)
      have h2 := htri z hzΩ w hwΩ (c k) (hcΩ k)
      rw [hsymm w hwΩ (c k) (hcΩ k)] at h2
      have h3 := hsub i z hz
      have h4 : (A + 1) * ρ (c i) ≤ L * ρ (c i) := mul_le_mul_of_nonneg_right hL1 hρi.le
      have h5 : L' * ρ (c k) ≤ L * ρ (c k) := mul_le_mul_of_nonneg_right hL2 hρk.le
      nlinarith
  · -- Case 1: `j` not selected
    have hnot : ¬ (j = i ∨ ∃ z' ∈ R i, d z' (c j) < (Bl + 2) * ρ (c j)) :=
      fun h ↦ hsel ⟨i, hi, h⟩
    push Not at hnot
    have hzj : (Bl + 2) * ρ (c j) ≤ d z (c j) := hnot.2 z hz
    have hwj := hns j hsel w hw
    have htr := htri z hzΩ (c j) (hcΩ j) w hwΩ
    have htr' := htri z hzΩ w hwΩ (c j) (hcΩ j)
    rw [hsymm w hwΩ (c j) (hcΩ j)] at htr'
    have hdzw : 2 * ρ (c j) ≤ d z w := by nlinarith
    have h0 : 0 ≤ d z w := le_trans (by linarith) hdzw
    by_cases hcase : d z (c j) ≤ 1 * max (ρ z) (ρ (c j))
    · have := hcl1 z hzΩ (c j) (hcΩ j) hcase
      calc ρ z ≤ C1 * ρ (c j) := this
        _ ≤ C1 * d z w := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        _ ≤ P * d z w := mul_le_mul_of_nonneg_right hPC1 h0
    · push Not at hcase
      have hlt : ρ z < d z (c j) := lt_of_le_of_lt (by simp) hcase
      have h1 : Bl * ((Bl + 2) * ρ (c j)) ≤ Bl * d z (c j) := mul_le_mul_of_nonneg_left hzj hBl
      have h3 : (Bl + 2) * (d z (c j) - Bl * ρ (c j)) ≤ (Bl + 2) * d z w :=
        mul_le_mul_of_nonneg_left (by linarith only [htr', hwj]) (by linarith only [hBl])
      have h2 : 2 * ρ z ≤ (Bl + 2) * d z w := by linarith only [h1, h3, hlt]
      calc ρ z ≤ (Bl + 2) * d z w := by linarith only [h2, hρz]
        _ ≤ P * d z w := mul_le_mul_of_nonneg_right hPBl h0

end Prop2

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
      ∀ i, col i = l → ∀ z ∈ R i, ∀ j, ∀ w ∈ Λ j, c₅ * massRadius ν z ≤ dist z w := by
  obtain ⟨C1, hC1, hcl1⟩ := claim1_plane_quant Cd R₀ 1
  obtain ⟨CA, hCA, hclA⟩ := claim1_plane_quant Cd R₀ A
  obtain ⟨C2, hC2, hcl2⟩ := claim1_plane_quant Cd R₀ (A + Bl + 2)
  have hBl2 : 0 < Bl + 2 := by linarith
  refine ⟨max (A + 1) (2 * A * C2 + Bl + 3), fun Bk Bk' hBk ↦
    ⟨max (A + 1) (A + (Bl + 2 + max Bk' 0) * C2), fun L hL ↦
      ⟨(C1 * (Bl + 2) * C2 * CA)⁻¹, by positivity, ?_⟩⟩⟩
  intro ν N R c n col l Λ hν hC hsep hns hs
  exact Prop2.nodesFar_generic (Ω := univ) hA.le hBl hC1 hCA hC2 (le_of_max_le_left hBk)
    (le_of_max_le_right hBk) (le_of_max_le_left hL) (le_of_max_le_right hL)
    (fun x _ y _ ↦ dist_comm x y) (fun x _ y _ z _ ↦ dist_triangle x y z)
    (fun x _ ↦ (hcl1 ν hν x x).1) (fun x _ y _ ↦ (hcl1 ν hν x y).2.2)
    (fun x _ y _ ↦ (hclA ν hν x y).2.2) (fun x _ y _ ↦ (hcl2 ν hν x y).2.2)
    (fun _ ↦ subset_univ _) hC.center_mem hC.subset (fun _ _ _ ↦ mem_univ _) hsep hns hs

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
      ∀ i, col i = l → ∀ z ∈ R i, ∀ j, ∀ w ∈ Λ j, c₅ * massRadiusDisc ν z ≤ hypDist z w := by
  obtain ⟨C1, hC1, hcl1⟩ := claim1_disc_quant Cd R₀ 1
  obtain ⟨CA, hCA, hclA⟩ := claim1_disc_quant Cd R₀ A
  obtain ⟨C2, hC2, hcl2⟩ := claim1_disc_quant Cd R₀ (A + Bl + 2)
  have hBl2 : 0 < Bl + 2 := by linarith
  refine ⟨max (A + 1) (2 * A * C2 + Bl + 3), fun Bk Bk' hBk ↦
    ⟨max (A + 1) (A + (Bl + 2 + max Bk' 0) * C2), fun L hL ↦
      ⟨(C1 * (Bl + 2) * C2 * CA)⁻¹, by positivity, ?_⟩⟩⟩
  intro ν N R c n col l Λ hν hC hΛ hsep hns hs
  exact Prop2.nodesFar_generic (Ω := 𝔻) hA.le hBl hC1 hCA hC2 (le_of_max_le_left hBk)
    (le_of_max_le_right hBk) (le_of_max_le_left hL) (le_of_max_le_right hL)
    (fun x _ y _ ↦ hypDist_comm x y) (fun x hx y hy z hz ↦ hypDist_triangle hx hy hz)
    (fun x hx ↦ (hcl1 ν hν x hx x hx).1) (fun x hx y hy ↦ (hcl1 ν hν x hx y hy).2.2)
    (fun x hx y hy ↦ (hclA ν hν x hx y hy).2.2) (fun x hx y hy ↦ (hcl2 ν hν x hx y hy).2.2)
    (fun i ↦ hC.iUnion_eq ▸ subset_iUnion R i) hC.center_mem hC.subset hΛ hsep hns hs

namespace Prop2

theorem thm4BoundsPlane_mono {ψ : ℂ → ℝ} {μ : Measure ℂ} {h : ℂ → ℂ} {M : ℕ} {C C' : ℝ≥0}
    (hC : 0 < C) (hCC' : C ≤ C') (hb : Thm4BoundsPlane ψ μ h M C) :
    Thm4BoundsPlane ψ μ h M C' := by
  intro z
  obtain ⟨h1, h2, h3⟩ := hb z
  have hc : (C : ℝ≥0∞) ≤ C' := ENNReal.coe_le_coe.2 hCC'
  have hc' : ((C'⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ ((C⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_le_coe.2 (inv_anti₀ hC hCC')
  exact ⟨le_trans (by gcongr) h1, h2.trans (by gcongr), h3.trans (by gcongr)⟩

theorem thm4BoundsDisc_mono {ψ : ℂ → ℝ} {μ : Measure ℂ} {h : ℂ → ℂ} {M : ℕ} {C C' : ℝ≥0}
    (hC : 0 < C) (hCC' : C ≤ C') (hb : Thm4BoundsDisc ψ μ h M C) :
    Thm4BoundsDisc ψ μ h M C' := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hb z hz
  have hc : (C : ℝ≥0∞) ≤ C' := ENNReal.coe_le_coe.2 hCC'
  have hc' : ((C'⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ ((C⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_le_coe.2 (inv_anti₀ hC hCC')
  exact ⟨le_trans (by gcongr) h1, h2.trans (by gcongr), h3.trans (by gcongr)⟩

/-- Upper bound `|h| ≤ C² e^ψ` from the Theorem-4 upper bound and the Remark `d ≤ C ρ`. -/
theorem upper_of_bounds {D : ℝ≥0∞} {ρ x ψ : ℝ} {C : ℝ≥0} (hx : 0 ≤ x)
    (h1 : ENNReal.ofReal (x * Real.exp (-ψ)) ≤ C * (D / ENNReal.ofReal ρ))
    (h2 : D ≤ C * ENNReal.ofReal ρ) : x ≤ (C : ℝ) ^ 2 * Real.exp ψ := by
  have h3 : D / ENNReal.ofReal ρ ≤ C := ENNReal.div_le_of_le_mul h2
  have h4 : ENNReal.ofReal (x * Real.exp (-ψ)) ≤ ENNReal.ofReal ((C : ℝ) ^ 2) := by
    rw [ENNReal.ofReal_pow C.coe_nonneg, ENNReal.ofReal_coe_nnreal, sq]
    exact h1.trans (by gcongr)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h4
  calc x = x * Real.exp (-ψ) * Real.exp ψ := by rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ (C : ℝ) ^ 2 * Real.exp ψ := mul_le_mul_of_nonneg_right h4 (Real.exp_pos ψ).le

/-- Lower bound `C⁻¹ c₆^M e^ψ ≤ |h|` from the Theorem-4 lower bound and `d ≥ c₆ ρ`. -/
theorem lower_of_bounds {D : ℝ≥0∞} {ρ c₆ x ψ : ℝ} {C : ℝ≥0} {M : ℕ} (hρ : 0 < ρ)
    (hc₆ : 0 ≤ c₆) (hC : 0 < C) (hx : 0 ≤ x) (hD : ENNReal.ofReal (c₆ * ρ) ≤ D)
    (h1 : ((C⁻¹ : ℝ≥0) : ℝ≥0∞) * (D / ENNReal.ofReal ρ) ^ M ≤
      ENNReal.ofReal (x * Real.exp (-ψ))) :
    (C : ℝ)⁻¹ * c₆ ^ M * Real.exp ψ ≤ x := by
  have h2 : ENNReal.ofReal c₆ ≤ D / ENNReal.ofReal ρ := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hρ)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul hc₆]
    exact hD
  have hC' : (0 : ℝ) < C := hC
  have h3 : ENNReal.ofReal ((C : ℝ)⁻¹ * c₆ ^ M) ≤ ENNReal.ofReal (x * Real.exp (-ψ)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hc₆,
      ENNReal.ofReal_inv_of_pos hC', ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_inv hC.ne']
    exact le_trans (by gcongr) h1
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  calc (C : ℝ)⁻¹ * c₆ ^ M * Real.exp ψ ≤ x * Real.exp (-ψ) * Real.exp ψ :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos ψ).le
    _ = x := by rw [mul_assoc, ← Real.exp_add]; simp

theorem nodeSet_countable (Λ : ℕ → Multiset ℂ) : (nodeSet Λ).Countable := by
  have : nodeSet Λ = ⋃ i, ((Λ i).toFinset : Set ℂ) := by ext w; simp [nodeSet]
  rw [this]
  exact countable_iUnion fun i ↦ (Λ i).toFinset.countable_toSet

theorem exists_mem_disc_notMem_nodeSet (Λ : ℕ → Multiset ℂ) : ∃ z ∈ 𝔻, z ∉ nodeSet Λ := by
  by_contra h
  push Not at h
  have h0 : volume (nodeSet Λ) = 0 := (nodeSet_countable Λ).measure_zero volume
  exact (measure_ball_pos volume (0 : ℂ) one_pos).ne' (measure_mono_null h h0)

/-- Constants of the good-set bounds: `C_P = max(C², C c₆^{-M})`. -/
theorem constP_spec {C : ℝ≥0} (hC : 1 ≤ C) {c₆ : ℝ} (M : ℕ) (hc₆ : 0 < c₆) :
    C ≤ Real.toNNReal (max ((C : ℝ) ^ 2) (C * c₆⁻¹ ^ M)) ∧
    (C : ℝ) ^ 2 ≤ (Real.toNNReal (max ((C : ℝ) ^ 2) (C * c₆⁻¹ ^ M)) : ℝ) ∧
    ((Real.toNNReal (max ((C : ℝ) ^ 2) (C * c₆⁻¹ ^ M)) : ℝ))⁻¹ ≤ (C : ℝ)⁻¹ * c₆ ^ M := by
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hCP : ((Real.toNNReal (max ((C : ℝ) ^ 2) (C * c₆⁻¹ ^ M)) : ℝ)) =
      max ((C : ℝ) ^ 2) (C * c₆⁻¹ ^ M) := Real.coe_toNNReal _ (le_max_of_le_left (sq_nonneg _))
  have hCC2 : (C : ℝ) ≤ C ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, hCP]; exact le_max_of_le_left hCC2
  · rw [hCP]; exact le_max_left _ _
  · rw [hCP]
    have hpos : 0 < (C : ℝ)⁻¹ * c₆ ^ M := by positivity
    calc (max ((C : ℝ) ^ 2) (C * c₆⁻¹ ^ M))⁻¹ ≤ ((C : ℝ)⁻¹ * c₆ ^ M)⁻¹⁻¹ := by
          apply inv_anti₀ (inv_pos.2 hpos)
          rw [mul_inv, inv_inv, ← inv_pow]
          exact le_max_right _ _
      _ = (C : ℝ)⁻¹ * c₆ ^ M := inv_inv _

end Prop2

/-- **Proposition 2, quantitative, full form (plane).** -/
theorem prop2_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ (n M : ℕ) (C : ℝ≥0) (ε : ℝ), 1 ≤ M ∧ 1 ≤ C ∧ 0 < ε ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassPlane ψ μ Cd R₀ →
      ∃ h : Fin n → ℂ → ℂ, (∀ i, Differentiable ℂ (h i)) ∧ (∀ i, ∃ z₀, h i z₀ ≠ 0) ∧
        (∀ i, Thm4BoundsPlane ψ μ (h i) M C) ∧
        (∀ z : ℂ, ∃ i, ∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) ∧
        (∀ i, ∀ z : ℂ, (∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) →
          (C : ℝ)⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ ∧ ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
        (∀ i, ∀ z : ℂ, ‖h i z‖ ≤ C * Real.exp (ψ z)) := by
  classical
  -- constants, all depending only on `(Cd, R₀)`
  obtain ⟨a, A, ha, hA, hpart⟩ := lemma4_plane_quant Cd (15 * R₀) 12 (by norm_num)
  obtain ⟨Bk₀, hfar⟩ := nodes_far_of_color_plane Cd (15 * R₀) a A (6 * A) ha hA (by positivity)
  set B := max Bk₀ 0 / A with hB_def
  have hB : 0 ≤ B := div_nonneg (le_max_right _ _) hA.le
  have hBA : Bk₀ ≤ B * A := by
    rw [hB_def, div_mul_cancel₀ _ hA.ne']; exact le_max_left _ _
  obtain ⟨L₀, hL₀⟩ := hfar (B * A) ((B + 12) * A) hBA
  obtain ⟨c₅, hc₅, hfarL⟩ := hL₀ L₀ le_rfl
  obtain ⟨n, hcolor⟩ := exists_separated_coloring_plane Cd (15 * R₀) a A L₀ ha
  obtain ⟨M, C, hM, hC, hmult⟩ :=
    multiplier_of_nodes_plane Cd R₀ a A ((B + 12) * A) 12 hR₀ ha hA (by positivity)
      (by norm_num)
  obtain ⟨C1, hC1, hcl1⟩ := claim1_plane_quant Cd (15 * R₀) 1
  obtain ⟨C1', hC1', hcl1'⟩ := claim1_plane_quant Cd R₀ 1
  obtain ⟨Cρ, -, hρν⟩ := massRadius_lapNorm_quant Cd R₀
  set K := max (C1 / c₅) 1 with hK_def
  have hK0 : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε := K⁻¹ with hε_def
  have hε : 0 < ε := inv_pos.2 hK0
  set c₆ := min (ε / C1') 1 with hc₆_def
  have hc₆ : 0 < c₆ := lt_min (div_pos hε (by linarith)) one_pos
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  obtain ⟨hCCP, hC2CP, hCPinv⟩ := Prop2.constP_spec hC M hc₆
  set CP : ℝ≥0 := Real.toNNReal (max ((C : ℝ) ^ 2) (C * c₆⁻¹ ^ M))
  refine ⟨n, M, CP, ε, hM, hC.trans hCCP, hε, fun ψ μ hw ↦ ?_⟩
  -- the cells of `ν = Δψ/2π`, their colouring, and the multipliers
  set ν := lapNorm μ with hν_def
  have hν : MeasClassPlane ν Cd (15 * R₀) := hw.meas.lapNorm
  obtain ⟨R, hR⟩ := hpart ν hν
  obtain ⟨c, hc⟩ := hR.exists_cells
  obtain ⟨col, hcol⟩ := hcolor ν 12 R c hν hc
  have hl : ∀ l : Fin n, ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∃ z₀, g z₀ ≠ 0) ∧
      Thm4BoundsPlane ψ μ g M C ∧ ∀ i, col i = l → ∀ z ∈ R i, ∀ w, g w = 0 →
        c₅ * massRadius ν z ≤ dist z w := by
    intro l
    let sel : ℕ → Bool := fun j ↦
      decide (colorSel dist (massRadius ν) R c col (6 * A + 2) l j)
    obtain ⟨Λ, hΛ, hfalse, htrue⟩ := exists_nodes_plane hc hA.le B hB sel
    obtain ⟨g, hgd, hzero, -, hb⟩ := hmult ψ μ hw R c (fun _ ↦ 3) Λ hc hΛ (fun _ ↦ le_rfl)
    have hfar' := hfarL ν 12 R c col l Λ hν hc hcol
      (fun j hj w hw ↦ hfalse j (by simp [sel, hj]) w hw)
      (fun j hj w hw ↦ ⟨htrue j (by simp [sel, hj]) w hw, hΛ.near j w hw⟩)
    obtain ⟨z₀, -, hz₀n⟩ := Prop2.exists_mem_disc_notMem_nodeSet Λ
    refine ⟨g, hgd, ⟨z₀, fun h0 ↦ hz₀n ((hzero z₀).1 h0)⟩, hb, ?_⟩
    intro i hi z hz w hw0
    obtain ⟨j, hj⟩ := (hzero w).1 hw0
    exact hfar' i hi z hz j w hj
  choose h hhd hh0 hhb hhfar using hl
  have hupper : ∀ l, ∀ z, ‖h l z‖ ≤ (C : ℝ) ^ 2 * Real.exp (ψ z) := fun l z ↦
    Prop2.upper_of_bounds (norm_nonneg _) (hhb l z).2.1 (hhb l z).2.2
  refine ⟨h, hhd, hh0, fun l ↦ Prop2.thm4BoundsPlane_mono hC0 hCCP (hhb l), ?_, ?_, ?_⟩
  · -- every point is good for the colour of its cell
    intro z
    have hz : z ∈ ⋃ i, R i := by rw [hc.iUnion_eq]; exact mem_univ z
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    refine ⟨col k, fun w hw0 ↦ ?_⟩
    have h5 := hhfar (col k) k rfl z hk w hw0
    have hd0 : 0 ≤ dist z w := dist_nonneg
    have hρw : massRadius μ w ≤ massRadius ν w := (hρν μ hw.meas w).1
    have hKd : massRadius ν w ≤ K * dist z w := by
      by_cases hcase : dist w z ≤ 1 * max (massRadius ν w) (massRadius ν z)
      · have h6 := (hcl1 ν hν w z).2.2 hcase
        have h7 : C1 * massRadius ν z ≤ C1 / c₅ * dist z w := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hc₅]
          nlinarith
        calc massRadius ν w ≤ C1 / c₅ * dist z w := h6.trans h7
          _ ≤ K * dist z w := mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
      · push Not at hcase
        rw [dist_comm] at hcase
        calc massRadius ν w ≤ dist z w :=
              (le_max_left _ _).trans (by simpa using hcase.le)
          _ ≤ K * dist z w := le_mul_of_one_le_left hd0 (le_max_right _ _)
    calc ε * massRadius μ w ≤ ε * (K * dist z w) :=
          mul_le_mul_of_nonneg_left (hρw.trans hKd) hε.le
      _ = dist z w := by rw [hε_def, ← mul_assoc, inv_mul_cancel₀ hK0.ne', one_mul]
  · -- the two-sided bound on the good set
    intro l z hgood
    have hρz : 0 < massRadius μ z := (hcl1' μ hw.meas z z).1
    have hD : ENNReal.ofReal (c₆ * massRadius μ z) ≤ edistSet z {w | h l w = 0} := by
      refine le_iInf₂ fun w hw0 ↦ ?_
      rw [edist_dist]
      refine ENNReal.ofReal_le_ofReal ?_
      have hεw := hgood w hw0
      by_cases hcase : dist z w ≤ 1 * max (massRadius μ z) (massRadius μ w)
      · have h6 := (hcl1' μ hw.meas z w).2.2 hcase
        have h7 : ε * massRadius μ z ≤ C1' * dist z w := by nlinarith
        calc c₆ * massRadius μ z ≤ ε / C1' * massRadius μ z :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) hρz.le
          _ ≤ dist z w := by
              rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; linarith
      · push Not at hcase
        calc c₆ * massRadius μ z ≤ 1 * massRadius μ z :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hρz.le
          _ ≤ dist z w := by
              rw [one_mul]; exact (le_max_left _ _).trans (by simpa using hcase.le)
    have hlow := Prop2.lower_of_bounds hρz hc₆.le hC0 (norm_nonneg _) hD (hhb l z).1
    refine ⟨le_trans ?_ hlow, (hupper l z).trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hCPinv (Real.exp_pos _).le
    · exact mul_le_mul_of_nonneg_right hC2CP (Real.exp_pos _).le
  · intro l z
    exact (hupper l z).trans (mul_le_mul_of_nonneg_right hC2CP (Real.exp_pos _).le)

/-- **Proposition 2, quantitative, full form (disc).** -/
theorem prop2_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ (n M : ℕ) (C : ℝ≥0) (ε : ℝ), 1 ≤ M ∧ 1 ≤ C ∧ 0 < ε ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassDisc ψ μ Cd R₀ →
      ∃ h : Fin n → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (h i) 𝔻) ∧ (∀ i, ∃ z₀ ∈ 𝔻, h i z₀ ≠ 0) ∧
        (∀ i, Thm4BoundsDisc ψ μ (h i) M C) ∧
        (∀ z ∈ 𝔻, ∃ i, ∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) ∧
        (∀ i, ∀ z ∈ 𝔻, (∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) →
          (C : ℝ)⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ ∧ ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
        (∀ i, ∀ z ∈ 𝔻, ‖h i z‖ ≤ C * Real.exp (ψ z)) := by
  classical
  -- constants, all depending only on `(Cd, R₀)`
  obtain ⟨a, A, ha, hA, hpart⟩ := lemma4_disc_quant Cd (15 * R₀) 12 (by norm_num)
  obtain ⟨Bl, hBl, hnodes⟩ := exists_nodes_disc A hA
  obtain ⟨Bk₀, hfar⟩ := nodes_far_of_color_disc Cd (15 * R₀) a A Bl ha hA hBl
  set B := max Bk₀ 0 / A with hB_def
  have hB : 0 ≤ B := div_nonneg (le_max_right _ _) hA.le
  have hBA : Bk₀ ≤ B * A := by
    rw [hB_def, div_mul_cancel₀ _ hA.ne']; exact le_max_left _ _
  obtain ⟨ρ₀, B', hρ₀, hB', hnodesB⟩ := hnodes B hB
  obtain ⟨L₀, hL₀⟩ := hfar (B * A) B' hBA
  obtain ⟨c₅, hc₅, hfarL⟩ := hL₀ L₀ le_rfl
  obtain ⟨n, hcolor⟩ := exists_separated_coloring_disc Cd (15 * R₀) a A L₀ ha
  obtain ⟨M, C, hM, hC, hmult⟩ :=
    multiplier_of_nodes_disc Cd R₀ a A B' ρ₀ 12 hR₀ ha hA hB' hρ₀ (by norm_num)
  obtain ⟨C1, hC1, hcl1⟩ := claim1_disc_quant Cd (15 * R₀) 1
  obtain ⟨C1', hC1', hcl1'⟩ := claim1_disc_quant Cd R₀ 1
  obtain ⟨Cρ, -, hρν⟩ := massRadiusDisc_lapNorm_quant Cd R₀
  set K := max (C1 / c₅) 1 with hK_def
  have hK0 : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε := K⁻¹ with hε_def
  have hε : 0 < ε := inv_pos.2 hK0
  set c₆ := min (ε / C1') 1 with hc₆_def
  have hc₆ : 0 < c₆ := lt_min (div_pos hε (by linarith)) one_pos
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  obtain ⟨hCCP, hC2CP, hCPinv⟩ := Prop2.constP_spec hC M hc₆
  set CP : ℝ≥0 := Real.toNNReal (max ((C : ℝ) ^ 2) (C * c₆⁻¹ ^ M))
  refine ⟨n, M, CP, ε, hM, hC.trans hCCP, hε, fun ψ μ hw ↦ ?_⟩
  -- the cells of `ν = Δψ/2π`, their colouring, and the multipliers
  set ν := lapNorm μ with hν_def
  have hν : MeasClassDisc ν Cd (15 * R₀) := hw.meas.lapNorm
  obtain ⟨R, hR⟩ := hpart ν hν
  obtain ⟨c, hc⟩ := hR.exists_cells
  obtain ⟨col, hcol⟩ := hcolor ν 12 R c hν hc
  have hRΩ : ∀ i, R i ⊆ 𝔻 := fun i ↦ hc.iUnion_eq ▸ subset_iUnion R i
  have hcD : ∀ i, c i ∈ 𝔻 := fun i ↦ hRΩ i (hc.center_mem i)
  have hρpos : ∀ i, 0 < massRadiusDisc ν (c i) := fun i ↦ (hcl1 ν hν _ (hcD i) _ (hcD i)).1
  have hl : ∀ l : Fin n, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g 𝔻 ∧ (∃ z₀ ∈ 𝔻, g z₀ ≠ 0) ∧
      Thm4BoundsDisc ψ μ g M C ∧ ∀ i, col i = l → ∀ z ∈ R i, ∀ w ∈ 𝔻, g w = 0 →
        c₅ * massRadiusDisc ν z ≤ hypDist z w := by
    intro l
    let sel : ℕ → Bool := fun j ↦
      decide (colorSel hypDist (massRadiusDisc ν) R c col (Bl + 2) l j)
    obtain ⟨m, Λ, hΛ, hm2, hm3, hfalse, htrue⟩ := hnodesB ν a R c hc hρpos sel
    obtain ⟨g, hgd, hzero, -, hb⟩ := hmult ψ μ hw R c m Λ hc hΛ hm2 hm3
    have hfar' := hfarL ν 12 R c col l Λ hν hc hΛ.mem hcol
      (fun j hj w hw ↦ hfalse j (by simp [sel, hj]) w hw)
      (fun j hj w hw ↦ ⟨htrue j (by simp [sel, hj]) w hw, hΛ.near j w hw⟩)
    obtain ⟨z₀, hz₀, hz₀n⟩ := Prop2.exists_mem_disc_notMem_nodeSet Λ
    refine ⟨g, hgd, ⟨z₀, hz₀, fun h0 ↦ hz₀n ((hzero z₀ hz₀).1 h0)⟩, hb, ?_⟩
    intro i hi z hz w hwD hw0
    obtain ⟨j, hj⟩ := (hzero w hwD).1 hw0
    exact hfar' i hi z hz j w hj
  choose h hhd hh0 hhb hhfar using hl
  have hupper : ∀ l, ∀ z ∈ 𝔻, ‖h l z‖ ≤ (C : ℝ) ^ 2 * Real.exp (ψ z) := fun l z hz ↦
    Prop2.upper_of_bounds (norm_nonneg _) (hhb l z hz).2.1 (hhb l z hz).2.2
  refine ⟨h, hhd, hh0, fun l ↦ Prop2.thm4BoundsDisc_mono hC0 hCCP (hhb l), ?_, ?_, ?_⟩
  · -- every point is good for the colour of its cell
    intro z hz
    rw [← hc.iUnion_eq] at hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    have hzD := hRΩ k hk
    refine ⟨col k, fun w hwD hw0 ↦ ?_⟩
    have h5 := hhfar (col k) k rfl z hk w hwD hw0
    have hd0 : 0 ≤ hypDist z w := hypDist_nonneg z w
    have hρw : massRadiusDisc μ w ≤ massRadiusDisc ν w := (hρν μ hw.meas w hwD).1
    have hKd : massRadiusDisc ν w ≤ K * hypDist z w := by
      by_cases hcase : hypDist w z ≤ 1 * max (massRadiusDisc ν w) (massRadiusDisc ν z)
      · have h6 := (hcl1 ν hν w hwD z hzD).2.2 hcase
        have h7 : C1 * massRadiusDisc ν z ≤ C1 / c₅ * hypDist z w := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hc₅]
          nlinarith
        calc massRadiusDisc ν w ≤ C1 / c₅ * hypDist z w := h6.trans h7
          _ ≤ K * hypDist z w := mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
      · push Not at hcase
        rw [hypDist_comm] at hcase
        calc massRadiusDisc ν w ≤ hypDist z w :=
              (le_max_left _ _).trans (by simpa using hcase.le)
          _ ≤ K * hypDist z w := le_mul_of_one_le_left hd0 (le_max_right _ _)
    calc ε * massRadiusDisc μ w ≤ ε * (K * hypDist z w) :=
          mul_le_mul_of_nonneg_left (hρw.trans hKd) hε.le
      _ = hypDist z w := by rw [hε_def, ← mul_assoc, inv_mul_cancel₀ hK0.ne', one_mul]
  · -- the two-sided bound on the good set
    intro l z hz hgood
    have hρz : 0 < massRadiusDisc μ z := (hcl1' μ hw.meas z hz z hz).1
    have hD : ENNReal.ofReal (c₆ * massRadiusDisc μ z) ≤
        hypDistSet z {w | w ∈ 𝔻 ∧ h l w = 0} := by
      refine le_iInf₂ fun w hw ↦ ENNReal.ofReal_le_ofReal ?_
      obtain ⟨hwD, hw0⟩ := hw
      have hεw := hgood w hwD hw0
      by_cases hcase : hypDist z w ≤ 1 * max (massRadiusDisc μ z) (massRadiusDisc μ w)
      · have h6 := (hcl1' μ hw.meas z hz w hwD).2.2 hcase
        have h7 : ε * massRadiusDisc μ z ≤ C1' * hypDist z w := by nlinarith
        calc c₆ * massRadiusDisc μ z ≤ ε / C1' * massRadiusDisc μ z :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) hρz.le
          _ ≤ hypDist z w := by
              rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; linarith
      · push Not at hcase
        calc c₆ * massRadiusDisc μ z ≤ 1 * massRadiusDisc μ z :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hρz.le
          _ ≤ hypDist z w := by
              rw [one_mul]; exact (le_max_left _ _).trans (by simpa using hcase.le)
    have hlow := Prop2.lower_of_bounds hρz hc₆.le hC0 (norm_nonneg _) hD (hhb l z hz).1
    refine ⟨le_trans ?_ hlow, (hupper l z hz).trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hCPinv (Real.exp_pos _).le
    · exact mul_le_mul_of_nonneg_right hC2CP (Real.exp_pos _).le
  · intro l z hz
    exact (hupper l z hz).trans (mul_le_mul_of_nonneg_right hC2CP (Real.exp_pos _).le)

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
      ∀ z ∈ S, ∃! i, z ∈ Ω i := by
  classical
  refine ⟨fun i ↦ (G i ∩ S) \ ⋃ j, ⋃ (_ : j < i), G j, fun i ↦ ?_, fun i ↦ sdiff_subset, ?_⟩
  · exact ((hG i).inter hS).diff (MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun _ ↦ hG j)
  · intro z hz
    obtain ⟨i₀, hi₀⟩ := hcov z hz
    have hne : (Finset.univ.filter fun i ↦ z ∈ G i).Nonempty := ⟨i₀, by simp [hi₀]⟩
    set i := (Finset.univ.filter fun i ↦ z ∈ G i).min' hne with hi_def
    have hiG : z ∈ G i := by
      have := Finset.min'_mem _ hne
      simpa using this
    have hmin : ∀ j, z ∈ G j → i ≤ j := fun j hj ↦ Finset.min'_le _ _ (by simp [hj])
    refine ⟨i, ⟨⟨hiG, hz⟩, ?_⟩, ?_⟩
    · simp only [mem_iUnion, not_exists]
      exact fun j hji hj ↦ absurd (hmin j hj) (not_le.2 hji)
    · rintro j ⟨⟨hjG, -⟩, hj⟩
      simp only [mem_iUnion, not_exists] at hj
      rcases lt_trichotomy i j with h | h | h
      · exact absurd hiG (hj i h)
      · exact h.symm
      · exact absurd (hmin j hjG) (not_le.2 h)

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
