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
