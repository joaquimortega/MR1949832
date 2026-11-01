import OrtegaCerdaMultipliers.Multiplier.Basic
import OrtegaCerdaMultipliers.Multiplier.Defs
import OrtegaCerdaMultipliers.Partition.Lemma4

/-!
# M08 (Multiplier) — Geometry of cells and nodes

See `blueprint/M08_Multiplier.md` §2.3, §3.3.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- From M05's partition to cells (`c i` = centre of the inner ball). -/
theorem IsMassPartition.exists_cells {ν : Measure ℂ} {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    {N : ℕ} {a A : ℝ} {R : ℕ → Set ℂ} (hP : IsMassPartition ν Ω d ρ N a A R) :
    ∃ c : ℕ → ℂ, IsCells Ω d ρ ν N a A R c := by
  choose c hc hin using hP.inner
  exact ⟨c, hP.measurableSet, hP.pairwise_disjoint, hP.iUnion_eq, hc,
    fun i w hw ↦ hP.dist_le i (c i) (hc i) w hw, hin, hP.measure_eq⟩

/-! ### Elementary facts on cells -/

theorem IsCells.subset_univ {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {η A : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells Ω d ρ ν N η A R c) (i : ℕ) :
    R i ⊆ Ω := by
  rw [← hC.iUnion_eq]; exact subset_iUnion R i

theorem IsCells.center_mem' {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {η A : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells Ω d ρ ν N η A R c) (i : ℕ) :
    c i ∈ Ω :=
  hC.subset_univ i (hC.center_mem i)

theorem IsCells.measure_lt_top {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {η A : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells Ω d ρ ν N η A R c) (i : ℕ) :
    ν (R i) < ∞ := by
  rw [hC.measure_eq i]; exact ENNReal.natCast_lt_top N

theorem IsCells.isBounded_plane {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells univ dist ρ ν N η A R c) (i : ℕ) :
    Bornology.IsBounded (R i) :=
  (isBounded_closedBall (x := c i) (r := A * ρ (c i))).subset fun w hw ↦ by
    rw [mem_closedBall, dist_comm]; exact hC.subset i w hw

theorem IsCells.isBounded_disc {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells 𝔻 hypDist ρ ν N η A R c) (i : ℕ) :
    Bornology.IsBounded (R i) :=
  isBounded_ball.subset (hC.subset_univ i)

theorem IsCells.mono_A {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {η A A' : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells Ω d ρ ν N η A R c)
    (hρ : ∀ i, 0 ≤ ρ (c i)) (hA : A ≤ A') : IsCells Ω d ρ ν N η A' R c :=
  ⟨hC.measurableSet, hC.pairwise_disjoint, hC.iUnion_eq, hC.center_mem,
    fun i w hw ↦ (hC.subset i w hw).trans (mul_le_mul_of_nonneg_right hA (hρ i)), hC.inner,
    hC.measure_eq⟩

theorem IsNodes.mono_B {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {B B' : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hN : IsNodes Ω d ρ ν N B R c m Λ) (hρ : ∀ i, 0 ≤ ρ (c i)) (hB : B ≤ B') :
    IsNodes Ω d ρ ν N B' R c m Λ :=
  ⟨hN.card, hN.mem,
    fun i w hw ↦ (hN.near i w hw).trans (mul_le_mul_of_nonneg_right hB (hρ i)), hN.moments⟩

/-! ### Elementary consequences of the cell axioms -/

/-- A point at prescribed hyperbolic distance from `c`. -/
theorem exists_hypDist_eq {c : ℂ} (hc : c ∈ 𝔻) {t : ℝ} (ht : 0 ≤ t) :
    ∃ w ∈ 𝔻, hypDist c w = t := by
  have hu : ((Real.tanh t : ℝ) : ℂ) ∈ 𝔻 := by
    rw [mem_disc_iff_norm_lt_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tanh_nonneg_of_nonneg ht)]
    exact Real.tanh_lt_one t
  refine ⟨mobius c (Real.tanh t), mobius_mem_disc hc hu, ?_⟩
  have h0 : (0 : ℂ) ∈ 𝔻 := mem_ball_self one_pos
  have e : hypDist c (mobius c (Real.tanh t)) =
      hypDist (mobius c 0) (mobius c (Real.tanh t)) := by rw [mobius_zero]
  rw [e, hypDist_mobius hc h0 hu, hypDist_zero_left, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tanh_nonneg_of_nonneg ht), Real.artanh_tanh]

theorem IsCells.half_le_A_disc {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells 𝔻 hypDist ρ ν N η A R c) {i : ℕ}
    (hρ : 0 < ρ (c i)) (hη : 0 < η) : η / 2 ≤ A := by
  have hc : c i ∈ 𝔻 := by rw [← hC.iUnion_eq]; exact mem_iUnion.2 ⟨i, hC.center_mem i⟩
  obtain ⟨w, hw, hdw⟩ := exists_hypDist_eq hc (t := η * ρ (c i) / 2) (by positivity)
  have hwR : w ∈ R i := hC.inner i ⟨hw, by rw [hdw]; linarith [mul_pos hη hρ]⟩
  have := hC.subset i w hwR
  rw [hdw] at this
  nlinarith

theorem IsCells.half_le_A_plane {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells univ dist ρ ν N η A R c) {i : ℕ}
    (hρ : 0 < ρ (c i)) (hη : 0 < η) : η / 2 ≤ A := by
  set w : ℂ := c i + ((η * ρ (c i) / 2 : ℝ) : ℂ)
  have hdw : dist (c i) w = η * ρ (c i) / 2 := by
    simp only [w, dist_eq_norm, sub_add_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hwR : w ∈ R i := hC.inner i ⟨mem_univ _, by rw [hdw]; linarith [mul_pos hη hρ]⟩
  have := hC.subset i w hwR
  rw [hdw] at this
  nlinarith

theorem IsNodes.B_nonneg {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {B : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hN : IsNodes Ω d ρ ν N B R c m Λ) (hd : ∀ x y, 0 ≤ d x y) (hN1 : 1 ≤ N) {i : ℕ}
    (hρ : 0 < ρ (c i)) : 0 ≤ B := by
  have : 0 < Multiset.card (Λ i) := by rw [hN.card i]; omega
  obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.1 this
  have := (hd _ _).trans (hN.near i w hw)
  nlinarith

/-! ### Claim 1 consequences -/

/-- (C4) for the disc: a non-near cell is at distance `≥ δ ρ(z)` from `z`. -/
theorem claim1_nonNear_disc (Cd : ℝ≥0) (R₀ K₀ : ℝ) (hK₀ : 0 < K₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ w ∈ 𝔻,
      K₀ * massRadiusDisc ν w ≤ hypDist z w → δ * massRadiusDisc ν z ≤ hypDist z w := by
  obtain ⟨C₁, hC₁, hcl⟩ := claim1_disc_quant Cd R₀ K₀
  refine ⟨min (min 1 K₀) (K₀ / C₁), lt_min (lt_min one_pos hK₀) (by positivity),
    (min_le_left _ _).trans (min_le_left _ _), ?_⟩
  intro ν hν z hz w hw hK
  by_contra hlt
  push Not at hlt
  obtain ⟨hρz, -, h1⟩ := hcl ν hν z hz w hw
  have hlt1 : hypDist z w < massRadiusDisc ν z :=
    hlt.trans_le (by nlinarith [min_le_left (min 1 K₀) (K₀ / C₁), min_le_left 1 K₀])
  have hlt2 : hypDist z w < K₀ * massRadiusDisc ν z :=
    hlt.trans_le (by nlinarith [min_le_left (min 1 K₀) (K₀ / C₁), min_le_right 1 K₀])
  have hle : hypDist z w ≤ K₀ * max (massRadiusDisc ν z) (massRadiusDisc ν w) :=
    hlt2.le.trans (by nlinarith [le_max_left (massRadiusDisc ν z) (massRadiusDisc ν w)])
  have h2 := h1 hle
  have h3 : K₀ / C₁ * massRadiusDisc ν z ≤ hypDist z w := by
    calc K₀ / C₁ * massRadiusDisc ν z ≤ K₀ / C₁ * (C₁ * massRadiusDisc ν w) := by gcongr
      _ = K₀ * massRadiusDisc ν w := by field_simp
      _ ≤ hypDist z w := hK
  have h4 : min (min 1 K₀) (K₀ / C₁) * massRadiusDisc ν z ≤ K₀ / C₁ * massRadiusDisc ν z :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hρz.le
  linarith

/-- (C4) for the plane. -/
theorem claim1_nonNear_plane (Cd : ℝ≥0) (R₀ K₀ : ℝ) (hK₀ : 0 < K₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z w : ℂ,
      K₀ * massRadius ν w ≤ dist z w → δ * massRadius ν z ≤ dist z w := by
  obtain ⟨C₁, hC₁, hcl⟩ := claim1_plane_quant Cd R₀ K₀
  refine ⟨min (min 1 K₀) (K₀ / C₁), lt_min (lt_min one_pos hK₀) (by positivity),
    (min_le_left _ _).trans (min_le_left _ _), ?_⟩
  intro ν hν z w hK
  by_contra hlt
  push Not at hlt
  obtain ⟨hρz, -, h1⟩ := hcl ν hν z w
  have hlt1 : dist z w < massRadius ν z :=
    hlt.trans_le (by nlinarith [min_le_left (min 1 K₀) (K₀ / C₁), min_le_left 1 K₀])
  have hlt2 : dist z w < K₀ * massRadius ν z :=
    hlt.trans_le (by nlinarith [min_le_left (min 1 K₀) (K₀ / C₁), min_le_right 1 K₀])
  have hle : dist z w ≤ K₀ * max (massRadius ν z) (massRadius ν w) :=
    hlt2.le.trans (by nlinarith [le_max_left (massRadius ν z) (massRadius ν w)])
  have h2 := h1 hle
  have h3 : K₀ / C₁ * massRadius ν z ≤ dist z w := by
    calc K₀ / C₁ * massRadius ν z ≤ K₀ / C₁ * (C₁ * massRadius ν w) := by gcongr
      _ = K₀ * massRadius ν w := by field_simp
      _ ≤ dist z w := hK
  have h4 : min (min 1 K₀) (K₀ / C₁) * massRadius ν z ≤ K₀ / C₁ * massRadius ν z :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hρz.le
  linarith

/-- Bounded number of near cells, near/far dichotomy for nodes (plane). -/
theorem cells_near_plane (Cd : ℝ≥0) (R₀ η A B K₀ : ℝ) (hη : 0 < η) (hK₀ : 2 * (A + B) ≤ K₀) :
    ∃ (Mc : ℕ) (δ C₃ : ℝ), 0 < δ ∧ 0 < C₃ ∧ ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ)
      (c : ℕ → ℂ) (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassPlane ν Cd R₀ → 1 ≤ N →
      IsCells univ dist (massRadius ν) ν N η A R c →
      IsNodes univ dist (massRadius ν) ν N B R c m Λ → ∀ z : ℂ,
        {i | dist z (c i) < K₀ * massRadius ν (c i)}.encard ≤ Mc ∧
        (∀ i, dist z (c i) < K₀ * massRadius ν (c i) →
          ∀ w ∈ R i ∪ {w | w ∈ Λ i}, dist z w ≤ C₃ * massRadius ν z) ∧
        (∀ i, K₀ * massRadius ν (c i) ≤ dist z (c i) →
          δ * massRadius ν z ≤ dist z (c i) ∧ ∀ w ∈ Λ i, δ * massRadius ν z ≤ 2 * dist z w) ∧
        (∃ i, z ∈ R i ∧ dist z (c i) < K₀ * massRadius ν (c i)) := by
  set K₁ := max K₀ η with hK₁
  have hK₁pos : 0 < K₁ := lt_of_lt_of_le hη (le_max_right _ _)
  obtain ⟨C₁, hC₁, hcl⟩ := claim1_plane_quant Cd R₀ K₁
  obtain ⟨δ, hδ, -, hδK⟩ := claim1_nonNear_plane Cd R₀ K₁ hK₁pos
  set Kb := K₁ * C₁ + η with hKbdef
  have hKb : 0 < Kb := by positivity
  set Mc : ℕ := ⌈(Kb * C₁ / η) ^ 2⌉₊ with hMc
  refine ⟨Mc, δ, (K₁ + |A| + |B|) * C₁, hδ, by positivity, ?_⟩
  intro ν N R c m Λ hν hN1 hC hN z
  have hρ : ∀ w, 0 < massRadius ν w := fun w ↦ (hcl ν hν w w).1
  have hρz := hρ z
  have hA : η / 2 ≤ A := hC.half_le_A_plane (i := 0) (hρ _) hη
  have hB : 0 ≤ B := hN.B_nonneg (fun _ _ ↦ dist_nonneg) hN1 (i := 0) (hρ _)
  have hK₀η : η ≤ K₀ := by linarith
  have hK₁eq : K₁ = K₀ := max_eq_left hK₀η
  have hcomp : ∀ i, dist z (c i) < K₀ * massRadius ν (c i) →
      massRadius ν z ≤ C₁ * massRadius ν (c i) ∧
        massRadius ν (c i) ≤ C₁ * massRadius ν z := by
    intro i hi
    have hle : dist z (c i) ≤ K₁ * max (massRadius ν z) (massRadius ν (c i)) := by
      rw [hK₁eq]
      exact hi.le.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith))
    refine ⟨(hcl ν hν z (c i)).2.2 hle, (hcl ν hν (c i) z).2.2 ?_⟩
    rw [dist_comm, max_comm]; exact hle
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine encard_le_of_forall_finset fun F hF ↦ ?_
    set a := η * massRadius ν z / C₁ with ha
    set b := Kb * massRadius ν z with hb
    have ha0 : 0 < a := by positivity
    have hab : ∀ i ∈ F, ball (c i) a ⊆ ball z b := by
      intro i hi w hw
      have hiF := hF hi
      obtain ⟨h1, h2⟩ := hcomp i hiF
      rw [mem_ball] at hw ⊢
      have htri := dist_triangle w (c i) z
      have : dist (c i) z < K₁ * C₁ * massRadius ν z := by
        rw [hK₁eq, dist_comm]
        calc dist z (c i) < K₀ * massRadius ν (c i) := hiF
          _ ≤ K₀ * (C₁ * massRadius ν z) := mul_le_mul_of_nonneg_left h2 (by linarith)
          _ = K₀ * C₁ * massRadius ν z := by ring
      have ha' : a ≤ η * massRadius ν z := by
        rw [ha]; exact div_le_self (by positivity) hC₁
      calc dist w z ≤ dist w (c i) + dist (c i) z := htri
        _ < a + K₁ * C₁ * massRadius ν z := by linarith
        _ ≤ b := by rw [hb, hKbdef]; nlinarith
    have hsub : ∀ i ∈ F, ball (c i) a ⊆ R i := by
      intro i hi w hw
      obtain ⟨h1, -⟩ := hcomp i (hF hi)
      refine hC.inner i ⟨mem_univ _, ?_⟩
      rw [dist_comm]
      refine (mem_ball.1 hw).trans_le ?_
      rw [ha, div_le_iff₀ (by linarith), mul_assoc, mul_comm (massRadius ν (c i))]
      exact mul_le_mul_of_nonneg_left (by linarith) hη.le
    have hdisj : (F : Set ℕ).PairwiseDisjoint fun i ↦ ball (c i) a := by
      intro i _ j _ hij
      exact (hC.pairwise_disjoint hij).mono (hsub i ‹_›) (hsub j ‹_›)
    have hcount := sum_le_of_pairwiseDisjoint (μ := volume) (E := fun i ↦ ball (c i) a)
      (U := ball z b) (f := fun _ ↦ Real.pi * a ^ 2)
      (V := Real.pi * b ^ 2) (fun i _ ↦ isOpen_ball.measurableSet) hdisj hab
      (fun i _ ↦ by positivity) (fun i _ ↦ by
        rw [Complex.volume_ball, ← ENNReal.ofReal_pow ha0.le, ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_mul (by positivity)]
        simp [mul_comm])
      (by positivity) (by
        rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_mul (by positivity)]
        simp [mul_comm])
    rw [Finset.sum_const, nsmul_eq_mul] at hcount
    have hba : b / a = Kb * C₁ / η := by rw [hb, ha]; field_simp
    have hcard : (F.card : ℝ) ≤ (Kb * C₁ / η) ^ 2 := by
      rw [← hba, div_pow, le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    exact_mod_cast hcard.trans (Nat.le_ceil _)
  · intro i hi w hw
    obtain ⟨-, h2⟩ := hcomp i hi
    have hcw : dist (c i) w ≤ (|A| + |B|) * massRadius ν (c i) := by
      rcases hw with hw | hw
      · exact (hC.subset i w hw).trans (mul_le_mul_of_nonneg_right
          ((le_abs_self A).trans (le_add_of_nonneg_right (abs_nonneg B))) (hρ _).le)
      · exact (hN.near i w hw).trans (mul_le_mul_of_nonneg_right
          ((le_abs_self B).trans (le_add_of_nonneg_left (abs_nonneg A))) (hρ _).le)
    calc dist z w ≤ dist z (c i) + dist (c i) w := dist_triangle _ _ _
      _ ≤ K₀ * massRadius ν (c i) + (|A| + |B|) * massRadius ν (c i) := by linarith
      _ = (K₁ + |A| + |B|) * massRadius ν (c i) := by rw [hK₁eq]; ring
      _ ≤ (K₁ + |A| + |B|) * (C₁ * massRadius ν z) := by gcongr
      _ = (K₁ + |A| + |B|) * C₁ * massRadius ν z := by ring
  · intro i hi
    have hi' : K₁ * massRadius ν (c i) ≤ dist z (c i) := by rw [hK₁eq]; exact hi
    refine ⟨hδK ν hν z (c i) hi', fun w hw ↦ ?_⟩
    have h1 := hδK ν hν z (c i) hi'
    have htri' : dist z (c i) ≤ dist z w + dist w (c i) := dist_triangle _ _ _
    rw [dist_comm w] at htri'
    have hnear := hN.near i w hw
    have hBK : B * massRadius ν (c i) ≤ K₀ / 2 * massRadius ν (c i) :=
      mul_le_mul_of_nonneg_right (by linarith) (hρ _).le
    nlinarith
  · have hz' : z ∈ ⋃ i, R i := by rw [hC.iUnion_eq]; exact mem_univ z
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz'
    refine ⟨i, hi, ?_⟩
    rw [dist_comm]
    calc dist (c i) z ≤ A * massRadius ν (c i) := hC.subset i z hi
      _ < K₀ * massRadius ν (c i) := by
          apply mul_lt_mul_of_pos_right _ (hρ _); linarith

/-- Local finiteness: a bounded set meets only finitely many enlarged cells. -/
theorem finite_cells_plane {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hν : MeasClassPlane ν Cd R₀) (hη : 0 < η)
    (hC : IsCells univ dist (massRadius ν) ν N η A R c) (K : Set ℂ)
    (hK : Bornology.IsBounded K) (L : ℝ) :
    {i | ∃ z ∈ K, dist z (c i) < L}.Finite := by
  obtain ⟨r, hr⟩ := hK.subset_closedBall 0
  set D := |r| + |L| with hD
  obtain ⟨C0, -, hcl0⟩ := claim1_plane_quant Cd R₀ 0
  have hρ0 : 0 < massRadius ν 0 := (hcl0 ν hν 0 0).1
  set Kc := D / massRadius ν 0 + 1 with hKc
  obtain ⟨C, hC1, hcl⟩ := claim1_plane_quant Cd R₀ Kc
  have hdist : ∀ i ∈ {i | ∃ z ∈ K, dist z (c i) < L}, dist 0 (c i) ≤ D := by
    rintro i ⟨z, hzK, hz⟩
    have h1 := dist_triangle 0 z (c i)
    have h2 : dist 0 z ≤ r := by rw [dist_comm]; exact hr hzK
    have := le_abs_self r
    have := le_abs_self L
    linarith
  have hρi : ∀ i ∈ {i | ∃ z ∈ K, dist z (c i) < L},
      massRadius ν 0 ≤ C * massRadius ν (c i) := by
    intro i hi
    refine (hcl ν hν 0 (c i)).2.2 ((hdist i hi).trans ?_)
    calc D ≤ Kc * massRadius ν 0 := by rw [hKc]; field_simp; linarith
      _ ≤ Kc * max (massRadius ν 0) (massRadius ν (c i)) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  set a := η * massRadius ν 0 / C with ha
  have ha0 : 0 < a := by positivity
  refine Set.finite_of_encard_le_coe (k := ⌈(D + a) ^ 2 / a ^ 2⌉₊) ?_
  refine encard_le_of_forall_finset fun F hF ↦ ?_
  have hsub : ∀ i ∈ F, ball (c i) a ⊆ R i := by
    intro i hi w hw
    have h1 := hρi i (hF hi)
    refine hC.inner i ⟨mem_univ _, ?_⟩
    rw [dist_comm]
    refine (mem_ball.1 hw).trans_le ?_
    rw [ha, div_le_iff₀ (by linarith)]
    nlinarith
  have hab : ∀ i ∈ F, ball (c i) a ⊆ ball 0 (D + a) := by
    intro i hi w hw
    rw [mem_ball] at hw ⊢
    have := dist_triangle w (c i) 0
    have := hdist i (hF hi)
    rw [dist_comm 0] at this
    linarith
  have hdisj : (F : Set ℕ).PairwiseDisjoint fun i ↦ ball (c i) a := by
    intro i hi j hj hij
    exact (hC.pairwise_disjoint hij).mono (hsub i hi) (hsub j hj)
  have hcount := sum_le_of_pairwiseDisjoint (μ := volume) (E := fun i ↦ ball (c i) a)
    (U := ball 0 (D + a)) (f := fun _ ↦ Real.pi * a ^ 2)
    (V := Real.pi * (D + a) ^ 2) (fun i _ ↦ isOpen_ball.measurableSet)
    hdisj hab (fun i _ ↦ by positivity) (fun i _ ↦ by
      rw [Complex.volume_ball, ← ENNReal.ofReal_pow ha0.le, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (by positivity)]
      simp [mul_comm])
    (by positivity) (by
      rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (by positivity)]
      simp [mul_comm])
  rw [Finset.sum_const, nsmul_eq_mul] at hcount
  have : (F.card : ℝ) ≤ (D + a) ^ 2 / a ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  exact_mod_cast this.trans (Nat.le_ceil _)

/-- Bounded number of near cells, near/far dichotomy for nodes (disc). -/
theorem cells_near_disc (Cd : ℝ≥0) (R₀ η A B K₀ : ℝ) (hη : 0 < η) (hK₀ : 2 * (A + B) ≤ K₀) :
    ∃ (Mc : ℕ) (δ C₃ : ℝ), 0 < δ ∧ 0 < C₃ ∧ ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ)
      (c : ℕ → ℂ) (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassDisc ν Cd R₀ → 1 ≤ N →
      IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ → ∀ z ∈ 𝔻,
        {i | hypDist z (c i) < K₀ * massRadiusDisc ν (c i)}.encard ≤ Mc ∧
        (∀ i, hypDist z (c i) < K₀ * massRadiusDisc ν (c i) →
          ∀ w ∈ R i ∪ {w | w ∈ Λ i}, hypDist z w ≤ C₃ * massRadiusDisc ν z) ∧
        (∀ i, K₀ * massRadiusDisc ν (c i) ≤ hypDist z (c i) →
          δ * massRadiusDisc ν z ≤ hypDist z (c i) ∧
            ∀ w ∈ Λ i, δ * massRadiusDisc ν z ≤ 2 * hypDist z w) ∧
        (∃ i, z ∈ R i ∧ hypDist z (c i) < K₀ * massRadiusDisc ν (c i)) := by
  set K₁ := max K₀ η with hK₁
  have hK₁pos : 0 < K₁ := lt_of_lt_of_le hη (le_max_right _ _)
  obtain ⟨C₁, hC₁, hcl⟩ := claim1_disc_quant Cd R₀ K₁
  obtain ⟨δ, hδ, -, hδK⟩ := claim1_nonNear_disc Cd R₀ K₁ hK₁pos
  set Kb := K₁ * C₁ + η with hKbdef
  have hKb : 0 < Kb := by positivity
  set Mc : ℕ := ⌈(Kb * C₁ / η) ^ 2 * Real.exp (2 * Kb * max R₀ 0)⌉₊ with hMc
  refine ⟨Mc, δ, (K₁ + |A| + |B|) * C₁, hδ, by positivity, ?_⟩
  intro ν N R c m Λ hν hN1 hC hN z hz
  have hci := hC.center_mem'
  have hρ : ∀ w ∈ 𝔻, 0 < massRadiusDisc ν w := fun w hw ↦ (hcl ν hν w hw w hw).1
  have hρR : ∀ w ∈ 𝔻, massRadiusDisc ν w ≤ R₀ := fun w hw ↦ (hcl ν hν w hw w hw).2.1
  have hρz := hρ z hz
  have hA : η / 2 ≤ A := hC.half_le_A_disc (i := 0) (hρ _ (hci 0)) hη
  have hB : 0 ≤ B := hN.B_nonneg hypDist_nonneg hN1 (i := 0) (hρ _ (hci 0))
  have hK₀η : η ≤ K₀ := by linarith
  have hK₁eq : K₁ = K₀ := max_eq_left hK₀η
  -- comparability of radii for near cells
  have hcomp : ∀ i, hypDist z (c i) < K₀ * massRadiusDisc ν (c i) →
      massRadiusDisc ν z ≤ C₁ * massRadiusDisc ν (c i) ∧
        massRadiusDisc ν (c i) ≤ C₁ * massRadiusDisc ν z := by
    intro i hi
    have hle : hypDist z (c i) ≤ K₁ * max (massRadiusDisc ν z) (massRadiusDisc ν (c i)) := by
      rw [hK₁eq]
      exact hi.le.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith))
    refine ⟨(hcl ν hν z hz (c i) (hci i)).2.2 hle, (hcl ν hν (c i) (hci i) z hz).2.2 ?_⟩
    rw [hypDist_comm, max_comm]; exact hle
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (C2) bounded count, by hyperbolic area
    refine encard_le_of_forall_finset fun F hF ↦ ?_
    set a := η * massRadiusDisc ν z / C₁ with ha
    set b := Kb * massRadiusDisc ν z with hb
    have ha0 : 0 < a := by positivity
    have hab : ∀ i ∈ F, hypBall (c i) a ⊆ hypBall z b := by
      intro i hi w hw
      have hiF := hF hi
      obtain ⟨h1, h2⟩ := hcomp i hiF
      refine ⟨hw.1, ?_⟩
      have htri := hypDist_triangle hz (hci i) hw.1
      have : hypDist z (c i) < K₁ * C₁ * massRadiusDisc ν z := by
        rw [hK₁eq]
        calc hypDist z (c i) < K₀ * massRadiusDisc ν (c i) := hiF
          _ ≤ K₀ * (C₁ * massRadiusDisc ν z) := mul_le_mul_of_nonneg_left h2 (by linarith)
          _ = K₀ * C₁ * massRadiusDisc ν z := by ring
      have ha' : a ≤ η * massRadiusDisc ν z := by
        rw [ha]; exact div_le_self (by positivity) hC₁
      calc hypDist z w ≤ hypDist z (c i) + hypDist (c i) w := htri
        _ < K₁ * C₁ * massRadiusDisc ν z + a := by linarith [hw.2]
        _ ≤ b := by rw [hb, hKbdef]; nlinarith
    have hsub : ∀ i ∈ F, hypBall (c i) a ⊆ R i := by
      intro i hi w hw
      obtain ⟨h1, -⟩ := hcomp i (hF hi)
      refine hC.inner i ⟨hw.1, hw.2.trans_le ?_⟩
      rw [ha, div_le_iff₀ (by linarith), mul_assoc, mul_comm (massRadiusDisc ν (c i))]
      exact mul_le_mul_of_nonneg_left (by linarith) hη.le
    have hdisj : (F : Set ℕ).PairwiseDisjoint fun i ↦ hypBall (c i) a := by
      intro i _ j _ hij
      exact (hC.pairwise_disjoint hij).mono (hsub i ‹_›) (hsub j ‹_›)
    have hcount := sum_le_of_pairwiseDisjoint (μ := hypArea) (E := fun i ↦ hypBall (c i) a)
      (U := hypBall z b) (f := fun _ ↦ Real.pi * Real.sinh a ^ 2)
      (V := Real.pi * Real.sinh b ^ 2) (fun i _ ↦ (isOpen_hypBall _ _).measurableSet) hdisj hab
      (fun i _ ↦ by positivity) (fun i _ ↦ (hypArea_hypBall (hci i) ha0.le).ge) (by positivity)
      (hypArea_hypBall hz (by positivity)).le
    rw [Finset.sum_const, nsmul_eq_mul] at hcount
    have hsa : a ≤ Real.sinh a := Real.self_le_sinh_iff.2 ha0.le
    have hsb : Real.sinh b ≤ b * Real.exp b := sinh_le_mul_exp (by positivity)
    have hbR : b ≤ Kb * max R₀ 0 :=
      mul_le_mul_of_nonneg_left ((hρR z hz).trans (le_max_left _ _)) hKb.le
    have hcard : (F.card : ℝ) ≤ (Kb * C₁ / η) ^ 2 * Real.exp (2 * Kb * max R₀ 0) := by
      have hsa2 : 0 < Real.sinh a ^ 2 := by positivity
      have h1 : (F.card : ℝ) ≤ Real.sinh b ^ 2 / Real.sinh a ^ 2 := by
        rw [le_div_iff₀ hsa2]; nlinarith [Real.pi_pos]
      refine h1.trans ?_
      rw [div_le_iff₀ hsa2]
      have hexp : Real.exp b ^ 2 ≤ Real.exp (2 * Kb * max R₀ 0) := by
        rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; linarith)
      have hba : b / a = Kb * C₁ / η := by
        rw [hb, ha]; field_simp
      calc Real.sinh b ^ 2 ≤ (b * Real.exp b) ^ 2 := by
            gcongr
        _ = (b / a) ^ 2 * Real.exp b ^ 2 * a ^ 2 := by field_simp
        _ ≤ (Kb * C₁ / η) ^ 2 * Real.exp (2 * Kb * max R₀ 0) * Real.sinh a ^ 2 := by
            rw [hba]; gcongr
    have := hcard.trans (Nat.le_ceil _)
    exact_mod_cast this
  · -- (C3) points of near cells are close to `z`
    intro i hi w hw
    obtain ⟨-, h2⟩ := hcomp i hi
    have hcw : hypDist (c i) w ≤ (|A| + |B|) * massRadiusDisc ν (c i) := by
      rcases hw with hw | hw
      · exact (hC.subset i w hw).trans (mul_le_mul_of_nonneg_right
          ((le_abs_self A).trans (le_add_of_nonneg_right (abs_nonneg B))) (hρ _ (hci i)).le)
      · exact (hN.near i w hw).trans (mul_le_mul_of_nonneg_right
          ((le_abs_self B).trans (le_add_of_nonneg_left (abs_nonneg A))) (hρ _ (hci i)).le)
    have hw𝔻 : w ∈ 𝔻 := by
      rcases hw with hw | hw
      · exact hC.subset_univ i hw
      · exact hN.mem i w hw
    calc hypDist z w ≤ hypDist z (c i) + hypDist (c i) w := hypDist_triangle hz (hci i) hw𝔻
      _ ≤ K₀ * massRadiusDisc ν (c i) + (|A| + |B|) * massRadiusDisc ν (c i) := by
          linarith
      _ = (K₁ + |A| + |B|) * massRadiusDisc ν (c i) := by rw [hK₁eq]; ring
      _ ≤ (K₁ + |A| + |B|) * (C₁ * massRadiusDisc ν z) := by gcongr
      _ = (K₁ + |A| + |B|) * C₁ * massRadiusDisc ν z := by ring
  · -- (C4) non-near cells and their nodes are far
    intro i hi
    have hi' : K₁ * massRadiusDisc ν (c i) ≤ hypDist z (c i) := by rw [hK₁eq]; exact hi
    refine ⟨hδK ν hν z hz (c i) (hci i) hi', fun w hw ↦ ?_⟩
    have h1 := hδK ν hν z hz (c i) (hci i) hi'
    have hw𝔻 := hN.mem i w hw
    have htri' : hypDist z (c i) ≤ hypDist z w + hypDist w (c i) :=
      hypDist_triangle hz hw𝔻 (hci i)
    rw [hypDist_comm w] at htri'
    have hnear := hN.near i w hw
    have hBK : B * massRadiusDisc ν (c i) ≤ K₀ / 2 * massRadiusDisc ν (c i) :=
      mul_le_mul_of_nonneg_right (by linarith) (hρ _ (hci i)).le
    nlinarith
  · -- (C5) `z` lies in a near cell
    have hz' : z ∈ ⋃ i, R i := by rw [hC.iUnion_eq]; exact hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz'
    refine ⟨i, hi, ?_⟩
    rw [hypDist_comm]
    have hρi := hρ _ (hci i)
    calc hypDist (c i) z ≤ A * massRadiusDisc ν (c i) := hC.subset i z hi
      _ < K₀ * massRadiusDisc ν (c i) := by
          apply mul_lt_mul_of_pos_right _ hρi; linarith

/-- Local finiteness (disc): a compact subset of `𝔻` meets only finitely many enlarged cells. -/
theorem finite_cells_disc {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hν : MeasClassDisc ν Cd R₀) (hη : 0 < η)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c) (K : Set ℂ) (hK𝔻 : K ⊆ 𝔻)
    (hK : IsCompact K) (L : ℝ) :
    {i | ∃ z ∈ K, hypDist z (c i) < L}.Finite := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · simp [hKe]
  obtain ⟨x₀, hx₀K, hx₀max⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
  have h0 : (0 : ℂ) ∈ 𝔻 := mem_ball_self one_pos
  have hx₀1 : ‖x₀‖ < 1 := norm_lt_one_of_mem_disc (hK𝔻 hx₀K)
  set D := Real.artanh ‖x₀‖ + L with hD
  obtain ⟨C0, -, hcl0⟩ := claim1_disc_quant Cd R₀ 0
  have hρ0 : 0 < massRadiusDisc ν 0 := (hcl0 ν hν 0 h0 0 h0).1
  set Kc := |D| / massRadiusDisc ν 0 + 1 with hKc
  obtain ⟨C, hC1, hcl⟩ := claim1_disc_quant Cd R₀ Kc
  have hci := hC.center_mem'
  have hdist : ∀ i ∈ {i | ∃ z ∈ K, hypDist z (c i) < L}, hypDist 0 (c i) ≤ D := by
    rintro i ⟨z, hzK, hz⟩
    have hz𝔻 := hK𝔻 hzK
    have h1 := hypDist_triangle h0 hz𝔻 (hci i)
    have h1' := hypDist_zero_left z
    have h2 : Real.artanh ‖z‖ ≤ Real.artanh ‖x₀‖ :=
      Real.artanh_le_artanh (by linarith [norm_nonneg z]) hx₀1 (hx₀max hzK)
    linarith
  have hρi : ∀ i ∈ {i | ∃ z ∈ K, hypDist z (c i) < L},
      massRadiusDisc ν 0 ≤ C * massRadiusDisc ν (c i) := by
    intro i hi
    refine (hcl ν hν 0 h0 (c i) (hci i)).2.2 ((hdist i hi).trans ?_)
    calc D ≤ |D| := le_abs_self D
      _ ≤ Kc * massRadiusDisc ν 0 := by rw [hKc]; field_simp; linarith
      _ ≤ Kc * max (massRadiusDisc ν 0) (massRadiusDisc ν (c i)) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  set a := η * massRadiusDisc ν 0 / C with ha
  have ha0 : 0 < a := by positivity
  refine Set.finite_of_encard_le_coe (k := ⌈Real.sinh (|D| + a) ^ 2 / Real.sinh a ^ 2⌉₊) ?_
  refine encard_le_of_forall_finset fun F hF ↦ ?_
  have hsub : ∀ i ∈ F, hypBall (c i) a ⊆ R i := by
    intro i hi w hw
    have h1 := hρi i (hF hi)
    refine hC.inner i ⟨hw.1, hw.2.trans_le ?_⟩
    rw [ha, div_le_iff₀ (by linarith)]
    nlinarith
  have hab : ∀ i ∈ F, hypBall (c i) a ⊆ hypBall 0 (|D| + a) := by
    intro i hi w hw
    refine ⟨hw.1, ?_⟩
    have := hypDist_triangle h0 (hci i) hw.1
    have := hdist i (hF hi)
    have := le_abs_self D
    linarith [hw.2]
  have hdisj : (F : Set ℕ).PairwiseDisjoint fun i ↦ hypBall (c i) a := by
    intro i hi j hj hij
    exact (hC.pairwise_disjoint hij).mono (hsub i hi) (hsub j hj)
  have hcount := sum_le_of_pairwiseDisjoint (μ := hypArea) (E := fun i ↦ hypBall (c i) a)
    (U := hypBall 0 (|D| + a)) (f := fun _ ↦ Real.pi * Real.sinh a ^ 2)
    (V := Real.pi * Real.sinh (|D| + a) ^ 2) (fun i _ ↦ (isOpen_hypBall _ _).measurableSet)
    hdisj hab (fun i _ ↦ by positivity) (fun i _ ↦ (hypArea_hypBall (hci i) ha0.le).ge)
    (by positivity) (hypArea_hypBall h0 (by positivity)).le
  rw [Finset.sum_const, nsmul_eq_mul] at hcount
  have hsa : 0 < Real.sinh a := Real.sinh_pos_iff.2 ha0
  have : (F.card : ℝ) ≤ Real.sinh (|D| + a) ^ 2 / Real.sinh a ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  exact_mod_cast this.trans (Nat.le_ceil _)

end OC
