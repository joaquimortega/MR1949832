import OrtegaCerdaMultipliers.Partition.Lemma4

/-!
# M05 (Partition) — Claim 2 and the properties of the partitions used later

See `blueprint/M05_Partition.md` §2.4.  Proofs complete (they use the upstream M01/M03 interfaces).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

section PartitionProps
variable {μ : Measure ℂ} {N : ℕ} {a A : ℝ} {R : ℕ → Set ℂ}

/-! #### Helpers -/

theorem prop_massRadius_le {ν : Measure ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r) (h : 1 ≤ ν (ball z r)) :
    massRadius ν z ≤ r :=
  csInf_le ⟨0, fun _ hx ↦ hx.1.le⟩ ⟨hr, h⟩

theorem prop_massRadius_nonneg (ν : Measure ℂ) (z : ℂ) : 0 ≤ massRadius ν z :=
  Real.sInf_nonneg fun _ hx ↦ hx.1.le

theorem prop_massRadiusDisc_le {ν : Measure ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (h : 1 ≤ ν (hypBall z r)) : massRadiusDisc ν z ≤ r :=
  csInf_le ⟨0, fun _ hx ↦ hx.1.le⟩ ⟨hr, h⟩

theorem prop_massRadiusDisc_nonneg (ν : Measure ℂ) (z : ℂ) : 0 ≤ massRadiusDisc ν z :=
  Real.sInf_nonneg fun _ hx ↦ hx.1.le

theorem prop_massRadiusLine_le {ν : Measure ℂ} {x r : ℝ} (hr : 0 < r)
    (h : 1 ≤ ν (lineInterval x r)) : massRadiusLine ν x ≤ r :=
  csInf_le ⟨0, fun _ hx ↦ hx.1.le⟩ ⟨hr, h⟩

theorem prop_massRadiusLine_nonneg (ν : Measure ℂ) (x : ℝ) : 0 ≤ massRadiusLine ν x :=
  Real.sInf_nonneg fun _ hx ↦ hx.1.le

/-- `ρ ≤ r` as soon as every larger radius gives mass `≥ 1` (closed-ball form). -/
theorem prop_le_of_forall_gt {ρ r : ℝ} (h : ∀ r' : ℝ, r < r' → ρ ≤ r') : ρ ≤ r := by
  by_contra hlt
  push Not at hlt
  have := h ((r + ρ) / 2) (by linarith)
  linarith

theorem IsMassPartition.subset_of_mem {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) (i : ℕ) : R i ⊆ Ω := by
  rw [← hP.iUnion_eq]; exact subset_iUnion R i

theorem IsMassPartition.one_le_measure {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) (hN : 1 ≤ N) (i : ℕ) : 1 ≤ μ (R i) := by
  rw [hP.measure_eq]; exact_mod_cast hN

theorem IsMassPartition.nonempty {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) (hN : 1 ≤ N) (i : ℕ) : (R i).Nonempty :=
  nonempty_of_measure_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one (hP.one_le_measure hN i)))

/-- Counting disjoint pieces of mass `≥ 1` inside a set of bounded mass. -/
theorem prop_encard_le {ν : Measure ℂ} {R : ℕ → Set ℂ} (hmeas : ∀ i, MeasurableSet (R i))
    (hdisj : Pairwise (Function.onFun Disjoint R)) (h1 : ∀ i, 1 ≤ ν (R i)) {S : Set ℕ}
    {B : Set ℂ} (hSB : ∀ i ∈ S, R i ⊆ B) {M : ℕ} (hB : ν B ≤ M) : S.encard ≤ M := by
  by_contra h
  push Not at h
  have hk : ((M + 1 : ℕ) : ℕ∞) ≤ S.encard := by
    have := Order.add_one_le_of_lt h
    exact_mod_cast this
  obtain ⟨t, htS, htc⟩ := Set.exists_subset_encard_eq hk
  have htf : t.Finite := Set.finite_of_encard_eq_coe htc
  have hcard : htf.toFinset.card = M + 1 := by
    have := htf.encard_eq_coe_toFinset_card
    rw [htc] at this
    exact_mod_cast this.symm
  have hsum : ν (⋃ i ∈ htf.toFinset, R i) = ∑ i ∈ htf.toFinset, ν (R i) :=
    measure_biUnion_finset (hdisj.set_pairwise _) fun i _ ↦ hmeas i
  have hsub : (⋃ i ∈ htf.toFinset, R i) ⊆ B := by
    refine iUnion₂_subset fun i hi ↦ hSB i (htS ?_)
    simpa using hi
  have hle : ((M + 1 : ℕ) : ℝ≥0∞) ≤ ν B := by
    calc ((M + 1 : ℕ) : ℝ≥0∞) = ∑ _i ∈ htf.toFinset, (1 : ℝ≥0∞) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
      _ ≤ ∑ i ∈ htf.toFinset, ν (R i) := Finset.sum_le_sum fun i _ ↦ h1 i
      _ = ν (⋃ i ∈ htf.toFinset, R i) := hsum.symm
      _ ≤ ν B := measure_mono hsub
  have := hle.trans hB
  have : ((M + 1 : ℕ) : ℝ≥0∞) ≤ (M : ℝ≥0∞) := this
  norm_cast at this
  omega

theorem prop_ofReal_le_ceil (x : ℝ) : ENNReal.ofReal x ≤ ((⌈x⌉₊ : ℕ) : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (Nat.le_ceil x)

theorem prop_dist_ofReal (x t : ℝ) : dist (x : ℂ) (t : ℂ) = |x - t| := by
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem prop_eq_ofReal_re {w : ℂ} (hw : w ∈ range fun t : ℝ ↦ (t : ℂ)) : w = (w.re : ℂ) := by
  obtain ⟨t, rfl⟩ := hw
  simp

/-- **Claim 2**, lower bound: a piece is not inside a ball of radius `< ρ(z)` around `z`. -/
theorem claim2_lower_plane (hP : IsMassPartition μ univ dist (massRadius μ) N a A R)
    (hN : 1 ≤ N) (i : ℕ) {z : ℂ} (hz : z ∈ R i) {r : ℝ} (hr : R i ⊆ closedBall z r) :
    massRadius μ z ≤ r := by
  have hr0 : 0 ≤ r := by simpa using hr hz
  refine prop_le_of_forall_gt fun r' hr' ↦ prop_massRadius_le (by linarith) ?_
  exact (hP.one_le_measure hN i).trans
    (measure_mono (hr.trans (closedBall_subset_ball hr')))

/-- **Claim 2**, comparability of `ρ` inside a piece (diameters of neighbours, via Claim 1). -/
theorem claim2_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j, ∀ z ∈ R i, ∀ w ∈ R j,
      dist z w ≤ K * max (massRadius μ z) (massRadius μ w) → massRadius μ w ≤ C * massRadius μ z := by
  obtain ⟨C, hC, h⟩ := claim1_plane hd hfin hm K
  refine ⟨C, hC, fun i j z _ w _ hzw ↦ h w z ?_⟩
  rwa [dist_comm, max_comm]

/-- Pieces meeting `B(z, Kρ(z))` are boundedly many. -/
theorem finite_near_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀))
    (hP : IsMassPartition μ univ dist (massRadius μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ z : ℂ, {i | ∃ w ∈ R i, dist z w ≤ K * massRadius μ z}.encard ≤ M := by
  obtain ⟨R₀, hR₀, hm'⟩ := hm
  set K' := max K 0
  set A' := max A 0
  set K₂ := K' + A' * (1 + K') + 1 with hK₂
  have hK₂1 : 1 ≤ K₂ := by
    have : 0 ≤ K' := le_max_right _ _
    have : 0 ≤ A' := le_max_right _ _
    nlinarith
  obtain ⟨c, C, δ, s, -, hC, -, -, hb⟩ :=
    measure_ball_massRadius_bounds_plane hd hfin ⟨R₀, hR₀, hm'⟩ (K₂ * R₀)
  refine ⟨⌈C * K₂ ^ s⌉₊, fun z ↦ ?_⟩
  have hρ := massRadius_pos hd hfin ⟨R₀, hR₀, hm'⟩ z
  have hρR := massRadius_le hR₀ hm' z
  have hlip := lipschitzWith_massRadius (μ := μ) ⟨R₀, hR₀, hm'⟩
  refine prop_encard_le hP.measurableSet hP.pairwise_disjoint (hP.one_le_measure hN)
    (B := ball z (K₂ * massRadius μ z)) ?_ ?_
  · rintro i ⟨w, hw, hzw⟩ w' hw'
    rw [mem_ball, dist_comm]
    have h1 : dist w w' ≤ A' * massRadius μ w :=
      (hP.dist_le i w hw w' hw').trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (prop_massRadius_nonneg μ w))
    have h2 : massRadius μ w ≤ massRadius μ z + dist z w := by
      have := hlip.dist_le_mul w z
      rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_comm] at this
      linarith [le_abs_self (massRadius μ w - massRadius μ z)]
    have h3 : dist z w ≤ K' * massRadius μ z :=
      hzw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.le)
    have hA' : 0 ≤ A' := le_max_right _ _
    calc dist z w' ≤ dist z w + dist w w' := dist_triangle _ _ _
      _ ≤ K' * massRadius μ z + A' * (massRadius μ z + K' * massRadius μ z) := by
          gcongr
          · exact h1.trans (by gcongr; linarith)
      _ < K₂ * massRadius μ z := by rw [hK₂]; nlinarith
  · refine (hb z _ (by nlinarith) (by nlinarith)).2.trans ?_
    rw [mul_div_assoc, div_self hρ.ne', mul_one]
    exact prop_ofReal_le_ceil _

/-- Bounded number of neighbours of a piece. -/
theorem finite_neighbours_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀))
    (hP : IsMassPartition μ univ dist (massRadius μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ i, {j | ∃ z ∈ R i, ∃ w ∈ R j, dist z w ≤ K * massRadius μ z}.encard ≤ M := by
  set K' := max K 0
  set A' := max A 0
  have hK' : 0 ≤ K' := le_max_right _ _
  have hA' : 0 ≤ A' := le_max_right _ _
  obtain ⟨M, hM⟩ := finite_near_plane hd hfin hm hP hN (A' + K' * (1 + A'))
  have hlip := lipschitzWith_massRadius (μ := μ) hm
  refine ⟨M, fun i ↦ ?_⟩
  obtain ⟨z₀, hz₀⟩ := hP.nonempty hN i
  refine (Set.encard_le_encard ?_).trans (hM z₀)
  rintro j ⟨z, hz, w, hw, hzw⟩
  refine ⟨w, hw, ?_⟩
  have hρ0 := prop_massRadius_nonneg μ z₀
  have h1 : dist z₀ z ≤ A' * massRadius μ z₀ :=
    (hP.dist_le i z₀ hz₀ z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ0)
  have h2 : massRadius μ z ≤ massRadius μ z₀ + dist z₀ z := by
    have := hlip.dist_le_mul z z₀
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_comm] at this
    linarith [le_abs_self (massRadius μ z - massRadius μ z₀)]
  have h3 : dist z w ≤ K' * massRadius μ z :=
    hzw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (prop_massRadius_nonneg μ z))
  calc dist z₀ w ≤ dist z₀ z + dist z w := dist_triangle _ _ _
    _ ≤ A' * massRadius μ z₀ + K' * (massRadius μ z₀ + A' * massRadius μ z₀) := by
        gcongr
        exact h3.trans (by gcongr; linarith)
    _ = (A' + K' * (1 + A')) * massRadius μ z₀ := by ring

/-- For a piece missing `B(z, ηρ(z))`, all its points are at comparable distance from `z`. -/
theorem far_comparable_plane (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀))
    (hP : IsMassPartition μ univ dist (massRadius μ) N a A R) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (i : ℕ), (∀ w ∈ R i, η * massRadius μ z ≤ dist z w) →
      ∀ w ∈ R i, ∀ w' ∈ R i, dist z w' ≤ C * dist z w := by
  set A' := max A 0
  have hA' : 0 ≤ A' := le_max_right _ _
  have hlip := lipschitzWith_massRadius (μ := μ) hm
  refine ⟨1 + A' + A' / η, by positivity, fun z i hfar w hw w' hw' ↦ ?_⟩
  have h1 : dist w w' ≤ A' * massRadius μ w :=
    (hP.dist_le i w hw w' hw').trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (prop_massRadius_nonneg μ w))
  have h2 : massRadius μ w ≤ massRadius μ z + dist z w := by
    have := hlip.dist_le_mul w z
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_comm] at this
    linarith [le_abs_self (massRadius μ w - massRadius μ z)]
  have h3 : massRadius μ z ≤ dist z w / η := by rw [le_div_iff₀ hη, mul_comm]; exact hfar w hw
  have hd0 : 0 ≤ dist z w := dist_nonneg
  calc dist z w' ≤ dist z w + dist w w' := dist_triangle _ _ _
    _ ≤ dist z w + A' * (dist z w / η + dist z w) := by
        gcongr
        exact h1.trans (by gcongr; linarith)
    _ = (1 + A' + A' / η) * dist z w := by field_simp; ring

theorem far_comparable_disc (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ 𝔻, ∀ i : ℕ, (∀ w ∈ R i, η * massRadiusDisc μ z ≤ hypDist z w) →
      ∀ w ∈ R i, ∀ w' ∈ R i, hypDist z w' ≤ C * hypDist z w := by
  set A' := max A 0
  have hA' : 0 ≤ A' := le_max_right _ _
  refine ⟨1 + A' + A' / η, by positivity, fun z hz i hfar w hw w' hw' ↦ ?_⟩
  have hwD := hP.subset_of_mem i hw
  have hw'D := hP.subset_of_mem i hw'
  have h1 : hypDist w w' ≤ A' * massRadiusDisc μ w :=
    (hP.dist_le i w hw w' hw').trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (prop_massRadiusDisc_nonneg μ w))
  have h2 : massRadiusDisc μ w ≤ massRadiusDisc μ z + hypDist z w := by
    have := abs_massRadiusDisc_sub_le hm hz hwD
    linarith [neg_abs_le (massRadiusDisc μ z - massRadiusDisc μ w)]
  have h3 : massRadiusDisc μ z ≤ hypDist z w / η := by
    rw [le_div_iff₀ hη, mul_comm]; exact hfar w hw
  have hd0 : 0 ≤ hypDist z w := hypDist_nonneg _ _
  calc hypDist z w' ≤ hypDist z w + hypDist w w' := hypDist_triangle hz hwD hw'D
    _ ≤ hypDist z w + A' * (hypDist z w / η + hypDist z w) := by
        gcongr
        exact h1.trans (by gcongr; linarith)
    _ = (1 + A' + A' / η) * hypDist z w := by field_simp; ring

theorem finite_near_disc (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ z ∈ 𝔻, {i | ∃ w ∈ R i, hypDist z w ≤ K * massRadiusDisc μ z}.encard ≤ M := by
  obtain ⟨R₀, hR₀, hm'⟩ := hm
  set K' := max K 0
  set A' := max A 0
  set K₂ := K' + A' * (1 + K') + 1 with hK₂
  have hK₂1 : 1 ≤ K₂ := by
    have : 0 ≤ K' := le_max_right _ _
    have : 0 ≤ A' := le_max_right _ _
    nlinarith
  obtain ⟨c, C, δ, s, -, hC, -, -, hb⟩ :=
    measure_hypBall_massRadiusDisc_bounds hd hfin ⟨R₀, hR₀, hm'⟩ (K₂ * R₀)
  refine ⟨⌈C * K₂ ^ s⌉₊, fun z hz ↦ ?_⟩
  have hρ := massRadiusDisc_pos hd hfin ⟨R₀, hR₀, hm'⟩ hz
  have hρR := massRadiusDisc_le hR₀ hm' hz
  refine prop_encard_le hP.measurableSet hP.pairwise_disjoint (hP.one_le_measure hN)
    (B := hypBall z (K₂ * massRadiusDisc μ z)) ?_ ?_
  · rintro i ⟨w, hw, hzw⟩ w' hw'
    have hwD := hP.subset_of_mem i hw
    have hw'D := hP.subset_of_mem i hw'
    refine ⟨hw'D, ?_⟩
    have h1 : hypDist w w' ≤ A' * massRadiusDisc μ w :=
      (hP.dist_le i w hw w' hw').trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (prop_massRadiusDisc_nonneg μ w))
    have h2 : massRadiusDisc μ w ≤ massRadiusDisc μ z + hypDist z w := by
      have := abs_massRadiusDisc_sub_le ⟨R₀, hR₀, hm'⟩ hz hwD
      linarith [neg_abs_le (massRadiusDisc μ z - massRadiusDisc μ w)]
    have h3 : hypDist z w ≤ K' * massRadiusDisc μ z :=
      hzw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.le)
    have hA' : 0 ≤ A' := le_max_right _ _
    calc hypDist z w' ≤ hypDist z w + hypDist w w' := hypDist_triangle hz hwD hw'D
      _ ≤ K' * massRadiusDisc μ z + A' * (massRadiusDisc μ z + K' * massRadiusDisc μ z) := by
          gcongr
          · exact h1.trans (by gcongr; linarith)
      _ < K₂ * massRadiusDisc μ z := by rw [hK₂]; nlinarith
  · refine (hb z hz _ (by nlinarith) (by nlinarith)).2.trans ?_
    rw [mul_div_assoc, div_self hρ.ne', mul_one]
    exact prop_ofReal_le_ceil _

theorem claim2_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j, ∀ z ∈ R i, ∀ w ∈ R j,
      hypDist z w ≤ K * max (massRadiusDisc μ z) (massRadiusDisc μ w) →
        massRadiusDisc μ w ≤ C * massRadiusDisc μ z := by
  obtain ⟨C, hC, h⟩ := claim1_disc hd hfin hm K
  refine ⟨C, hC, fun i j z hz w hw hzw ↦ h w (hP.subset_of_mem j hw) z (hP.subset_of_mem i hz) ?_⟩
  rwa [hypDist_comm, max_comm]

theorem claim2_lower_disc (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R)
    (hN : 1 ≤ N) (i : ℕ) {z : ℂ} (hz : z ∈ R i) {r : ℝ}
    (hr : R i ⊆ {w | w ∈ 𝔻 ∧ hypDist z w ≤ r}) : massRadiusDisc μ z ≤ r := by
  have hr0 : 0 ≤ r := by
    have := (hr hz).2
    rwa [hypDist_self] at this
  refine prop_le_of_forall_gt fun r' hr' ↦ prop_massRadiusDisc_le (by linarith) ?_
  refine (hP.one_le_measure hN i).trans (measure_mono fun w hw ↦ ?_)
  exact ⟨(hr hw).1, (hr hw).2.trans_lt hr'⟩

theorem finite_neighbours_disc (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ i, {j | ∃ z ∈ R i, ∃ w ∈ R j, hypDist z w ≤ K * massRadiusDisc μ z}.encard ≤ M := by
  set K' := max K 0
  set A' := max A 0
  have hK' : 0 ≤ K' := le_max_right _ _
  have hA' : 0 ≤ A' := le_max_right _ _
  obtain ⟨M, hM⟩ := finite_near_disc hd hfin hm hP hN (A' + K' * (1 + A'))
  refine ⟨M, fun i ↦ ?_⟩
  obtain ⟨z₀, hz₀⟩ := hP.nonempty hN i
  have hz₀D := hP.subset_of_mem i hz₀
  refine (Set.encard_le_encard ?_).trans (hM z₀ hz₀D)
  rintro j ⟨z, hz, w, hw, hzw⟩
  refine ⟨w, hw, ?_⟩
  have hzD := hP.subset_of_mem i hz
  have hwD := hP.subset_of_mem j hw
  have hρ0 := prop_massRadiusDisc_nonneg μ z₀
  have h1 : hypDist z₀ z ≤ A' * massRadiusDisc μ z₀ :=
    (hP.dist_le i z₀ hz₀ z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ0)
  have h2 : massRadiusDisc μ z ≤ massRadiusDisc μ z₀ + hypDist z₀ z := by
    have := abs_massRadiusDisc_sub_le hm hz₀D hzD
    linarith [neg_abs_le (massRadiusDisc μ z₀ - massRadiusDisc μ z)]
  have h3 : hypDist z w ≤ K' * massRadiusDisc μ z :=
    hzw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (prop_massRadiusDisc_nonneg μ z))
  calc hypDist z₀ w ≤ hypDist z₀ z + hypDist z w := hypDist_triangle hz₀D hzD hwD
    _ ≤ A' * massRadiusDisc μ z₀ + K' * (massRadiusDisc μ z₀ + A' * massRadiusDisc μ z₀) := by
        gcongr
        exact h3.trans (by gcongr; linarith)
    _ = (A' + K' * (1 + A')) * massRadiusDisc μ z₀ := by ring

/-! Line versions (`Ω = ℝ ⊆ ℂ`, `ρ(z) = massRadiusLine μ z.re`). -/

theorem claim2_lower_line
    (hP : IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R)
    (hN : 1 ≤ N) (i : ℕ) {z : ℂ} (hz : z ∈ R i) {r : ℝ} (hr : R i ⊆ closedBall z r) :
    massRadiusLine μ z.re ≤ r := by
  have hr0 : 0 ≤ r := by simpa using hr hz
  have hzR := prop_eq_ofReal_re (hP.subset_of_mem i hz)
  refine prop_le_of_forall_gt fun r' hr' ↦ prop_massRadiusLine_le (by linarith) ?_
  refine (hP.one_le_measure hN i).trans (measure_mono fun w hw ↦ ?_)
  have hwR := prop_eq_ofReal_re (hP.subset_of_mem i hw)
  have hd := hr hw
  rw [mem_closedBall, hwR, hzR, prop_dist_ofReal] at hd
  refine ⟨w.re, ⟨?_, ?_⟩, hwR.symm⟩ <;> linarith [abs_le.1 hd]

theorem finite_near_line (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R₀))
    (hP : IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R)
    (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ x : ℝ, {i | ∃ w ∈ R i, dist (x : ℂ) w ≤ K * massRadiusLine μ x}.encard ≤ M := by
  obtain ⟨R₀, hR₀, hm'⟩ := hm
  set K' := max K 0
  set A' := max A 0
  set K₂ := K' + A' * (1 + K') + 1 with hK₂
  have hK₂1 : 1 ≤ K₂ := by
    have : 0 ≤ K' := le_max_right _ _
    have : 0 ≤ A' := le_max_right _ _
    nlinarith
  obtain ⟨c, C, δ, s, -, hC, -, -, hb⟩ :=
    measure_lineInterval_massRadiusLine_bounds hd hfin ⟨R₀, hR₀, hm'⟩ (K₂ * R₀)
  have hlip := lipschitzWith_massRadiusLine (μ := μ) ⟨R₀, hR₀, hm'⟩
  refine ⟨⌈C * K₂ ^ s⌉₊, fun x ↦ ?_⟩
  have hρ := massRadiusLine_pos hd hfin ⟨R₀, hR₀, hm'⟩ x
  have hρR := massRadiusLine_le hR₀ hm' x
  refine prop_encard_le hP.measurableSet hP.pairwise_disjoint (hP.one_le_measure hN)
    (B := lineInterval x (K₂ * massRadiusLine μ x)) ?_ ?_
  · rintro i ⟨w, hw, hzw⟩ w' hw'
    have hwR := prop_eq_ofReal_re (hP.subset_of_mem i hw)
    have hw'R := prop_eq_ofReal_re (hP.subset_of_mem i hw')
    have h1 : dist w w' ≤ A' * massRadiusLine μ w.re :=
      (hP.dist_le i w hw w' hw').trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (prop_massRadiusLine_nonneg μ _))
    have h2 : massRadiusLine μ w.re ≤ massRadiusLine μ x + dist (x : ℂ) w := by
      have := hlip.dist_le_mul w.re x
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at this
      rw [hwR, prop_dist_ofReal, ← hwR]
      linarith [le_abs_self (massRadiusLine μ w.re - massRadiusLine μ x), abs_sub_comm w.re x]
    have h3 : dist (x : ℂ) w ≤ K' * massRadiusLine μ x :=
      hzw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.le)
    have hA' : 0 ≤ A' := le_max_right _ _
    have hlt : dist (x : ℂ) w' < K₂ * massRadiusLine μ x :=
      calc dist (x : ℂ) w' ≤ dist (x : ℂ) w + dist w w' := dist_triangle _ _ _
        _ ≤ K' * massRadiusLine μ x + A' * (massRadiusLine μ x + K' * massRadiusLine μ x) := by
            gcongr
            · exact h1.trans (by gcongr; linarith)
        _ < K₂ * massRadiusLine μ x := by rw [hK₂]; nlinarith
    rw [hw'R, prop_dist_ofReal] at hlt
    refine ⟨w'.re, ⟨?_, ?_⟩, hw'R.symm⟩ <;> linarith [abs_lt.1 hlt]
  · refine (hb x _ (by nlinarith) (by nlinarith)).2.trans ?_
    rw [mul_div_assoc, div_self hρ.ne', mul_one]
    exact prop_ofReal_le_ceil _

theorem far_comparable_line (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R₀))
    (hP : IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (i : ℕ), (∀ w ∈ R i, η * massRadiusLine μ x ≤ dist (x : ℂ) w) →
      ∀ w ∈ R i, ∀ w' ∈ R i, dist (x : ℂ) w' ≤ C * dist (x : ℂ) w := by
  set A' := max A 0
  have hA' : 0 ≤ A' := le_max_right _ _
  have hlip := lipschitzWith_massRadiusLine (μ := μ) hm
  refine ⟨1 + A' + A' / η, by positivity, fun x i hfar w hw w' hw' ↦ ?_⟩
  have hwR := prop_eq_ofReal_re (hP.subset_of_mem i hw)
  have h1 : dist w w' ≤ A' * massRadiusLine μ w.re :=
    (hP.dist_le i w hw w' hw').trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (prop_massRadiusLine_nonneg μ _))
  have h2 : massRadiusLine μ w.re ≤ massRadiusLine μ x + dist (x : ℂ) w := by
    have := hlip.dist_le_mul w.re x
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at this
    rw [hwR, prop_dist_ofReal, ← hwR]
    linarith [le_abs_self (massRadiusLine μ w.re - massRadiusLine μ x), abs_sub_comm w.re x]
  have h3 : massRadiusLine μ x ≤ dist (x : ℂ) w / η := by
    rw [le_div_iff₀ hη, mul_comm]; exact hfar w hw
  have hd0 : 0 ≤ dist (x : ℂ) w := dist_nonneg
  calc dist (x : ℂ) w' ≤ dist (x : ℂ) w + dist w w' := dist_triangle _ _ _
    _ ≤ dist (x : ℂ) w + A' * (dist (x : ℂ) w / η + dist (x : ℂ) w) := by
        gcongr
        exact h1.trans (by gcongr; linarith)
    _ = (1 + A' + A' / η) * dist (x : ℂ) w := by field_simp; ring

/-- Euclidean size of the disc pieces. -/
theorem euclid_size_disc (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, ∀ z ∈ R i, ∀ w ∈ R i,
      ‖z - w‖ ≤ C * (1 - ‖z‖ ^ 2) * massRadiusDisc μ z := by
  obtain ⟨R₀, hR₀, hm'⟩ := hm
  set A' := max A 0
  have hA' : 0 ≤ A' := le_max_right _ _
  refine ⟨(A' + 1) * Real.exp (2 * A' * R₀), by positivity, fun i z hz w hw ↦ ?_⟩
  have hzD := hP.subset_of_mem i hz
  have hwD := hP.subset_of_mem i hw
  have hρ0 := prop_massRadiusDisc_nonneg μ z
  have hρR := massRadiusDisc_le hR₀ hm' hzD
  set u := A' * massRadiusDisc μ z with hu
  have hu0 : 0 ≤ u := by positivity
  have hdist : hypDist z w ≤ u :=
    (hP.dist_le i z hz w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ0)
  have hkey := norm_sub_le_of_hypDist_le hzD hwD hdist (Real.tanh_lt_one u)
  rw [norm_sub_rev] at hkey
  have hz1 : 0 ≤ 1 - ‖z‖ ^ 2 := by
    have := norm_lt_one_of_mem_disc hzD
    nlinarith [norm_nonneg z]
  -- `tanh u / (1 - tanh u) = (e^{2u} - 1)/2 ≤ u e^{2u}`
  have hf : Real.tanh u / (1 - Real.tanh u) ≤ u * Real.exp (2 * u) := by
    have he : Real.tanh u / (1 - Real.tanh u) = (Real.exp (2 * u) - 1) / 2 := by
      have hpos : 0 < Real.exp (2 * u) + 1 := by positivity
      rw [tanh_eq_exp_two_mul]
      field_simp
      ring
    rw [he]
    have h1 := Real.add_one_le_exp (-(2 * u))
    have h2 : Real.exp (2 * u) * Real.exp (-(2 * u)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (2 * u)
    nlinarith
  have hexp : Real.exp (2 * u) ≤ Real.exp (2 * A' * R₀) := by
    apply Real.exp_le_exp.2
    rw [hu]; nlinarith
  calc ‖z - w‖ ≤ Real.tanh u / (1 - Real.tanh u) * (1 - ‖z‖ ^ 2) := hkey
    _ ≤ u * Real.exp (2 * u) * (1 - ‖z‖ ^ 2) := by gcongr
    _ ≤ (A' + 1) * massRadiusDisc μ z * Real.exp (2 * A' * R₀) * (1 - ‖z‖ ^ 2) := by
        rw [hu]; gcongr; linarith
    _ = (A' + 1) * Real.exp (2 * A' * R₀) * (1 - ‖z‖ ^ 2) * massRadiusDisc μ z := by ring

/-- Sum over pieces versus integral (generic). -/
theorem IsMassPartition.mass_mul_le_setLIntegral {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) (i : ℕ) {c : ℝ≥0∞} {f : ℂ → ℝ≥0∞}
    (hc : ∀ z ∈ R i, c ≤ f z) : (N : ℝ≥0∞) * c ≤ ∫⁻ z in R i, f z ∂μ := by
  calc (N : ℝ≥0∞) * c = ∫⁻ _ in R i, c ∂μ := by rw [setLIntegral_const, hP.measure_eq, mul_comm]
    _ ≤ ∫⁻ z in R i, f z ∂μ := setLIntegral_mono' (hP.measurableSet i) hc

theorem IsMassPartition.lintegral_biUnion {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) (S : Set ℕ) (f : ℂ → ℝ≥0∞) :
    ∫⁻ z in ⋃ i ∈ S, R i, f z ∂μ = ∑' i : S, ∫⁻ z in R i, f z ∂μ :=
  MeasureTheory.lintegral_biUnion S.to_countable (fun i _ ↦ hP.measurableSet i)
    (hP.pairwise_disjoint.set_pairwise S) f

theorem IsMassPartition.existsUnique_mem {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) {z : ℂ} (hz : z ∈ Ω) : ∃! i, z ∈ R i := by
  rw [← hP.iUnion_eq, mem_iUnion] at hz
  obtain ⟨i, hi⟩ := hz
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  by_contra hji
  exact Set.disjoint_left.1 (hP.pairwise_disjoint hji) hj hi

end PartitionProps

end OC
