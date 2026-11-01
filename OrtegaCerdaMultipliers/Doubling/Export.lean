import OrtegaCerdaMultipliers.Doubling.Line
import OrtegaCerdaMultipliers.Doubling.HypDisc

/-!
# M03 (Doubling) — The statements in `ℂ`-terms (plane, disc, line)

See `blueprint/M03_Doubling.md` §2.4.  All proofs complete.

These are the `ℂ`-level statements consumed downstream, obtained from `Doubling/Abstract.lean`
through `ℂ`, `linePull` and `discPull`, and the finiteness bridge from `IsSubharmonicWeight`.
The last section adds the forms requested by M04 (`measure_singleton_*`, `logSmall_*`, the latter
moved from M04) and M11 (`exists_hypBall_measure_gt`).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ### Small real-analysis helpers -/

theorem M03b.le_rpow_one_div_of_rpow_le {q M δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (h : q ^ δ ≤ M) :
    q ≤ M ^ (1 / δ) := by
  have h1 : (q ^ δ) ^ (1 / δ) ≤ M ^ (1 / δ) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hq _) h (by positivity)
  rwa [one_div, Real.rpow_rpow_inv hq hδ.ne', ← one_div] at h1

/-! ### Finiteness from `IsSubharmonicWeight` -/

theorem M03b.dist_ofReal_ofReal (x y : ℝ) : dist (x : ℂ) (y : ℂ) = |x - y| := by
  rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq]

/-- Hyperbolic balls lie in a Euclidean closed disc of radius `< 1` (hence in a compact subset
of `𝔻`). -/
theorem M03b.hypBall_subset_closedBall_tanh {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    hypBall z r ⊆ closedBall 0 (Real.tanh (Real.artanh ‖z‖ + r)) := by
  intro w hw
  have hw𝔻 : w ∈ 𝔻 := hw.1
  have h0 : (0 : ℂ) ∈ 𝔻 := mem_ball_self one_pos
  have htri := hypDist_triangle h0 hz hw𝔻
  rw [hypDist_zero_left, hypDist_zero_left] at htri
  have hlt : Real.artanh ‖w‖ < Real.artanh (Real.tanh (Real.artanh ‖z‖ + r)) := by
    rw [Real.artanh_tanh]; linarith [hw.2]
  have hwI : ‖w‖ ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [norm_nonneg w], norm_lt_one_of_mem_disc hw𝔻⟩
  rw [mem_closedBall_zero_iff]
  exact ((Real.artanh_lt_artanh_iff hwI
    ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).1 hlt).le

theorem IsSubharmonicWeight.measure_ball_lt_top {φ : ℂ → ℝ} {μ : Measure ℂ}
    (h : IsSubharmonicWeight univ φ μ) (z : ℂ) (r : ℝ) : μ (ball z r) < ∞ :=
  (measure_mono ball_subset_closedBall).trans_lt
    (h.finite_of_compact _ (subset_univ _) (isCompact_closedBall z r))

theorem IsSubharmonicWeight.measure_hypBall_lt_top {φ : ℂ → ℝ} {μ : Measure ℂ}
    (h : IsSubharmonicWeight 𝔻 φ μ) {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) : μ (hypBall z r) < ∞ :=
  (measure_mono (M03b.hypBall_subset_closedBall_tanh hz r)).trans_lt
    (h.finite_of_compact _ (closedBall_subset_ball (Real.tanh_lt_one _))
      (isCompact_closedBall _ _))

theorem IsSubharmonicWeight.measure_lineInterval_lt_top {φ : ℂ → ℝ} {μ : Measure ℂ}
    (h : IsSubharmonicWeight univ φ μ) (x r : ℝ) : μ (lineInterval x r) < ∞ := by
  refine (measure_mono ?_).trans_lt
    (h.finite_of_compact _ (subset_univ _) (isCompact_closedBall (x : ℂ) r))
  rintro _ ⟨t, ht, rfl⟩
  rw [mem_closedBall, M03b.dist_ofReal_ofReal]
  rw [Set.mem_Ioo] at ht
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-! ### Plane -/

section Plane
variable {μ : Measure ℂ}

theorem lemma1_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ γ A : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < A ∧
      ∀ (z z' : ℂ) (r r' : ℝ), 0 < r' → r ≤ R₁ → dist z z' + r' ≤ r →
        0 < μ (ball z' r') → μ (ball z r) < ∞ →
        ((μ (ball z r)).toReal / (μ (ball z' r')).toReal) ^ γ ≤ A * (r / r') ∧
        r / r' ≤ A * ((μ (ball z r)).toReal / (μ (ball z' r')).toReal) ^ (1 / γ) :=
  IsLocDoublingM.lemma1 (μ := μ) hd R₁

theorem doubling_upTo_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ R₁ →
      μ (ball z (2 * r)) ≤ C * μ (ball z r) := IsLocDoublingM.exists_const_of_le (μ := μ) hd R₁

theorem measure_ball_le_rpow_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (z z' : ℂ) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist z z' ≤ r → μ (ball z r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (ball z' r') :=
  IsLocDoublingM.measure_ball_le_rpow (μ := μ) hd R₁

theorem rpow_le_measure_ball_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (z z' : ℂ) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist z z' ≤ r → ENNReal.ofReal (c * (r / r') ^ δ) * μ (ball z' r') ≤ μ (ball z r) :=
  IsLocDoublingM.rpow_le_measure_ball (μ := μ) hd R₁

theorem measure_ball_le_of_dist_le_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ z w : ℂ, ∀ r : ℝ, 0 < r → r ≤ R₁ → dist z w ≤ r →
      μ (ball w r) ≤ C * μ (ball z r) := IsLocDoublingM.measure_ball_le_of_dist_le (μ := μ) hd R₁

/-- **Lemma 2** (plane): porous sets, in particular lines, segments and circles, are null. -/
theorem measure_eq_zero_of_isPorous_plane (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) {E : Set ℂ} (hE : IsPorous E) : μ E = 0 :=
  IsLocDoublingM.measure_eq_zero_of_isPorous (μ := μ) hd hfin hE

theorem lemma2_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞) (a b : ℂ) :
    μ (segment ℝ a b) = 0 := measure_eq_zero_of_isPorous_plane hd hfin (isPorous_segment a b)

theorem measure_sphere_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (z : ℂ) (r : ℝ) : μ (sphere z r) = 0 := IsLocDoublingM.measure_sphere (μ := μ) hd hfin z r

theorem continuous_measure_ball_plane (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (z : ℂ) : Continuous fun r : ℝ ↦ μ (ball z r) :=
  IsLocDoublingM.continuous_measure_ball (μ := μ) hd hfin z

theorem massRadius_pos (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (z : ℂ) : 0 < massRadius μ z :=
  IsLocDoublingM.massRadiusM_pos (μ := μ) hd hfin (let ⟨R, hR, h⟩ := hm; ⟨R, hR, h z⟩)

theorem massRadius_le {R : ℝ} (hR : 0 < R) (hm : ∀ z, 1 ≤ μ (ball z R)) (z : ℂ) :
    massRadius μ z ≤ R := massRadiusM_le hR (hm z)

theorem measure_ball_massRadius (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (z : ℂ) :
    μ (ball z (massRadius μ z)) = 1 :=
  IsLocDoublingM.measure_ball_massRadiusM (μ := μ) hd hfin (let ⟨R, hR, h⟩ := hm; ⟨R, hR, h z⟩)

theorem lipschitzWith_massRadius (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) :
    LipschitzWith 1 (massRadius μ) :=
  lipschitzWith_massRadiusM (μ := μ) fun z ↦ let ⟨R, hR, h⟩ := hm; ⟨R, hR, h z⟩

theorem measure_ball_massRadius_bounds_plane (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ (z : ℂ) (r : ℝ),
      massRadius μ z ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadius μ z) ^ δ) ≤ μ (ball z r) ∧
        μ (ball z r) ≤ ENNReal.ofReal (C * (r / massRadius μ z) ^ s) :=
  IsLocDoublingM.measure_ball_massRadiusM_bounds (μ := μ) hd hfin hm R₁

theorem claim1_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z w : ℂ, dist z w ≤ K * max (massRadius μ z) (massRadius μ w) →
      massRadius μ z ≤ C * massRadius μ w := IsLocDoublingM.claim1 (μ := μ) hd hfin hm K

theorem lemma3_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w : ℂ,
      ∫⁻ z in ball w R₁,
        ENNReal.ofReal ((massRadius μ z / max (dist z w) (δ * massRadius μ w)) ^ m) ∂μ ≤ C :=
  IsLocDoublingM.lemma3 (μ := μ) hd hfin hm

theorem christ_lemma23_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ (z : ℂ) (R : ℝ), 0 < R → R ≤ R₁ →
      ∫⁻ ζ in ball z R, ENNReal.ofReal (Real.log (R / dist z ζ)) ∂μ ≤ C * μ (ball z R) :=
  IsLocDoublingM.christ_lemma23 (μ := μ) hd R₁

theorem exists_radius_lt_measure_ball_plane (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R))
    (p : ℝ≥0) : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, (p : ℝ≥0∞) < μ (ball z r) :=
  exists_radius_lt_measure_ball hm p

end Plane

/-! ### Transfer helpers -/

/-- Integrals against a pulled-back measure over a set, as integrals over the image. -/
theorem M03b.lintegral_comap_image {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {e : α → β}
    (he : MeasurableEmbedding e) (μ : Measure β) (g : β → ℝ≥0∞) (s : Set α) :
    ∫⁻ a in s, g (e a) ∂(μ.comap e) = ∫⁻ z in e '' s, g z ∂μ := by
  rw [he.restrict_comap, ← he.lintegral_map, he.map_comap,
    Measure.restrict_restrict he.measurableSet_range,
    inter_eq_self_of_subset_right (image_subset_range _ _)]

@[simp] theorem M03b.hdisc_val_mk (z : ℂ) (hz : z ∈ 𝔻) : (HDisc.mk z hz).val = z := rfl

theorem M03b.hdisc_dist_mk (z : ℂ) (hz : z ∈ 𝔻) (w : ℂ) (hw : w ∈ 𝔻) :
    dist (HDisc.mk z hz) (HDisc.mk w hw) = hypDist z w := rfl

theorem M03b.lintegral_discPull (μ : Measure ℂ) (g : ℂ → ℝ≥0∞) (s : Set HDisc) :
    ∫⁻ a in s, g a.val ∂(discPull μ) = ∫⁻ z in HDisc.val '' s, g z ∂μ :=
  M03b.lintegral_comap_image HDisc.measurableEmbedding_val μ g s

theorem M03b.isLocDoublingM_discPull {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ) :
    IsLocDoublingM (discPull μ) :=
  (isLocallyDoublingDisc_iff μ).1 hd

theorem M03b.discPull_hfin {μ : Measure ℂ} (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) :
    ∀ (a : HDisc) (r : ℝ), discPull μ (ball a r) < ∞ := fun a r ↦ by
  rw [discPull_ball]; exact hfin _ a.2 r

theorem M03b.discPull_hm {μ : Measure ℂ} (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : HDisc, 1 ≤ discPull μ (ball a R) := by
  obtain ⟨R, hR, h⟩ := hm
  exact ⟨R, hR, fun a ↦ by rw [discPull_ball]; exact h _ a.2⟩

theorem M03b.discPull_hne {μ : Measure ℂ} (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R))
    (a : HDisc) : ∃ r, 0 < r ∧ 1 ≤ discPull μ (ball a r) := by
  obtain ⟨R, hR, h⟩ := M03b.discPull_hm hm
  exact ⟨R, hR, h a⟩

theorem M03b.massRadiusDisc_eq' {μ : Measure ℂ} {z : ℂ} (hz : z ∈ 𝔻) :
    massRadiusDisc μ z = massRadiusM (discPull μ) (HDisc.mk z hz) := by
  have := massRadiusDisc_eq μ (HDisc.mk z hz)
  rwa [M03b.hdisc_val_mk] at this

theorem M03b.hypBall_eq_image_ball {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    hypBall z r = HDisc.val '' ball (HDisc.mk z hz) r := by
  rw [HDisc.image_ball, M03b.hdisc_val_mk]

section Growth

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- **Growth, explicit radius** (no doubling): `k + 1` disjoint balls of radius `R` centred at
distances `2iR` from `x` lie in `B(x, (2k+1)R)`. -/
theorem M03b.sum_le_measure_ball_of_le [BallGeometry X] {μ : Measure X} {R : ℝ} (hR : 0 < R)
    {m : ℝ≥0∞} (h : ∀ y : X, m ≤ μ (ball y R)) (x : X) (k : ℕ) :
    ((k : ℝ≥0∞) + 1) * m ≤ μ (ball x ((2 * k + 1) * R)) := by
  have hy : ∀ i : ℕ, ∃ y : X, dist x y = 2 * i * R := fun i ↦
    exists_dist_eq x (by positivity)
  choose y hy using hy
  have hdisj : (↑(Finset.range (k + 1)) : Set ℕ).PairwiseDisjoint fun i ↦ ball (y i) R := by
    intro i _ j _ hij
    refine Set.disjoint_left.2 fun w hwi hwj ↦ ?_
    rw [mem_ball] at hwi hwj
    have h1 : dist (y i) (y j) < 2 * R := by
      calc dist (y i) (y j) ≤ dist (y i) w + dist w (y j) := dist_triangle _ _ _
        _ < R + R := add_lt_add (by rwa [dist_comm]) hwj
        _ = 2 * R := by ring
    have h2 : |dist x (y i) - dist x (y j)| ≤ dist (y i) (y j) := by
      have := abs_dist_sub_le (y i) (y j) x
      rwa [dist_comm (y i) x, dist_comm (y j) x] at this
    rw [hy i, hy j] at h2
    have h3 : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      rcases lt_or_gt_of_ne hij with h | h
      · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]
        linarith
    have h4 : 2 * i * R - 2 * j * R = 2 * R * ((i : ℝ) - j) := by ring
    rw [h4, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * R)] at h2
    nlinarith
  have hsub : (⋃ i ∈ Finset.range (k + 1), ball (y i) R) ⊆ ball x ((2 * k + 1) * R) := by
    intro w hw
    simp only [mem_iUnion, Finset.mem_range] at hw
    obtain ⟨i, hi, hw⟩ := hw
    rw [mem_ball] at hw ⊢
    have hik : (i : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 hi
    calc dist w x ≤ dist w (y i) + dist (y i) x := dist_triangle _ _ _
      _ < R + 2 * i * R := by rw [dist_comm (y i) x, hy i]; linarith
      _ ≤ (2 * k + 1) * R := by nlinarith
  calc ((k : ℝ≥0∞) + 1) * m = ∑ _i ∈ Finset.range (k + 1), m := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ∑ i ∈ Finset.range (k + 1), μ (ball (y i) R) := Finset.sum_le_sum fun i _ ↦ h (y i)
    _ = μ (⋃ i ∈ Finset.range (k + 1), ball (y i) R) :=
        (measure_biUnion_finset hdisj fun i _ ↦ measurableSet_ball).symm
    _ ≤ μ (ball x ((2 * k + 1) * R)) := measure_mono hsub

end Growth

/-! ### Disc (hyperbolic balls) -/

section Disc
variable {μ : Measure ℂ}

theorem lemma1_disc (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ γ A : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < A ∧
      ∀ (z z' : ℂ) (r r' : ℝ), z ∈ 𝔻 → z' ∈ 𝔻 → 0 < r' → r ≤ R₁ → hypDist z z' + r' ≤ r →
        0 < μ (hypBall z' r') → μ (hypBall z r) < ∞ →
        ((μ (hypBall z r)).toReal / (μ (hypBall z' r')).toReal) ^ γ ≤ A * (r / r') ∧
        r / r' ≤ A * ((μ (hypBall z r)).toReal / (μ (hypBall z' r')).toReal) ^ (1 / γ) := by
  obtain ⟨γ, A, hγ, hγ1, hA, h⟩ := IsLocDoublingM.lemma1 (M03b.isLocDoublingM_discPull hd) R₁
  refine ⟨γ, A, hγ, hγ1, hA, fun z z' r r' hz hz' hr' hr hdist h0 hfin => ?_⟩
  have := h (HDisc.mk z hz) (HDisc.mk z' hz') r r' hr' hr hdist
    (by rwa [discPull_ball]) (by rwa [discPull_ball])
  simpa only [discPull_ball, M03b.hdisc_val_mk] using this

theorem doubling_upTo_disc (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → r ≤ R₁ →
      μ (hypBall z (2 * r)) ≤ C * μ (hypBall z r) := by
  obtain ⟨C, hC, h⟩ := IsLocDoublingM.exists_const_of_le (M03b.isLocDoublingM_discPull hd) R₁
  refine ⟨C, hC, fun z hz r hr hr1 => ?_⟩
  simpa only [discPull_ball, M03b.hdisc_val_mk] using h (HDisc.mk z hz) r hr hr1

theorem measure_hypBall_le_rpow (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (z z' : ℂ) (r r' : ℝ), z ∈ 𝔻 → z' ∈ 𝔻 → 0 < r' → r' ≤ r →
      r ≤ R₁ → hypDist z z' ≤ r →
        μ (hypBall z r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (hypBall z' r') := by
  obtain ⟨C, s, hC, hs, h⟩ :=
      IsLocDoublingM.measure_ball_le_rpow (M03b.isLocDoublingM_discPull hd) R₁
  refine ⟨C, s, hC, hs, fun z z' r r' hz hz' hr' hrr hr hdist => ?_⟩
  simpa only [discPull_ball, M03b.hdisc_val_mk] using
    h (HDisc.mk z hz) (HDisc.mk z' hz') r r' hr' hrr hr hdist

theorem rpow_le_measure_hypBall (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (z z' : ℂ) (r r' : ℝ), z ∈ 𝔻 → z' ∈ 𝔻 → 0 < r' → r' ≤ r →
      r ≤ R₁ → hypDist z z' ≤ r →
        ENNReal.ofReal (c * (r / r') ^ δ) * μ (hypBall z' r') ≤ μ (hypBall z r) := by
  obtain ⟨c, δ, hc, hδ, h⟩ :=
      IsLocDoublingM.rpow_le_measure_ball (M03b.isLocDoublingM_discPull hd) R₁
  refine ⟨c, δ, hc, hδ, fun z z' r r' hz hz' hr' hrr hr hdist => ?_⟩
  simpa only [discPull_ball, M03b.hdisc_val_mk] using
    h (HDisc.mk z hz) (HDisc.mk z' hz') r r' hr' hrr hr hdist

theorem measure_hypBall_le_of_hypDist_le (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ z ∈ 𝔻, ∀ w ∈ 𝔻, ∀ r : ℝ, 0 < r → r ≤ R₁ → hypDist z w ≤ r →
      μ (hypBall w r) ≤ C * μ (hypBall z r) := by
  obtain ⟨C, h⟩ := IsLocDoublingM.measure_ball_le_of_dist_le (M03b.isLocDoublingM_discPull hd) R₁
  refine ⟨C, fun z hz w hw r hr hr1 hdist => ?_⟩
  simpa only [discPull_ball, M03b.hdisc_val_mk] using h (HDisc.mk z hz) (HDisc.mk w hw) r hr hr1
      hdist

/-- **Lemma 2** (disc): Euclidean-porous sets (segments, lines, circles, horocycles, geodesic
arcs) meet `𝔻` in a null set. -/
theorem measure_inter_disc_eq_zero_of_isPorous (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {E : Set ℂ} (hE : IsPorous E) :
    μ (E ∩ 𝔻) = 0 := by
  have h1 := IsLocDoublingM.measure_eq_zero_of_isPorous (M03b.isLocDoublingM_discPull hd)
    (M03b.discPull_hfin hfin) hE.preimage_hDisc
  rw [discPull_apply] at h1
  have e : HDisc.val '' (HDisc.val ⁻¹' E) = E ∩ 𝔻 := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, a.2⟩
    · rintro ⟨hz, hz𝔻⟩
      exact ⟨HDisc.mk z hz𝔻, hz, rfl⟩
  rwa [e] at h1

theorem lemma2_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (a b : ℂ) : μ (segment ℝ a b ∩ 𝔻) = 0 :=
  measure_inter_disc_eq_zero_of_isPorous hd hfin (isPorous_segment a b)

theorem measure_hypSphere (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    μ {w | w ∈ 𝔻 ∧ hypDist z w = r} = 0 := by
  have h1 :=
      IsLocDoublingM.measure_sphere (M03b.isLocDoublingM_discPull hd) (M03b.discPull_hfin hfin)
    (HDisc.mk z hz) r
  rw [discPull_apply] at h1
  have e : HDisc.val '' sphere (HDisc.mk z hz) r = {w | w ∈ 𝔻 ∧ hypDist z w = r} := by
    ext w
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [mem_sphere, HDisc.dist_eq, hypDist_comm] at hb
      exact ⟨b.2, hb⟩
    · rintro ⟨hw, hwr⟩
      refine ⟨HDisc.mk w hw, ?_, rfl⟩
      rw [mem_sphere, HDisc.dist_eq, hypDist_comm]
      exact hwr
  rwa [e] at h1

theorem continuous_measure_hypBall (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {z : ℂ} (hz : z ∈ 𝔻) :
    Continuous fun r : ℝ ↦ μ (hypBall z r) := by
  have h1 := IsLocDoublingM.continuous_measure_ball (M03b.isLocDoublingM_discPull hd)
    (M03b.discPull_hfin hfin) (HDisc.mk z hz)
  simpa only [discPull_ball, M03b.hdisc_val_mk] using h1

theorem massRadiusDisc_pos (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {z : ℂ} (hz : z ∈ 𝔻) :
    0 < massRadiusDisc μ z := by
  rw [M03b.massRadiusDisc_eq' hz]
  exact IsLocDoublingM.massRadiusM_pos (M03b.isLocDoublingM_discPull hd) (M03b.discPull_hfin hfin)
    (M03b.discPull_hne hm _)

theorem massRadiusDisc_le {R : ℝ} (hR : 0 < R) (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {z : ℂ}
    (hz : z ∈ 𝔻) : massRadiusDisc μ z ≤ R := by
  rw [M03b.massRadiusDisc_eq' hz]
  exact massRadiusM_le hR (by rw [discPull_ball]; exact hm z hz)

theorem measure_hypBall_massRadiusDisc (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {z : ℂ} (hz : z ∈ 𝔻) :
    μ (hypBall z (massRadiusDisc μ z)) = 1 := by
  rw [M03b.massRadiusDisc_eq' hz]
  have := IsLocDoublingM.measure_ball_massRadiusM (M03b.isLocDoublingM_discPull hd)
    (M03b.discPull_hfin hfin) (M03b.discPull_hne hm (HDisc.mk z hz))
  rwa [discPull_ball] at this

theorem abs_massRadiusDisc_sub_le (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R))
    {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    |massRadiusDisc μ z - massRadiusDisc μ w| ≤ hypDist z w := by
  rw [M03b.massRadiusDisc_eq' hz, M03b.massRadiusDisc_eq' hw]
  have :=
      (lipschitzWith_massRadiusM (M03b.discPull_hne hm)).dist_le_mul (HDisc.mk z hz) (HDisc.mk w hw)
  rwa [Real.dist_eq, NNReal.coe_one, one_mul, M03b.hdisc_dist_mk] at this

theorem continuousOn_massRadiusDisc (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ContinuousOn (massRadiusDisc μ) 𝔻 := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (massRadiusM (discPull μ)) :=
    (lipschitzWith_massRadiusM (M03b.discPull_hne hm)).continuous
  exact hc.congr fun a ↦ (massRadiusDisc_eq μ a).symm

theorem measure_hypBall_massRadiusDisc_bounds (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ z ∈ 𝔻, ∀ r : ℝ,
      massRadiusDisc μ z ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusDisc μ z) ^ δ) ≤ μ (hypBall z r) ∧
        μ (hypBall z r) ≤ ENNReal.ofReal (C * (r / massRadiusDisc μ z) ^ s) := by
  obtain ⟨c, C, δ, s, hc, hC, hδ, hs, h⟩ := IsLocDoublingM.measure_ball_massRadiusM_bounds
    (M03b.isLocDoublingM_discPull hd) (M03b.discPull_hfin hfin) (M03b.discPull_hm hm) R₁
  refine ⟨c, C, δ, s, hc, hC, hδ, hs, fun z hz r h1 h2 => ?_⟩
  rw [M03b.massRadiusDisc_eq' hz] at h1 ⊢
  simpa only [discPull_ball, M03b.hdisc_val_mk] using h (HDisc.mk z hz) r h1 h2

theorem claim1_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ 𝔻, ∀ w ∈ 𝔻,
      hypDist z w ≤ K * max (massRadiusDisc μ z) (massRadiusDisc μ w) →
        massRadiusDisc μ z ≤ C * massRadiusDisc μ w := by
  obtain ⟨C, hC, h⟩ :=
      IsLocDoublingM.claim1 (M03b.isLocDoublingM_discPull hd) (M03b.discPull_hfin hfin)
    (M03b.discPull_hm hm) K
  refine ⟨C, hC, fun z hz w hw hdist => ?_⟩
  rw [M03b.massRadiusDisc_eq' hz, M03b.massRadiusDisc_eq' hw] at hdist ⊢
  exact h (HDisc.mk z hz) (HDisc.mk w hw) hdist

theorem lemma3_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w ∈ 𝔻,
      ∫⁻ z in hypBall w R₁,
        ENNReal.ofReal
          ((massRadiusDisc μ z / max (hypDist z w) (δ * massRadiusDisc μ w)) ^ m) ∂μ ≤ C := by
  obtain ⟨m₀, hm₀⟩ := IsLocDoublingM.lemma3 (M03b.isLocDoublingM_discPull hd)
    (M03b.discPull_hfin hfin) (M03b.discPull_hm hm)
  refine ⟨m₀, fun m hm δ R₁ hδ => ?_⟩
  obtain ⟨C, hC⟩ := hm₀ m hm δ R₁ hδ
  refine ⟨C, fun w hw => ?_⟩
  have key := hC (HDisc.mk w hw)
  rw [M03b.hypBall_eq_image_ball hw, ← M03b.lintegral_discPull]
  convert key using 3 with b
  rw [massRadiusDisc_eq, M03b.massRadiusDisc_eq' hw, HDisc.dist_eq, M03b.hdisc_val_mk]

theorem christ_lemma23_disc (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ z ∈ 𝔻, ∀ R : ℝ, 0 < R → R ≤ R₁ →
      ∫⁻ ζ in hypBall z R, ENNReal.ofReal (Real.log (R / hypDist z ζ)) ∂μ ≤
        C * μ (hypBall z R) := by
  obtain ⟨C, hC⟩ := IsLocDoublingM.christ_lemma23 (M03b.isLocDoublingM_discPull hd) R₁
  refine ⟨C, fun z hz R hR hR1 => ?_⟩
  have key := hC (HDisc.mk z hz) R hR hR1
  rw [discPull_ball, M03b.hdisc_val_mk] at key
  rw [M03b.hypBall_eq_image_ball hz, ← M03b.lintegral_discPull, ← M03b.hypBall_eq_image_ball hz]
  convert key using 3 with b
  rw [HDisc.dist_eq, M03b.hdisc_val_mk]

theorem exists_radius_lt_measure_hypBall
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (p : ℝ≥0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, (p : ℝ≥0∞) < μ (hypBall z r) := by
  obtain ⟨r, hr, h⟩ := exists_radius_lt_measure_ball (M03b.discPull_hm hm) p
  exact ⟨r, hr, fun z hz => by simpa only [discPull_ball, M03b.hdisc_val_mk] using h (HDisc.mk z
      hz)⟩

end Disc

/-! ### Line (intervals) -/

theorem M03b.measurableEmbedding_ofReal : MeasurableEmbedding (fun x : ℝ ↦ (x : ℂ)) :=
  Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding

theorem M03b.lineInterval_eq_image_ball (x r : ℝ) :
    lineInterval x r = (fun t : ℝ ↦ (t : ℂ)) '' ball x r := by
  rw [Real.ball_eq_Ioo]; rfl

theorem M03b.lintegral_linePull (μ : Measure ℂ) (g : ℂ → ℝ≥0∞) (s : Set ℝ) :
    ∫⁻ t in s, g (t : ℂ) ∂(linePull μ) = ∫⁻ z in (fun t : ℝ ↦ (t : ℂ)) '' s, g z ∂μ :=
  M03b.lintegral_comap_image M03b.measurableEmbedding_ofReal μ g s

theorem M03b.linePull_hfin {μ : Measure ℂ} (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞) :
    ∀ (x : ℝ) (r : ℝ), linePull μ (ball x r) < ∞ := fun x r ↦ by
  rw [linePull_ball]; exact hfin x r

theorem M03b.linePull_hm {μ : Measure ℂ} (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ linePull μ (ball x R) := by
  obtain ⟨R, hR, h⟩ := hm
  exact ⟨R, hR, fun x ↦ by rw [linePull_ball]; exact h x⟩

theorem M03b.linePull_hne {μ : Measure ℂ} (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R))
    (x : ℝ) : ∃ r, 0 < r ∧ 1 ≤ linePull μ (ball x r) := by
  obtain ⟨R, hR, h⟩ := M03b.linePull_hm hm
  exact ⟨R, hR, h x⟩

section Line
variable {μ : Measure ℂ}

theorem doubling_upTo_line (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x r : ℝ, 0 < r → r ≤ R₁ →
      μ (lineInterval x (2 * r)) ≤ C * μ (lineInterval x r) := by
  obtain ⟨C, hC, h⟩ := IsLocDoublingM.exists_const_of_le hd.isLocDoublingM R₁
  exact ⟨C, hC, fun x r hr hr1 ↦ by simpa only [linePull_ball] using h x r hr hr1⟩

theorem measure_lineInterval_le_rpow (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (x x' r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ → |x - x'| ≤ r →
      μ (lineInterval x r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (lineInterval x' r') := by
  obtain ⟨C, s, hC, hs, h⟩ := IsLocDoublingM.measure_ball_le_rpow hd.isLocDoublingM R₁
  refine ⟨C, s, hC, hs, fun x x' r r' hr' hrr hr hdist ↦ ?_⟩
  simpa only [linePull_ball] using h x x' r r' hr' hrr hr (by rwa [Real.dist_eq])

theorem rpow_le_measure_lineInterval (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (x x' r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ → |x - x'| ≤ r →
      ENNReal.ofReal (c * (r / r') ^ δ) * μ (lineInterval x' r') ≤ μ (lineInterval x r) := by
  obtain ⟨c, δ, hc, hδ, h⟩ := IsLocDoublingM.rpow_le_measure_ball hd.isLocDoublingM R₁
  refine ⟨c, δ, hc, hδ, fun x x' r r' hr' hrr hr hdist ↦ ?_⟩
  simpa only [linePull_ball] using h x x' r r' hr' hrr hr (by rwa [Real.dist_eq])

theorem measure_singleton_line (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞) (z : ℂ) : μ {z} = 0 := by
  by_cases hz : z.im = 0
  · have h1 := IsLocDoublingM.measure_singleton hd.isLocDoublingM (M03b.linePull_hfin hfin) z.re
    rw [linePull_apply, Set.image_singleton] at h1
    have e : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz])
    rwa [e] at h1
  · refine measure_mono_null (fun w hw ↦ ?_) hd.1
    rw [mem_singleton_iff] at hw
    subst hw
    exact hz

theorem continuous_measure_lineInterval (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞) (x : ℝ) :
    Continuous fun r : ℝ ↦ μ (lineInterval x r) := by
  simpa only [linePull_ball] using
    IsLocDoublingM.continuous_measure_ball hd.isLocDoublingM (M03b.linePull_hfin hfin) x

theorem massRadiusLine_pos (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (x : ℝ) :
    0 < massRadiusLine μ x := by
  rw [massRadiusLine_eq]
  exact IsLocDoublingM.massRadiusM_pos hd.isLocDoublingM (M03b.linePull_hfin hfin)
      (M03b.linePull_hne hm x)

theorem massRadiusLine_le {R : ℝ} (hR : 0 < R) (hm : ∀ x : ℝ, 1 ≤ μ (lineInterval x R))
    (x : ℝ) : massRadiusLine μ x ≤ R := by
  rw [massRadiusLine_eq]
  exact massRadiusM_le hR (by rw [linePull_ball]; exact hm x)

theorem measure_lineInterval_massRadiusLine (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (x : ℝ) :
    μ (lineInterval x (massRadiusLine μ x)) = 1 := by
  rw [massRadiusLine_eq, ← linePull_ball]
  exact IsLocDoublingM.measure_ball_massRadiusM hd.isLocDoublingM (M03b.linePull_hfin hfin)
    (M03b.linePull_hne hm x)

theorem lipschitzWith_massRadiusLine (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) :
    LipschitzWith 1 (massRadiusLine μ) := by
  have e : massRadiusLine μ = massRadiusM (linePull μ) := funext (massRadiusLine_eq μ)
  rw [e]
  exact lipschitzWith_massRadiusM (M03b.linePull_hne hm)

theorem measure_lineInterval_massRadiusLine_bounds (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ x r : ℝ,
      massRadiusLine μ x ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusLine μ x) ^ δ) ≤ μ (lineInterval x r) ∧
        μ (lineInterval x r) ≤ ENNReal.ofReal (C * (r / massRadiusLine μ x) ^ s) := by
  obtain ⟨c, C, δ, s, hc, hC, hδ, hs, h⟩ := IsLocDoublingM.measure_ball_massRadiusM_bounds
    hd.isLocDoublingM (M03b.linePull_hfin hfin) (M03b.linePull_hm hm) R₁
  refine ⟨c, C, δ, s, hc, hC, hδ, hs, fun x r h1 h2 ↦ ?_⟩
  rw [massRadiusLine_eq] at h1 ⊢
  simpa only [linePull_ball] using h x r h1 h2

theorem claim1_line (hd : IsLocallyDoublingLine μ) (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, |x - y| ≤ K * max (massRadiusLine μ x) (massRadiusLine μ y) →
      massRadiusLine μ x ≤ C * massRadiusLine μ y := by
  obtain ⟨C, hC, h⟩ := IsLocDoublingM.claim1 hd.isLocDoublingM (M03b.linePull_hfin hfin)
    (M03b.linePull_hm hm) K
  refine ⟨C, hC, fun x y hxy ↦ ?_⟩
  rw [massRadiusLine_eq, massRadiusLine_eq] at hxy ⊢
  exact h x y (by rwa [Real.dist_eq])

/-- **Lemma 3** on the line; the integral is over `μ` on `ℂ` (carried by `ℝ`). -/
theorem lemma3_line (hd : IsLocallyDoublingLine μ) (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ x : ℝ,
      ∫⁻ z in lineInterval x R₁,
        ENNReal.ofReal
          ((massRadiusLine μ z.re / max |z.re - x| (δ * massRadiusLine μ x)) ^ m) ∂μ ≤ C := by
  obtain ⟨m₀, hm₀⟩ := IsLocDoublingM.lemma3 hd.isLocDoublingM (M03b.linePull_hfin hfin)
    (M03b.linePull_hm hm)
  refine ⟨m₀, fun m hm δ R₁ hδ ↦ ?_⟩
  obtain ⟨C, hC⟩ := hm₀ m hm δ R₁ hδ
  refine ⟨C, fun x ↦ ?_⟩
  have key := hC x
  rw [M03b.lineInterval_eq_image_ball, ← M03b.lintegral_linePull]
  convert key using 3 with t
  rw [Complex.ofReal_re, massRadiusLine_eq, massRadiusLine_eq, Real.dist_eq]

theorem christ_lemma23_line (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ x R : ℝ, 0 < R → R ≤ R₁ →
      ∫⁻ z in lineInterval x R, ENNReal.ofReal (Real.log (R / |z.re - x|)) ∂μ ≤
        C * μ (lineInterval x R) := by
  obtain ⟨C, hC⟩ := IsLocDoublingM.christ_lemma23 hd.isLocDoublingM R₁
  refine ⟨C, fun x R hR hR1 ↦ ?_⟩
  have key := hC x R hR hR1
  rw [linePull_ball] at key
  rw [M03b.lineInterval_eq_image_ball, ← M03b.lintegral_linePull, ← M03b.lineInterval_eq_image_ball]
  convert key using 3 with t
  rw [Complex.ofReal_re, Real.dist_eq, abs_sub_comm]

theorem exists_radius_lt_measure_lineInterval
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (p : ℝ≥0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, (p : ℝ≥0∞) < μ (lineInterval x r) := by
  obtain ⟨r, hr, h⟩ := exists_radius_lt_measure_ball (M03b.linePull_hm hm) p
  exact ⟨r, hr, fun x ↦ by simpa only [linePull_ball] using h x⟩

end Line


/-! ### Decay and bounded count in `ℂ`-terms (coordinator additions) -/

theorem decay_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (z ζ : ℂ) (n : ℕ),
      2 ^ n * massRadius μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadius μ ζ / dist z ζ ≤ C * θ ^ n := IsLocDoublingM.decay (μ := μ) hd hfin hm M₀

theorem decay_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (z ζ : ℂ) (n : ℕ), z ∈ 𝔻 → ζ ∈ 𝔻 →
      2 ^ n * massRadiusDisc μ z ≤ hypDist z ζ → hypDist z ζ ≤ M₀ →
        massRadiusDisc μ ζ / hypDist z ζ ≤ C * θ ^ n := by
  obtain ⟨C, θ, hC, hθ, hθ1, h⟩ := IsLocDoublingM.decay (M03b.isLocDoublingM_discPull hd)
    (M03b.discPull_hfin hfin) (M03b.discPull_hm hm) M₀
  refine ⟨C, θ, hC, hθ, hθ1, fun z ζ n hz hζ h1 h2 => ?_⟩
  rw [M03b.massRadiusDisc_eq' hz] at h1
  rw [M03b.massRadiusDisc_eq' hζ]
  exact h (HDisc.mk z hz) (HDisc.mk ζ hζ) n h1 h2

theorem decay_line {μ : Measure ℂ} (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (x y : ℝ) (n : ℕ),
      2 ^ n * massRadiusLine μ x ≤ |x - y| → |x - y| ≤ M₀ →
        massRadiusLine μ y / |x - y| ≤ C * θ ^ n := by
  obtain ⟨C, θ, hC, hθ, hθ1, h⟩ := IsLocDoublingM.decay hd.isLocDoublingM
    (M03b.linePull_hfin hfin) (M03b.linePull_hm hm) M₀
  refine ⟨C, θ, hC, hθ, hθ1, fun x y n h1 h2 ↦ ?_⟩
  rw [massRadiusLine_eq] at h1
  rw [massRadiusLine_eq]
  rw [← Real.dist_eq] at h1 h2 ⊢
  exact h x y n h1 h2

/-- Bounded count in `ℂ` for convex sets (no upper size bound needed). -/
theorem encard_le_of_disjoint_convex (a b L : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set ℂ) (c : ι → ℂ) (r : ι → ℝ) (z : ℂ),
      Pairwise (Function.onFun Disjoint E) → (∀ i, Convex ℝ (E i)) → (∀ i, a ≤ r i) →
      (∀ i, ball (c i) (r i) ⊆ E i) → (∀ i, E i ⊆ ball (c i) (L * r i)) →
        {i | (E i ∩ ball z b).Nonempty}.encard ≤ M := by
  have hL1 : 0 < max L 0 + 1 := by linarith [le_max_right L 0]
  set a' := min a (b / (max L 0 + 1)) with ha'
  have ha'0 : 0 < a' := lt_min ha (div_pos hb hL1)
  obtain ⟨M, hM⟩ := BallGeometry.encard_le_of_disjoint (X := ℂ) a' b (4 * b) ha'0
  refine ⟨M, fun {ι} E c r z hdisj hconv har hin hout ↦ ?_⟩
  have hr : ∀ i, 0 < r i := fun i ↦ ha.trans_le (har i)
  let S : Set ι := {i | (E i ∩ ball z b).Nonempty}
  let p : S → ℂ := fun j ↦ Set.Nonempty.some (j.2 : (E j ∩ ball z b).Nonempty)
  have hp : ∀ j : S, p j ∈ E j ∩ ball z b := fun j ↦ Set.Nonempty.some_mem _
  let t : S → ℝ := fun j ↦ min 1 (b / (dist (c j) (p j) + r j))
  let c' : S → ℂ := fun j ↦ p j + t j • (c j - p j)
  have hdp : ∀ j : S, 0 < dist (c j) (p j) + r j := fun j ↦ by
    have := hr j; positivity
  have ht0 : ∀ j, 0 < t j := fun j ↦ lt_min one_pos (div_pos hb (hdp j))
  have ht1 : ∀ j, t j ≤ 1 := fun j ↦ min_le_left _ _
  have htb : ∀ j, t j * (dist (c j) (p j) + r j) ≤ b := fun j ↦ by
    calc t j * (dist (c j) (p j) + r j)
        ≤ b / (dist (c j) (p j) + r j) * (dist (c j) (p j) + r j) :=
          mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) _) (hdp j).le
      _ = b := div_mul_cancel₀ _ (hdp j).ne'
  have hrad : ∀ j, a' ≤ t j * r j := fun j ↦ by
    have hpc : dist (c j) (p j) < L * r j := by
      have := hout j (hp j).1
      rwa [mem_ball, dist_comm] at this
    have e : t j * r j = min (r j) (b / (dist (c j) (p j) + r j) * r j) := by
      rw [min_mul_of_nonneg _ _ (hr j).le, one_mul]
    rw [e]
    apply min_le_min (har j)
    rw [div_mul_eq_mul_div, le_div_iff₀ (hdp j)]
    have hLr : dist (c j) (p j) + r j ≤ (max L 0 + 1) * r j := by
      nlinarith [le_max_left L 0, hr j]
    calc b / (max L 0 + 1) * (dist (c j) (p j) + r j)
        ≤ b / (max L 0 + 1) * ((max L 0 + 1) * r j) := by gcongr
      _ = b * r j := by field_simp
  have hball : ∀ j : S, ball (c' j) (t j * r j) ⊆ E j ∩ ball z (2 * b) := by
    intro j w hw
    rw [mem_ball] at hw
    have htne := (ht0 j).ne'
    set u := p j + (t j)⁻¹ • (w - p j) with hu_def
    have hwu : w = p j + t j • (u - p j) := by
      rw [hu_def, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ htne, one_smul,
        add_sub_cancel]
    have hu : u ∈ ball (c j) (r j) := by
      rw [mem_ball, dist_eq_norm]
      have e : u - c j = (t j)⁻¹ • (w - c' j) := by
        simp only [hu_def, c', smul_sub, smul_add, smul_smul, inv_mul_cancel₀ htne, one_smul]
        abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (ht0 j), ← dist_eq_norm,
        inv_mul_lt_iff₀ (ht0 j)]
      exact hw
    refine ⟨?_, ?_⟩
    · rw [hwu]
      exact (hconv j).add_smul_sub_mem (hp j).1 (hin j hu) ⟨(ht0 j).le, ht1 j⟩
    · have h1 : dist w (p j) < b := by
        have e : dist w (p j) = t j * dist u (p j) := by
          rw [dist_eq_norm, dist_eq_norm, hwu, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos (ht0 j)]
        have hu' : dist u (p j) < r j + dist (c j) (p j) := by
          have := dist_triangle u (c j) (p j)
          rw [mem_ball] at hu
          linarith
        rw [e]
        calc t j * dist u (p j) < t j * (r j + dist (c j) (p j)) :=
              mul_lt_mul_of_pos_left hu' (ht0 j)
          _ ≤ b := by rw [add_comm]; exact htb j
      have h2 : dist (p j) z < b := (hp j).2
      rw [mem_ball]
      linarith [dist_triangle w (p j) z]
  have hc'z : ∀ j : S, dist (c' j) z < 2 * b := fun j ↦
    (hball j (mem_ball_self (mul_pos (ht0 j) (hr j)))).2
  have key := hM (fun j : S ↦ E j ∩ ball z (2 * b)) c' z
    (fun j k hjk ↦ (hdisj (Subtype.coe_injective.ne hjk)).mono inter_subset_left
      inter_subset_left)
    (fun j ↦ (ball_subset_ball (hrad j)).trans (hball j))
    (fun j w hw ↦ by
      have h1 : dist w z < 2 * b := hw.2
      rw [mem_ball]
      linarith [dist_triangle w z (c' j), dist_comm z (c' j), hc'z j])
  have huniv : {j : S | ((fun j : S ↦ E j ∩ ball z (2 * b)) j ∩ ball z b).Nonempty} = univ := by
    ext j
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨p j, ⟨(hp j).1, ball_subset_ball (by linarith) (hp j).2⟩, (hp j).2⟩
  rw [huniv, Set.encard_univ, ENat.card_coe_set_eq] at key
  exact key

/-- Bounded count in `𝔻` (hyperbolic balls). -/
theorem encard_le_of_disjoint_disc (a b D : ℝ) (ha : 0 < a) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set ℂ) (c : ι → ℂ) (z : ℂ), z ∈ 𝔻 → (∀ i, c i ∈ 𝔻) →
      Pairwise (Function.onFun Disjoint E) → (∀ i, hypBall (c i) a ⊆ E i) →
      (∀ i, E i ⊆ hypBall (c i) D) → {i | (E i ∩ hypBall z b).Nonempty}.encard ≤ M := by
  obtain ⟨M, hM⟩ := BallGeometry.encard_le_of_disjoint (X := HDisc) a b D ha
  refine ⟨M, fun {ι} E c z hz hc hdisj hin hout => ?_⟩
  have key := hM (fun i ↦ HDisc.val ⁻¹' E i) (fun i ↦ HDisc.mk (c i) (hc i)) (HDisc.mk z hz)
    (fun i j hij ↦ (hdisj hij).preimage _)
    (fun i x hx ↦ hin i (by
      rw [← M03b.hdisc_val_mk (c i) (hc i), ← HDisc.image_ball]; exact ⟨x, hx, rfl⟩))
    (fun i x hx ↦ by
      have := (hout i hx).2
      rw [mem_ball, HDisc.dist_eq, M03b.hdisc_val_mk, hypDist_comm]
      exact this)
  refine le_of_eq_of_le (congrArg _ ?_) key
  ext i
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨w, hwE, hwB⟩
    refine ⟨HDisc.mk w hwB.1, hwE, ?_⟩
    rw [mem_ball, HDisc.dist_eq, M03b.hdisc_val_mk, M03b.hdisc_val_mk, hypDist_comm]
    exact hwB.2
  · rintro ⟨x, hxE, hxB⟩
    refine ⟨x.val, hxE, x.2, ?_⟩
    rw [mem_ball, HDisc.dist_eq, M03b.hdisc_val_mk, hypDist_comm] at hxB
    exact hxB

/-- Bounded count in `ℂ` (Euclidean balls, bounded size). -/
theorem encard_le_of_disjoint_plane (a b D : ℝ) (ha : 0 < a) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set ℂ) (c : ι → ℂ) (z : ℂ),
      Pairwise (Function.onFun Disjoint E) → (∀ i, ball (c i) a ⊆ E i) →
      (∀ i, E i ⊆ ball (c i) D) → {i | (E i ∩ ball z b).Nonempty}.encard ≤ M :=
  BallGeometry.encard_le_of_disjoint a b D ha

theorem lineInterval_eq (x r : ℝ) :
    lineInterval x r = ball (x : ℂ) r ∩ range fun t : ℝ ↦ (t : ℂ) := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, t, rfl⟩
    rw [mem_ball, M03b.dist_ofReal_ofReal]
    rw [mem_Ioo] at ht
    exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  · rintro ⟨hz, t, rfl⟩
    rw [mem_ball, M03b.dist_ofReal_ofReal] at hz
    obtain ⟨h1, h2⟩ := abs_sub_lt_iff.1 hz
    exact ⟨t, ⟨by linarith, by linarith⟩, rfl⟩

/-! ### Requested by later modules (reconciliation additions) -/

/-- No atoms, plane (M04's (A4)). -/
theorem measure_singleton_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (z : ℂ) : μ {z} = 0 :=
  IsLocDoublingM.measure_singleton (μ := μ) hd hfin z

/-- No atoms, disc (M04's (A4')). -/
theorem measure_singleton_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {z : ℂ} (hz : z ∈ 𝔻) : μ {z} = 0 := by
  have h1 :=
      IsLocDoublingM.measure_singleton (M03b.isLocDoublingM_discPull hd) (M03b.discPull_hfin hfin)
    (HDisc.mk z hz)
  rw [discPull_apply, Set.image_singleton, M03b.hdisc_val_mk] at h1
  exact h1

/-- **Growth of hyperbolic balls, explicit radius**: if every hyperbolic ball of radius `r` has
mass `≥ m₀ > 0`, then every ball of radius `(2k + 1) r`, `k = ⌈M/m₀⌉₊`, has mass `> M`: it
contains `k + 1` disjoint balls of radius `r` centred on a geodesic through its centre.  No
doubling needed; the radius depends only on `r`, `m₀` and the target mass `M`, not on `μ`. -/
theorem ofReal_lt_measure_hypBall {μ : Measure ℂ} {r m₀ : ℝ} (hr : 0 < r) (hm₀ : 0 < m₀)
    (h : ∀ z ∈ 𝔻, ENNReal.ofReal m₀ ≤ μ (hypBall z r)) (M : ℝ) {z : ℂ} (hz : z ∈ 𝔻) :
    ENNReal.ofReal M < μ (hypBall z ((2 * ⌈M / m₀⌉₊ + 1) * r)) := by
  have hgrow := M03b.sum_le_measure_ball_of_le (μ := discPull μ) hr
    (fun y ↦ by rw [discPull_ball]; exact h _ y.2) (HDisc.mk z hz) ⌈M / m₀⌉₊
  rw [discPull_ball, M03b.hdisc_val_mk] at hgrow
  refine lt_of_lt_of_le ?_ hgrow
  have hk : M < (⌈M / m₀⌉₊ + 1 : ℝ) * m₀ := by
    have h1 := Nat.le_ceil (M / m₀)
    rw [div_le_iff₀ hm₀] at h1
    nlinarith
  rw [show ((⌈M / m₀⌉₊ : ℝ≥0∞) + 1) = ENNReal.ofReal (⌈M / m₀⌉₊ + 1 : ℝ) by
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one], ← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hk

/-- **Growth of hyperbolic balls** (M11 §2.1): a uniform positive lower bound on the balls of one
radius gives arbitrarily large mass on the balls of a larger radius.  No doubling needed. -/
theorem exists_hypBall_measure_gt {μ : Measure ℂ} {r m₀ : ℝ} (hr : 0 < r) (hm₀ : 0 < m₀)
    (h : ∀ z ∈ 𝔻, ENNReal.ofReal m₀ ≤ μ (hypBall z r)) (M : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, ENNReal.ofReal M < μ (hypBall z R) :=
  ⟨(2 * ⌈M / m₀⌉₊ + 1) * r, by positivity, fun _ hz ↦ ofReal_lt_measure_hypBall hr hm₀ h M hz⟩

section LogSmall

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Uniform smallness of `∫_{B(z,δ)} (A + log(1/d(z,ζ))) dμ` over a compact set, abstract form
(Christ's lemma at scale `1` plus the lower Lemma 1 bound `μ(B(z,δ)) ≲ δ^a μ(B(z,1))`). -/
theorem M03b.logSmall_aux [BallGeometry X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) {K : Set X} (hK : IsCompact K) {A η : ℝ}
    (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
      ∫⁻ ζ in ball z δ, ENNReal.ofReal (A + Real.log (1 / dist z ζ)) ∂μ ≤ ENNReal.ofReal η := by
  rcases K.eq_empty_or_nonempty with hKe | ⟨x₀, hx₀⟩
  · exact ⟨1, one_pos, le_rfl, fun z hz ↦ by simp [hKe] at hz⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x₀).1 hK.isBounded
  set M := (μ (ball x₀ (R + 2))).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hball : ∀ z ∈ K, μ (ball z 1) ≤ ENNReal.ofReal M := fun z hz ↦ by
    rw [hM, ENNReal.ofReal_toReal (hfin x₀ (R + 2)).ne]
    apply measure_mono
    intro w hw
    rw [mem_ball] at hw ⊢
    have := hR hz
    rw [mem_closedBall] at this
    linarith [dist_triangle w z x₀]
  obtain ⟨Cc, hCc⟩ := hd.christ_lemma23 1
  obtain ⟨c, a, hc, ha, hlow⟩ := hd.rpow_le_measure_ball 1
  have hlim : Filter.Tendsto (fun δ : ℝ ↦ (A + Real.log (1 / δ) + Cc) * δ ^ a)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun δ : ℝ ↦ δ ^ a) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
      rw [Real.zero_rpow ha.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := tendsto_log_mul_rpow_nhdsGT_zero ha
    have h3 := (h1.const_mul (A + Cc)).sub h2
    rw [mul_zero, sub_zero] at h3
    refine h3.congr fun δ ↦ ?_
    rw [one_div, Real.log_inv]
    ring
  set η' := η * c / (M + 1) with hη'
  have hη'0 : 0 < η' := by positivity
  obtain ⟨δ, hδ1, hδ2⟩ :=
    ((hlim.eventually (gt_mem_nhds hη'0)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hδ0 : 0 < δ := hδ2.1
  have hδle : δ ≤ 1 := hδ2.2.le
  refine ⟨δ, hδ0, hδle, fun z hz ↦ ?_⟩
  have hlogδ : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (one_le_one_div hδ0 hδle)
  set P := A + Real.log (1 / δ) + Cc with hP
  have hP0 : 0 ≤ P := by positivity
  -- pointwise splitting of the integrand
  have hpt : ∀ ζ ∈ ball z δ, ENNReal.ofReal (A + Real.log (1 / dist z ζ)) ≤
      ENNReal.ofReal (A + Real.log (1 / δ)) + ENNReal.ofReal (Real.log (δ / dist z ζ)) := by
    intro ζ hζ
    rw [mem_ball, dist_comm] at hζ
    rcases (dist_nonneg (x := z) (y := ζ)).eq_or_lt with hd0 | hd0
    · rw [← hd0, div_zero, Real.log_zero, add_zero]
      exact le_add_right (ENNReal.ofReal_le_ofReal (by linarith))
    · have hsplit : Real.log (1 / dist z ζ) = Real.log (1 / δ) + Real.log (δ / dist z ζ) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      have hl2 : 0 ≤ Real.log (δ / dist z ζ) :=
        Real.log_nonneg ((one_le_div hd0).2 hζ.le)
      rw [hsplit, ← add_assoc, ENNReal.ofReal_add (by linarith) hl2]
  -- mass of the small ball
  have hμB : μ (ball z δ) ≤ ENNReal.ofReal (δ ^ a / c) * ENNReal.ofReal M := by
    have h1 := hlow z z 1 δ hδ0 hδle le_rfl (by rw [dist_self]; norm_num)
    have hone : ENNReal.ofReal (δ ^ a / c) * ENNReal.ofReal (c * (1 / δ) ^ a) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have : δ ^ a / c * (c * (1 / δ) ^ a) = (δ * (1 / δ)) ^ a := by
        rw [Real.mul_rpow hδ0.le (by positivity)]
        field_simp
      rw [this, mul_one_div_cancel hδ0.ne', Real.one_rpow, ENNReal.ofReal_one]
    calc μ (ball z δ) = ENNReal.ofReal (δ ^ a / c) *
          (ENNReal.ofReal (c * (1 / δ) ^ a) * μ (ball z δ)) := by
          rw [← mul_assoc, hone, one_mul]
      _ ≤ ENNReal.ofReal (δ ^ a / c) * ENNReal.ofReal M := by
          gcongr
          exact h1.trans (hball z hz)
  calc ∫⁻ ζ in ball z δ, ENNReal.ofReal (A + Real.log (1 / dist z ζ)) ∂μ
      ≤ ∫⁻ ζ in ball z δ, (ENNReal.ofReal (A + Real.log (1 / δ)) +
          ENNReal.ofReal (Real.log (δ / dist z ζ))) ∂μ := setLIntegral_mono' measurableSet_ball hpt
    _ = ENNReal.ofReal (A + Real.log (1 / δ)) * μ (ball z δ) +
          ∫⁻ ζ in ball z δ, ENNReal.ofReal (Real.log (δ / dist z ζ)) ∂μ := by
        rw [lintegral_add_left measurable_const, setLIntegral_const]
    _ ≤ ENNReal.ofReal (A + Real.log (1 / δ)) * μ (ball z δ) + Cc * μ (ball z δ) := by
        gcongr; exact hCc z δ hδ0 hδle
    _ = ENNReal.ofReal P * μ (ball z δ) := by
        rw [← add_mul, hP, ENNReal.ofReal_add (by linarith) (NNReal.coe_nonneg Cc),
          ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal P * (ENNReal.ofReal (δ ^ a / c) * ENNReal.ofReal M) := by gcongr
    _ = ENNReal.ofReal (P * δ ^ a / c * M) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hP0]; ring_nf
    _ ≤ ENNReal.ofReal η := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : P * δ ^ a < η' := hδ1
        calc P * δ ^ a / c * M ≤ η' / c * M := by gcongr
          _ = η * (M / (M + 1)) := by rw [hη']; field_simp
          _ ≤ η * 1 := by gcongr; rw [div_le_one (by linarith)]; linarith
          _ = η := mul_one η

end LogSmall

/-- Uniform smallness of the logarithmic integral near a compact set (plane).  Moved here from
M04 (`Regularization.lean`), so that M08 can use it without depending on M04. -/
theorem logSmall_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ K : Set ℂ, IsCompact K → μ K < ∞) {K : Set ℂ} (hK : IsCompact K) {η : ℝ}
    (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
      ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂μ ≤ ENNReal.ofReal η := by
  have hfin' : ∀ (z : ℂ) (r : ℝ), μ (ball z r) < ∞ := fun z r ↦
    (measure_mono ball_subset_closedBall).trans_lt (hfin _ (isCompact_closedBall z r))
  obtain ⟨δ, hδ0, hδ1, h⟩ := M03b.logSmall_aux (μ := μ) hd hfin' hK zero_le_one hη
  exact ⟨δ, hδ0, hδ1, fun z hz ↦ by simpa only [dist_eq_norm] using h z hz⟩

/-- Uniform smallness of the logarithmic integral near a compact subset of `𝔻` (disc).  Moved
here from M04. -/
theorem logSmall_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ K ⊆ 𝔻, IsCompact K → μ K < ∞) {K : Set ℂ} (hK𝔻 : K ⊆ 𝔻) (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
      ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂μ ≤ ENNReal.ofReal η := by
  obtain ⟨t, ht0, ht1, hKt⟩ : ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ ∀ z ∈ K, ‖z‖ ≤ t := by
    rcases K.eq_empty_or_nonempty with hKe | hne
    · exact ⟨0, le_rfl, one_pos, fun z hz ↦ by simp [hKe] at hz⟩
    obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    exact ⟨‖z₀‖, norm_nonneg _, norm_lt_one_of_mem_disc (hK𝔻 hz₀), fun z hz ↦ hmax hz⟩
  have hfinD : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞ := fun z hz r ↦
    (measure_mono (M03b.hypBall_subset_closedBall_tanh hz r)).trans_lt
      (hfin _ (closedBall_subset_ball (Real.tanh_lt_one _)) (isCompact_closedBall _ _))
  have h1t : 0 < 1 - t := by linarith
  have hB1 : 1 ≤ 10 / (1 - t) := by rw [le_div_iff₀ h1t]; linarith
  have hlogB : 0 ≤ Real.log (10 / (1 - t)) := Real.log_nonneg hB1
  have hK' : IsCompact (HDisc.val ⁻¹' K) :=
    (Topology.IsInducing.subtypeVal (t := 𝔻)).isCompact_preimage' hK
      (by rw [Subtype.range_coe]; exact hK𝔻)
  obtain ⟨r, hr0, hr1, hint⟩ := M03b.logSmall_aux (M03b.isLocDoublingM_discPull hd)
    (M03b.discPull_hfin hfinD) hK' (A := 1 + Real.log (10 / (1 - t))) (by linarith) hη
  refine ⟨r * (1 - t) / 10, by positivity, ?_, fun z hz ↦ ?_⟩
  · rw [div_le_one (by norm_num)]
    nlinarith
  have hz𝔻 := hK𝔻 hz
  have hzt := hKt z hz
  have hsub : ball z (r * (1 - t) / 10) ⊆ hypBall z r :=
    (ball_subset_ball (by gcongr)).trans (ball_subset_hypBall hz𝔻 hr0 hr1)
  have hpt : ∀ ζ ∈ ball z (r * (1 - t) / 10),
      ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ≤
        ENNReal.ofReal (1 + Real.log (10 / (1 - t)) + Real.log (1 / hypDist z ζ)) := by
    intro ζ hζ
    have hζH := hsub hζ
    have hζ𝔻 : ζ ∈ 𝔻 := hζH.1
    apply ENNReal.ofReal_le_ofReal
    by_cases hζz : ζ = z
    · subst hζz
      rw [sub_self, norm_zero, hypDist_self, div_zero, Real.log_zero]
      linarith
    have hβ0 : 0 < hypDist z ζ := lt_of_le_of_ne (hypDist_nonneg z ζ)
      (fun h ↦ hζz ((hypDist_eq_zero_iff hz𝔻 hζ𝔻).1 h.symm).symm)
    have hβ1 : hypDist z ζ ≤ 1 := (hζH.2.trans_le hr1).le
    -- `‖z - ζ‖ ≥ β (1 - t) / 10`
    have hD := norm_one_sub_conj_mul_pos hz𝔻 hζ𝔻
    have hnorm : ‖z - ζ‖ = pseudoHyp z ζ * ‖1 - conj z * ζ‖ := by
      rw [pseudoHyp, div_mul_cancel₀ _ hD.ne']
    have htanh : hypDist z ζ / 5 ≤ pseudoHyp z ζ := by
      rw [← tanh_hypDist hz𝔻 hζ𝔻]; exact div_five_le_tanh hβ0.le hβ1
    have hζt : ‖ζ‖ ≤ (1 + t) / 2 := by
      have h1 : ‖ζ - z‖ < r * (1 - t) / 10 := by rw [← dist_eq_norm]; exact hζ
      have h2 : ‖ζ‖ ≤ ‖z‖ + ‖ζ - z‖ := by
        have := norm_add_le z (ζ - z); rwa [add_sub_cancel] at this
      nlinarith
    have hden : (1 - t) / 2 ≤ ‖1 - conj z * ζ‖ := by
      have := one_sub_mul_le_norm_one_sub_conj_mul z ζ
      have hz1 : ‖z‖ ≤ 1 := hzt.trans ht1.le
      nlinarith [norm_nonneg ζ, norm_nonneg z]
    have hlow : hypDist z ζ / (10 / (1 - t)) ≤ ‖z - ζ‖ := by
      rw [hnorm]
      calc hypDist z ζ / (10 / (1 - t)) = hypDist z ζ / 5 * ((1 - t) / 2) := by
            field_simp; ring
        _ ≤ pseudoHyp z ζ * ‖1 - conj z * ζ‖ :=
            mul_le_mul htanh hden (by linarith) (pseudoHyp_nonneg z ζ)
    have hpos : 0 < ‖z - ζ‖ := lt_of_lt_of_le (by positivity) hlow
    have hlog : Real.log (1 / ‖z - ζ‖) ≤ Real.log (10 / (1 - t) * (1 / hypDist z ζ)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hpos]
      rw [div_le_iff₀ (by positivity)] at hlow
      calc 1 = 10 / (1 - t) * (1 / hypDist z ζ) * (hypDist z ζ / (10 / (1 - t))) := by
            field_simp
        _ ≤ 10 / (1 - t) * (1 / hypDist z ζ) * ‖z - ζ‖ := by
            gcongr
            rw [div_le_iff₀ (by positivity)]
            linarith
    rw [Real.log_mul (by positivity) (by positivity)] at hlog
    linarith
  calc ∫⁻ ζ in ball z (r * (1 - t) / 10), ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂μ
      ≤ ∫⁻ ζ in ball z (r * (1 - t) / 10),
          ENNReal.ofReal (1 + Real.log (10 / (1 - t)) + Real.log (1 / hypDist z ζ)) ∂μ :=
        setLIntegral_mono' measurableSet_ball hpt
    _ ≤ ∫⁻ ζ in hypBall z r,
          ENNReal.ofReal (1 + Real.log (10 / (1 - t)) + Real.log (1 / hypDist z ζ)) ∂μ :=
        lintegral_mono_set hsub
    _ = ∫⁻ b in ball (HDisc.mk z hz𝔻) r,
          ENNReal.ofReal (1 + Real.log (10 / (1 - t)) + Real.log (1 / hypDist z b.val))
            ∂(discPull μ) := by
        rw [M03b.hypBall_eq_image_ball hz𝔻, ← M03b.lintegral_discPull]
    _ ≤ ENNReal.ofReal η := by
        have := hint (HDisc.mk z hz𝔻) hz
        convert this using 4 with b
        rw [HDisc.dist_eq, M03b.hdisc_val_mk]

end OC
