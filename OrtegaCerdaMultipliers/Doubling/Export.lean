import OrtegaCerdaMultipliers.Doubling.Line
import OrtegaCerdaMultipliers.Doubling.HypDisc

/-!
# M03 (Doubling) — The statements in `ℂ`-terms (plane, disc, line)

See `blueprint/M03_Doubling.md` §2.4.  Scaffold: statements, proofs `sorry`.

These are the `ℂ`-level statements consumed downstream, obtained from `Doubling/Abstract.lean`
through `ℂ`, `linePull` and `discPull`, and the finiteness bridge from `IsSubharmonicWeight`.
The last section adds the forms requested by M04 (`measure_singleton_*`, `logSmall_*`, the latter
moved from M04) and M11 (`exists_hypBall_measure_gt`).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ### Finiteness from `IsSubharmonicWeight` -/

theorem dist_ofReal_ofReal (x y : ℝ) : dist (x : ℂ) (y : ℂ) = |x - y| := by
  rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq]

/-- Hyperbolic balls lie in a Euclidean closed disc of radius `< 1` (hence in a compact subset
of `𝔻`). -/
theorem hypBall_subset_closedBall_tanh {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
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
    (h : IsSubharmonicWeight 𝔻 φ μ) {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) : μ (hypBall z r) < ∞ := (measure_mono (hypBall_subset_closedBall_tanh hz r)).trans_lt
    (h.finite_of_compact _ (closedBall_subset_ball (Real.tanh_lt_one _))
      (isCompact_closedBall _ _))

theorem IsSubharmonicWeight.measure_lineInterval_lt_top {φ : ℂ → ℝ} {μ : Measure ℂ}
    (h : IsSubharmonicWeight univ φ μ) (x r : ℝ) : μ (lineInterval x r) < ∞ := by
  refine (measure_mono ?_).trans_lt
    (h.finite_of_compact _ (subset_univ _) (isCompact_closedBall (x : ℂ) r))
  rintro _ ⟨t, ht, rfl⟩
  rw [mem_closedBall, dist_ofReal_ofReal]
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
        r / r' ≤ A * ((μ (ball z r)).toReal / (μ (ball z' r')).toReal) ^ (1 / γ) := IsLocDoublingM.lemma1 (μ := μ) hd R₁

theorem doubling_upTo_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ R₁ →
      μ (ball z (2 * r)) ≤ C * μ (ball z r) := IsLocDoublingM.exists_const_of_le (μ := μ) hd R₁

theorem measure_ball_le_rpow_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (z z' : ℂ) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist z z' ≤ r → μ (ball z r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (ball z' r') := IsLocDoublingM.measure_ball_le_rpow (μ := μ) hd R₁

theorem rpow_le_measure_ball_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (z z' : ℂ) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist z z' ≤ r → ENNReal.ofReal (c * (r / r') ^ δ) * μ (ball z' r') ≤ μ (ball z r) := IsLocDoublingM.rpow_le_measure_ball (μ := μ) hd R₁

theorem measure_ball_le_of_dist_le_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ z w : ℂ, ∀ r : ℝ, 0 < r → r ≤ R₁ → dist z w ≤ r →
      μ (ball w r) ≤ C * μ (ball z r) := IsLocDoublingM.measure_ball_le_of_dist_le (μ := μ) hd R₁

/-- **Lemma 2** (plane): porous sets, in particular lines, segments and circles, are null. -/
theorem measure_eq_zero_of_isPorous_plane (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) {E : Set ℂ} (hE : IsPorous E) : μ E = 0 := IsLocDoublingM.measure_eq_zero_of_isPorous (μ := μ) hd hfin hE

theorem lemma2_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞) (a b : ℂ) :
    μ (segment ℝ a b) = 0 := measure_eq_zero_of_isPorous_plane hd hfin (isPorous_segment a b)

theorem measure_sphere_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (z : ℂ) (r : ℝ) : μ (sphere z r) = 0 := IsLocDoublingM.measure_sphere (μ := μ) hd hfin z r

theorem continuous_measure_ball_plane (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (z : ℂ) : Continuous fun r : ℝ ↦ μ (ball z r) := IsLocDoublingM.continuous_measure_ball (μ := μ) hd hfin z

theorem massRadius_pos (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (z : ℂ) : 0 < massRadius μ z := IsLocDoublingM.massRadiusM_pos (μ := μ) hd hfin (let ⟨R, hR, h⟩ := hm; ⟨R, hR, h z⟩)

theorem massRadius_le {R : ℝ} (hR : 0 < R) (hm : ∀ z, 1 ≤ μ (ball z R)) (z : ℂ) :
    massRadius μ z ≤ R := massRadiusM_le hR (hm z)

theorem measure_ball_massRadius (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (z : ℂ) :
    μ (ball z (massRadius μ z)) = 1 := IsLocDoublingM.measure_ball_massRadiusM (μ := μ) hd hfin (let ⟨R, hR, h⟩ := hm; ⟨R, hR, h z⟩)

theorem lipschitzWith_massRadius (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) :
    LipschitzWith 1 (massRadius μ) := lipschitzWith_massRadiusM (μ := μ) fun z ↦ let ⟨R, hR, h⟩ := hm; ⟨R, hR, h z⟩

theorem measure_ball_massRadius_bounds_plane (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ (z : ℂ) (r : ℝ),
      massRadius μ z ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadius μ z) ^ δ) ≤ μ (ball z r) ∧
        μ (ball z r) ≤ ENNReal.ofReal (C * (r / massRadius μ z) ^ s) := IsLocDoublingM.measure_ball_massRadiusM_bounds (μ := μ) hd hfin hm R₁

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
      ∫⁻ ζ in ball z R, ENNReal.ofReal (Real.log (R / dist z ζ)) ∂μ ≤ C * μ (ball z R) := IsLocDoublingM.christ_lemma23 (μ := μ) hd R₁

theorem exists_radius_lt_measure_ball_plane (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R))
    (p : ℝ≥0) : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, (p : ℝ≥0∞) < μ (ball z r) := exists_radius_lt_measure_ball hm p

end Plane

/-! ### Disc (hyperbolic balls) -/

section Disc
variable {μ : Measure ℂ}

theorem lemma1_disc (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ γ A : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < A ∧
      ∀ (z z' : ℂ) (r r' : ℝ), z ∈ 𝔻 → z' ∈ 𝔻 → 0 < r' → r ≤ R₁ → hypDist z z' + r' ≤ r →
        0 < μ (hypBall z' r') → μ (hypBall z r) < ∞ →
        ((μ (hypBall z r)).toReal / (μ (hypBall z' r')).toReal) ^ γ ≤ A * (r / r') ∧
        r / r' ≤ A * ((μ (hypBall z r)).toReal / (μ (hypBall z' r')).toReal) ^ (1 / γ) := sorry

theorem doubling_upTo_disc (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → r ≤ R₁ →
      μ (hypBall z (2 * r)) ≤ C * μ (hypBall z r) := sorry

theorem measure_hypBall_le_rpow (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (z z' : ℂ) (r r' : ℝ), z ∈ 𝔻 → z' ∈ 𝔻 → 0 < r' → r' ≤ r →
      r ≤ R₁ → hypDist z z' ≤ r →
        μ (hypBall z r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (hypBall z' r') := sorry

theorem rpow_le_measure_hypBall (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (z z' : ℂ) (r r' : ℝ), z ∈ 𝔻 → z' ∈ 𝔻 → 0 < r' → r' ≤ r →
      r ≤ R₁ → hypDist z z' ≤ r →
        ENNReal.ofReal (c * (r / r') ^ δ) * μ (hypBall z' r') ≤ μ (hypBall z r) := sorry

theorem measure_hypBall_le_of_hypDist_le (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ z ∈ 𝔻, ∀ w ∈ 𝔻, ∀ r : ℝ, 0 < r → r ≤ R₁ → hypDist z w ≤ r →
      μ (hypBall w r) ≤ C * μ (hypBall z r) := sorry

/-- **Lemma 2** (disc): Euclidean-porous sets (segments, lines, circles, horocycles, geodesic
arcs) meet `𝔻` in a null set. -/
theorem measure_inter_disc_eq_zero_of_isPorous (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {E : Set ℂ} (hE : IsPorous E) :
    μ (E ∩ 𝔻) = 0 := sorry

theorem lemma2_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (a b : ℂ) : μ (segment ℝ a b ∩ 𝔻) = 0 := sorry

theorem measure_hypSphere (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    μ {w | w ∈ 𝔻 ∧ hypDist z w = r} = 0 := sorry

theorem continuous_measure_hypBall (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {z : ℂ} (hz : z ∈ 𝔻) :
    Continuous fun r : ℝ ↦ μ (hypBall z r) := sorry

theorem massRadiusDisc_pos (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {z : ℂ} (hz : z ∈ 𝔻) :
    0 < massRadiusDisc μ z := sorry

theorem massRadiusDisc_le {R : ℝ} (hR : 0 < R) (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {z : ℂ}
    (hz : z ∈ 𝔻) : massRadiusDisc μ z ≤ R := sorry

theorem measure_hypBall_massRadiusDisc (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {z : ℂ} (hz : z ∈ 𝔻) :
    μ (hypBall z (massRadiusDisc μ z)) = 1 := sorry

theorem abs_massRadiusDisc_sub_le (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R))
    {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    |massRadiusDisc μ z - massRadiusDisc μ w| ≤ hypDist z w := sorry

theorem continuousOn_massRadiusDisc (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ContinuousOn (massRadiusDisc μ) 𝔻 := sorry

theorem measure_hypBall_massRadiusDisc_bounds (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ z ∈ 𝔻, ∀ r : ℝ,
      massRadiusDisc μ z ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusDisc μ z) ^ δ) ≤ μ (hypBall z r) ∧
        μ (hypBall z r) ≤ ENNReal.ofReal (C * (r / massRadiusDisc μ z) ^ s) := sorry

theorem claim1_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ 𝔻, ∀ w ∈ 𝔻,
      hypDist z w ≤ K * max (massRadiusDisc μ z) (massRadiusDisc μ w) →
        massRadiusDisc μ z ≤ C * massRadiusDisc μ w := sorry

theorem lemma3_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w ∈ 𝔻,
      ∫⁻ z in hypBall w R₁,
        ENNReal.ofReal
          ((massRadiusDisc μ z / max (hypDist z w) (δ * massRadiusDisc μ w)) ^ m) ∂μ ≤ C :=
  sorry

theorem christ_lemma23_disc (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ z ∈ 𝔻, ∀ R : ℝ, 0 < R → R ≤ R₁ →
      ∫⁻ ζ in hypBall z R, ENNReal.ofReal (Real.log (R / hypDist z ζ)) ∂μ ≤
        C * μ (hypBall z R) := sorry

theorem exists_radius_lt_measure_hypBall
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (p : ℝ≥0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, (p : ℝ≥0∞) < μ (hypBall z r) := sorry

end Disc

/-! ### Line (intervals) -/

section Line
variable {μ : Measure ℂ}

theorem doubling_upTo_line (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x r : ℝ, 0 < r → r ≤ R₁ →
      μ (lineInterval x (2 * r)) ≤ C * μ (lineInterval x r) := sorry

theorem measure_lineInterval_le_rpow (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (x x' r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ → |x - x'| ≤ r →
      μ (lineInterval x r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (lineInterval x' r') :=
  sorry

theorem rpow_le_measure_lineInterval (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (x x' r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ → |x - x'| ≤ r →
      ENNReal.ofReal (c * (r / r') ^ δ) * μ (lineInterval x' r') ≤ μ (lineInterval x r) :=
  sorry

theorem measure_singleton_line (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞) (z : ℂ) : μ {z} = 0 := sorry

theorem continuous_measure_lineInterval (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞) (x : ℝ) :
    Continuous fun r : ℝ ↦ μ (lineInterval x r) := sorry

theorem massRadiusLine_pos (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (x : ℝ) :
    0 < massRadiusLine μ x := sorry

theorem massRadiusLine_le {R : ℝ} (hR : 0 < R) (hm : ∀ x : ℝ, 1 ≤ μ (lineInterval x R))
    (x : ℝ) : massRadiusLine μ x ≤ R := sorry

theorem measure_lineInterval_massRadiusLine (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (x : ℝ) :
    μ (lineInterval x (massRadiusLine μ x)) = 1 := sorry

theorem lipschitzWith_massRadiusLine (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) :
    LipschitzWith 1 (massRadiusLine μ) := sorry

theorem measure_lineInterval_massRadiusLine_bounds (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ x r : ℝ,
      massRadiusLine μ x ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusLine μ x) ^ δ) ≤ μ (lineInterval x r) ∧
        μ (lineInterval x r) ≤ ENNReal.ofReal (C * (r / massRadiusLine μ x) ^ s) := sorry

theorem claim1_line (hd : IsLocallyDoublingLine μ) (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, |x - y| ≤ K * max (massRadiusLine μ x) (massRadiusLine μ y) →
      massRadiusLine μ x ≤ C * massRadiusLine μ y := sorry

/-- **Lemma 3** on the line; the integral is over `μ` on `ℂ` (carried by `ℝ`). -/
theorem lemma3_line (hd : IsLocallyDoublingLine μ) (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ x : ℝ,
      ∫⁻ z in lineInterval x R₁,
        ENNReal.ofReal
          ((massRadiusLine μ z.re / max |z.re - x| (δ * massRadiusLine μ x)) ^ m) ∂μ ≤ C :=
  sorry

theorem christ_lemma23_line (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ x R : ℝ, 0 < R → R ≤ R₁ →
      ∫⁻ z in lineInterval x R, ENNReal.ofReal (Real.log (R / |z.re - x|)) ∂μ ≤
        C * μ (lineInterval x R) := sorry

theorem exists_radius_lt_measure_lineInterval
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (p : ℝ≥0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, (p : ℝ≥0∞) < μ (lineInterval x r) := sorry

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
        massRadiusDisc μ ζ / hypDist z ζ ≤ C * θ ^ n := sorry

theorem decay_line {μ : Measure ℂ} (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (x y : ℝ) (n : ℕ),
      2 ^ n * massRadiusLine μ x ≤ |x - y| → |x - y| ≤ M₀ →
        massRadiusLine μ y / |x - y| ≤ C * θ ^ n := sorry

/-- Bounded count in `ℂ` for convex sets (no upper size bound needed). -/
theorem encard_le_of_disjoint_convex (a b L : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set ℂ) (c : ι → ℂ) (r : ι → ℝ) (z : ℂ),
      Pairwise (Function.onFun Disjoint E) → (∀ i, Convex ℝ (E i)) → (∀ i, a ≤ r i) →
      (∀ i, ball (c i) (r i) ⊆ E i) → (∀ i, E i ⊆ ball (c i) (L * r i)) →
        {i | (E i ∩ ball z b).Nonempty}.encard ≤ M := sorry

/-- Bounded count in `𝔻` (hyperbolic balls). -/
theorem encard_le_of_disjoint_disc (a b D : ℝ) (ha : 0 < a) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set ℂ) (c : ι → ℂ) (z : ℂ), z ∈ 𝔻 → (∀ i, c i ∈ 𝔻) →
      Pairwise (Function.onFun Disjoint E) → (∀ i, hypBall (c i) a ⊆ E i) →
      (∀ i, E i ⊆ hypBall (c i) D) → {i | (E i ∩ hypBall z b).Nonempty}.encard ≤ M := sorry

/-- Bounded count in `ℂ` (Euclidean balls, bounded size). -/
theorem encard_le_of_disjoint_plane (a b D : ℝ) (ha : 0 < a) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set ℂ) (c : ι → ℂ) (z : ℂ),
      Pairwise (Function.onFun Disjoint E) → (∀ i, ball (c i) a ⊆ E i) →
      (∀ i, E i ⊆ ball (c i) D) → {i | (E i ∩ ball z b).Nonempty}.encard ≤ M := BallGeometry.encard_le_of_disjoint a b D ha

theorem lineInterval_eq (x r : ℝ) :
    lineInterval x r = ball (x : ℂ) r ∩ range fun t : ℝ ↦ (t : ℂ) := sorry

/-! ### Requested by later modules (reconciliation additions) -/

/-- No atoms, plane (M04's (A4)). -/
theorem measure_singleton_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (z : ℂ) : μ {z} = 0 := IsLocDoublingM.measure_singleton (μ := μ) hd hfin z

/-- No atoms, disc (M04's (A4')). -/
theorem measure_singleton_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {z : ℂ} (hz : z ∈ 𝔻) : μ {z} = 0 := sorry

/-- **Growth of hyperbolic balls, explicit radius**: if every hyperbolic ball of radius `r` has
mass `≥ m₀ > 0`, then every ball of radius `(2k + 1) r`, `k = ⌈M/m₀⌉₊`, has mass `> M`: it
contains `k + 1` disjoint balls of radius `r` centred on a geodesic through its centre.  No
doubling needed; the radius depends only on `r`, `m₀` and the target mass `M`, not on `μ`. -/
theorem ofReal_lt_measure_hypBall {μ : Measure ℂ} {r m₀ : ℝ} (hr : 0 < r) (hm₀ : 0 < m₀)
    (h : ∀ z ∈ 𝔻, ENNReal.ofReal m₀ ≤ μ (hypBall z r)) (M : ℝ) {z : ℂ} (hz : z ∈ 𝔻) :
    ENNReal.ofReal M < μ (hypBall z ((2 * ⌈M / m₀⌉₊ + 1) * r)) := sorry

/-- **Growth of hyperbolic balls** (M11 §2.1): a uniform positive lower bound on the balls of one
radius gives arbitrarily large mass on the balls of a larger radius.  No doubling needed. -/
theorem exists_hypBall_measure_gt {μ : Measure ℂ} {r m₀ : ℝ} (hr : 0 < r) (hm₀ : 0 < m₀)
    (h : ∀ z ∈ 𝔻, ENNReal.ofReal m₀ ≤ μ (hypBall z r)) (M : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, ENNReal.ofReal M < μ (hypBall z R) :=
  ⟨(2 * ⌈M / m₀⌉₊ + 1) * r, by positivity, fun _ hz ↦ ofReal_lt_measure_hypBall hr hm₀ h M hz⟩

/-- Uniform smallness of the logarithmic integral near a compact set (plane).  Moved here from
M04 (`Regularization.lean`), so that M08 can use it without depending on M04. -/
theorem logSmall_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ K : Set ℂ, IsCompact K → μ K < ∞) {K : Set ℂ} (hK : IsCompact K) {η : ℝ}
    (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
      ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂μ ≤ ENNReal.ofReal η :=
  sorry

/-- Uniform smallness of the logarithmic integral near a compact subset of `𝔻` (disc).  Moved
here from M04. -/
theorem logSmall_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ K ⊆ 𝔻, IsCompact K → μ K < ∞) {K : Set ℂ} (hK𝔻 : K ⊆ 𝔻) (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
      ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂μ ≤ ENNReal.ofReal η :=
  sorry

end OC
