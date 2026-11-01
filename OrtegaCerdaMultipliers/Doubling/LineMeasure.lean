import OrtegaCerdaMultipliers.Doubling.Export

/-!
# M03 (Doubling) — Line forms requested by M13 (`IsLineMeasure`, L1–L8)

See `blueprint/M13_Theorem5.md` §4.2 and `blueprint/M03_Doubling.md` §4.  Scaffold: statements,
proofs `sorry` (a few are short term proofs from `Doubling/Export.lean`); the structure is real.

M13 bundles the standing hypotheses on the Riesz measure `μ` of a weight whose Laplacian is
carried by `ℝ` (`IsLineMeasure`) and needs the line forms of Lemma 1, Claim 1, Claim 2,
[Chr91, Lemma 2.3], reverse doubling and no atoms (L1–L8).  They are stated here, upstream of
M13, as the reconciliation asked for.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Standing hypotheses of §4.3 on the Riesz measure `μ` (bundled for brevity). -/
structure IsLineMeasure (μ : Measure ℂ) : Prop where
  finite_of_compact : ∀ K : Set ℂ, IsCompact K → μ K < ∞
  doubling : IsLocallyDoublingLine μ
  mass : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)

/-- From the hypotheses of `theorem5` (proved). -/
theorem IsLineMeasure.of_weight {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoublingLine μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) :
    IsLineMeasure μ :=
  ⟨fun K hK ↦ hφ.finite_of_compact K (subset_univ K) hK, hd, hm⟩

theorem IsLineMeasure.hfin {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x r : ℝ) :
    μ (lineInterval x r) < ∞ := by
  rw [lineInterval_eq]
  exact (measure_mono (inter_subset_left.trans ball_subset_closedBall)).trans_lt
    (hμ.finite_of_compact _ (isCompact_closedBall _ _))

theorem IsLineMeasure.hm {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R) := by
  obtain ⟨r, hr, h⟩ := hμ.mass
  exact ⟨r, hr, fun x ↦ (h x).le⟩

/-! (L1) local doubling at every bounded scale. -/
theorem IsLineMeasure.doubling_le {μ : Measure ℂ} (hμ : IsLineMeasure μ) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x r : ℝ, 0 < r → r ≤ A →
      μ (lineInterval x (2 * r)) ≤ C * μ (lineInterval x r) :=
  doubling_upTo_line hμ.doubling A

/-! (L2) intervals have positive finite mass; no atoms. -/
theorem IsLineMeasure.lineInterval_pos {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) {r : ℝ}
    (hr : 0 < r) : 0 < μ (lineInterval x r) := by
  rw [← linePull_ball]
  exact IsLocDoublingM.measure_ball_pos hμ.doubling.isLocDoublingM (linePull_hm hμ.hm) x hr
theorem IsLineMeasure.lineInterval_lt_top {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x r : ℝ) :
    μ (lineInterval x r) < ∞ := hμ.hfin x r
theorem IsLineMeasure.measure_singleton {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) :
    μ {(x : ℂ)} = 0 := measure_singleton_line hμ.doubling hμ.hfin x

/-! (L3) reverse doubling at every bounded scale. -/
theorem IsLineMeasure.reverse_doubling {μ : Measure ℂ} (hμ : IsLineMeasure μ) {A : ℝ}
    (hA : 0 < A) :
    ∃ q : ℝ≥0, q < 1 ∧ ∀ x r : ℝ, 0 < r → r ≤ A →
      μ (lineInterval x (r / 2)) ≤ q * μ (lineInterval x r) := by
  obtain ⟨η, hη, h⟩ := IsLocDoublingM.reverse_doubling hμ.doubling.isLocDoublingM A
  refine ⟨(1 + η)⁻¹, ?_, fun x r hr hrA ↦ ?_⟩
  · rw [inv_lt_one₀ (by positivity)]
    exact lt_add_of_pos_right 1 hη
  · have key := h x (r / 2) (by positivity) (by linarith)
    rw [linePull_ball, linePull_ball, show 2 * (r / 2) = r by ring] at key
    have hne : (1 + η : ℝ≥0) ≠ 0 := by positivity
    calc μ (lineInterval x (r / 2))
        = ((1 + η)⁻¹ : ℝ≥0) * (((1 + η : ℝ≥0) : ℝ≥0∞) * μ (lineInterval x (r / 2))) := by
          rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hne, ENNReal.coe_one, one_mul]
      _ ≤ ((1 + η)⁻¹ : ℝ≥0) * μ (lineInterval x r) := by
          gcongr
          push_cast
          exact key

/-! (L4) the mass radius `ρ` on the line. -/
theorem IsLineMeasure.massRadiusLine_pos {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) :
    0 < massRadiusLine μ x := OC.massRadiusLine_pos hμ.doubling hμ.hfin hμ.hm x
theorem massRadiusLine_le_of_mass {μ : Measure ℂ} {r : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (x : ℝ) : massRadiusLine μ x ≤ r :=
  massRadiusLine_le hr (fun y ↦ (hmr y).le) x
theorem IsLineMeasure.measure_massRadiusLine {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) :
    μ (lineInterval x (massRadiusLine μ x)) = 1 := measure_lineInterval_massRadiusLine hμ.doubling hμ.hfin hμ.hm x

/-! (L5) Claim 1 on the line. -/
theorem IsLineMeasure.massRadiusLine_comparable {μ : Measure ℂ} (hμ : IsLineMeasure μ) {K : ℝ}
    (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x t : ℝ, |x - t| ≤ K * max (massRadiusLine μ x) (massRadiusLine μ t) →
      massRadiusLine μ t ≤ C * massRadiusLine μ x := by
  obtain ⟨C, hC, h⟩ := claim1_line hμ.doubling hμ.hfin hμ.hm K
  refine ⟨max C 1, le_max_right _ _, fun x t hxt ↦ ?_⟩
  have := h t x (by rwa [abs_sub_comm, max_comm])
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (hμ.massRadiusLine_pos x).le)

/-! (L6) Lemma 1 on the line: sublinear growth of `ρ`. -/
theorem IsLineMeasure.massRadiusLine_le_rpow {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ γ C : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < C ∧ ∀ x t : ℝ, massRadiusLine μ x ≤ |x - t| → |x - t| ≤ 1 →
      massRadiusLine μ t ≤ C * massRadiusLine μ x ^ γ * |x - t| ^ (1 - γ) := by
  obtain ⟨C, α, hC, hα, hα1, h⟩ := IsLocDoublingM.massRadiusM_div_dist_le
    hμ.doubling.isLocDoublingM (linePull_hfin hμ.hfin) (linePull_hm hμ.hm) 1
  refine ⟨α, C, hα, hα1, hC, fun x t h1 h2 ↦ ?_⟩
  have hρx := hμ.massRadiusLine_pos x
  have hd : 0 < |x - t| := hρx.trans_le h1
  have key := h x t (by rwa [← massRadiusLine_eq, Real.dist_eq])
    (by rwa [Real.dist_eq])
  rw [← massRadiusLine_eq, ← massRadiusLine_eq, Real.dist_eq] at key
  have k2 := (div_le_iff₀ hd).1 key
  calc massRadiusLine μ t ≤ C * (massRadiusLine μ x / |x - t|) ^ α * |x - t| := k2
    _ = C * massRadiusLine μ x ^ α * |x - t| ^ (1 - α) := by
      rw [Real.div_rpow hρx.le hd.le, Real.rpow_sub hd, Real.rpow_one]
      field_simp

/-! (L7) Claim 2 on the line: an interval of mass in `[m₁, m₂]`, `m₁ ≥ 1`, has length `≃ ρ`. -/
theorem IsLineMeasure.length_comparable {μ : Measure ℂ} (hμ : IsLineMeasure μ) {m₁ m₂ : ℝ}
    (hm₁ : 1 ≤ m₁) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : ℝ, a < b →
      ENNReal.ofReal m₁ ≤ μ ((fun t : ℝ ↦ (t : ℂ)) '' Ioc a b) →
      μ ((fun t : ℝ ↦ (t : ℂ)) '' Ioc a b) ≤ ENNReal.ofReal m₂ →
      ∀ t ∈ Icc a b, massRadiusLine μ t ≤ b - a ∧ b - a ≤ C * massRadiusLine μ t := by
  obtain ⟨r₂, hr₂, hgrow⟩ := exists_radius_lt_measure_lineInterval hμ.hm m₂.toNNReal
  obtain ⟨c, δ, hc, hδ, hlow⟩ := rpow_le_measure_lineInterval hμ.doubling r₂
  refine ⟨max 4 (2 * (m₂ / c) ^ (1 / δ)), le_trans (by norm_num) (le_max_left _ _),
    fun a b hab h1 h2 t ht ↦ ?_⟩
  set L := b - a with hLdef
  have hL : 0 < L := sub_pos.2 hab
  set J := (fun t : ℝ ↦ (t : ℂ)) '' Ioc a b with hJ
  -- the open interval has the same mass (no atoms)
  have hIoo : μ J ≤ μ ((fun t : ℝ ↦ (t : ℂ)) '' Ioo a b) := by
    have e : Ioc a b = Ioo a b ∪ {b} := (Ioo_union_right hab).symm
    rw [hJ, e, image_union, image_singleton]
    refine (measure_union_le _ _).trans ?_
    rw [hμ.measure_singleton b, add_zero]
  have hm1 : (1 : ℝ≥0∞) ≤ μ J := by
    refine le_trans ?_ h1
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hm₁
  have hm₂ : 1 ≤ m₂ := by
    have := hm1.trans h2
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff'] at this
    rcases this with h | h
    · exact h
    · norm_num at h
  have hρt := hμ.massRadiusLine_pos t
  refine ⟨?_, ?_⟩
  · -- `ρ(t) ≤ L`
    have hsub : (fun t : ℝ ↦ (t : ℂ)) '' Ioo a b ⊆ lineInterval t L := by
      apply image_mono
      intro u hu
      exact ⟨by linarith [hu.1, ht.2], by linarith [hu.2, ht.1]⟩
    have hmass : 1 ≤ μ (lineInterval t L) := hm1.trans (hIoo.trans (measure_mono hsub))
    exact csInf_le ⟨0, fun r hr ↦ hr.1.le⟩ ⟨hL, hmass⟩
  · -- `L ≤ C ρ(t)`
    have hmid : lineInterval ((a + b) / 2) (L / 2) = (fun t : ℝ ↦ (t : ℂ)) '' Ioo a b := by
      rw [lineInterval]
      congr 2 <;> ring
    have hmidJ : μ (lineInterval ((a + b) / 2) (L / 2)) ≤ ENNReal.ofReal m₂ := by
      rw [hmid]
      exact (measure_mono (image_mono Ioo_subset_Ioc_self)).trans h2
    have hLr : L / 2 < r₂ := by
      by_contra hcon
      replace hcon := not_lt.1 hcon
      have hsub : lineInterval ((a + b) / 2) r₂ ⊆ lineInterval ((a + b) / 2) (L / 2) := by
        apply image_mono
        intro u hu
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have := (hgrow ((a + b) / 2)).trans_le ((measure_mono hsub).trans hmidJ)
      rw [ENNReal.ofReal] at this
      exact lt_irrefl _ this
    by_cases hcase : L ≤ 4 * massRadiusLine μ t
    · exact hcase.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρt.le)
    replace hcase := not_le.1 hcase
    have key := hlow ((a + b) / 2) t (L / 2) (massRadiusLine μ t) hρt (by linarith) hLr.le
      (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
    rw [measure_lineInterval_massRadiusLine hμ.doubling hμ.hfin hμ.hm t, mul_one] at key
    have key2 := (key.trans hmidJ)
    rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at key2
    set q := L / 2 / massRadiusLine μ t with hq
    have hq0 : 0 ≤ q := by positivity
    have hqδ : q ^ δ ≤ m₂ / c := by rw [le_div_iff₀ hc]; linarith
    have hq1 : q ≤ (m₂ / c) ^ (1 / δ) := le_rpow_one_div_of_rpow_le hq0 hδ hqδ
    have : L = 2 * q * massRadiusLine μ t := by rw [hq]; field_simp
    rw [this]
    calc 2 * q * massRadiusLine μ t ≤ 2 * (m₂ / c) ^ (1 / δ) * massRadiusLine μ t := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hρt.le

/-! (L8) [Chr91, Lemma 2.3] on the line: uniform logarithmic integrability. -/
theorem IsLineMeasure.lintegral_log_le {μ : Measure ℂ} (hμ : IsLineMeasure μ) {A : ℝ}
    (hA : 0 < A) :
    ∃ C : ℝ≥0, ∀ x R : ℝ, 0 < R → R ≤ A →
      ∫⁻ ζ in lineInterval x R, ENNReal.ofReal (Real.log (R / ‖ζ - (x : ℂ)‖)) ∂μ ≤
        C * μ (lineInterval x R) := by
  obtain ⟨C, hC⟩ := christ_lemma23_line hμ.doubling A
  refine ⟨C, fun x R hR hRA ↦ ?_⟩
  refine le_of_eq_of_le (setLIntegral_congr_fun ?_ fun ζ hζ ↦ ?_) (hC x R hR hRA)
  · rw [lineInterval_eq_image_ball]
    exact measurableEmbedding_ofReal.measurableSet_image.2 measurableSet_ball
  · obtain ⟨t, -, rfl⟩ := hζ
    simp only [Complex.ofReal_re]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

end OC
