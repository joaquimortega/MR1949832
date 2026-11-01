import OrtegaCerdaMultipliers.SeveralMultipliers
import OrtegaCerdaMultipliers.Regularization
import OrtegaCerdaMultipliers.ModelKernels

/-!
# M11 (Theorem2) — Theorem 2 (disc): weighted `L^p` and sup estimates; the bridge to BOC

See `blueprint/M11_Theorem2.md`.  Scaffold: statements, proofs `sorry`; definitions are real.
`theorem2`, `theorem2_uniform`, `theorem2_printed` are verbatim from
`comparator/statements.lean`.  `theorem2_uniform` is proved from the uniform kernel
`exists_disc_solution_kernel_quant` and M10's `disc_kernel_operator`; `theorem2` is proved from
`theorem2_uniform`.  The uniform kernel comes from `exists_aux_weight_disc_quant` (built on M04's
`lemma6_disc_quant` and M03's explicit-radius growth lemma) and M09's `prop2_disc_quant`.

Reconciliation (consumed from upstream): `hypArea` (M01), `lemma6_disc_hypArea` (M04, corollary
of `lemma6_disc`), `exists_hypBall_measure_gt` (M03), `prop2_disc_full`,
`exists_measurable_partition`, `prop2_disc_unif` (M09), `Measure.exists_add_eq_of_le` (M04),
`IsSubharmonicWeight.sigmaFinite`, `integral_mul_laplacian_of_contDiffOn` (M02),
`disc_kernel_operator` (M10).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ## Measure-theoretic helpers -/

theorem measurable_hypAreaDensity :
    Measurable fun z : ℂ ↦ ENNReal.ofReal ((1 - ‖z‖ ^ 2)⁻¹ ^ 2) := by
  fun_prop

theorem hypArea_lt_top_of_isCompact {K : Set ℂ} (hK : K ⊆ 𝔻) (hKc : IsCompact K) :
    hypArea K < ∞ := by
  obtain ⟨r', hr'1, hKr'⟩ := exists_lt_subset_ball hKc.isClosed hK
  calc hypArea K ≤ hypArea (ball 0 r') := measure_mono hKr'
    _ = ∫⁻ z in ball 0 r' ∩ 𝔻, ENNReal.ofReal ((1 - ‖z‖ ^ 2)⁻¹ ^ 2) := by
        rw [hypArea, withDensity_apply _ measurableSet_ball, Measure.restrict_restrict
          measurableSet_ball]
    _ ≤ ∫⁻ _ in ball 0 r' ∩ 𝔻, ENNReal.ofReal ((1 - r' ^ 2)⁻¹ ^ 2) := by
        apply setLIntegral_mono measurable_const
        intro z hz
        apply ENNReal.ofReal_le_ofReal
        have hz' : ‖z‖ < r' := by simpa using hz.1
        have hz0 := norm_nonneg z
        have h1 : 0 < 1 - r' ^ 2 := by nlinarith
        have h2 : 1 - r' ^ 2 ≤ 1 - ‖z‖ ^ 2 := by nlinarith
        have h3 : 0 ≤ (1 - ‖z‖ ^ 2)⁻¹ := inv_nonneg.2 (by linarith)
        gcongr
    _ = ENNReal.ofReal ((1 - r' ^ 2)⁻¹ ^ 2) * volume (ball 0 r' ∩ 𝔻) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top)

/-- A continuous function with compact support in `𝔻` is integrable against any measure that is
finite on the compact subsets of `𝔻`. -/
theorem integrable_of_tsupport_subset_disc {μ : Measure ℂ}
    (hμ : ∀ K ⊆ 𝔻, IsCompact K → μ K < ∞) {χ : ℂ → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ 𝔻) : Integrable χ μ := by
  have hfin : μ (tsupport χ) < ∞ := hμ _ hs hc
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hc
  rw [← integrableOn_iff_integrable_of_support_subset (subset_tsupport χ)]
  exact Measure.integrableOn_of_bounded hfin.ne hχ.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-- Real version of `integrable_mul_of_tsupport_subset`. -/
theorem integrable_mul_of_tsupport_subset_real {Ω : Set ℂ} (hΩ : IsOpen Ω) {h β : ℂ → ℝ}
    (hh : ContinuousOn h Ω) (hβ : Continuous β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ω) : Integrable (fun x ↦ h x * β x) := by
  have hcont : Continuous (fun x ↦ h x * β x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ Ω
    · exact (hh.continuousAt (hΩ.mem_nhds hx)).mul hβ.continuousAt
    · have hx' : x ∉ tsupport β := fun h' ↦ hx (hs h')
      rw [notMem_tsupport_iff_eventuallyEq] at hx'
      have : (fun _ ↦ (0 : ℝ)) =ᶠ[nhds x] fun x ↦ h x * β x := by
        filter_upwards [hx'] with y hy
        simp [hy]
      exact continuousAt_const.congr this
  exact hcont.integrable_of_hasCompactSupport (hc.mul_left (f := h))

theorem hasCompactSupport_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) : HasCompactSupport (Laplacian.laplacian χ) :=
  hc.mono' ((subset_tsupport _).trans (laplacian_testFunction hχ).2)

theorem contDiffOn_log_one_sub_normSq :
    ContDiffOn ℝ 2 (fun z : ℂ ↦ Real.log (1 - ‖z‖ ^ 2)) 𝔻 :=
  (contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffOn.log
    fun _ hz ↦ (one_sub_normSq_pos hz).ne'

theorem integral_eq_integral_hypArea {χ : ℂ → ℝ} (hs : tsupport χ ⊆ 𝔻) :
    ∫ z, χ z ∂hypArea = ∫ z, (1 - ‖z‖ ^ 2)⁻¹ ^ 2 * χ z := by
  rw [hypArea, integral_withDensity_eq_integral_toReal_smul measurable_hypAreaDensity
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · congr 1
    ext z
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  · intro z hz
    have : χ z = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h))
    simp [this]


theorem integral_log_one_sub_normSq_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ 𝔻) :
    ∫ z, Real.log (1 - ‖z‖ ^ 2) * Laplacian.laplacian χ z = -(4 * ∫ z, χ z ∂hypArea) := by
  rw [integral_mul_laplacian_of_contDiffOn isOpen_ball contDiffOn_log_one_sub_normSq
    (hχ.of_le (by norm_cast)) hχc hχs, integral_eq_integral_hypArea hχs,
    ← integral_const_mul, ← integral_neg]
  congr 1
  ext z
  by_cases hz : z ∈ 𝔻
  · have hU : ContDiffAt ℝ 2 (fun w : ℂ ↦ -Real.log (1 - ‖w‖ ^ 2)) z :=
      (contDiffOn_log_one_sub_normSq.contDiffAt (isOpen_ball.mem_nhds hz)).neg
    have heq : (fun w : ℂ ↦ Real.log (1 - ‖w‖ ^ 2)) =
        fun w ↦ (-1) * (-Real.log (1 - ‖w‖ ^ 2)) := by
      ext w; ring
    rw [laplacian_eq_four_mul_lap, heq, lap_const_mul _ hU, lap_neg_log_one_sub_normSq hz]
    ring
  · have : χ z = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hχs h))
    simp [this]

/-! ## Hyperbolic area of hyperbolic discs -/

theorem one_sub_normSq_le_of_mem_hypBall {z w : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr1 : r ≤ 1)
    (hw : w ∈ hypBall z r) : 1 - ‖z‖ ^ 2 ≤ 12 * (1 - ‖w‖ ^ 2) := by
  obtain ⟨hwD, hd⟩ := hw
  have hρ : pseudoHyp z w < 4 / 5 := by
    have h1 := (hypDist_lt_iff hz hwD r).1 hd
    have hE := exp_two_mul_lt_nine hr1
    have hEpos := Real.exp_pos (2 * r)
    have : Real.tanh r < 4 / 5 := by
      rw [tanh_eq_exp_two_mul, div_lt_iff₀ (by positivity)]
      linarith
    linarith
  have hρ0 : 0 ≤ pseudoHyp z w := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hid := one_sub_normSq_mobius hz hwD
  rw [← pseudoHyp_eq_norm_mobius] at hid
  have hD := norm_one_sub_conj_mul_pos hz hwD
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have hw1 : ‖w‖ < 1 := by simpa using hwD
  have hz0 := norm_nonneg z
  have hw0 := norm_nonneg w
  -- `‖1 - z̄ w‖ ≥ 1 - ‖z‖`
  have hlow : 1 - ‖z‖ ≤ ‖1 - conj z * w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (conj z * w)
    rw [norm_one, norm_mul, Complex.norm_conj] at h
    nlinarith
  have hkey : (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) = (1 - pseudoHyp z w ^ 2) * ‖1 - conj z * w‖ ^ 2 := by
    rw [hid]; field_simp
  have h9 : 9 / 25 * (1 - ‖z‖) ^ 2 ≤ (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
    rw [hkey]
    have h1 : 9 / 25 ≤ 1 - pseudoHyp z w ^ 2 := by nlinarith
    have h2 : (1 - ‖z‖) ^ 2 ≤ ‖1 - conj z * w‖ ^ 2 := pow_le_pow_left₀ (by linarith) hlow 2
    nlinarith [sq_nonneg (1 - ‖z‖)]
  have hpos : 0 < 1 - ‖z‖ := by linarith
  have hzz : 1 - ‖z‖ ^ 2 ≤ 2 * (1 - ‖z‖) := by nlinarith
  have hzpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
  -- `(9/100)(1-|z|²)² ≤ (1-|z|²)(1-|w|²)`
  have h100 : 9 / 100 * (1 - ‖z‖ ^ 2) ^ 2 ≤ (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
    have : (1 - ‖z‖ ^ 2) ^ 2 ≤ 4 * (1 - ‖z‖) ^ 2 := by nlinarith
    nlinarith
  have : 9 / 100 * (1 - ‖z‖ ^ 2) ≤ 1 - ‖w‖ ^ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  linarith

theorem sinh_le_two_mul_of_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Real.sinh r ≤ 2 * r := by
  have h1 := Real.abs_exp_sub_one_sub_id_le (x := r) (by rw [abs_of_nonneg hr0]; exact hr1)
  have h2 := Real.add_one_le_exp (-r)
  rw [Real.sinh_eq]
  have h3 := (abs_le.1 h1).2
  nlinarith

theorem cosh_le_two_of_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Real.cosh r ≤ 2 := by
  have h1 := Real.abs_exp_sub_one_sub_id_le (x := r) (by rw [abs_of_nonneg hr0]; exact hr1)
  have h2 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [Real.cosh_eq]
  have h3 := (abs_le.1 h1).2
  nlinarith

theorem isLocallyDoublingDiscWith_hypArea : IsLocallyDoublingDiscWith hypArea 16 := by
  intro z hz s hs h2s
  rw [hypArea_hypBall hz (by linarith), hypArea_hypBall hz hs.le, Real.sinh_two_mul]
  have hc := cosh_le_two_of_le_one hs.le (by linarith)
  have hc0 := Real.cosh_pos s
  have : Real.pi * (2 * Real.sinh s * Real.cosh s) ^ 2 ≤ 16 * (Real.pi * Real.sinh s ^ 2) := by
    have : (2 * Real.sinh s * Real.cosh s) ^ 2 = 4 * Real.sinh s ^ 2 * Real.cosh s ^ 2 := by ring
    rw [this]
    have hcs : Real.cosh s ^ 2 ≤ 4 := by nlinarith
    have := sq_nonneg (Real.sinh s)
    have := Real.pi_pos
    nlinarith [mul_le_mul_of_nonneg_left hcs (mul_nonneg this.le (sq_nonneg (Real.sinh s)))]
  calc ENNReal.ofReal (Real.pi * (2 * Real.sinh s * Real.cosh s) ^ 2)
      ≤ ENNReal.ofReal (16 * (Real.pi * Real.sinh s ^ 2)) := ENNReal.ofReal_le_ofReal this
    _ = ((16 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (Real.pi * Real.sinh s ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; simp


theorem hypArea_hypBall_ge {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr0 : 0 < r) (_hr1 : r ≤ 1) :
    ENNReal.ofReal (Real.pi * r ^ 2 / 900) ≤ hypArea (hypBall z r) := by
  rw [hypArea_hypBall hz hr0.le]
  apply ENNReal.ofReal_le_ofReal
  have h1 : r ≤ Real.sinh r := Real.self_le_sinh_iff.2 hr0.le
  have h2 : r ^ 2 ≤ Real.sinh r ^ 2 := pow_le_pow_left₀ hr0.le h1 2
  have := Real.pi_pos
  nlinarith [sq_nonneg r]

theorem hypArea_hypBall_le {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    hypArea (hypBall z r) ≤ ENNReal.ofReal (46656 * Real.pi * r ^ 2) := by
  rw [hypArea_hypBall hz hr0.le]
  apply ENNReal.ofReal_le_ofReal
  have h1 : Real.sinh r ≤ 2 * r := sinh_le_two_mul_of_le_one hr0.le hr1
  have h0 : 0 ≤ Real.sinh r := Real.sinh_nonneg_iff.2 hr0.le
  have h2 : Real.sinh r ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have := Real.pi_pos
  nlinarith [sq_nonneg r]

/-- Transfer of local doubling with explicit constants along `a • μ ≤ ν ≤ b • μ`. -/
theorem IsLocallyDoublingDiscWith.of_le_of_le {μ ν : Measure ℂ} {Cd : ℝ≥0}
    (hμ : IsLocallyDoublingDiscWith μ Cd) {a b : ℝ≥0} (ha : a ≠ 0)
    (h₁ : (a : ℝ≥0∞) • μ ≤ ν) (h₂ : ν ≤ (b : ℝ≥0∞) • μ) :
    IsLocallyDoublingDiscWith ν (b * Cd / a) := by
  intro z hz s hs h2s
  calc ν (hypBall z (2 * s)) ≤ b * μ (hypBall z (2 * s)) := h₂ _
    _ ≤ b * (Cd * μ (hypBall z s)) := by gcongr; exact hμ z hz s hs h2s
    _ = ((b * Cd / a : ℝ≥0) : ℝ≥0∞) * (a * μ (hypBall z s)) := by
        symm
        rw [← mul_assoc, ← ENNReal.coe_mul, div_mul_cancel₀ _ ha, ENNReal.coe_mul, mul_assoc]
    _ ≤ ((b * Cd / a : ℝ≥0) : ℝ≥0∞) * ν (hypBall z s) := by gcongr; exact h₁ _

theorem IsLocallyDoublingDisc.of_le_of_le {μ ν : Measure ℂ} (hμ : IsLocallyDoublingDisc μ)
    {a b : ℝ≥0∞} (ha : a ≠ 0) (hb : b ≠ ∞) (h₁ : a • μ ≤ ν) (h₂ : ν ≤ b • μ) :
    IsLocallyDoublingDisc ν := by
  obtain ⟨Cd, hCd⟩ := hμ
  set a' : ℝ≥0 := (min a 1).toNNReal with ha'
  have ha'c : (a' : ℝ≥0∞) = min a 1 := ENNReal.coe_toNNReal (min_lt_of_right_lt
    ENNReal.one_lt_top).ne
  have ha'0 : a' ≠ 0 := by
    intro h0
    have : (a' : ℝ≥0∞) = 0 := by rw [h0]; rfl
    rw [ha'c] at this
    rcases min_eq_iff.1 this with h | h
    · exact ha h.1
    · exact one_ne_zero h.1
  have h₁' : (a' : ℝ≥0∞) • μ ≤ ν := by
    refine le_trans ?_ h₁
    intro s
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    rw [ha'c]; exact min_le_left _ _
  have hbc : ((b.toNNReal : ℝ≥0) : ℝ≥0∞) = b := ENNReal.coe_toNNReal hb
  exact ⟨_, IsLocallyDoublingDiscWith.of_le_of_le hCd ha'0 h₁' (by rw [hbc]; exact h₂)⟩

theorem isLocallyDoublingDisc_hypArea : IsLocallyDoublingDisc hypArea :=
  ⟨16, isLocallyDoublingDiscWith_hypArea⟩

/-! ## The auxiliary weight -/

theorem isSubharmonicWeight_add_log {φ' : ℂ → ℝ} {ν : Measure ℂ} {ε c : ℝ} (hc : 0 ≤ c)
    (hcε : 4 * c ≤ ε) (hφ' : IsSubharmonicWeight 𝔻 φ' (ν + ENNReal.ofReal ε • hypArea)) :
    IsSubharmonicWeight 𝔻 (fun z ↦ φ' z + c * Real.log (1 - ‖z‖ ^ 2))
      (ν + ENNReal.ofReal (ε - 4 * c) • hypArea) := by
  have hε0 : 0 ≤ ε := by linarith
  have hle : ν + ENNReal.ofReal (ε - 4 * c) • hypArea ≤ ν + ENNReal.ofReal ε • hypArea := by
    intro s
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    gcongr
    linarith
  have hνfin : ∀ K ⊆ 𝔻, IsCompact K → ν K < ∞ := fun K hK hKc ↦
    (Measure.le_add_right le_rfl K).trans_lt (hφ'.finite_of_compact K hK hKc)
  refine ⟨hφ'.continuousOn.add (continuousOn_const.mul contDiffOn_log_one_sub_normSq.continuousOn),
    fun K hK hKc ↦ (hle K).trans_lt (hφ'.finite_of_compact K hK hKc),
    nonpos_iff_eq_zero.1 (hφ'.carried ▸ hle _), fun χ hχ hχc hχs ↦ ?_⟩
  have hL := laplacian_testFunction hχ
  have hΔc := hasCompactSupport_laplacian hχ hχc
  have hΔs : tsupport (Laplacian.laplacian χ) ⊆ 𝔻 := hL.2.trans hχs
  have i1 := integrable_mul_of_tsupport_subset_real isOpen_ball hφ'.continuousOn hL.1 hΔc hΔs
  have i2 := integrable_mul_of_tsupport_subset_real isOpen_ball
    contDiffOn_log_one_sub_normSq.continuousOn hL.1 hΔc hΔs
  have iν : Integrable χ ν := integrable_of_tsupport_subset_disc hνfin hχ.continuous hχc hχs
  have iA : Integrable χ hypArea := integrable_of_tsupport_subset_disc
    (fun K hK hKc ↦ hypArea_lt_top_of_isCompact hK hKc) hχ.continuous hχc hχs
  calc ∫ z, (φ' z + c * Real.log (1 - ‖z‖ ^ 2)) * Laplacian.laplacian χ z
      = (∫ z, φ' z * Laplacian.laplacian χ z) +
          c * ∫ z, Real.log (1 - ‖z‖ ^ 2) * Laplacian.laplacian χ z := by
        have h := integral_add i1 (i2.const_mul c)
        simp only [integral_const_mul] at h
        rw [← h]
        congr 1; ext z; ring
    _ = ((∫ z, χ z ∂ν) + ε * ∫ z, χ z ∂hypArea) + c * (-(4 * ∫ z, χ z ∂hypArea)) := by
        rw [hφ'.laplacian_eq χ hχ hχc hχs, integral_log_one_sub_normSq_mul_laplacian hχ hχc hχs,
          integral_add_measure iν (iA.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
          ENNReal.toReal_ofReal hε0, smul_eq_mul]
    _ = (∫ z, χ z ∂ν) + (ε - 4 * c) * ∫ z, χ z ∂hypArea := by ring
    _ = ∫ z, χ z ∂(ν + ENNReal.ofReal (ε - 4 * c) • hypArea) := by
        rw [integral_add_measure iν (iA.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul]

/-! ## The partition and the kernel -/

theorem measurableSet_goodSet_disc (Z : Set ℂ) (ρ : ℂ → ℝ) (ε : ℝ) :
    MeasurableSet {z | z ∈ 𝔻 ∧ ∀ w ∈ Z, w ∈ 𝔻 → ε * ρ w ≤ hypDist z w} := by
  have hU : IsOpen (⋃ w ∈ Z ∩ 𝔻, 𝔻 ∩ pseudoHyp w ⁻¹' Iio (Real.tanh (ε * ρ w))) :=
    isOpen_biUnion fun w hw ↦
      (continuousOn_pseudoHyp hw.2).isOpen_inter_preimage isOpen_ball isOpen_Iio
  have heq : {z | z ∈ 𝔻 ∧ ∀ w ∈ Z, w ∈ 𝔻 → ε * ρ w ≤ hypDist z w} =
      𝔻 \ ⋃ w ∈ Z ∩ 𝔻, 𝔻 ∩ pseudoHyp w ⁻¹' Iio (Real.tanh (ε * ρ w)) := by
    ext z
    simp only [mem_ofPred_eq, mem_sdiff, mem_iUnion, mem_inter_iff, mem_preimage, mem_Iio,
      exists_prop, not_exists, not_and]
    constructor
    · rintro ⟨hz, h⟩
      refine ⟨hz, fun w ⟨hwZ, hwD⟩ _ hlt ↦ ?_⟩
      rw [pseudoHyp_comm, ← hypDist_lt_iff hz hwD] at hlt
      exact absurd (h w hwZ hwD) (not_le.2 hlt)
    · rintro ⟨hz, h⟩
      refine ⟨hz, fun w hwZ hwD ↦ not_lt.1 fun hlt ↦ h w ⟨hwZ, hwD⟩ hz ?_⟩
      rw [pseudoHyp_comm, ← hypDist_lt_iff hz hwD]
      exact hlt
  rw [heq]
  exact measurableSet_ball.diff hU.measurableSet

/-- The holomorphic factor of the kernel of Theorem 2:
`H(z, ζ) = ∑ᵢ χ_{Ωᵢ}(ζ) hᵢ(z)/hᵢ(ζ) · (1 - |ζ|²)/(1 - ζ̄ z)`. -/
def thm2H {n : ℕ} (h : Fin n → ℂ → ℂ) (Ω : Fin n → Set ℂ) (z ζ : ℂ) : ℂ :=
  (∑ i, (Ω i).indicator (fun ζ ↦ h i z / h i ζ) ζ) *
    (((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) / (1 - conj ζ * z))

/-! ## Uniform forms (constants depending only on `(Cd, r)`) -/

/-- The auxiliary weight `ψ ≈ φ + c log(1 − |z|²)`, uniformly in the class `(Cd, r)`: from
`lemma6_disc_quant` (M04), `isSubharmonicWeight_add_log` and the growth lemma
`ofReal_lt_measure_hypBall` (M03, explicit radius). -/
theorem exists_aux_weight_disc_quant (Cd : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    ∃ (c B : ℝ) (Cd' : ℝ≥0) (R' : ℝ), 0 < c ∧ c < 1 ∧ 0 ≤ B ∧ 0 < R' ∧
      ∀ (φ : ℂ → ℝ) (μ : Measure ℂ), IsSubharmonicWeight 𝔻 φ μ → MeasClassDisc μ Cd r →
        ∃ (ψ : ℂ → ℝ) (μψ : Measure ℂ), IsSubharmonicWeight 𝔻 ψ μψ ∧ MeasClassDisc μψ Cd' R' ∧
          ∀ z ∈ 𝔻, |ψ z - (φ z + c * Real.log (1 - ‖z‖ ^ 2))| ≤ B := by
  obtain ⟨ε, B, Cd₁, R₁, hε, hB, hR₁, hL⟩ := lemma6_disc_quant Cd r hr
  set c := min (ε / 8) (1 / 2) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by norm_num)
  have hc1 : c < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hcε : 8 * c ≤ ε := by have := min_le_left (ε / 8) (1 / 2); linarith
  refine ⟨c, B, 2 * Cd₁, (2 * ⌈1 / (1 / 2 : ℝ)⌉₊ + 1) * R₁, hc0, hc1, hB, by positivity,
    fun φ μ hφ hμ ↦ ?_⟩
  obtain ⟨φ', μ', hφ', hμ', hεμ', hφφ'⟩ := hL φ μ hφ hμ
  have := hφ'.sigmaFinite isOpen_ball
  obtain ⟨ν, hν⟩ := Measure.exists_add_eq_of_le hεμ'
  rw [← hν] at hφ'
  have hψ := isSubharmonicWeight_add_log hc0.le (by linarith) hφ'
  set μψ := ν + ENNReal.ofReal (ε - 4 * c) • hypArea with hμψ
  have hup : μψ ≤ μ' := by
    rw [← hν]
    intro s
    simp only [hμψ, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    gcongr
    linarith
  have hlow : μ' ≤ (2 : ℝ≥0∞) • μψ := by
    rw [← hν]
    intro s
    simp only [hμψ, Measure.add_apply, Measure.smul_apply, smul_eq_mul, mul_add, ← mul_assoc]
    gcongr
    · exact le_mul_of_one_le_left' one_le_two
    · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  have hhalf : ∀ z ∈ 𝔻, ENNReal.ofReal (1 / 2) ≤ μψ (hypBall z R₁) := by
    intro z hz
    have h1 : 1 < 2 * μψ (hypBall z R₁) := (hμ'.mass z hz).trans_le (hlow _)
    rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat,
      ENNReal.inv_le_iff_le_mul (by simp) (by simp)]
    exact h1.le
  refine ⟨fun z ↦ φ' z + c * Real.log (1 - ‖z‖ ^ 2), μψ, hψ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro z hz s hs h2s
    calc μψ (hypBall z (2 * s)) ≤ μ' (hypBall z (2 * s)) := hup _
      _ ≤ Cd₁ * μ' (hypBall z s) := hμ'.doubling z hz s hs h2s
      _ ≤ Cd₁ * (2 * μψ (hypBall z s)) := by gcongr; exact hlow _
      _ = ((2 * Cd₁ : ℝ≥0) : ℝ≥0∞) * μψ (hypBall z s) := by
          rw [ENNReal.coe_mul]; push_cast; ring
  · intro z hz
    have := ofReal_lt_measure_hypBall hR₁ (by norm_num) hhalf 1 hz
    rwa [ENNReal.ofReal_one] at this
  · exact fun K hK hKc ↦ (hup K).trans_lt (hμ'.finite K hK hKc)
  · intro z hz
    rw [show φ' z + c * Real.log (1 - ‖z‖ ^ 2) - (φ z + c * Real.log (1 - ‖z‖ ^ 2)) =
      φ' z - φ z by ring, abs_sub_comm]
    exact hφφ' z hz

/-- The kernel of Theorem 2, uniformly in the class `(Cd, r)`: from
`exists_aux_weight_disc_quant`, `prop2_disc_quant` (M09) applied to the auxiliary weight, and
`exists_measurable_partition`. -/
theorem exists_disc_solution_kernel_quant (Cd : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    ∃ (c A : ℝ), 0 < c ∧ c < 1 ∧ 0 ≤ A ∧ ∀ (φ : ℂ → ℝ) (μ : Measure ℂ),
      IsSubharmonicWeight 𝔻 φ μ → MeasClassDisc μ Cd r →
      ∃ H : ℂ → ℂ → ℂ, Measurable (Function.uncurry H) ∧
        (∀ ζ ∈ 𝔻, DifferentiableOn ℂ (fun z ↦ H z ζ) 𝔻) ∧ (∀ ζ ∈ 𝔻, H ζ ζ = 1) ∧
        ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) *
          ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) := by
  classical
  obtain ⟨c, B, Cd', R', hc0, hc1, hB, hR', haux⟩ := exists_aux_weight_disc_quant Cd r hr
  obtain ⟨n, M, C, εP, -, hC, -, hP⟩ := prop2_disc_quant Cd' R' hR'
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos (by exact_mod_cast hC)
  refine ⟨c, (C : ℝ) ^ 2 * Real.exp (2 * B), hc0, hc1, by positivity, fun φ μ hφ hμ ↦ ?_⟩
  obtain ⟨ψ, μψ, hψ, hμψ, hψφ⟩ := haux φ μ hφ hμ
  obtain ⟨h, hh, -, -, hcov, hgood, hup⟩ := hP ψ μψ ⟨hψ, hμψ⟩
  -- measurable versions of the multipliers (equal to `h i` on `𝔻`)
  let h' : Fin n → ℂ → ℂ := fun i ↦ 𝔻.piecewise (h i) 0
  have hh'm : ∀ i, Measurable (h' i) := fun i ↦
    (hh i).continuousOn.measurable_piecewise continuousOn_const measurableSet_ball
  have hh'eq : ∀ i, ∀ z ∈ 𝔻, h' i z = h i z := fun i z hz ↦ piecewise_eq_of_mem _ _ _ hz
  -- the good sets and the partition
  let G : Fin n → Set ℂ := fun i ↦
    {z | z ∈ 𝔻 ∧ ∀ w ∈ {w | h i w = 0}, w ∈ 𝔻 → εP * massRadiusDisc μψ w ≤ hypDist z w}
  obtain ⟨Ω, hΩm, hΩG, hΩu⟩ := exists_measurable_partition measurableSet_ball G
    (fun i ↦ measurableSet_goodSet_disc _ _ _) (fun z hz ↦ by
      obtain ⟨i, hi⟩ := hcov z hz
      exact ⟨i, hz, fun w hw0 hwD ↦ hi w hwD hw0⟩)
  have hform : ∀ ζ ∈ 𝔻, ∃ i, ζ ∈ Ω i ∧ ∀ z, thm2H h' Ω z ζ =
      h' i z / h' i ζ * (((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) / (1 - conj ζ * z)) := by
    intro ζ hζ
    obtain ⟨i, hi, huniq⟩ := hΩu ζ hζ
    refine ⟨i, hi, fun z ↦ ?_⟩
    unfold thm2H
    rw [Finset.sum_eq_single i (fun j _ hji ↦ indicator_of_notMem (fun hj ↦ hji (huniq j hj)) _)
      (by simp), indicator_of_mem hi]
  have hne : ∀ i, ∀ ζ ∈ Ω i, h i ζ ≠ 0 ∧ (C : ℝ)⁻¹ * Real.exp (ψ ζ) ≤ ‖h i ζ‖ := by
    intro i ζ hζ
    obtain ⟨hζD, hζG⟩ := (hΩG i hζ).1
    have hl := (hgood i ζ hζD (fun w hwD hw0 ↦ hζG w hw0 hwD)).1
    refine ⟨fun h0 ↦ ?_, hl⟩
    rw [h0, norm_zero] at hl
    have : 0 < (C : ℝ)⁻¹ * Real.exp (ψ ζ) := by positivity
    linarith
  refine ⟨thm2H h' Ω, ?_, ?_, ?_, ?_⟩
  · -- measurability
    have hfun : Function.uncurry (thm2H h' Ω) = fun p : ℂ × ℂ ↦
        (∑ i, (Prod.snd ⁻¹' Ω i).indicator (fun q : ℂ × ℂ ↦ h' i q.1 / h' i q.2) p) *
          (((1 - ‖p.2‖ ^ 2 : ℝ) : ℂ) / (1 - conj p.2 * p.1)) := by
      ext p
      simp only [Function.uncurry, thm2H, indicator, mem_preimage]
    rw [hfun]
    refine Measurable.mul (Finset.measurable_sum _ fun i _ ↦ ?_) ?_
    · exact (((hh'm i).comp measurable_fst).div ((hh'm i).comp measurable_snd)).indicator
        (measurable_snd (hΩm i))
    · exact (Complex.measurable_ofReal.comp (measurable_const.sub
        (measurable_snd.norm.pow_const 2))).div (measurable_const.sub
        ((Complex.continuous_conj.measurable.comp measurable_snd).mul measurable_fst))
  · -- holomorphy in `z`
    intro ζ hζ
    obtain ⟨i, -, hfor⟩ := hform ζ hζ
    have hd : DifferentiableOn ℂ (fun z ↦ h i z / h i ζ *
        (((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) / (1 - conj ζ * z))) 𝔻 :=
      ((hh i).div_const _).mul ((differentiableOn_const _).div
        ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id))
        fun z hz ↦ one_sub_conj_mul_ne_zero_of_mem hζ hz)
    refine hd.congr fun z hz ↦ ?_
    rw [hfor, hh'eq i z hz, hh'eq i ζ hζ]
  · -- diagonal
    intro ζ hζ
    obtain ⟨i, hi, hfor⟩ := hform ζ hζ
    rw [hfor, hh'eq i ζ hζ, div_self (hne i ζ hi).1, one_mul, one_sub_conj_mul_self, div_self]
    exact_mod_cast (one_sub_normSq_pos hζ).ne'
  · -- the bound
    intro z hz ζ hζ
    obtain ⟨i, hi, hfor⟩ := hform ζ hζ
    have hlow := (hne i ζ hi).2
    have hupz := hup i z hz
    have hz0 := one_sub_normSq_pos hz
    have hζ0 := one_sub_normSq_pos hζ
    rw [hfor, hh'eq i z hz, hh'eq i ζ hζ, norm_mul, norm_div, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hζ0.le]
    have hratio : ‖h i z‖ / ‖h i ζ‖ ≤ (C : ℝ) ^ 2 * Real.exp (ψ z - ψ ζ) := by
      have hpos : 0 < (C : ℝ)⁻¹ * Real.exp (ψ ζ) := by positivity
      calc ‖h i z‖ / ‖h i ζ‖ ≤ (C * Real.exp (ψ z)) / ((C : ℝ)⁻¹ * Real.exp (ψ ζ)) := by
            gcongr
        _ = (C : ℝ) ^ 2 * Real.exp (ψ z - ψ ζ) := by
            rw [Real.exp_sub]; field_simp
    have hψ' : Real.exp (ψ z - ψ ζ) ≤ Real.exp (2 * B) * Real.exp (φ z - φ ζ) *
        ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c := by
      have e1 : ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c =
          Real.exp (c * (Real.log (1 - ‖z‖ ^ 2) - Real.log (1 - ‖ζ‖ ^ 2))) := by
        rw [Real.rpow_def_of_pos (div_pos hz0 hζ0), Real.log_div hz0.ne' hζ0.ne', mul_comm]
      rw [e1, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 := abs_le.1 (hψφ z hz)
      have h2 := abs_le.1 (hψφ ζ hζ)
      nlinarith
    have hK : 0 ≤ (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ := by positivity
    calc ‖h i z‖ / ‖h i ζ‖ * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖)
        ≤ (C : ℝ) ^ 2 * Real.exp (ψ z - ψ ζ) * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) := by
          gcongr
      _ ≤ (C : ℝ) ^ 2 * (Real.exp (2 * B) * Real.exp (φ z - φ ζ) *
            ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c) * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) := by
          gcongr
      _ = (C : ℝ) ^ 2 * Real.exp (2 * B) * Real.exp (φ z - φ ζ) *
            ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) := by
          ring

/-! ## Per-weight forms -/

theorem exists_aux_weight_disc (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ (ψ : ℂ → ℝ) (μψ : Measure ℂ) (c B : ℝ), 0 < c ∧ c < 1 ∧ 0 ≤ B ∧
      IsSubharmonicWeight 𝔻 ψ μψ ∧ IsLocallyDoublingDisc μψ ∧
      (∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μψ (hypBall z R)) ∧
      ∀ z ∈ 𝔻, |ψ z - (φ z + c * Real.log (1 - ‖z‖ ^ 2))| ≤ B := by
  obtain ⟨r, hr, hmr⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  obtain ⟨c, B, Cd', R', hc0, hc1, hB, hR', h⟩ := exists_aux_weight_disc_quant Cd r hr
  obtain ⟨ψ, μψ, hψ, hcl, hb⟩ := h φ μ hφ (MeasClassDisc.of_weight hφ hCd hmr)
  exact ⟨ψ, μψ, c, B, hc0, hc1, hB, hψ, ⟨Cd', hcl.doubling⟩, ⟨R', hR', hcl.mass⟩, hb⟩

theorem exists_disc_solution_kernel (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight 𝔻 φ μ) (hd : IsLocallyDoublingDisc μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ (H : ℂ → ℂ → ℂ) (c A : ℝ), 0 < c ∧ c < 1 ∧ 0 ≤ A ∧ Measurable (Function.uncurry H) ∧
      (∀ ζ ∈ 𝔻, DifferentiableOn ℂ (fun z ↦ H z ζ) 𝔻) ∧ (∀ ζ ∈ 𝔻, H ζ ζ = 1) ∧
      ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) *
        ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) := by
  obtain ⟨r, hr, hmr⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  obtain ⟨c, A, hc0, hc1, hA, h⟩ := exists_disc_solution_kernel_quant Cd r hr
  obtain ⟨H, hHm, hHd, hH1, hHb⟩ := h φ μ hφ (MeasClassDisc.of_weight hφ hCd hmr)
  exact ⟨H, c, A, hc0, hc1, hA, hHm, hHd, hH1, hHb⟩

/-! ## Main statements -/

/-- **Theorem 2, uniform form**: the constant depends only on the doubling constant `Cd` and the
radius `r` of the mass condition (this is what the proof gives, and what the companion BOC
project needs: one constant for a whole family of weights). -/
theorem theorem2_uniform (Cd : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ≥0, ∀ (φ : ℂ → ℝ) (μ : Measure ℂ), IsSubharmonicWeight 𝔻 φ μ →
      (∀ z ∈ 𝔻, ∀ s : ℝ, 0 < s → 2 * s < 1 → μ (hypBall z (2 * s)) ≤ Cd * μ (hypBall z s)) →
      (∀ z ∈ 𝔻, 1 < μ (hypBall z r)) →
      ∀ f : ℂ → ℂ, AEStronglyMeasurable f (volume.restrict 𝔻) →
      (∃ p : ℝ≥0∞, 1 ≤ p ∧
        eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure < ∞) →
      ∃ u : ℂ → ℂ, IsWeakDbarSol 𝔻 u f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
        eLpNorm (fun z ↦ u z * (Real.exp (-φ z) : ℝ)) p discMeasure ≤
          C * eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure := by
  obtain ⟨c, A, hc0, hc1, -, hK⟩ := exists_disc_solution_kernel_quant Cd r hr
  refine ⟨(24 * A / (c * (1 - c))).toNNReal, fun φ μ hφ hdμ hmμ f hf hadm ↦ ?_⟩
  obtain ⟨H, hHm, hHd, hH1, hHb⟩ := hK φ μ hφ (MeasClassDisc.of_weight hφ hdμ hmμ)
  obtain ⟨hsol, hest⟩ := disc_kernel_operator hφ.continuousOn hc0 hc1 hHm hHd hH1 hHb f hf hadm
  exact ⟨_, hsol, hest⟩

/-- **Theorem 2** (paper, p. 357), in the normalisation that its proof gives (NOTEBOOK): one
solution `u` of `∂̄u = f` in `𝔻` satisfies, for every `p ∈ [1, ∞]`,
`‖u e^{-φ}‖_{L^p(dm/(1-|z|²))} ≲ ‖f (1-|z|²) e^{-φ}‖_{L^p(dm/(1-|z|²))}`.  For `p = ∞` this is
`sup |u| e^{-φ} ≲ sup |f(ζ)| (1-|ζ|) e^{-φ(ζ)}` (essential suprema). -/
theorem theorem2 (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ C : ℝ≥0, ∀ f : ℂ → ℂ, AEStronglyMeasurable f (volume.restrict 𝔻) →
      (∃ p : ℝ≥0∞, 1 ≤ p ∧
        eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure < ∞) →
      ∃ u : ℂ → ℂ, IsWeakDbarSol 𝔻 u f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
        eLpNorm (fun z ↦ u z * (Real.exp (-φ z) : ℝ)) p discMeasure ≤
          C * eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure := by
  obtain ⟨r, hr, hmr⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  obtain ⟨C, hC⟩ := theorem2_uniform Cd r hr
  exact ⟨C, hC φ μ hφ hCd hmr⟩

theorem IsSubharmonicWeight.div_const {Ω : Set ℂ} {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight Ω φ μ) {p : ℝ} (hp : 0 < p) :
    IsSubharmonicWeight Ω (fun z ↦ φ z / p) (ENNReal.ofReal p⁻¹ • μ) := sorry

theorem IsLocallyDoublingDisc.smul {μ : Measure ℂ} (h : IsLocallyDoublingDisc μ) (a : ℝ≥0∞) :
    IsLocallyDoublingDisc (a • μ) := by
  obtain ⟨Cd, hCd⟩ := h
  refine ⟨Cd, fun z hz s hs h2s ↦ ?_⟩
  simp only [Measure.smul_apply, smul_eq_mul]
  calc a * μ (hypBall z (2 * s)) ≤ a * (Cd * μ (hypBall z s)) := by gcongr; exact hCd z hz s hs h2s
    _ = Cd * (a * μ (hypBall z s)) := mul_left_comm _ _ _

/-- **Theorem 2**, the `L^p` estimate exactly as printed (paper, p. 357), with the solution
allowed to depend on `p`:
`∫_𝔻 |u|^p e^{-φ} dm/(1-|z|²) ≲ ∫_𝔻 |f (1-|z|²)|^p e^{-φ} dm/(1-|z|²)`. -/
theorem theorem2_printed (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r))
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ≥0, ∀ f : ℂ → ℂ, AEStronglyMeasurable f (volume.restrict 𝔻) →
      ∫⁻ z, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * Real.exp (-φ z)) ∂discMeasure < ∞ →
      ∃ u : ℂ → ℂ, IsWeakDbarSol 𝔻 u f ∧
        ∫⁻ z, ENNReal.ofReal (‖u z‖ ^ p * Real.exp (-φ z)) ∂discMeasure ≤
          C * ∫⁻ z, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * Real.exp (-φ z)) ∂discMeasure :=
  sorry

/-! ## The bridge to BOC -/

/-- The Riesz measure of `ψ₀ / 2` for `ψ₀ ∈ C²(𝔻)`: `Δ(ψ₀/2) dm = 2 lap ψ₀ dm` on `𝔻`. -/
def bridgeMeasure (ψ₀ : ℂ → ℝ) : Measure ℂ :=
  (volume.restrict 𝔻).withDensity fun z ↦ ENNReal.ofReal (2 * lap ψ₀ z)

theorem laplacian_half_eq {ψ₀ : ℂ → ℝ} (hψ : ContDiffOn ℝ 2 ψ₀ 𝔻) {z : ℂ} (hz : z ∈ 𝔻) :
    Laplacian.laplacian (fun z ↦ ψ₀ z / 2) z = 2 * lap ψ₀ z := by
  have hc : ContDiffAt ℝ 2 ψ₀ z := hψ.contDiffAt (isOpen_ball.mem_nhds hz)
  rw [laplacian_eq_four_mul_lap,
    show (fun z ↦ ψ₀ z / 2) = fun z ↦ (1 / 2 : ℝ) * ψ₀ z by ext; ring, lap_const_mul _ hc]
  ring

theorem bridge_isSubharmonicWeight {ψ₀ : ℂ → ℝ} (hψ : ContDiffOn ℝ 2 ψ₀ 𝔻)
    (hpos : ∀ z ∈ 𝔻, 0 ≤ lap ψ₀ z) :
    IsSubharmonicWeight 𝔻 (fun z ↦ ψ₀ z / 2) (bridgeMeasure ψ₀) := by
  have hw := isSubharmonicWeight_of_contDiffOn isOpen_ball (hψ.div_const 2)
    (fun z hz ↦ by rw [laplacian_half_eq hψ hz]; linarith [hpos z hz])
  have hmeas : volume.withDensity
      (𝔻.indicator fun z ↦ ENNReal.ofReal (Laplacian.laplacian (fun z ↦ ψ₀ z / 2) z)) =
      bridgeMeasure ψ₀ := by
    rw [withDensity_indicator measurableSet_ball, bridgeMeasure]
    refine withDensity_congr_ae (ae_restrict_of_forall_mem measurableSet_ball fun z hz ↦ ?_)
    dsimp only
    rw [laplacian_half_eq hψ hz]
  rw [hmeas] at hw
  exact hw

/-- Lower half of `bridge_le_le` (only the lower bound on `invLap` is needed). -/
theorem bridge_ge {ψ₀ : ℂ → ℝ} {δ : ℝ} (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) :
    ENNReal.ofReal (2 * δ) • hypArea ≤ bridgeMeasure ψ₀ := by
  rw [hypArea, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top, bridgeMeasure]
  refine withDensity_mono (ae_restrict_of_forall_mem measurableSet_ball fun z hz ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul' (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have ht : 0 < (1 - ‖z‖ ^ 2) ^ 2 := pow_pos (one_sub_normSq_pos hz) 2
  have h := hlow z hz
  unfold invLap at h
  have : δ * ((1 - ‖z‖ ^ 2) ^ 2)⁻¹ ≤ lap ψ₀ z := by
    rw [← div_eq_mul_inv, div_le_iff₀ ht]; linarith
  rw [inv_pow]
  linarith

/-- Upper half of `bridge_le_le`. -/
theorem bridge_le {ψ₀ : ℂ → ℝ} {M : ℝ} (hup : ∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) :
    bridgeMeasure ψ₀ ≤ ENNReal.ofReal (2 * M) • hypArea := by
  rw [hypArea, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top, bridgeMeasure]
  refine withDensity_mono (ae_restrict_of_forall_mem measurableSet_ball fun z hz ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul' (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have ht : 0 < (1 - ‖z‖ ^ 2) ^ 2 := pow_pos (one_sub_normSq_pos hz) 2
  have h := hup z hz
  unfold invLap at h
  have : lap ψ₀ z ≤ M * ((1 - ‖z‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ ht]; linarith
  rw [inv_pow]
  linarith

theorem bridge_le_le {ψ₀ : ℂ → ℝ} {δ M : ℝ} (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z)
    (hup : ∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) :
    ENNReal.ofReal (2 * δ) • hypArea ≤ bridgeMeasure ψ₀ ∧
      bridgeMeasure ψ₀ ≤ ENNReal.ofReal (2 * M) • hypArea :=
  ⟨bridge_ge hlow, bridge_le hup⟩

/-- Mass of hyperbolic balls for a measure dominating `a · hypArea`, with an explicit radius
depending only on `a`. -/
theorem one_lt_measure_hypBall_of_le {a : ℝ} (ha : 0 < a) {μ : Measure ℂ}
    (h₁ : ENNReal.ofReal a • hypArea ≤ μ) {z : ℂ} (hz : z ∈ 𝔻) :
    1 < μ (hypBall z ((2 * ⌈1 / (a * Real.pi)⌉₊ + 1) * 1)) := by
  have hm : ∀ z ∈ 𝔻, ENNReal.ofReal (a * Real.pi) ≤ μ (hypBall z 1) := fun z hz ↦ by
    calc ENNReal.ofReal (a * Real.pi) ≤ ENNReal.ofReal a * hypArea (hypBall z 1) := by
          rw [hypArea_hypBall hz zero_le_one, ← ENNReal.ofReal_mul ha.le]
          apply ENNReal.ofReal_le_ofReal
          have h1 : (1 : ℝ) ≤ Real.sinh 1 := Real.self_le_sinh_iff.2 zero_le_one
          have h2 : (1 : ℝ) ≤ Real.sinh 1 ^ 2 := by nlinarith
          have := Real.pi_pos
          have : Real.pi ≤ Real.pi * Real.sinh 1 ^ 2 := by nlinarith
          nlinarith
      _ ≤ μ (hypBall z 1) := h₁ _
  have := ofReal_lt_measure_hypBall one_pos (by positivity) hm 1 hz
  rwa [ENNReal.ofReal_one] at this

/-- The class `(Cd, R₀)` of a measure comparable to `hypArea`, with explicit constants depending
only on the comparison constants. -/
theorem measClassDisc_of_le_hypArea {a b : ℝ} (ha : 0 < a) {μ : Measure ℂ}
    (h₁ : ENNReal.ofReal a • hypArea ≤ μ) (h₂ : μ ≤ ENNReal.ofReal b • hypArea) :
    MeasClassDisc μ (b.toNNReal * 16 / a.toNNReal) ((2 * ⌈1 / (a * Real.pi)⌉₊ + 1) * 1) := by
  refine ⟨isLocallyDoublingDiscWith_hypArea.of_le_of_le (by simpa using ha) h₁ h₂,
    fun z hz ↦ one_lt_measure_hypBall_of_le ha h₁ hz, fun K hK hKc ↦ (h₂ K).trans_lt ?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hypArea_lt_top_of_isCompact hK hKc)

theorem bridge_isLocallyDoublingDisc {ψ₀ : ℂ → ℝ} {δ M : ℝ} (hδ : 0 < δ)
    (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) (hup : ∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) :
    IsLocallyDoublingDisc (bridgeMeasure ψ₀) :=
  ⟨_, (measClassDisc_of_le_hypArea (by linarith) (bridge_ge hlow) (bridge_le hup)).doubling⟩

theorem bridge_mass {ψ₀ : ℂ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < bridgeMeasure ψ₀ (hypBall z R) :=
  ⟨_, by positivity, fun _ hz ↦ one_lt_measure_hypBall_of_le (by linarith) (bridge_ge hlow) hz⟩

/-- The bridge with a constant uniform in `ψ₀` (needed by BOC, M11 §8.3).  Not derivable from
the per-weight `theorem2`; it follows from `theorem2_uniform` (now among the comparator
statements) together with `bridge_*`, or from `prop2_disc_unif`. -/
theorem dbar_sup_estimate_C2_uniform {δ M : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ₀ : ℂ → ℝ, ContDiffOn ℝ 2 ψ₀ 𝔻 → (∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) →
      (∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) → ∀ g : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g → tsupport g ⊆ 𝔻 → ∃ W : ℂ → ℂ, IsWeakDbarSol 𝔻 W g ∧ ∀ B : ℝ,
        (∀ ζ ∈ 𝔻, ‖g ζ‖ * (1 - ‖ζ‖) * Real.exp (-ψ₀ ζ / 2) ≤ B) →
        ∀ᵐ z ∂(volume.restrict 𝔻), ‖W z‖ * Real.exp (-ψ₀ z / 2) ≤ C * B := by
  have h2δ : 0 < 2 * δ := by linarith
  obtain ⟨C₂, hC₂⟩ := theorem2_uniform ((2 * M).toNNReal * 16 / (2 * δ).toNNReal)
    ((2 * ⌈1 / (2 * δ * Real.pi)⌉₊ + 1) * 1) (by positivity)
  refine ⟨2 * C₂, by positivity, fun ψ₀ hψ hlow hup g hg hgc hgs ↦ ?_⟩
  have hpos : ∀ z ∈ 𝔻, 0 ≤ lap ψ₀ z := fun z hz ↦ by
    have ht : 0 < (1 - ‖z‖ ^ 2) ^ 2 := pow_pos (one_sub_normSq_pos hz) 2
    have h := hlow z hz
    unfold invLap at h
    by_contra hneg
    push Not at hneg
    nlinarith
  have hw := bridge_isSubharmonicWeight hψ hpos
  have hcl := measClassDisc_of_le_hypArea h2δ (bridge_ge hlow) (bridge_le hup)
  -- the admissible right-hand side
  set F : ℂ → ℂ := fun z ↦ g z * ((1 - ‖z‖ ^ 2) * Real.exp (-(ψ₀ z / 2)) : ℝ) with hFdef
  have hFc : Continuous F := by
    have hcont : ContinuousOn (fun z : ℂ ↦ (((1 - ‖z‖ ^ 2) * Real.exp (-(ψ₀ z / 2)) : ℝ) : ℂ)) 𝔻 :=
      Complex.continuous_ofReal.comp_continuousOn ((continuousOn_const.sub
        (continuous_norm.pow 2).continuousOn).mul
        (Real.continuous_exp.comp_continuousOn (hψ.continuousOn.div_const 2).neg))
    have := continuous_mul_of_tsupport_subset isOpen_ball hcont hg.continuous hgs
    simpa only [hFdef, mul_comm] using this
  have hFcs : HasCompactSupport F := hgc.mul_right
  obtain ⟨K, hK⟩ := hFc.bounded_above_of_compact_support hFcs
  have hFfin : eLpNorm F ∞ discMeasure < ∞ := by
    rw [eLpNorm_exponent_top hFc.aestronglyMeasurable]
    exact (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hK)).trans_lt
      ENNReal.ofReal_lt_top
  obtain ⟨W, hW, hest⟩ := hC₂ (fun z ↦ ψ₀ z / 2) (bridgeMeasure ψ₀) hw hcl.doubling hcl.mass g
    hg.continuous.aestronglyMeasurable ⟨∞, le_top, hFfin⟩
  refine ⟨W, hW, fun B hB ↦ ?_⟩
  have hB0 : 0 ≤ B := by
    have := hB 0 (by simp)
    have : 0 ≤ ‖g 0‖ * (1 - ‖(0 : ℂ)‖) * Real.exp (-ψ₀ 0 / 2) := by simp; positivity
    linarith
  -- the right-hand side is at most `2B`
  have hac : discMeasure ≪ volume.restrict 𝔻 := withDensity_absolutelyContinuous _ _
  have hF2B : eLpNorm F ∞ discMeasure ≤ ENNReal.ofReal (2 * B) := by
    rw [eLpNorm_exponent_top hFc.aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_bound (hac.ae_le
      (ae_restrict_of_forall_mem measurableSet_ball fun z hz ↦ ?_))
    have hz0 := norm_nonneg z
    have hz1 : ‖z‖ < 1 := by simpa using hz
    have hexp := Real.exp_pos (-(ψ₀ z / 2))
    rw [hFdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (mul_nonneg (one_sub_normSq_pos hz).le hexp.le)]
    have h1 := hB z hz
    rw [neg_div] at h1
    have h2 : 1 - ‖z‖ ^ 2 ≤ 2 * (1 - ‖z‖) := by nlinarith
    have h3 : ‖g z‖ * ((1 - ‖z‖ ^ 2) * Real.exp (-(ψ₀ z / 2))) ≤
        ‖g z‖ * (2 * (1 - ‖z‖) * Real.exp (-(ψ₀ z / 2))) := by gcongr
    linarith
  have hest' : eLpNorm (fun z ↦ W z * (Real.exp (-(ψ₀ z / 2)) : ℂ)) ∞ discMeasure ≤
      C₂ * ENNReal.ofReal (2 * B) := by
    refine (hest ∞ le_top).trans ?_
    gcongr
  have hae := ae_le_eLpNormEssSup (μ := discMeasure)
    (f := fun z ↦ W z * (Real.exp (-(fun z ↦ ψ₀ z / 2) z) : ℂ))
  have hdens : volume.restrict 𝔻 ≪ discMeasure := by
    refine withDensity_absolutelyContinuous' (by fun_prop)
      (ae_restrict_of_forall_mem measurableSet_ball fun z hz ↦ ?_)
    have := one_sub_normSq_pos hz
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  filter_upwards [hdens.ae_le hae] with z hz
  have hz' := (hz.trans eLpNormEssSup_le_eLpNorm_top).trans hest'
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity), norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le] at hz'
  rw [neg_div]
  linarith

theorem dbar_sup_estimate_C2 {ψ₀ : ℂ → ℝ} (hψ : ContDiffOn ℝ 2 ψ₀ 𝔻) {δ M : ℝ} (hδ : 0 < δ)
    (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) (hup : ∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ 𝔻 → ∃ W : ℂ → ℂ, IsWeakDbarSol 𝔻 W g ∧ ∀ B : ℝ,
        (∀ ζ ∈ 𝔻, ‖g ζ‖ * (1 - ‖ζ‖) * Real.exp (-ψ₀ ζ / 2) ≤ B) →
        ∀ᵐ z ∂(volume.restrict 𝔻), ‖W z‖ * Real.exp (-ψ₀ z / 2) ≤ C * B := by
  obtain ⟨C, hC0, hC⟩ := dbar_sup_estimate_C2_uniform (M := M) hδ
  exact ⟨C, hC0, hC ψ₀ hψ hlow hup⟩

end OC
