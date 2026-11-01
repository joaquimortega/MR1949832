import OrtegaCerdaMultipliers.Multiplier.CellBounds
import OrtegaCerdaMultipliers.Potential.Fundamental
import OrtegaCerdaMultipliers.LogModulusWeak

/-!
# M08 (Multiplier) — Convergence, continuity and Laplacian of the potential `S`

See `blueprint/M08_Multiplier.md` §2.5.  Scaffold: statements, proofs `sorry`.

These are the fields of M07's `IsWeakLogModulus` for `v = ψ + S`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ### Disc: continuity and Laplacian of the potential of a finite piece -/

/-- Continuity on `𝔻` from continuity on every closed disc `closedBall 0 r`, `r < 1`. -/
theorem continuousOn_disc_of_closedBall {f : ℂ → ℝ}
    (h : ∀ r : ℝ, 0 < r → r < 1 → ContinuousOn f (closedBall 0 r)) : ContinuousOn f 𝔻 := by
  intro z hz
  have hz1 := norm_lt_one_of_mem_disc hz
  have hr0 : 0 < (‖z‖ + 1) / 2 := by positivity
  have hr1 : (‖z‖ + 1) / 2 < 1 := by linarith
  have hzr : z ∈ ball (0 : ℂ) ((‖z‖ + 1) / 2) := by
    rw [mem_ball, dist_zero_right]; linarith
  exact (((h _ hr0 hr1).mono ball_subset_closedBall).continuousAt
    (isOpen_ball.mem_nhds hzr)).continuousWithinAt

theorem log_one_div_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ Real.log (1 / x) := by
  rcases hx0.eq_or_lt with h | h
  · simp [← h]
  · exact Real.log_nonneg (by rw [le_div_iff₀ h]; linarith)

/-- The truncated Green kernel `log max(ρ(ζ,z), t)`. -/
def kerDiscTrunc (t : ℝ) (z ζ : ℂ) : ℝ := Real.log (max (pseudoHyp ζ z) t)

theorem abs_kerDiscTrunc_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {z ζ : ℂ} (hz : z ∈ 𝔻)
    (hζ : ζ ∈ 𝔻) : |kerDiscTrunc t z ζ| ≤ -Real.log t := by
  have hp1 := pseudoHyp_lt_one hζ hz
  have hmax : t ≤ max (pseudoHyp ζ z) t := le_max_right _ _
  have hmax1 : max (pseudoHyp ζ z) t ≤ 1 := max_le hp1.le ht1
  rw [kerDiscTrunc, abs_of_nonpos (Real.log_nonpos (by linarith) hmax1)]
  have := Real.log_le_log ht0 hmax
  linarith

theorem abs_kerDisc_sub_trunc_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) {z ζ : ℂ}
    (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) (hζz : ζ ≠ z) :
    |kerDisc z ζ - kerDiscTrunc t z ζ| ≤
      (ball z (2 * t)).indicator (fun w ↦ 1 + Real.log (1 / ‖z - w‖)) ζ := by
  have hp1 := pseudoHyp_lt_one hζ hz
  have hD := norm_one_sub_conj_mul_pos hζ hz
  have hp0 : 0 < pseudoHyp ζ z := by
    rw [pseudoHyp]; exact div_pos (norm_pos_iff.2 (sub_ne_zero.2 hζz)) hD
  have hgnn : ∀ w ∈ ball z (2 * t), 0 ≤ 1 + Real.log (1 / ‖z - w‖) := by
    intro w hw
    have : ‖z - w‖ ≤ 1 := by
      rw [← dist_eq_norm, dist_comm]; exact (mem_ball.1 hw).le.trans (by linarith)
    linarith [log_one_div_nonneg (norm_nonneg (z - w)) this]
  by_cases hpt : t ≤ pseudoHyp ζ z
  · have : kerDisc z ζ - kerDiscTrunc t z ζ = 0 := by
      simp [kerDisc, kerDiscTrunc, max_eq_left hpt]
    rw [this, abs_zero]
    exact indicator_nonneg hgnn _
  · push Not at hpt
    have hD2 : ‖1 - conj ζ * z‖ ≤ 2 := by
      have := norm_one_sub_conj_mul_le ζ z
      have := norm_lt_one_of_mem_disc hζ
      have := norm_lt_one_of_mem_disc hz
      nlinarith [norm_nonneg ζ, norm_nonneg z]
    have hzz : ‖ζ - z‖ = pseudoHyp ζ z * ‖1 - conj ζ * z‖ := by
      rw [pseudoHyp, div_mul_cancel₀ _ hD.ne']
    have hball : ζ ∈ ball z (2 * t) := by
      rw [mem_ball, dist_eq_norm, hzz]
      calc pseudoHyp ζ z * ‖1 - conj ζ * z‖ < t * ‖1 - conj ζ * z‖ :=
            mul_lt_mul_of_pos_right hpt hD
        _ ≤ t * 2 := by gcongr
        _ = 2 * t := by ring
    rw [indicator_of_mem hball]
    have hdiff : kerDisc z ζ - kerDiscTrunc t z ζ = Real.log (pseudoHyp ζ z) - Real.log t := by
      simp [kerDisc, kerDiscTrunc, max_eq_right hpt.le]
    have hzζ : 0 < ‖z - ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 hζz.symm)
    rw [hdiff, abs_of_nonpos (by linarith [Real.log_le_log hp0 hpt.le])]
    have h1 : -Real.log (pseudoHyp ζ z) = Real.log ‖1 - conj ζ * z‖ + Real.log (1 / ‖z - ζ‖) := by
      rw [pseudoHyp, Real.log_div (norm_pos_iff.2 (sub_ne_zero.2 hζz)).ne' hD.ne', one_div,
        Real.log_inv, norm_sub_rev]; ring
    have h2 : Real.log ‖1 - conj ζ * z‖ ≤ 1 := by
      have := Real.log_le_sub_one_of_pos hD; linarith
    have h3 : Real.log t ≤ 0 := Real.log_nonpos ht0.le (by linarith)
    linarith

/-- Continuity of the potential of a finite piece of `ν` (disc, Green kernel). -/
theorem continuousOn_setIntegral_kerDisc {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hν : MeasClassDisc ν Cd R₀) {E : Set ℂ} (hE : MeasurableSet E) (hE𝔻 : E ⊆ 𝔻)
    (hfin : ν E < ∞) : ContinuousOn (fun z ↦ ∫ ζ in E, kerDisc z ζ ∂ν) 𝔻 := by
  have : IsFiniteMeasure (ν.restrict E) := isFiniteMeasure_restrict.2 hfin.ne
  have hmeas_t : ∀ t z, Measurable (kerDiscTrunc t z) := fun t z ↦ by
    unfold kerDiscTrunc pseudoHyp; fun_prop
  have hint_t : ∀ t z, 0 < t → t ≤ 1 → z ∈ 𝔻 → IntegrableOn (kerDiscTrunc t z) E ν := by
    intro t z ht0 ht1 hz
    refine Integrable.of_bound (hmeas_t t z).aestronglyMeasurable (-Real.log t) ?_
    refine (ae_restrict_iff' hE).2 (Eventually.of_forall fun ζ hζ ↦ ?_)
    rw [Real.norm_eq_abs]; exact abs_kerDiscTrunc_le ht0 ht1 hz (hE𝔻 hζ)
  have hcont_t : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ContinuousOn (fun z ↦ ∫ ζ in E, kerDiscTrunc t z ζ ∂ν) 𝔻 := by
    intro t ht0 ht1
    refine continuousOn_of_dominated (bound := fun _ ↦ -Real.log t)
      (fun z _ ↦ (hmeas_t t z).aestronglyMeasurable) ?_ (integrable_const _) ?_
    · intro z hz
      refine (ae_restrict_iff' hE).2 (Eventually.of_forall fun ζ hζ ↦ ?_)
      rw [Real.norm_eq_abs]; exact abs_kerDiscTrunc_le ht0 ht1 hz (hE𝔻 hζ)
    · refine (ae_restrict_iff' hE).2 (Eventually.of_forall fun ζ hζ ↦ ?_)
      have h1 : ContinuousOn (fun z ↦ max (pseudoHyp ζ z) t) 𝔻 :=
        ContinuousOn.sup (continuousOn_pseudoHyp (hE𝔻 hζ)) continuousOn_const
      exact h1.log fun z _ ↦ (lt_of_lt_of_le ht0 (le_max_right _ _)).ne'
  refine continuousOn_disc_of_closedBall fun r hr0 hr1 ↦ ?_
  have hK𝔻 : closedBall (0 : ℂ) r ⊆ 𝔻 := closedBall_subset_ball hr1
  refine continuousOn_of_uniform_approx_of_continuousOn fun u hu ↦ ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨δ, hδ0, hδ1, hsmall⟩ := logSmall_disc ⟨Cd, hν.doubling⟩ hν.finite hK𝔻
    (isCompact_closedBall 0 r) (half_pos hε)
  set t := δ / 2 with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 2 := by linarith
  refine ⟨fun z ↦ ∫ ζ in E, kerDiscTrunc t z ζ ∂ν, (hcont_t t ht0 (by linarith)).mono hK𝔻,
    fun z hz ↦ hεu ?_⟩
  have hz𝔻 := hK𝔻 hz
  have h2t : 2 * t = δ := by rw [htdef]; ring
  have hne : ∀ᵐ ζ ∂ν, ζ ≠ z := by
    rw [ae_iff]; simpa using hν.measure_singleton hz𝔻
  have hpt : ∀ᵐ ζ ∂ν.restrict E, ‖kerDisc z ζ - kerDiscTrunc t z ζ‖ ≤
      (ball z δ).indicator (fun w ↦ 1 + Real.log (1 / ‖z - w‖)) ζ := by
    filter_upwards [ae_restrict_mem hE, ae_restrict_of_ae hne] with ζ hζ hζz
    rw [Real.norm_eq_abs, ← h2t]
    exact abs_kerDisc_sub_trunc_le ht0 ht1 hz𝔻 (hE𝔻 hζ) hζz
  have hlint : ∫⁻ ζ in E, ENNReal.ofReal
      ((ball z δ).indicator (fun w ↦ 1 + Real.log (1 / ‖z - w‖)) ζ) ∂ν ≤
      ENNReal.ofReal (ε / 2) := by
    calc ∫⁻ ζ in E, ENNReal.ofReal
          ((ball z δ).indicator (fun w ↦ 1 + Real.log (1 / ‖z - w‖)) ζ) ∂ν
        ≤ ∫⁻ ζ, ENNReal.ofReal
          ((ball z δ).indicator (fun w ↦ 1 + Real.log (1 / ‖z - w‖)) ζ) ∂ν :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂ν := by
          rw [← lintegral_indicator isOpen_ball.measurableSet]
          congr 1; ext ζ
          by_cases h : ζ ∈ ball z δ <;> simp [h]
      _ ≤ ENNReal.ofReal (ε / 2) := hsmall z hz
  -- the difference is integrable
  have hdiff_int : IntegrableOn (fun ζ ↦ kerDisc z ζ - kerDiscTrunc t z ζ) E ν := by
    refine ⟨(by unfold kerDisc kerDiscTrunc pseudoHyp; fun_prop :
      Measurable fun ζ ↦ kerDisc z ζ - kerDiscTrunc t z ζ).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt ?_ (hlint.trans_lt ENNReal.ofReal_lt_top)
    refine lintegral_mono_ae ?_
    filter_upwards [hpt] with ζ hζ
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hζ
  have hint1 : IntegrableOn (kerDisc z) E ν := by
    have := hdiff_int.add (hint_t t z ht0 (by linarith) hz𝔻)
    refine this.congr_fun (fun ζ _ ↦ ?_) hE
    simp
  rw [dist_eq_norm, ← integral_sub hint1 (hint_t t z ht0 (by linarith) hz𝔻)]
  refine (norm_integral_le_lintegral_norm _).trans_lt ?_
  have h1 : ∫⁻ ζ in E, ENNReal.ofReal ‖kerDisc z ζ - kerDiscTrunc t z ζ‖ ∂ν ≤
      ENNReal.ofReal (ε / 2) := by
    refine le_trans (lintegral_mono_ae ?_) hlint
    filter_upwards [hpt] with ζ hζ
    exact ENNReal.ofReal_le_ofReal hζ
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_ofReal (by linarith)] at h2
  linarith

/-- Splitting the Green kernel. -/
theorem kerDisc_eq_sub {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) (hne : z ≠ ζ) :
    kerDisc z ζ = Real.log ‖z - ζ‖ - Real.log ‖1 - conj ζ * z‖ := by
  rw [kerDisc, pseudoHyp, norm_sub_rev, Real.log_div (norm_pos_iff.2 (sub_ne_zero.2 hne)).ne'
    (norm_one_sub_conj_mul_pos hζ hz).ne']

theorem abs_log_norm_one_sub_le {z ζ : ℂ} {r : ℝ} (hr : r < 1) (hz : ‖z‖ ≤ r) (hζ : ζ ∈ 𝔻) :
    |Real.log ‖1 - conj ζ * z‖| ≤ Real.log 2 - Real.log (1 - r) := by
  have hζ1 := norm_lt_one_of_mem_disc hζ
  have h1 : 1 - r ≤ ‖1 - conj ζ * z‖ := by
    have := one_sub_mul_le_norm_one_sub_conj_mul ζ z
    nlinarith [norm_nonneg ζ, norm_nonneg z]
  have h2 : ‖1 - conj ζ * z‖ ≤ 2 := by
    have := norm_one_sub_conj_mul_le ζ z
    nlinarith [norm_nonneg ζ, norm_nonneg z]
  have hpos : 0 < 1 - r := by linarith
  have hl1 := Real.log_le_log hpos h1
  have hl2 := Real.log_le_log (hpos.trans_le h1) h2
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogr : Real.log (1 - r) ≤ 0 := Real.log_nonpos hpos.le (by
    have := norm_nonneg z; linarith)
  rw [abs_le]; constructor <;> linarith

/-- **Laplacian of the potential of a finite piece** (disc, by Fubini and M02). -/
theorem integral_setIntegral_kerDisc_mul_laplacian {ν : Measure ℂ} {E : Set ℂ}
    (hE : MeasurableSet E) (hE𝔻 : E ⊆ 𝔻) (hfin : ν E < ∞) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ 𝔻) :
    ∫ z, (∫ ζ in E, kerDisc z ζ ∂ν) * Laplacian.laplacian χ z =
      2 * Real.pi * ∫ ζ in E, χ ζ ∂ν := by
  have : IsFiniteMeasure (ν.restrict E) := isFiniteMeasure_restrict.2 hfin.ne
  set K := tsupport χ with hK
  have hKc : IsCompact K := hc
  obtain ⟨r, hr1, hKr⟩ := exists_lt_subset_ball (isClosed_tsupport χ) hs
  obtain ⟨hΔc, hΔs⟩ := laplacian_testFunction hχ
  set Δ := Laplacian.laplacian χ with hΔdef
  have hΔ0 : ∀ z, z ∉ K → Δ z = 0 := fun z hz ↦
    image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hΔs h))
  obtain ⟨D, hD⟩ := hΔc.bounded_above_of_compact_support
    (IsCompact.of_isClosed_subset hKc (isClosed_tsupport _) hΔs)
  obtain ⟨M, hM⟩ := integrableOn_log_norm_sub_uniform hKc (isCompact_closedBall (0 : ℂ) 1)
  set r' := max r 0 with hr'
  have hr'1 : r' < 1 := max_lt hr1 one_pos
  set CK := Real.log 2 - Real.log (1 - r') with hCK
  have hCK0 : 0 ≤ CK := by
    have h1 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have h2 := Real.log_nonpos (show 0 ≤ 1 - r' by linarith)
      (by have := le_max_right r 0; linarith)
    linarith
  have hKn : ∀ z ∈ K, ‖z‖ ≤ r' := fun z hz ↦ by
    have := hKr hz; rw [mem_ball, dist_zero_right] at this
    exact this.le.trans (le_max_left _ _)
  set f : ℂ × ℂ → ℝ := fun p ↦ kerDisc p.1 p.2 * Δ p.1 with hf
  have hfm : Measurable f := by
    have : Measurable Δ := hΔc.measurable
    simp only [hf, kerDisc, pseudoHyp]; fun_prop
  have hvol0 : ∀ ζ : ℂ, ∀ᵐ z ∂(volume : Measure ℂ), z ≠ ζ := fun ζ ↦ by
    rw [ae_iff]; simp
  -- integrability in `z` for fixed `ζ ∈ 𝔻`
  have hzint : ∀ ζ ∈ 𝔻, Integrable (fun z ↦ f (z, ζ)) ∧
      ∫ z, ‖f (z, ζ)‖ ≤ D * (M + CK * volume.real K) := by
    intro ζ hζ
    have hζ1 : ζ ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right]; exact (norm_lt_one_of_mem_disc hζ).le
    obtain ⟨hlogint, hlogM⟩ := hM ζ hζ1
    have hcont2 : ContinuousOn (fun z ↦ Real.log ‖1 - conj ζ * z‖) K := by
      refine ContinuousOn.log (by fun_prop) fun z hz ↦ ?_
      exact (norm_one_sub_conj_mul_pos hζ (hs hz)).ne'
    have hkint : IntegrableOn (fun z ↦ kerDisc z ζ) K := by
      have h1 := hlogint.sub (hcont2.integrableOn_compact hKc)
      refine h1.congr_fun_ae ?_
      filter_upwards [ae_restrict_mem hKc.measurableSet, ae_restrict_of_ae (hvol0 ζ)] with z hz hzζ
      exact (kerDisc_eq_sub (hs hz) hζ hzζ).symm
    have hfK : IntegrableOn (fun z ↦ f (z, ζ)) K := hkint.mul_continuousOn hΔc.continuousOn hKc
    have hfint : Integrable (fun z ↦ f (z, ζ)) :=
      hfK.integrable_of_forall_notMem_eq_zero fun z hz ↦ by simp [hf, hΔ0 z hz]
    refine ⟨hfint, ?_⟩
    have hpt : ∀ᵐ z ∂volume.restrict K, ‖f (z, ζ)‖ ≤ D * (|Real.log ‖z - ζ‖| + CK) := by
      filter_upwards [ae_restrict_mem hKc.measurableSet, ae_restrict_of_ae (hvol0 ζ)] with z hz hzζ
      simp only [hf, norm_mul, Real.norm_eq_abs]
      rw [kerDisc_eq_sub (hs hz) hζ hzζ]
      have h1 := abs_log_norm_one_sub_le hr'1 (hKn z hz) hζ
      have h2 : |Real.log ‖z - ζ‖ - Real.log ‖1 - conj ζ * z‖| ≤ |Real.log ‖z - ζ‖| + CK :=
        (abs_sub _ _).trans (by linarith)
      have h3 : |Δ z| ≤ D := by have := hD z; rwa [Real.norm_eq_abs] at this
      calc |Real.log ‖z - ζ‖ - Real.log ‖1 - conj ζ * z‖| * |Δ z|
          ≤ (|Real.log ‖z - ζ‖| + CK) * D := by
            apply mul_le_mul h2 h3 (abs_nonneg _); positivity
        _ = D * (|Real.log ‖z - ζ‖| + CK) := by ring
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun z hz ↦ by
      simp [hf, hΔ0 z hz]]
    calc ∫ z in K, ‖f (z, ζ)‖ ≤ ∫ z in K, D * (|Real.log ‖z - ζ‖| + CK) :=
          setIntegral_mono_ae_restrict hfK.norm
            ((hlogint.abs.add (integrableOn_const hKc.measure_lt_top.ne)).const_mul D) hpt
      _ = D * ((∫ z in K, |Real.log ‖z - ζ‖|) + CK * volume.real K) := by
          rw [integral_const_mul, integral_add hlogint.abs
            (integrableOn_const hKc.measure_lt_top.ne), setIntegral_const, smul_eq_mul, mul_comm CK]
      _ ≤ D * (M + CK * volume.real K) := by
          have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
          gcongr
  -- integrability on the product
  have hprod : Integrable f ((volume : Measure ℂ).prod (ν.restrict E)) := by
    rw [integrable_prod_iff' hfm.aestronglyMeasurable]
    refine ⟨(ae_restrict_iff' hE).2 (Eventually.of_forall fun ζ hζ ↦ (hzint ζ (hE𝔻 hζ)).1), ?_⟩
    refine Integrable.of_bound ((hfm.norm.stronglyMeasurable.integral_prod_left'
      (μ := volume)).aestronglyMeasurable) (D * (M + CK * volume.real K)) ?_
    refine (ae_restrict_iff' hE).2 (Eventually.of_forall fun ζ hζ ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    exact (hzint ζ (hE𝔻 hζ)).2
  have hswap := integral_integral_swap (f := fun z ζ ↦ kerDisc z ζ * Δ z) hprod
  calc ∫ z, (∫ ζ in E, kerDisc z ζ ∂ν) * Δ z
      = ∫ z, ∫ ζ in E, kerDisc z ζ * Δ z ∂ν := by
        congr 1; ext z; rw [integral_mul_const]
    _ = ∫ ζ in E, ∫ z, kerDisc z ζ * Δ z ∂volume ∂ν := hswap
    _ = ∫ ζ in E, 2 * Real.pi * χ ζ ∂ν := by
        refine setIntegral_congr_fun hE fun ζ hζ ↦ ?_
        exact integral_log_pseudoHyp_mul_laplacian
          (hχ.of_le (WithTop.coe_le_coe.2 le_top)) hc hs (hE𝔻 hζ)
    _ = 2 * Real.pi * ∫ ζ in E, χ ζ ∂ν := integral_const_mul _ _


theorem continuousOn_kerDisc_left {w : ℂ} (hw : w ∈ 𝔻) :
    ContinuousOn (fun z ↦ kerDisc z w) (𝔻 \ {w}) := by
  refine ContinuousOn.log ((continuousOn_pseudoHyp hw).mono diff_subset) fun z hz ↦ ?_
  rw [pseudoHyp]
  exact (div_pos (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hz.2)))
    (norm_one_sub_conj_mul_pos hw hz.1)).ne'

theorem integrableOn_kerDisc_left {w : ℂ} (hw : w ∈ 𝔻) {K : Set ℂ} (hK : IsCompact K)
    (hK𝔻 : K ⊆ 𝔻) : IntegrableOn (fun z ↦ kerDisc z w) K := by
  have h1 : IntegrableOn (fun z ↦ Real.log ‖z - w‖) K :=
    (locallyIntegrable_log_norm_sub w).integrableOn_isCompact hK
  have h2 : ContinuousOn (fun z ↦ Real.log ‖1 - conj w * z‖) K :=
    ContinuousOn.log (by fun_prop) fun z hz ↦ (norm_one_sub_conj_mul_pos hw (hK𝔻 hz)).ne'
  refine (h1.sub (h2.integrableOn_compact hK)).congr_fun_ae ?_
  have hvol : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ w := by rw [ae_iff]; simp
  filter_upwards [ae_restrict_mem hK.measurableSet, ae_restrict_of_ae hvol] with z hz hzw
  exact (kerDisc_eq_sub (hK𝔻 hz) hw hzw).symm

/-- Test-function facts packaged. -/
theorem testFunction_facts {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ 𝔻) :
    Continuous (Laplacian.laplacian χ) ∧ IsCompact (tsupport χ) ∧
      (∀ z, z ∉ tsupport χ → Laplacian.laplacian χ z = 0) ∧
      ∃ r < 1, tsupport χ ⊆ ball 0 r := by
  obtain ⟨hΔc, hΔs⟩ := laplacian_testFunction hχ
  obtain ⟨r, hr1, hKr⟩ := exists_lt_subset_ball (isClosed_tsupport χ) hs
  exact ⟨hΔc, hc, fun z hz ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hΔs h)), r, hr1, hKr⟩

/-- Integrability of `f · Δχ` for `f` integrable on `tsupport χ`. -/
theorem integrable_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) {f : ℂ → ℝ} (hf : IntegrableOn f (tsupport χ)) :
    Integrable fun z ↦ f z * Laplacian.laplacian χ z := by
  obtain ⟨hΔc, hΔs⟩ := laplacian_testFunction hχ
  exact (hf.mul_continuousOn hΔc.continuousOn hc).integrable_of_forall_notMem_eq_zero
    fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hΔs h))]

/-- Laplacian of the node part. -/
theorem integral_nodes_kerDisc_mul_laplacian {L : Multiset ℂ} (hL : ∀ w ∈ L, w ∈ 𝔻)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ 𝔻) :
    Integrable (fun z ↦ (L.map (kerDisc z)).sum * Laplacian.laplacian χ z) ∧
    ∫ z, (L.map (kerDisc z)).sum * Laplacian.laplacian χ z = 2 * Real.pi * (L.map χ).sum := by
  induction L using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have ha : a ∈ 𝔻 := hL a (Multiset.mem_cons_self a t)
    obtain ⟨ih1, ih2⟩ := ih fun w hw ↦ hL w (Multiset.mem_cons_of_mem hw)
    have h1 : Integrable fun z ↦ kerDisc z a * Laplacian.laplacian χ z :=
      integrable_mul_laplacian hχ hc (integrableOn_kerDisc_left ha hc hs)
    have e : (fun z ↦ ((a ::ₘ t).map (kerDisc z)).sum * Laplacian.laplacian χ z) =
        fun z ↦ kerDisc z a * Laplacian.laplacian χ z +
          (t.map (kerDisc z)).sum * Laplacian.laplacian χ z := by
      ext z; simp [add_mul]
    rw [e]
    refine ⟨h1.add ih1, ?_⟩
    rw [integral_add h1 ih1, ih2, Multiset.map_cons, Multiset.sum_cons,
      show ∫ z, kerDisc z a * Laplacian.laplacian χ z = 2 * Real.pi * χ a from
        integral_log_pseudoHyp_mul_laplacian (hχ.of_le (WithTop.coe_le_coe.2 le_top)) hc hs ha]
    ring

/-- Laplacian of one cell potential. -/
theorem integral_cellPot_kerDisc_mul_laplacian {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hν : MeasClassDisc ν Cd R₀) {R : ℕ → Set ℂ} {Λ : ℕ → Multiset ℂ} {i : ℕ}
    (hR : MeasurableSet (R i)) (hR𝔻 : R i ⊆ 𝔻) (hfin : ν (R i) < ∞) (hΛ : ∀ w ∈ Λ i, w ∈ 𝔻)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ 𝔻) :
    Integrable (fun z ↦ cellPot kerDisc ν R Λ i z * Laplacian.laplacian χ z) ∧
    ∫ z, cellPot kerDisc ν R Λ i z * Laplacian.laplacian χ z =
      2 * Real.pi * (((Λ i).map χ).sum - ∫ ζ in R i, χ ζ ∂ν) := by
  obtain ⟨h1, h2⟩ := integral_nodes_kerDisc_mul_laplacian hΛ hχ hc hs
  have hU : Integrable fun z ↦ (∫ ζ in R i, kerDisc z ζ ∂ν) * Laplacian.laplacian χ z :=
    integrable_mul_laplacian hχ hc
      (((continuousOn_setIntegral_kerDisc hν hR hR𝔻 hfin).mono hs).integrableOn_compact hc)
  have e : (fun z ↦ cellPot kerDisc ν R Λ i z * Laplacian.laplacian χ z) =
      fun z ↦ ((Λ i).map (kerDisc z)).sum * Laplacian.laplacian χ z -
        (∫ ζ in R i, kerDisc z ζ ∂ν) * Laplacian.laplacian χ z := by
    ext z; simp [cellPot, sub_mul]
  rw [e]
  refine ⟨h1.sub hU, ?_⟩
  rw [integral_sub h1 hU, h2, integral_setIntegral_kerDisc_mul_laplacian hR hR𝔻 hfin hχ hc hs]
  ring

theorem finsum_nodeCount_mul {Λ : ℕ → Multiset ℂ} {G : Finset ℕ} {χ : ℂ → ℝ}
    (hG : ∀ i, i ∉ G → ∀ w ∈ Λ i, χ w = 0) :
    ∑ᶠ ζ, (nodeCount Λ ζ : ℝ) * χ ζ = ∑ i ∈ G, ((Λ i).map χ).sum := by
  classical
  set Z := G.biUnion fun i ↦ (Λ i).toFinset with hZ
  have hcnt : ∀ ζ, χ ζ ≠ 0 → (Function.support fun i ↦ (Λ i).count ζ) ⊆ G := by
    intro ζ hχ i hi
    by_contra hiG
    exact hχ (hG i hiG ζ (Multiset.count_ne_zero.1 hi))
  have hsupp : (Function.support fun ζ ↦ (nodeCount Λ ζ : ℝ) * χ ζ) ⊆ Z := by
    intro ζ hζ
    have hχ : χ ζ ≠ 0 := fun h ↦ hζ (by simp [h])
    have hn : nodeCount Λ ζ ≠ 0 := fun h ↦ hζ (by simp [h])
    rw [nodeCount, finsum_eq_sum_of_support_subset _ (hcnt ζ hχ)] at hn
    obtain ⟨i, hi, hci⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    exact Finset.mem_biUnion.2 ⟨i, hi, Multiset.mem_toFinset.2 (Multiset.count_ne_zero.1 hci)⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hn : ∀ ζ ∈ Z, (nodeCount Λ ζ : ℝ) * χ ζ = ∑ i ∈ G, ((Λ i).count ζ : ℝ) * χ ζ := by
    intro ζ _
    by_cases hχ : χ ζ = 0
    · simp [hχ]
    rw [nodeCount, finsum_eq_sum_of_support_subset _ (hcnt ζ hχ), ← Finset.sum_mul]
    push_cast; rfl
  rw [Finset.sum_congr rfl hn, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hsub : (Λ i).toFinset ⊆ Z := fun ζ hζ ↦ Finset.mem_biUnion.2 ⟨i, hi, hζ⟩
  rw [Finset.sum_multiset_map_count (Λ i) χ, Finset.sum_subset hsub (fun ζ _ hζ ↦ by
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hζ; simp [hζ])]
  exact Finset.sum_congr rfl fun ζ _ ↦ by rw [nsmul_eq_mul]

theorem tsum_eq_sum_add_tsum_ite {f : ℕ → ℝ} (hf : Summable f) (G : Finset ℕ) :
    ∑' i, f i = ∑ i ∈ G, f i + ∑' i, (if i ∈ G then 0 else f i) := by
  have hg : Summable fun i ↦ if i ∈ G then f i else 0 :=
    summable_of_ne_finset_zero (s := G) fun i hi ↦ by simp [hi]
  have hh : Summable fun i ↦ if i ∈ G then 0 else f i := by
    have := hf.sub hg
    refine this.congr fun i ↦ ?_
    by_cases hi : i ∈ G <;> simp [hi]
  have e : ∑' i, f i = ∑' i, ((if i ∈ G then f i else 0) + (if i ∈ G then 0 else f i)) := by
    congr 1; ext i; by_cases hi : i ∈ G <;> simp [hi]
  rw [e, hg.tsum_add hh, tsum_eq_sum (s := G) (fun i hi ↦ by simp [hi])]
  congr 1
  exact Finset.sum_congr rfl fun i hi ↦ by simp [hi]

theorem integrableOn_nodes_kerDisc {L : Multiset ℂ} (hL : ∀ w ∈ L, w ∈ 𝔻) {K : Set ℂ}
    (hK : IsCompact K) (hK𝔻 : K ⊆ 𝔻) : IntegrableOn (fun z ↦ (L.map (kerDisc z)).sum) K := by
  induction L using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have := (integrableOn_kerDisc_left (hL a (Multiset.mem_cons_self a t)) hK hK𝔻).add
      (ih fun w hw ↦ hL w (Multiset.mem_cons_of_mem hw))
    refine this.congr_fun (fun z _ ↦ ?_) hK.measurableSet
    simp

theorem continuousAt_nodes_kerDisc {L : Multiset ℂ} (hL : ∀ w ∈ L, w ∈ 𝔻) {z₀ : ℂ}
    (hz₀ : z₀ ∈ 𝔻) (hz₀L : z₀ ∉ L) : ContinuousAt (fun z ↦ (L.map (kerDisc z)).sum) z₀ := by
  induction L using Multiset.induction_on with
  | empty => simp [continuousAt_const]
  | cons a t ih =>
    have ha := hL a (Multiset.mem_cons_self a t)
    have hne : z₀ ≠ a := fun h ↦ hz₀L (h ▸ Multiset.mem_cons_self a t)
    have h1 : ContinuousAt (fun z ↦ kerDisc z a) z₀ :=
      (continuousOn_kerDisc_left ha).continuousAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds
        ⟨hz₀, hne⟩)
    have h2 := ih (fun w hw ↦ hL w (Multiset.mem_cons_of_mem hw))
      (fun h ↦ hz₀L (Multiset.mem_cons_of_mem h))
    have := h1.add h2
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact this

theorem local_structure_disc {ν : Measure ℂ} {Cd : ℝ≥0} {R₁ : ℝ} {N : ℕ} {η A B : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hν : MeasClassDisc ν Cd R₁) (hη : 0 < η) (hA : 0 < A) (hB : 0 ≤ B)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c)
    (hN : IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ) (hm2 : ∀ i, 2 ≤ m i)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ G : Finset ℕ, (∀ i ∉ G, ∀ w ∈ R i, w ∉ closedBall (0 : ℂ) r) ∧
      (∀ i ∉ G, ∀ w ∈ Λ i, w ∉ closedBall (0 : ℂ) r) ∧
      ∃ u : ℕ → ℝ, (∀ i, 0 ≤ u i) ∧ Summable u ∧
        ∀ i ∉ G, ∀ z ∈ closedBall (0 : ℂ) r, |cellPot kerDisc ν R Λ i z| ≤ u i := by
  obtain ⟨C1, -, hcl⟩ := claim1_disc_quant Cd R₁ 0
  have hci := hC.center_mem'
  have hρ : ∀ i, 0 < massRadiusDisc ν (c i) := fun i ↦ (hcl ν hν _ (hci i) _ (hci i)).1
  have hρR : ∀ i, massRadiusDisc ν (c i) ≤ R₁ := fun i ↦ (hcl ν hν _ (hci i) _ (hci i)).2.1
  obtain ⟨CD, hCD0, hCD⟩ := abs_cellPot_le_disc_far A B R₁ 1 N hA hB one_pos
  set L := (2 * (A + B) + 1) * max R₁ 0 + 2 with hL
  have hL0 : 0 < L := by positivity
  obtain ⟨Cf, hCf⟩ := farField_sum_le_disc Cd R₁ η A L hη hL0
  have hK𝔻 : closedBall (0 : ℂ) r ⊆ 𝔻 := closedBall_subset_ball hr1
  have hGfin := finite_cells_disc hν hη hC (closedBall 0 r) hK𝔻 (isCompact_closedBall _ _) L
  set G := hGfin.toFinset with hGdef
  have hfar : ∀ i ∉ G, ∀ z ∈ closedBall (0 : ℂ) r, L ≤ hypDist z (c i) := by
    intro i hi z hz
    by_contra h; push Not at h
    exact hi ((Set.Finite.mem_toFinset _).2 ⟨z, hz, h⟩)
  have hR₁ : ∀ i, massRadiusDisc ν (c i) ≤ max R₁ 0 := fun i ↦ (hρR i).trans (le_max_left _ _)
  have hAB : ∀ i, 2 * (A + B) * massRadiusDisc ν (c i) + 1 ≤ L := fun i ↦ by
    have := mul_le_mul_of_nonneg_left (hR₁ i) (by positivity : (0:ℝ) ≤ 2 * (A + B))
    have h2 : 0 ≤ max R₁ 0 := le_max_right _ _
    rw [hL]; nlinarith
  refine ⟨G, ?_, ?_, ?_⟩
  · intro i hi w hw hwK
    have h1 := hfar i hi w hwK
    rw [hypDist_comm] at h1
    have h2 := hC.subset i w hw
    have := hAB i
    nlinarith [hρ i]
  · intro i hi w hw hwK
    have h1 := hfar i hi w hwK
    rw [hypDist_comm] at h1
    have h2 := hN.near i w hw
    have := hAB i
    nlinarith [hρ i]
  · set u : ℕ → ℝ := fun i ↦ if i ∈ G then 0 else
      CD * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 / (1 - r) ^ 3 with hu
    have hr' : 0 < 1 - r := by linarith
    have hu0 : ∀ i, 0 ≤ u i := fun i ↦ by
      simp only [hu]; split_ifs
      · exact le_rfl
      · have := one_sub_normSq_pos (hci i); positivity
    refine ⟨u, hu0, ?_, ?_⟩
    · refine summable_of_sum_le hu0 (c := CD * max Cf 0 / (1 - r) ^ 3) fun F ↦ ?_
      have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) r := mem_closedBall_self hr0
      have hFG := hCf ν N R c hν hC 0 (mem_ball_self one_pos) (F.filter (· ∉ G))
        fun i hi ↦ hfar i (Finset.mem_filter.1 hi).2 0 h0
      have hsimp : ∀ i, (1 - ‖(0 : ℂ)‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
          ‖1 - conj (0 : ℂ) * c i‖ ^ 3 = ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 := by
        intro i; simp
      simp_rw [hsimp] at hFG
      rw [← Finset.sum_filter_add_sum_filter_not F (· ∈ G)]
      have e1 : ∑ i ∈ F.filter (· ∈ G), u i = 0 :=
        Finset.sum_eq_zero fun i hi ↦ by simp [hu, (Finset.mem_filter.1 hi).2]
      have e2 : ∑ i ∈ F.filter (· ∉ G), u i = CD / (1 - r) ^ 3 *
          ∑ i ∈ F.filter (· ∉ G), ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi ↦ by
          simp only [hu, (Finset.mem_filter.1 hi).2, ite_false]; ring
      rw [e1, e2, zero_add]
      calc CD / (1 - r) ^ 3 *
            ∑ i ∈ F.filter (· ∉ G), ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2
          ≤ CD / (1 - r) ^ 3 * max Cf 0 := by gcongr; exact hFG.trans (le_max_left _ _)
        _ = CD * max Cf 0 / (1 - r) ^ 3 := by ring
    · intro i hi z hz
      have hz𝔻 := hK𝔻 hz
      have hzr : ‖z‖ ≤ r := by rw [mem_closedBall, dist_zero_right] at hz; exact hz
      have hβ := hfar i hi z hz
      have hpos : 0 ≤ 2 * (A + B) * massRadiusDisc ν (c i) := by have := hρ i; positivity
      have hABi := hAB i
      have hb := hCD ν η R c m Λ hC hN i (hm2 i) z hz𝔻 (integrableOn_kerDisc_cell hν hC i hz𝔻)
        (hρ i).le (hρR i) (by linarith) (by linarith)
      simp only [hu, if_neg hi]
      refine hb.trans ?_
      have hc1 := norm_lt_one_of_mem_disc (hci i)
      have hD : 1 - r ≤ ‖1 - conj z * c i‖ := by
        have := one_sub_mul_le_norm_one_sub_conj_mul z (c i)
        nlinarith [norm_nonneg z, norm_nonneg (c i)]
      have hX : 0 ≤ ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 := sq_nonneg _
      have hz2 : 0 ≤ 1 - ‖z‖ ^ 2 := (one_sub_normSq_pos hz𝔻).le
      have h1 : (1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
          ‖1 - conj z * c i‖ ^ 3 ≤ ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 / (1 - r) ^ 3 :=
        div_le_div₀ hX (by nlinarith [norm_nonneg z]) (pow_pos hr' 3)
          (pow_le_pow_left₀ hr'.le hD 3)
      calc CD * ((1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
            ‖1 - conj z * c i‖ ^ 3)
          ≤ CD * (((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 / (1 - r) ^ 3) :=
            mul_le_mul_of_nonneg_left h1 hCD0
        _ = CD * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 / (1 - r) ^ 3 := by ring

/-- `S` is a weak log-modulus datum (M07 `IsWeakLogModulus` fields), plane. -/
theorem multPot_props_plane {ψ : ℂ → ℝ} {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ}
    {η A B : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hw : WeightClassPlane ψ μ Cd R₀) (hη : 0 < η)
    (hC : IsCells univ dist (massRadius (lapNorm μ)) (lapNorm μ) N η A R c)
    (hN : IsNodes univ dist (massRadius (lapNorm μ)) (lapNorm μ) N B R c m Λ)
    (hm : ∀ i, 3 ≤ m i) :
    (∀ K : Set ℂ, IsCompact K → (K ∩ Function.support (nodeCount Λ)).Finite) ∧
    (∀ z, Summable fun i ↦ cellPot kerPlane (lapNorm μ) R Λ i z) ∧
    LocallyIntegrable (fun z ↦ ψ z + multPot kerPlane (lapNorm μ) R Λ z) ∧
    ContinuousOn (fun z ↦ ψ z + multPot kerPlane (lapNorm μ) R Λ z)
      (univ \ Function.support (nodeCount Λ)) ∧
    ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      ∫ z, (ψ z + multPot kerPlane (lapNorm μ) R Λ z) * Laplacian.laplacian χ z =
        2 * Real.pi * ∑ᶠ ζ, (nodeCount Λ ζ : ℝ) * χ ζ := sorry

/-- Same, disc. -/
theorem multPot_props_disc {ψ : ℂ → ℝ} {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ}
    {η A B ρ₀ : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hw : WeightClassDisc ψ μ Cd R₀) (hη : 0 < η) (hρ₀ : 0 < ρ₀)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N η A R c)
    (hN : IsNodes 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N B R c m Λ)
    (hm2 : ∀ i, 2 ≤ m i) (hm3 : ∀ i, massRadiusDisc (lapNorm μ) (c i) ≤ ρ₀ → 3 ≤ m i) :
    (∀ K ⊆ 𝔻, IsCompact K → (K ∩ Function.support (nodeCount Λ)).Finite) ∧
    (∀ z ∈ 𝔻, Summable fun i ↦ cellPot kerDisc (lapNorm μ) R Λ i z) ∧
    LocallyIntegrableOn (fun z ↦ ψ z + multPot kerDisc (lapNorm μ) R Λ z) 𝔻 ∧
    ContinuousOn (fun z ↦ ψ z + multPot kerDisc (lapNorm μ) R Λ z)
      (𝔻 \ Function.support (nodeCount Λ)) ∧
    ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ 𝔻 →
      ∫ z, (ψ z + multPot kerDisc (lapNorm μ) R Λ z) * Laplacian.laplacian χ z =
        2 * Real.pi * ∑ᶠ ζ, (nodeCount Λ ζ : ℝ) * χ ζ := by
  set ν := lapNorm μ with hνdef
  have hν : MeasClassDisc ν Cd (15 * R₀) := hw.meas.lapNorm
  obtain ⟨C1, -, hcl⟩ := claim1_disc_quant Cd (15 * R₀) 0
  have hci := hC.center_mem'
  have hρ : ∀ i, 0 < massRadiusDisc ν (c i) := fun i ↦ (hcl ν hν _ (hci i) _ (hci i)).1
  have hA : 0 < A := lt_of_lt_of_le (half_pos hη) (hC.half_le_A_disc (i := 0) (hρ 0) hη)
  have hN0 := hN.mono_B (B' := max B 0) (fun i ↦ (hρ i).le) (le_max_left _ _)
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hfinI : ∀ w ∈ 𝔻, {i | w ∈ Λ i}.Finite := fun w hw ↦
    (finite_nodeIdx_disc hν hη hC hN0 (K := {w}) (singleton_subset_iff.2 hw)
      isCompact_singleton).subset fun i hi ↦ ⟨w, hi, rfl⟩
  have hnc : ∀ w ∈ 𝔻, nodeCount Λ w ≠ 0 ↔ w ∈ nodeSet Λ := fun w hw ↦
    nodeCount_ne_zero_iff (hfinI w hw)
  have hΛ𝔻 : ∀ i, ∀ w ∈ Λ i, w ∈ 𝔻 := hN.mem
  have hR𝔻 : ∀ i, R i ⊆ 𝔻 := hC.subset_univ
  have hsumm : ∀ z ∈ 𝔻, Summable fun i ↦ cellPot kerDisc ν R Λ i z := fun z hz ↦
    (summable_cellPot_disc hν hη hA hB0 hρ₀ hC hN0 hm2 hm3 hz).of_abs
  -- continuity of the tail and of the single cells
  have hUcont : ∀ i, ContinuousOn (fun z ↦ ∫ ζ in R i, kerDisc z ζ ∂ν) 𝔻 := fun i ↦
    continuousOn_setIntegral_kerDisc hν (hC.measurableSet i) (hR𝔻 i) (hC.measure_lt_top i)
  have hcellAt : ∀ i, ∀ z ∈ 𝔻, z ∉ Λ i → ContinuousAt (cellPot kerDisc ν R Λ i) z := by
    intro i z hz hzΛ
    have h1 := continuousAt_nodes_kerDisc (hΛ𝔻 i) hz hzΛ
    have h2 := (hUcont i).continuousAt (isOpen_ball.mem_nhds hz)
    exact h1.sub h2
  have hloc : ∀ r : ℝ, 0 ≤ r → r < 1 → ∃ G : Finset ℕ,
      (∀ i ∉ G, ∀ w ∈ R i, w ∉ closedBall (0 : ℂ) r) ∧
      (∀ i ∉ G, ∀ w ∈ Λ i, w ∉ closedBall (0 : ℂ) r) ∧
      ∃ u : ℕ → ℝ, (∀ i, 0 ≤ u i) ∧ Summable u ∧
        (∀ i ∉ G, ∀ z ∈ closedBall (0 : ℂ) r, |cellPot kerDisc ν R Λ i z| ≤ u i) ∧
        ContinuousOn (fun z ↦ ∑' i, if i ∈ G then 0 else cellPot kerDisc ν R Λ i z)
          (closedBall 0 r) := by
    intro r hr0 hr1
    obtain ⟨G, hGR, hGΛ, u, hu0, hus, hub⟩ :=
      local_structure_disc hν hη hA hB0 hC hN0 hm2 hr0 hr1
    refine ⟨G, hGR, hGΛ, u, hu0, hus, hub, ?_⟩
    refine continuousOn_tsum (u := u) (fun i ↦ ?_) hus fun i z hz ↦ ?_
    · by_cases hi : i ∈ G
      · simp only [hi, ite_true]; exact continuousOn_const
      · simp only [hi, ite_false]
        intro z hz
        exact (hcellAt i z (closedBall_subset_ball hr1 hz)
          (fun h ↦ hGΛ i hi z h hz)).continuousWithinAt
    · by_cases hi : i ∈ G
      · simp only [hi, ite_true, norm_zero]; exact hu0 i
      · simp only [hi, ite_false, Real.norm_eq_abs]; exact hub i hi z hz
  -- decomposition of `S` on `𝔻`
  have hdec : ∀ (G : Finset ℕ), ∀ z ∈ 𝔻, multPot kerDisc ν R Λ z =
      ∑ i ∈ G, cellPot kerDisc ν R Λ i z +
        ∑' i, (if i ∈ G then 0 else cellPot kerDisc ν R Λ i z) := fun G z hz ↦
    tsum_eq_sum_add_tsum_ite (hsumm z hz) G
  -- radius for a compact set
  have hrad : ∀ K ⊆ 𝔻, IsCompact K → ∃ r, 0 ≤ r ∧ r < 1 ∧ K ⊆ closedBall 0 r := by
    intro K hK hKc
    obtain ⟨r, hr1, hKr⟩ := exists_lt_subset_ball hKc.isClosed hK
    exact ⟨max r 0, le_max_right _ _, max_lt hr1 one_pos,
      hKr.trans ((ball_subset_closedBall).trans (closedBall_subset_closedBall (le_max_left _ _)))⟩
  have hSK : ∀ K ⊆ 𝔻, IsCompact K → IntegrableOn (fun z ↦ multPot kerDisc ν R Λ z) K := by
    intro K hK hKc
    obtain ⟨r, hr0, hr1, hKr⟩ := hrad K hK hKc
    obtain ⟨G, -, -, u, -, -, -, hT⟩ := hloc r hr0 hr1
    have hT' : IntegrableOn (fun z ↦ ∑' i, if i ∈ G then 0 else cellPot kerDisc ν R Λ i z) K :=
      (hT.mono hKr).integrableOn_compact hKc
    have hcells : IntegrableOn (fun z ↦ ∑ i ∈ G, cellPot kerDisc ν R Λ i z) K :=
      integrable_finsetSum G fun i _ ↦ (integrableOn_nodes_kerDisc (hΛ𝔻 i) hKc hK).sub
        (((hUcont i).mono hK).integrableOn_compact hKc)
    refine (hcells.add hT').congr_fun (fun z hz ↦ ?_) hKc.measurableSet
    simp only [Pi.add_apply]
    rw [hdec G z (hK hz)]
  refine ⟨?_, hsumm, ?_, ?_, ?_⟩
  · -- (1) local finiteness of the nodes
    intro K hK hKc
    have hF := finite_nodeIdx_disc hν hη hC hN0 hK hKc
    refine (hF.biUnion fun i _ ↦ (Λ i).finite_toSet).subset ?_
    rintro w ⟨hwK, hw⟩
    obtain ⟨i, hi⟩ := (hnc w (hK hwK)).1 hw
    exact mem_biUnion ⟨w, hi, hwK⟩ hi
  · -- (3) local integrability
    refine (locallyIntegrableOn_iff isOpen_ball.isLocallyClosed).2 fun K hK hKc ↦ ?_
    exact ((hw.weight.continuousOn.mono hK).integrableOn_compact hKc).add (hSK K hK hKc)
  · -- (4) continuity off the nodes
    intro z₀ hz₀
    obtain ⟨hz₀𝔻, hz₀n⟩ := hz₀
    have hz₀N : z₀ ∉ nodeSet Λ := fun h ↦ hz₀n ((hnc z₀ hz₀𝔻).2 h)
    have hz1 := norm_lt_one_of_mem_disc hz₀𝔻
    set r := (‖z₀‖ + 1) / 2 with hr
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := by rw [hr]; linarith
    have hz₀r : z₀ ∈ ball (0 : ℂ) r := by rw [mem_ball, dist_zero_right, hr]; linarith
    obtain ⟨G, -, -, u, -, -, -, hT⟩ := hloc r hr0 hr1
    have hTat := (hT.mono ball_subset_closedBall).continuousAt (isOpen_ball.mem_nhds hz₀r)
    have hψat := hw.weight.continuousOn.continuousAt (isOpen_ball.mem_nhds hz₀𝔻)
    have hGat : ContinuousAt (fun z ↦ ∑ i ∈ G, cellPot kerDisc ν R Λ i z) z₀ :=
      tendsto_finsetSum _ fun i _ ↦ hcellAt i z₀ hz₀𝔻 fun h ↦ hz₀N ⟨i, h⟩
    have hsum := hψat.add (hGat.add hTat)
    refine (hsum.congr ?_).continuousWithinAt
    filter_upwards [isOpen_ball.mem_nhds hz₀𝔻] with z hz
    rw [hdec G z hz]; rfl
  · -- (5) the Laplacian
    intro χ hχ hc hs
    obtain ⟨hΔc, hKc, hΔ0, -⟩ := testFunction_facts hχ hc hs
    obtain ⟨r, hr0, hr1, hKr⟩ := hrad (tsupport χ) hs hKc
    obtain ⟨G, hGR, hGΛ, u, hu0, hus, hub, -⟩ := hloc r hr0 hr1
    have hχ0 : ∀ w, w ∉ closedBall (0 : ℂ) r → χ w = 0 := fun w hw ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hw (hKr h)
    have hcellΔ := fun i ↦ integral_cellPot_kerDisc_mul_laplacian hν (hC.measurableSet i)
      (hR𝔻 i) (hC.measure_lt_top i) (hΛ𝔻 i) hχ hc hs
    -- interchange of sum and integral
    have hΔint : Integrable fun z ↦ |Laplacian.laplacian χ z| :=
      (hΔc.integrable_of_hasCompactSupport (hc.mono' (fun z hz ↦ ?_))).abs
    swap
    · exact by
        by_contra h
        exact hz (by simpa [Function.mem_support] using hΔ0 z h)
    have hbound : ∀ i ∉ G, ∀ z, ‖cellPot kerDisc ν R Λ i z * Laplacian.laplacian χ z‖ ≤ u i * |Laplacian.laplacian χ z| := by
      intro i hi z
      by_cases hz : z ∈ tsupport χ
      · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hub i hi z (hKr hz)) (abs_nonneg _)
      · simp [hΔ0 z hz]
    set w : ℕ → ℝ := fun i ↦ if i ∈ G then ∫ z, ‖cellPot kerDisc ν R Λ i z * Laplacian.laplacian χ z‖
      else u i * ∫ z, |Laplacian.laplacian χ z| with hw'
    have hw0 : ∀ i, 0 ≤ w i := fun i ↦ by
      simp only [hw']; split_ifs
      · exact integral_nonneg fun _ ↦ norm_nonneg _
      · exact mul_nonneg (hu0 i) (integral_nonneg fun _ ↦ abs_nonneg _)
    have hws : Summable w := by
      have h1 : Summable fun i ↦ u i * ∫ z, |Laplacian.laplacian χ z| := hus.mul_right _
      have h2 : Summable fun i ↦ if i ∈ G then ∫ z, ‖cellPot kerDisc ν R Λ i z * Laplacian.laplacian χ z‖ else 0 :=
        summable_of_ne_finset_zero (s := G) fun i hi ↦ by simp [hi]
      refine (h1.add h2).of_nonneg_of_le hw0 fun i ↦ ?_
      simp only [hw']
      split_ifs with hi
      · have := mul_nonneg (hu0 i)
          (integral_nonneg (μ := volume) fun z ↦ abs_nonneg (Laplacian.laplacian χ z))
        linarith
      · simp
    have hlint : ∀ i, ∫⁻ z, ‖cellPot kerDisc ν R Λ i z * Laplacian.laplacian χ z‖ₑ ≤ ENNReal.ofReal (w i) := by
      intro i
      by_cases hi : i ∈ G
      · simp only [hw', hi, ite_true]
        rw [ofReal_integral_norm_eq_lintegral_enorm (hcellΔ i).1]
      · simp only [hw', hi, ite_false]
        rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hΔint.const_mul (u i))
          (Eventually.of_forall fun z ↦ mul_nonneg (hu0 i) (abs_nonneg _))]
        refine lintegral_mono fun z ↦ ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbound i hi z)
    have htsum_ne : ∑' i, ∫⁻ z, ‖cellPot kerDisc ν R Λ i z * Laplacian.laplacian χ z‖ₑ ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hlint)
      rw [← ENNReal.ofReal_tsum_of_nonneg hw0 hws]
      exact ENNReal.ofReal_ne_top
    have hint_tsum := integral_tsum (fun i ↦ (hcellΔ i).1.aestronglyMeasurable) htsum_ne
    have hSΔ : ∀ z, multPot kerDisc ν R Λ z * Laplacian.laplacian χ z = ∑' i, cellPot kerDisc ν R Λ i z * Laplacian.laplacian χ z :=
      fun z ↦ by rw [multPot, tsum_mul_right]
    have hterm : ∀ i ∉ G, ∫ z, cellPot kerDisc ν R Λ i z * Laplacian.laplacian χ z = 0 := by
      intro i hi
      rw [(hcellΔ i).2]
      have h1 : ((Λ i).map χ).sum = 0 := Multiset.sum_eq_zero fun x hx ↦ by
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
        exact hχ0 w (hGΛ i hi w hw)
      have h2 : ∫ ζ in R i, χ ζ ∂ν = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun ζ hζ ↦ hχ0 ζ (hGR i hi ζ hζ)
      rw [h1, h2]; ring
    have hS_int : ∫ z, multPot kerDisc ν R Λ z * Laplacian.laplacian χ z =
        ∑ i ∈ G, 2 * Real.pi * (((Λ i).map χ).sum - ∫ ζ in R i, χ ζ ∂ν) := by
      simp_rw [hSΔ]
      rw [hint_tsum, tsum_eq_sum (s := G) fun i hi ↦ hterm i hi]
      exact Finset.sum_congr rfl fun i _ ↦ (hcellΔ i).2
    -- the weight part
    have hψint : Integrable fun z ↦ ψ z * Laplacian.laplacian χ z :=
      integrable_mul_laplacian hχ hc ((hw.weight.continuousOn.mono hs).integrableOn_compact hKc)
    have hψΔ : ∫ z, ψ z * Laplacian.laplacian χ z = 2 * Real.pi * ∫ ζ, χ ζ ∂ν := by
      rw [hw.weight.laplacian_eq χ hχ hc hs, hνdef, lapNorm, integral_smul_measure]
      rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
      field_simp
    have hSint : Integrable fun z ↦ multPot kerDisc ν R Λ z * Laplacian.laplacian χ z :=
      integrable_mul_laplacian hχ hc (hSK _ hs hKc)
    -- integral of `χ` against `ν` as a sum over the cells
    have hχν : ∫ ζ, χ ζ ∂ν = ∑ i ∈ G, ∫ ζ in R i, χ ζ ∂ν := by
      have hχint : Integrable χ ν := by
        obtain ⟨Dχ, hDχ⟩ := hχ.continuous.bounded_above_of_compact_support hc
        have hfinK : ν (tsupport χ) < ∞ := hν.finite _ hs hKc
        refine (IntegrableOn.of_bound hfinK hχ.continuous.aestronglyMeasurable.restrict Dχ
          (Eventually.of_forall fun z ↦ hDχ z)).integrable_of_forall_notMem_eq_zero
          fun z hz ↦ image_eq_zero_of_notMem_tsupport hz
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := 𝔻) fun z hz ↦
        image_eq_zero_of_notMem_tsupport fun h ↦ hz (hs h)]
      rw [← hC.iUnion_eq, integral_iUnion hC.measurableSet hC.pairwise_disjoint
        (by rw [hC.iUnion_eq]; exact hχint.integrableOn)]
      exact tsum_eq_sum fun i hi ↦
        setIntegral_eq_zero_of_forall_eq_zero fun ζ hζ ↦ hχ0 ζ (hGR i hi ζ hζ)
    have hfin : ∑ᶠ ζ, (nodeCount Λ ζ : ℝ) * χ ζ = ∑ i ∈ G, ((Λ i).map χ).sum :=
      finsum_nodeCount_mul fun i hi w hw ↦ hχ0 w (hGΛ i hi w hw)
    have hsplit : ∫ z, (ψ z + multPot kerDisc ν R Λ z) * Laplacian.laplacian χ z =
        (∫ z, ψ z * Laplacian.laplacian χ z) +
          ∫ z, multPot kerDisc ν R Λ z * Laplacian.laplacian χ z := by
      have h := integral_add hψint hSint
      refine Eq.trans ?_ h
      congr 1; ext z; ring
    rw [hsplit, hψΔ, hS_int, hχν, hfin, ← Finset.mul_sum, Finset.sum_sub_distrib]
    ring

end OC
