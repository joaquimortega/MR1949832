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
        2 * Real.pi * ∑ᶠ ζ, (nodeCount Λ ζ : ℝ) * χ ζ := sorry

end OC
