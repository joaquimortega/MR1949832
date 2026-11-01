import OrtegaCerdaMultipliers.Potential.Local
import OrtegaCerdaMultipliers.Doubling.Quant
import OrtegaCerdaMultipliers.Foundations.HyperbolicExtra

/-!
# M04 (Regularization) — Lemma 6: regularization of the weight

See `blueprint/M04_Regularization.md`.  Fully proved (modulo the upstream M01–M03 interfaces).

Lemma 6 in `ℂ` and `𝔻`, via the compactly supported local potentials of M02 §4 applied to
`σ = w·μ` with `w(ζ) = 1/(2μ(B(ζ,R)))`.  Reconciliation: `logSmall_plane`, `logSmall_disc` moved
to M03 (`Doubling/Export.lean`); M03's names are used for (A1)–(A4) (`doubling_upTo_*`,
`christ_lemma23_*`, `rpow_le_measure_*`, `measure_singleton_*`); the forms of Lemma 6 consumed by
M11/M12 are the corollaries `lemma6_disc_hypArea`, `lemma6_plane_volume`.

**Structure of the proofs.**
* `Reg.isSubharmonicWeight_regularized` (generic `Ω`): `ψ = φ + V` is a weight with Laplacian
  `μ.withDensity (1 - w) + volume.withDensity (smoothedDensity σ s)`, `σ = μ.withDensity w`.
* Disc: `Reg.lemma6_disc_core` chooses `ε, K, M, Cd'` from `(Cd, R, D₁, D₂, C_L)` before the
  weight, where `D₁, D₂, C_L` are the constants of `μ(D(x,R+r₁)) ≤ D₁ μ(D(x,r₁))`,
  `μ(D(x,2r₂)) ≤ D₂ μ(D(x,R))` and [Chr91, Lemma 2.3] at radius `r₂` (`r₁ = artanh(1/9)`,
  `r₂ = artanh(1/2)`).  These come from `measure_hypBall_le_rpow`, `christ_lemma23_disc`
  (`Reg.exists_disc_consts`, for `lemma6_disc`) or uniformly in the class from
  `measure_ball_le_rpow_quant` on `HDisc`, `christ_disc_quant` (`Reg.exists_disc_consts_quant`,
  for `lemma6_disc_quant`).
* Deviations from the doc: (i) `D₁`, `D₂` come from the power form `measure_*_le_rpow` (one
  application) instead of iterated doubling; (ii) the doubling of `volume.withDensity g` on
  hyperbolic discs is read off the sandwich `ε·hypArea ≤ g dm ≤ K·hypArea` and
  `hypArea (D(z,r)) = π sinh² r` (ratio `4 cosh² r ≤ 4 cosh²(1/2)`), not from (G1)–(G3);
  (iii) in `localPot_disc_le` the bound `s(ζ)/|z−ζ| ≤ 1/β(z,ζ)` uses `artanh t ≤ 2t` on
  `[0, 1/2]` instead of the monotonicity of `artanh t / t`; (iv) the mass radius of the
  regularized measure in `lemma6_disc_quant` is `5R` (`ofReal_lt_measure_hypBall`, `μ' ≥ μ/2`).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The weight `w(ζ) = 1/(2 μ(B(ζ,R)))` (plane). -/
def massWeight (μ : Measure ℂ) (R : ℝ) (ζ : ℂ) : ℝ≥0∞ := (2 * μ (ball ζ R))⁻¹
/-- The weight `w(ζ) = 1/(2 μ(D(ζ,R)))` (disc, hyperbolic balls). -/
def massWeightDisc (μ : Measure ℂ) (R : ℝ) (ζ : ℂ) : ℝ≥0∞ := (2 * μ (hypBall ζ R))⁻¹
/-- Smoothing radius in the disc: `s(ζ) = (1 − |ζ|²)/4`. -/
def discRadius (ζ : ℂ) : ℝ := (1 - ‖ζ‖ ^ 2) / 4

/-! ### Generic helpers (namespace `OC.Reg`) -/

namespace Reg

theorem measurable_hypDist : Measurable (fun p : ℂ × ℂ ↦ hypDist p.1 p.2) := by
  unfold hypDist pseudoHyp Real.artanh
  fun_prop

theorem measurableSet_hypBall (z : ℂ) (r : ℝ) : MeasurableSet (hypBall z r) :=
  (isOpen_hypBall z r).measurableSet

/-- A measure carried by `Ω`: almost every point lies in `Ω`. -/
theorem ae_mem_of_carried {Ω : Set ℂ} {μ : Measure ℂ} (h : μ Ωᶜ = 0) : ∀ᵐ ζ ∂μ, ζ ∈ Ω := by
  have := (measure_eq_zero_iff_ae_notMem).1 h
  filter_upwards [this] with ζ hζ
  simpa using hζ

/-- `μ.withDensity w ≤ μ` when `w ≤ 1` a.e. -/
theorem withDensity_le_self {μ : Measure ℂ} {w : ℂ → ℝ≥0∞} (hw1 : ∀ᵐ ζ ∂μ, w ζ ≤ 1) :
    μ.withDensity w ≤ μ := by
  calc μ.withDensity w ≤ μ.withDensity 1 := withDensity_mono hw1
    _ = μ := withDensity_one

/-- The split `μ = μ.withDensity w + μ.withDensity (1 - w)` when `w ≤ 1` a.e. -/
theorem withDensity_add_one_sub {μ : Measure ℂ} {w : ℂ → ℝ≥0∞} (hw : Measurable w)
    (hw1 : ∀ᵐ ζ ∂μ, w ζ ≤ 1) :
    μ.withDensity w + μ.withDensity (fun ζ ↦ 1 - w ζ) = μ := by
  rw [← withDensity_add_left hw]
  conv_rhs => rw [← withDensity_one (μ := μ)]
  apply withDensity_congr_ae
  filter_upwards [hw1] with ζ hζ
  simp [add_tsub_cancel_of_le hζ]

/-- `μ ≤ 2 • μ.withDensity (1 - w)` when `w ≤ 1/2` a.e. -/
theorem le_two_smul_withDensity_one_sub {μ : Measure ℂ} {w : ℂ → ℝ≥0∞} (hw : Measurable w)
    (hw2 : ∀ᵐ ζ ∂μ, w ζ ≤ 2⁻¹) : μ ≤ (2 : ℝ≥0∞) • μ.withDensity (fun ζ ↦ 1 - w ζ) := by
  rw [← withDensity_smul (2 : ℝ≥0∞)
    (show Measurable (fun ζ ↦ 1 - w ζ) from measurable_const.sub hw)]
  conv_lhs => rw [← withDensity_one (μ := μ)]
  apply withDensity_mono
  filter_upwards [hw2] with ζ hζ
  simp only [Pi.one_apply, Pi.smul_apply, smul_eq_mul]
  calc (1 : ℝ≥0∞) = 2 * 2⁻¹ := (ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top).symm
    _ = 2 * (1 - 2⁻¹) := by rw [ENNReal.one_sub_inv_two]
    _ ≤ 2 * (1 - w ζ) := by gcongr

/-- Upper bound for the weighted average of `f` (the averaged weight `(2 m)⁻¹`). -/
theorem setLIntegral_inv_two_mul_mul_le {μ : Measure ℂ} {B : Set ℂ} (hBm : MeasurableSet B)
    (hB : μ B ≠ ∞) {m f : ℂ → ℝ≥0∞} {D C : ℝ} (hD : 0 ≤ D)
    (h : ∀ ζ ∈ B, μ B ≤ ENNReal.ofReal D * m ζ)
    (hf : ∫⁻ ζ in B, f ζ ∂μ ≤ ENNReal.ofReal C * μ B) :
    ∫⁻ ζ in B, (2 * m ζ)⁻¹ * f ζ ∂μ ≤ ENNReal.ofReal (D * C / 2) := by
  by_cases h0 : μ B = 0
  · rw [Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]
    exact bot_le
  have hpt : ∀ ζ ∈ B, (2 * m ζ)⁻¹ ≤ ENNReal.ofReal D * (2 * μ B)⁻¹ := by
    intro ζ hζ
    have h2B : 2 * μ B ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hB
    have h2B0 : 2 * μ B ≠ 0 := mul_ne_zero two_ne_zero h0
    calc (2 * m ζ)⁻¹ ≤ (2 * μ B / ENNReal.ofReal D)⁻¹ := by
          apply ENNReal.inv_le_inv.2
          apply ENNReal.div_le_of_le_mul
          calc 2 * μ B ≤ 2 * (ENNReal.ofReal D * m ζ) := by gcongr; exact h ζ hζ
            _ = 2 * m ζ * ENNReal.ofReal D := by ring
      _ = ENNReal.ofReal D * (2 * μ B)⁻¹ := by
          rw [ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inr h2B0), div_eq_mul_inv]
  calc ∫⁻ ζ in B, (2 * m ζ)⁻¹ * f ζ ∂μ
      ≤ ∫⁻ ζ in B, ENNReal.ofReal D * (2 * μ B)⁻¹ * f ζ ∂μ :=
        setLIntegral_mono' hBm fun ζ hζ ↦ by gcongr; exact hpt ζ hζ
    _ = ENNReal.ofReal D * (2 * μ B)⁻¹ * ∫⁻ ζ in B, f ζ ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.inv_ne_top.2 (mul_ne_zero two_ne_zero h0)))]
    _ ≤ ENNReal.ofReal D * (2 * μ B)⁻¹ * (ENNReal.ofReal C * μ B) := by gcongr
    _ = ENNReal.ofReal D * ENNReal.ofReal C * 2⁻¹ * ((μ B)⁻¹ * μ B) := by
        rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
        ring
    _ = ENNReal.ofReal (D * C / 2) := by
        rw [ENNReal.inv_mul_cancel h0 hB, mul_one, ENNReal.ofReal_div_of_pos two_pos,
          ENNReal.ofReal_mul hD, ENNReal.ofReal_ofNat, div_eq_mul_inv]

/-- Upper bound for the mass of the weight `(2 m)⁻¹` on `B`. -/
theorem setLIntegral_inv_two_mul_le {μ : Measure ℂ} {B : Set ℂ} (hBm : MeasurableSet B)
    (hB : μ B ≠ ∞) {m : ℂ → ℝ≥0∞} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ ζ ∈ B, μ B ≤ ENNReal.ofReal D * m ζ) :
    ∫⁻ ζ in B, (2 * m ζ)⁻¹ ∂μ ≤ ENNReal.ofReal (D / 2) := by
  have := setLIntegral_inv_two_mul_mul_le hBm hB hD h (f := fun _ ↦ 1) (C := 1)
    (by simp)
  simpa using this

/-- Lower bound for the mass of the weight `(2 m)⁻¹` on `B`. -/
theorem le_setLIntegral_inv_two_mul {μ : Measure ℂ} {B : Set ℂ} (hBm : MeasurableSet B)
    (h0 : μ B ≠ 0) (hB : μ B ≠ ∞) {m : ℂ → ℝ≥0∞} {D : ℝ} (hD : 0 < D)
    (h : ∀ ζ ∈ B, m ζ ≤ ENNReal.ofReal D * μ B) :
    ENNReal.ofReal (1 / (2 * D)) ≤ ∫⁻ ζ in B, (2 * m ζ)⁻¹ ∂μ := by
  calc ENNReal.ofReal (1 / (2 * D)) = (2 * ENNReal.ofReal D * μ B)⁻¹ * μ B := by
        rw [ENNReal.mul_inv (Or.inr hB) (Or.inr h0), mul_assoc, ENNReal.inv_mul_cancel h0 hB,
          mul_one, one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_mul
          zero_le_two, ENNReal.ofReal_ofNat]
    _ = ∫⁻ ζ in B, (2 * ENNReal.ofReal D * μ B)⁻¹ ∂μ := (setLIntegral_const B _).symm
    _ ≤ ∫⁻ ζ in B, (2 * m ζ)⁻¹ ∂μ := by
        apply setLIntegral_mono' hBm
        intro ζ hζ
        apply ENNReal.inv_le_inv.2
        rw [mul_assoc]
        gcongr
        exact h ζ hζ

/-- Integrability of a continuous compactly supported function against a measure that is finite
on its support. -/
theorem integrable_of_tsupport {ν : Measure ℂ} {χ : ℂ → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (hν : ν (tsupport χ) < ∞) : Integrable χ ν := by
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hc
  have hon : IntegrableOn χ (tsupport χ) ν :=
    Measure.integrableOn_of_bounded hν.ne hχ.aestronglyMeasurable
      (ae_of_all _ fun x ↦ hC x)
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport χ)).1 hon

/-- Test functions: `Δχ` is continuous and supported in `tsupport χ` (copy of M07's
`laplacian_testFunction`, which this file does not import). -/
theorem laplacian_testFunction {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    Continuous (Laplacian.laplacian χ) ∧ tsupport (Laplacian.laplacian χ) ⊆ tsupport χ := by
  have hfun : Laplacian.laplacian χ =
      fun z ↦ iteratedFDeriv ℝ 2 χ z ![1, 1] + iteratedFDeriv ℝ 2 χ z ![I, I] :=
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane χ
  have hcont : Continuous (iteratedFDeriv ℝ 2 χ) :=
    hχ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact ((continuous_eval_const _).comp hcont).add ((continuous_eval_const _).comp hcont)
  · refine closure_minimal (fun z hz ↦ ?_) (isClosed_tsupport χ)
    apply tsupport_iteratedFDeriv_subset (𝕜 := ℝ) 2
    apply subset_tsupport
    intro h0
    apply hz
    rw [hfun]
    simp [h0]

/-- `a + b ≤ max A B * (x + y)` from `a ≤ A x`, `b ≤ B y`. -/
theorem add_le_max_mul {a b x y : ℝ≥0∞} {A B : ℝ≥0} (ha : a ≤ A * x) (hb : b ≤ B * y) :
    a + b ≤ ((max A B : ℝ≥0) : ℝ≥0∞) * (x + y) := by
  rw [mul_add]
  gcongr
  · exact ha.trans (by gcongr; exact le_max_left _ _)
  · exact hb.trans (by gcongr; exact le_max_right _ _)

/-! #### Disc geometry -/

/-- `r₁ = artanh (1/9)`, so `hypBall x r₁ = pB(x, 1/9)`. -/
def r₁ : ℝ := Real.artanh (1 / 9)
/-- `r₂ = artanh (1/2)`, so `hypBall x r₂ = pB(x, 1/2)`. -/
def r₂ : ℝ := Real.artanh (1 / 2)

theorem r₁_pos : 0 < r₁ := Real.artanh_pos ⟨by norm_num, by norm_num⟩
theorem r₂_pos : 0 < r₂ := Real.artanh_pos ⟨by norm_num, by norm_num⟩
theorem tanh_r₁ : Real.tanh r₁ = 1 / 9 := Real.tanh_artanh ⟨by norm_num, by norm_num⟩
theorem tanh_r₂ : Real.tanh r₂ = 1 / 2 := Real.tanh_artanh ⟨by norm_num, by norm_num⟩

/-- `artanh t ≤ 2 t` for `0 ≤ t ≤ 1/2`. -/
theorem artanh_le_two_mul {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : Real.artanh t ≤ 2 * t := by
  rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩]
  have hpos : 0 < (1 + t) / (1 - t) := div_pos (by linarith) (by linarith)
  have h := Real.log_le_sub_one_of_pos hpos
  have e : (1 + t) / (1 - t) - 1 = 2 * t / (1 - t) := by
    rw [div_sub_one (by linarith)]
    congr 1
    ring
  have h2 : 2 * t / (1 - t) ≤ 4 * t := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem r₂_le_one : r₂ ≤ 1 := by
  have := artanh_le_two_mul (t := 1 / 2) (by norm_num) le_rfl
  unfold r₂
  linarith

theorem mem_hypBall_iff_pseudoHyp {x ζ : ℂ} (hx : x ∈ 𝔻) {r : ℝ} :
    ζ ∈ hypBall x r ↔ ζ ∈ 𝔻 ∧ pseudoHyp x ζ < Real.tanh r := by
  rw [hypBall_eq_pseudoBall hx]
  rfl

theorem discRadius_pos {ζ : ℂ} (hζ : ζ ∈ 𝔻) : 0 < discRadius ζ := by
  have := one_sub_normSq_pos hζ
  unfold discRadius
  linarith

/-- (D1) `ball ζ (s ζ) ⊆ 𝔻`. -/
theorem ball_discRadius_subset {ζ : ℂ} (hζ : ζ ∈ 𝔻) : ball ζ (discRadius ζ) ⊆ 𝔻 := by
  intro x hx
  have h := ball_subset_pseudoBall hζ (s := 1 / 2) (by norm_num) (by norm_num)
  refine (h ?_).1
  rw [mem_ball] at hx ⊢
  unfold discRadius at hx
  linarith

/-- (D3) If `|x − ζ| < s(ζ)` then `ζ ∈ D(x, r₂)` and `1 − |ζ|² ≥ (1 − |x|²)/3`. -/
theorem near_of_lt_discRadius {x ζ : ℂ} (hx : x ∈ 𝔻) (hζ : ζ ∈ 𝔻)
    (h : ‖x - ζ‖ < discRadius ζ) :
    ζ ∈ hypBall x r₂ ∧ (1 - ‖x‖ ^ 2) / 3 ≤ 1 - ‖ζ‖ ^ 2 := by
  have hb : x ∈ ball ζ (1 / 2 * (1 - ‖ζ‖ ^ 2) / 2) := by
    rw [mem_ball, dist_eq_norm]
    unfold discRadius at h
    linarith
  have hρ' := (ball_subset_pseudoBall hζ (s := 1 / 2) (by norm_num) (by norm_num) hb).2
  have hρ : pseudoHyp x ζ < 1 / 2 := by rw [pseudoHyp_comm]; exact hρ'
  refine ⟨(mem_hypBall_iff_pseudoHyp hx).2 ⟨hζ, by rw [tanh_r₂]; exact hρ⟩, ?_⟩
  have := (one_sub_normSq_comparable hx hζ (s := 1 / 2) (by norm_num) hρ).1
  norm_num at this
  linarith

/-- (D4) If `ζ ∈ D(x, r₁)` then `|x − ζ| < s(ζ)/2` and `1 − |ζ|² ≤ (5/4)(1 − |x|²)`. -/
theorem close_of_mem_hypBall_r₁ {x ζ : ℂ} (hx : x ∈ 𝔻) (hζ : ζ ∈ hypBall x r₁) :
    ‖x - ζ‖ < discRadius ζ / 2 ∧ 1 - ‖ζ‖ ^ 2 ≤ 5 / 4 * (1 - ‖x‖ ^ 2) := by
  obtain ⟨hζ𝔻, hρ⟩ := (mem_hypBall_iff_pseudoHyp hx).1 hζ
  rw [tanh_r₁] at hρ
  have hρ' : pseudoHyp ζ x < 1 / 9 := by rw [pseudoHyp_comm]; exact hρ
  have hb := pseudoBall_subset_ball hζ𝔻 (s := 1 / 9) (by norm_num) (by norm_num) ⟨hx, hρ'⟩
  rw [mem_ball, dist_eq_norm] at hb
  refine ⟨?_, ?_⟩
  · have e : 1 / 9 * (1 - ‖ζ‖ ^ 2) / (1 - 1 / 9) = discRadius ζ / 2 := by
      unfold discRadius
      ring
    linarith
  · have := (one_sub_normSq_comparable hx hζ𝔻 (s := 1 / 9) (by norm_num) hρ).2
    norm_num at this
    linarith

/-- The logarithm in the local potential, bounded by the hyperbolic one. -/
theorem log_discRadius_sq_le {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ hypBall z r₂) :
    Real.log (discRadius ζ ^ 2 / ‖z - ζ‖ ^ 2) ≤
      2 * Real.log (r₂ / hypDist z ζ) + 2 * Real.log (1 / r₂) := by
  have hlog1 : 0 ≤ Real.log (1 / r₂) :=
    Real.log_nonneg (by rw [le_div_iff₀ r₂_pos]; linarith [r₂_le_one])
  obtain ⟨hζ𝔻, hρ⟩ := (mem_hypBall_iff_pseudoHyp hz).1 hζ
  rw [tanh_r₂] at hρ
  by_cases hzζ : z = ζ
  · subst hzζ
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      div_zero, Real.log_zero, hypDist_self]
    linarith
  have hd : 0 < ‖z - ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 hzζ)
  have hD := norm_one_sub_conj_mul_pos hz hζ𝔻
  have hρdef : pseudoHyp z ζ * ‖1 - conj z * ζ‖ = ‖z - ζ‖ := by
    unfold pseudoHyp
    exact div_mul_cancel₀ _ hD.ne'
  have hρ0 : 0 < pseudoHyp z ζ := div_pos hd hD
  have hβ : hypDist z ζ ≤ 2 * pseudoHyp z ζ := artanh_le_two_mul hρ0.le hρ.le
  have hβpos : 0 < hypDist z ζ := Real.artanh_pos ⟨hρ0, by linarith⟩
  have hz1 := norm_lt_one_of_mem_disc hz
  have hζ1 := norm_lt_one_of_mem_disc hζ𝔻
  have hs : discRadius ζ ≤ ‖1 - conj z * ζ‖ / 2 := by
    have h1 := one_sub_mul_le_norm_one_sub_conj_mul z ζ
    have h2 : ‖z‖ * ‖ζ‖ ≤ ‖ζ‖ := mul_le_of_le_one_left (norm_nonneg ζ) hz1.le
    unfold discRadius
    nlinarith [norm_nonneg ζ]
  have hspos := discRadius_pos hζ𝔻
  have key : discRadius ζ / ‖z - ζ‖ ≤ 1 / hypDist z ζ := by
    rw [div_le_div_iff₀ hd hβpos, one_mul]
    calc discRadius ζ * hypDist z ζ ≤ ‖1 - conj z * ζ‖ / 2 * (2 * pseudoHyp z ζ) := by
          gcongr
      _ = ‖z - ζ‖ := by rw [← hρdef]; ring
  have e1 : Real.log (discRadius ζ ^ 2 / ‖z - ζ‖ ^ 2) = 2 * Real.log (discRadius ζ / ‖z - ζ‖) := by
    rw [← div_pow, Real.log_pow]
    norm_num
  have e2 : Real.log (1 / hypDist z ζ) = Real.log (r₂ / hypDist z ζ) + Real.log (1 / r₂) := by
    rw [← Real.log_mul (div_pos r₂_pos hβpos).ne' (div_pos one_pos r₂_pos).ne']
    congr 1
    field_simp
    exact (div_self r₂_pos.ne').symm
  have h3 := Real.log_le_log (div_pos hspos hd) key
  linarith

theorem hypBall_subset_hypBall_add {x ζ : ℂ} (hx : x ∈ 𝔻) {a b : ℝ} (hζ : ζ ∈ hypBall x a) :
    hypBall ζ b ⊆ hypBall x (a + b) := by
  intro w hw
  refine ⟨hw.1, ?_⟩
  have := hypDist_triangle hx hζ.1 hw.1
  linarith [hζ.2, hw.2]

theorem hypBall_subset_hypBall_two_mul {x ζ : ℂ} (hx : x ∈ 𝔻) {a : ℝ} (hζ : ζ ∈ hypBall x a) :
    hypBall x a ⊆ hypBall ζ (2 * a) := by
  intro w hw
  refine ⟨hw.1, ?_⟩
  have := hypDist_triangle hζ.1 hx hw.1
  rw [hypDist_comm ζ x] at this
  linarith [hζ.2, hw.2]

theorem hypBall_mono {z : ℂ} {r r' : ℝ} (h : r ≤ r') : hypBall z r ⊆ hypBall z r' :=
  fun _ hw ↦ ⟨hw.1, hw.2.trans_le h⟩

/-! #### The weight -/

theorem massWeightDisc_le {μ : Measure ℂ} {R : ℝ} (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {ζ : ℂ}
    (hζ : ζ ∈ 𝔻) : massWeightDisc μ R ζ ≤ 2⁻¹ := by
  unfold massWeightDisc
  apply ENNReal.inv_le_inv.2
  calc (2 : ℝ≥0∞) = 2 * 1 := (mul_one 2).symm
    _ ≤ 2 * μ (hypBall ζ R) := by gcongr; exact hm ζ hζ

theorem ae_massWeightDisc_le {μ : Measure ℂ} (hc : μ 𝔻ᶜ = 0) {R : ℝ}
    (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) : ∀ᵐ ζ ∂μ, massWeightDisc μ R ζ ≤ 2⁻¹ := by
  filter_upwards [ae_mem_of_carried hc] with ζ hζ
  exact massWeightDisc_le hm hζ

theorem ae_massWeightDisc_le_one {μ : Measure ℂ} (hc : μ 𝔻ᶜ = 0) {R : ℝ}
    (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) : ∀ᵐ ζ ∂μ, massWeightDisc μ R ζ ≤ 1 := by
  filter_upwards [ae_massWeightDisc_le hc hm] with ζ hζ
  exact hζ.trans (ENNReal.inv_le_one.2 one_le_two)

theorem massWeight_le {μ : Measure ℂ} {R : ℝ} (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) (ζ : ℂ) :
    massWeight μ R ζ ≤ 2⁻¹ := by
  unfold massWeight
  apply ENNReal.inv_le_inv.2
  calc (2 : ℝ≥0∞) = 2 * 1 := (mul_one 2).symm
    _ ≤ 2 * μ (ball ζ R) := by gcongr; exact hm ζ

end Reg

theorem measurable_massWeight {μ : Measure ℂ} [SFinite μ] (R : ℝ) :
    Measurable (massWeight μ R) := by
  have hs : MeasurableSet {p : ℂ × ℂ | dist p.2 p.1 < R} :=
    measurableSet_lt (by fun_prop) measurable_const
  have h := measurable_measure_prodMk_left (ν := μ) hs
  have e : (fun ζ ↦ μ (Prod.mk ζ ⁻¹' {p : ℂ × ℂ | dist p.2 p.1 < R})) =
      fun ζ ↦ μ (ball ζ R) := rfl
  rw [e] at h
  exact (measurable_const.mul h).inv

theorem measurable_massWeightDisc {μ : Measure ℂ} [SFinite μ] (R : ℝ) :
    Measurable (massWeightDisc μ R) := by
  have hs : MeasurableSet {p : ℂ × ℂ | p.2 ∈ 𝔻 ∧ hypDist p.1 p.2 < R} :=
    (measurableSet_ball.preimage measurable_snd).inter
      (measurableSet_lt Reg.measurable_hypDist measurable_const)
  have h := measurable_measure_prodMk_left (ν := μ) hs
  have e : (fun ζ ↦ μ (Prod.mk ζ ⁻¹' {p : ℂ × ℂ | p.2 ∈ 𝔻 ∧ hypDist p.1 p.2 < R})) =
      fun ζ ↦ μ (hypBall ζ R) := rfl
  rw [e] at h
  exact (measurable_const.mul h).inv

theorem isLocalPotData_plane {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    IsLocalPotData univ (μ.withDensity (massWeight μ R)) (fun _ ↦ R) := by
  have : SigmaFinite μ := hφ.sigmaFinite isOpen_univ
  have hle : μ.withDensity (massWeight μ R) ≤ μ :=
    Reg.withDensity_le_self (ae_of_all _ fun ζ ↦ (Reg.massWeight_le hm ζ).trans
      (ENNReal.inv_le_one.2 one_le_two))
  have hfin : ∀ z r, μ (ball z r) < ∞ := fun z r ↦ hφ.measure_ball_lt_top z r
  refine ⟨isOpen_univ, measurable_const, fun _ _ ↦ hR, ⟨R, fun _ ↦ le_rfl⟩,
    fun _ _ ↦ subset_univ _, by simp, inferInstance, ?_, ?_, ?_⟩
  · intro z
    refine le_antisymm ((Measure.le_iff'.1 hle {z}).trans ?_) bot_le
    rw [measure_singleton_plane hd hfin z]
  · intro K _ hKc
    obtain ⟨ρ, hKρ⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hKc.isBounded
    have hsub : {ζ | ∃ z ∈ K, dist z ζ < R} ⊆ closedBall 0 (ρ + R) := by
      rintro ζ ⟨z, hzK, hzζ⟩
      have hz := hKρ hzK
      rw [mem_closedBall] at hz ⊢
      linarith [dist_triangle ζ z 0, dist_comm z ζ]
    calc _ ≤ μ {ζ | ∃ z ∈ K, dist z ζ < R} := Measure.le_iff'.1 hle _
      _ ≤ μ (closedBall 0 (ρ + R)) := measure_mono hsub
      _ < ∞ := hφ.finite_of_compact _ (subset_univ _) (isCompact_closedBall _ _)
  · intro K _ hKc η hη
    obtain ⟨δ, hδ, hδ1, hδK⟩ :=
      logSmall_plane hd (fun K hK ↦ hφ.finite_of_compact K (subset_univ K) hK) hKc hη
    exact ⟨δ, hδ, hδ1, fun z hz ↦
      (lintegral_mono' (Measure.restrict_mono subset_rfl hle) le_rfl).trans (hδK z hz)⟩

theorem isLocalPotData_disc {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    IsLocalPotData 𝔻 (μ.withDensity (massWeightDisc μ R)) discRadius := by
  have : SigmaFinite μ := hφ.sigmaFinite isOpen_ball
  have hle : μ.withDensity (massWeightDisc μ R) ≤ μ :=
    Reg.withDensity_le_self (Reg.ae_massWeightDisc_le_one hφ.carried hm)
  have hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞ := fun z hz r ↦ hφ.measure_hypBall_lt_top hz r
  refine ⟨isOpen_ball, ?_, fun ζ hζ ↦ Reg.discRadius_pos hζ, ⟨1 / 4, ?_⟩,
    fun ζ hζ ↦ Reg.ball_discRadius_subset hζ, withDensity_absolutelyContinuous μ _ hφ.carried,
    inferInstance, ?_, ?_, ?_⟩
  · unfold discRadius
    fun_prop
  · intro ζ
    unfold discRadius
    nlinarith [norm_nonneg ζ]
  · intro z
    refine le_antisymm ((Measure.le_iff'.1 hle {z}).trans ?_) bot_le
    by_cases hz : z ∈ 𝔻
    · rw [measure_singleton_disc hd hfin hz]
    · exact (measure_mono (by simpa using hz : ({z} : Set ℂ) ⊆ 𝔻ᶜ)).trans hφ.carried.le
  · intro K hK hKc
    obtain ⟨ρ, hρ1, hKρ⟩ := exists_lt_subset_ball hKc.isClosed hK
    have hsub : {ζ | ∃ z ∈ K, dist z ζ < discRadius ζ} ⊆ closedBall 0 ((1 + 2 * ρ) / 3) := by
      rintro ζ ⟨z, hzK, hzζ⟩
      have hzρ : ‖z‖ < ρ := by simpa using hKρ hzK
      rw [mem_closedBall, dist_zero_right]
      rw [dist_eq_norm] at hzζ
      unfold discRadius at hzζ
      have h1 : ‖ζ‖ ≤ ‖z‖ + ‖z - ζ‖ := by
        calc ‖ζ‖ = ‖z - (z - ζ)‖ := by ring_nf
          _ ≤ ‖z‖ + ‖z - ζ‖ := norm_sub_le _ _
      nlinarith [norm_nonneg ζ, norm_nonneg (z - ζ)]
    have hcl : closedBall (0 : ℂ) ((1 + 2 * ρ) / 3) ⊆ 𝔻 := closedBall_subset_ball (by linarith)
    calc _ ≤ μ {ζ | ∃ z ∈ K, dist z ζ < discRadius ζ} := Measure.le_iff'.1 hle _
      _ ≤ μ (closedBall 0 ((1 + 2 * ρ) / 3)) := measure_mono hsub
      _ < ∞ := hφ.finite_of_compact _ hcl (isCompact_closedBall _ _)
  · intro K hK hKc η hη
    obtain ⟨δ, hδ, hδ1, hδK⟩ := logSmall_disc hd hφ.finite_of_compact hK hKc hη
    exact ⟨δ, hδ, hδ1, fun z hz ↦
      (lintegral_mono' (Measure.restrict_mono subset_rfl hle) le_rfl).trans (hδK z hz)⟩

/-! ### Explicit bounds and the assembly (namespace `OC.Reg`) -/

namespace Reg

theorem measurable_bump_comp {s : ℂ → ℝ} (hs : Measurable s) (x : ℂ) :
    Measurable (fun ζ ↦ ENNReal.ofReal (bumpKernel (s ζ) (x - ζ))) :=
  (measurable_bumpKernel.comp (hs.prodMk (measurable_const.sub measurable_id))).ennreal_ofReal

/-- **The assembly** (doc §4.4, generic `Ω`): `ψ = φ + V` is a weight with Laplacian
`ν₀ + σ̃`, where `σ = μ.withDensity w`, `ν₀ = μ.withDensity (1 - w)`, `σ̃ = smoothedDensity σ s`. -/
theorem isSubharmonicWeight_regularized {Ω : Set ℂ} {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight Ω φ μ) {w : ℂ → ℝ≥0∞} (hw : Measurable w)
    (hw1 : ∀ᵐ ζ ∂μ, w ζ ≤ 1) {s : ℂ → ℝ} (h : IsLocalPotData Ω (μ.withDensity w) s) :
    IsSubharmonicWeight Ω (fun z ↦ φ z + localPot (μ.withDensity w) s z)
      (μ.withDensity (fun ζ ↦ 1 - w ζ) +
        volume.withDensity (smoothedDensity (μ.withDensity w) s)) := by
  set μ₁ := μ.withDensity w with hμ₁def
  set ν₀ := μ.withDensity (fun ζ ↦ 1 - w ζ) with hν₀def
  set g := smoothedDensity μ₁ s with hgdef
  have hΩ := h.isOpen
  have hsplit : μ₁ + ν₀ = μ := withDensity_add_one_sub hw hw1
  have hν₀ : ν₀ ≤ μ := withDensity_le_self (ae_of_all _ fun _ ↦ tsub_le_self)
  have hμ₁ : μ₁ ≤ μ := withDensity_le_self hw1
  have hgK : ∀ K ⊆ Ω, IsCompact K → volume.withDensity g K < ∞ := fun K hK hKc ↦ by
    rw [withDensity_apply _ hKc.isClosed.measurableSet]
    exact h.lintegral_smoothedDensity_lt_top hK hKc
  refine ⟨hφ.continuousOn.add h.continuousOn_localPot, ?_, ?_, ?_⟩
  · intro K hK hKc
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2 ⟨(Measure.le_iff'.1 hν₀ K).trans_lt
      (hφ.finite_of_compact K hK hKc), hgK K hK hKc⟩
  · have h1 : ν₀ Ωᶜ = 0 := withDensity_absolutelyContinuous μ _ hφ.carried
    have h2 : volume.withDensity g Ωᶜ = 0 := by
      rw [withDensity_apply _ hΩ.isClosed_compl.measurableSet,
        setLIntegral_congr_fun hΩ.isClosed_compl.measurableSet
          (fun x hx ↦ h.smoothedDensity_eq_zero hx), lintegral_zero]
    rw [Measure.add_apply, h1, h2, add_zero]
  · intro χ hχ hc hs
    obtain ⟨hΔc, hΔs⟩ := laplacian_testFunction hχ
    have hΔcs : HasCompactSupport (Laplacian.laplacian χ) :=
      IsCompact.of_isClosed_subset hc (isClosed_tsupport _) hΔs
    have I1 := hφ.integrable_mul hΩ hΔc hΔcs (hΔs.trans hs)
    have I2 : Integrable (fun z ↦ localPot μ₁ s z * Laplacian.laplacian χ z) := by
      have hK : IsCompact (tsupport (Laplacian.laplacian χ)) := hΔcs
      have h1 : IntegrableOn (localPot μ₁ s) (tsupport (Laplacian.laplacian χ)) :=
        (h.continuousOn_localPot.mono (hΔs.trans hs)).integrableOn_compact hK
      exact (h1.mul_continuousOn hΔc.continuousOn hK).integrable_of_forall_notMem_eq_zero
        (fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz])
    have hμK : μ (tsupport χ) < ∞ := hφ.finite_of_compact _ hs hc
    have i₁ : Integrable χ μ₁ :=
      integrable_of_tsupport hχ.continuous hc ((Measure.le_iff'.1 hμ₁ _).trans_lt hμK)
    have i₀ : Integrable χ ν₀ :=
      integrable_of_tsupport hχ.continuous hc ((Measure.le_iff'.1 hν₀ _).trans_lt hμK)
    have ig : Integrable χ (volume.withDensity g) :=
      integrable_of_tsupport hχ.continuous hc (hgK _ hs hc)
    have e1 : ∫ z, (φ z + localPot μ₁ s z) * Laplacian.laplacian χ z =
        (∫ z, φ z * Laplacian.laplacian χ z) +
          ∫ z, localPot μ₁ s z * Laplacian.laplacian χ z := by
      calc ∫ z, (φ z + localPot μ₁ s z) * Laplacian.laplacian χ z
          = ∫ z, (φ z * Laplacian.laplacian χ z +
              localPot μ₁ s z * Laplacian.laplacian χ z) := by
            congr 1
            ext z
            ring
        _ = _ := integral_add I1 I2
    have e2 : ∫ z, χ z ∂μ = (∫ z, χ z ∂μ₁) + ∫ z, χ z ∂ν₀ := by
      rw [← integral_add_measure i₁ i₀, hsplit]
    rw [e1, hφ.laplacian_eq χ hχ hc hs,
      h.integral_localPot_mul_laplacian (hχ.of_le (WithTop.coe_le_coe.2 le_top)) hc hs,
      integral_add_measure i₀ ig, e2]
    ring

/-- The doubling of `ν₀ + μ̃` from that of `μ` (with `ν₀ ≤ μ ≤ 2ν₀`) and that of `μ̃`. -/
theorem doubling_disc_add {μ ν₀ μ' : Measure ℂ} {Cd A : ℝ≥0}
    (hdC : IsLocallyDoublingDiscWith μ Cd) (hν₀ : ν₀ ≤ μ) (h2 : μ ≤ (2 : ℝ≥0∞) • ν₀)
    (hμ' : ∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → 2 * r < 1 →
      μ' (hypBall z (2 * r)) ≤ A * μ' (hypBall z r)) :
    IsLocallyDoublingDiscWith (ν₀ + μ') (max (2 * Cd) A) := by
  intro z hz r hr h2r
  rw [Measure.add_apply, Measure.add_apply]
  refine add_le_max_mul ?_ (hμ' z hz r hr h2r)
  calc ν₀ (hypBall z (2 * r)) ≤ μ (hypBall z (2 * r)) := Measure.le_iff'.1 hν₀ _
    _ ≤ Cd * μ (hypBall z r) := hdC z hz r hr h2r
    _ ≤ Cd * (2 * ν₀ (hypBall z r)) := by
        gcongr
        exact Measure.le_iff'.1 h2 _
    _ = ((2 * Cd : ℝ≥0) : ℝ≥0∞) * ν₀ (hypBall z r) := by push_cast; ring

/-- `ε · hypArea ≤ volume.withDensity g` from the pointwise lower bound. -/
theorem smul_hypArea_le_withDensity {g : ℂ → ℝ≥0∞} {ε : ℝ} (hε : 0 ≤ ε)
    (hg : ∀ z ∈ 𝔻, ENNReal.ofReal (ε / (1 - ‖z‖ ^ 2) ^ 2) ≤ g z) :
    ENNReal.ofReal ε • hypArea ≤ volume.withDensity g := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, hypArea, withDensity_apply _ hs,
    Measure.restrict_restrict hs, withDensity_apply _ hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ z in s ∩ 𝔻, ENNReal.ofReal ε * ENNReal.ofReal ((1 - ‖z‖ ^ 2)⁻¹ ^ 2)
      ≤ ∫⁻ z in s ∩ 𝔻, g z := by
        refine setLIntegral_mono' (hs.inter measurableSet_ball) fun z hz ↦ ?_
        rw [← ENNReal.ofReal_mul hε, inv_pow, ← div_eq_mul_inv]
        exact hg z hz.2
    _ ≤ ∫⁻ z in s, g z := lintegral_mono_set inter_subset_left

/-- `volume.withDensity g ≤ K · hypArea` from the pointwise upper bound and `g = 0` off `𝔻`. -/
theorem withDensity_le_smul_hypArea {g : ℂ → ℝ≥0∞} {K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ z ∈ 𝔻, g z ≤ ENNReal.ofReal (K / (1 - ‖z‖ ^ 2) ^ 2)) (hg0 : ∀ z ∉ 𝔻, g z = 0) :
    volume.withDensity g ≤ ENNReal.ofReal K • hypArea := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, hypArea, withDensity_apply _ hs, withDensity_apply _ hs,
    Measure.restrict_restrict hs, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ z in s, g z
      ≤ ∫⁻ z in s, 𝔻.indicator
          (fun z ↦ ENNReal.ofReal K * ENNReal.ofReal ((1 - ‖z‖ ^ 2)⁻¹ ^ 2)) z := by
        refine setLIntegral_mono' hs fun z _ ↦ ?_
        by_cases hz : z ∈ 𝔻
        · rw [indicator_of_mem hz, ← ENNReal.ofReal_mul hK, inv_pow, ← div_eq_mul_inv]
          exact hg z hz
        · rw [hg0 z hz]
          exact bot_le
    _ = ∫⁻ z in s ∩ 𝔻, ENNReal.ofReal K * ENNReal.ofReal ((1 - ‖z‖ ^ 2)⁻¹ ^ 2) := by
        rw [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
          inter_comm]

/-- Doubling of an absolutely continuous measure squeezed between multiples of `hypArea`. -/
theorem doubling_of_hypArea_sandwich {μ' : Measure ℂ} {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hlo : ENNReal.ofReal ε • hypArea ≤ μ') (hup : μ' ≤ ENNReal.ofReal K • hypArea) {z : ℂ}
    (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 < r) (h2r : 2 * r < 1) :
    μ' (hypBall z (2 * r)) ≤
      ENNReal.ofReal (4 * Real.cosh (1 / 2) ^ 2 * K / ε) * μ' (hypBall z r) := by
  have hc : Real.cosh r ≤ Real.cosh (1 / 2) :=
    Real.cosh_le_cosh.2 (by rw [abs_of_pos hr, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith)
  have hc2 : Real.cosh r ^ 2 ≤ Real.cosh (1 / 2) ^ 2 :=
    pow_le_pow_left₀ (Real.cosh_pos r).le hc 2
  have hsq : Real.sinh (2 * r) ^ 2 = 4 * Real.sinh r ^ 2 * Real.cosh r ^ 2 := by
    rw [Real.sinh_two_mul]
    ring
  have hsr : 0 ≤ Real.sinh r ^ 2 := sq_nonneg _
  calc μ' (hypBall z (2 * r)) ≤ (ENNReal.ofReal K • hypArea) (hypBall z (2 * r)) :=
        Measure.le_iff'.1 hup _
    _ = ENNReal.ofReal (K * (Real.pi * Real.sinh (2 * r) ^ 2)) := by
        rw [Measure.smul_apply, smul_eq_mul, hypArea_hypBall hz (by linarith),
          ENNReal.ofReal_mul hK]
    _ ≤ ENNReal.ofReal (4 * Real.cosh (1 / 2) ^ 2 * K / ε * (ε * (Real.pi * Real.sinh r ^ 2))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hsq]
        have e : 4 * Real.cosh (1 / 2) ^ 2 * K / ε * (ε * (Real.pi * Real.sinh r ^ 2)) =
            K * (Real.pi * (4 * Real.sinh r ^ 2 * Real.cosh (1 / 2) ^ 2)) := by
          field_simp
        rw [e]
        gcongr
    _ = ENNReal.ofReal (4 * Real.cosh (1 / 2) ^ 2 * K / ε) *
          (ENNReal.ofReal ε • hypArea) (hypBall z r) := by
        rw [Measure.smul_apply, smul_eq_mul, hypArea_hypBall hz hr.le,
          ← ENNReal.ofReal_mul hε.le, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by gcongr

/-! #### Explicit bounds in the disc -/

section DiscBounds

variable {φ : ℂ → ℝ} {μ : Measure ℂ} {R : ℝ}

/-- Lower bound for `g` (doc §5.2), with the constant `D₁` of
`μ(D(x, R + r₁)) ≤ D₁ μ(D(x, r₁))`. -/
theorem smoothedDensity_disc_ge (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {D₁ : ℝ} (hD₁ : 0 < D₁)
    (h₁ : ∀ x ∈ 𝔻, μ (hypBall x (R + r₁)) ≤ ENNReal.ofReal D₁ * μ (hypBall x r₁))
    {x : ℂ} (hx : x ∈ 𝔻) :
    ENNReal.ofReal (128 / (25 * Real.pi * D₁) / (1 - ‖x‖ ^ 2) ^ 2) ≤
      smoothedDensity (μ.withDensity (massWeightDisc μ R)) discRadius x := by
  set w := massWeightDisc μ R with hwdef
  set B := hypBall x r₁ with hBdef
  have hBm : MeasurableSet B := measurableSet_hypBall x r₁
  have hA := one_sub_normSq_pos hx
  set c : ℝ := 256 / (25 * Real.pi) / (1 - ‖x‖ ^ 2) ^ 2 with hc
  have hk : ∀ ζ ∈ B, ENNReal.ofReal c ≤ ENNReal.ofReal (bumpKernel (discRadius ζ) (x - ζ)) := by
    intro ζ hζ
    obtain ⟨h1, h2⟩ := close_of_mem_hypBall_r₁ hx hζ
    have hs := discRadius_pos hζ.1
    apply ENNReal.ofReal_le_ofReal
    have hk0 := le_bumpKernel hs (x - ζ)
    rw [indicator_of_mem (by simpa using h1 : x - ζ ∈ ball (0 : ℂ) (discRadius ζ / 2)),
      Pi.one_apply, mul_one] at hk0
    refine le_trans ?_ hk0
    have hs' : discRadius ζ ≤ 5 / 16 * (1 - ‖x‖ ^ 2) := by
      unfold discRadius
      linarith
    have e : c = 1 / (Real.pi * (5 / 16 * (1 - ‖x‖ ^ 2)) ^ 2) := by
      rw [hc]
      field_simp
      ring
    rw [e]
    exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hμB : μ B ≠ ∞ := (hφ.measure_hypBall_lt_top hx r₁).ne
  have hRB : ∀ ζ ∈ B, μ (hypBall ζ R) ≤ ENNReal.ofReal D₁ * μ B := fun ζ hζ ↦
    (measure_mono (by simpa [add_comm] using hypBall_subset_hypBall_add hx hζ)).trans (h₁ x hx)
  have hμB0 : μ B ≠ 0 := by
    intro h0
    have h1 : (1 : ℝ≥0∞) ≤ 0 := by
      calc (1 : ℝ≥0∞) ≤ μ (hypBall x R) := hm x hx
        _ ≤ μ (hypBall x (R + r₁)) := measure_mono (hypBall_mono (by linarith [r₁_pos]))
        _ ≤ ENNReal.ofReal D₁ * μ B := h₁ x hx
        _ = 0 := by rw [h0, mul_zero]
    exact absurd h1 (by norm_num)
  have hw : ENNReal.ofReal (1 / (2 * D₁)) ≤ ∫⁻ ζ in B, w ζ ∂μ :=
    le_setLIntegral_inv_two_mul (m := fun ζ ↦ μ (hypBall ζ R)) hBm hμB0 hμB hD₁ hRB
  calc ENNReal.ofReal (128 / (25 * Real.pi * D₁) / (1 - ‖x‖ ^ 2) ^ 2)
      = ENNReal.ofReal c * ENNReal.ofReal (1 / (2 * D₁)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hc]
        field_simp
        ring
    _ ≤ ENNReal.ofReal c * ∫⁻ ζ in B, w ζ ∂μ := by gcongr
    _ = ENNReal.ofReal c * (μ.withDensity w) B := by rw [withDensity_apply _ hBm]
    _ = ∫⁻ ζ in B, ENNReal.ofReal c ∂(μ.withDensity w) := (setLIntegral_const B _).symm
    _ ≤ ∫⁻ ζ in B, ENNReal.ofReal (bumpKernel (discRadius ζ) (x - ζ)) ∂(μ.withDensity w) :=
        setLIntegral_mono' hBm hk
    _ ≤ smoothedDensity (μ.withDensity w) discRadius x := setLIntegral_le_lintegral _ _

/-- Upper bound for `g` (doc §5.2), with the constant `D₂` of
`μ(D(ζ, 2r₂)) ≤ D₂ μ(D(ζ, R))`. -/
theorem smoothedDensity_disc_le (hφ : IsSubharmonicWeight 𝔻 φ μ) {D₂ : ℝ} (hD₂ : 0 < D₂)
    (h₂ : ∀ x ∈ 𝔻, μ (hypBall x (2 * r₂)) ≤ ENNReal.ofReal D₂ * μ (hypBall x R))
    {x : ℂ} (hx : x ∈ 𝔻) :
    smoothedDensity (μ.withDensity (massWeightDisc μ R)) discRadius x ≤
      ENNReal.ofReal (288 * D₂ / Real.pi / (1 - ‖x‖ ^ 2) ^ 2) := by
  set w := massWeightDisc μ R with hwdef
  set B := hypBall x r₂ with hBdef
  have hBm : MeasurableSet B := measurableSet_hypBall x r₂
  have hA := one_sub_normSq_pos hx
  set c : ℝ := 576 / Real.pi / (1 - ‖x‖ ^ 2) ^ 2 with hc
  have hk : ∀ᵐ ζ ∂(μ.withDensity w),
      ENNReal.ofReal (bumpKernel (discRadius ζ) (x - ζ)) ≤
        B.indicator (fun _ ↦ ENNReal.ofReal c) ζ := by
    filter_upwards [ae_mem_of_carried (withDensity_absolutelyContinuous μ _ hφ.carried)]
      with ζ hζ
    have hs := discRadius_pos hζ
    by_cases hlt : ‖x - ζ‖ < discRadius ζ
    · obtain ⟨hB, h3⟩ := near_of_lt_discRadius hx hζ hlt
      rw [indicator_of_mem hB]
      apply ENNReal.ofReal_le_ofReal
      have hk0 := bumpKernel_le hs (x - ζ)
      rw [indicator_of_mem (by simpa using hlt : x - ζ ∈ ball (0 : ℂ) (discRadius ζ)),
        Pi.one_apply, mul_one] at hk0
      refine hk0.trans ?_
      have hs' : (1 - ‖x‖ ^ 2) / 12 ≤ discRadius ζ := by
        unfold discRadius
        linarith
      have e : c = 4 / (Real.pi * ((1 - ‖x‖ ^ 2) / 12) ^ 2) := by
        rw [hc]
        field_simp
        ring
      rw [e]
      gcongr
    · rw [bumpKernel_eq_zero hs (not_lt.1 hlt), ENNReal.ofReal_zero]
      exact bot_le
  have hμB : μ B ≠ ∞ := (hφ.measure_hypBall_lt_top hx r₂).ne
  have hw : ∫⁻ ζ in B, w ζ ∂μ ≤ ENNReal.ofReal (D₂ / 2) :=
    setLIntegral_inv_two_mul_le (m := fun ζ ↦ μ (hypBall ζ R)) hBm hμB hD₂.le fun ζ hζ ↦
      (measure_mono (hypBall_subset_hypBall_two_mul hx hζ)).trans (h₂ ζ hζ.1)
  calc smoothedDensity (μ.withDensity w) discRadius x
      ≤ ∫⁻ ζ, B.indicator (fun _ ↦ ENNReal.ofReal c) ζ ∂(μ.withDensity w) :=
        lintegral_mono_ae hk
    _ = ENNReal.ofReal c * (μ.withDensity w) B := lintegral_indicator_const hBm _
    _ = ENNReal.ofReal c * ∫⁻ ζ in B, w ζ ∂μ := by rw [withDensity_apply _ hBm]
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (D₂ / 2) := by gcongr
    _ = ENNReal.ofReal (288 * D₂ / Real.pi / (1 - ‖x‖ ^ 2) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hc]
        field_simp
        ring

/-- The pointwise bound of `exists_localPot_le`, as a hypothesis. -/
def LocalPotBound (C₀ : ℝ) : Prop :=
  ∀ (Ω : Set ℂ) (σ : Measure ℂ) (s : ℂ → ℝ), IsLocalPotData Ω σ s → ∀ z : ℂ,
    ENNReal.ofReal (localPot σ s z) ≤
      ∫⁻ ζ in {ζ | dist z ζ < s ζ},
        ENNReal.ofReal ((4 * Real.pi)⁻¹ * (Real.log (s ζ ^ 2 / ‖z - ζ‖ ^ 2) + C₀)) ∂σ

/-- The constant of the bound on the local potential in the disc. -/
def potConstDisc (D₂ C_L C₀ : ℝ) : ℝ :=
  2 * (4 * Real.pi)⁻¹ * (D₂ * C_L / 2) +
    (4 * Real.pi)⁻¹ * (2 * Real.log (1 / r₂) + C₀) * (D₂ / 2)

theorem potConstDisc_nonneg {D₂ C_L C₀ : ℝ} (hD₂ : 0 ≤ D₂) (hCL : 0 ≤ C_L) (hC₀ : 0 ≤ C₀) :
    0 ≤ potConstDisc D₂ C_L C₀ := by
  have hlog1 : 0 ≤ Real.log (1 / r₂) :=
    Real.log_nonneg (by rw [le_div_iff₀ r₂_pos]; linarith [r₂_le_one])
  unfold potConstDisc
  positivity

/-- Bound on the local potential (doc §5.3), with the constants `D₂` (as in
`smoothedDensity_disc_le`) and `C_L` ([Chr91, Lemma 2.3] at radius `r₂`). -/
theorem localPot_disc_le_of (hφ : IsSubharmonicWeight 𝔻 φ μ) (hd : IsLocallyDoublingDisc μ)
    (hR : 0 < R) (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {D₂ C_L C₀ : ℝ} (hD₂ : 0 < D₂)
    (hCL : 0 ≤ C_L) (hC₀ : 0 ≤ C₀) (hpot : LocalPotBound C₀)
    (h₂ : ∀ x ∈ 𝔻, μ (hypBall x (2 * r₂)) ≤ ENNReal.ofReal D₂ * μ (hypBall x R))
    (hL : ∀ z ∈ 𝔻, ∫⁻ ζ in hypBall z r₂, ENNReal.ofReal (Real.log (r₂ / hypDist z ζ)) ∂μ ≤
      ENNReal.ofReal C_L * μ (hypBall z r₂))
    {z : ℂ} (hz : z ∈ 𝔻) :
    localPot (μ.withDensity (massWeightDisc μ R)) discRadius z ≤ potConstDisc D₂ C_L C₀ := by
  have : SigmaFinite μ := hφ.sigmaFinite isOpen_ball
  set w := massWeightDisc μ R with hwdef
  have hwm : Measurable w := measurable_massWeightDisc R
  set σ := μ.withDensity w with hσdef
  have h := isLocalPotData_disc hφ hd hR hm
  have hP := hpot 𝔻 σ discRadius h z
  set B := hypBall z r₂ with hBdef
  have hBm : MeasurableSet B := measurableSet_hypBall z r₂
  have hμB : μ B ≠ ∞ := (hφ.measure_hypBall_lt_top hz r₂).ne
  have hEB : {ζ | dist z ζ < discRadius ζ} ⊆ B := by
    intro ζ hζ
    have hζ' : dist z ζ < discRadius ζ := hζ
    have hζ𝔻 : ζ ∈ 𝔻 := by
      by_contra hn
      have h1 : 1 ≤ ‖ζ‖ := by simpa using hn
      have : discRadius ζ ≤ 0 := by
        unfold discRadius
        nlinarith
      exact absurd hζ' (not_lt.2 (this.trans dist_nonneg))
    rw [dist_eq_norm] at hζ'
    exact (near_of_lt_discRadius hz hζ𝔻 hζ').1
  set a₁ : ℝ := 2 * (4 * Real.pi)⁻¹ with ha₁
  set a₀ : ℝ := (4 * Real.pi)⁻¹ * (2 * Real.log (1 / r₂) + C₀) with ha₀
  have hlog1 : 0 ≤ Real.log (1 / r₂) :=
    Real.log_nonneg (by rw [le_div_iff₀ r₂_pos]; linarith [r₂_le_one])
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₀0 : 0 ≤ a₀ := by positivity
  have hpt : ∀ ζ ∈ B, ENNReal.ofReal ((4 * Real.pi)⁻¹ *
      (Real.log (discRadius ζ ^ 2 / ‖z - ζ‖ ^ 2) + C₀)) ≤
      ENNReal.ofReal a₁ * ENNReal.ofReal (Real.log (r₂ / hypDist z ζ)) + ENNReal.ofReal a₀ := by
    intro ζ hζ
    have hlog := log_discRadius_sq_le hz hζ
    calc ENNReal.ofReal ((4 * Real.pi)⁻¹ * (Real.log (discRadius ζ ^ 2 / ‖z - ζ‖ ^ 2) + C₀))
        ≤ ENNReal.ofReal (a₁ * Real.log (r₂ / hypDist z ζ) + a₀) := by
          apply ENNReal.ofReal_le_ofReal
          have hpi : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
          have := mul_le_mul_of_nonneg_left (add_le_add_right hlog C₀) hpi
          rw [ha₁, ha₀]
          linarith
      _ ≤ ENNReal.ofReal (a₁ * Real.log (r₂ / hypDist z ζ)) + ENNReal.ofReal a₀ :=
          ENNReal.ofReal_add_le
      _ = _ := by rw [ENNReal.ofReal_mul ha₁0]
  have hrestr : σ.restrict B = (μ.restrict B).withDensity w := restrict_withDensity hBm w
  have hbound1 : ∫⁻ ζ in B, ENNReal.ofReal (Real.log (r₂ / hypDist z ζ)) ∂σ ≤
      ENNReal.ofReal (D₂ * C_L / 2) := by
    rw [hrestr]
    refine (lintegral_withDensity_le_lintegral_mul _ hwm _).trans ?_
    exact setLIntegral_inv_two_mul_mul_le (m := fun ζ ↦ μ (hypBall ζ R)) hBm hμB hD₂.le
      (fun ζ hζ ↦ (measure_mono (hypBall_subset_hypBall_two_mul hz hζ)).trans (h₂ ζ hζ.1))
      (hL z hz)
  have hbound0 : σ B ≤ ENNReal.ofReal (D₂ / 2) := by
    rw [hσdef, withDensity_apply _ hBm]
    exact setLIntegral_inv_two_mul_le (m := fun ζ ↦ μ (hypBall ζ R)) hBm hμB hD₂.le
      fun ζ hζ ↦ (measure_mono (hypBall_subset_hypBall_two_mul hz hζ)).trans (h₂ ζ hζ.1)
  have hfin : ENNReal.ofReal (localPot σ discRadius z) ≤
      ENNReal.ofReal (potConstDisc D₂ C_L C₀) := by
    calc ENNReal.ofReal (localPot σ discRadius z)
        ≤ ∫⁻ ζ in {ζ | dist z ζ < discRadius ζ}, ENNReal.ofReal ((4 * Real.pi)⁻¹ *
            (Real.log (discRadius ζ ^ 2 / ‖z - ζ‖ ^ 2) + C₀)) ∂σ := hP
      _ ≤ ∫⁻ ζ in B, ENNReal.ofReal ((4 * Real.pi)⁻¹ *
            (Real.log (discRadius ζ ^ 2 / ‖z - ζ‖ ^ 2) + C₀)) ∂σ := lintegral_mono_set hEB
      _ ≤ ∫⁻ ζ in B, (ENNReal.ofReal a₁ * ENNReal.ofReal (Real.log (r₂ / hypDist z ζ)) +
            ENNReal.ofReal a₀) ∂σ := setLIntegral_mono' hBm hpt
      _ = ENNReal.ofReal a₁ * ∫⁻ ζ in B, ENNReal.ofReal (Real.log (r₂ / hypDist z ζ)) ∂σ +
            ENNReal.ofReal a₀ * σ B := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            setLIntegral_const, mul_comm (ENNReal.ofReal a₀)]
      _ ≤ ENNReal.ofReal a₁ * ENNReal.ofReal (D₂ * C_L / 2) +
            ENNReal.ofReal a₀ * ENNReal.ofReal (D₂ / 2) := by gcongr
      _ = ENNReal.ofReal (potConstDisc D₂ C_L C₀) := by
          rw [← ENNReal.ofReal_mul ha₁0, ← ENNReal.ofReal_mul ha₀0,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          rfl
  exact (ENNReal.ofReal_le_ofReal_iff (potConstDisc_nonneg hD₂.le hCL hC₀)).1 hfin

end DiscBounds

/-! #### Explicit bounds in the plane -/

section PlaneBounds

variable {φ : ℂ → ℝ} {μ : Measure ℂ} {R : ℝ}

/-- Lower bound for `g` (doc §4.2), with the constant `C` of doubling up to scale `R`. -/
theorem smoothedDensity_plane_ge (hφ : IsSubharmonicWeight univ φ μ) (hR : 0 < R)
    (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) {C : ℝ≥0}
    (hC : ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ R → μ (ball z (2 * r)) ≤ C * μ (ball z r)) (x : ℂ) :
    ENNReal.ofReal (1 / (2 * Real.pi * R ^ 2 * (C : ℝ) ^ 2)) ≤
      smoothedDensity (μ.withDensity (massWeight μ R)) (fun _ ↦ R) x := by
  set w := massWeight μ R with hwdef
  set B := ball x (R / 2) with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  have hCC : (C : ℝ≥0∞) = ENNReal.ofReal (C : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
  have h2R : μ (ball x R) ≤ C * μ B := by
    have := hC x (R / 2) (by positivity) (by linarith)
    rwa [show 2 * (R / 2) = R by ring] at this
  have hRB : ∀ ζ ∈ B, μ (ball ζ R) ≤ ENNReal.ofReal ((C : ℝ) ^ 2) * μ B := by
    intro ζ hζ
    have hsub : ball ζ R ⊆ ball x (2 * R) := by
      intro y hy
      rw [mem_ball] at hy hζ ⊢
      linarith [dist_triangle y ζ x]
    calc μ (ball ζ R) ≤ μ (ball x (2 * R)) := measure_mono hsub
      _ ≤ C * μ (ball x R) := hC x R hR le_rfl
      _ ≤ C * (C * μ B) := by gcongr
      _ = ENNReal.ofReal ((C : ℝ) ^ 2) * μ B := by
          rw [ENNReal.ofReal_pow NNReal.zero_le_coe, ← hCC]
          ring
  have hμB : μ B ≠ ∞ := (hφ.measure_ball_lt_top x _).ne
  have hμB0 : μ B ≠ 0 := by
    intro h0
    have h1 : (1 : ℝ≥0∞) ≤ 0 := by
      calc (1 : ℝ≥0∞) ≤ μ (ball x R) := hm x
        _ ≤ C * μ B := h2R
        _ = 0 := by rw [h0, mul_zero]
    exact absurd h1 (by norm_num)
  have hCpos : 0 < (C : ℝ) := by
    by_contra hc
    have hc0 : C = 0 := by
      have := le_antisymm (not_lt.1 hc) C.2
      exact_mod_cast this
    apply hμB0
    have h1 : (1 : ℝ≥0∞) ≤ 0 := by
      calc (1 : ℝ≥0∞) ≤ μ (ball x R) := hm x
        _ ≤ C * μ B := h2R
        _ = 0 := by rw [hc0, ENNReal.coe_zero, zero_mul]
    exact absurd h1 (by norm_num)
  have hw : ENNReal.ofReal (1 / (2 * (C : ℝ) ^ 2)) ≤ ∫⁻ ζ in B, w ζ ∂μ :=
    le_setLIntegral_inv_two_mul (m := fun ζ ↦ μ (ball ζ R)) hBm hμB0 hμB (by positivity) hRB
  have hk : ∀ ζ ∈ B, ENNReal.ofReal (1 / (Real.pi * R ^ 2)) ≤
      ENNReal.ofReal (bumpKernel R (x - ζ)) := by
    intro ζ hζ
    apply ENNReal.ofReal_le_ofReal
    have hk0 := le_bumpKernel hR (x - ζ)
    have hmem : x - ζ ∈ ball (0 : ℂ) (R / 2) := by
      rw [mem_ball, dist_zero_right, ← dist_eq_norm, dist_comm]
      exact hζ
    rwa [indicator_of_mem hmem, Pi.one_apply, mul_one] at hk0
  calc ENNReal.ofReal (1 / (2 * Real.pi * R ^ 2 * (C : ℝ) ^ 2))
      = ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * ENNReal.ofReal (1 / (2 * (C : ℝ) ^ 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * ∫⁻ ζ in B, w ζ ∂μ := by gcongr
    _ = ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * (μ.withDensity w) B := by
        rw [withDensity_apply _ hBm]
    _ = ∫⁻ ζ in B, ENNReal.ofReal (1 / (Real.pi * R ^ 2)) ∂(μ.withDensity w) :=
        (setLIntegral_const B _).symm
    _ ≤ ∫⁻ ζ in B, ENNReal.ofReal (bumpKernel R (x - ζ)) ∂(μ.withDensity w) :=
        setLIntegral_mono' hBm hk
    _ ≤ smoothedDensity (μ.withDensity w) (fun _ ↦ R) x := setLIntegral_le_lintegral _ _

/-- For `ζ ∈ B(x, R)`: `μ(B(x,R)) ≤ C μ(B(ζ,R))`. -/
theorem measure_ball_le_of_mem {C : ℝ≥0} (hR : 0 < R)
    (hC : ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ R → μ (ball z (2 * r)) ≤ C * μ (ball z r)) {x ζ : ℂ}
    (hζ : ζ ∈ ball x R) : μ (ball x R) ≤ ENNReal.ofReal (C : ℝ) * μ (ball ζ R) := by
  have hsub : ball x R ⊆ ball ζ (2 * R) := by
    intro y hy
    rw [mem_ball] at hy hζ ⊢
    linarith [dist_triangle y x ζ, dist_comm x ζ]
  rw [ENNReal.ofReal_coe_nnreal]
  exact (measure_mono hsub).trans (hC ζ R hR le_rfl)

/-- Upper bound for `g` (doc §4.2). -/
theorem smoothedDensity_plane_le (hφ : IsSubharmonicWeight univ φ μ) (hR : 0 < R) {C : ℝ≥0}
    (hC : ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ R → μ (ball z (2 * r)) ≤ C * μ (ball z r)) (x : ℂ) :
    smoothedDensity (μ.withDensity (massWeight μ R)) (fun _ ↦ R) x ≤
      ENNReal.ofReal (2 * C / (Real.pi * R ^ 2)) := by
  set w := massWeight μ R with hwdef
  set B := ball x R with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  set c : ℝ := 4 / (Real.pi * R ^ 2) with hc
  have hk : ∀ ζ, ENNReal.ofReal (bumpKernel R (x - ζ)) ≤
      B.indicator (fun _ ↦ ENNReal.ofReal c) ζ := by
    intro ζ
    have hk0 := bumpKernel_le hR (x - ζ)
    by_cases hζ : ζ ∈ B
    · rw [indicator_of_mem hζ]
      apply ENNReal.ofReal_le_ofReal
      have hmem : x - ζ ∈ ball (0 : ℂ) R := by
        rw [mem_ball, dist_zero_right, ← dist_eq_norm, dist_comm]
        exact hζ
      rwa [indicator_of_mem hmem, Pi.one_apply, mul_one] at hk0
    · rw [indicator_of_notMem hζ]
      have hmem : x - ζ ∉ ball (0 : ℂ) R := by
        rw [mem_ball, dist_zero_right, ← dist_eq_norm, dist_comm]
        exact hζ
      rw [indicator_of_notMem hmem, mul_zero] at hk0
      rw [ENNReal.ofReal_of_nonpos hk0]
  have hμB : μ B ≠ ∞ := (hφ.measure_ball_lt_top x _).ne
  have hw : ∫⁻ ζ in B, w ζ ∂μ ≤ ENNReal.ofReal ((C : ℝ) / 2) :=
    setLIntegral_inv_two_mul_le (m := fun ζ ↦ μ (ball ζ R)) hBm hμB C.2
      fun ζ hζ ↦ measure_ball_le_of_mem hR hC hζ
  calc smoothedDensity (μ.withDensity w) (fun _ ↦ R) x
      ≤ ∫⁻ ζ, B.indicator (fun _ ↦ ENNReal.ofReal c) ζ ∂(μ.withDensity w) := lintegral_mono hk
    _ = ENNReal.ofReal c * (μ.withDensity w) B := lintegral_indicator_const hBm _
    _ = ENNReal.ofReal c * ∫⁻ ζ in B, w ζ ∂μ := by rw [withDensity_apply _ hBm]
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal ((C : ℝ) / 2) := by gcongr
    _ = ENNReal.ofReal (2 * C / (Real.pi * R ^ 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hc]
        field_simp
        ring

/-- The constant of the bound on the local potential in the plane. -/
def potConstPlane (C C_L C₀ : ℝ) : ℝ :=
  2 * (4 * Real.pi)⁻¹ * (C * C_L / 2) + (4 * Real.pi)⁻¹ * C₀ * (C / 2)

/-- Bound on the local potential (doc §4.3). -/
theorem localPot_plane_le_of (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoubling μ)
    (hR : 0 < R) (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) {C : ℝ≥0}
    (hC : ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ R → μ (ball z (2 * r)) ≤ C * μ (ball z r))
    {C_L C₀ : ℝ} (hCL : 0 ≤ C_L) (hC₀ : 0 ≤ C₀) (hpot : LocalPotBound C₀)
    (hL : ∀ z : ℂ, ∫⁻ ζ in ball z R, ENNReal.ofReal (Real.log (R / dist z ζ)) ∂μ ≤
      ENNReal.ofReal C_L * μ (ball z R)) (z : ℂ) :
    localPot (μ.withDensity (massWeight μ R)) (fun _ ↦ R) z ≤ potConstPlane C C_L C₀ := by
  have : SigmaFinite μ := hφ.sigmaFinite isOpen_univ
  set w := massWeight μ R with hwdef
  have hwm : Measurable w := measurable_massWeight R
  set σ := μ.withDensity w with hσdef
  have h := isLocalPotData_plane hφ hd hR hm
  have hP := hpot univ σ (fun _ ↦ R) h z
  set B := ball z R with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  have hμB : μ B ≠ ∞ := (hφ.measure_ball_lt_top z _).ne
  have hEB : {ζ : ℂ | dist z ζ < R} = B := by
    ext ζ
    rw [hBdef, mem_ball, dist_comm]
    rfl
  set a₁ : ℝ := 2 * (4 * Real.pi)⁻¹ with ha₁
  set a₀ : ℝ := (4 * Real.pi)⁻¹ * C₀ with ha₀
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₀0 : 0 ≤ a₀ := by positivity
  have hpt : ∀ ζ, ENNReal.ofReal ((4 * Real.pi)⁻¹ * (Real.log (R ^ 2 / ‖z - ζ‖ ^ 2) + C₀)) ≤
      ENNReal.ofReal a₁ * ENNReal.ofReal (Real.log (R / dist z ζ)) + ENNReal.ofReal a₀ := by
    intro ζ
    have hlog : Real.log (R ^ 2 / ‖z - ζ‖ ^ 2) = 2 * Real.log (R / dist z ζ) := by
      rw [dist_eq_norm, ← div_pow, Real.log_pow]
      norm_num
    calc ENNReal.ofReal ((4 * Real.pi)⁻¹ * (Real.log (R ^ 2 / ‖z - ζ‖ ^ 2) + C₀))
        = ENNReal.ofReal (a₁ * Real.log (R / dist z ζ) + a₀) := by
          congr 1
          rw [hlog, ha₁, ha₀]
          ring
      _ ≤ ENNReal.ofReal (a₁ * Real.log (R / dist z ζ)) + ENNReal.ofReal a₀ :=
          ENNReal.ofReal_add_le
      _ = _ := by rw [ENNReal.ofReal_mul ha₁0]
  have hrestr : σ.restrict B = (μ.restrict B).withDensity w := restrict_withDensity hBm w
  have hbound1 : ∫⁻ ζ in B, ENNReal.ofReal (Real.log (R / dist z ζ)) ∂σ ≤
      ENNReal.ofReal (C * C_L / 2) := by
    rw [hrestr]
    refine (lintegral_withDensity_le_lintegral_mul _ hwm _).trans ?_
    exact setLIntegral_inv_two_mul_mul_le (m := fun ζ ↦ μ (ball ζ R)) hBm hμB C.2
      (fun ζ hζ ↦ measure_ball_le_of_mem hR hC hζ) (hL z)
  have hbound0 : σ B ≤ ENNReal.ofReal ((C : ℝ) / 2) := by
    rw [hσdef, withDensity_apply _ hBm]
    exact setLIntegral_inv_two_mul_le (m := fun ζ ↦ μ (ball ζ R)) hBm hμB C.2
      fun ζ hζ ↦ measure_ball_le_of_mem hR hC hζ
  have hM : 0 ≤ potConstPlane C C_L C₀ := by
    unfold potConstPlane
    have := C.2
    positivity
  have hfin : ENNReal.ofReal (localPot σ (fun _ ↦ R) z) ≤
      ENNReal.ofReal (potConstPlane C C_L C₀) := by
    calc ENNReal.ofReal (localPot σ (fun _ ↦ R) z)
        ≤ ∫⁻ ζ in {ζ | dist z ζ < R}, ENNReal.ofReal ((4 * Real.pi)⁻¹ *
            (Real.log (R ^ 2 / ‖z - ζ‖ ^ 2) + C₀)) ∂σ := hP
      _ ≤ ∫⁻ ζ in B, (ENNReal.ofReal a₁ * ENNReal.ofReal (Real.log (R / dist z ζ)) +
            ENNReal.ofReal a₀) ∂σ := by
          rw [hEB]
          exact setLIntegral_mono' hBm fun ζ _ ↦ hpt ζ
      _ = ENNReal.ofReal a₁ * ∫⁻ ζ in B, ENNReal.ofReal (Real.log (R / dist z ζ)) ∂σ +
            ENNReal.ofReal a₀ * σ B := by
          rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_const,
            mul_comm (ENNReal.ofReal a₀)]
      _ ≤ ENNReal.ofReal a₁ * ENNReal.ofReal (C * C_L / 2) +
            ENNReal.ofReal a₀ * ENNReal.ofReal ((C : ℝ) / 2) := by gcongr
      _ = ENNReal.ofReal (potConstPlane C C_L C₀) := by
          have := C.2
          rw [← ENNReal.ofReal_mul ha₁0, ← ENNReal.ofReal_mul ha₀0,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          rfl
  exact (ENNReal.ofReal_le_ofReal_iff hM).1 hfin

/-- The doubling of `ν₀ + μ̃` in the plane. -/
theorem doubling_plane_add {ν₀ μ' : Measure ℂ} {Cd A : ℝ≥0}
    (hdC : IsLocallyDoublingWith μ Cd) (hν₀ : ν₀ ≤ μ) (h2 : μ ≤ (2 : ℝ≥0∞) • ν₀)
    (hμ' : ∀ z : ℂ, ∀ r : ℝ, 0 < r → 2 * r < 1 →
      μ' (ball z (2 * r)) ≤ A * μ' (ball z r)) :
    IsLocallyDoublingWith (ν₀ + μ') (max (2 * Cd) A) := by
  intro z r hr h2r
  rw [Measure.add_apply, Measure.add_apply]
  refine add_le_max_mul ?_ (hμ' z r hr h2r)
  calc ν₀ (ball z (2 * r)) ≤ μ (ball z (2 * r)) := Measure.le_iff'.1 hν₀ _
    _ ≤ Cd * μ (ball z r) := hdC z r hr h2r
    _ ≤ Cd * (2 * ν₀ (ball z r)) := by
        gcongr
        exact Measure.le_iff'.1 h2 _
    _ = ((2 * Cd : ℝ≥0) : ℝ≥0∞) * ν₀ (ball z r) := by push_cast; ring

/-- Doubling of a measure with density between `ε` and `K`. -/
theorem withDensity_ball_two_mul_le {g : ℂ → ℝ≥0∞} {ε K : ℝ} (hε : 0 < ε)
    (hg : ∀ z, ENNReal.ofReal ε ≤ g z ∧ g z ≤ ENNReal.ofReal K) (z : ℂ) (r : ℝ) :
    volume.withDensity g (ball z (2 * r)) ≤
      ENNReal.ofReal (4 * K / ε) * volume.withDensity g (ball z r) := by
  rw [withDensity_apply _ measurableSet_ball, withDensity_apply _ measurableSet_ball]
  have hK : 0 ≤ K :=
    (ENNReal.ofReal_pos.1 ((ENNReal.ofReal_pos.2 hε).trans_le ((hg z).1.trans (hg z).2))).le
  calc ∫⁻ x in ball z (2 * r), g x ≤ ∫⁻ x in ball z (2 * r), ENNReal.ofReal K :=
        setLIntegral_mono measurable_const fun x _ ↦ (hg x).2
    _ = ENNReal.ofReal K * (4 * volume (ball z r)) := by
        rw [setLIntegral_const, Complex.volume_ball, Complex.volume_ball,
          ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
        ring
    _ = ENNReal.ofReal (4 * K / ε) * (ENNReal.ofReal ε * volume (ball z r)) := by
        rw [← mul_assoc (ENNReal.ofReal (4 * K / ε)), ← ENNReal.ofReal_mul (by positivity),
          div_mul_cancel₀ _ hε.ne', ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring
    _ = ENNReal.ofReal (4 * K / ε) * ∫⁻ x in ball z r, ENNReal.ofReal ε := by
        rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (4 * K / ε) * ∫⁻ x in ball z r, g x := by
        gcongr with x
        exact (hg x).1

end PlaneBounds

/-- **Lemma 6 (disc), core**: the construction of doc §3/§5, with all constants chosen before the
weight, from the doubling constant `Cd`, the radius `R` and the constants `D₁`, `D₂`, `C_L` of the
three doubling/[Chr91] inequalities used. -/
theorem lemma6_disc_core (Cd : ℝ≥0) {R : ℝ} (hR : 0 < R) {D₁ D₂ C_L : ℝ} (hD₁ : 0 < D₁)
    (hD₂ : 0 < D₂) (hCL : 0 ≤ C_L) :
    ∃ (ε K M : ℝ) (Cd' : ℝ≥0), 0 < ε ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ (φ : ℂ → ℝ) (μ : Measure ℂ), IsSubharmonicWeight 𝔻 φ μ →
        IsLocallyDoublingDiscWith μ Cd → (∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) →
        (∀ x ∈ 𝔻, μ (hypBall x (R + r₁)) ≤ ENNReal.ofReal D₁ * μ (hypBall x r₁)) →
        (∀ x ∈ 𝔻, μ (hypBall x (2 * r₂)) ≤ ENNReal.ofReal D₂ * μ (hypBall x R)) →
        (∀ z ∈ 𝔻, ∫⁻ ζ in hypBall z r₂, ENNReal.ofReal (Real.log (r₂ / hypDist z ζ)) ∂μ ≤
          ENNReal.ofReal C_L * μ (hypBall z r₂)) →
        ∃ (ψ : ℂ → ℝ) (ν₀ : Measure ℂ) (g : ℂ → ℝ≥0∞), Measurable g ∧
          IsSubharmonicWeight 𝔻 ψ (ν₀ + volume.withDensity g) ∧
          IsLocallyDoublingDiscWith (ν₀ + volume.withDensity g) Cd' ∧
          (∀ z ∈ 𝔻, |ψ z - φ z| ≤ M) ∧
          (∀ z ∈ 𝔻, ENNReal.ofReal (ε / (1 - ‖z‖ ^ 2) ^ 2) ≤ g z ∧
            g z ≤ ENNReal.ofReal (K / (1 - ‖z‖ ^ 2) ^ 2)) ∧
          (∀ z ∉ 𝔻, g z = 0) ∧ ν₀ ≤ μ ∧ μ ≤ (2 : ℝ≥0∞) • ν₀ := by
  obtain ⟨C₀, hC₀, hpot⟩ := exists_localPot_le
  set ε : ℝ := 128 / (25 * Real.pi * D₁) with hε
  set K : ℝ := 288 * D₂ / Real.pi with hK
  have hε0 : 0 < ε := by positivity
  have hK0 : 0 ≤ K := by positivity
  refine ⟨ε, K, potConstDisc D₂ C_L C₀,
    max (2 * Cd) (Real.toNNReal (4 * Real.cosh (1 / 2) ^ 2 * K / ε)), hε0, hK0,
    potConstDisc_nonneg hD₂.le hCL hC₀, fun φ μ hφ hdC hm h₁ h₂ hL ↦ ?_⟩
  have hd : IsLocallyDoublingDisc μ := ⟨Cd, hdC⟩
  have : SigmaFinite μ := hφ.sigmaFinite isOpen_ball
  have hw : Measurable (massWeightDisc μ R) := measurable_massWeightDisc R
  have h := isLocalPotData_disc hφ hd hR hm
  have hw1 := ae_massWeightDisc_le_one hφ.carried hm
  have hw2 := ae_massWeightDisc_le hφ.carried hm
  set g := smoothedDensity (μ.withDensity (massWeightDisc μ R)) discRadius with hgdef
  have hgb : ∀ z ∈ 𝔻, ENNReal.ofReal (ε / (1 - ‖z‖ ^ 2) ^ 2) ≤ g z ∧
      g z ≤ ENNReal.ofReal (K / (1 - ‖z‖ ^ 2) ^ 2) := fun z hz ↦
    ⟨smoothedDensity_disc_ge hφ hm hD₁ h₁ hz, smoothedDensity_disc_le hφ hD₂ h₂ hz⟩
  have hg0 : ∀ z ∉ 𝔻, g z = 0 := fun z hz ↦ h.smoothedDensity_eq_zero hz
  have hν₀ : μ.withDensity (fun ζ ↦ 1 - massWeightDisc μ R ζ) ≤ μ :=
    withDensity_le_self (ae_of_all _ fun _ ↦ tsub_le_self)
  have h2 := le_two_smul_withDensity_one_sub hw hw2
  refine ⟨fun z ↦ φ z + localPot (μ.withDensity (massWeightDisc μ R)) discRadius z,
    μ.withDensity (fun ζ ↦ 1 - massWeightDisc μ R ζ), g, h.measurable_smoothedDensity,
    isSubharmonicWeight_regularized hφ hw hw1 h, ?_, ?_, hgb, hg0, hν₀, h2⟩
  · exact doubling_disc_add hdC hν₀ h2 fun z hz r hr h2r ↦
      doubling_of_hypArea_sandwich hε0 hK0
        (smul_hypArea_le_withDensity hε0.le fun z hz ↦ (hgb z hz).1)
        (withDensity_le_smul_hypArea hK0 (fun z hz ↦ (hgb z hz).2) hg0) hz hr h2r
  · intro z hz
    simp only [add_sub_cancel_left]
    rw [abs_of_nonneg (h.localPot_nonneg z)]
    exact localPot_disc_le_of hφ hd hR hm hD₂ hCL hC₀ hpot h₂ hL hz

/-- The three inequalities used by the construction, for a fixed locally doubling `μ`. -/
theorem exists_disc_consts {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R) :
    ∃ D₁ D₂ C_L : ℝ, 0 < D₁ ∧ 0 < D₂ ∧ 0 ≤ C_L ∧
      (∀ x ∈ 𝔻, μ (hypBall x (R + r₁)) ≤ ENNReal.ofReal D₁ * μ (hypBall x r₁)) ∧
      (∀ x ∈ 𝔻, μ (hypBall x (2 * r₂)) ≤ ENNReal.ofReal D₂ * μ (hypBall x R)) ∧
      (∀ z ∈ 𝔻, ∫⁻ ζ in hypBall z r₂, ENNReal.ofReal (Real.log (r₂ / hypDist z ζ)) ∂μ ≤
        ENNReal.ofReal C_L * μ (hypBall z r₂)) := by
  obtain ⟨C₁, s₁, hC₁, hs₁, hrp₁⟩ := measure_hypBall_le_rpow hd (R + r₁)
  obtain ⟨C₂, s₂, hC₂, hs₂, hrp₂⟩ := measure_hypBall_le_rpow hd (max R (2 * r₂))
  obtain ⟨CL, hCL⟩ := christ_lemma23_disc hd r₂
  have hr₁ := r₁_pos
  refine ⟨C₁ * ((R + r₁) / r₁) ^ s₁, C₂ * (max R (2 * r₂) / R) ^ s₂, CL, by positivity,
    mul_pos hC₂ (Real.rpow_pos_of_pos (div_pos (hR.trans_le (le_max_left _ _)) hR) _), CL.2,
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun z hz ↦ ?_⟩
  · exact hrp₁ x x (R + r₁) r₁ hx hx hr₁ (by linarith) le_rfl
      (by rw [hypDist_self]; positivity)
  · exact (measure_mono (hypBall_mono (le_max_right _ _))).trans
      (hrp₂ x x _ R hx hx hR (le_max_left _ _) le_rfl
        (by rw [hypDist_self]; exact hR.le.trans (le_max_left _ _)))
  · have := hCL z hz r₂ r₂_pos le_rfl
    rwa [← ENNReal.ofReal_coe_nnreal] at this

/-- The three inequalities, uniformly in the class `MeasClassDisc · Cd R`. -/
theorem exists_disc_consts_quant (Cd : ℝ≥0) {R : ℝ} (hR : 0 < R) :
    ∃ D₁ D₂ C_L : ℝ, 0 < D₁ ∧ 0 < D₂ ∧ 0 ≤ C_L ∧ ∀ μ : Measure ℂ, MeasClassDisc μ Cd R →
      (∀ x ∈ 𝔻, μ (hypBall x (R + r₁)) ≤ ENNReal.ofReal D₁ * μ (hypBall x r₁)) ∧
      (∀ x ∈ 𝔻, μ (hypBall x (2 * r₂)) ≤ ENNReal.ofReal D₂ * μ (hypBall x R)) ∧
      (∀ z ∈ 𝔻, ∫⁻ ζ in hypBall z r₂, ENNReal.ofReal (Real.log (r₂ / hypDist z ζ)) ∂μ ≤
        ENNReal.ofReal C_L * μ (hypBall z r₂)) := by
  obtain ⟨C₁, s₁, hC₁, hs₁, hrp₁⟩ := measure_ball_le_rpow_quant (X := HDisc) Cd (R + r₁)
  obtain ⟨C₂, s₂, hC₂, hs₂, hrp₂⟩ := measure_ball_le_rpow_quant (X := HDisc) Cd (max R (2 * r₂))
  obtain ⟨CL, hCL⟩ := christ_disc_quant Cd R r₂
  have hr₁ := r₁_pos
  refine ⟨C₁ * ((R + r₁) / r₁) ^ s₁, C₂ * (max R (2 * r₂) / R) ^ s₂, CL, by positivity,
    mul_pos hC₂ (Real.rpow_pos_of_pos (div_pos (hR.trans_le (le_max_left _ _)) hR) _), CL.2,
    fun μ hμ ↦ ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun z hz ↦ ?_⟩⟩
  · have hdbl := hμ.measClassM_discPull.doubling
    have := hrp₁ (discPull μ) hdbl (HDisc.mk x hx) (HDisc.mk x hx) (R + r₁) r₁ hr₁ (by linarith)
      le_rfl (by rw [dist_self]; positivity)
    rwa [discPull_ball, discPull_ball] at this
  · have hdbl := hμ.measClassM_discPull.doubling
    have := hrp₂ (discPull μ) hdbl (HDisc.mk x hx) (HDisc.mk x hx) _ R hR (le_max_left _ _)
      le_rfl (by rw [dist_self]; exact hR.le.trans (le_max_left _ _))
    rw [discPull_ball, discPull_ball] at this
    exact (measure_mono (hypBall_mono (le_max_right _ _))).trans this
  · have := hCL μ hμ z hz r₂ r₂_pos le_rfl
    rwa [← ENNReal.ofReal_coe_nnreal] at this

end Reg

theorem smoothedDensity_plane_bounds {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoubling μ) {R : ℝ} (hR : 0 < R)
    (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ ε K : ℝ, 0 < ε ∧ ∀ x : ℂ,
      ENNReal.ofReal ε ≤ smoothedDensity (μ.withDensity (massWeight μ R)) (fun _ ↦ R) x ∧
      smoothedDensity (μ.withDensity (massWeight μ R)) (fun _ ↦ R) x ≤ ENNReal.ofReal K := by
  obtain ⟨C, hC1, hC⟩ := doubling_upTo_plane hd R
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos (by exact_mod_cast hC1)
  exact ⟨1 / (2 * Real.pi * R ^ 2 * (C : ℝ) ^ 2), 2 * C / (Real.pi * R ^ 2), by positivity,
    fun x ↦ ⟨Reg.smoothedDensity_plane_ge hφ hR hm hC x, Reg.smoothedDensity_plane_le hφ hR hC x⟩⟩

theorem smoothedDensity_disc_bounds {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight 𝔻 φ μ) (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R)
    (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ ε K : ℝ, 0 < ε ∧ ∀ x ∈ 𝔻,
      ENNReal.ofReal (ε / (1 - ‖x‖ ^ 2) ^ 2) ≤
        smoothedDensity (μ.withDensity (massWeightDisc μ R)) discRadius x ∧
      smoothedDensity (μ.withDensity (massWeightDisc μ R)) discRadius x ≤
        ENNReal.ofReal (K / (1 - ‖x‖ ^ 2) ^ 2) := by
  obtain ⟨D₁, D₂, C_L, hD₁, hD₂, hCL, h₁, h₂, hL⟩ := Reg.exists_disc_consts hd hR
  exact ⟨128 / (25 * Real.pi * D₁), 288 * D₂ / Real.pi, by positivity, fun x hx ↦
    ⟨Reg.smoothedDensity_disc_ge hφ hm hD₁ h₁ hx, Reg.smoothedDensity_disc_le hφ hD₂ h₂ hx⟩⟩

theorem localPot_plane_le {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ M : ℝ, ∀ z : ℂ, localPot (μ.withDensity (massWeight μ R)) (fun _ ↦ R) z ≤ M := by
  obtain ⟨C, -, hC⟩ := doubling_upTo_plane hd R
  obtain ⟨CL, hCL⟩ := christ_lemma23_plane hd R
  obtain ⟨C₀, hC₀, hpot⟩ := exists_localPot_le
  refine ⟨Reg.potConstPlane C CL C₀, fun z ↦
    Reg.localPot_plane_le_of hφ hd hR hm hC CL.2 hC₀ hpot (fun z ↦ ?_) z⟩
  have := hCL z R hR le_rfl
  rwa [← ENNReal.ofReal_coe_nnreal] at this

theorem localPot_disc_le {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ M : ℝ, ∀ z ∈ 𝔻, localPot (μ.withDensity (massWeightDisc μ R)) discRadius z ≤ M := by
  obtain ⟨D₁, D₂, C_L, hD₁, hD₂, hCL, h₁, h₂, hL⟩ := Reg.exists_disc_consts hd hR
  obtain ⟨C₀, hC₀, hpot⟩ := exists_localPot_le
  exact ⟨Reg.potConstDisc D₂ C_L C₀, fun z hz ↦
    Reg.localPot_disc_le_of hφ hd hR hm hD₂ hCL hC₀ hpot h₂ hL hz⟩

/-- **Lemma 6 (plane)** (paper, p. 370). -/
theorem lemma6_plane {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ (ψ : ℂ → ℝ) (ν₀ : Measure ℂ) (g : ℂ → ℝ≥0∞) (ε K M : ℝ), 0 < ε ∧ Measurable g ∧
      IsSubharmonicWeight univ ψ (ν₀ + volume.withDensity g) ∧
      IsLocallyDoubling (ν₀ + volume.withDensity g) ∧
      (∀ z, |ψ z - φ z| ≤ M) ∧
      (∀ z, ENNReal.ofReal ε ≤ g z ∧ g z ≤ ENNReal.ofReal K) ∧
      ν₀ ≤ μ ∧ μ ≤ (2 : ℝ≥0∞) • ν₀ := by
  obtain ⟨R, hR, hm⟩ := hm
  have : SigmaFinite μ := hφ.sigmaFinite isOpen_univ
  have hw : Measurable (massWeight μ R) := measurable_massWeight R
  have h := isLocalPotData_plane hφ hd hR hm
  have hw2 : ∀ᵐ ζ ∂μ, massWeight μ R ζ ≤ 2⁻¹ := ae_of_all _ (Reg.massWeight_le hm)
  have hw1 : ∀ᵐ ζ ∂μ, massWeight μ R ζ ≤ 1 :=
    ae_of_all _ fun ζ ↦ (Reg.massWeight_le hm ζ).trans (ENNReal.inv_le_one.2 one_le_two)
  obtain ⟨ε, K, hε, hgb⟩ := smoothedDensity_plane_bounds hφ hd hR hm
  obtain ⟨M, hM⟩ := localPot_plane_le hφ hd hR hm
  obtain ⟨Cd, hdC⟩ := hd
  have hν₀ : μ.withDensity (fun ζ ↦ 1 - massWeight μ R ζ) ≤ μ :=
    Reg.withDensity_le_self (ae_of_all _ fun _ ↦ tsub_le_self)
  have h2 := Reg.le_two_smul_withDensity_one_sub hw hw2
  refine ⟨fun z ↦ φ z + localPot (μ.withDensity (massWeight μ R)) (fun _ ↦ R) z,
    μ.withDensity (fun ζ ↦ 1 - massWeight μ R ζ),
    smoothedDensity (μ.withDensity (massWeight μ R)) (fun _ ↦ R), ε, K, M, hε,
    h.measurable_smoothedDensity, Reg.isSubharmonicWeight_regularized hφ hw hw1 h,
    ⟨_, Reg.doubling_plane_add (A := Real.toNNReal (4 * K / ε)) hdC hν₀ h2
      fun z r _ _ ↦ Reg.withDensity_ball_two_mul_le hε hgb z r⟩, fun z ↦ ?_, hgb, hν₀, h2⟩
  simp only [add_sub_cancel_left]
  rw [abs_of_nonneg (h.localPot_nonneg z)]
  exact hM z

/-- **Lemma 6 (disc)** (paper, p. 370). -/
theorem lemma6_disc {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ (ψ : ℂ → ℝ) (ν₀ : Measure ℂ) (g : ℂ → ℝ≥0∞) (ε K M : ℝ), 0 < ε ∧ Measurable g ∧
      IsSubharmonicWeight 𝔻 ψ (ν₀ + volume.withDensity g) ∧
      IsLocallyDoublingDisc (ν₀ + volume.withDensity g) ∧
      (∀ z ∈ 𝔻, |ψ z - φ z| ≤ M) ∧
      (∀ z ∈ 𝔻, ENNReal.ofReal (ε / (1 - ‖z‖ ^ 2) ^ 2) ≤ g z ∧
        g z ≤ ENNReal.ofReal (K / (1 - ‖z‖ ^ 2) ^ 2)) ∧
      (∀ z ∉ 𝔻, g z = 0) ∧
      ν₀ ≤ μ ∧ μ ≤ (2 : ℝ≥0∞) • ν₀ := by
  obtain ⟨R, hR, hm⟩ := hm
  obtain ⟨D₁, D₂, C_L, hD₁, hD₂, hCL, h₁, h₂, hL⟩ := Reg.exists_disc_consts hd hR
  obtain ⟨Cd, hdC⟩ := hd
  obtain ⟨ε, K, M, Cd', hε, -, -, hcore⟩ := Reg.lemma6_disc_core Cd hR hD₁ hD₂ hCL
  obtain ⟨ψ, ν₀, g, hg, hψ, hdbl, hψφ, hgb, hg0, hν₀, h2⟩ := hcore φ μ hφ hdC hm h₁ h₂ hL
  exact ⟨ψ, ν₀, g, ε, K, M, hε, hg, hψ, ⟨Cd', hdbl⟩, hψφ, hgb, hg0, hν₀, h2⟩

/-! ### Corollaries in the form consumed by M11 and M12 (reconciliation) -/

/-- Lemma 6 (disc) in the form M11 consumes: `μ' ≥ ε · hypArea` and `|φ − φ'| ≤ B`.  Follows
from `lemma6_disc` (`μ' = ν₀ + volume.withDensity g`, `g ≥ ε/(1-|z|²)²` on `𝔻`; `1 < ·`
implies the hypothesis `1 ≤ ·` of `lemma6_disc`). -/
theorem lemma6_disc_hypArea (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ) (ε B : ℝ), 0 < ε ∧ IsSubharmonicWeight 𝔻 φ' μ' ∧
      IsLocallyDoublingDisc μ' ∧ ENNReal.ofReal ε • hypArea ≤ μ' ∧
      ∀ z ∈ 𝔻, |φ z - φ' z| ≤ B := by
  obtain ⟨r, hr, hm'⟩ := hm
  obtain ⟨ψ, ν₀, g, ε, K, M, hε, hg, hψ, hdbl, hψφ, hgb, hg0, hν₀, h2⟩ :=
    lemma6_disc hφ hd ⟨r, hr, fun z hz ↦ (hm' z hz).le⟩
  exact ⟨ψ, ν₀ + volume.withDensity g, ε, M, hε, hψ, hdbl,
    (Reg.smul_hypArea_le_withDensity hε.le fun z hz ↦ (hgb z hz).1).trans
      (Measure.le_add_left le_rfl),
    fun z hz ↦ by rw [abs_sub_comm]; exact hψφ z hz⟩

/-- Lemma 6 (plane) in the form M12 consumes: `μ' ≥ ε · dm` and `|φ − φ'| ≤ B`.  Follows from
`lemma6_plane`. -/
theorem lemma6_plane_volume (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 < μ (ball z r)) :
    ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ) (ε B : ℝ), 0 < ε ∧ IsSubharmonicWeight univ φ' μ' ∧
      IsLocallyDoubling μ' ∧ ENNReal.ofReal ε • volume ≤ μ' ∧ ∀ z, |φ z - φ' z| ≤ B := by
  obtain ⟨r, hr, hm'⟩ := hm
  obtain ⟨ψ, ν₀, g, ε, K, M, hε, hg, hψ, hdbl, hψφ, hgb, hν₀, h2⟩ :=
    lemma6_plane hφ hd ⟨r, hr, fun z ↦ (hm' z).le⟩
  refine ⟨ψ, ν₀ + volume.withDensity g, ε, M, hε, hψ, hdbl, ?_,
    fun z ↦ by rw [abs_sub_comm]; exact hψφ z⟩
  rw [← withDensity_const]
  exact (withDensity_mono (ae_of_all _ fun z ↦ (hgb z).1)).trans (Measure.le_add_left le_rfl)

/-- **Lemma 6 (disc), uniform form** (requested for `theorem2_uniform`): the constants `ε`, `B`
and the class `(Cd', R')` of the regularized measure depend only on the class `(Cd, R)` of `μ`,
not on the weight.  (The construction of `lemma6_disc` is uniform: the bounds come from
[Chr91, Lemma 2.3] and doubling at bounded scales, `christ_disc_quant`, `doubling_upTo_disc`.) -/
theorem lemma6_disc_quant (Cd : ℝ≥0) (R : ℝ) (hR : 0 < R) :
    ∃ (ε B : ℝ) (Cd' : ℝ≥0) (R' : ℝ), 0 < ε ∧ 0 ≤ B ∧ 0 < R' ∧
      ∀ (φ : ℂ → ℝ) (μ : Measure ℂ), IsSubharmonicWeight 𝔻 φ μ → MeasClassDisc μ Cd R →
        ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ), IsSubharmonicWeight 𝔻 φ' μ' ∧
          MeasClassDisc μ' Cd' R' ∧ ENNReal.ofReal ε • hypArea ≤ μ' ∧
          ∀ z ∈ 𝔻, |φ z - φ' z| ≤ B := by
  obtain ⟨D₁, D₂, C_L, hD₁, hD₂, hCL, hconsts⟩ := Reg.exists_disc_consts_quant Cd hR
  obtain ⟨ε, K, M, Cd', hε, -, hM, hcore⟩ := Reg.lemma6_disc_core Cd hR hD₁ hD₂ hCL
  refine ⟨ε, M, Cd', (2 * ⌈1 / (1 / 2 : ℝ)⌉₊ + 1) * R, hε, hM, by positivity,
    fun φ μ hφ hμ ↦ ?_⟩
  obtain ⟨h₁, h₂, hL⟩ := hconsts μ hμ
  obtain ⟨ψ, ν₀, g, -, hψ, hdbl, hψφ, hgb, -, -, h2⟩ :=
    hcore φ μ hφ hμ.doubling (fun z hz ↦ (hμ.mass z hz).le) h₁ h₂ hL
  have hhalf : ∀ z ∈ 𝔻, ENNReal.ofReal (1 / 2) ≤ (ν₀ + volume.withDensity g) (hypBall z R) := by
    intro z hz
    have h1 : 1 < 2 * (ν₀ + volume.withDensity g) (hypBall z R) := by
      calc (1 : ℝ≥0∞) < μ (hypBall z R) := hμ.mass z hz
        _ ≤ ((2 : ℝ≥0∞) • ν₀) (hypBall z R) := Measure.le_iff'.1 h2 _
        _ = 2 * ν₀ (hypBall z R) := by rw [Measure.smul_apply, smul_eq_mul]
        _ ≤ 2 * (ν₀ + volume.withDensity g) (hypBall z R) := by
            rw [Measure.add_apply]
            gcongr
            exact le_self_add
    rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat,
      ENNReal.inv_le_iff_le_mul (by simp) (by simp)]
    exact h1.le
  refine ⟨ψ, ν₀ + volume.withDensity g, hψ, ⟨hdbl, fun z hz ↦ ?_,
    fun K hK hKc ↦ hψ.finite_of_compact K hK hKc⟩, ?_, fun z hz ↦ ?_⟩
  · have := ofReal_lt_measure_hypBall hR (by norm_num) hhalf 1 hz
    rwa [ENNReal.ofReal_one] at this
  · exact (Reg.smul_hypArea_le_withDensity hε.le fun z hz ↦ (hgb z hz).1).trans
      (Measure.le_add_left le_rfl)
  · rw [abs_sub_comm]
    exact hψφ z hz

/-- Splitting a σ-finite measure dominating another (used by M11 and M12 to write `μ' = ν + ε·m`;
moved here from M11 so that M12 need not import M11). -/
theorem Measure.exists_add_eq_of_le {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [SigmaFinite μ] (h : ν ≤ μ) : ∃ d : Measure X, d + ν = μ := by
  have : SigmaFinite ν := MeasureTheory.Measure.sigmaFinite_of_le μ h
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le h
  obtain ⟨f, hfdef⟩ : ∃ f, f = ν.rnDeriv μ := ⟨_, rfl⟩
  have hf : Measurable f := hfdef ▸ Measure.measurable_rnDeriv ν μ
  have hle : f ≤ᵐ[μ] 1 := hfdef ▸ Measure.rnDeriv_le_one_of_le h
  have hν : μ.withDensity f = ν := hfdef ▸ Measure.withDensity_rnDeriv_eq ν μ hac
  refine ⟨μ.withDensity (fun x ↦ 1 - f x), ?_⟩
  rw [← hν, ← withDensity_add_right _ hf]
  conv_rhs => rw [← withDensity_one (μ := μ)]
  apply withDensity_congr_ae
  filter_upwards [hle] with x hx
  exact tsub_add_cancel_of_le hx

end OC
