import OrtegaCerdaMultipliers.Potential.Local
import OrtegaCerdaMultipliers.Doubling.Quant
import OrtegaCerdaMultipliers.Foundations.HyperbolicExtra

/-!
# M04 (Regularization) — Lemma 6: regularization of the weight

See `blueprint/M04_Regularization.md`.  Scaffold: statements, proofs `sorry`; the definitions are
real.

Lemma 6 in `ℂ` and `𝔻`, via the compactly supported local potentials of M02 §4 applied to
`σ = w·μ` with `w(ζ) = 1/(2μ(B(ζ,R)))`.  Reconciliation: `logSmall_plane`, `logSmall_disc` moved
to M03 (`Doubling/Export.lean`); M03's names are used for (A1)–(A4) (`doubling_upTo_*`,
`christ_lemma23_*`, `rpow_le_measure_*`, `measure_singleton_*`); the forms of Lemma 6 consumed by
M11/M12 are the corollaries `lemma6_disc_hypArea`, `lemma6_plane_volume`.
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
    (hB : μ B ≠ ∞) {m f : ℂ → ℝ≥0∞} {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
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
  have := setLIntegral_inv_two_mul_mul_le hBm hB hD zero_le_one h (f := fun _ ↦ 1)
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
    IsLocalPotData univ (μ.withDensity (massWeight μ R)) (fun _ ↦ R) := sorry

theorem isLocalPotData_disc {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    IsLocalPotData 𝔻 (μ.withDensity (massWeightDisc μ R)) discRadius := sorry

theorem smoothedDensity_plane_bounds {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoubling μ) {R : ℝ} (hR : 0 < R)
    (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ ε K : ℝ, 0 < ε ∧ ∀ x : ℂ,
      ENNReal.ofReal ε ≤ smoothedDensity (μ.withDensity (massWeight μ R)) (fun _ ↦ R) x ∧
      smoothedDensity (μ.withDensity (massWeight μ R)) (fun _ ↦ R) x ≤ ENNReal.ofReal K := sorry

theorem smoothedDensity_disc_bounds {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight 𝔻 φ μ) (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R)
    (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ ε K : ℝ, 0 < ε ∧ ∀ x ∈ 𝔻,
      ENNReal.ofReal (ε / (1 - ‖x‖ ^ 2) ^ 2) ≤
        smoothedDensity (μ.withDensity (massWeightDisc μ R)) discRadius x ∧
      smoothedDensity (μ.withDensity (massWeightDisc μ R)) discRadius x ≤
        ENNReal.ofReal (K / (1 - ‖x‖ ^ 2) ^ 2) := sorry

theorem localPot_plane_le {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ M : ℝ, ∀ z : ℂ, localPot (μ.withDensity (massWeight μ R)) (fun _ ↦ R) z ≤ M := sorry

theorem localPot_disc_le {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ M : ℝ, ∀ z ∈ 𝔻, localPot (μ.withDensity (massWeightDisc μ R)) discRadius z ≤ M := sorry

/-- **Lemma 6 (plane)** (paper, p. 370). -/
theorem lemma6_plane {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ (ψ : ℂ → ℝ) (ν₀ : Measure ℂ) (g : ℂ → ℝ≥0∞) (ε K M : ℝ), 0 < ε ∧ Measurable g ∧
      IsSubharmonicWeight univ ψ (ν₀ + volume.withDensity g) ∧
      IsLocallyDoubling (ν₀ + volume.withDensity g) ∧
      (∀ z, |ψ z - φ z| ≤ M) ∧
      (∀ z, ENNReal.ofReal ε ≤ g z ∧ g z ≤ ENNReal.ofReal K) ∧
      ν₀ ≤ μ ∧ μ ≤ (2 : ℝ≥0∞) • ν₀ := sorry

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
      ν₀ ≤ μ ∧ μ ≤ (2 : ℝ≥0∞) • ν₀ := sorry

/-! ### Corollaries in the form consumed by M11 and M12 (reconciliation) -/

/-- Lemma 6 (disc) in the form M11 consumes: `μ' ≥ ε · hypArea` and `|φ − φ'| ≤ B`.  Follows
from `lemma6_disc` (`μ' = ν₀ + volume.withDensity g`, `g ≥ ε/(1-|z|²)²` on `𝔻`; `1 < ·`
implies the hypothesis `1 ≤ ·` of `lemma6_disc`). -/
theorem lemma6_disc_hypArea (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ) (ε B : ℝ), 0 < ε ∧ IsSubharmonicWeight 𝔻 φ' μ' ∧
      IsLocallyDoublingDisc μ' ∧ ENNReal.ofReal ε • hypArea ≤ μ' ∧
      ∀ z ∈ 𝔻, |φ z - φ' z| ≤ B := sorry

/-- Lemma 6 (plane) in the form M12 consumes: `μ' ≥ ε · dm` and `|φ − φ'| ≤ B`.  Follows from
`lemma6_plane`. -/
theorem lemma6_plane_volume (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 < μ (ball z r)) :
    ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ) (ε B : ℝ), 0 < ε ∧ IsSubharmonicWeight univ φ' μ' ∧
      IsLocallyDoubling μ' ∧ ENNReal.ofReal ε • volume ≤ μ' ∧ ∀ z, |φ z - φ' z| ≤ B := sorry

/-- **Lemma 6 (disc), uniform form** (requested for `theorem2_uniform`): the constants `ε`, `B`
and the class `(Cd', R')` of the regularized measure depend only on the class `(Cd, R)` of `μ`,
not on the weight.  (The construction of `lemma6_disc` is uniform: the bounds come from
[Chr91, Lemma 2.3] and doubling at bounded scales, `christ_disc_quant`, `doubling_upTo_disc`.) -/
theorem lemma6_disc_quant (Cd : ℝ≥0) (R : ℝ) (hR : 0 < R) :
    ∃ (ε B : ℝ) (Cd' : ℝ≥0) (R' : ℝ), 0 < ε ∧ 0 ≤ B ∧ 0 < R' ∧
      ∀ (φ : ℂ → ℝ) (μ : Measure ℂ), IsSubharmonicWeight 𝔻 φ μ → MeasClassDisc μ Cd R →
        ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ), IsSubharmonicWeight 𝔻 φ' μ' ∧
          MeasClassDisc μ' Cd' R' ∧ ENNReal.ofReal ε • hypArea ≤ μ' ∧
          ∀ z ∈ 𝔻, |φ z - φ' z| ≤ B := sorry

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
