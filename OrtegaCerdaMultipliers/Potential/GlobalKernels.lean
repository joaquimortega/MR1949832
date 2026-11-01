import OrtegaCerdaMultipliers.Potential.Fundamental

/-!
# M02 (Potentials) Appendix A — The paper's global kernels (documentation; not used)

See `blueprint/M02_Potentials.md`, Appendix A.  Scaffold: statements, proofs `sorry`.  These
kernels are not used by the formal proof of Lemma 6 (which uses local potentials, §4); they
document the paper's construction (p. 371) and its sign error in the plane.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Plane kernel of Lemma 6, sign of the quadratic term corrected. -/
def kPlane (z ζ : ℂ) : ℝ :=
  (4 * Real.pi)⁻¹ * Real.log (‖z - ζ‖ ^ 2) -
    (2 * Real.pi)⁻¹ * (if 1 ≤ ‖ζ‖ then
      Real.log ‖ζ‖ - (z / ζ).re - (z ^ 2 / (2 * ζ ^ 2)).re else 0)

/-- Disc kernel of Lemma 6. -/
def kDisc (z ζ : ℂ) : ℝ :=
  (4 * Real.pi)⁻¹ * (Real.log (pseudoHyp ζ z ^ 2) +
    (1 - ‖ζ‖ ^ 2) * (1 / (1 - conj z * ζ) + 1 / (1 - z * conj ζ) - 1).re)

theorem kDisc_eq {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    kDisc z ζ = (4 * Real.pi)⁻¹ * (Real.log (pseudoHyp ζ z ^ 2) + (1 - pseudoHyp ζ z ^ 2) +
      ‖z‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2 / ‖1 - conj ζ * z‖ ^ 2) := sorry

/-- **Andersson–Pascuas estimate** with explicit constant `4/π`. -/
theorem abs_kDisc_le {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) (hne : z ≠ ζ) :
    |kDisc z ζ| ≤ 4 / Real.pi * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) ^ 2 *
      (1 + Real.log (1 / pseudoHyp ζ z)) := sorry

/-- Sharp tail of the logarithmic series: `|log(1 − w) + w + w²/2| ≤ |w|³ / (3 (1 − |w|))`. -/
theorem norm_log_one_sub_add_le {w : ℂ} (hw : ‖w‖ < 1) :
    ‖Complex.log (1 - w) + w + w ^ 2 / 2‖ ≤ ‖w‖ ^ 3 / (3 * (1 - ‖w‖)) := by
  have h := Complex.hasSum_taylorSeries_neg_log hw
  have h3 := (hasSum_nat_add_iff' 3).2 h
  have hsum : ∑ i ∈ Finset.range 3, w ^ i / (i : ℂ) = w + w ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  rw [hsum] at h3
  have hw0 := norm_nonneg w
  have hg : HasSum (fun n : ℕ ↦ ‖w‖ ^ 3 / 3 * ‖w‖ ^ n) (‖w‖ ^ 3 / 3 * (1 - ‖w‖)⁻¹) :=
    (hasSum_geometric_of_lt_one hw0 hw).mul_left _
  have hle := h3.norm_le_of_bounded hg fun n ↦ by
    rw [norm_div, norm_pow]
    have hn : ‖((n + 3 : ℕ) : ℂ)‖ = (n : ℝ) + 3 := by
      rw [Complex.norm_natCast]; push_cast; ring
    rw [hn, div_le_iff₀ (by positivity), pow_add]
    have : (0 : ℝ) ≤ ‖w‖ ^ n * ‖w‖ ^ 3 := by positivity
    nlinarith [show (0 : ℝ) ≤ n from n.cast_nonneg]
  have e : Complex.log (1 - w) + w + w ^ 2 / 2 = -(-Complex.log (1 - w) - (w + w ^ 2 / 2)) := by
    ring
  rw [e, norm_neg]
  refine hle.trans (le_of_eq ?_)
  field_simp

theorem abs_kPlane_le {z ζ : ℂ} (hζ : 1 ≤ ‖ζ‖) (hzζ : 2 * ‖z‖ ≤ ‖ζ‖) :
    |kPlane z ζ| ≤ (3 * Real.pi)⁻¹ * (‖z‖ / ‖ζ‖) ^ 3 := by
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ; linarith
  have hζn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ0
  set w := z / ζ with hw
  have hwn : ‖w‖ = ‖z‖ / ‖ζ‖ := norm_div z ζ
  have hw2 : ‖w‖ ≤ 1 / 2 := by
    rw [hwn, div_le_iff₀ hζn]; linarith
  have hw1 : ‖w‖ < 1 := by linarith
  have h1w : (1 - w) ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw1
    exact lt_irrefl _ hw1
  have hzζe : z - ζ = -ζ * (1 - w) := by
    rw [hw]; field_simp; ring
  have hnorm : ‖z - ζ‖ = ‖ζ‖ * ‖1 - w‖ := by rw [hzζe, norm_mul, norm_neg]
  have hk : kPlane z ζ = (2 * Real.pi)⁻¹ * (Complex.log (1 - w) + w + w ^ 2 / 2).re := by
    unfold kPlane
    rw [ite_eq_left_iff.2 (fun h ↦ absurd hζ h), hnorm, mul_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow]
    have e2 : z ^ 2 / (2 * ζ ^ 2) = w ^ 2 / 2 := by rw [hw]; field_simp
    rw [e2, ← hw]
    simp only [Complex.add_re, Complex.log_re]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [hk, abs_mul, abs_of_pos (by positivity), ← hwn]
  have hre := Complex.abs_re_le_norm (Complex.log (1 - w) + w + w ^ 2 / 2)
  have htail := norm_log_one_sub_add_le hw1
  have h3 : ‖w‖ ^ 3 / (3 * (1 - ‖w‖)) ≤ 2 / 3 * ‖w‖ ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ ‖w‖ ^ 3 := by positivity
    nlinarith
  calc (2 * Real.pi)⁻¹ * |(Complex.log (1 - w) + w + w ^ 2 / 2).re|
      ≤ (2 * Real.pi)⁻¹ * (2 / 3 * ‖w‖ ^ 3) := by
        gcongr
        exact hre.trans (htail.trans h3)
    _ = (3 * Real.pi)⁻¹ * ‖w‖ ^ 3 := by
        have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp

end OC
