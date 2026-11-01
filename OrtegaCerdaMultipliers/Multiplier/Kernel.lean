import OrtegaCerdaMultipliers.Multiplier.Basic
import OrtegaCerdaMultipliers.Multiplier.Defs

/-!
# M08 (Multiplier) — Taylor remainders, polynomial form, moment cancellation

See `blueprint/M08_Multiplier.md` §2.2.  Scaffold: statements, proofs `sorry`.

Reconciliation: the disc geometry lemmas of §2.2 (`norm_sub_le_of_hypDist_le`,
`norm_one_sub_conj_mul_comparable`, `convex_closedHypBall`) are in M01
(`Foundations/HyperbolicExtra.lean`); the Forelli–Rudin bound
`integral_one_sub_conj_mul_rpow_neg_three_le` is in M10 (`ModelKernels.lean`).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ### The series remainder -/

theorem norm_pow_sub_pow_le' {a b : ℂ} (hab : ‖b‖ ≤ ‖a‖) (k : ℕ) :
    ‖a ^ k - b ^ k‖ ≤ k * ‖a - b‖ * ‖a‖ ^ (k - 1) := by
  rw [← geom_sum₂_mul, norm_mul]
  have h : ‖∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)‖ ≤ k * ‖a‖ ^ (k - 1) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.range k, ‖a ^ i * b ^ (k - 1 - i)‖
        ≤ ∑ i ∈ Finset.range k, ‖a‖ ^ (k - 1) := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hi' : i ≤ k - 1 := by have := Finset.mem_range.1 hi; omega
          rw [norm_mul, norm_pow, norm_pow]
          calc ‖a‖ ^ i * ‖b‖ ^ (k - 1 - i) ≤ ‖a‖ ^ i * ‖a‖ ^ (k - 1 - i) := by gcongr
            _ = ‖a‖ ^ (k - 1) := by rw [← pow_add]; congr 1; omega
      _ = k * ‖a‖ ^ (k - 1) := by simp
  calc ‖∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)‖ * ‖a - b‖
      ≤ k * ‖a‖ ^ (k - 1) * ‖a - b‖ := by gcongr
    _ = k * ‖a - b‖ * ‖a‖ ^ (k - 1) := by ring

/-- The general series remainder: `log|1 - w₁| - log|1 - w₂|` minus its Taylor polynomial. -/
theorem abs_log_sub_log_add_taylor_le {w₁ w₂ : ℂ} (h1 : ‖w₁‖ ≤ 1 / 2) (h21 : ‖w₂‖ ≤ ‖w₁‖)
    {m : ℕ} (hm : 1 ≤ m) :
    |Real.log ‖1 - w₁‖ - Real.log ‖1 - w₂‖ +
        (∑ k ∈ Finset.Ico 1 m, (w₁ ^ k - w₂ ^ k) / (k : ℂ)).re| ≤
      2 * ‖w₁ - w₂‖ * ‖w₁‖ ^ (m - 1) := by
  have hw1 : ‖w₁‖ < 1 := by linarith
  have hw2 : ‖w₂‖ < 1 := by linarith
  set f : ℕ → ℂ := fun n ↦ (w₁ ^ n - w₂ ^ n) / n with hf
  have hs : HasSum f (log (1 - w₂) - log (1 - w₁)) := by
    have := (hasSum_taylorSeries_neg_log hw1).sub (hasSum_taylorSeries_neg_log hw2)
    convert this using 1
    · ext n; simp [hf, sub_div]
    · ring
  have htail := (hasSum_nat_add_iff' m).2 hs
  -- sum over `range m` equals the sum over `Ico 1 m`
  have hrange : ∑ i ∈ Finset.range m, f i = ∑ k ∈ Finset.Ico 1 m, (w₁ ^ k - w₂ ^ k) / (k : ℂ) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp [hf]
  set r := ‖w₁‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hgeo := (hasSum_geometric_of_lt_one hr0 hw1).mul_left (‖w₁ - w₂‖ * r ^ (m - 1))
  have hbd : ∀ n, ‖f (n + m)‖ ≤ ‖w₁ - w₂‖ * r ^ (m - 1) * r ^ n := by
    intro n
    have hk : (0 : ℝ) < ((n + m : ℕ) : ℝ) := by exact_mod_cast (show 0 < n + m by omega)
    simp only [hf, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hk]
    calc ‖w₁ ^ (n + m) - w₂ ^ (n + m)‖ ≤ ((n + m : ℕ) : ℝ) * ‖w₁ - w₂‖ * r ^ (n + m - 1) :=
          norm_pow_sub_pow_le' h21 _
      _ = ‖w₁ - w₂‖ * r ^ (m - 1) * r ^ n * ((n + m : ℕ) : ℝ) := by
          rw [show n + m - 1 = (m - 1) + n by omega, pow_add]; ring
  have hle := htail.norm_le_of_bounded hgeo hbd
  -- identify the quantity
  have hlog1 : Real.log ‖1 - w₁‖ = (log (1 - w₁)).re := (log_re _).symm
  have hlog2 : Real.log ‖1 - w₂‖ = (log (1 - w₂)).re := (log_re _).symm
  have hq : Real.log ‖1 - w₁‖ - Real.log ‖1 - w₂‖ +
      (∑ k ∈ Finset.Ico 1 m, (w₁ ^ k - w₂ ^ k) / (k : ℂ)).re =
      -(log (1 - w₂) - log (1 - w₁) - ∑ i ∈ Finset.range m, f i).re := by
    rw [hlog1, hlog2, hrange]; simp only [neg_re, sub_re]; ring
  rw [hq, abs_neg]
  refine (abs_re_le_norm _).trans (hle.trans ?_)
  have h1r : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]; linarith
  calc ‖w₁ - w₂‖ * r ^ (m - 1) * (1 - r)⁻¹ ≤ ‖w₁ - w₂‖ * r ^ (m - 1) * 2 := by gcongr
    _ = 2 * ‖w₁ - w₂‖ * r ^ (m - 1) := by ring


theorem abs_kerPlane_sub_taylorPlane_le {m : ℕ} (hm : 1 ≤ m) {z c ζ : ℂ} (hzc : z ≠ c)
    (hζ : 2 * ‖ζ - c‖ ≤ ‖z - c‖) :
    |kerPlane z ζ - taylorPlane m z c ζ| ≤ 2 * (‖ζ - c‖ / ‖z - c‖) ^ m := by
  have hzc' : z - c ≠ 0 := sub_ne_zero.2 hzc
  have hn : 0 < ‖z - c‖ := norm_pos_iff.2 hzc'
  set w := (ζ - c) / (z - c) with hw
  have hwn : ‖w‖ = ‖ζ - c‖ / ‖z - c‖ := by rw [hw, norm_div]
  have hw2 : ‖w‖ ≤ 1 / 2 := by rw [hwn, div_le_iff₀ hn]; linarith
  have h1w : 1 - w ≠ 0 := by
    intro h; have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw2; norm_num at hw2
  have hfac : z - ζ = (z - c) * (1 - w) := by rw [hw]; field_simp; ring
  have hk : kerPlane z ζ = Real.log ‖z - c‖ + Real.log ‖1 - w‖ := by
    rw [kerPlane, hfac, norm_mul, Real.log_mul hn.ne' (norm_ne_zero_iff.2 h1w)]
  have hG := abs_log_sub_log_add_taylor_le (w₂ := 0) hw2 (by simp) hm
  have hsum : ∑ k ∈ Finset.Ico 1 m, (w ^ k - 0 ^ k) / (k : ℂ) =
      ∑ k ∈ Finset.Ico 1 m, w ^ k / (k : ℂ) := by
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [zero_pow (by have := (Finset.mem_Ico.1 hk).1; omega), sub_zero]
  rw [hsum] at hG
  simp only [sub_zero, norm_one, Real.log_one] at hG
  have e : kerPlane z ζ - taylorPlane m z c ζ =
      Real.log ‖1 - w‖ + (∑ k ∈ Finset.Ico 1 m, w ^ k / (k : ℂ)).re := by
    rw [hk, taylorPlane]; ring
  rw [e]
  calc _ ≤ 2 * ‖w‖ * ‖w‖ ^ (m - 1) := hG
    _ = 2 * ‖w‖ ^ m := by
        rw [mul_assoc, ← pow_succ']; congr 2; omega
    _ = 2 * (‖ζ - c‖ / ‖z - c‖) ^ m := by rw [hwn]

theorem abs_kerDisc_sub_taylorDisc_le {m : ℕ} (hm : 1 ≤ m) {z c ζ : ℂ} (hz : z ∈ 𝔻)
    (hc : c ∈ 𝔻) (hzc : z ≠ c) (hζ : 2 * ‖ζ - c‖ ≤ ‖z - c‖) :
    |kerDisc z ζ - taylorDisc m z c ζ| ≤
      2 * (1 - ‖z‖ ^ 2) * ‖ζ - c‖ ^ m / (‖z - c‖ ^ m * ‖1 - conj z * c‖) := by
  have hzc' : z - c ≠ 0 := sub_ne_zero.2 hzc
  have hn : 0 < ‖z - c‖ := norm_pos_iff.2 hzc'
  have hD : 0 < ‖1 - conj z * c‖ := norm_one_sub_conj_mul_pos hz hc
  have hD' : 1 - conj z * c ≠ 0 := norm_pos_iff.1 hD
  have hz1 : ‖z‖ < 1 := norm_lt_one_of_mem_disc hz
  have hzD : ‖z - c‖ ≤ ‖1 - conj z * c‖ := by
    have := norm_one_sub_conj_mul_sq_sub z c
    have h0 : 0 ≤ (1 - ‖z‖ ^ 2) * (1 - ‖c‖ ^ 2) :=
      mul_nonneg (one_sub_normSq_pos hz).le (one_sub_normSq_pos hc).le
    nlinarith [norm_nonneg (z - c), norm_nonneg (1 - conj z * c)]
  set w₁ := (ζ - c) / (z - c) with hw₁
  set w₂ := conj z * (ζ - c) / (1 - conj z * c) with hw₂
  have hw₁n : ‖w₁‖ = ‖ζ - c‖ / ‖z - c‖ := by rw [hw₁, norm_div]
  have hw₁2 : ‖w₁‖ ≤ 1 / 2 := by rw [hw₁n, div_le_iff₀ hn]; linarith
  have hw21 : ‖w₂‖ ≤ ‖w₁‖ := by
    rw [hw₂, hw₁n, norm_div, norm_mul, Complex.norm_conj]
    calc ‖z‖ * ‖ζ - c‖ / ‖1 - conj z * c‖ ≤ 1 * ‖ζ - c‖ / ‖z - c‖ := by
          gcongr
      _ = ‖ζ - c‖ / ‖z - c‖ := by ring
  have hne : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → 1 - w ≠ 0 := by
    intro w hw h; have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw; norm_num at hw
  have h1w₁ := hne w₁ hw₁2
  have h1w₂ := hne w₂ (hw21.trans hw₁2)
  have hfac1 : ζ - z = -((z - c) * (1 - w₁)) := by rw [hw₁]; field_simp; ring
  have hfac2 : 1 - conj ζ * z = conj ((1 - conj z * c) * (1 - w₂)) := by
    rw [hw₂]; field_simp; simp [map_sub, map_mul]; ring
  have hk : kerDisc z ζ = Real.log ‖z - c‖ + Real.log ‖1 - w₁‖ -
      (Real.log ‖1 - conj z * c‖ + Real.log ‖1 - w₂‖) := by
    rw [kerDisc, pseudoHyp, hfac1, hfac2, norm_neg, Complex.norm_conj, norm_mul, norm_mul,
      Real.log_div (mul_ne_zero hn.ne' (norm_ne_zero_iff.2 h1w₁))
        (mul_ne_zero hD.ne' (norm_ne_zero_iff.2 h1w₂)),
      Real.log_mul hn.ne' (norm_ne_zero_iff.2 h1w₁), Real.log_mul hD.ne' (norm_ne_zero_iff.2 h1w₂)]
  have hpc : Real.log (pseudoHyp c z) = Real.log ‖z - c‖ - Real.log ‖1 - conj z * c‖ := by
    have e1 : ‖c - z‖ = ‖z - c‖ := norm_sub_rev _ _
    have e2 : ‖1 - conj c * z‖ = ‖1 - conj z * c‖ := by
      rw [← Complex.norm_conj (1 - conj c * z)]; simp [map_sub, mul_comm]
    rw [pseudoHyp, e1, e2, Real.log_div hn.ne' hD.ne']
  have e : kerDisc z ζ - taylorDisc m z c ζ = Real.log ‖1 - w₁‖ - Real.log ‖1 - w₂‖ +
      (∑ k ∈ Finset.Ico 1 m, (w₁ ^ k - w₂ ^ k) / (k : ℂ)).re := by
    rw [hk, taylorDisc, hpc]; ring
  have hdiff : ‖w₁ - w₂‖ = (1 - ‖z‖ ^ 2) * ‖ζ - c‖ / (‖z - c‖ * ‖1 - conj z * c‖) := by
    have hzz : conj z * z = (‖z‖ : ℂ) ^ 2 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have : w₁ - w₂ = (ζ - c) * ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) / ((z - c) * (1 - conj z * c)) := by
      rw [hw₁, hw₂, div_sub_div _ _ hzc' hD']
      congr 1
      push_cast
      linear_combination (-(ζ - c)) * hzz
    rw [this, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (one_sub_normSq_pos hz)]
    ring
  rw [e]
  refine (abs_log_sub_log_add_taylor_le hw₁2 hw21 hm).trans (le_of_eq ?_)
  rw [hdiff, hw₁n, div_pow]
  have hm' : m = (m - 1) + 1 := by omega
  conv_rhs => rw [hm', pow_succ, pow_succ]
  field_simp
  ring

/-- First-order remainder along a segment (disc far field, no convergent series needed). -/
theorem abs_kerDisc_sub_taylorDisc_two_le {z c ζ : ℂ} (hz : z ∈ 𝔻) {Bd : ℝ}
    (hseg : ∀ ξ ∈ segment ℝ c ζ, ξ ∈ 𝔻 ∧ ξ ≠ z)
    (hB : ∀ ξ ∈ segment ℝ c ζ, 2 * (1 - ‖z‖ ^ 2) / (‖z - ξ‖ ^ 2 * ‖1 - conj z * ξ‖) ≤ Bd) :
    |kerDisc z ζ - taylorDisc 2 z c ζ| ≤ Bd * ‖ζ - c‖ ^ 2 := sorry

theorem natDegree_C_mul_X_sub_C_pow_le (a c : ℂ) (k : ℕ) :
    ((Polynomial.C a * (Polynomial.X - Polynomial.C c)) ^ k).natDegree ≤ k := by
  refine Polynomial.natDegree_pow_le.trans ?_
  have : (Polynomial.C a * (Polynomial.X - Polynomial.C c)).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_sub_C_le _)
  nlinarith

theorem exists_poly_taylorPlane {m : ℕ} (hm : 1 ≤ m) (z c : ℂ) :
    ∃ p : Polynomial ℂ, p.natDegree < m ∧ ∀ ζ, taylorPlane m z c ζ = (p.eval ζ).re := by
  open Polynomial in
  refine ⟨C (Real.log ‖z - c‖ : ℂ) - ∑ k ∈ Finset.Ico 1 m,
      C (1 / (k : ℂ)) * (C (z - c)⁻¹ * (X - C c)) ^ k, ?_, fun ζ ↦ ?_⟩
  · have : (C (Real.log ‖z - c‖ : ℂ) - ∑ k ∈ Finset.Ico 1 m,
        C (1 / (k : ℂ)) * (C (z - c)⁻¹ * (X - C c)) ^ k).natDegree ≤ m - 1 := by
      refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
      refine (natDegree_C_mul_le _ _).trans ((natDegree_C_mul_X_sub_C_pow_le _ _ _).trans ?_)
      have := (Finset.mem_Ico.1 hk).2; omega
    omega
  · simp only [taylorPlane, eval_sub, eval_C, eval_finset_sum, eval_mul, eval_pow, eval_X,
      sub_re, ofReal_re]
    congr 2
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [div_eq_mul_inv]
    ring

theorem exists_poly_taylorDisc {m : ℕ} (hm : 1 ≤ m) (z c : ℂ) :
    ∃ p : Polynomial ℂ, p.natDegree < m ∧ ∀ ζ, taylorDisc m z c ζ = (p.eval ζ).re := by
  open Polynomial in
  refine ⟨C (Real.log (pseudoHyp c z) : ℂ) - ∑ k ∈ Finset.Ico 1 m,
      C (1 / (k : ℂ)) * ((C (z - c)⁻¹ * (X - C c)) ^ k -
        (C (conj z / (1 - conj z * c)) * (X - C c)) ^ k), ?_, fun ζ ↦ ?_⟩
  · have : (C (Real.log (pseudoHyp c z) : ℂ) - ∑ k ∈ Finset.Ico 1 m,
        C (1 / (k : ℂ)) * ((C (z - c)⁻¹ * (X - C c)) ^ k -
          (C (conj z / (1 - conj z * c)) * (X - C c)) ^ k)).natDegree ≤ m - 1 := by
      refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
      refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans
        (max_le ((natDegree_C_mul_X_sub_C_pow_le _ _ _).trans ?_)
          ((natDegree_C_mul_X_sub_C_pow_le _ _ _).trans ?_))) <;>
      · have := (Finset.mem_Ico.1 hk).2; omega
    omega
  · simp only [taylorDisc, eval_sub, eval_C, eval_finset_sum, eval_mul, eval_pow, eval_X,
      sub_re, ofReal_re]
    congr 2
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [div_eq_mul_inv]
    ring

/-- Moment cancellation. -/
theorem cellPot_eq_sub_poly {ν : Measure ℂ} {R : ℕ → Set ℂ} {Λ : ℕ → Multiset ℂ} {i m : ℕ}
    (hR : MeasurableSet (R i)) (hfin : ν (R i) < ∞) (hb : Bornology.IsBounded (R i))
    (hmom : ∀ j < m, ∫ ζ in R i, ζ ^ j ∂ν = ((Λ i).map (· ^ j)).sum)
    {k : ℂ → ℂ → ℝ} {z : ℂ} (hint : IntegrableOn (k z) (R i) ν)
    {T : ℂ → ℝ} {p : Polynomial ℂ} (hp : p.natDegree < m) (hT : ∀ ζ, T ζ = (p.eval ζ).re) :
    cellPot k ν R Λ i z =
      ((Λ i).map fun w ↦ k z w - T w).sum - ∫ ζ in R i, (k z ζ - T ζ) ∂ν := by
  obtain ⟨r, hr⟩ := hb.subset_closedBall 0
  -- integrability of polynomials on the cell
  have hpoly : ∀ q : Polynomial ℂ, IntegrableOn (fun ζ ↦ q.eval ζ) (R i) ν := by
    intro q
    obtain ⟨Cq, hCq⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
      (q.continuous.continuousOn)
    refine IntegrableOn.of_bound hfin q.continuous.aestronglyMeasurable.restrict Cq ?_
    exact (ae_restrict_iff' hR).2 (Filter.Eventually.of_forall fun ζ hζ ↦ hCq ζ (hr hζ))
  have hTint : IntegrableOn T (R i) ν := by
    have : T = fun ζ ↦ (p.eval ζ).re := funext hT
    rw [this]; exact (hpoly p).re
  -- moments
  have hmomp : ∫ ζ in R i, p.eval ζ ∂ν = ((Λ i).map fun w ↦ p.eval w).sum := by
    have hev : ∀ ζ, p.eval ζ = ∑ j ∈ Finset.range m, p.coeff j * ζ ^ j :=
      fun ζ ↦ Polynomial.eval_eq_sum_range' hp ζ
    simp_rw [hev]
    rw [integral_finsetSum _ fun j _ ↦ (hpoly (Polynomial.X ^ j)).congr
      (Filter.Eventually.of_forall fun ζ ↦ by simp) |>.const_mul (p.coeff j)]
    simp_rw [integral_const_mul]
    have hswap : ∀ (L : Multiset ℂ) (f : ℕ → ℂ → ℂ),
        ∑ j ∈ Finset.range m, (L.map (f j)).sum =
          (L.map fun w ↦ ∑ j ∈ Finset.range m, f j w).sum := by
      intro L f
      induction L using Multiset.induction_on with
      | empty => simp
      | cons a t ih => simp [Multiset.map_cons, Multiset.sum_cons, Finset.sum_add_distrib, ih]
    rw [← hswap]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [hmom j (Finset.mem_range.1 hj), Multiset.sum_map_mul_left]
  have hTsum : ((Λ i).map T).sum = ∫ ζ in R i, T ζ ∂ν := by
    simp_rw [hT]
    rw [show (∫ x in R i, (p.eval x).re ∂ν) = (∫ x in R i, p.eval x ∂ν).re from
      integral_re (hpoly p), hmomp]
    induction (Λ i) using Multiset.induction_on with
    | empty => simp
    | cons a t ih => simp [Multiset.map_cons, Multiset.sum_cons, ih]
  rw [cellPot, integral_sub hint hTint, Multiset.sum_map_sub, hTsum]
  ring

end OC
