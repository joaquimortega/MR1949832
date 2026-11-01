import OrtegaCerdaMultipliers.Defs

/-!
# M06 — Lemma 5: moment-matching points (relaxed form)

J. Ortega-Cerdà, *Multipliers and weighted ∂̄-estimates*, Rev. Mat. Iberoam. 18 (2002), Lemma 5
(pp. 365–366).  Blueprint: `blueprint/M06_Quadrature.md`.

Given a measure `μ` of mass `N = m k` carried by `B̄(c, r)`, we produce `N` points `Λ` in
`B̄(c, 2 m r)` and `N` points `K` in the annulus `B r ≤ |w - c| ≤ (B + 4m) r`, both with the
moments of `μ` of order `< m`.  The paper uses Chebyshev quadrature with nodes *inside* `R`; that
claim is false for general measures (see the blueprint, §0), and the relaxed form suffices.

**Construction (purely algebraic).**
1. `q_t = (1/k) ∫ (z - c)^t dμ`, so `‖q_t‖ ≤ m r^t`.
2. `newtonE q`: the sequence `e_n` defined by Newton's recursion
   `n e_n = (-1)^(n+1) ∑_{i<n} (-1)^i e_i q_(n-i)`; then `‖e_n‖ ≤ (m r)^n`.
3. `Z` = roots of `X^m + ∑_{i<m} (-1)^(m-i) e_(m-i) X^i` (splits over `ℂ`); Vieta gives
   `esymm Z = e`, and Mathlib's Newton identities give power sums `p_t(Z) = q_t`, `1 ≤ t ≤ m`.
4. Fujiwara-type bound: all roots satisfy `|z| ≤ 2 m r`.
5. `Λ = k • (c + Z)`; `K = {c + z + τ ζ^l : z ∈ Z, l < k}` with `ζ = e^{2πi/k}`, `k ≥ m`.
-/
open Finset Polynomial MeasureTheory Metric
namespace OC

noncomputable def newtonE (q : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => (-1) ^ n / (n + 1) * ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) * newtonE q i * q (n + 1 - i)

/-- The `j`-th power sum `∑_{z ∈ Z} z^j` of a multiset `Z` (with multiplicity). -/
def msPsum (Z : Multiset ℂ) (j : ℕ) : ℂ := (Z.map (· ^ j)).sum

lemma newtonE_zero (q : ℕ → ℂ) : newtonE q 0 = 1 := by rw [newtonE]

lemma newtonE_rec (q : ℕ → ℂ) (n : ℕ) :
    (n : ℂ) * newtonE q n =
      (-1) ^ (n + 1) * ∑ i ∈ range n, (-1) ^ i * newtonE q i * q (n - i) := by
  rcases n with _ | k
  · simp
  · rw [newtonE, ← Fin.sum_univ_eq_sum_range (fun i => (-1) ^ i * newtonE q i * q (k + 1 - i))]
    have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    push_cast at hk ⊢
    field_simp
    ring

lemma sum_antidiagonal_filter_lt (k : ℕ) (f : ℕ → ℕ → ℂ) :
    ∑ a ∈ antidiagonal k with a.1 < k, f a.1 a.2 = ∑ i ∈ range k, f i (k - i) := by
  rw [Finset.sum_filter,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if i < k then f i j else 0),
    Finset.sum_range_succ]
  simp only [lt_irrefl, ite_false, add_zero]
  exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.mp hi)

/-- Newton's identities for a multiset of complex numbers. -/
lemma multiset_newton (Z : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * Z.esymm k =
      (-1) ^ (k + 1) * ∑ i ∈ range k, (-1) ^ i * Z.esymm i * msPsum Z (k - i) := by
  classical
  set x : Fin Z.toList.length → ℂ := Z.toList.get with hxdef
  have hx : (univ.val.map x) = Z := by
    rw [Fin.univ_val_map, hxdef, List.ofFn_get, Multiset.coe_toList]
  have h := congrArg (MvPolynomial.aeval (R := ℂ) x)
    (MvPolynomial.mul_esymm_eq_sum (Fin Z.toList.length) ℂ k)
  have hp : ∀ j, MvPolynomial.aeval x (MvPolynomial.psum (Fin Z.toList.length) ℂ j) =
      msPsum Z j := by
    intro j
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X, msPsum]
    conv_rhs => rw [← hx, Multiset.map_map]
    rfl
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, hx, hp] at h
  rw [h, sum_antidiagonal_filter_lt k (fun i j => (-1) ^ i * Z.esymm i * msPsum Z j)]


/-- If the elementary symmetric functions of `Z` agree with `newtonE q` up to order `m`, then the
power sums of `Z` are `q j` for `1 ≤ j ≤ m`. -/
lemma msPsum_eq_of_esymm_eq (Z : Multiset ℂ) (q : ℕ → ℂ) (m : ℕ)
    (he : ∀ n ≤ m, Z.esymm n = newtonE q n) : ∀ j, 1 ≤ j → j ≤ m → msPsum Z j = q j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h1 hjm
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hZ := multiset_newton Z (j' + 1)
    have hE := newtonE_rec q (j' + 1)
    rw [he _ hjm] at hZ
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [he i (by have := Finset.mem_range.mp hi; omega)])] at hZ
    have hsum := mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) (hZ.symm.trans hE)
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hsum
    have hrest : ∑ i ∈ range j', (-1) ^ (i + 1) * newtonE q (i + 1) * msPsum Z (j' + 1 - (i + 1))
        = ∑ i ∈ range j', (-1) ^ (i + 1) * newtonE q (i + 1) * q (j' + 1 - (i + 1)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [ih (j' + 1 - (i + 1)) (by omega) (by omega) (by omega)]
    rw [hrest, add_left_cancel_iff] at hsum
    simpa [newtonE_zero] using hsum

/-- The monic polynomial `X^m + ∑_{i<m} (-1)^(m-i) e_(m-i) X^i` splits over `ℂ`; its roots `Z` have
elementary symmetric functions `e`. -/
lemma exists_multiset_esymm (e : ℕ → ℂ) (he0 : e 0 = 1) (m : ℕ) :
    ∃ Z : Multiset ℂ, Multiset.card Z = m ∧ (∀ n ≤ m, Z.esymm n = e n) ∧
      ∀ z ∈ Z, z ^ m + ∑ i : Fin m, (-1) ^ (m - (i : ℕ)) * e (m - i) * z ^ (i : ℕ) = 0 := by
  set c : Fin m → ℂ := fun i => (-1) ^ (m - (i : ℕ)) * e (m - i) with hc
  set Q : ℂ[X] := X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ) with hQ
  have hdeg : degree (∑ i : Fin m, C (c i) * X ^ (i : ℕ)) < m := degree_sum_fin_lt c
  have hmon : Q.Monic := monic_X_pow_add hdeg
  have hnat : Q.natDegree = m := by
    rw [hQ, natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hQ0 : Q ≠ 0 := hmon.ne_zero
  have hcard : Multiset.card Q.roots = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hcoeff : ∀ k (hk : k < m), Q.coeff k = c ⟨k, hk⟩ := by
    intro k hk
    simp only [hQ, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow,
      ite_eq_right (Nat.ne_of_lt hk), zero_add]
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro b _ hb
      exact ite_eq_right fun h => hb (Fin.ext h.symm)
    · simp
  refine ⟨Q.roots, hcard.trans hnat, ?_, ?_⟩
  · intro n hn
    have hV := coeff_eq_esymm_roots_of_card hcard (k := m - n) (by omega)
    rw [hnat, hmon.leadingCoeff, one_mul, Nat.sub_sub_self hn] at hV
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp [he0]
    · rw [hcoeff (m - n) (by omega)] at hV
      simp only [hc, Nat.sub_sub_self hn] at hV
      exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) hV).symm
  · intro z hz
    have := (mem_roots hQ0).mp hz
    simpa [hQ, eval_finsetSum, hc, mul_assoc] using this


/-- Coefficient bound: if `‖q j‖ ≤ m r^j` then `‖e_n‖ ≤ (m r)^n`. -/
lemma norm_newtonE_le (q : ℕ → ℂ) (m : ℕ) (hm : 1 ≤ m) (r : ℝ) (hr : 0 ≤ r)
    (hq : ∀ j, ‖q j‖ ≤ m * r ^ j) : ∀ n, ‖newtonE q n‖ ≤ ((m : ℝ) * r) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | k
    · simp [newtonE_zero]
    · have hterm : ∀ i : Fin (k + 1),
          ‖(-1 : ℂ) ^ (i : ℕ) * newtonE q i * q (k + 1 - i)‖ ≤ ((m : ℝ) * r) ^ (k + 1) := by
        intro i
        have hi := i.isLt
        rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        calc ‖newtonE q i‖ * ‖q (k + 1 - i)‖
            ≤ ((m : ℝ) * r) ^ (i : ℕ) * (m * r ^ (k + 1 - i)) :=
              mul_le_mul (ih i hi) (hq _) (norm_nonneg _) (by positivity)
          _ = (m : ℝ) ^ ((i : ℕ) + 1) * r ^ (k + 1) := by
              have hr' : r ^ (i : ℕ) * r ^ (k + 1 - i) = r ^ (k + 1) := by
                rw [← pow_add, Nat.add_sub_cancel' hi.le]
              rw [mul_pow, pow_succ, ← hr']
              ring
          _ ≤ (m : ℝ) ^ (k + 1) * r ^ (k + 1) := by
              gcongr
              · exact_mod_cast hm
              · omega
          _ = ((m : ℝ) * r) ^ (k + 1) := (mul_pow _ _ _).symm
      rw [newtonE, norm_mul]
      have hk : ‖(-1 : ℂ) ^ k / ((k : ℂ) + 1)‖ = 1 / ((k : ℝ) + 1) := by
        rw [norm_div, norm_pow, norm_neg, norm_one, one_pow]
        congr 1
        exact_mod_cast Complex.norm_natCast (k + 1)
      rw [hk]
      calc 1 / ((k : ℝ) + 1) * ‖∑ i : Fin (k + 1), (-1 : ℂ) ^ (i : ℕ) * newtonE q i * q (k + 1 - i)‖
          ≤ 1 / ((k : ℝ) + 1) * ∑ _i : Fin (k + 1), ((m : ℝ) * r) ^ (k + 1) := by
            gcongr
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
        _ = ((m : ℝ) * r) ^ (k + 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            field_simp

/-- Fujiwara-type root bound: if `z^m + ∑_{i<m} c_i z^i = 0` and `‖c_i‖ ≤ B^(m-i)`, then
`‖z‖ ≤ 2B`. -/
lemma norm_le_of_root (m : ℕ) (B : ℝ) (hB : 0 ≤ B) (c : Fin m → ℂ)
    (hc : ∀ i : Fin m, ‖c i‖ ≤ B ^ (m - (i : ℕ))) (z : ℂ)
    (hz : z ^ m + ∑ i : Fin m, c i * z ^ (i : ℕ) = 0) : ‖z‖ ≤ 2 * B := by
  by_contra h
  replace h := lt_of_not_ge h
  set t := ‖z‖ with ht_def
  have ht : 0 < t := by linarith
  have h1 : t ^ m ≤ ∑ i : Fin m, B ^ (m - (i : ℕ)) * t ^ (i : ℕ) := by
    have hzm : z ^ m = -∑ i : Fin m, c i * z ^ (i : ℕ) := eq_neg_of_add_eq_zero_left hz
    calc t ^ m = ‖z ^ m‖ := by rw [norm_pow]
      _ = ‖∑ i : Fin m, c i * z ^ (i : ℕ)‖ := by rw [hzm, norm_neg]
      _ ≤ ∑ i : Fin m, ‖c i * z ^ (i : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin m, B ^ (m - (i : ℕ)) * t ^ (i : ℕ) := by
          gcongr with i
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_right (hc i) (by positivity)
  have h2 : ∑ i : Fin m, B ^ (m - (i : ℕ)) * t ^ (i : ℕ)
      ≤ t ^ m * ∑ i : Fin m, (1 / 2 : ℝ) ^ (m - (i : ℕ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hi := i.isLt
    calc B ^ (m - (i : ℕ)) * t ^ (i : ℕ) ≤ (t / 2) ^ (m - (i : ℕ)) * t ^ (i : ℕ) := by
          gcongr; linarith
      _ = t ^ m * (1 / 2) ^ (m - (i : ℕ)) := by
          rw [div_eq_mul_one_div t 2, mul_pow, mul_comm (t ^ (m - (i : ℕ))), mul_assoc,
            ← pow_add, Nat.sub_add_cancel hi.le, mul_comm]
  have h3 : ∑ i : Fin m, (1 / 2 : ℝ) ^ (m - (i : ℕ)) < 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (1 / 2 : ℝ) ^ (m - i)) m,
      ← Finset.sum_range_reflect]
    have : ∀ j ∈ range m, (1 / 2 : ℝ) ^ (m - (m - 1 - j)) = 1 / 2 * (1 / 2) ^ j := by
      intro j hj
      have := Finset.mem_range.mp hj
      rw [show m - (m - 1 - j) = j + 1 by omega, pow_succ, mul_comm]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, geom_sum_eq (by norm_num)]
    have h0 : (0 : ℝ) < (1 / 2) ^ m := by positivity
    have hg : ((1 / 2 : ℝ) ^ m - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2) ^ m) := by
      rw [div_eq_iff (by norm_num)]; ring
    rw [hg]
    linarith
  have := h1.trans h2
  have htm : 0 < t ^ m := by positivity
  nlinarith

/-- **Key lemma (a)+(b).** Prescribed power sums with a root bound: given `q` with
`‖q j‖ ≤ m r^j`, there are `m` points (with multiplicity) whose `j`-th power sums are `q j` for
`1 ≤ j ≤ m`, all in the closed disc of radius `2 m r`. -/
theorem exists_multiset_psum (m : ℕ) (q : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hq : ∀ j, ‖q j‖ ≤ m * r ^ j) :
    ∃ Z : Multiset ℂ, Multiset.card Z = m ∧ (∀ j, 1 ≤ j → j ≤ m → msPsum Z j = q j) ∧
      ∀ z ∈ Z, ‖z‖ ≤ 2 * m * r := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, rfl, fun j h1 h2 => by omega, fun z hz => by simp at hz⟩
  obtain ⟨Z, hcard, hes, hroot⟩ := exists_multiset_esymm (newtonE q) (newtonE_zero q) m
  refine ⟨Z, hcard, msPsum_eq_of_esymm_eq Z q m hes, fun z hz => ?_⟩
  have := norm_le_of_root m ((m : ℝ) * r) (by positivity)
    (fun i => (-1) ^ (m - (i : ℕ)) * newtonE q (m - i)) (fun i => by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact norm_newtonE_le q m hm r hr hq _) z (hroot z hz)
  linarith

/-! ## Moments of measures -/

lemma integrable_pow_sub {μ : Measure ℂ} [IsFiniteMeasure μ] {c : ℂ} {r : ℝ}
    (hsupp : μ (closedBall c r)ᶜ = 0) (t : ℕ) : Integrable (fun z => (z - c) ^ t) μ := by
  refine Integrable.of_bound ((continuous_id.sub continuous_const).pow t).aestronglyMeasurable
    (r ^ t) ?_
  filter_upwards [mem_ae_iff.mpr hsupp] with z hz
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_iff_norm.mp hz) t

lemma norm_integral_pow_sub_le {μ : Measure ℂ} [IsFiniteMeasure μ] {c : ℂ} {r : ℝ}
    (hsupp : μ (closedBall c r)ᶜ = 0) (t : ℕ) :
    ‖∫ z, (z - c) ^ t ∂μ‖ ≤ r ^ t * μ.real Set.univ := by
  refine norm_integral_le_of_norm_le_const ?_
  filter_upwards [mem_ae_iff.mpr hsupp] with z hz
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_iff_norm.mp hz) t

lemma finset_sum_multiset_sum_comm (Λ : Multiset ℂ) (s : Finset ℕ) (f : ℕ → ℂ → ℂ) :
    ∑ i ∈ s, (Λ.map (f i)).sum = (Λ.map fun w => ∑ i ∈ s, f i w).sum := by
  induction Λ using Multiset.induction_on with
  | empty => simp
  | cons a t ih => simp [Multiset.map_cons, Multiset.sum_cons, Finset.sum_add_distrib, ih]

/-- Matching the centred moments of order `< m` gives exactness on polynomials of degree `< m`. -/
lemma integral_eval_eq_of_moments {μ : Measure ℂ} [IsFiniteMeasure μ] {c : ℂ} {r : ℝ}
    (hsupp : μ (closedBall c r)ᶜ = 0) (Λ : Multiset ℂ) (m : ℕ)
    (h : ∀ t < m, ∫ z, (z - c) ^ t ∂μ = (Λ.map fun w => (w - c) ^ t).sum)
    (p : ℂ[X]) (hp : p.natDegree < m) :
    ∫ z, p.eval z ∂μ = (Λ.map fun w => p.eval w).sum := by
  set p' := p.comp (X + C c) with hp'def
  have hp' : p'.natDegree < m := by
    rw [hp'def, natDegree_comp, natDegree_X_add_C, mul_one]; exact hp
  have hev : ∀ z, p.eval z = ∑ i ∈ range m, p'.coeff i * (z - c) ^ i := fun z => by
    rw [← eval_eq_sum_range' hp' (z - c)]; simp [hp'def, eval_comp]
  simp_rw [hev]
  rw [integral_finsetSum _ (fun i _ => (integrable_pow_sub hsupp i).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])]
  simp_rw [← Multiset.sum_map_mul_left]
  exact finset_sum_multiset_sum_comm Λ (range m) _

/-- Roots-of-unity identity: `∑_{l<k} (z + τ ζ^l)^t = k z^t` for `t < k`, `ζ` a primitive `k`-th
root of unity. -/
lemma sum_shift_rootsOfUnity_pow {k : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k) (z τ : ℂ) {t : ℕ}
    (ht : t < k) : ∑ l ∈ range k, (z + τ * ζ ^ l) ^ t = k * z ^ t := by
  have hgeom : ∀ s < t, ∑ l ∈ range k, (ζ ^ (t - s)) ^ l = 0 := by
    intro s hs
    have hne : ζ ^ (t - s) ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
      zero_div]
  simp_rw [add_pow]
  rw [Finset.sum_comm, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · simp
  · intro s hs
    have hs' := Finset.mem_range.mp hs
    calc ∑ l ∈ range k, z ^ s * (τ * ζ ^ l) ^ (t - s) * (t.choose s : ℂ)
        = z ^ s * τ ^ (t - s) * (t.choose s : ℂ) * ∑ l ∈ range k, (ζ ^ (t - s)) ^ l := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm l]
          ring
      _ = 0 := by rw [hgeom s hs', mul_zero]

/-- **Lemma 5 (relaxed form).** Let `μ` be a measure carried by the closed disc `B̄(c, r)` with
total mass `N = m k`, where `1 ≤ m ≤ k`, and let `B ≥ 0`.  There are two multisets `Λ` and `K` of
`N` points each such that
* `Λ ⊆ B̄(c, 2 m r)`;
* `K ⊆ {w : B r ≤ |w - c| ≤ (B + 4m) r}`;
* `∫ p dμ = ∑_{w ∈ Λ} p(w) = ∑_{w ∈ K} p(w)` for every polynomial `p` of degree `< m`. -/
theorem lemma5 (m k : ℕ) (hm : 0 < m) (hk : m ≤ k) (μ : Measure ℂ) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hsupp : μ (closedBall c r)ᶜ = 0)
    (hmass : μ Set.univ = ((m * k : ℕ) : ENNReal)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ Λ K : Multiset ℂ, Multiset.card Λ = m * k ∧ Multiset.card K = m * k ∧
      (∀ w ∈ Λ, ‖w - c‖ ≤ 2 * m * r) ∧
      (∀ w ∈ K, B * r ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ (B + 4 * m) * r) ∧
      ∀ p : ℂ[X], p.natDegree < m →
        ∫ z, p.eval z ∂μ = (Λ.map fun w => p.eval w).sum ∧
        ∫ z, p.eval z ∂μ = (K.map fun w => p.eval w).sum := by
  have : IsFiniteMeasure μ := ⟨by rw [hmass]; exact ENNReal.natCast_lt_top _⟩
  have hreal : μ.real Set.univ = (m : ℝ) * k := by
    simp [Measure.real, hmass]
  have hk0 : k ≠ 0 := by omega
  have hNpos : (0 : ℝ) < (m : ℝ) * k := by positivity
  -- normalised moments
  set q : ℕ → ℂ := fun t => (m : ℂ) * ((1 / ((m : ℂ) * k)) * ∫ z, (z - c) ^ t ∂μ) with hqdef
  have hq : ∀ t, ‖q t‖ ≤ m * r ^ t := by
    intro t
    have h1 := norm_integral_pow_sub_le hsupp t
    rw [hreal] at h1
    simp only [hqdef, norm_mul, norm_div, norm_one, Complex.norm_natCast]
    calc (m : ℝ) * (1 / ((m : ℝ) * k) * ‖∫ z, (z - c) ^ t ∂μ‖)
        ≤ (m : ℝ) * (1 / ((m : ℝ) * k) * (r ^ t * ((m : ℝ) * k))) := by gcongr
      _ = m * r ^ t := by field_simp
  obtain ⟨Z, hcard, hpsum, hnorm⟩ := exists_multiset_psum m q r hr hq
  have hmom : ∀ t < m, ∫ z, (z - c) ^ t ∂μ = k * msPsum Z t := by
    intro t ht
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · simp [msPsum, hcard, hreal, mul_comm]
    · rw [hpsum t htpos ht.le, hqdef]
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      have hk0' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
      field_simp
  -- the nodes `Λ`
  refine ⟨k • Z.map (· + c),
    Z.bind fun z => (range k).val.map fun l =>
      z + c + (((B + 2 * m) * r : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I / k) ^ l,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [Multiset.card_nsmul, Multiset.card_map, hcard, mul_comm]
  · rw [Multiset.card_bind]
    simp [hcard, Multiset.map_const', mul_comm]
  · intro w hw
    rw [Multiset.mem_nsmul_of_ne_zero hk0, Multiset.mem_map] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    simpa using hnorm z hz
  · intro w hw
    rw [Multiset.mem_bind] at hw
    obtain ⟨z, hz, hw⟩ := hw
    rw [Multiset.mem_map] at hw
    obtain ⟨l, -, rfl⟩ := hw
    have hζ := (Complex.isPrimitiveRoot_exp k hk0).norm'_eq_one hk0
    have hτ : ‖(((B + 2 * m) * r : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I / k) ^ l‖
        = (B + 2 * m) * r := by
      rw [norm_mul, norm_pow, hζ, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    have hz' := hnorm z hz
    rw [show z + c + (((B + 2 * m) * r : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I / k) ^ l
        - c = z + (((B + 2 * m) * r : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I / k) ^ l
        by ring]
    constructor
    · have := norm_sub_norm_le
        ((((B + 2 * m) * r : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I / k) ^ l) (-z)
      rw [sub_neg_eq_add, norm_neg, hτ] at this
      rw [add_comm z]
      linarith
    · have := norm_add_le z
        ((((B + 2 * m) * r : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I / k) ^ l)
      rw [hτ] at this
      linarith
  · intro p hp
    have hζ := Complex.isPrimitiveRoot_exp k hk0
    constructor
    · refine integral_eval_eq_of_moments hsupp _ m (fun t ht => ?_) p hp
      rw [hmom t ht, Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_map, nsmul_eq_mul]
      simp [msPsum]
    · refine integral_eval_eq_of_moments hsupp _ m (fun t ht => ?_) p hp
      rw [hmom t ht, Multiset.map_bind, Multiset.sum_bind]
      simp only [Multiset.map_map, Function.comp_def]
      have : ∀ z : ℂ, ((range k).val.map fun l =>
          (z + c + (((B + 2 * m) * r : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I / k) ^ l
            - c) ^ t).sum = k * z ^ t := by
        intro z
        rw [← sum_shift_rootsOfUnity_pow hζ z (((B + 2 * m) * r : ℝ) : ℂ) (by omega : t < k)]
        simp only [Finset.sum_eq_multiset_sum]
        congr 1
        refine Multiset.map_congr rfl fun l _ => ?_
        ring
      simp_rw [this, Multiset.sum_map_mul_left, msPsum]

/-- Lemma 5, in the paper's moment form: `∫ z^j dμ = ∑_{w∈Λ} w^j = ∑_{w∈K} w^j`, `j < m`. -/
theorem lemma5_moments (m k : ℕ) (hm : 0 < m) (hk : m ≤ k) (μ : Measure ℂ) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hsupp : μ (closedBall c r)ᶜ = 0)
    (hmass : μ Set.univ = ((m * k : ℕ) : ENNReal)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ Λ K : Multiset ℂ, Multiset.card Λ = m * k ∧ Multiset.card K = m * k ∧
      (∀ w ∈ Λ, ‖w - c‖ ≤ 2 * m * r) ∧
      (∀ w ∈ K, B * r ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ (B + 4 * m) * r) ∧
      ∀ j < m, ∫ z, z ^ j ∂μ = (Λ.map (· ^ j)).sum ∧ ∫ z, z ^ j ∂μ = (K.map (· ^ j)).sum := by
  obtain ⟨Λ, K, h1, h2, h3, h4, h5⟩ := lemma5 m k hm hk μ c r hr hsupp hmass B hB
  refine ⟨Λ, K, h1, h2, h3, h4, fun j hj => ?_⟩
  have := h5 (X ^ j) (by rwa [natDegree_X_pow])
  simpa using this

end OC
