# M06 — Lemma 5: moment-matching points (relaxed form)

**Lean file:** `OrtegaCerdaMultipliers/Quadrature.lean` (≈410 lines, **fully proved**: no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only). It is not yet imported by `OrtegaCerdaMultipliers.lean`.

**Depends on:**
- Mathlib only: polynomials and roots, Vieta, Newton identities, primitive roots of unity, Bochner integral.
- `Defs.lean` is imported for the namespace, but none of its definitions are used.
- **M06 does not depend on M05.** The interface is a measure carried by a closed disc, not a rectangle.

**Used by:** M08 (Theorem 4) for the nodes `Λ(R)`, and M09 (Proposition 2) for the alternative nodes `κ(R)`. Probably also M13 (Theorem 5), where the zeros are those of entire functions, so §6 does not apply.

## 0. The paper [pp. 365–366]

> **Lemma 5.** Let `R` be a rectangle with ratio of side-lengths bounded by `K`. Given any `m ∈ ℕ` and any `C > 1` there is a `k ∈ ℕ` such that for any measure `μ` in a rectangle `R ⊂ ℂ` of total mass `N = mk`, there are two sets of `N` points `Λ(R) = {λ_1,…,λ_N}` inside `R` and `κ(R) = {κ_1,…,κ_N}` inside `4CKR ∖ CR` satisfying
> `∫_R z^j dμ(z) = λ_1^j + ⋯ + λ_N^j = κ_1^j + ⋯ + κ_N^j`, for `j = 0,…,m−1`.

The proof has two parts:
- **The λ's.** It cites Chebyshev quadrature with `k` nodes in `R`, exact for polynomials of degree `m − 1` [Gau76, Kor94]; each node is taken with multiplicity `m`.
- **The κ's.** It sets `κ_{j,l} = λ_j + τ e^{2πil/m}`, using `m p(λ) = Σ_{l<m} p(λ + τ e^{2πil/m})` for `deg p ≤ m − 1`.

## 1. The printed statement is false; what we prove instead

**Counterexample ("inside `R`").** Take:
- `R = [−1,1]²`, so `K = 1`, and `m = 3`;
- `μ = N(w δ_{−1} + (1−w) δ_1)` with `w ∈ (0,1)` irrational.

Suppose `λ_1,…,λ_N ∈ R` satisfy `Σ λ_i² = ∫ z² dμ = N`.
- On `R`, `Re λ² = x² − y² ≤ 1`, with equality only at `λ = ±1`. So every `λ_i = ±1`.
- Then `Σ λ_i ∈ ℤ`. But `∫ z dμ = N(1 − 2w) ∉ ℤ`.

So no `k` works. Equal-weight quadrature with nodes in `R` does not exist for general measures. The paper applies the lemma only to `μ = Δψ|_R` with `Δψ` doubling. For such measures an "inside `R`" version might hold, with `k` depending also on the doubling constant, but the paper does not prove it, and we have not checked whether [Gau76, Kor94] cover it. Seed for `NOTEBOOK.md`.

**What we prove (relaxed Lemma 5).** Let `μ` be carried by the closed disc `B̄(c, r)` with mass `N = mk`, where `1 ≤ m ≤ k`, and let `B ≥ 0`. Then there are multisets `Λ` and `K` of `N` points each such that:
- `Λ ⊆ B̄(c, 2mr)`;
- `K ⊆ {w : Br ≤ |w − c| ≤ (B + 4m) r}`;
- `∫ p dμ = Σ_{w∈Λ} p(w) = Σ_{w∈K} p(w)` for every `p ∈ ℂ[X]` with `deg p < m`.

The constants depend only on `m`, not on `K`, `μ` or `k`. The README (§2.6) already records this divergence: "nodes within a bounded multiple of `R`".

**Quantifiers.** The paper chooses `k` from `m` and `C`. Here **any** `k ≥ m` works, and `k ≥ 1` already suffices for `Λ` alone. So M08 can fix `N := m·m`, or any `mk` with `k ≥ m`, before calling M05.

## 2. Lean statements (all proved)

```lean
namespace OC
open Finset Polynomial MeasureTheory Metric

/-- Newton's recursion: e₀ = 1, n eₙ = (-1)^(n+1) ∑_{i<n} (-1)^i eᵢ q_(n-i). -/
noncomputable def newtonE (q : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => (-1) ^ n / (n + 1) * ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) * newtonE q i * q (n + 1 - i)

/-- Power sum ∑_{z∈Z} z^j (with multiplicity). -/
def msPsum (Z : Multiset ℂ) (j : ℕ) : ℂ := (Z.map (· ^ j)).sum

lemma newtonE_rec (q : ℕ → ℂ) (n : ℕ) :
    (n : ℂ) * newtonE q n =
      (-1) ^ (n + 1) * ∑ i ∈ range n, (-1) ^ i * newtonE q i * q (n - i)

/-- Newton's identities for a multiset of complex numbers. -/
lemma multiset_newton (Z : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * Z.esymm k =
      (-1) ^ (k + 1) * ∑ i ∈ range k, (-1) ^ i * Z.esymm i * msPsum Z (k - i)

lemma msPsum_eq_of_esymm_eq (Z : Multiset ℂ) (q : ℕ → ℂ) (m : ℕ)
    (he : ∀ n ≤ m, Z.esymm n = newtonE q n) : ∀ j, 1 ≤ j → j ≤ m → msPsum Z j = q j

lemma exists_multiset_esymm (e : ℕ → ℂ) (he0 : e 0 = 1) (m : ℕ) :
    ∃ Z : Multiset ℂ, Multiset.card Z = m ∧ (∀ n ≤ m, Z.esymm n = e n) ∧
      ∀ z ∈ Z, z ^ m + ∑ i : Fin m, (-1) ^ (m - (i : ℕ)) * e (m - i) * z ^ (i : ℕ) = 0

lemma norm_newtonE_le (q : ℕ → ℂ) (m : ℕ) (hm : 1 ≤ m) (r : ℝ) (hr : 0 ≤ r)
    (hq : ∀ j, ‖q j‖ ≤ m * r ^ j) : ∀ n, ‖newtonE q n‖ ≤ ((m : ℝ) * r) ^ n

lemma norm_le_of_root (m : ℕ) (B : ℝ) (hB : 0 ≤ B) (c : Fin m → ℂ)
    (hc : ∀ i : Fin m, ‖c i‖ ≤ B ^ (m - (i : ℕ))) (z : ℂ)
    (hz : z ^ m + ∑ i : Fin m, c i * z ^ (i : ℕ) = 0) : ‖z‖ ≤ 2 * B

/-- Key lemma (a)+(b): prescribed power sums with a root bound. -/
theorem exists_multiset_psum (m : ℕ) (q : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hq : ∀ j, ‖q j‖ ≤ m * r ^ j) :
    ∃ Z : Multiset ℂ, Multiset.card Z = m ∧ (∀ j, 1 ≤ j → j ≤ m → msPsum Z j = q j) ∧
      ∀ z ∈ Z, ‖z‖ ≤ 2 * m * r

lemma integral_eval_eq_of_moments {μ : Measure ℂ} [IsFiniteMeasure μ] {c : ℂ} {r : ℝ}
    (hsupp : μ (closedBall c r)ᶜ = 0) (Λ : Multiset ℂ) (m : ℕ)
    (h : ∀ t < m, ∫ z, (z - c) ^ t ∂μ = (Λ.map fun w => (w - c) ^ t).sum)
    (p : ℂ[X]) (hp : p.natDegree < m) :
    ∫ z, p.eval z ∂μ = (Λ.map fun w => p.eval w).sum

lemma sum_shift_rootsOfUnity_pow {k : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k) (z τ : ℂ) {t : ℕ}
    (ht : t < k) : ∑ l ∈ range k, (z + τ * ζ ^ l) ^ t = k * z ^ t

/-- **Lemma 5 (relaxed).** -/
theorem lemma5 (m k : ℕ) (hm : 0 < m) (hk : m ≤ k) (μ : Measure ℂ) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hsupp : μ (closedBall c r)ᶜ = 0)
    (hmass : μ Set.univ = ((m * k : ℕ) : ENNReal)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ Λ K : Multiset ℂ, Multiset.card Λ = m * k ∧ Multiset.card K = m * k ∧
      (∀ w ∈ Λ, ‖w - c‖ ≤ 2 * m * r) ∧
      (∀ w ∈ K, B * r ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ (B + 4 * m) * r) ∧
      ∀ p : ℂ[X], p.natDegree < m →
        ∫ z, p.eval z ∂μ = (Λ.map fun w => p.eval w).sum ∧
        ∫ z, p.eval z ∂μ = (K.map fun w => p.eval w).sum

/-- The paper's moment form. -/
theorem lemma5_moments (m k : ℕ) (hm : 0 < m) (hk : m ≤ k) (μ : Measure ℂ) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hsupp : μ (closedBall c r)ᶜ = 0)
    (hmass : μ Set.univ = ((m * k : ℕ) : ENNReal)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ Λ K : Multiset ℂ, Multiset.card Λ = m * k ∧ Multiset.card K = m * k ∧
      (∀ w ∈ Λ, ‖w - c‖ ≤ 2 * m * r) ∧
      (∀ w ∈ K, B * r ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ (B + 4 * m) * r) ∧
      ∀ j < m, ∫ z, z ^ j ∂μ = (Λ.map (· ^ j)).sum ∧ ∫ z, z ^ j ∂μ = (K.map (· ^ j)).sum
end OC
```

Design choices:
- Nodes are a `Multiset ℂ`, so multiplicities are explicit. Every node of `Λ` has multiplicity `≥ k`.
- The mass hypothesis is in `ℝ≥0∞`. It yields `IsFiniteMeasure μ` inside the proof.
- Integrals are complex Bochner integrals.

## 3. Proof

### 3.1 Choice of route

The proposed generating-function route needs analytic estimates:
- Cauchy estimates for the Taylor coefficients of `exp(−N Σ s_j w^j/j)`;
- the identification of the power series;
- the tail bound.

We use instead a **purely algebraic** route. It has fewer nodes per moment problem, `m` instead of `N`, and an elementary root bound:
- solve the moment problem with **`m` points** `Z`, prescribing the power sums `p_1..p_m`;
- repeat each point `k` times.

Prescribing `p_m` as well (with the true `m`-th moment) is harmless, and it makes point masses exact: `μ = Nδ_a` gives `Z = {a,…,a}`.

### 3.2 Newton recursion (`newtonE`, `newtonE_rec`)

For `q : ℕ → ℂ`, define `e_0 = 1` and `e_{n+1} = (−1)^n/(n+1) · Σ_{i≤n} (−1)^i e_i q_{n+1−i}`.
- The recursion is well founded through `i : Fin (n+1)`; Lean's default `decreasing_by` handles it.
- `newtonE_rec`: `n e_n = (−1)^{n+1} Σ_{i<n} (−1)^i e_i q_{n−i}`. Unfold, then `Fin.sum_univ_eq_sum_range`, `field_simp`, `ring`.

### 3.3 Newton identities for a multiset (`multiset_newton`)

Mathlib has Newton's identities only for `MvPolynomial σ R`:
- `MvPolynomial.mul_esymm_eq_sum`: `k · esymm k = (−1)^{k+1} Σ_{a ∈ antidiagonal k, a.1 < k} (−1)^{a.1} esymm a.1 · psum a.2`.

Transfer it to a multiset `Z`:
1. Let `σ = Fin Z.toList.length` and `x = Z.toList.get`. Then `univ.val.map x = Z`, by `Fin.univ_val_map`, `List.ofFn_get` and `Multiset.coe_toList`.
2. Apply `MvPolynomial.aeval x`.
   - `aeval_esymm_eq_multiset_esymm` turns `esymm` into `Z.esymm`.
   - `aeval (psum j) = Σ_i x_i^j = msPsum Z j`. Rewrite only the right-hand side with `← hx` and `Multiset.map_map`; a plain `rw` hits a motive error.
3. Antidiagonal to range (`sum_antidiagonal_filter_lt`): `Finset.sum_filter`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, `sum_range_succ`, `ite_eq_left`.

### 3.4 Power sums from elementary symmetric functions (`msPsum_eq_of_esymm_eq`)

Assume `Z.esymm n = e_n` for `n ≤ m`. We prove `p_j(Z) = q_j` for `1 ≤ j ≤ m` by strong induction on `j`; write `j = j' + 1`.
1. Compare `multiset_newton Z j` with `newtonE_rec q j`, after rewriting `Z.esymm i = e_i` (`i ≤ j ≤ m`). The left-hand sides agree.
2. Cancel `(−1)^{j+1}`. This gives `Σ_{i<j} (−1)^i e_i p_{j−i} = Σ_{i<j} (−1)^i e_i q_{j−i}`.
3. Split off `i = 0` with `sum_range_succ'`. The terms with `i ≥ 1` agree by the induction hypothesis, since `1 ≤ j − i < j`.
4. What is left is `e_0 p_j = e_0 q_j`, with `e_0 = 1`.

### 3.5 The polynomial and its roots (`exists_multiset_esymm`)

Let `c_i = (−1)^{m−i} e_{m−i}` for `i : Fin m`, and `Q = X^m + Σ_{i:Fin m} C(c_i) X^i`.
- **Monic of degree `m`:** `degree_sum_fin_lt`, `monic_X_pow_add`, `natDegree_add_eq_left_of_degree_lt`, `natDegree_X_pow`.
- **Roots:** let `Z = Q.roots`. Then `card Z = m` by `IsAlgClosed.card_roots_eq_natDegree`.
- **Coefficients:** `Q.coeff k = c_k` for `k < m`, by `finsetSum_coeff`, `coeff_C_mul_X_pow`, `Finset.sum_eq_single`.
- **Vieta** (`coeff_eq_esymm_roots_of_card`) at `k = m − n`, `1 ≤ n ≤ m`: `(−1)^n e_n = (−1)^n Z.esymm n`, then cancel. For `n = 0`, `simp` gives `esymm 0 = 1`.
- **Root equation:** for `z ∈ Z`, `mem_roots` and `eval` give `z^m + Σ c_i z^i = 0`.

### 3.6 Coefficient bound (`norm_newtonE_le`)

Assume `|q_j| ≤ m r^j` for all `j`, and `m ≥ 1`. We prove `|e_n| ≤ (mr)^n` by strong induction.
- Each term satisfies `|e_i||q_{n−i}| ≤ (mr)^i · m r^{n−i} = m^{i+1} r^n ≤ m^n r^n`, since `i + 1 ≤ n` and `m ≥ 1` (`pow_le_pow_right₀`).
- There are `n` terms, and the prefactor is `1/n`.

### 3.7 Root bound (`norm_le_of_root`), constant `A = 2m`

Assume `z^m + Σ_{i<m} c_i z^i = 0` with `|c_i| ≤ B^{m−i}`. Suppose `t = |z| > 2B`.
1. `t^m ≤ Σ_{i<m} B^{m−i} t^i`.
2. Since `B ≤ t/2`, the right-hand side is at most `t^m Σ_{i<m} (1/2)^{m−i}`.
3. That sum equals `1 − 2^{−m} < 1`, by `sum_range_reflect` and `geom_sum_eq`. Since `t^m > 0`, this is a contradiction.

Apply this with `B = mr` (§3.6). Then `exists_multiset_psum` holds: `|z| ≤ 2mr`. The case `m = 0` is handled separately with `Z = 0`.

### 3.8 From measures to nodes: `Λ`

Let `q_t = m · (1/(mk)) ∫(z−c)^t dμ = (1/k)∫(z−c)^t dμ`.
- `norm_integral_le_of_norm_le_const`, with the a.e. bound `|z − c| ≤ r` from `mem_ae_iff.mpr hsupp`, gives `|q_t| ≤ m r^t`.
- Take `Z` from §3.7.
- **Centred moments.** `∫(z−c)^t dμ = k · p_t(Z)` for `t < m`:
  - `t = 0`: `μ.real univ = mk = k · card Z`;
  - `t ≥ 1`: by §3.4.
- **Nodes.** `Λ = k • Z.map (· + c)`:
  - `card Λ = km`;
  - `|w − c| = |z| ≤ 2mr`, by `Multiset.mem_nsmul_of_ne_zero`;
  - `Σ_{w∈Λ}(w − c)^t = k · p_t(Z)`, by `map_nsmul` and `sum_nsmul`.

**Polynomial transfer** (`integral_eval_eq_of_moments`). Let `p' = p.comp (X + C c)`.
- `natDegree p' = natDegree p < m`, by `natDegree_comp` and `natDegree_X_add_C`.
- `eval_eq_sum_range'` gives `p(z) = Σ_{i<m} p'_i (z − c)^i`.
- Integrate term by term (`integral_finsetSum`, `integral_const_mul`). Integrability comes from `Integrable.of_bound` (continuous, and bounded a.e. by `r^t`).
- Use the moment hypothesis, then swap `Σ_i` and `Σ_{w∈Λ}` (`finset_sum_multiset_sum_comm`, by multiset induction).

### 3.9 The alternative set `K`

Let `ζ = exp(2πi/k)`, primitive by `Complex.isPrimitiveRoot_exp`. Let `τ = (B + 2m) r`.
- **Definition.** `K = Z.bind (fun z ↦ (range k).val.map (fun l ↦ z + c + τ ζ^l))`.
- **Count.** `card K = m k`, by `card_bind` and `map_const'`.
- **Location.** `|τζ^l| = τ` (`norm'_eq_one`), and `|z| ≤ 2mr`. The triangle inequality gives `Br ≤ |w − c| ≤ (B + 4m) r`.
- **Moments** (`sum_shift_rootsOfUnity_pow`): `Σ_{l<k} (z + τζ^l)^t = k z^t` for `t < k`.
  - Expand with `add_pow` and swap the sums.
  - The `s = t` term gives `k z^t`.
  - For `s < t`, the inner sum is `Σ_l (ζ^{t−s})^l = 0`, by `geom_sum_eq`. Here `ζ^{t−s} ≠ 1` by `pow_ne_one_of_pos_of_lt`, since `0 < t − s < k`, and `(ζ^{t−s})^k = 1`.
  - Hence `Σ_{w∈K} (w−c)^t = k p_t(Z)` for `t < m ≤ k`. This is where **`k ≥ m`** is used.

The paper groups points by `m`, using `m`-th roots of unity on nodes of multiplicity `m`. We group them by `k`, using `k`-th roots of unity on each of the `m` roots. Both are the same identity.

## 4. Mathlib dependencies (checked in v4.35.0)

- **Newton.** `MvPolynomial.mul_esymm_eq_sum`, `MvPolynomial.aeval_esymm_eq_multiset_esymm`, `MvPolynomial.psum`. `psum_eq_mul_esymm_sub_sum` is not needed.
- **Vieta and roots.** `Polynomial.coeff_eq_esymm_roots_of_card`, `IsAlgClosed.card_roots_eq_natDegree`, `Polynomial.mem_roots`.
- **Degree.** `Polynomial.monic_X_pow_add`, `Polynomial.degree_sum_fin_lt`, `natDegree_comp`, `eval_eq_sum_range'`.
- **Sums.** `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, `Fin.univ_val_map`, `List.ofFn_get`, `geom_sum_eq`, `Finset.sum_range_reflect`, `add_pow`.
- **Roots of unity.** `Complex.isPrimitiveRoot_exp`, `IsPrimitiveRoot.pow_ne_one_of_pos_of_lt`, `IsPrimitiveRoot.norm'_eq_one`.
- **Integration.** `MeasureTheory.norm_integral_le_of_norm_le_const`, `Integrable.of_bound`, `integral_finsetSum`, `integral_const_mul`, `mem_ae_iff`.
- **Renamed lemmas** (deprecated names in this version): `finset_sum_coeff` → `finsetSum_coeff`, `eval_finset_sum` → `eval_finsetSum`, `integral_finset_sum` → `integral_finsetSum`, `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`, `push_neg` → `push Not`.

## 5. Interface for M08 / M09

For each rectangle `R_i` of M05:
1. Pick `c_i ∈ R_i` and `r_i := diam R_i`, so that `R_i ⊆ B̄(c_i, r_i)`.
2. Let `μ_i` be the restricted Riesz measure in the README normalisation: `μ_i := (2π)⁻¹ • (Δψ).restrict R_i`, so point masses carry no `2π` (see README §4, p. 366).
3. Fix `N := m·k` with `k := m`. M05 must deliver `μ_i(ℂ) = N`.

`lemma5` then gives:
- `Λ_i ⊆ B̄(c_i, A r_i)` with `A = 2m`;
- `K_i ⊆ {B₁ r_i ≤ |w − c_i| ≤ B₂ r_i}` with `B₁ = B` free and `B₂ = B + 4m`;
- exactness on `ℂ[X]_{<m}`.

M08 uses the real part:
- For a positive real measure, `∫ Re p dμ = Re ∫ p dμ` (`integral_re`, `reCLM`). So the Taylor polynomial of `log|z − ζ|` (or of `log|(z−ζ)/(1−z̄ζ)|`) in `ζ`, which is `Re` of a holomorphic polynomial of degree `< m`, integrates to the same value against `μ_i` and against `Σ_{λ∈Λ_i} δ_λ`.

Consequences for M08 and M09:
- **Neighbour counts.** In the error estimate for far rectangles, "far" must now mean `z ∉ B̄(c_i, (2m+1)·const·r_i)`. The nodes and the Taylor centre `c_i` lie in `B̄(c_i, 2m r_i)`. This only changes the constant `K` in Claim 2 (the number of near rectangles).
- **Multiplicities.** Nodes have multiplicity `≥ k`. Theorem 4's lower bound `(d(z,Λ)/ρ(z))^M` then holds with `M ≤ N · #(near rectangles)`. The Remark's separated zeros with `M = 1` is not obtained, and the paper does not need it.
- **M09.** Choose `B` so that `B r_i` exceeds the distance from `c_i` to the far side of every immediate neighbour of `R_i` (Claim 2). Then choose the family separation `M` of Proposition 2 larger than `(B + 4m)·const`.

## 6. Open risk: the disc case (M08 disc, hence Theorem 2)

In `𝔻` the nodes must lie **in `𝔻`**, and within bounded hyperbolic distance of `R_i`. `lemma5` gives Euclidean distance `2m r_i`. Normalise by the Möbius map `T_{c_i}` (the kernel `log|(z−ζ)/(1−z̄ζ)|` is Möbius invariant, so moments may be matched in that coordinate). Then `R_i ⊆ B̄(0, tanh D_i)`, where `D_i` is the hyperbolic diameter of `R_i`.
- **Safe case.** The nodes are safe if `2m tanh D_i ≤ 1/2`, that is `D_i ≲ 1/(4m)`.
- **Large rectangles.** Mass-`N` rectangles can be hyperbolically large when `Δψ` is sparse. Example: `(1−|z|²)²Δψ ≡ δ` small, as in BOC's application. Then `tanh D_i → 1`, and the nodes may leave `𝔻`.
- **Lower bound.** Even the best `m`-point solution can lie outside `B̄(0, ρ)`: for `μ ∝ δ_ρ + δ_{−ρ}` and `m = 3`, the roots are `0, ±ρ√1.5`. So in `𝔻`, something beyond §3 is needed. Options:
  - **(a)** A Chebyshev-type quadrature theorem: nodes in `B̄(0, ρ')` with `ρ' = ρ'(ρ, m) < 1` for measures on `B̄(0, ρ)`, `N` large. This needs a perturbation/implicit-function argument, or the [Kor94] potential theory.
  - **(b)** Keep disc rectangles hyperbolically small. This needs `Δψ(D(z, c/m)) ≥ N`, which the hypotheses of Theorem 2 do not give.
- **The paper's proof is affected too:** with exact quadrature "inside `R`" the problem would not arise, but see §1.
- **Decision needed** before M08 (disc) is scaffolded. The plane case is unaffected.

## 7. Status and effort

- **Done:** everything in §2, proved, about 410 lines; it compiles with `lake env lean` and has no warnings.
- **To do before merging:**
  - add `import OrtegaCerdaMultipliers.Quadrature` to the root file;
  - optionally add a corollary in "diameter" form (`S ⊆ B̄(c, d)`, `μ Sᶜ = 0`), about 15 lines.
- **Not done:** the disc remedy of §6. If option (a) is chosen, expect a new, hard module, roughly 800–1500 lines.
