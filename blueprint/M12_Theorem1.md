# M12 — Theorem 1 (locally doubling), Christ's Theorem 1, Proposition 1

**Lean file:** `OrtegaCerdaMultipliers/Theorem1.lean`.

**Paper:**
- Theorem 1 (p. 356, Christ);
- the remark that the proof works for locally doubling `Δφ` (p. 357, last paragraph);
- formula (1) and Proposition 1 (pp. 358–359);
- the proof in §4.2 (p. 374).

**Depends on:**
- M00: `IsSubharmonicWeight univ`, `IsLocallyDoubling`, `IsDoubling`, `massRadius`, `IsWeakDbarSol`.
- M01: `integral_mul_lap` and `lap_const_mul_normSq` (Wirtinger), `laplacian_eq_four_mul_lap` (Basic), `volume_ball_complex` (Polar).
- M04: Lemma 6 in `ℂ` (`lemma6_plane`, §2.1).
- M09: Proposition 2 in `ℂ` **with the global upper bound** (`prop2_plane_full`, §2.1).
- M10: `plane_kernel_operator`, `norm_exp_planeKernel_num`.
- M11: `Measure.exists_add_eq_of_le`, `IsSubharmonicWeight.sigmaFinite`, `exists_measurable_partition`.
- Mathlib: `integral_add_measure`, `integral_smul_measure`, `Finset.sum_eq_single`, `isClosed_biInter`, `Measurable.indicator`, `Complex.norm_exp`.

No growth lemma is needed in the plane: `μ ≥ ε·dm` gives `μ(B(z,R)) ≥ επR²` directly.

---

## 0. The paper

**Theorem 1 (Christ; p. 356).** Let `φ` be subharmonic in `ℂ` with `Δφ(D) ≥ 1` for every disc `D` of radius `r`, and `Δφ` doubling. Then there is a solution of `∂̄u = f` with `‖u e^{−φ}‖_p ≲ ‖f e^{−φ}‖_p` for all `p ∈ [1,∞]`.

**p. 357:** "it is also possible to show with the same type of proof that Theorem 1 holds when the measure `Δφ` is locally doubling instead of doubling."

**(1) and Proposition 1 (pp. 358–359).** Under the hypotheses of Theorem 1 there is a kernel `k` such that `u(z) = ∫_ℂ e^{φ(z)−φ(ζ)} k(z,ζ) f(ζ) dm(ζ)` solves `∂̄u = f`, and for some `ε > 0`, `|k(z,ζ)| ≃ e^{−ε|z−ζ|²}/|z−ζ|`.

**Proof (p. 374).**
- "The same construction proves Theorem 1": replace Lemma 7 by Lemma 8.
- Take the auxiliary function `ψ = φ − (ε/2)|z|²`.
- Take the solution `∫ κ'(z,ζ) f(ζ) dm(ζ)` with `κ'(z,ζ) = Σ_i h_i(z)χ_{Ω_i}(ζ)/h_i(ζ) · (1/π) e^{2ε(ζ̄z−|ζ|²)}/(z−ζ)`.
- "Therefore `|κ'(z,ζ)| ≃ e^{φ(z)}e^{−ε|z−ζ|²}/(e^{φ(ζ)}|z−ζ|)`. This estimate proves Proposition 1 and Theorem 1."

---

## 1. Verification

### 1.1 The auxiliary weight and the Lemma 8 exponent in the plane

The sign of `ψ = φ − (ε/2)|z|²` is right (unlike the disc, M11 §1(a)). Two constants are inconsistent, though.
- **The exponent of the kernel.** With `ψ = φ − a|z|²`, the matching Lemma 8 kernel is `e^{2a(ζ̄z−|ζ|²)}` (`α = a`). Then

  `e^{ψ(z)−ψ(ζ)} |e^{2a(ζ̄z−|ζ|²)}| = e^{φ(z)−φ(ζ)} e^{−a|z−ζ|²}`

  (M10 `norm_exp_planeKernel_num`). The paper takes `a = ε/2` but writes `e^{2ε(ζ̄z−|ζ|²)}`, i.e. `α = ε`. Then the factor becomes, with `w = z−ζ`,

  `e^{−(ε/2)|z|² + 2εRe(ζ̄z) − (3ε/2)|ζ|²} = e^{εRe(ζ̄w) − (ε/2)|w|²}`,

  which is unbounded. Both Schur integrals diverge, for instance `∫ e^{εRe(ζ̄w)−(ε/2)|w|²}/|w| dm(w) ≈ e^{ε|ζ|²/2}/|ζ| → ∞`. The kernel should be `e^{ε(ζ̄z−|ζ|²)}`, and then the bound is `e^{−(ε/2)|z−ζ|²}`.
- **Laplacian normalisation.** As in the disc, the paper uses `Δ = ∂∂̄` here (`Δ(ε/2 |z|²) = ε/2`). With the standard Laplacian, `Δ(c|z|²) = 4c`, so we need `4c ≤ ε/2`: we take `c := ε/8`, `ψ := φ' − c|z|²` and the kernel `e^{2c(ζ̄z−|ζ|²)}`.

### 1.2 Proposition 1: the printed `≃` fails (issue (c), confirmed)

`κ'(z,ζ) = h_i(z)/h_i(ζ) · (1/π) e^{2c(ζ̄z−|ζ|²)}/(z−ζ)` for `ζ ∈ Ω_i`. So `κ'(λ,ζ) = 0` whenever `ζ ∈ Ω_i` and `h_i(λ) = 0`, with `λ ≠ ζ` (`ζ ∈ G_i` keeps `ζ` away from the zeros). Lean: `thm1H_eq_zero_of_zero`.

Such pairs exist.
- Some `Ω_i` is nonempty.
- Every `h_i` has zeros. If `h_i` had none, then `G_i = ℂ`, so `|log|h_i| − ψ| ≤ log C` on `ℂ`, and `log|h_i|` would be harmonic. But `ψ − log|h_i|` has Laplacian `μψ ≥ (ε/2)dm`, so its circle means grow: `M_R − value(0) = (1/2π)∫_{B(0,R)} log(R/|w|) dμψ ≥ (ε/4π)·2π∫_0^R t log(R/t) dt = εR²/8 → ∞`. That contradicts boundedness.

So the lower bound in `|k| ≃ e^{−ε|z−ζ|²}/|z−ζ|` fails for the paper's kernel, and only `≲` is provable for it. This is why `prop1` has only the upper bound.

**Remark (no other kernel can satisfy `≃` in general; heuristic).** Suppose a measurable kernel gives a solution operator for all `f ∈ C_c^∞`. Then `e^{φ(z)−φ(ζ)}k(z,ζ) = 1/(π(z−ζ)) + D(z,ζ)` with `D(·,ζ)` entire (Weyl, applied in `z` for a.e. `ζ`). A two-sided bound would make `F_ζ(z) := 1/π + (z−ζ)D(z,ζ)` a zero-free entire function with `log|F_ζ| = φ − φ(ζ) − ε|z−ζ|² + O(1)`. Hence `φ − ε|z|²` would be harmonic up to a bounded function. This fails for `φ = |z|⁴`: `Δφ = 16|z|² dm` is locally doubling and satisfies the mass condition, while `Δ(φ − ε|z|²) = 16|z|² − 4ε` cannot be the Laplacian of a bounded function. So the printed Proposition 1 is false in general, not only for this construction. (The step "`D(·,ζ)` entire" needs a Weyl argument in the product space; we do not formalize this remark.)

### 1.3 Hypotheses

- **Mass condition.** `theorem1` has `1 ≤ μ(ball z r)`; Lemma 6 and Proposition 2 have `1 < …`. The upgrade is free: `B(z,3r) ⊇ B(z,r) ⊔ B(z+2r,r)` (disjoint), so `μ(B(z,3r)) ≥ 2`.
- **`theorem1_christ`.** Doubling implies locally doubling, with the same constant.

---

## 2. Statements (namespace `OC`)

All typecheck (scratch file `m12_check.lean`, which contains M10's statements and the M11 helpers used; imports `Defs`, `Foundations.Basic`).

### 2.1 Assumed from other modules (exact form required)

```lean
/-- (M04) Lemma 6 in the plane. -/
theorem lemma6_plane (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 < μ (ball z r)) :
    ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ) (ε B : ℝ), 0 < ε ∧ IsSubharmonicWeight univ φ' μ' ∧
      IsLocallyDoubling μ' ∧ ENNReal.ofReal ε • volume ≤ μ' ∧ ∀ z, |φ z - φ' z| ≤ B

/-- (M09) Proposition 2 in the plane, with the global upper bound. -/
theorem prop2_plane_full (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight univ ψ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 < μ (ball z R)) :
    ∃ (n : ℕ) (h : Fin n → ℂ → ℂ) (ε : ℝ) (C : ℝ), 0 < ε ∧ 0 < C ∧
      (∀ i, Differentiable ℂ (h i)) ∧
      (∀ z : ℂ, ∃ i, ∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) ∧
      (∀ i, ∀ z, ‖h i z‖ ≤ C * Real.exp (ψ z)) ∧
      ∀ i, ∀ z : ℂ, (∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) →
        C⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖
```

As in the disc (M11 §2.1), the fixed `prop2_plane` lacks the conjunct `∀ i z, ‖h i z‖ ≤ C e^{ψ z}`, which is not derivable from it. M09 must export `prop2_plane_full`; `prop2_plane` is a corollary.

### 2.2 Exported

```lean
theorem two_le_measure_ball_three_mul {μ : Measure ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ z : ℂ, 1 ≤ μ (ball z r)) (z : ℂ) : 2 ≤ μ (ball z (3 * r))

theorem IsLocallyDoubling.of_le_of_le {μ ν : Measure ℂ} (hμ : IsLocallyDoubling μ)
    {a b : ℝ≥0∞} (ha : a ≠ 0) (hb : b ≠ ∞) (h₁ : a • μ ≤ ν) (h₂ : ν ≤ b • μ) :
    IsLocallyDoubling ν

theorem isSubharmonicWeight_sub_normSq {φ' : ℂ → ℝ} {ν : Measure ℂ} {ε c : ℝ} (hc : 0 ≤ c)
    (hcε : 4 * c ≤ ε) (hφ' : IsSubharmonicWeight univ φ' (ν + ENNReal.ofReal ε • volume)) :
    IsSubharmonicWeight univ (fun z ↦ φ' z - c * ‖z‖ ^ 2)
      (ν + ENNReal.ofReal (ε - 4 * c) • volume)

theorem exists_aux_weight_plane (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 ≤ μ (ball z r)) :
    ∃ (ψ : ℂ → ℝ) (μψ : Measure ℂ) (c B : ℝ), 0 < c ∧ 0 ≤ B ∧
      IsSubharmonicWeight univ ψ μψ ∧ IsLocallyDoubling μψ ∧
      (∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 < μψ (ball z R)) ∧
      ∀ z, |ψ z - (φ z - c * ‖z‖ ^ 2)| ≤ B

theorem isClosed_goodSet_plane (Z : Set ℂ) (ρ : ℂ → ℝ) (ε : ℝ) :
    IsClosed {z : ℂ | ∀ w ∈ Z, ε * ρ w ≤ dist z w}

/-- The holomorphic factor of the kernel `κ'` of Theorem 1:
`H(z, ζ) = ∑ᵢ χ_{Ωᵢ}(ζ) hᵢ(z)/hᵢ(ζ) · e^{2c(ζ̄ z - |ζ|²)}`. -/
def thm1H {n : ℕ} (h : Fin n → ℂ → ℂ) (Ω : Fin n → Set ℂ) (c : ℝ) (z ζ : ℂ) : ℂ :=
  (∑ i, (Ω i).indicator (fun ζ ↦ h i z / h i ζ) ζ) *
    Complex.exp (2 * c * (conj ζ * z - ((‖ζ‖ ^ 2 : ℝ) : ℂ)))

theorem exists_plane_solution_kernel (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoubling μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 ≤ μ (ball z r)) :
    ∃ (H : ℂ → ℂ → ℂ) (c A : ℝ), 0 < c ∧ 0 ≤ A ∧ Measurable (Function.uncurry H) ∧
      (∀ ζ, Differentiable ℂ (fun z ↦ H z ζ)) ∧ (∀ ζ, H ζ ζ = 1) ∧
      ∀ z ζ, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) * Real.exp (-c * ‖z - ζ‖ ^ 2)

theorem IsDoubling.isLocallyDoubling {μ : Measure ℂ} (h : IsDoubling μ) :
    IsLocallyDoubling μ

theorem thm1H_eq_zero_of_zero {n : ℕ} {h : Fin n → ℂ → ℂ} {Ω : Fin n → Set ℂ} {c : ℝ}
    (hΩ : ∀ ζ, ∃! i, ζ ∈ Ω i) {i : Fin n} {ζ z : ℂ} (hζ : ζ ∈ Ω i) (hz : h i z = 0) :
    thm1H h Ω c z ζ = 0
```

### 2.3 Main statements (fixed in `comparator/statements.lean`)

`theorem1`, `theorem1_christ`, `prop1`, verbatim (typechecked again in the scratch file).

**Count:** 1 definition (`thm1H`) and 8 helper theorems, plus the 3 main statements. All typecheck. Assumed: 2 (M04, M09), plus 3 from M11.

---

## 3. Proofs

### 3.1 `two_le_measure_ball_three_mul`

`ball z r` and `ball (z + 2r) r` are disjoint, since their centres are `2r` apart (`Metric.ball_disjoint_ball` with `r + r ≤ dist z (z + 2r) = 2r`). Both lie in `ball z (3r)`, because `‖w − z‖ < r`, or `‖w − z‖ ≤ 2r + ‖w − (z+2r)‖ < 3r`. Hence `μ(ball z 3r) ≥ μ(ball z r ∪ ball (z+2r) r) = μ(ball z r) + μ(ball (z+2r) r) ≥ 2` (`measure_mono`, then `measure_union` for disjoint measurable sets).

### 3.2 `IsLocallyDoubling.of_le_of_le`, `IsDoubling.isLocallyDoubling`

- **`of_le_of_le`.** Identical to M11 §4.6, with Euclidean balls and the constraint `2r < 1` carried along.
- **`isLocallyDoubling`.** Take the same `C` and drop the hypothesis `2 * r < 1`.

### 3.3 `isSubharmonicWeight_sub_normSq`

Let `ψ := φ' − c|z|²` and `μψ := ν + ofReal(ε−4c)•volume`.
- **`continuousOn`:** `φ'` is continuous on `univ`, and `‖z‖²` is continuous.
- **`finite_of_compact`:** `ν(K) ≤ μ'(K) < ∞` and `volume K < ∞` (`IsCompact.measure_lt_top`).
- **`carried`:** `univᶜ = ∅`.
- **`laplacian_eq`:**
  - M01's `integral_mul_lap` (global, `U = ‖·‖²` is `C^∞`) with `lap (‖·‖²) = 1` (`lap_const_mul_normSq 1`) and `Δ = 4 lap` gives `∫ |z|² Δχ = 4 ∫ χ dm`.
  - So `∫ ψ Δχ = ∫ φ'Δχ − c·4∫χ = (∫χ dν + ε∫χ dm) − 4c∫χ dm = ∫ χ dμψ`, by `integral_sub`, `integral_add_measure`, `integral_smul_measure` and `ENNReal.toReal_ofReal (0 ≤ ε − 4c)`.
  - `χ` is integrable for `ν` because `ν ≤ ν + ε•volume`, which is finite on `tsupport χ`.

### 3.4 `exists_aux_weight_plane`

1. **Mass upgrade.** `hm` and §3.1 give `∀ z, 1 < μ(ball z (3r))`.
2. **Lemma 6.** `lemma6_plane` gives `φ', μ', ε, B` with `ε•volume ≤ μ'`.
3. **Decomposition.** `μ'` is σ-finite (`IsSubharmonicWeight.sigmaFinite isOpen_univ`), so `Measure.exists_add_eq_of_le` gives `ν` with `ν + ε•volume = μ'`.
4. **The weight.** `c := ε/8`, `ψ := φ' − c|z|²`, `μψ := ν + ofReal(ε/2)•volume`. Then `IsSubharmonicWeight univ ψ μψ` by §3.3, since `ε − 4c = ε/2`.
5. **Comparison.** `(1/2)•μ' ≤ μψ ≤ μ'`, as in M11 §4.8 step 4. So `μψ` is locally doubling by §3.2 with `a = 1/2`, `b = 1`.
6. **Mass.** `μψ(ball z R) ≥ (ε/2) vol(ball z R) = (ε/2)πR²` (`volume_ball_complex`). With `R := √(4/(επ))` this is `2 > 1`.
7. **Equivalence.** `|ψ − (φ − c|z|²)| = |φ' − φ| ≤ B`, and `B ≥ 0`.

### 3.5 `isClosed_goodSet_plane`

The set is `⋂_{w ∈ Z} {z | ε ρ w ≤ dist z w}`. Each piece is closed (`isClosed_le continuous_const (continuous_id.dist continuous_const)`), and so is the intersection (`isClosed_biInter`). It is therefore Borel measurable (`IsClosed.measurableSet`), which is needed for `Measurable (uncurry k)` in `prop1`, with no a.e. slack.

### 3.6 `exists_plane_solution_kernel`

1. `exists_aux_weight_plane` gives `ψ, μψ, c, B`.
2. `prop2_plane_full ψ μψ` gives `n, h, ε_P, C_P`. The `h i` are entire, hence continuous and measurable; no indicator trick is needed, unlike the disc.
3. **Partition.** `G i := {z | ∀ w ∈ {w | h i w = 0}, ε_P * massRadius μψ w ≤ dist z w}`. These are closed (§3.5) and cover `ℂ` (second conjunct). `exists_measurable_partition` with `S = univ` gives `Ω`.
4. **Definition.** `H := thm1H h Ω c`; `A := C_P² e^{2B}`.
5. **Measurability.** Each summand is `indicator (univ ×ˢ Ω i)` of `(z,ζ) ↦ h i z / h i ζ`. The exponential factor is continuous.
6. **For each `ζ`, let `i₀` be the unique index** with `ζ ∈ Ω i₀`. By `Finset.sum_eq_single`:

   `H z ζ = (h i₀ z / h i₀ ζ) · exp(2c(ζ̄z − |ζ|²))`.
   - **Entire in `z`:** `Differentiable.mul`, `.div_const`, `Differentiable.cexp` of an affine map.
   - **`H ζ ζ = 1`:** `h i₀ ζ ≠ 0` because `ζ ∈ G i₀` gives `C_P⁻¹e^{ψ ζ} ≤ ‖h i₀ ζ‖`. Also `conj ζ * ζ = ‖ζ‖²` (`Complex.conj_mul'`), so the exponential is `exp 0 = 1`.
   - **Bound.** The global upper bound at `z` and the lower bound at `ζ` give `‖h i₀ z‖/‖h i₀ ζ‖ ≤ C_P² e^{ψ z − ψ ζ}`. Moreover `ψ z − ψ ζ ≤ φ z − φ ζ − c|z|² + c|ζ|² + 2B`. By `norm_exp_planeKernel_num` (with `α = c`), `‖exp(2c(ζ̄z−|ζ|²))‖ = e^{c|z|² − c|ζ|²} e^{−c|z−ζ|²}`. Multiplying, the `±c|·|²` terms cancel:

     `‖H z ζ‖ ≤ C_P² e^{2B} e^{φ z − φ ζ} e^{−c|z−ζ|²}`.

### 3.7 `theorem1`

Take `H, c, A` from §3.6 and `C := (A √(π/c)).toNNReal`. For admissible `f`, M10's `plane_kernel_operator` (with `continuousOn_univ.1 hφ.continuousOn`) gives, for `u := fun z ↦ ∫ ζ, H z ζ/(π(z−ζ)) * f ζ`, both `IsWeakDbarSol univ u f` and the `L^p` bound for every `p ∈ [1,∞]` with this `C`.

**Admissibility** is as in M11 §5, with `ν = volume` and `F = f e^{−φ}`.
- `TF = ∫ G_c(·−ζ)|F(ζ)| dm(ζ) ∈ L^{p₀}` by Schur, with constant `π√(π/c)`.
- So the integral defining `u` converges absolutely for a.e. `z`, `u ∈ L¹_loc` (Hölder on compacts), and `f = F e^{φ} ∈ L¹_loc`.

### 3.8 `theorem1_christ`

`theorem1 φ μ hφ hd.isLocallyDoubling hm`.

### 3.9 `prop1`

Take `H, c, A` from §3.6 and define

`k z ζ := (Real.exp (φ ζ − φ z) : ℂ) * (H z ζ / ((π : ℂ) * (z − ζ)))`,  `ε := c`,  `C := A/π`.

- **Measurability.** `φ` is continuous (`continuousOn_univ.1 hφ.continuousOn`), so `(z,ζ) ↦ exp(φ ζ − φ z)` is continuous. `H` is measurable and `(z,ζ) ↦ (z−ζ)⁻¹` is measurable. Hence `Measurable (uncurry k)`.
- **Bound.** For every `z, ζ` with `z ≠ ζ`,

  `‖k z ζ‖ = e^{φ ζ − φ z} ‖H z ζ‖/(π‖z−ζ‖) ≤ (A/π) e^{−c‖z−ζ‖²}/‖z−ζ‖`

  (`norm_mul`, `Complex.norm_real`, `Real.exp_add`, and `e^{a}e^{−a} = 1`). It holds for all pairs, not just a.e., because the multiplier bounds of `prop2_plane_full` are pointwise.
- **Solution.** For admissible `f`, `(exp(φ z − φ ζ) : ℂ) * k z ζ * f ζ = H z ζ/(π(z−ζ)) * f ζ`, since `↑(e^{a})·↑(e^{−a}) = 1` (`← Complex.ofReal_mul`, `← Real.exp_add`, `add_neg_cancel`/`sub_add_sub_cancel`). So the function in `prop1` is equal (`funext` + `integral_congr`) to the `u` of §3.7, and `IsWeakDbarSol` follows from `plane_kernel_operator`.

### 3.10 `thm1H_eq_zero_of_zero`

- The sum collapses to its `i`-th term (`Finset.sum_eq_single`; for `j ≠ i`, `ζ ∉ Ω j` by uniqueness).
- That term is `h i z / h i ζ = 0 / h i ζ = 0` (`zero_div`).
- Hence `thm1H … = 0 * exp(…) = 0`.

---

## 4. Interface

**Consumed.**
- `lemma6_plane` (M04) and `prop2_plane_full` (M09), in the form of §2.1.
- From M11: `Measure.exists_add_eq_of_le`, `IsSubharmonicWeight.sigmaFinite`, `exists_measurable_partition`.
- From M10: `plane_kernel_operator`, `norm_exp_planeKernel_num`.
- From M01: `integral_mul_lap`, `lap_const_mul_normSq`, `laplacian_eq_four_mul_lap`, `volume_ball_complex`.

**If M04 states Lemma 6 with `1 ≤`**, step 1 of §3.4 is unnecessary. If it uses `1 <`, step 1 adapts the hypothesis.

**Exported.**
- `theorem1`, `theorem1_christ`, `prop1` (comparator);
- `exists_plane_solution_kernel`, available to M13/M14 if a kernel representation is useful there;
- `two_le_measure_ball_three_mul` and `IsLocallyDoubling.of_le_of_le` (general).

---

## 5. Issues found (for NOTEBOOK)

1. **p. 374, the Lemma 8 exponent is inconsistent with `ψ`.** With `ψ = φ − (ε/2)|z|²` the kernel must be `e^{ε(ζ̄z−|ζ|²)}`, i.e. Lemma 8 with `α = ε/2`, not `e^{2ε(ζ̄z−|ζ|²)}`. As printed, the conjugated kernel contains `e^{εRe(ζ̄(z−ζ))}` and both Schur integrals diverge. With the matching exponent, `|κ'| ≲ e^{φ(z)−φ(ζ)}e^{−(ε/2)|z−ζ|²}/|z−ζ|`.
2. **p. 374, normalisation of `Δ`.** `ψ = φ − (ε/2)|z|²` keeps `Δψ ≥ ε/2` only for `Δ = ∂∂̄`. With the standard Laplacian (the paper's convention elsewhere, `Δ log|z| = 2πδ`) one needs `ψ = φ − c|z|²` with `c ≤ ε/8`.
3. **p. 359, Proposition 1: `≃` is false; only `≲` holds.**
   - The constructed kernel vanishes at `(λ, ζ)` with `h_i(λ) = 0`, `ζ ∈ Ω_i`. Such pairs exist, since each multiplier has zeros (§1.2).
   - Heuristically, no kernel at all can satisfy the two-sided bound for `φ = |z|⁴`.
   - The same applies to "`|κ'| ≃ …`" on p. 374.
4. **pp. 356–357, Theorem 1 in the locally doubling form.**
   - The proof needs only local doubling, as the paper says on p. 357. `theorem1_christ` is a corollary.
   - The mass hypothesis `Δφ(D) ≥ 1` (Theorem 1) versus `> 1` (Lemma 6, Proposition 2) is harmless (§1.3).
5. **The proof needs `|h_i| ≲ e^ψ` on all of `ℂ`.** The fixed `prop2_plane` does not provide it. M09 must export `prop2_plane_full` (same issue as M11 §8.2 item 7).
