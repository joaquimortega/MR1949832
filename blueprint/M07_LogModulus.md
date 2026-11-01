# M07 — Holomorphic functions with prescribed log-modulus

**Paper.** §3, p. 366: "Now we take a holomorphic function `h` that vanishes at all the points `{λ_j^i}` … This function is defined up to a factor of the form `e^g`, with `g ∈ H(Ω)`. We choose this `g` in such a way that `log|h| = ψ − (1/2π)∫ log|z−ζ| (Δψ − Σ δ_{λ_j^i})` (in `ℂ`), resp. with kernel `log|(z−ζ)/(1−ζ̄z)|` (in `𝔻`)."

**Lean file.** `OrtegaCerdaMultipliers/LogModulus.lean` (proof of concept, ~470 lines, **no `sorry`**). It imports only `Mathlib` and `OrtegaCerdaMultipliers.Defs`. It is not yet in the root import file.
- The axioms are `propext`, `Classical.choice` and `Quot.sound`, checked with `#print axioms` on all five main declarations.
- The weak form takes the two M02 results as hypotheses, as `Prop`s (see §4). When M02 exists, replace them by the M02 theorems.

**Depends on:**
- Mathlib only, for the core (§2);
- M02 (Weyl for `Δ`, log kernel), for the weak form (§3).

M01 is not needed. The primitive comes from Mathlib's `HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`, which itself uses `DifferentiableOn.isExactOn_ball`.

**Used by:**
- M08 (Theorem 4 in `𝔻` and `ℂ`);
- M09 (Proposition 2, zeros moved to `κ(R)`);
- M13 (Theorem 5).

## 0. Mathlib API used

| Purpose | Declaration | File |
|---|---|---|
| harmonic | `InnerProductSpace.HarmonicAt f x := ContDiffAt ℝ 2 f x ∧ Δ f =ᶠ[𝓝 x] 0`; `HarmonicOnNhd f s := ∀ x ∈ s, HarmonicAt f x` (`Δ = Laplacian.laplacian`, standard) | `Analysis/InnerProductSpace/Harmonic/Basic.lean` |
| locality | `harmonicAt_congr_nhds`, `HarmonicAt.sub`, `HarmonicOnNhd.continuousOn` | same |
| `log|f|` harmonic | `AnalyticAt.harmonicAt_log_norm (hf : AnalyticAt ℂ f z) (h : f z ≠ 0)` | `…/Harmonic/Constructions.lean` |
| harmonic = Re holomorphic | `HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` (ball, `R : ℝ`), `…_univ_re_eq` | `Analysis/Complex/Harmonic/Analytic.lean` |
| max modulus | `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` | `Analysis/Complex/AbsMax.lean` |
| identity theorem | `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` | `Analysis/Analytic/Uniqueness.lean` |
| orders | `AnalyticAt.analyticOrderAt_eq_natCast` (witness form `f =ᶠ (·−z₀)^n • g`, `g z₀ ≠ 0`), `analyticOrderAt_congr` | `Analysis/Analytic/Order.lean` |
| products | `Finset.analyticAt_fun_prod`, `Finset.mul_prod_erase`, `Real.log_prod` | — |
| weak → strong | `Measure.eqOn_open_of_ae_eq`, `LocallyIntegrable.integrable_smul_right_of_hasCompactSupport`, `laplacian_eq_iteratedFDeriv_complexPlane`, `tsupport_iteratedFDeriv_subset` | — |
| a point off `Λ` | `Set.Countable.dense_compl ℂ` | `Topology/Algebra/Module/Cardinality.lean` |

Mathlib has **no** Weierstrass product or "function with prescribed divisor" theorem. `Analysis/Meromorphic/Divisor.lean` only computes divisors of given functions. Hence the gluing below.

## 1. Statements (Lean, namespace `OC`)

These are verbatim from `LogModulus.lean`, which compiles. Proofs are omitted; `WeylLaplacianStmt` and `LogKernelStmt` are in §4.

```lean
/-- The local polynomial `∏_{ζ ∈ F} (z - ζ)^{n ζ}`. -/
def zeroProd (n : ℂ → ℕ) (F : Finset ℂ) (z : ℂ) : ℂ := ∏ ζ ∈ F, (z - ζ) ^ n ζ

/-- Ball-wise hypothesis: on every ball `ball c r` with `closedBall c r ⊆ Ω`,
`v = u + log |∏_{ζ∈F} (z-ζ)^{n ζ}|` off `supp n`, with `u` harmonic and `F ⊇ ball c r ∩ supp n`. -/
def LogModulusBallwise (Ω : Set ℂ) (c : ℂ) (n : ℂ → ℕ) (v : ℂ → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → closedBall c r ⊆ Ω → ∃ F : Finset ℂ, (∀ z ∈ ball c r, n z ≠ 0 → z ∈ F) ∧
    ∃ u : ℂ → ℝ, HarmonicOnNhd u (ball c r) ∧
      ∀ z ∈ ball c r, n z = 0 → v z = u z + Real.log ‖zeroProd n F z‖

/-- Main theorem.  `Ω` is a union of closed balls centred at `c` (covers `ball c R` and `univ`). -/
theorem exists_analytic_norm_eq_exp {Ω : Set ℂ} {c : ℂ}
    (hΩ : ∀ z ∈ Ω, ∃ r, dist z c < r ∧ closedBall c r ⊆ Ω)
    {n : ℂ → ℕ} {v : ℂ → ℝ} (hball : LogModulusBallwise Ω c n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω ∧ (∀ z ∈ Ω, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z ∈ Ω, analyticOrderAt h z = n z

theorem exists_analytic_norm_eq_exp_univ {n : ℂ → ℕ} {v : ℂ → ℝ}
    (hball : LogModulusBallwise univ 0 n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h univ ∧ (∀ z, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z, analyticOrderAt h z = n z
theorem exists_analytic_norm_eq_exp_ball {c : ℂ} {R : ℝ} {n : ℂ → ℕ} {v : ℂ → ℝ}
    (hball : LogModulusBallwise (ball c R) c n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball c R) ∧
      (∀ z ∈ ball c R, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z ∈ ball c R, analyticOrderAt h z = n z
theorem exists_analytic_norm_eq_exp_disc {n : ℂ → ℕ} {v : ℂ → ℝ}
    (hball : LogModulusBallwise 𝔻 0 n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h 𝔻 ∧ (∀ z ∈ 𝔻, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z ∈ 𝔻, analyticOrderAt h z = n z

/-- Steps 1–2 (one ball). -/
theorem exists_on_ball {c : ℂ} {r : ℝ} {n : ℂ → ℕ} {v : ℂ → ℝ} (F : Finset ℂ)
    (hF : ∀ z ∈ ball c r, n z ≠ 0 → z ∈ F) (u : ℂ → ℝ) (hu : HarmonicOnNhd u (ball c r))
    (hv : ∀ z ∈ ball c r, n z = 0 → v z = u z + Real.log ‖zeroProd n F z‖)
    {p : ℂ} (hp : p ∈ ball c r) (hnp : n p = 0) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball c r) ∧
      (∀ z ∈ ball c r, n z = 0 → ‖H z‖ = Real.exp (v z)) ∧
      (∀ a ∈ ball c r, analyticOrderAt H a = n a) ∧ H p = (Real.exp (v p) : ℂ)

/-- Step 3 (uniqueness up to the value at one point), exported. -/
theorem eqOn_of_norm_eq {c p : ℂ} {r : ℝ} {n : ℂ → ℕ} {v : ℂ → ℝ} {H₁ H₂ : ℂ → ℂ}
    (F : Finset ℂ) (hF : ∀ z ∈ ball c r, n z ≠ 0 → z ∈ F)
    (h₁ : AnalyticOnNhd ℂ H₁ (ball c r)) (h₂ : AnalyticOnNhd ℂ H₂ (ball c r))
    (hn₁ : ∀ z ∈ ball c r, n z = 0 → ‖H₁ z‖ = Real.exp (v z))
    (hn₂ : ∀ z ∈ ball c r, n z = 0 → ‖H₂ z‖ = Real.exp (v z))
    (hp : p ∈ ball c r) (hnp : n p = 0) (hH : H₁ p = H₂ p) :
    EqOn H₁ H₂ (ball c r)

/-- Test functions (helper for §3b). -/
lemma laplacian_testFunction {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    Continuous (Laplacian.laplacian χ) ∧ tsupport (Laplacian.laplacian χ) ⊆ tsupport χ

/-- Alternative entry point: the pointwise hypothesis. -/
structure LogModulusLocal (Ω : Set ℂ) (n : ℂ → ℕ) (v : ℂ → ℝ) : Prop where
  finite_support : ∀ K ⊆ Ω, IsCompact K → (K ∩ Function.support n).Finite
  local_harmonic : ∀ a ∈ Ω, ∃ ε > 0, ∃ u : ℂ → ℝ, HarmonicOnNhd u (ball a ε) ∧
    ∀ z ∈ ball a ε, n z = 0 → v z = u z + n a * Real.log ‖z - a‖
theorem LogModulusLocal.ballwise {Ω : Set ℂ} {n : ℂ → ℕ} {v : ℂ → ℝ}
    (hd : LogModulusLocal Ω n v) (c : ℂ) : LogModulusBallwise Ω c n v

/-- Weak entry point (the one M08 uses). -/
structure IsWeakLogModulus (Ω : Set ℂ) (n : ℂ → ℕ) (v : ℂ → ℝ) : Prop where
  finite_support : ∀ K ⊆ Ω, IsCompact K → (K ∩ Function.support n).Finite
  locallyIntegrableOn : LocallyIntegrableOn v Ω
  continuousOn : ContinuousOn v (Ω \ Function.support n)
  laplacian_eq : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
    ∫ z, v z * Laplacian.laplacian χ z = 2 * Real.pi * ∑ᶠ ζ, (n ζ : ℝ) * χ ζ
theorem IsWeakLogModulus.ballwise (hweyl : WeylLaplacianStmt) (hker : LogKernelStmt)
    {Ω : Set ℂ} {n : ℂ → ℕ} {v : ℂ → ℝ} (hd : IsWeakLogModulus Ω n v) (c : ℂ) :
    LogModulusBallwise Ω c n v
theorem exists_analytic_norm_eq_exp_of_weak (hweyl : WeylLaplacianStmt) (hker : LogKernelStmt)
    {Ω : Set ℂ} {c : ℂ} (hΩ : ∀ z ∈ Ω, ∃ r, dist z c < r ∧ closedBall c r ⊆ Ω)
    {n : ℂ → ℕ} {v : ℂ → ℝ} (hd : IsWeakLogModulus Ω n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω ∧ (∀ z ∈ Ω, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z ∈ Ω, analyticOrderAt h z = n z
```

**Reading the conclusion.**
- `‖h z‖ = e^{v z}` off `Λ := supp n` is an exact equality, with no additive constant.
- It also gives `h z ≠ 0` off `Λ`.
- `analyticOrderAt h a = n a` gives the zeros with multiplicity: `h a = 0 ↔ n a ≠ 0` by `analyticOrderAt_eq_zero`.
- **Uniqueness:** `h` is unique up to a unimodular constant (`eqOn_of_norm_eq` on balls).

**Why `n : ℂ → ℕ` and not a list of points.** The quadrature nodes repeat: each node of Lemma 5 carries weight `m`, and nodes of neighbouring rectangles may coincide since they lie *near* `R`, not inside it. M08 must therefore *define* `n λ := #{(i,j) : λ_j^i = λ}`, a counting function.

**Why not a hypothesis "`v − Σ n log|z−λ|` is harmonic".** In Lean `log 0 = 0`, so that function has junk values on `Λ`. All hypotheses therefore constrain `v` only **off `supp n`**, and the harmonic part `u` is a separate function.

## 2. Proof of the core theorem (`exists_analytic_norm_eq_exp`)

Fix `Ω`, `c`, `n`, `v` as in the statement. If `Ω = ∅`, take `h = 0`. Otherwise:

**Step 0 (base point).**
- Take `z₀ ∈ Ω`, and `r₀ > dist z₀ c` with `closedBall c r₀ ⊆ Ω`.
- `hball r₀` gives a finite `F₀ ⊇ ball c r₀ ∩ supp n`.
- A countable set has dense complement in `ℂ` (`Set.Countable.dense_compl ℂ`). So there is `p ∈ ball c r₀ \ F₀`, and then `n p = 0` and `p ∈ Ω`.

Call `r` *admissible* if `0 < r`, `dist p c < r` and `closedBall c r ⊆ Ω`.

**Step 1 (one ball: the harmonic part is `Re G`).** Let `r` be admissible, with `F`, `u` from `hball r`.
- Since `u` is harmonic on `ball c r`, Mathlib gives `G` analytic on `ball c r` with `Re G = u` there (`exists_analyticOnNhd_ball_re_eq`).
- Put `P := zeroProd n F`, a polynomial, and `H₀ := exp(G) · P`.
- For `z ∈ ball c r` with `n z = 0`:
  - `P z ≠ 0`, since each factor `(z−ζ)^{n ζ}` is `1` if `ζ = z` (as `n z = 0`) and nonzero otherwise;
  - hence `|H₀ z| = e^{u z} |P z| = e^{u z + log|P z|} = e^{v z}`.

**Step 2 (normalisation and orders).**
- `|H₀ p| = e^{v p} > 0`. Put `k := e^{v p}/H₀(p)`, so `|k| = 1`, and `H := k·H₀`.
- Then `H` is analytic on `ball c r`, `|H| = e^v` off `supp n`, and `H(p) = e^{v p}` (a positive real).
- **Orders.** For `a ∈ ball c r`: `P(z) = (z−a)^{n a} · zeroProd n (F.erase a) z`.
  - If `a ∈ F`, this is `Finset.mul_prod_erase`.
  - If `a ∉ F`, then `n a = 0` and `F.erase a = F`.
  - So `H = (z−a)^{n a} · g` with `g := k·exp(G)·zeroProd n (F.erase a)`, which is analytic with `g a ≠ 0`. Hence `analyticOrderAt H a = n a` by the witness form `AnalyticAt.analyticOrderAt_eq_natCast`.

This is `exists_on_ball`.

**Step 3 (compatibility).** Let `r ≤ r'` both be admissible, with local solutions `H_r`, `H_{r'}`. Claim: `H_r = H_{r'}` on `ball c r`. (`eqOn_of_norm_eq`, applied with the `F` of radius `r`.)
- **A zero-free disc.** `U := ball c r \ (F \ {p})` is open and contains `p`. On `U` we have `n = 0`: if `n z ≠ 0` then `z ∈ F`, and `z ≠ p` because `n p = 0`. Pick `δ` with `ball p δ ⊆ U`.
- **The quotient.** On `ball p δ`, `q := H_r / H_{r'}` is holomorphic, since `|H_{r'}| = e^v ≠ 0`. It satisfies `|q| ≡ 1` and `q(p) = 1`.
- **Maximum modulus.** `|q|` attains its maximum at the interior point `p`, so `q ≡ q(p) = 1` on `ball p δ` (`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`). Hence `H_r =ᶠ[𝓝 p] H_{r'}`.
- **Identity theorem.** On the connected `ball c r`, this gives `H_r = H_{r'}` on `ball c r`.

**Step 4 (gluing).**
- *Choice of radii.* For each admissible `r`, choose `H r` (a non-dependent `choose`, with a junk witness `0` when `r` is not admissible). For `z ∈ Ω` choose an admissible `R z > dist z c`, namely `max r₁ r₂` with `r₁, r₂` from `hΩ` at `z` and at `p`; `max_choice` gives `closedBall c (R z) ⊆ Ω`.
- *Definition.* `h z := H (R z) z`.
- *Local agreement.* For `w ∈ ball c (R z)` (a neighbourhood of `z`): `w ∈ ball c (R w) ∩ ball c (R z)`, and Step 3 applied to `min(R w, R z) ≤ max(R w, R z)` gives `h w = H (R z) w`. So `h =ᶠ[𝓝 z] H (R z)`.
- *Conclusions.*
  - `h` is analytic at `z` (`AnalyticAt.congr`);
  - `|h z| = |H (R z) z| = e^{v z}` if `n z = 0`;
  - `analyticOrderAt h z = analyticOrderAt (H (R z)) z = n z` (`analyticOrderAt_congr`).

**Corollaries.**
- `ℂ`: take `c = 0` and `r = dist z 0 + 1`.
- `ball c R`: take `r = (dist z c + R)/2`.
- `𝔻 = ball 0 1`: a special case of the ball.

## 3. Entry points: from the hypotheses M08 can check to `LogModulusBallwise`

### 3a. Pointwise (`LogModulusLocal.ballwise`, proved)

Given admissible `r`:
- **The finite set.** `F := (closedBall c r ∩ supp n).toFinset`, which is finite by `finite_support`.
- **The harmonic part.** Choose `ε_a`, `u_a` for each `a ∈ Ω` (`choose!`). Define
  `W(w) := u_w(w) − log|zeroProd n (F.erase w) w|`.
- **`W` is harmonic.** Fix `z ∈ ball c r`. For `w` near `z` we have `w ∈ ball c r ∩ ball z ε_z` and `w ∉ F \ {z}`, so `w = z` or `n w = 0`. For `w ≠ z`:
  - `W(w) = v(w) − log|P(w)|`, by the hypothesis at `a = w` and `n w = 0`;
  - `v(w) = u_z(w) + n z·log|w−z|`;
  - `log|P(w)| = n z·log|w−z| + log|zeroProd n (F.erase z) w|`.
  
  Hence `W =ᶠ[𝓝 z] u_z − log|zeroProd n (F.erase z) ·|`. This is harmonic at `z`, since `u_z` is harmonic and the product is analytic and nonzero at `z` (`AnalyticAt.harmonicAt_log_norm`).
- **The identity.** For `n z = 0`: `v z = u_z(z) = W(z) + log|P(z)|`.

### 3b. Weak (`IsWeakLogModulus.ballwise`, proved modulo the M02 statements)

Given admissible `r`, let `F` be as in 3a, `L := Σ_{ζ∈F} n ζ · log|z−ζ|` and `f := v − L`.
1. **Local integrability.** `f ∈ L¹_loc(ball c r)`, by `locallyIntegrableOn` and `L¹_loc` of `log|·−ζ|` (M02).
2. **`f` is weakly harmonic.** For a test `χ` with `tsupport χ ⊆ ball c r`:
   - `Δχ` is continuous and `tsupport Δχ ⊆ tsupport χ` (`laplacian_testFunction`, proved here from `laplacian_eq_iteratedFDeriv_complexPlane`);
   - hence `vΔχ` and `log|·−ζ|Δχ` are integrable;
   - `∫ fΔχ = 2π Σᶠ n χ − Σ_{ζ∈F} n ζ · 2πχ(ζ) = 0`. The finsum equals the sum over `F` because `supp(nχ) ⊆ supp n ∩ ball c r ⊆ F`.
3. **Weyl.** Weyl for `Δ` (M02) gives `u` harmonic on `ball c r` with `f = u` a.e. there.
4. **From a.e. to everywhere.** `f` and `u` are continuous on the open set `ball c r \ F` (on which `n = 0`), so `f = u` there (`Measure.eqOn_open_of_ae_eq`). For `z ∈ ball c r` with `n z = 0` we have `z ∉ F`, and `L z = log|zeroProd n F z|` (`Real.log_prod`). Hence `v z = u z + log|P z|`.

## 4. Interface to M02

M07 takes these as hypotheses (`Prop` definitions in `LogModulus.lean`). M02 must prove them, and then `exists_analytic_norm_eq_exp_of_weak` loses the two arguments.

```lean
/-- Weyl's lemma for Δ. -/
def WeylLaplacianStmt : Prop :=
  ∀ U : Set ℂ, IsOpen U → ∀ f : ℂ → ℝ, LocallyIntegrableOn f U →
    (∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0) →
    ∃ u : ℂ → ℝ, HarmonicOnNhd u U ∧ ∀ᵐ z ∂(volume.restrict U), f z = u z

/-- The logarithmic kernel: L¹_loc and Δ log|z − a| = 2π δ_a weakly. -/
def LogKernelStmt : Prop :=
  ∀ a : ℂ, LocallyIntegrable (fun z ↦ Real.log ‖z - a‖) ∧
    ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      ∫ z, Real.log ‖z - a‖ * Laplacian.laplacian χ z = 2 * Real.pi * χ a
```

Weyl for `Δ` only needs to hold on balls (`U = ball c r`). The M02 proof can mollify, use the mean-value property, and apply Mathlib's `HarmonicOnNhd` (`ContDiffAt ℝ 2` plus `Δ = 0` near each point).

### 4a. Interface (reconciled)

`LogModulus.lean` is unchanged. It is proved, and it is now in the root import. The new file `LogModulusWeak.lean` imports it together with M02 and discharges the two hypotheses. Its proofs are terms over the M02 lemmas:
- `weylLaplacian` comes from `exists_harmonicOnNhd_ae_eq_of_weakHarmonic`, M02's `L¹_loc` Weyl lemma. That lemma has exactly the body of `WeylLaplacianStmt`.
- `logKernel` comes from `locallyIntegrable_log_norm_sub` and `integral_log_norm_sub_mul_laplacian`.

M08 and M13 call the unconditional entry point.

```lean
/-- **M02 → M07: Weyl's lemma for `Δ`** (from `exists_harmonicOnNhd_ae_eq_of_weakHarmonic`). -/
theorem weylLaplacian : WeylLaplacianStmt
/-- **M02 → M07: the logarithmic kernel** (from `locallyIntegrable_log_norm_sub` and
`integral_log_norm_sub_mul_laplacian`). -/
theorem logKernel : LogKernelStmt
/-- `IsWeakLogModulus.ballwise` without the M02 hypotheses. -/
theorem IsWeakLogModulus.logModulusBallwise {Ω : Set ℂ} {n : ℂ → ℕ} {v : ℂ → ℝ}
    (hd : IsWeakLogModulus Ω n v) (c : ℂ) : LogModulusBallwise Ω c n v
/-- **M07, weak form, unconditional**: the statement M08 and M13 call. -/
theorem exists_analytic_norm_eq_exp_of_isWeakLogModulus {Ω : Set ℂ} {c : ℂ}
    (hΩ : ∀ z ∈ Ω, ∃ r, dist z c < r ∧ closedBall c r ⊆ Ω)
    {n : ℂ → ℕ} {v : ℂ → ℝ} (hd : IsWeakLogModulus Ω n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω ∧ (∀ z ∈ Ω, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z ∈ Ω, analyticOrderAt h z = n z
```

## 5. Interface to M08 (Theorem 4): verifying `IsWeakLogModulus Ω n v`

M08 calls `exists_analytic_norm_eq_exp_of_weak`:
- with `Ω = 𝔻`, `c = 0` and `hΩ` as in `_ball`;
- or with `Ω = univ`, `c = 0`.

The inputs are:
- `n λ :=` number of indices `(i,j)` with `λ_j^i = λ`;
- `v := ψ + S`, with `S(z) = Σ_i S_i(z)` and
  `S_i(z) := Σ_j log|z − λ_j^i| − (1/2π) ∫_{R_i} k(z,ζ) dμ(ζ)`;
- `k(z,ζ) = log|z−ζ|` in `ℂ`, and `k(z,ζ) = log|(z−ζ)/(1−ζ̄z)|` in `𝔻`.

The `2π Σ nδ` computation belongs to **M08**, which owns the partition, the nodes and the convergence of `S`. M07 owns only the bridge. M08 must prove the four fields:

1. **`finite_support`.**
   - The rectangles `R_i` are locally finite in `Ω` (M05).
   - The nodes of `R_i` lie within a bounded (hyperbolic) multiple of `R_i` (M06, Lemma 5 "near `R`").
   - So a compact `K ⊆ Ω` meets the node sets of only finitely many `i`, and each node set is finite.
2. **`locallyIntegrableOn`.**
   - `ψ` is continuous on `Ω`.
   - On a compact `K`, only finitely many `S_i` are not uniformly small; the tail converges uniformly on `K` (M08 estimate, via the moment conditions of Lemma 5).
   - Each `S_i` is `L¹_loc`: log terms by M02, and the potential of a finite measure by Fubini.
3. **`continuousOn` off `Λ`.** `ψ` is continuous, and the tail converges uniformly.
   - **Subtlety:** each potential `U_i(z) = (1/2π)∫_{R_i} log|z−ζ| dμ` must be continuous. This is true but not automatic.
   - Near `K ⊇ R_i`, write `ψ = U^{μ|_B} + harmonic` (`B` a ball; Weyl plus the kernel identity). Then `U^{μ|_B} = U_i + U^{μ|_{B∖R_i}}`.
   - The left side is continuous, and both summands are upper semicontinuous (Fatou). Hence each summand is also lower semicontinuous, i.e. continuous.
   - Put this lemma in M02 ("pieces of a measure with continuous potential have continuous potentials").
   - **Alternative**, if this is unwelcome: an a.e. variant of M07 (drop `continuousOn`, conclude `|h| = e^v` a.e.). This suffices for M08, because `|h|e^{-ψ}` is continuous, so a.e. bounds are everywhere bounds. It is not implemented.
4. **`laplacian_eq`.** For a test `χ`:
   - `∫ ψ Δχ = ∫ χ dμ` (`IsSubharmonicWeight.laplacian_eq`).
   - Interchange `Σ_i` and `∫` (uniform convergence on `supp χ`, finitely many singular terms).
   - `∫ log|z−λ| Δχ = 2πχ(λ)` (M02).
   - Fubini: `∫∫_{R_i} log|z−ζ| Δχ(z) dμ(ζ) dz = 2π ∫_{R_i} χ dμ`. The kernel is integrable since `sup_{ζ∈K'} ∫_K |log|z−ζ|| dz < ∞`.
   - In `𝔻`, the extra `log|1−ζ̄z|` is harmonic in `z ∈ 𝔻`, so `∫ log|1−ζ̄z| Δχ(z) dz = 0` (Green; M02).
   - `Σ_i ∫_{R_i} χ dμ = ∫ χ dμ`, because the rectangles partition `Ω` up to `μ`-null boundaries (M03, Lemma 2: segments, arcs and circles are null).
   - Total: `∫ vΔχ = 2π Σ_{i,j} χ(λ_j^i) = 2π Σᶠ_λ n(λ) χ(λ)`.

M08 then gets `h` holomorphic on `Ω` with zeros exactly at the `λ_j^i` (with multiplicity), and `|h| = e^{ψ+S}` off `Λ`. Estimates (2)–(3) are then bounds on `S` alone.

## 6. Subtleties

- **The `2π` normalisation (paper bug, see README §4).** With the standard `Δ`, `Δ log|z−λ| = 2πδ_λ`. The printed `log|h| = ψ − (1/2π)∫ log|z−ζ| (Δψ − Σδ)` gives `Δ log|h| = Σδ`, which is off by `2π`. The correct form is
  `log|h| = ψ − (1/2π)∫ log|z−ζ| dΔψ + Σ log|z−λ|`, i.e. point masses `2πδ`.
  - Consequently, the rectangle masses in Lemma 4 and the moments in Lemma 5 must be taken for `ν = μ/(2π)`: `#nodes in R_i = ν(R_i) = N` and `Σ_j (λ_j^i)^k = ∫_{R_i} ζ^k dν`. M05/M06 must use this normalisation.
  - In `IsWeakLogModulus` the factor is explicit: `2π Σᶠ n χ`.
- **Convergence.** `∫_ℂ log|z−ζ| dΔψ` does not converge in general. Only the grouped sum `Σ_i S_i` converges, thanks to the moment conditions. M07 never sees this: it only needs `v`.
- **Multiplicities.** These are handled by `n : ℂ → ℕ` and `analyticOrderAt`. The paper's "each `λ_j` appears with multiplicity `m`" is just `n = m` (or a multiple, when nodes coincide).
- **Exact equality.** `|h| = e^v` holds exactly, with no additive constant: the phase normalisation at `p` only fixes the unimodular ambiguity.
- **Domain generality.** One proof covers `ℂ` and `𝔻`, via "`Ω` is a union of closed balls centred at `c`". Mathlib's `exists_analyticOnNhd_ball_re_eq` takes `R : ℝ`, so the plane is handled by exhaustion, not by `…_univ_re_eq`.
- **Junk values.** `v` is constrained only off `supp n`, so `v(λ) = ψ(λ) + S(λ)`, with Lean's `log 0 = 0`, is irrelevant.

## 7. Status and remaining effort

- **Done (PoC, compiles, no `sorry`):** §2 completely; §3a; §3b modulo `WeylLaplacianStmt` and `LogKernelStmt`, both supplied as hypotheses.
- **To do:**
  - when M02 lands, discharge the two hypotheses (≈ 5 lines);
  - add the file to the root import;
  - M08's verification of `IsWeakLogModulus` (§5), including the continuity lemma for potentials of pieces of `μ` (M02);
  - optionally, the a.e. variant.
