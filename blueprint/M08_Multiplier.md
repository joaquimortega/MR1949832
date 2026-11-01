# M08 — Theorem 4: multipliers in `𝔻` and `ℂ`

**Lean files** (namespace `OC`):
- `OrtegaCerdaMultipliers/Multiplier/Defs.lean`: `lapNorm`, the quantitative classes, `IsCells`, `IsNodes`, kernels, `cellPot`, `multPot`, Taylor polynomials, `Thm4BoundsPlane/Disc`;
- `Multiplier/Kernel.lean`: Taylor remainders, polynomial form, moment cancellation, disc geometry;
- `Multiplier/Cells.lean`: near/far geometry of cells and nodes, local finiteness;
- `Multiplier/NearField.lean`: the area-counting near-field lemma (replaces Lemma 3) and the far-field sums;
- `Multiplier/Potential.lean`: convergence, continuity and Laplacian of `S` (the M07 fields);
- `Multiplier/Estimates.lean`: the corrected estimates (2), (3);
- `Multiplier/Nodes.lean`: node configurations from M06 (plane; disc with two regimes);
- `Multiplier/Theorem4.lean`: the core `multiplier_of_nodes_*`, `theorem4_*_quant`, `theorem4_*`.

**Paper:** Theorem 4 (p. 363), the Remark after it (p. 363), the construction and proof (pp. 365–369: "In order to construct the multiplier…" up to the end of the proof on p. 369).

**Depends on:**
- **M01:** pseudo-hyperbolic geometry (`hypDist_triangle`, `hypBall_eq_ball`, `div_five_le_tanh`, `pseudoHyp_mobius`, `norm_one_sub_conj_mul_*`), plus three small lemmas stated in §2.2 (`norm_sub_le_of_hypDist_le`, `norm_one_sub_conj_mul_comparable`, `convex_closedHypBall`). They can live in M01 or here.
- **M02:** `integral_log_norm_sub_mul_laplacian`, `integral_log_pseudoHyp_mul_laplacian`, `locallyIntegrable_log_norm_sub`; via M07, `WeylLaplacianStmt` and `LogKernelStmt`.
- **M03:** Claim 1, ball-mass bounds, decay of `ρ(ζ)/d(z,ζ)`, [Chr91, 2.3], growth, scaling of `ρ`. They are needed in **quantitative form** (constants depending only on `(C_d, R₀)`), see §4.2.
- **M04:** `logSmall_plane`, `logSmall_disc` (uniform smallness of the log-potential near the diagonal; for continuity of potentials). They could equally live in M03.
- **M05:** Lemma 4 (`IsMassPartition`), in quantitative form (§4.2).
- **M06:** `lemma5_moments` (proved).
- **M07:** `IsWeakLogModulus`, `exists_analytic_norm_eq_exp_of_weak` (`_univ`/`_disc` variants).
- **M10 or here:** the Forelli–Rudin bound `∫_𝔻 |1 − z̄w|^{-3} dm(w) ≲ (1 − |z|²)^{-1}`.
- **Mathlib:** `Complex.log_re`, `Complex.norm_log_sub_logTaylor_le` / `hasSum_taylorSeries_neg_log`, `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`, `Convex.integral_mem`, `integral_finsetSum`, `integral_tsum`, `TendstoLocallyUniformlyOn`, `tsum` API, `analyticOrderAt_eq_zero`, `ENNReal.ofReal_div_of_pos`.

Scratch file with every statement of M08 and M09 (stubs for M03/M05/M11 interfaces, proofs `sorry`): `scratchpad/m0809_check.lean`. **All typecheck**. `theorem4_disc` and `theorem4_plane` are *proved* there from the `_quant` versions. So are `prop2_disc`, `prop2_plane`, `prop2_disc_full` and `prop2_plane_full` from `prop2_*_quant` (M09).

---

## 0. The paper and what changes

**Theorem 4 (p. 363).** "Let `ψ` be a subharmonic function in `Ω` such that its Laplacian `Δψ` is a locally doubling measure, with the property `Δψ(D(z,R)) > 1` for all disks of some large radius `R > 0`. Then there is a holomorphic function `h` with zero set `Z(h) = Λ` such that `d(z,Λ)/ρ(z) ≲ |h(z)| e^{−ψ(z)} ≲ (d(z,Λ)/ρ(z))^M`."

**Remark (p. 363).** "It will follow from the construction of `h` that `d(z,Λ) ≲ ρ(z)`, thus `|h| ≃ e^ψ` outside `E_h = ∪_{λ∈Λ} D(λ, ερ(λ))`."

**The proof (pp. 365–369):**
1. Partition `Ω` into rectangles `R_i` of mass `N`.
2. In each, choose `N` points with the same moments `0..m−1` as `Δψ|_{R_i}` (Lemma 5).
3. Let `h` vanish exactly there, normalised by `log|h| = ψ − (1/2π)∫ log|z−ζ| (Δψ − Σδ)` (Green kernel in `𝔻`).
4. Prove (2)/(3): split into far rectangles (Taylor expansion and moment cancellation, then Lemma 3 for `δρ(z) ≤ |z−ζ| ≤ M` and Fubini for `|z−ζ| ≥ M`) and the near rectangles (`[Chr91, 2.3]` plus the finite node sum).

**What this module does differently** (each item is justified in §3 and recorded in §5):
- **Direction of the bounds.** The printed Theorem 4 has the two inequalities in the wrong order. With `d ≲ ρ`, `d/ρ ≲ (d/ρ)^M` is false for `M > 1`. We prove `(d/ρ)^M ≲ |h|e^{−ψ} ≲ d/ρ`, which is what `theorem4_*` state.
- **Sign in (2)/(3).** The printed middle term `I = ∫ log|z−ζ| (Δψ − Σδ)` must be replaced by `−I` (with `2π` on the point masses). We prove `M log(d/ρ) − C ≤ S(z) ≤ log(d/ρ) + C` for `S = log|h| − ψ`. In (3) the `+C` on the right is also missing.
- **`2π`.** We work with `ν := Δψ/(2π) = lapNorm μ`. Cells have `ν`-mass `N`, nodes match the moments of `ν|R_i`, and `Δ log|h| = 2π Σ δ_λ`.
- **Moment order 3, not the paper's `m` with `mγ > 1`.** Lemma 3 is replaced by an *area-counting near-field lemma* (§3.5). It works for every locally doubling measure (coordinator's design, verified here).
- **Disc: two regimes.** Small cells (`ρ(c_i) ≤ ρ₀`) get Lemma-5 nodes (order 3). Large cells get `N` copies of the barycentre (order 2). This keeps all nodes in `𝔻` for sparse `Δψ`, where the paper's construction breaks down (§5, item 6).
- **Disc far field by a first-order Taylor bound with remainder along segments,** not by power series, which may diverge for hyperbolically large cells.
- **"Near" is defined by distance to the cell centre in units of the cell radius,** not by "immediate neighbours". Nodes lie *near* `R_i`, not inside it (M06), so the paper's neighbour notion does not control them.
- **Constants are uniform** over the class `(C_d, R₀)` (needed by BOC through M11).

---

## 1. Conventions, normalisation and the order of constants

### 1.1 The class
`WeightClassPlane ψ μ Cd R₀` (resp. `…Disc`) bundles:
- `IsSubharmonicWeight univ ψ μ` (resp. `𝔻`);
- local doubling of `μ` with the explicit constant `Cd`;
- `1 < μ(B(z,R₀))` for all `z`;
- `μ` finite on compacts (resp. compacts of `𝔻`).

The fixed statements give `∃ Cd` (from `IsLocallyDoubling`) and `∃ R₀` (from `hm`), so they follow from the `_quant` versions in four lines (proved in the scratch file).

### 1.2 Normalisation
`ν := lapNorm μ = (2π)⁻¹ • μ`. Then:
- `IsSubharmonicWeight` gives `∫ ψ Δχ = ∫ χ dμ = 2π ∫ χ dν`.
- For a node multiset `Λ` with counting function `n`, `Δ(Σ log|z−λ|) = 2π Σ n(λ) δ_λ`.

So `v := ψ + S`, with `S = Σ_i [Σ_{λ∈Λ_i} k(z,λ) − ∫_{R_i} k(z,ζ) dν(ζ)]`, satisfies `Δv = 2π Σ n δ` (§3.8). This is exactly M07's `IsWeakLogModulus`.

Write `ρ̃ := massRadius ν` (resp. `massRadiusDisc ν`) and `ρ := massRadius μ`.
- `MeasClassPlane.lapNorm`: `ν` is in the class `(Cd, 15R₀)`. Doubling is scale-invariant. `B(z, 15R₀)` contains `8` disjoint balls `B(z + 2kR₀ e, R₀)`, `k = 0..7`, for a fixed unit `e` (in `𝔻`: points on a geodesic, `hypDist_triangle`). So `μ(B(z,15R₀)) > 8 > 2π`.
- `massRadius_lapNorm_quant`: `ρ ≤ ρ̃ ≤ C_ρ ρ`. Since `ν ≤ μ`, `ρ ≤ ρ̃`. Since `ν ≥ μ/7`, `ρ̃ ≤ massRadius(μ/7) ≤ Cρ` by M03 `massRadiusM_inv_smul` with `N = 7` and monotonicity of `massRadius` in the measure (an `sInf` over a smaller set).

All estimates are proved for `ρ̃` and converted to `ρ` at the very end (§3.11). This changes only constants.

### 1.3 Order in which constants are fixed (all depend only on `(Cd, R₀)`)
1. `m = 3`, `k = 4`, `N = 12` (M06 needs `k ≥ m`; `N` even is used for the disc `κ`, M09).
2. `R̃₀ := 15R₀` (class of `ν`) and the M03 constants for `(Cd, R̃₀)`.
3. M05: `a = η`, `A` (cells: `B(c_i, ηρ̃(c_i)) ⊆ R_i ⊆ B̄(c_i, Aρ̃(c_i))`).
4. Node spread `B` (`IsNodes`): plane `6A` for `λ`, `(B_κ+12)A` with `κ`; disc from `exists_nodes_disc`. The disc threshold is `ρ₀`.
5. `K₀ := 64(A + B + 1)` (near ⇔ `d(z,c_i) < K₀ ρ̃(c_i)`).
6. `δ` (non-near ⟹ `d(z,c_i) ≥ δ ρ̃(z)`), from Claim 1 with `K = K₀`.
7. `ρ₀' := min(ρ₀, 1/(8(A+B+1)))` and `M₀ := min(1/4, K₀ ρ₀')`, the near/far split.
8. The constants of §3.5–§3.9, then `M := N · M_c` and `C`.

---

## 2. Formal statements

### 2.1 Definitions

```lean
/-- `Δψ/(2π)`.  With this normalisation a zero of `h` contributes exactly one unit of mass:
`Δ log|h| = 2π Σ δ_λ` and `Δψ = 2π · lapNorm μ`. -/
def lapNorm (μ : Measure ℂ) : Measure ℂ := (ENNReal.ofReal (2 * Real.pi))⁻¹ • μ

/-- Local doubling with an explicit constant (plane). -/
def IsLocallyDoublingWith (μ : Measure ℂ) (Cd : ℝ≥0) : Prop :=
  ∀ z : ℂ, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball z (2 * r)) ≤ Cd * μ (ball z r)

/-- Local doubling with an explicit constant (disc, hyperbolic balls). -/
def IsLocallyDoublingDiscWith (μ : Measure ℂ) (Cd : ℝ≥0) : Prop :=
  ∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (hypBall z (2 * r)) ≤ Cd * μ (hypBall z r)

/-- The class of measures with parameters `(Cd, R₀)` (plane). -/
structure MeasClassPlane (ν : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocallyDoublingWith ν Cd
  mass : ∀ z : ℂ, 1 < ν (ball z R₀)
  finite : ∀ K : Set ℂ, IsCompact K → ν K < ∞

/-- The class of measures with parameters `(Cd, R₀)` (disc). -/
structure MeasClassDisc (ν : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocallyDoublingDiscWith ν Cd
  mass : ∀ z ∈ 𝔻, 1 < ν (hypBall z R₀)
  finite : ∀ K ⊆ 𝔻, IsCompact K → ν K < ∞

/-- The class of weights with parameters `(Cd, R₀)` (plane). -/
structure WeightClassPlane (ψ : ℂ → ℝ) (μ : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  weight : IsSubharmonicWeight univ ψ μ
  meas : MeasClassPlane μ Cd R₀

/-- The class of weights with parameters `(Cd, R₀)` (disc). -/
structure WeightClassDisc (ψ : ℂ → ℝ) (μ : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  weight : IsSubharmonicWeight 𝔻 ψ μ
  meas : MeasClassDisc μ Cd R₀

/-- Cells with centres `c i ∈ R i`; the cell radius is `ρ(c i)`. -/
structure IsCells (Ω : Set ℂ) (d : ℂ → ℂ → ℝ) (ρ : ℂ → ℝ) (ν : Measure ℂ) (N : ℕ) (η A : ℝ)
    (R : ℕ → Set ℂ) (c : ℕ → ℂ) : Prop where
  measurableSet : ∀ i, MeasurableSet (R i)
  pairwise_disjoint : Pairwise (Function.onFun Disjoint R)
  iUnion_eq : ⋃ i, R i = Ω
  center_mem : ∀ i, c i ∈ R i
  subset : ∀ i, ∀ w ∈ R i, d (c i) w ≤ A * ρ (c i)
  inner : ∀ i, {w | w ∈ Ω ∧ d (c i) w < η * ρ (c i)} ⊆ R i
  measure_eq : ∀ i, ν (R i) = N

/-- Node multisets: `N` nodes per cell, within `B ρ(c i)` of the centre, matching the complex
moments `0, …, m i − 1` of `ν|R i`. -/
structure IsNodes (Ω : Set ℂ) (d : ℂ → ℂ → ℝ) (ρ : ℂ → ℝ) (ν : Measure ℂ) (N : ℕ) (B : ℝ)
    (R : ℕ → Set ℂ) (c : ℕ → ℂ) (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ) : Prop where
  card : ∀ i, Multiset.card (Λ i) = N
  mem : ∀ i, ∀ w ∈ Λ i, w ∈ Ω
  near : ∀ i, ∀ w ∈ Λ i, d (c i) w ≤ B * ρ (c i)
  moments : ∀ i, ∀ j < m i, ∫ ζ in R i, ζ ^ j ∂ν = ((Λ i).map (· ^ j)).sum

/-- Multiplicity of `w` as a node. -/
def nodeCount (Λ : ℕ → Multiset ℂ) (w : ℂ) : ℕ := ∑ᶠ i, (Λ i).count w

/-- The set of all nodes. -/
def nodeSet (Λ : ℕ → Multiset ℂ) : Set ℂ := {w | ∃ i, w ∈ Λ i}

/-- Kernels: `log|z − ζ|` and the Green kernel `log |(z − ζ)/(1 − ζ̄ z)|`. -/
def kerPlane (z ζ : ℂ) : ℝ := Real.log ‖z - ζ‖
def kerDisc (z ζ : ℂ) : ℝ := Real.log (pseudoHyp ζ z)

/-- Potential of `Σ_{λ∈Λ i} δ_λ − ν|R i` at `z`. -/
def cellPot (k : ℂ → ℂ → ℝ) (ν : Measure ℂ) (R : ℕ → Set ℂ) (Λ : ℕ → Multiset ℂ) (i : ℕ)
    (z : ℂ) : ℝ :=
  ((Λ i).map (k z)).sum - ∫ ζ in R i, k z ζ ∂ν

/-- `S(z) = Σ_i cellPot i z`. -/
def multPot (k : ℂ → ℂ → ℝ) (ν : Measure ℂ) (R : ℕ → Set ℂ) (Λ : ℕ → Multiset ℂ) (z : ℂ) : ℝ :=
  ∑' i, cellPot k ν R Λ i z

/-- Taylor polynomial of degree `< m` of `ζ ↦ log|z − ζ|` at `c`. -/
def taylorPlane (m : ℕ) (z c ζ : ℂ) : ℝ :=
  Real.log ‖z - c‖ - (∑ k ∈ Finset.Ico 1 m, ((ζ - c) / (z - c)) ^ k / (k : ℂ)).re

/-- Taylor polynomial of degree `< m` of `ζ ↦ log|(z − ζ)/(1 − z̄ζ)|` at `c`. -/
def taylorDisc (m : ℕ) (z c ζ : ℂ) : ℝ :=
  Real.log (pseudoHyp c z) - (∑ k ∈ Finset.Ico 1 m,
    (((ζ - c) / (z - c)) ^ k - (conj z * (ζ - c) / (1 - conj z * c)) ^ k) / (k : ℂ)).re

/-- The conclusion of Theorem 4 (plane), plus the Remark `d(z,Λ) ≲ ρ(z)`. -/
def Thm4BoundsPlane (ψ : ℂ → ℝ) (μ : Measure ℂ) (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0) : Prop :=
  ∀ z : ℂ,
    C⁻¹ * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) ^ M ≤
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
      ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
        C * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) ∧
      edistSet z {w | h w = 0} ≤ C * ENNReal.ofReal (massRadius μ z)

/-- The conclusion of Theorem 4 (disc), plus the Remark `d(z,Λ) ≲ ρ(z)`. -/
def Thm4BoundsDisc (ψ : ℂ → ℝ) (μ : Measure ℂ) (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0) : Prop :=
  ∀ z ∈ 𝔻,
    C⁻¹ * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) ^ M ≤
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
      ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
        C * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) ∧
      hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} ≤ C * ENNReal.ofReal (massRadiusDisc μ z)
```

**Design notes.**
- **Cells indexed by `ℕ`.** M05 gives `R : ℕ → Set ℂ`. The radius of cell `i` is `ρ̃(c i)`; M05's `IsMassPartition` is converted by `IsMassPartition.exists_cells`, taking `c i` to be the centre of its inner ball.
- **`IsNodes.mem`.** In `𝔻` every node must lie in `𝔻`: a node `λ ∉ 𝔻` makes `log|(z−λ)/(1−λ̄z)|` singular at `1/λ̄ ∈ 𝔻`.
- **`m : ℕ → ℕ`, per cell.** This allows the disc's mixed orders.
- **Moments are complex Bochner integrals** over `R i`. They are genuine: `R i` is bounded and `ν(R i) = N < ∞`.
- **Junk values.** `kerPlane z z = log 0 = 0`. This is irrelevant: `ν{z} = 0` (M03, no atoms), and `cellPot` is only used for `z` off the nodes, or summed where the singular cells are finitely many. `multPot` is a `tsum`; we *prove* summability everywhere (§3.8), so its junk value 0 never occurs.
- **`Thm4Bounds*` contain the Remark** (`d(z,Λ) ≤ Cρ(z)`) as a third conjunct. M09 needs it.

### 2.2 Kernel lemmas (`Multiplier/Kernel.lean`)

```lean
theorem abs_kerPlane_sub_taylorPlane_le {m : ℕ} (hm : 1 ≤ m) {z c ζ : ℂ} (hzc : z ≠ c)
    (hζ : 2 * ‖ζ - c‖ ≤ ‖z - c‖) :
    |kerPlane z ζ - taylorPlane m z c ζ| ≤ 2 * (‖ζ - c‖ / ‖z - c‖) ^ m := sorry

theorem abs_kerDisc_sub_taylorDisc_le {m : ℕ} (hm : 1 ≤ m) {z c ζ : ℂ} (hz : z ∈ 𝔻)
    (hc : c ∈ 𝔻) (hzc : z ≠ c) (hζ : 2 * ‖ζ - c‖ ≤ ‖z - c‖) :
    |kerDisc z ζ - taylorDisc m z c ζ| ≤
      2 * (1 - ‖z‖ ^ 2) * ‖ζ - c‖ ^ m / (‖z - c‖ ^ m * ‖1 - conj z * c‖) := sorry

/-- First-order remainder along a segment (disc far field, no convergent series needed). -/
theorem abs_kerDisc_sub_taylorDisc_two_le {z c ζ : ℂ} (hz : z ∈ 𝔻) {Bd : ℝ}
    (hseg : ∀ ξ ∈ segment ℝ c ζ, ξ ∈ 𝔻 ∧ ξ ≠ z)
    (hB : ∀ ξ ∈ segment ℝ c ζ, 2 * (1 - ‖z‖ ^ 2) / (‖z - ξ‖ ^ 2 * ‖1 - conj z * ξ‖) ≤ Bd) :
    |kerDisc z ζ - taylorDisc 2 z c ζ| ≤ Bd * ‖ζ - c‖ ^ 2 := sorry

theorem exists_poly_taylorPlane {m : ℕ} (hm : 1 ≤ m) (z c : ℂ) :
    ∃ p : Polynomial ℂ, p.natDegree < m ∧ ∀ ζ, taylorPlane m z c ζ = (p.eval ζ).re := sorry

theorem exists_poly_taylorDisc {m : ℕ} (hm : 1 ≤ m) (z c : ℂ) :
    ∃ p : Polynomial ℂ, p.natDegree < m ∧ ∀ ζ, taylorDisc m z c ζ = (p.eval ζ).re := sorry

/-- Moment cancellation. -/
theorem cellPot_eq_sub_poly {ν : Measure ℂ} {R : ℕ → Set ℂ} {Λ : ℕ → Multiset ℂ} {i m : ℕ}
    (hR : MeasurableSet (R i)) (hfin : ν (R i) < ∞) (hb : Bornology.IsBounded (R i))
    (hmom : ∀ j < m, ∫ ζ in R i, ζ ^ j ∂ν = ((Λ i).map (· ^ j)).sum)
    {k : ℂ → ℂ → ℝ} {z : ℂ} (hint : IntegrableOn (k z) (R i) ν)
    {T : ℂ → ℝ} {p : Polynomial ℂ} (hp : p.natDegree < m) (hT : ∀ ζ, T ζ = (p.eval ζ).re) :
    cellPot k ν R Λ i z =
      ((Λ i).map fun w ↦ k z w - T w).sum - ∫ ζ in R i, (k z ζ - T ζ) ∂ν := sorry

/-- Euclidean/hyperbolic comparisons used in the disc (M01-type geometry). -/
theorem norm_sub_le_of_hypDist_le {c w : ℂ} (hc : c ∈ 𝔻) (hw : w ∈ 𝔻) {s : ℝ}
    (hs : hypDist c w ≤ s) (hs1 : Real.tanh s < 1) :
    ‖w - c‖ ≤ Real.tanh s / (1 - Real.tanh s) * (1 - ‖c‖ ^ 2) := sorry

theorem norm_one_sub_conj_mul_comparable {z c ξ : ℂ} (hz : z ∈ 𝔻) (hc : c ∈ 𝔻) (hξ : ξ ∈ 𝔻)
    {s : ℝ} (hs : hypDist c ξ ≤ s) :
    ‖1 - conj z * ξ‖ ≤ Real.exp (2 * s) * ‖1 - conj z * c‖ ∧
      ‖1 - conj z * c‖ ≤ Real.exp (2 * s) * ‖1 - conj z * ξ‖ := sorry

theorem convex_closedHypBall {c : ℂ} (hc : c ∈ 𝔻) (s : ℝ) :
    Convex ℝ {w | w ∈ 𝔻 ∧ hypDist c w ≤ s} := sorry

/-- Forelli–Rudin, the case used here (possibly from M10). -/
theorem integral_one_sub_conj_mul_rpow_neg_three_le :
    ∃ C : ℝ, ∀ z ∈ 𝔻,
      ∫⁻ w in 𝔻, ENNReal.ofReal (1 / ‖1 - conj z * w‖ ^ 3) ≤ ENNReal.ofReal (C / (1 - ‖z‖ ^ 2)) :=
  sorry
```

### 2.3 Cells (`Multiplier/Cells.lean`)

```lean
/-- From M05's partition to cells (`c i` = centre of the inner ball). -/
theorem IsMassPartition.exists_cells {ν : Measure ℂ} {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    {N : ℕ} {a A : ℝ} {R : ℕ → Set ℂ} (hP : IsMassPartition ν Ω d ρ N a A R) :
    ∃ c : ℕ → ℂ, IsCells Ω d ρ ν N a A R c := sorry

/-- Bounded number of near cells, near/far dichotomy for nodes (plane). -/
theorem cells_near_plane (Cd : ℝ≥0) (R₀ η A B K₀ : ℝ) (hη : 0 < η) (hK₀ : 2 * (A + B) ≤ K₀) :
    ∃ (Mc : ℕ) (δ C₃ : ℝ), 0 < δ ∧ 0 < C₃ ∧ ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ)
      (c : ℕ → ℂ) (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassPlane ν Cd R₀ → 1 ≤ N →
      IsCells univ dist (massRadius ν) ν N η A R c →
      IsNodes univ dist (massRadius ν) ν N B R c m Λ → ∀ z : ℂ,
        {i | dist z (c i) < K₀ * massRadius ν (c i)}.encard ≤ Mc ∧
        (∀ i, dist z (c i) < K₀ * massRadius ν (c i) →
          ∀ w ∈ R i ∪ {w | w ∈ Λ i}, dist z w ≤ C₃ * massRadius ν z) ∧
        (∀ i, K₀ * massRadius ν (c i) ≤ dist z (c i) →
          δ * massRadius ν z ≤ dist z (c i) ∧ ∀ w ∈ Λ i, δ * massRadius ν z ≤ 2 * dist z w) ∧
        (∃ i, z ∈ R i ∧ dist z (c i) < K₀ * massRadius ν (c i)) := sorry

/-- Local finiteness: a bounded set meets only finitely many enlarged cells. -/
theorem finite_cells_plane {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hν : MeasClassPlane ν Cd R₀) (hη : 0 < η)
    (hC : IsCells univ dist (massRadius ν) ν N η A R c) (K : Set ℂ)
    (hK : Bornology.IsBounded K) (L : ℝ) :
    {i | ∃ z ∈ K, dist z (c i) < L}.Finite := sorry

/-- Bounded number of near cells, near/far dichotomy for nodes (disc). -/
theorem cells_near_disc (Cd : ℝ≥0) (R₀ η A B K₀ : ℝ) (hη : 0 < η) (hK₀ : 2 * (A + B) ≤ K₀) :
    ∃ (Mc : ℕ) (δ C₃ : ℝ), 0 < δ ∧ 0 < C₃ ∧ ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ)
      (c : ℕ → ℂ) (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassDisc ν Cd R₀ → 1 ≤ N →
      IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ → ∀ z ∈ 𝔻,
        {i | hypDist z (c i) < K₀ * massRadiusDisc ν (c i)}.encard ≤ Mc ∧
        (∀ i, hypDist z (c i) < K₀ * massRadiusDisc ν (c i) →
          ∀ w ∈ R i ∪ {w | w ∈ Λ i}, hypDist z w ≤ C₃ * massRadiusDisc ν z) ∧
        (∀ i, K₀ * massRadiusDisc ν (c i) ≤ hypDist z (c i) →
          δ * massRadiusDisc ν z ≤ hypDist z (c i) ∧
            ∀ w ∈ Λ i, δ * massRadiusDisc ν z ≤ 2 * hypDist z w) ∧
        (∃ i, z ∈ R i ∧ hypDist z (c i) < K₀ * massRadiusDisc ν (c i)) := sorry

/-- Local finiteness (disc): a compact subset of `𝔻` meets only finitely many enlarged cells. -/
theorem finite_cells_disc {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hν : MeasClassDisc ν Cd R₀) (hη : 0 < η)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c) (K : Set ℂ) (hK𝔻 : K ⊆ 𝔻)
    (hK : IsCompact K) (L : ℝ) :
    {i | ∃ z ∈ K, hypDist z (c i) < L}.Finite := sorry
```

### 2.4 Near and far field (`Multiplier/NearField.lean`)

```lean
/-- **Area-counting near-field lemma (plane)** — replaces the paper's Lemma 3. -/
theorem nearField_sum_le_plane (Cd : ℝ≥0) (R₀ η A δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c → ∀ z : ℂ,
      ∀ F : Finset ℕ, (∀ i ∈ F, δ * massRadius ν z ≤ dist z (c i) ∧ dist z (c i) ≤ 1 / 4 ∧
          A * massRadius ν (c i) ≤ dist z (c i)) →
        ∑ i ∈ F, (massRadius ν (c i) / dist z (c i)) ^ 3 ≤ C := sorry

/-- **Area-counting near-field lemma (disc)**. -/
theorem nearField_sum_le_disc (Cd : ℝ≥0) (R₀ η A δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassDisc ν Cd R₀ → IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c → ∀ z ∈ 𝔻,
      ∀ F : Finset ℕ, (∀ i ∈ F, δ * massRadiusDisc ν z ≤ hypDist z (c i) ∧
          hypDist z (c i) ≤ 1 / 4 ∧ A * massRadiusDisc ν (c i) ≤ hypDist z (c i)) →
        ∑ i ∈ F, (massRadiusDisc ν (c i) / hypDist z (c i)) ^ 3 ≤ C := sorry

/-- Far field (plane). -/
theorem farField_sum_le_plane (Cd : ℝ≥0) (R₀ η A M₀ : ℝ) (hη : 0 < η) (hM₀ : 0 < M₀) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c → ∀ z : ℂ,
      ∀ F : Finset ℕ, (∀ i ∈ F, M₀ ≤ dist z (c i) ∧ 2 * A * massRadius ν (c i) ≤ dist z (c i)) →
        ∑ i ∈ F, (massRadius ν (c i) / dist z (c i)) ^ 3 ≤ C := sorry

/-- Far field (disc): the Forelli–Rudin sum. -/
theorem farField_sum_le_disc (Cd : ℝ≥0) (R₀ η A M₀ : ℝ) (hη : 0 < η) (hM₀ : 0 < M₀) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassDisc ν Cd R₀ → IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c → ∀ z ∈ 𝔻,
      ∀ F : Finset ℕ, (∀ i ∈ F, M₀ ≤ hypDist z (c i)) →
        ∑ i ∈ F, (1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
          ‖1 - conj z * c i‖ ^ 3 ≤ C := sorry
```

### 2.5 The potential `S` (`Multiplier/Potential.lean`)

```lean
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
```

### 2.6 The corrected estimates (2), (3) (`Multiplier/Estimates.lean`)

```lean
/-- Estimate (2), corrected: `M log(d/ρ) − C ≤ S(z) ≤ log(d/ρ) + C` off the nodes, and
`d(z, Λ) ≤ C ρ(z)` everywhere.  Here `ρ = massRadius (lapNorm μ)`. -/
theorem multPot_bounds_plane (Cd : ℝ≥0) (R₀ η A B : ℝ) (N : ℕ) (hη : 0 < η) (hA : 0 < A)
    (hB : 0 ≤ B) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ), 1 ≤ M ∧ 0 < C ∧ ∀ (μ : Measure ℂ) (R : ℕ → Set ℂ) (c : ℕ → ℂ)
      (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassPlane μ Cd R₀ →
      IsCells univ dist (massRadius (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes univ dist (massRadius (lapNorm μ)) (lapNorm μ) N B R c m Λ → (∀ i, 3 ≤ m i) →
      (∀ z, ∃ w ∈ nodeSet Λ, dist z w ≤ C * massRadius (lapNorm μ) z) ∧
      ∀ z, z ∉ nodeSet Λ → ∀ d : ℝ, (∀ w ∈ nodeSet Λ, d ≤ dist z w) →
        (∃ w ∈ nodeSet Λ, dist z w ≤ d) →
        M * Real.log (d / massRadius (lapNorm μ) z) - C ≤ multPot kerPlane (lapNorm μ) R Λ z ∧
        multPot kerPlane (lapNorm μ) R Λ z ≤ Real.log (d / massRadius (lapNorm μ) z) + C := sorry

/-- Estimate (3), corrected (disc, hyperbolic distance). -/
theorem multPot_bounds_disc (Cd : ℝ≥0) (R₀ η A B ρ₀ : ℝ) (N : ℕ) (hη : 0 < η) (hA : 0 < A)
    (hB : 0 ≤ B) (hρ₀ : 0 < ρ₀) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ), 1 ≤ M ∧ 0 < C ∧ ∀ (μ : Measure ℂ) (R : ℕ → Set ℂ) (c : ℕ → ℂ)
      (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassDisc μ Cd R₀ →
      IsCells 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N B R c m Λ →
      (∀ i, 2 ≤ m i) → (∀ i, massRadiusDisc (lapNorm μ) (c i) ≤ ρ₀ → 3 ≤ m i) →
      (∀ z ∈ 𝔻, ∃ w ∈ nodeSet Λ, hypDist z w ≤ C * massRadiusDisc (lapNorm μ) z) ∧
      ∀ z ∈ 𝔻, z ∉ nodeSet Λ → ∀ d : ℝ, (∀ w ∈ nodeSet Λ, d ≤ hypDist z w) →
        (∃ w ∈ nodeSet Λ, hypDist z w ≤ d) →
        M * Real.log (d / massRadiusDisc (lapNorm μ) z) - C ≤
            multPot kerDisc (lapNorm μ) R Λ z ∧
        multPot kerDisc (lapNorm μ) R Λ z ≤ Real.log (d / massRadiusDisc (lapNorm μ) z) + C :=
  sorry
```

### 2.7 Nodes (`Multiplier/Nodes.lean`)

```lean
/-- Nodes from Lemma 5 with `m = 3`, `k = 4`, `N = 12`; on cells with `sel i = true` the
alternative set `κ` (distance `≥ B·A·ρ(c i)` from the centre). -/
theorem exists_nodes_plane {ν : Measure ℂ} {η A : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ}
    (hC : IsCells univ dist (massRadius ν) ν 12 η A R c) (hA : 0 ≤ A) (B : ℝ) (hB : 0 ≤ B)
    (sel : ℕ → Bool) :
    ∃ Λ : ℕ → Multiset ℂ, IsNodes univ dist (massRadius ν) ν 12 ((B + 12) * A) R c (fun _ ↦ 3) Λ ∧
      (∀ i, sel i = false → ∀ w ∈ Λ i, dist (c i) w ≤ 6 * A * massRadius ν (c i)) ∧
      ∀ i, sel i = true → ∀ w ∈ Λ i, B * A * massRadius ν (c i) ≤ dist (c i) w := sorry

/-- Disc: small cells (`ρ(c i) ≤ ρ₀`) use Lemma 5 (order 3); large cells use `N` copies of the
barycentre (order 2), or, if selected, `6` copies each of `b ± v` (`v` tangential). -/
theorem exists_nodes_disc (A : ℝ) (hA : 0 < A) :
    ∃ Bl : ℝ, 0 ≤ Bl ∧ ∀ B : ℝ, 0 ≤ B → ∃ ρ₀ B' : ℝ, 0 < ρ₀ ∧ 0 ≤ B' ∧
      ∀ (ν : Measure ℂ) (η : ℝ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      IsCells 𝔻 hypDist (massRadiusDisc ν) ν 12 η A R c → (∀ i, 0 < massRadiusDisc ν (c i)) →
      ∀ sel : ℕ → Bool, ∃ (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ),
        IsNodes 𝔻 hypDist (massRadiusDisc ν) ν 12 B' R c m Λ ∧ (∀ i, 2 ≤ m i) ∧
        (∀ i, massRadiusDisc ν (c i) ≤ ρ₀ → 3 ≤ m i) ∧
        (∀ i, sel i = false → ∀ w ∈ Λ i, hypDist (c i) w ≤ Bl * massRadiusDisc ν (c i)) ∧
        ∀ i, sel i = true → ∀ w ∈ Λ i, B * A * massRadiusDisc ν (c i) ≤ hypDist (c i) w := sorry
```

### 2.8 Theorem 4 (`Multiplier/Theorem4.lean`)

```lean
/-- Core: multiplier from an arbitrary admissible node configuration (plane). -/
theorem multiplier_of_nodes_plane (Cd : ℝ≥0) (R₀ η A B : ℝ) (N : ℕ) (hR₀ : 0 < R₀)
    (hη : 0 < η) (hA : 0 < A) (hB : 0 ≤ B) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassPlane ψ μ Cd R₀ → ∀ (R : ℕ → Set ℂ) (c : ℕ → ℂ) (m : ℕ → ℕ)
      (Λ : ℕ → Multiset ℂ),
      IsCells univ dist (massRadius (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes univ dist (massRadius (lapNorm μ)) (lapNorm μ) N B R c m Λ → (∀ i, 3 ≤ m i) →
      ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ w, h w = 0 ↔ w ∈ nodeSet Λ) ∧
        (∀ w, analyticOrderAt h w = (nodeCount Λ w : ℕ∞)) ∧ Thm4BoundsPlane ψ μ h M C := sorry

/-- Core: multiplier from an arbitrary admissible node configuration (disc). -/
theorem multiplier_of_nodes_disc (Cd : ℝ≥0) (R₀ η A B ρ₀ : ℝ) (N : ℕ) (hR₀ : 0 < R₀)
    (hη : 0 < η) (hA : 0 < A) (hB : 0 ≤ B) (hρ₀ : 0 < ρ₀) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassDisc ψ μ Cd R₀ → ∀ (R : ℕ → Set ℂ) (c : ℕ → ℂ) (m : ℕ → ℕ)
      (Λ : ℕ → Multiset ℂ),
      IsCells 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N B R c m Λ →
      (∀ i, 2 ≤ m i) → (∀ i, massRadiusDisc (lapNorm μ) (c i) ≤ ρ₀ → 3 ≤ m i) →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h 𝔻 ∧ (∀ w ∈ 𝔻, h w = 0 ↔ w ∈ nodeSet Λ) ∧
        (∀ w ∈ 𝔻, analyticOrderAt h w = (nodeCount Λ w : ℕ∞)) ∧
        Thm4BoundsDisc ψ μ h M C := sorry

theorem theorem4_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassPlane ψ μ Cd R₀ →
        ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∃ z₀, h z₀ ≠ 0) ∧ Thm4BoundsPlane ψ μ h M C := sorry

theorem theorem4_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassDisc ψ μ Cd R₀ →
        ∃ h : ℂ → ℂ, DifferentiableOn ℂ h 𝔻 ∧ (∃ z₀ ∈ 𝔻, h z₀ ≠ 0) ∧
          Thm4BoundsDisc ψ μ h M C := sorry

/-- The fixed statement (comparator), from `theorem4_disc_quant`. -/
theorem theorem4_disc (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight 𝔻 ψ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z R)) :
    ∃ (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0), DifferentiableOn ℂ h 𝔻 ∧ (∃ z₀ ∈ 𝔻, h z₀ ≠ 0) ∧
      ∀ z ∈ 𝔻,
        C⁻¹ * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) ^ M ≤
          ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
          C * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) := by
  obtain ⟨R, hR, hmR⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  have hw : WeightClassDisc ψ μ Cd R :=
    ⟨hψ, ⟨fun z hz r hr h2 ↦ hCd z hz r hr h2, hmR, fun K hK hKc ↦ hψ.finite_of_compact K hK hKc⟩⟩
  obtain ⟨M, C, -, -, hall⟩ := theorem4_disc_quant Cd R hR
  obtain ⟨h, hh, hz₀, hb⟩ := hall ψ μ hw
  exact ⟨h, M, C, hh, hz₀, fun z hz ↦ ⟨(hb z hz).1, (hb z hz).2.1⟩⟩

/-- The fixed statement (comparator), from `theorem4_plane_quant`. -/
theorem theorem4_plane (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight univ ψ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 < μ (ball z R)) :
    ∃ (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0), Differentiable ℂ h ∧ (∃ z₀, h z₀ ≠ 0) ∧
      ∀ z : ℂ,
        C⁻¹ * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) ^ M ≤
          ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
          C * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) := by
  obtain ⟨R, hR, hmR⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  have hw : WeightClassPlane ψ μ Cd R :=
    ⟨hψ, ⟨fun z r hr h2 ↦ hCd z r hr h2, hmR,
      fun K hKc ↦ hψ.finite_of_compact K (subset_univ K) hKc⟩⟩
  obtain ⟨M, C, -, -, hall⟩ := theorem4_plane_quant Cd R hR
  obtain ⟨h, hh, hz₀, hb⟩ := hall ψ μ hw
  exact ⟨h, M, C, hh, hz₀, fun z ↦ ⟨(hb z).1, (hb z).2.1⟩⟩
```

**Count:** 19 definitions (6 of them structures) and 31 theorems (M08 proper), including the two fixed statements, plus the assumed interface lemmas of §4.1 (stubs). All typecheck; `theorem4_disc` and `theorem4_plane` are proved in the scratch file.

---
## 3. Proofs

Throughout, `ν = lapNorm μ`, `ρ̃ = massRadius ν` (plane) or `massRadiusDisc ν` (disc), and `d` is `dist` (plane) or `hypDist` (disc). Cell data `(R, c)` satisfy `IsCells … ν N η A R c`, and nodes `(m, Λ)` satisfy `IsNodes … ν N B R c m Λ`. "Cell `i` is **near** `z`" means `d(z, c_i) < K₀ ρ̃(c_i)`. Write `ρ_i := ρ̃(c_i)`.

### 3.1 Taylor remainders

**(K1) `abs_kerPlane_sub_taylorPlane_le`.** Let `w := (ζ − c)/(z − c)`, so `|w| ≤ 1/2`.
- `z − ζ = (z − c)(1 − w)`, hence `log|z − ζ| = log|z − c| + log|1 − w|`.
- `log|1 − w| = Re log(1 − w)` (`Complex.log_re`) `= −Re Σ_{k≥1} w^k/k` (`hasSum_taylorSeries_neg_log`, `|w| < 1`).
- So `kerPlane z ζ − taylorPlane m z c ζ = −Re Σ_{k≥m} w^k/k`.
- Its modulus is `≤ Σ_{k≥m} |w|^k/k ≤ |w|^m/(m(1−|w|)) ≤ 2|w|^m/m ≤ 2|w|^m`.

Mathlib's `Complex.norm_log_sub_logTaylor_le` (applied to `−w`) gives `‖log(1−w) + Σ_{k<m} w^k/k‖ ≤ |w|^m/(m(1−|w|))` directly. Note `logTaylor n` has signs `(−1)^{j+1}`; with argument `−w` they turn into `−w^j/j`.

**(K2) `abs_kerDisc_sub_taylorDisc_le`.** Write `kerDisc z ζ = log|z − ζ| − log|1 − z̄ζ|`. Here `pseudoHyp ζ z = |ζ − z|/|1 − ζ̄z|` and `|1 − ζ̄z| = |1 − z̄ζ|` (conjugate).
- **Factorisation.** `1 − z̄ζ = (1 − z̄c)(1 − w₂)` with `w₂ := z̄(ζ−c)/(1 − z̄c)`, and `z − ζ = (z−c)(1 − w₁)` with `w₁ := (ζ−c)/(z−c)`.
- **Size of `w₂`.** For `z, c ∈ 𝔻`, `|1 − z̄c|² − |z − c|² = (1 − |z|²)(1 − |c|²) > 0`, so `|z − c| ≤ |1 − z̄c|`. Hence `|w₂| ≤ |z||ζ−c|/|z−c| ≤ |w₁| ≤ 1/2`. Both series converge, and `1 − z̄ζ ≠ 0`.
- **The difference.** `kerDisc z ζ − taylorDisc m z c ζ = −Re Σ_{k≥m} (w₁^k − w₂^k)/k`.
  - `|w₁^k − w₂^k| ≤ k|w₁ − w₂| |w₁|^{k−1}`: telescoping `a^k − b^k = (a−b)Σ a^{k−1−j}b^j` with `|b| ≤ |a|`.
  - `w₁ − w₂ = (ζ − c)(1 − |z|²)/((z − c)(1 − z̄c))`, by direct algebra.
  - So the remainder is `≤ |w₁ − w₂| Σ_{k≥m} |w₁|^{k−1} ≤ 2|w₁ − w₂||w₁|^{m−1} = 2(1−|z|²)|ζ−c|^m/(|z−c|^m |1−z̄c|)`.

`ζ ∈ 𝔻` is not needed.

**(K3) `abs_kerDisc_sub_taylorDisc_two_le`** (first order, no series). Let `F'(ξ) := −(1−|z|²)/((z−ξ)(1−z̄ξ)) = −1/(z−ξ) + z̄/(1−z̄ξ)`, an explicit rational function, holomorphic off `{z, 1/z̄}`.
1. **Real gradient.** On `U := 𝔻 ∖ {z}`, `G(ξ) := kerDisc z ξ = ½ log|z−ξ|² − ½ log|1−z̄ξ|²` is `C¹` with `dG_ξ(h) = Re(F'(ξ) h)`.
   - Use `HasFDerivAt` of `Real.log ∘ normSq` (positive) composed with affine maps.
   - Check: `d/dt ½ log|z − ξ − th|²|_{t=0} = −Re(h/(z−ξ))`, and `d/dt ½ log|1 − z̄(ξ+th)|²|_{t=0} = −Re(z̄h/(1−z̄ξ))`.
2. **Reduction.** `taylorDisc 2 z c ζ = G(c) + Re(F'(c)(ζ−c))`, since `−Re(w₁ − w₂) = Re(F'(c)(ζ − c))`. Let `Φ(ξ) := G(ξ) − Re(F'(c)(ξ − c))`. Then `dΦ_ξ(h) = Re((F'(ξ) − F'(c))h)`.
3. **Second derivative.** `F''(ξ) = −1/(z−ξ)² + z̄²/(1−z̄ξ)²`. With `a = 1/(z−ξ)`, `b = z̄/(1−z̄ξ)`, `|b| ≤ |a|`: `|F''| = |a² − b²| ≤ 2|a − b||a| = 2(1−|z|²)/(|z−ξ|²|1−z̄ξ|) ≤ Bd` on the segment.
4. **Mean value twice** (`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` on the convex set `segment ℝ c ζ ⊆ U`):
   - `|F'(ξ) − F'(c)| ≤ Bd |ξ − c|`;
   - hence `‖dΦ_ξ‖ ≤ Bd|ξ−c| ≤ Bd|ζ − c|` on the segment;
   - hence `|Φ(ζ) − Φ(c)| ≤ Bd|ζ − c|²`, and `Φ(c) = G(c)`.

**(K4) `exists_poly_taylorPlane/Disc`.** The polynomial is:
- plane: `p := C(log|z−c|) − Σ_{k=1}^{m−1} C(1/(k(z−c)^k)) (X − C c)^k`;
- disc: `p := C(log ρ(c,z)) − Σ_k C(1/k)[(C(1/(z−c))(X − C c))^k − (C(z̄/(1−z̄c))(X − C c))^k]`.

`natDegree ≤ m − 1 < m` (`natDegree_sum_le`, `natDegree_pow_le`, `natDegree_X_sub_C`). `Re(p.eval ζ) = taylor…` by `Polynomial.eval_finset_sum` and `Complex.re_sum`, with `ofReal_re` for the constant. If `z = c` the coefficients are junk (`1/0 = 0`), but the identity is still literally true: both sides use the same expressions.

**(K5) `cellPot_eq_sub_poly`** (moment cancellation).
- `∫_{R_i} Re(p ζ) dν = Re ∫_{R_i} p dν` (`integral_re`; `p` is bounded on the bounded set `R_i`, `ν(R_i) < ∞`).
- `∫_{R_i} p dν = Σ_{λ∈Λ_i} p(λ)`, by expanding `p = Σ_{j<m} a_j X^j` (`Polynomial.as_sum_range'`) and using `hmom` for each `j` (`integral_finsetSum`, `integral_const_mul`, `Multiset.sum_map_sum_map`).
- Taking real parts gives `Σ_λ T(λ) = ∫_{R_i} T dν`. Subtract this from `cellPot`, using `integral_sub` with `hint` and the integrability of `T`.

### 3.2 Disc geometry (M01-type lemmas)

**`norm_sub_le_of_hypDist_le`.** Let `t := tanh s ≥ ρ(c,w)` (`tanh_hypDist`, monotone).
- `|w − c| = ρ(c,w)|1 − c̄w| ≤ t(|1 − |c|²| + |c||c − w|) ≤ t((1−|c|²) + |w − c|)`, since `1 − c̄w = (1 − |c|²) + c̄(c − w)`.
- Rearranging: `|w − c| ≤ t(1−|c|²)/(1−t)`.

**`norm_one_sub_conj_mul_comparable`** (Zhu, *Operator Theory in Function Spaces*, Lemma 4.30). For `ρ(c,ξ) ≤ t`:
- **Statement:** `(1−t)/(1+t) ≤ |1 − z̄ξ|/|1 − z̄c| ≤ (1+t)/(1−t)`, and `(1+t)/(1−t) = e^{2 artanh t} ≤ e^{2s}`.
- **Proof:**
  - Write `ξ = φ_c(u)` with `|u| = ρ(c,ξ)`, `φ_c(u) = (c − u)/(1 − c̄u)` (`mobius` in M01).
  - Use the identity `1 − z̄φ_c(u) = (1 − z̄c)(1 − \overline{φ_c(z)} u)/(1 − c̄u)`, which follows from `one_sub_conj_mobius_mul_mobius` in M01.
  - Then `|1 − \overline{φ_c(z)}u| ∈ [1−t, 1+t]` and `|1 − c̄u| ∈ [1−t, 1+t]`.

**`convex_closedHypBall`.** The closed hyperbolic ball equals `⋂_{s'>s} hypBall c s'`. Each `hypBall c s'` is a Euclidean ball (`hypBall_eq_ball`), hence convex (`convex_ball`), and intersections of convex sets are convex. ∎

**Forelli–Rudin** (`integral_one_sub_conj_mul_rpow_neg_three_le`). In polar coordinates `w = re^{iθ}`, with `t = r|z|`:
- `∫_0^{2π} |1 − t e^{iθ}|^{-3} dθ ≤ C/(1 − t)²` (standard; e.g. Zhu, Lemma 4.2.2; M10 may already have it);
- `∫_0^1 dr/(1 − r|z|)² ≤ 1/(1 − |z|)`;
- and `1/(1−|z|) ≤ 2/(1 − |z|²)`.

### 3.3 Cells: near and far (`cells_near_plane`, `cells_near_disc`)

Fix `z`. Let `C₁ := C_{K}` from `claim1_*_quant` (`ν` in class `(Cd, R̃₀)`), with `K := K₀ + A + B + 2`.

**(C1) Near cells have radius `≃ ρ̃(z)`.** If `d(z, c_i) < K₀ρ_i`, then `d ≤ K₀ max(ρ̃(z), ρ_i)`, so Claim 1 gives `ρ̃(z)/C₁ ≤ ρ_i ≤ C₁ ρ̃(z)`.

**(C2) Bounded count `M_c`.**
- Near cells contain the disjoint balls `B(c_i, ηρ_i)`, of radius `≥ ηρ̃(z)/C₁`, and these lie in `B(z, (K₀+η)C₁ρ̃(z))`.
- **Plane** (Lebesgue measure): `#near ≤ ((K₀+η)C₁ / (η/C₁))² = ((K₀+η)C₁²/η)²`.
- **Disc** (`hypArea`, using `hypArea (hypBall z r) = π sinh² r`, see §4.1): `#near ≤ sinh²((K₀+η)C₁ρ̃)/sinh²(ηρ̃/C₁)`. Use `sinh(ax) ≤ ax e^{ax}`, `sinh(bx) ≥ bx` and `ρ̃ ≤ R̃₀`: `#near ≤ ((K₀+η)C₁²/η)² e^{2(K₀+η)C₁R̃₀} =: M_c`.

**(C3) Points of near cells and their nodes are within `C₃ρ̃(z)` of `z`.** For `w ∈ R_i ∪ Λ_i`: `d(z,w) ≤ d(z,c_i) + max(A,B)ρ_i ≤ (K₀ + A + B)C₁ρ̃(z) =: C₃ρ̃(z)`.

**(C4) Non-near cells are at distance `≥ δρ̃(z)`, and so are their nodes (up to a factor 2).** Let `δ := min(1, K₀/C₁)` and suppose `K₀ρ_i ≤ d(z,c_i)`.
- If `d(z,c_i) < δρ̃(z) ≤ ρ̃(z)`, then Claim 1 gives `ρ̃(z) ≤ C₁ρ_i`, so `d(z,c_i) ≥ K₀ρ_i ≥ (K₀/C₁)ρ̃(z) ≥ δρ̃(z)`, a contradiction.
- **Nodes.** `d(z,λ) ≥ d(z,c_i) − Bρ_i ≥ d(z,c_i)(1 − B/K₀) ≥ d(z,c_i)/2 ≥ δρ̃(z)/2`, by the triangle inequality (`hypDist_triangle` in `𝔻`).

**(C5) `z` lies in a near cell.** `z ∈ R_{i₀}` (`iUnion_eq`), and `d(z, c_{i₀}) ≤ Aρ_{i₀} < K₀ρ_{i₀}`.

**The Remark `d(z,Λ) ≤ C₃ρ̃(z)`.** By (C5) and (C3), the `N ≥ 1` nodes of `R_{i₀}` are within `C₃ρ̃(z)`. This is the first conjunct of `multPot_bounds_*`, and after §1.2 the third conjunct of `Thm4Bounds*`.

**(C6) Local finiteness (`finite_cells_plane`, `finite_cells_disc`).** Let `K` be bounded (compact in `𝔻` for the disc) and `L > 0`.
- Cells with `d(z,c_i) < L` for some `z ∈ K` have centres in `K_L := cthickening L K`.
- `ρ̃ ≥ ρ_min(K_{L+R̃₀A}) > 0` there. Indeed `ρ̃` is 1-Lipschitz (M03 `lipschitzWith_massRadiusM`) and positive, so it is bounded below on compacts.
- The cells' inner balls are disjoint, of radius `≥ ηρ_min`, and lie in a bounded set (compact in `𝔻`). So there are finitely many, by area (`measure_biUnion_finset` against `volume`).

Consequences:
- **Nodes are locally finite:** finitely many cells have a node in `K`, each with `N` nodes. This is the `finite_support` field of M07.
- `nodeCount` is a finite sum, and `w ∈ nodeSet Λ ↔ nodeCount Λ w ≠ 0`.
- The minimum `d(z, Λ)` is attained (finitely many nodes within `C₃ρ̃(z)`), as `multPot_bounds_*` assume.

### 3.4 Per-cell bounds for non-near cells

Let `i` be non-near: `d(z,c_i) ≥ K₀ρ_i`, with `K₀ = 64(A+B+1)`. Put `s_i := cellPot k ν R Λ i z`. By (K5) with `T = taylor(m_i)`, `|s_i| ≤ N sup_{ζ∈R_i∪Λ_i} |k(z,ζ) − T(ζ)| + N sup_{ζ∈R_i} |…|`: there are `N` nodes and `ν(R_i) = N`. All `ζ ∈ R_i ∪ Λ_i` satisfy `d(c_i, ζ) ≤ max(A,B)ρ_i`.

**Plane.** `|ζ − c_i| ≤ (A+B)ρ_i ≤ |z − c_i|/2`, so (K1) with `m_i ≥ 3` (use `m = 3`: lower-order moments also match) gives
`|s_i| ≤ 4N (A+B)³ (ρ_i/|z−c_i|)³`.  (P)

**Disc, near field** (`d(z,c_i) < M₀`, hence `ρ_i < ρ₀'` and `m_i ≥ 3`).
- Let `s := (A+B)ρ_i ≤ 1/8`. By `norm_sub_le_of_hypDist_le`, `|ζ − c_i| ≤ (tanh s/(1 − tanh s))(1 − |c_i|²) ≤ (8/7)s(1 − |c_i|²)`.
- **Lower bound for `|z − c_i|`.** With `β := hypDist z c_i ≤ 1/4`: `|z − c_i| = tanh β · |1 − z̄c_i| ≥ (β/5)(1 − |c_i|) ≥ β(1 − |c_i|²)/10` (`div_five_le_tanh`, and `|1 − z̄c| ≥ 1 − |c|`).
- Since `β ≥ K₀ρ_i ≥ 64s`, `|ζ − c_i|/|z − c_i| ≤ (80/7)s/β ≤ 80/448 < 1/2`.
- **(K2), and `(1−|z|²)/|1−z̄c_i| ≤ 2`** (as `|1 − z̄c| ≥ 1 − |z|`) give
  `|s_i| ≤ 8N(12(A+B))³(ρ_i/β)³`.  (D-near)

**Disc, far field** (`d(z,c_i) ≥ M₀`; `m_i ≥ 2`).
- Let `s := (A+B)ρ_i ≤ (A+B)R̃₀`. The closed hyperbolic ball `B̄(c_i, s)` is convex (`convex_closedHypBall`) and contains `R_i ∪ Λ_i` and every segment `[c_i, ζ]`.
- For `ξ` in it, `β(z, ξ) ≥ β(z,c_i) − s ≥ β(z,c_i)/2 ≥ M₀/2`, since `K₀ ≥ 2(A+B)`. Hence:
  - `|z − ξ| ≥ tanh(M₀/2)|1 − z̄ξ|`;
  - `|1 − z̄ξ| ≥ e^{−2s}|1 − z̄c_i|` (`norm_one_sub_conj_mul_comparable`).
- So (K3) applies with `Bd := 2(1−|z|²) e^{6s} / (tanh²(M₀/2) |1−z̄c_i|³)`.
- Also `|ζ − c_i| ≤ s e^{2s}(1−|c_i|²)`, since `tanh s/(1−tanh s) = (e^{2s}−1)/2 ≤ s e^{2s}`.
- Result:
  `|s_i| ≤ C_D (1−|z|²)((1−|c_i|²)ρ_i)²/|1−z̄c_i|³`, with `C_D := 4N(A+B)² e^{10(A+B)R̃₀}/tanh²(M₀/2)`.  (D-far)

This covers large and small cells alike: only order 2 is used.

### 3.5 The area-counting near-field lemma (replaces Lemma 3)

**Statement** (`nearField_sum_le_plane/disc`). Let `F` be finite, and for `i ∈ F` let `δρ̃(z) ≤ d(z,c_i) ≤ 1/4` and `Aρ_i ≤ d(z,c_i)`. Then `Σ_{i∈F} (ρ_i/d(z,c_i))³ ≤ C`, with `C = C(Cd, R₀, η, A, δ)`.

**Proof.**
1. **Rings.** Split `F` into `F_n := {i : 2^n δρ̃(z) ≤ d(z,c_i) < 2^{n+1}δρ̃(z)}`, `n ≥ 0`. Only `n ≤ log₂(1/(4δρ̃(z)))` occur, finitely many.
2. **Area count in a ring.** For `i ∈ F_n`, the inner balls `B(c_i, ηρ_i) ⊆ R_i` are pairwise disjoint, and `R_i ⊆ B̄(c_i, Aρ_i) ⊆ B̄(z, 2d(z,c_i)) ⊆ B(z, 2^{n+2}δρ̃(z))`, since `Aρ_i ≤ d(z,c_i)`.
   - **Plane:** `Σ_{F_n} πη²ρ_i² ≤ π 4^{n+2}δ²ρ̃(z)²`.
   - **Disc:** use hyperbolic area: `π sinh²(ηρ_i) ≥ πη²ρ_i²`, and `π sinh²(2^{n+2}δρ̃) ≤ π sinh²(1)·4^{n+2}δ²ρ̃²`, since the radius is `≤ 4·(1/4) = 1` and `sinh x ≤ sinh(1)·x` on `[0,1]`.
   - Either way `Σ_{F_n} ρ_i² ≤ 16 sinh²(1) 4^n δ²ρ̃(z)²/η²`, hence `Σ_{F_n} (ρ_i/d(z,c_i))² ≤ 16 sinh²(1)/η² =: Q`.
3. **Decay of the maximum.** For `i ∈ F_n`:
   - if `d(z,c_i) ≥ ρ̃(z)`: by `decay_*_quant` (`d ≤ 1/4`), `ρ_i/d ≤ C_dec (ρ̃(z)/d)^α ≤ C_dec (2^nδ)^{−α}`;
   - if `δρ̃(z) ≤ d < ρ̃(z)`: Claim 1 gives `ρ_i ≤ C₁ρ̃(z)`, so `ρ_i/d ≤ C₁/δ ≤ (C₁/δ)·(2^nδ)^{−α}·(2^nδ)^{α}`. Here `2^nδ < 1`, so `ρ_i/d ≤ (C₁/δ)(2^nδ)^{−α}`.
   - So `max_{F_n} ρ_i/d ≤ C' 2^{−nα}`, with `C' := max(C_dec, C₁/δ) δ^{−α}`.
4. **Sum.** `Σ_{F_n} (ρ_i/d)³ ≤ (max_{F_n} ρ_i/d) · Σ_{F_n}(ρ_i/d)² ≤ C' Q 2^{−nα}`, and `Σ_n 2^{−nα} = 1/(1 − 2^{−α})`. ∎

**Why order 3.** With order 2 each ring contributes `O(1)`, and there are `≈ log(1/ρ̃(z))` rings, which is unbounded since `ρ̃` can be arbitrarily small. The third power buys the factor `max ρ_i/d`, which decays geometrically. This is where local doubling enters, through the decay lemma: the paper's `mγ > 1` is not needed.

### 3.6 Far-field sums

**Plane** (`farField_sum_le_plane`; `d(z,c_i) ≥ M₀` and `2Aρ_i ≤ d(z,c_i)`). For `w ∈ R_i`, `d/2 ≤ |z − w| ≤ 2d` with `d := |z − c_i|`. Then:
- `(ρ_i/d)³ ≤ R̃₀ρ_i²/d³` (`ρ_i ≤ R̃₀`), `ρ_i² ≤ |R_i|/(πη²)` (inner ball) and `d^{-3} ≤ 8|z−w|^{-3}` on `R_i`; hence `(ρ_i/d)³ ≤ (8R̃₀/(πη²)) ∫_{R_i} dm(w)/|z−w|³`;
- summing over disjoint cells: `≤ (8R̃₀/(πη²)) ∫_{|z−w|≥M₀/2} |z−w|^{−3} dm(w) = (8R̃₀/(πη²))·2π·(2/M₀) = 32R̃₀/(η²M₀)`.

This is the paper's Fubini step on p. 368 ("`ρ(ζ)² ≃ ∫_{|ζ−w|≤ρ(ζ)} dm(w)`"), done with the area of the cell instead of `μ`-mass.

**Disc** (`farField_sum_le_disc`). Let `w ∈ R_i ⊆ B̄_hyp(c_i, AR̃₀)`. Then:
- `|1 − z̄w| ≤ e^{2AR̃₀}|1 − z̄c_i|`;
- `area_e(R_i) ≥ area_e(hypBall(c_i, ηρ_i)) ≥ π tanh²(ηρ_i)(1−|c_i|²)²`, since the Euclidean disc `hypBall(c,r)` has radius `tanh r (1−|c|²)/(1 − tanh²r |c|²) ≥ tanh r (1−|c|²)` (M01 `hypBall_eq_ball`);
- `tanh(ηρ_i) ≥ ηρ_i·tanh(ηR̃₀)/(ηR̃₀)` (concavity).

So `((1−|c_i|²)ρ_i)² ≤ C_a area_e(R_i)`, and
`Σ_i (1−|z|²)((1−|c_i|²)ρ_i)²/|1−z̄c_i|³ ≤ C_a e^{6AR̃₀}(1−|z|²) ∫_𝔻 dm(w)/|1−z̄w|³ ≤ C_a e^{6AR̃₀} C_FR`.
The hypothesis `M₀ ≤ d(z,c_i)` is not even needed for the sum. This is the paper's Ω₂ step on p. 369.

### 3.7 The non-near part is bounded

Let `S_far(z) := Σ_{i non-near} s_i(z)`. Then `|S_far(z)| ≤ C_nf`, uniformly in `z` and in the configuration.
- **Plane.** By (P), `|S_far| ≤ 4N(A+B)³ Σ_{non-near}(ρ_i/d)³`. Split at `M₀ = 1/4`:
  - `d < 1/4`: §3.5 with `δ` from (C4) (`K₀ ≥ A`);
  - `d ≥ 1/4`: §3.6 (`K₀ ≥ 2A`).
- **Disc.** For `d < M₀`, (D-near) and §3.5. For `d ≥ M₀`, (D-far) and §3.6.

The sums run over all finite `F`, so the series `Σ_{non-near} |s_i|` converges, with sum `≤ C_nf`.

### 3.8 Convergence, continuity, Laplacian (`multPot_props_*`: the M07 fields)

1. **`finite_support`:** (C6).
2. **Summability for every `z`.** Near cells are finite (C2), and the rest is absolutely summable (§3.7). Use `Summable.of_norm_bounded_eventually` or `summable_of_finite_compl`.
3. **Locally uniform convergence.** Fix a compact `K` (`⊆ 𝔻` in the disc). Let `F_K := {i : ∃ z ∈ K, d(z,c_i) < L}`, which is finite by (C6).
   - **Plane:** `L := diam K + (K₀ + A + 1)R̃₀ + 1`, so that `L ≥ K₀R̃₀` (non-near), `L ≥ 1/4` (far field) and `L − AR̃₀ ≥ diam K`. For `i ∉ F_K` and `z, z₀ ∈ K`: `i` is non-near and far from every `z ∈ K`. For `w ∈ R_i`, `|z − w| ≥ |z₀ − w|/2`, so the §3.6 integrand gives `sup_K |s_i| ≤ 8·b_i(z₀)` with `Σ_i b_i(z₀) < ∞`.
   - **Disc:** `L := K₀R̃₀ + 1` (non-near and `β ≥ M₀`). For `i ∉ F_K`, (D-far) holds for all `z ∈ K`, and `|1 − z̄c_i| ≥ 1 − r_K`, where `K ⊆ B̄(0, r_K)`. So `sup_K |s_i| ≤ C_D (1−r_K)^{−3}(1−|c_i|²)²ρ_i² ≤ C' area_e(R_i)`, and `Σ_i area_e(R_i) ≤ π`.
   - Weierstrass M-test (`tendstoUniformlyOn_tsum`): `Σ_{i∉F_K} s_i` converges uniformly on `K`. Each term is continuous (indeed harmonic) on a neighbourhood of `K`: its cell and nodes are at positive distance from `K`.
4. **Continuity of each `s_i`, `i ∈ F_K`, off its nodes.**
   - The node part `Σ_λ k(·,λ)` is continuous off `Λ_i`.
   - The potential `U_i(z) := ∫_{R_i} k(z,ζ) dν(ζ)` is continuous on `Ω`. Given `ε`, `logSmall_*` (M04, for `ν ≤ μ`) gives `δ_ε ≤ 1` with `∫_{B(z,δ_ε)} (1 + log(1/|z−ζ|)) dν ≤ ε` for `z ∈ K`. Split `log|z−ζ| = log max(|z−ζ|, δ_ε) + (log|z−ζ| − log δ_ε)⁻`.
     - The first part is jointly continuous and bounded on `K × R_i`, so its integral is continuous (`continuousOn_of_dominated`).
     - The second part is supported in `B(z, δ_ε)`, with absolute integral `≤ ∫_{B(z,δ_ε)} log(1/|z−ζ|) dν ≤ ε`.
     - So `U_i` is a uniform limit of continuous functions on `K`.
   - In the disc, `−log|1−z̄ζ|` is jointly continuous on `𝔻 × 𝔻`. This is M07 §5 item 3, without the semicontinuity detour.
5. **`LocallyIntegrable(On)`.** On `K`: `ψ` is continuous, `Σ_{i∉F_K}` is continuous, and for `i ∈ F_K`, `U_i` is continuous and `log|·−λ|` is `L¹_loc` (M02 `locallyIntegrable_log_norm_sub`). In `𝔻`, `log|1 − λ̄ z|` is continuous.
6. **Continuity of `v = ψ + S` on `Ω ∖ supp n`.** Items 3–4, on a compact neighbourhood of each point.
7. **Laplacian.** Fix a test function `χ` with `K := tsupport χ` (`⊆ 𝔻`).
   - **Interchange.** `∫ S Δχ = Σ_{i∈F_K} ∫ s_i Δχ + ∫ (Σ_{i∉F_K} s_i) Δχ`. The tail converges uniformly on `K`, so `∫ (Σ_{i∉F_K} s_i)Δχ = Σ_{i∉F_K} ∫ s_iΔχ` (`integral_tsum` with `Σ ∫_K |s_i||Δχ| ≤ ‖Δχ‖_∞ |K| Σ sup_K|s_i| < ∞`).
   - **Per cell.** `∫ s_i Δχ = Σ_λ ∫ k(z,λ)Δχ(z)dz − ∫∫ k(z,ζ)Δχ(z) dz dν_i(ζ)`.
     - Fubini (`integral_integral_swap`) applies: `∫_{R_i}∫_K |k(z,ζ)||Δχ(z)| dz dν(ζ) ≤ ‖Δχ‖_∞ N sup_{ζ∈R_i} ∫_K |k(z,ζ)| dz < ∞`, and the inner sup is finite (`log` is locally integrable, uniformly in `ζ` on bounded sets).
     - By M02, `∫ k(z,a)Δχ(z) dz = 2πχ(a)`. In the plane this is `integral_log_norm_sub_mul_laplacian`. In the disc it is `integral_log_pseudoHyp_mul_laplacian` (`kerDisc z a = log pseudoHyp a z`, `a ∈ 𝔻`: nodes lie in `𝔻` by `IsNodes.mem`, and cells do too).
     - So `∫ s_iΔχ = 2π(Σ_{λ∈Λ_i} χ(λ) − ∫_{R_i} χ dν)`.
   - **Sum.** Only finitely many `i` have `Λ_i ∩ K ≠ ∅` or `R_i ∩ K ≠ ∅` (C6); for the others the term is 0. The finite sum is `2π Σᶠ_w nodeCount(w)χ(w) − 2π ∫ χ dν`, since the `R_i` partition `Ω` (`iUnion_eq`, disjoint, measurable; `integral_finset_biUnion`).
   - `∫ ψΔχ = ∫χ dμ = 2π∫χ dν`. The total is `2πΣᶠ nodeCount·χ`. ∎

All of `IsWeakLogModulus Ω (nodeCount Λ) (ψ + S)` is now verified. M07's `exists_analytic_norm_eq_exp_of_weak` (`_univ`, or `_disc` with `c = 0`) gives `h`, analytic on `Ω`, with:
- `‖h z‖ = exp(ψ z + S z)` off the nodes;
- `analyticOrderAt h z = nodeCount Λ z`, hence `h z = 0 ↔ z ∈ nodeSet Λ` (`analyticOrderAt_eq_zero`).

### 3.9 The corrected estimates (2), (3) (`multPot_bounds_*`)

Let `z ∉ Λ`, and let `d := min_{w∈Λ} d(z,w)`, which is attained (C6). Split `S = S_near + S_far`, with `|S_far| ≤ C_nf` (§3.7).

**The near part, plane.** Since `ν(R_i) = N = #Λ_i`, we may subtract `log ρ̃(z)` from every term:
`S_near = Σ_{i near} Σ_{λ∈Λ_i} log(|z−λ|/ρ̃(z)) − Σ_{i near} ∫_{R_i} log(|z−ζ|/ρ̃(z)) dν(ζ) =: Σ₁ − Σ₂`.

- **(Σ₂ is bounded.)** For near `i`, `R_i ⊆ B(z, S_r)` with `S_r := C₃ρ̃(z)` (C3). Then:
  - `|log(|z−ζ|/ρ̃)| ≤ log(S_r/|z−ζ|) + log C₃`;
  - `christ_plane_quant` with `s = S_r ≤ C₃R̃₀`: `∫_{B(z,S_r)} log(S_r/|z−ζ|) dν ≤ C_χ ν(B(z, C₃ρ̃(z))) ≤ C_χ C_B` (`measure_ball_massRadius_quant` with `K = C₃`).
  - So `|Σ₂| ≤ C_χC_B + C_B log C₃ =: C_Σ`. All near cells lie in that ball and are disjoint, so the integrals add up.
- **(Upper bound for Σ₁.)** Every term is `≤ log C₃` (C3), and there are `M' := N·#near ≤ N M_c =: M` terms.
  - If `d < (δ/2)ρ̃(z)`, the nearest node is not from a non-near cell (C4). So it belongs to a near cell and its term is `log(d/ρ̃)`. Hence `Σ₁ ≤ log(d/ρ̃) + (M−1)log⁺C₃`.
  - If `d ≥ (δ/2)ρ̃(z)`, then `Σ₁ ≤ M log⁺C₃ ≤ log(d/ρ̃) + log(2/δ) + M log⁺ C₃`.
- **(Lower bound for Σ₁.)** Every term is `≥ log(d/ρ̃)`, and there are `M' ≤ M` of them. Since `d ≤ C₃ρ̃(z)` (Remark), `log(d/ρ̃) ≤ log C₃`.
  - If `log(d/ρ̃) ≤ 0`: `M' log(d/ρ̃) ≥ M log(d/ρ̃)`.
  - Otherwise: `M' log(d/ρ̃) ≥ 0 ≥ M log(d/ρ̃) − M log⁺ C₃`.

**Result:** `M log(d/ρ̃) − C ≤ S(z) ≤ log(d/ρ̃) + C` with `C := C_nf + C_Σ + log(2/δ) + M log⁺ C₃`.

**The near part, disc.** Use `hypDist` throughout, with `k(z,ζ) = log tanh β(z,ζ)` (`tanh_hypDist`: `pseudoHyp = tanh ∘ hypDist`). For `β ≤ S_max := C₃R̃₀`, concavity of `tanh` gives `log β + log(tanh S_max/S_max) ≤ log tanh β ≤ log β`. So, up to an additive error `≤ 2N M_c |log(tanh S_max/S_max)|`, the near part is `Σ₁ − Σ₂` with `β` in place of `|z−ζ|`. `christ_disc_quant` and `measure_hypBall_massRadius_quant` give `|Σ₂| ≤ C_Σ`, and the rest is identical.

**Which side is which, and what `M` is.** `S = log|h| − ψ`. The *upper* bound has coefficient 1: only the nearest node can make `S` very negative at the rate `log d`. The *lower* bound has coefficient `M = N·M_c` = the maximal number of nodes, counted with multiplicity, in the cells near `z`. All of them could be at distance `≈ d`; for example nodes of multiplicity `k = 4` from M06 coincide. Printed (2)/(3) bound `I = ∫ log|z−ζ| (Δψ − Σδ) = −2πS` (with the point masses scaled by `2π`) from the wrong side. The correct statement is the one above for `S = −I/2π`.

### 3.10 Node configurations (`exists_nodes_*`)

**Plane.** For each `i`, let `ν_i := ν.restrict (R i)`. It has mass `12 = 3·4` and is carried by `B̄(c_i, Aρ_i)`. Apply `lemma5_moments 3 4 (by norm_num) (by norm_num) ν_i (c i) (A ρ_i) _ _ _ B`, and choose `Λ i := Λ` or `K` according to `sel i` (`Classical.choose`, per `i`). Then:
- ordinary nodes: `|w − c_i| ≤ 6Aρ_i`;
- `κ` nodes: `BAρ_i ≤ |w − c_i| ≤ (B+12)Aρ_i`;
- moments `j < 3`: `∫_{R i} ζ^j dν = ∫ ζ^j dν_i` (`setIntegral` vs `restrict`);
- `mem` is trivial (`Ω = univ`).

**Disc.** Put `Bl := 64A`, `s_i := Aρ_i`, `t_i := tanh s_i`.

*Small cells* (`ρ_i ≤ ρ₀`, with `ρ₀ := 1/(64(B+12)(A+1))`, so `(B+12)t_i ≤ 1/64` and `t_i ≤ 1/64`).
1. `R_i ⊆ B̄(c_i, r_e)` (Euclidean), with `r_e := t_i(1−|c_i|²)/(1−t_i) ≤ (64/63)t_i(1−|c_i|²)` (`norm_sub_le_of_hypDist_le`).
2. Apply `lemma5_moments 3 4` with radius `r_e` and parameter `B`.
   - Ordinary nodes `|w − c| ≤ 6r_e`; `κ` nodes `B r_e ≤ |w − c| ≤ (B+12) r_e ≤ (1/32)(1−|c|²)`.
3. **Back to hyperbolic distance.** For `|w − c| ≤ τ(1−|c|²)` with `τ ≤ 1/32`: `|1 − c̄w| ≥ (1−|c|²) − |c||w−c| ≥ (1−τ)(1−|c|²)`. So `ρ(c,w) ≤ τ/(1−τ) < 1`; in particular `w ∈ 𝔻`, by `|1−c̄w|² − |c−w|² = (1−|c|²)(1−|w|²)`.
   - Then `hypDist c w = artanh ρ(c,w) ≤ 2ρ(c,w)`.
   - Ordinary nodes: `hypDist ≤ 2·(64/63)·6t_i/(1 − 1/32) ≤ 13 t_i ≤ 13Aρ_i ≤ Bl ρ_i`.
   - `κ` nodes, lower bound: `ρ(c,w) ≥ |w−c|/((1−|c|²) + |w−c|) ≥ Bt_i/(1 + 1/32)`. So `hypDist ≥ ρ(c,w) ≥ (32/33)B tanh(Aρ_i) ≥ (32/33)(63/64)BAρ_i`, using `tanh x ≥ x(1 − x)` for small `x`.
   - **To get exactly `BAρ_i`,** call M06 with `B·(33/31)` in place of `B`. This is a harmless constant change; the Lean statement only needs *some* such choice.
   - `κ` nodes, upper bound: `hypDist ≤ 2(B+12)·(64/63)t_i/(1−1/32) ≤ 3(B+12)Aρ_i`.
4. Moments `< 3`; `m_i := 3`.

*Large cells* (`ρ_i > ρ₀`); `m_i := 2`.
- **Barycentre.** `b_i := (1/12)∫_{R_i} ζ dν`, the integral of `ζ` against the probability measure `ν_i/12`. Its support lies in the closed convex set `B̄_hyp(c_i, Aρ_i)` (`convex_closedHypBall`; closed in `ℂ` since it is a closed Euclidean disc inside `𝔻`). So `Convex.integral_mem` gives `b_i ∈ B̄_hyp(c_i, Aρ_i) ⊆ 𝔻`.
- **Ordinary nodes:** `Λ_i := 12 • {b_i}`. Moments `j = 0, 1` match by definition, and `hypDist(c_i, b_i) ≤ Aρ_i ≤ Bl ρ_i`.
- **`κ` nodes** (if `sel i`): `6 • {b + v} + 6 • {b − v}`, with `v := τ·u`, `u := i b/|b|` (or `u := 1` if `b = 0`), `τ := T(1−|b|²)/√(1 − T²|b|²)`, `T := tanh((B+1)Aρ_i)`.
  - Then `|1 − b̄(b ± v)|² = (1−|b|²)² + τ²|b|²`, since `b̄u` is purely imaginary with modulus `|b|`.
  - So `ρ(b, b±v) = τ/√((1−|b|²)² + τ²|b|²) = T`, i.e. `hypDist(b, b ± v) = (B+1)Aρ_i` exactly.
  - `|b ± v|² = |b|² + τ² < 1`, because `τ² < 1 − |b|²` ⟺ `T² < 1`.
  - Moments `0, 1` match: `6(b+v) + 6(b−v) = 12b`.
  - By the triangle inequality, `BAρ_i ≤ hypDist(c_i, κ) ≤ (B+2)Aρ_i`.
- Take `B' := max(Bl, 3(B+12)A, (B+2)A)`.

### 3.11 The core theorem and Theorem 4

**`multiplier_of_nodes_*`.**
1. §3.8 gives `h`, with zero set and orders.
2. **Bounds.** Let `z ∈ Ω`.
   - If `z ∈ Λ`: `edistSet = 0`. With `M ≥ 1` the left side is `C⁻¹ · 0 = 0`; the middle is `ofReal 0 = 0`; and the Remark holds.
   - Otherwise `‖h z‖e^{−ψ(z)} = e^{S(z)}`. By §3.9, with `D := d/ρ̃(z)`: `e^{−C}D^M ≤ e^{S} ≤ e^{C}D`.
3. **Convert `ρ̃` to `ρ = massRadius μ`** (`massRadius_lapNorm_quant`, `ρ ≤ ρ̃ ≤ C_ρρ`):
   - `D ≤ d/ρ`;
   - `D^M ≥ C_ρ^{−M}(d/ρ)^M`;
   - `d ≤ C₃ρ̃ ≤ C₃C_ρ ρ`.
4. **ENNReal.** `edistSet z Z = ENNReal.ofReal d` (`Z` nonempty, minimum attained; `iInf` of `ofReal` over a set whose infimum is attained). `ofReal d / ofReal ρ = ofReal (d/ρ)` (`ENNReal.ofReal_div_of_pos`, `ρ > 0` by `claim1_*_quant`), and `ofReal(x^M) = ofReal(x)^M` (`ENNReal.ofReal_pow`).
   - `C := ⌈max(e^C C_ρ^M, e^C, C₃C_ρ, 1)⌉₊ : ℝ≥0`.
   - In `𝔻`, `hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} = ofReal(min_{w∈Λ} hypDist z w)`.

**`theorem4_*_quant`.**
1. `ν := lapNorm μ` is in class `(Cd, 15R₀)`.
2. M05 (`lemma4_*_quant`, `N = 12`) gives `IsMassPartition ν Ω d ρ̃ 12 a A R`, and `exists_cells` gives `c` (with `η = a`).
3. `exists_nodes_*` with `sel ≡ false` gives `Λ`.
4. `multiplier_of_nodes_*`.
5. `h ≢ 0`: `nodeSet Λ` is countable (a countable union of finite sets), so pick `z₀ ∈ Ω ∖ nodeSet Λ` (`Set.Countable.dense_compl`); then `h z₀ ≠ 0`.

The constants come from steps 2–4 and depend only on `(Cd, R₀)`.

**`theorem4_disc`, `theorem4_plane`.** Proved in the scratch file (4 lines each): `obtain` `R₀`, `Cd`; build the class; apply `_quant`; drop the third conjunct.

---
## 4. Interface

### 4.1 Consumed (assumed lemmas, exact forms)

```lean
/-- (M11/M01, shared name) hyperbolic area measure. -/
def hypArea : Measure ℂ :=
  (volume.restrict 𝔻).withDensity fun z ↦ ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2) ^ 2)

/-- (M05) copied verbatim from `M05_Partition.md` §2.3. -/
structure IsMassPartition (μ : Measure ℂ) (Ω : Set ℂ) (d : ℂ → ℂ → ℝ) (ρ : ℂ → ℝ) (N : ℕ)
    (a A : ℝ) (R : ℕ → Set ℂ) : Prop where
  measurableSet : ∀ i, MeasurableSet (R i)
  pairwise_disjoint : Pairwise (Function.onFun Disjoint R)
  iUnion_eq : ⋃ i, R i = Ω
  measure_eq : ∀ i, μ (R i) = N
  dist_le : ∀ i, ∀ z ∈ R i, ∀ w ∈ R i, d z w ≤ A * ρ z
  inner : ∀ i, ∃ c ∈ R i, {w | w ∈ Ω ∧ d c w < a * ρ c} ⊆ R i

/-- (M03, growth + scaling) `lapNorm` stays in a class; `ρ` and `ρ̃` are comparable. -/
theorem MeasClassPlane.lapNorm {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} (h : MeasClassPlane μ Cd R₀) :
    MeasClassPlane (lapNorm μ) Cd (15 * R₀) := sorry
theorem MeasClassDisc.lapNorm {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} (h : MeasClassDisc μ Cd R₀) :
    MeasClassDisc (lapNorm μ) Cd (15 * R₀) := sorry
theorem massRadius_lapNorm_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure ℂ, MeasClassPlane μ Cd R₀ → ∀ z,
      massRadius μ z ≤ massRadius (lapNorm μ) z ∧ massRadius (lapNorm μ) z ≤ C * massRadius μ z :=
  sorry
theorem massRadiusDisc_lapNorm_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure ℂ, MeasClassDisc μ Cd R₀ → ∀ z ∈ 𝔻,
      massRadiusDisc μ z ≤ massRadiusDisc (lapNorm μ) z ∧
        massRadiusDisc (lapNorm μ) z ≤ C * massRadiusDisc μ z := sorry

/-- (M03, quantitative Claim 1 + positivity/upper bound of `ρ`). -/
theorem claim1_plane_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z w : ℂ,
      0 < massRadius ν z ∧ massRadius ν z ≤ R₀ ∧
      (dist z w ≤ K * max (massRadius ν z) (massRadius ν w) →
        massRadius ν z ≤ C * massRadius ν w) := sorry
theorem claim1_disc_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ w ∈ 𝔻,
      0 < massRadiusDisc ν z ∧ massRadiusDisc ν z ≤ R₀ ∧
      (hypDist z w ≤ K * max (massRadiusDisc ν z) (massRadiusDisc ν w) →
        massRadiusDisc ν z ≤ C * massRadiusDisc ν w) := sorry

/-- (M03, quantitative) mass of comparable balls. -/
theorem measure_ball_massRadius_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z, ν (ball z (K * massRadius ν z)) ≤ C := sorry
theorem measure_hypBall_massRadius_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻,
      ν (hypBall z (K * massRadiusDisc ν z)) ≤ C := sorry

/-- (M03, quantitative decay; `massRadiusM_div_dist_le` with `M₀ = 1/4`). -/
theorem decay_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z ζ : ℂ,
      massRadius ν z ≤ dist z ζ → dist z ζ ≤ 1 / 4 →
        massRadius ν ζ / dist z ζ ≤ C * (massRadius ν z / dist z ζ) ^ α := sorry
theorem decay_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻,
      massRadiusDisc ν z ≤ hypDist z ζ → hypDist z ζ ≤ 1 / 4 →
        massRadiusDisc ν ζ / hypDist z ζ ≤ C * (massRadiusDisc ν z / hypDist z ζ) ^ α := sorry

/-- (M03, quantitative [Chr91, Lemma 2.3]). -/
theorem christ_plane_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z : ℂ, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ ζ in ball z s, ENNReal.ofReal (Real.log (s / dist z ζ)) ∂ν ≤ C * ν (ball z s) := sorry
theorem christ_disc_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ ζ in hypBall z s, ENNReal.ofReal (Real.log (s / hypDist z ζ)) ∂ν ≤
        C * ν (hypBall z s) := sorry

/-- (M05, quantitative Lemma 4). -/
theorem lemma4_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) : ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν univ dist (massRadius ν) N a A R := sorry
theorem lemma4_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) : ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν 𝔻 hypDist (massRadiusDisc ν) N a A R := sorry
```

The stubs are in the scratch file; names may change, shapes should not.

**M03 (quantitative).** Each needs a uniform version: constants depend only on `(Cd, R₀)` and the displayed auxiliary parameter. M03's current statements (`IsLocDoublingM.claim1`, `massRadiusM_div_dist_le`, `christ_lemma23`, `measure_ball_le_pow`, …) have `∃ C` *after* `μ`. Their proofs give uniform constants. M03 should export them in the form "∀ Cd R₀, ∃ C, ∀ μ in class". Thin wrappers over `discPull` / `HDisc` suffice for the disc.
- `MeasClassPlane.lapNorm`, `MeasClassDisc.lapNorm`: the class of `(2π)⁻¹μ` (growth, §1.2).
- `massRadius_lapNorm_quant`, `massRadiusDisc_lapNorm_quant`: `ρ ≤ ρ̃ ≤ Cρ`.
- `claim1_plane_quant`, `claim1_disc_quant`: Claim 1, plus `0 < ρ ≤ R₀`.
- `measure_ball_massRadius_quant`, `measure_hypBall_massRadius_quant`: `ν(B(z,Kρ(z))) ≤ C_K`.
- `decay_plane_quant`, `decay_disc_quant`: `ρ(ζ)/d ≤ C(ρ(z)/d)^α` for `ρ(z) ≤ d ≤ 1/4`.
- `christ_plane_quant`, `christ_disc_quant`: `∫_{B(z,s)} log(s/d) dν ≤ Cν(B(z,s))`, `s ≤ S`.
- `IsLocDoublingM.measure_singleton` (no atoms) and `lipschitzWith_massRadiusM`: qualitative, as in M03.

**M04.** `logSmall_plane`, `logSmall_disc` as stated in M04 §2 (qualitative; used for continuity only).

**M05 (quantitative).** `lemma4_plane_quant`, `lemma4_disc_quant`: `∃ a A`, uniform over the class, then `IsMassPartition ν Ω d ρ̃ N a A R`. M05's `lemma4_*` has `∃ a A L` after `μ`; the construction is uniform.
- Only `IsMassPartition` is used: the rectangle shape (`IsRectLE`, `discBox`) is not.
- M05's Claim 2 lemmas (`claim2_*`, `finite_near_*`, `far_comparable_*`) are **not** used: they are subsumed by §3.3, which works with centres `c_i` and needs only Claim 1.

**M06.** `lemma5_moments` exactly as proved (`m = 3`, `k = 4`).

**M07.**
- `IsWeakLogModulus` and `exists_analytic_norm_eq_exp_of_weak hweyl hker`, with `Ω = univ, c = 0` and `Ω = 𝔻, c = 0` (`hΩ`: `closedBall 0 r ⊆ 𝔻` for `|z| < r < 1`).
- `hweyl`, `hker` come from M02.

**M02.** `integral_log_norm_sub_mul_laplacian`, `integral_log_pseudoHyp_mul_laplacian`, `locallyIntegrable_log_norm_sub`.

**M01 / M11.**
- `hypArea` (shared name, M11's definition). **It must be defined in exactly one module, preferably M01**; M08, M09 and M11 then import it. The scratch file has a local stub.
- **`hypArea_hypBall : z ∈ 𝔻 → 0 ≤ r → hypArea (hypBall z r) = ENNReal.ofReal (π * Real.sinh r ^ 2)`**: Möbius invariance plus the computation at `0`. It is needed for the disc counts (C2) and §3.5, and also by M09 and by M11 §4.5. **It should live in M01.**
- The three geometry lemmas of §2.2 (`norm_sub_le_of_hypDist_le`, `norm_one_sub_conj_mul_comparable`, `convex_closedHypBall`) can go to M01 or stay here.

**M10 (optional).** The Forelli–Rudin bound, if M10 proves it; otherwise §3.2 proves it here.

### 4.2 Provided

- **To M09:**
  - the core theorems `multiplier_of_nodes_plane/disc` (any admissible node configuration, uniform constants);
  - the node builders `exists_nodes_plane/disc` with a selection `sel` (ordinary nodes `λ` or alternative nodes `κ`, per cell);
  - `IsMassPartition.exists_cells`;
  - the class structures and `lapNorm`.
- **To M11 / M12 / BOC:**
  - `theorem4_disc_quant`, `theorem4_plane_quant` (uniform in the class);
  - the fixed `theorem4_disc`, `theorem4_plane`.
- **To M13 (line):** nothing directly. M13 reproduces the same scheme with barycentres (`m = 2`, where `Σ|I_i|/d ≲ 1` per ring suffices). Its far/near split and per-cell bounds mirror §3.4–§3.7.

---

## 5. Issues found (for NOTEBOOK)

1. **p. 363, Theorem 4: inequalities reversed.** It prints `d/ρ ≲ |h|e^{−ψ} ≲ (d/ρ)^M`. Since `d ≲ ρ` (Remark), this would force `d/ρ ≲ (d/ρ)^M`, false for `M > 1` as `d → 0`. Correct: `(d/ρ)^M ≲ |h|e^{−ψ} ≲ d/ρ`. The formal `theorem4_*` already state the correct form. The same reversal is at p. 372 (M11).
2. **pp. 366–367, (2) and (3): wrong sign of the middle term, and missing `+C` in (3).** With `log|h| = ψ − (1/2π)I` and `I = ∫ log|z−ζ| (Δψ − Σ2πδ)`, the true bounds are `M log(d/ρ) − C ≤ −I/2π ≤ log(d/ρ) + C`; the printed version bounds `I`. In (3) the right-hand side lacks `+C`.
3. **p. 366, `2π`.** As in README §4: the point masses carry `2π`, or equivalently all masses/moments are for `Δψ/2π`. We use `ν = Δψ/2π`, with cells of `ν`-mass `N`.
4. **p. 367, "immediate neighbours".** With nodes only *near* `R_i` (M06: the printed "inside `R`" is false), the paper's neighbour notion does not separate `z` from the nodes of non-neighbouring rectangles. We define near/far by `d(z,c_i)` versus `K₀ρ(c_i)`, with `K₀` chosen after the node spread.
5. **p. 367, Lemma 3 and `m` with `mγ > 1`.** Not needed. Moment order 3 plus area counting and the decay `ρ(ζ)/d ≲ (ρ(z)/d)^α` (§3.5) suffices for every locally doubling measure. Lemma 3 is still true (M03) but unused.
6. **pp. 368–369, the disc proof assumes hyperbolically small rectangles.** For sparse `Δψ` (e.g. `(1−|z|²)²Δψ ≡ δ` small, BOC's case), mass-`N` rectangles have hyperbolic size `≫ 1`, and then:
   - Lemma-5 nodes at Euclidean distance `≈ size` leave `𝔻`, which is fatal: `log|(z−λ)/(1−λ̄z)|` is singular at `1/λ̄ ∈ 𝔻`;
   - the Euclidean Taylor series in `(ζ−c)/(z−c)` may diverge for hyperbolically far `z`.

   **Fix (§3.4, §3.10):** large cells use barycentres (order 2, nodes in the convex hull ⊂ `𝔻`), and the far field uses a first-order Taylor bound along segments. Order 2 suffices in the far field because the Euclidean-moment remainder carries the extra factor `(1−|c|²)/|1−z̄c|`; this makes the Forelli–Rudin sum converge.

   **Matching moments in the Möbius coordinate `φ_c(ζ)` instead would not work:** the remainder is then only `≈ (1−ρ(z,c)²)`, and `Σ_cells (1−ρ(z,c_i)²) = ∞` (log-divergent hyperbolic area sum).
7. **p. 367, Taylor bound "`C|ζ−λ₀|^m/|z−w|^m` with `|z−w| ≃ |z−ζ|`"** is right in the plane. The disc analogue on p. 368 (`|∇^m log|(z−ζ)/(1−ζ̄z)|| ≲ (1−|z|²)/(|1−ζ̄z||z−ζ|^m)`) is right too, with the explicit constant `m!` (§3.1 (K3)).
8. **p. 368, "`M = 2 sup_z ρ(z)`"** reuses the letter `M` of Theorem 4 for an unrelated radius. Our near/far split is `M₀ ≤ 1/4`.
9. **p. 363, the Remark ("`M` can be chosen to be 1" with separated zeros)** is not obtained: M06 nodes have multiplicity `k = 4`. It is not used.

**Formalization risks.**
- **(R1) §3.8 item 7.** The interchange of `Σ_i` with `∫` and Fubini per cell: routine but long.
- **(R2) The disc geometry lemmas.** `norm_one_sub_conj_mul_comparable` needs the Möbius identity from M01.
- **(R3) ENNReal bookkeeping** in §3.11.
- **(R4) Dependence on the uniform M03/M05 forms (§4.1).** If M03/M05 keep `∃ C` after `μ`, the `_quant` statements, and hence BOC's uniform Theorem 2, are blocked. The per-weight `theorem4_*` and `prop2_*` would still follow.
