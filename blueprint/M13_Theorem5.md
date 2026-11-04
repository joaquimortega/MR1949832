# M13 — Theorem 5: multipliers for Laplacians carried by the real line

**Paper.** §4.3, pp. 374–375 (Theorem 5 and its two-line "proof": "the same as in Theorem 4 when `Ω = ℂ`, except that at some points it is easier. For instance, it is trivial to split the real line into intervals all of mass `N`").

**Lean files** (proposed split):
- `OrtegaCerdaMultipliers/Line/Basic.lean`: `IsLineMeasure`, `lineMeasure`, the bridge lemmas (§3.1);
- `OrtegaCerdaMultipliers/Line/Partition.lean`: `lineCDF`, `lineLevel`, `lineKnot`, `lineLength`, `lineCentre`, `lineNode` and §3.2–§3.3;
- `OrtegaCerdaMultipliers/Line/Potential.lean`: `lineTerm`, `linePotential` and §3.4–§3.6;
- `OrtegaCerdaMultipliers/Theorem5.lean`: §3.7–§3.8, `lineMultipliers`, `theorem5`.

**Depends on:**
- **M02**: `LogKernelStmt`, `WeylLaplacianStmt` (through M07), the uniform `L¹` bound for `log|z−a|` and the weak Laplacian of a logarithmic potential (§4.2, stated in Lean);
- **M03**: the line forms of Lemma 1, Claim 1, Claim 2, [Chr91, Lemma 2.3], reverse doubling, no atoms (§4.2, stated in Lean);
- **M07**: `IsWeakLogModulus`, `exists_analytic_norm_eq_exp_of_weak` (`LogModulus.lean`, compiled);
- **not** M05, M06, M08, M09. The line partition is built here (it must be adapted to a *signed* measure, §2), and Lemma 5 (Chebyshev quadrature) is replaced by barycentres (§0).
- **Mathlib:** `MeasurableEmbedding.comap_apply`, `MeasurableEmbedding.map_comap`, `Complex.isometry_ofReal`, `IsClosed.csInf_mem`, `intermediate_value_Icc`, `integral_withDensity_*`, `integral_tsum`, `continuousOn_tsum`, `Complex.volume_preserving_equiv_real_prod`, `InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane`, `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, and a bound `|log(1−w) + w| ≤ |w|²` for `|w| ≤ 1/2` (`Complex.norm_log_one_add_sub_self_le` or a direct power-series bound).

Scratch file with every statement below (all typecheck, proofs `sorry`; `theorem5` is *proved* there from `lineMultipliers`):
`/tmp/claude-1000/-home-quim-cloud-papers-Lean-1995ReineAngewMath/c37e0653-2eb9-4b15-945d-8755a676cb36/scratchpad/m1314_check.lean`.

---

## 0. Summary of the construction and of the deviations from the paper

1. **One barycentre per cell, moment order `m = 2`.** On the line, matching the mass and the first moment of `μ` on each cell is enough. The far-field error of a cell `I` at distance `d` is then `O((|I|/d)²)`. The number of cells at distance `≃ d` grows only *linearly*, and `|I| ≃ ρ` grows *sublinearly* (Lemma 1 on `ℝ`). So `Σ (|I|/d)²` converges uniformly. The paper's `N = mk` nodes with `m` moments, Chebyshev quadrature (Lemma 5) and Lemma 3 with `mγ > 1` are not needed.
   - The barycentre of a positive measure on a cell is real and lies in the cell. So **all zeros are real**, as Theorem 5 states.
   - The paper's literal route ("the same as Theorem 4") would use Lemma 5. M06 builds complex nodes (roots of a real polynomial, not necessarily real), and equal-weight quadrature with real nodes inside the interval fails in general (Bernstein). The literal route therefore does **not** give `Z(f) ⊆ ℝ`.
   - (This agrees with the coordinator's design note: "N copies of the μ-barycenter of each interval", with `N = 2` here.)
2. **Two multipliers per cell structure (needed by M14).** Each cell `I_k` carries `2` zeros:
   - `s = 0`: a double zero at the barycentre `λ_k`;
   - `s = s₀ > 0`: two simple zeros `λ_k ± s₀ a_k`, where `a_k = |I_k|`.
   
   Both node sets match moments `0` and `1`, both are real, and together all nodes are `≳ ρ`-separated. Hence the exceptional sets are disjoint (Proposition 2 on the line, §3.8).
3. **A signed Laplacian `μ − 2α·dt`, `0 ≤ α ≤ α₀`.** M14 (Theorem 3) needs multipliers for the weight `φ − α|Im z|` with some `α > 0`, i.e. `|f| ≃ e^{φ − α|Im z|}` (see M14 §2.2). Its Laplacian `μ − 2α dt` is *not* positive in general (e.g. `μ` singular w.r.t. Lebesgue measure), so Theorem 5 cannot be applied to it.
   - The paper's intended route ("in the same way as Theorems 1 and 2") would need a line version of Lemma 6 (regularisation), which the paper never states.
   - We instead run the construction directly with the **signed** measure `σ_α := μ − 2α·dt` on `ℝ`.
   - Only three properties of `σ_α` are used: cells of `σ_α`-mass exactly `4π`; `|σ_α|(I_k) ≤ μ(I_k) + 2α|I_k|` bounded; the barycentre stays inside the cell. All three hold for `α` small.
   - Theorem 5 is the case `α = 0`.

---

## 1. Statements

### 1.1 Paper

> **Theorem 5.** Let `φ` be subharmonic in `ℂ` such that `Δφ` is a locally doubling measure supported in the real line and `Δφ(I(x,r)) > 1` for some `r > 0`. There is a holomorphic `f` with zero set `Λ ⊆ ℝ` such that for any `ε > 0`, `|f(z)| ≃ e^{φ(z)}` for all `z` with `|z − λ_n| ≥ ε ρ(λ_n)` for all `λ_n ∈ Z(f)`.

### 1.2 Formal statements (namespace `OC`)

**Bundled hypotheses** (M13, new):
```lean
structure IsLineMeasure (μ : Measure ℂ) : Prop where
  finite_of_compact : ∀ K : Set ℂ, IsCompact K → μ K < ∞
  doubling : IsLocallyDoublingLine μ
  mass : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)

theorem IsLineMeasure.of_weight {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoublingLine μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) :
    IsLineMeasure μ
```

**Definitions** (M13, new):
```lean
/-- `μ` seen as a measure on `ℝ`. -/
-- (reconciled) M13's `linePull` is M03's `linePull` (same definition), used below:
-- def linePull (μ : Measure ℂ) : Measure ℝ := μ.comap fun x : ℝ ↦ (x : ℂ)

/-- Signed distribution function of `σ_α = μ − 2α·dt`: `G_α(t) = σ_α((0,t])` (oriented). -/
def lineCDF (μ : Measure ℂ) (α t : ℝ) : ℝ :=
  (if 0 ≤ t then (linePull μ (Ioc 0 t)).toReal else -(linePull μ (Ioc t 0)).toReal)
    - 2 * α * t

/-- First hitting time of the level `s` by `G_α`. -/
def lineLevel (μ : Measure ℂ) (α s : ℝ) : ℝ := sInf {t : ℝ | lineCDF μ α t = s}

/-- Knots `e_k = T_α(4π k)`; the cells are `I_k = (e_k, e_{k+1}]`, with `σ_α(I_k) = 4π`. -/
def lineKnot (μ : Measure ℂ) (α : ℝ) (k : ℤ) : ℝ := lineLevel μ α (4 * Real.pi * k)

def lineLength (μ : Measure ℂ) (α : ℝ) (k : ℤ) : ℝ := lineKnot μ α (k + 1) - lineKnot μ α k

/-- Signed barycentre `λ_k = (1/4π) ∫_{I_k} t dσ_α(t)`. -/
def lineCentre (μ : Measure ℂ) (α : ℝ) (k : ℤ) : ℝ :=
  ((∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), t ∂linePull μ) -
    2 * α * ∫ t in lineKnot μ α k..lineKnot μ α (k + 1), t) / (4 * Real.pi)

/-- The two nodes `λ_k ± s a_k` of the cell `I_k` (`b = true` is `+`). -/
def lineNode (μ : Measure ℂ) (α s : ℝ) (k : ℤ) (b : Bool) : ℝ :=
  lineCentre μ α k + (if b then s else -s) * lineLength μ α k

/-- `T_k(z) = (1/2π) ∫_{I_k} (½ log|z−ν₊| + ½ log|z−ν₋| − log|z−t|) dσ_α(t)`. -/
def lineTerm (μ : Measure ℂ) (α s : ℝ) (k : ℤ) (z : ℂ) : ℝ :=
  Real.log ‖z - lineNode μ α s k true‖ + Real.log ‖z - lineNode μ α s k false‖ -
    (1 / (2 * Real.pi)) *
      ((∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), Real.log ‖z - t‖ ∂linePull μ) -
        2 * α * ∫ t in lineKnot μ α k..lineKnot μ α (k + 1), Real.log ‖z - t‖)

def linePotential (μ : Measure ℂ) (α s : ℝ) (z : ℂ) : ℝ := ∑' k : ℤ, lineTerm μ α s k z

def lineNodeSet (μ : Measure ℂ) (α s : ℝ) (b : Bool) : Set ℂ :=
  range fun k : ℤ ↦ ((lineNode μ α s k b : ℝ) : ℂ)
def lineZeroSet (μ : Measure ℂ) (α s : ℝ) : Set ℂ :=
  lineNodeSet μ α s true ∪ lineNodeSet μ α s false
/-- `2` at `λ_k` when `s = 0`; `1` at `λ_k ± s a_k` when `0 < s ≤ s₁`. -/
def lineZeroCount (μ : Measure ℂ) (α s : ℝ) (z : ℂ) : ℕ :=
  (lineNodeSet μ α s true).indicator 1 z + (lineNodeSet μ α s false).indicator 1 z
```

**Exported lemmas** (M13):
```lean
-- 13.1 bridge ℂ ↔ ℝ
-- (reconciled) `linePull_apply` is M03's `linePull_apply` (no measurability needed):
-- theorem linePull_apply (μ : Measure ℂ) (s : Set ℝ) :
--     linePull μ s = μ ((fun x : ℝ ↦ (x : ℂ)) '' s)
theorem map_linePull {μ : Measure ℂ} (hμ : μ {z : ℂ | z.im ≠ 0} = 0) :
    (linePull μ).map (fun t : ℝ ↦ (t : ℂ)) = μ
theorem IsLineMeasure.linePull_Ioc_lt_top {μ : Measure ℂ} (hμ : IsLineMeasure μ) (a b : ℝ) :
    linePull μ (Ioc a b) < ∞

-- 13.2 the signed distribution function
theorem lineCDF_sub {μ : Measure ℂ} (hμ : IsLineMeasure μ) (α : ℝ) {a b : ℝ} (hab : a ≤ b) :
    lineCDF μ α b - lineCDF μ α a = (linePull μ (Ioc a b)).toReal - 2 * α * (b - a)
theorem continuous_lineCDF {μ : Measure ℂ} (hμ : IsLineMeasure μ) (α : ℝ) :
    Continuous (lineCDF μ α)
theorem lineCDF_add_ge {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hαr : α * r ≤ 1 / 8) (t : ℝ) :
    lineCDF μ α t + 1 / 2 ≤ lineCDF μ α (t + 2 * r)

-- 13.3 the knots (same hypotheses hμ hr hmr hα hαr in each)
theorem lineCDF_lineKnot … (k : ℤ) : lineCDF μ α (lineKnot μ α k) = 4 * Real.pi * k
theorem lineKnot_strictMono … : StrictMono (lineKnot μ α)
theorem lineLength_le … (k : ℤ) : lineLength μ α k ≤ 52 * r
theorem existsUnique_lineKnot_mem … (t : ℝ) :
    ∃! k : ℤ, t ∈ Ioc (lineKnot μ α k) (lineKnot μ α (k + 1))
theorem linePull_Ioc_lineKnot … (k : ℤ) :
    linePull μ (Ioc (lineKnot μ α k) (lineKnot μ α (k + 1))) =
      ENNReal.ofReal (4 * Real.pi + 2 * α * lineLength μ α k)

-- 13.4 barycentres and separation
theorem IsLineMeasure.lineCentre_mem {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ c₀ : ℝ, 0 < α₁ ∧ 0 < c₀ ∧ c₀ ≤ 1 / 4 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ k : ℤ,
      lineKnot μ α k + c₀ * lineLength μ α k ≤ lineCentre μ α k ∧
      lineCentre μ α k ≤ lineKnot μ α (k + 1) - c₀ * lineLength μ α k
theorem IsLineMeasure.lineNode_separated {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 < s → s ≤ s₁ →
      ∀ ν ∈ range (fun p : ℤ × Bool ↦ lineNode μ α 0 p.1 p.2) ∪
          range (fun p : ℤ × Bool ↦ lineNode μ α s p.1 p.2),
      ∀ ν' ∈ range (fun p : ℤ × Bool ↦ lineNode μ α 0 p.1 p.2) ∪
          range (fun p : ℤ × Bool ↦ lineNode μ α s p.1 p.2),
      ν ≠ ν' → s / 2 * (massRadiusLine μ ν + massRadiusLine μ ν') ≤ |ν - ν'|

-- 13.5 one term
theorem IsLineMeasure.abs_lineTerm_le_of_far {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → ∀ (k : ℤ) (z : ℂ),
      2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ →
      |lineTerm μ α s k z| ≤ 8 * (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2
theorem IsLineMeasure.lineTerm_le_of_near {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ C : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 →
      ∀ (k : ℤ) (z : ℂ), ‖z - lineCentre μ α k‖ < 2 * lineLength μ α k →
      (∀ b : Bool, z ≠ lineNode μ α s k b) → lineTerm μ α s k z ≤ C
theorem IsLineMeasure.le_lineTerm_of_near {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ C : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 ≤ s → s ≤ s₁ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (k : ℤ) (z : ℂ),
      ‖z - lineCentre μ α k‖ < 2 * lineLength μ α k →
      (∀ b : Bool, η * massRadiusLine μ (lineNode μ α s k b) ≤ ‖z - lineNode μ α s k b‖) →
      2 * Real.log η - C ≤ lineTerm μ α s k z

-- 13.6 the potential
theorem IsLineMeasure.summable_lineTerm {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → ∀ z : ℂ,
      Summable fun k : ℤ ↦ lineTerm μ α s k z
theorem IsLineMeasure.linePotential_bounds {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ C : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 ≤ s → s ≤ s₁ →
      (∀ z, z ∉ lineZeroSet μ α s → linePotential μ α s z ≤ C) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ z : ℂ,
        (∀ ν ∈ lineZeroSet μ α s, η * massRadiusLine μ ν.re ≤ ‖z - ν‖) →
        -C * (1 + |Real.log η|) ≤ linePotential μ α s z

-- 13.7 Laplacian of |Im z|
theorem integral_abs_im_mul_laplacian (χ : ℂ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) :
    ∫ z, |z.im| * Laplacian.laplacian χ z = 2 * ∫ t : ℝ, χ t

-- 13.8 continuity of the potential of a piece of μ
theorem IsLineMeasure.continuous_logPotential_Ioc {μ : Measure ℂ} (hμ : IsLineMeasure μ)
    (a b : ℝ) :
    Continuous fun z : ℂ ↦ ∫ t in Ioc a b, Real.log ‖z - t‖ ∂linePull μ

-- 13.9 the M07 input
theorem isWeakLogModulus_linePotential {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight univ φ μ) (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 ≤ s → s ≤ s₁ →
      IsWeakLogModulus univ (lineZeroCount μ α s)
        (fun z ↦ φ z - α * |z.im| + linePotential μ α s z)

-- 13.10 MAIN EXPORT (consumed by M14)
theorem lineMultipliers (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoublingLine μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₀ →
      ∃ (f : Fin 2 → ℂ → ℂ) (ε C : ℝ), 0 < ε ∧ 0 < C ∧
        (∀ i, Differentiable ℂ (f i)) ∧ (∀ i, ∃ z₀, f i z₀ ≠ 0) ∧
        (∀ i (z : ℂ), f i z = 0 → z.im = 0) ∧
        (∀ i (z : ℂ), ‖f i z‖ ≤ C * Real.exp (φ z - α * |z.im|)) ∧
        (∀ z : ℂ, ∃ i, ∀ x : ℝ, f i x = 0 → ε * massRadiusLine μ x ≤ ‖z - x‖) ∧
        ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∀ i (z : ℂ),
          (∀ x : ℝ, f i x = 0 → η * massRadiusLine μ x ≤ ‖z - x‖) →
            c * Real.exp (φ z - α * |z.im|) ≤ ‖f i z‖

-- 13.11 the comparator statement (verbatim)
theorem theorem5 (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoublingLine μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z₀, f z₀ ≠ 0) ∧ (∀ z, f z = 0 → z.im = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
        (∀ x : ℝ, f x = 0 → ε * massRadiusLine μ x ≤ ‖z - x‖) →
          C⁻¹ * Real.exp (φ z) ≤ ‖f z‖ ∧ ‖f z‖ ≤ C * Real.exp (φ z)
```
(The `…` in 13.3 abbreviate `{μ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r) (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8)`; the full text is in the scratch file.)

**On `theorem5` (verdict).** The statement is correct, non-vacuous, and follows from `lineMultipliers` at `α = 0` by a 15-line proof that **compiles** in the scratch file.
- `ρ = massRadiusLine μ` is `> 0` (no atoms, M03-L4), so the exceptional condition is never vacuous at a zero.
- `ρ ≤ r` (mass condition), so `massRadiusLine` is never a junk `sInf ∅ = 0`.
- Zeros of `f 0` (`s = 0`) are *double* zeros at the barycentres. Theorem 5 does not ask for simple zeros. If simple zeros are wanted, use `f 1`.

---

## 2. Setting, notation and constants

Fix `φ, μ` with `hφ : IsSubharmonicWeight univ φ μ`, `hd`, and `hm`. Choose `r > 0` with `μ(I(x,r)) > 1` for all `x`; `hμ := IsLineMeasure.of_weight hφ hd hm` (`finite_of_compact` is `hφ.finite_of_compact`).

- `μ_ℝ := lineMeasure μ`. For a Borel `s ⊆ ℝ`, `μ_ℝ(s) = μ(ι '' s)` with `ι = (↑) : ℝ → ℂ`, and `μ = ι_* μ_ℝ` (13.1). All one-dimensional analysis is done with `μ_ℝ`.
- `I(x,R) := Ioo (x−R) (x+R)`. Then `lineInterval x R = ι '' I(x,R)`, so `μ(lineInterval x R) = μ_ℝ(I(x,R))`.
- `σ_α := μ_ℝ − 2α·Leb` (never formed as a Lean object; only `μ_ℝ`-integrals and interval integrals appear).
- **Scales.**
  - `A := 52 r` is the cell length bound (13.3).
  - `A₀ := 512 r` is the largest radius at which doubling is used.
- **Constants from M03** (all at scale `A₀`):
  - `C_D ≥ 1`: doubling (L1);
  - `q < 1`: reverse doubling (L3);
  - `C_L`: logarithmic integrability (L8);
  - `C₁`: Claim 1 with `K = 1`, and `C₅`: Claim 1 with `K = 2C₂` (L5);
  - `γ, C_g`: Lemma 1 (L6);
  - `C₂`: Claim 2 with `m₁ = 4π`, `m₂ = 4π + 13` (L7).
- **Derived constants.**
  - `c_b := 1/(2C_D²)`: margin of the μ-barycentre;
  - `α₁ := min(1/(8r), 2π c_b / A)`;
  - `c₀ := c_b/2 ≤ 1/4`;
  - `s₁ := c₀/2 ≤ 1/8`: the largest node offset allowed;
  - for the multipliers: `s₀ := s₁`, `κ := s₀/2`, `ε := κ/2`.
  
  The `α₁` (resp. `s₁`) of each existential lemma can be taken to be this one (smaller is harmless). M14 receives `α₀ := α₁`.

Throughout, `0 ≤ α ≤ α₁` (so `αr ≤ 1/8`). In 13.5 (far field, near upper bound) and in `summable_lineTerm`, `0 ≤ s ≤ 1/2` suffices. In `le_lineTerm_of_near`, `linePotential_bounds`, `lineNode_separated` and `isWeakLogModulus_linePotential`, we need `0 ≤ s ≤ s₁`. Only then are the nodes inside their own cell, and the maps `k ↦ ν_k^±` injective, which the zero count needs; for `s` near `1/2` and `c₀` small, nodes of adjacent cells could coincide. Write:
- `e_k := lineKnot μ α k`, `I_k := (e_k, e_{k+1}]`, `a_k := e_{k+1} − e_k`;
- `m_k := (e_k + e_{k+1})/2`, `λ_k := lineCentre μ α k`;
- `ν_k^± := λ_k ± s a_k`.

---

## 3. Proofs

### 3.1 Bridge (13.1)

- `ι` is an isometry (`Complex.isometry_ofReal`), hence a closed embedding (`Isometry.isClosedEmbedding`), hence a measurable embedding (`IsClosedEmbedding.measurableEmbedding`).
- `lineMeasure_apply` is `MeasurableEmbedding.comap_apply`.
- `map_lineMeasure`:
  - `MeasurableEmbedding.map_comap` gives `ι_* μ_ℝ = μ.restrict (range ι)`;
  - `range ι = {z | z.im = 0}`, whose complement is `μ`-null by `hd.1`;
  - so `μ.restrict (range ι) = μ` (`Measure.restrict_eq_self_of_ae_mem`).
- `lineMeasure_Ioc_lt_top`: `ι '' Ioc a b ⊆ ι '' Icc a b`, which is compact; use `hμ.finite_of_compact`.

### 3.2 The signed distribution function (13.2)

- **`lineCDF_sub`.** Three cases: `0 ≤ a`, `a < 0 ≤ b`, `b < 0`.
  - Use `Ioc 0 b = Ioc 0 a ∪ Ioc a b` (disjoint), resp. `Ioc a b = Ioc a 0 ∪ Ioc 0 b`, resp. `Ioc a 0 = Ioc a b ∪ Ioc b 0`.
  - Then `measure_union` and `ENNReal.toReal_add` (finiteness from 13.1).
- **`continuous_lineCDF`.** It suffices that `F(t) := lineCDF μ 0 t` is continuous.
  - `F` is monotone (`lineCDF_sub` with `α = 0`).
  - At `t`: `F(t+h) − F(t) = μ_ℝ(Ioc t (t+h)) → μ_ℝ(∅) = 0` as `h ↓ 0` (continuity from above, `tendsto_measure_iInter_atTop`, finite measure). Similarly `F(t) − F(t−h) = μ_ℝ(Ioc (t−h) t) → μ_ℝ({t}) = 0` as `h ↓ 0`. Here `μ_ℝ({t}) = μ({ι t}) = 0` by M03-L2 (no atoms).
  - Monotone plus both one-sided limits gives continuity (`Monotone.continuous_of_…`, or directly by an `ε–δ` argument).
- **`lineCDF_add_ge`.**
  - `G(t+2r) − G(t) = μ_ℝ(Ioc t (t+2r)) − 4αr`.
  - `μ_ℝ(Ioc t (t+2r)) ≥ μ_ℝ(I(t+r, r)) = μ(lineInterval (t+r) r) > 1`.
  - `4αr ≤ 1/2`.
  - Hence `G(t+2r) − G(t) > 1/2`.
- **Consequences** (internal):
  - `G(t + 2rn) ≥ G(t) + n/2` for `n ∈ ℕ`;
  - `G → +∞` at `+∞` and `G → −∞` at `−∞`: for `t ≤ 0` write `t = t' − 2rn` with `t' ∈ (−2r, 0]`; then `G(t) ≤ max_{[−2r,0]} G − n/2`.

### 3.3 The knots (13.3)

Let `Z_s := {t | G(t) = s}`.
- **`Z_s` is nonempty, closed and bounded below.**
  - Nonempty: IVT (`intermediate_value_Icc`), using the limits at `±∞` and continuity.
  - Closed: preimage of a point under a continuous map.
  - Bounded below: `G < s` on some `(−∞, t₁]`.
  
  So `T(s) := sInf Z_s ∈ Z_s` (`IsClosed.csInf_mem`), i.e. `G(T(s)) = s`. This is `lineCDF_lineKnot` with `s = 4πk`.
- **Strict monotonicity.** Let `s < s'`. `G(T(s')) = s' > s` and `G → −∞`, so by IVT some `t < T(s')` has `G(t) = s`. Hence `T(s) ≤ t < T(s')`.
- **`lineLength_le`.**
  - Iterating `lineCDF_add_ge` 26 times: `G(e_k + 52 r) ≥ G(e_k) + 13 > 4πk + 4π = 4π(k+1)`, since `13 > 4π`.
  - By IVT on `[e_k, e_k + 52r]` there is `t` with `G(t) = 4π(k+1)`, so `e_{k+1} = T(4π(k+1)) ≤ t ≤ e_k + 52 r`.
  - Hence `a_k ≤ 52 r = A`.
- **`existsUnique_lineKnot_mem`.**
  - `G(e_k) = 4πk` and `G` is bounded on bounded sets, so `e_k → ±∞` as `k → ±∞`.
  - Given `t`, take `k := max {j | e_j < t}`, which exists since `e` is strictly monotone and unbounded in both directions. Uniqueness follows from monotonicity.
- **`lineMeasure_Ioc_lineKnot`.** By `lineCDF_sub`, `μ_ℝ(I_k) = G(e_{k+1}) − G(e_k) + 2α a_k = 4π + 2α a_k`.
  - Consequence: `4π ≤ μ_ℝ(I_k) ≤ 4π + 2αA ≤ 4π + 13`, since `2αA = 104 αr ≤ 13`.
  - Also `|σ_α|(I_k) ≤ μ_ℝ(I_k) + 2α a_k ≤ 4π + 26`.
  - Also `a_k > 0` (strict monotonicity) and `a_k ≥ ρ(t)` for `t ∈ [e_k, e_{k+1}]` (L7).

### 3.4 Barycentres and separation (13.4)

**The μ-barycentre is in the middle (internal lemma).** Let `b_k := μ_ℝ(I_k)⁻¹ ∫_{I_k} t dμ_ℝ`. Claim: `e_k + c_b a_k ≤ b_k ≤ e_{k+1} − c_b a_k`, with `c_b = 1/(2C_D²)`.
- Let `J := (m_k, e_{k+1})` be the right half: centre `m_k + a_k/4`, radius `a_k/4`.
- Then `I_k ⊆ I(m_k + a_k/4, a_k)`, so two doublings give `μ_ℝ(I_k) ≤ C_D² μ_ℝ(J)` (radius `a_k/4 ≤ A₀`).
- Hence `b_k − e_k = μ_ℝ(I_k)⁻¹ ∫_{I_k}(t − e_k) dμ_ℝ ≥ μ_ℝ(I_k)⁻¹ (a_k/2) μ_ℝ(J) ≥ a_k/(2C_D²)`.
- The other side is symmetric.

**`lineCentre_mem`.** From the definitions:
- `∫_{I_k} t dμ_ℝ = μ_ℝ(I_k) b_k` and `∫_{e_k}^{e_{k+1}} t dt = a_k m_k`;
- with `μ_ℝ(I_k) = 4π + 2αa_k`:

  `λ_k = ((4π + 2αa_k) b_k − 2α a_k m_k)/(4π) = b_k + (α a_k/2π)(b_k − m_k)`.
- So `|λ_k − b_k| ≤ (α a_k/2π)(a_k/2) ≤ (αA/4π) a_k ≤ (c_b/2) a_k`, because `α ≤ 2πc_b/A`.
- Hence `e_k + c₀ a_k ≤ λ_k ≤ e_{k+1} − c₀ a_k` with `c₀ = c_b/2`.

**Nodes stay inside — this is why `s ≤ s₁`.** For `0 ≤ s ≤ s₁ = c₀/2`: `ν_k^± ∈ [e_k + (c₀/2)a_k, e_{k+1} − (c₀/2)a_k]`, strictly inside `I_k`. In particular:
- `|ν_k^± − λ_k| ≤ s a_k ≤ a_k/2` and `|t − λ_k| ≤ a_k` for `t ∈ I_k`. These two facts, the only ones used by the far field and the near upper bound, hold for all `s ≤ 1/2` once `λ_k` is in the cell.
- `a_k ≤ C₂ ρ(ν_k^±)` (L7 on `[e_k, e_{k+1}]`), used by the near lower bound.
- Nodes of different cells are distinct, so `k ↦ ν_k^b` is injective, as is `k ↦ λ_k`. For `s > 0`, also `ν_k^+ ≠ ν_j^-` for all `k, j`.

**`lineNode_separated`** (separation constant `s/2`, for `0 < s ≤ s₁`). Let `N := {λ_k} ∪ {λ_k ± s a_k}`, the union of the node sets of offsets `0` and `s`. Each `ν ∈ N` from cell `k` has `ρ(ν) ≤ a_k` (L7, first part: `μ(I(ν, a_k)) ≥ μ_ℝ((e_k,e_{k+1})) ≥ 4π ≥ 1`).
- **Same cell, `ν ≠ ν'`.** The three points `λ_k − s a_k < λ_k < λ_k + s a_k` have gaps `s a_k`. So `|ν − ν'| ≥ s a_k ≥ (s/2)(ρ(ν) + ρ(ν'))`.
- **Cells `k < k'`.** `ν ≤ e_{k+1} − (c₀/2)a_k` and `ν' ≥ e_{k'} + (c₀/2)a_{k'} ≥ e_{k+1} + (c₀/2)a_{k'}`. So `|ν − ν'| ≥ (c₀/2)(a_k + a_{k'}) ≥ (s/2)(ρ(ν)+ρ(ν'))`, since `s ≤ c₀/2`.

### 3.5 One term (13.5)

**Algebraic identities** (internal, from 13.3 and the definition of `λ_k`):
- (M0) `μ_ℝ(I_k) − 2α a_k = 4π`;
- (M1) `∫_{I_k} t dμ_ℝ − 2α ∫_{e_k}^{e_{k+1}} t dt = 4π λ_k`;
- (N) `ν_k^+ + ν_k^- = 2λ_k`.

**Elementary bound** (internal). For `w ∈ ℂ` with `‖w‖ ≤ 1/2`:
`|log|1 − w| + Re w| ≤ |log(1−w) + w| ≤ Σ_{n≥2} |w|ⁿ/n ≤ |w|²/(2(1−|w|)) ≤ |w|²`.
(Mathlib: `Complex.norm_log_one_add_sub_self_le` or the `hasSum` of `−log(1−w)`; `Real.log ‖1 − w‖ = Re (Complex.log (1 − w))` via `Complex.log_re`.)

**Far field** (`‖z − λ_k‖ ≥ 2a_k`). Put `d := ‖z − λ_k‖`, `w_t := (t − λ_k)/(z − λ_k)` for `t ∈ I_k` (`|w_t| ≤ a_k/d ≤ 1/2`), and `w_± := (ν^± − λ_k)/(z − λ_k)` (`|w_±| ≤ s a_k/d ≤ 1/4`).
1. Write `log|z − ζ| = log d + log|1 − w_ζ|` for `ζ ∈ {ν^±} ∪ I_k`. This is valid since `z − ζ ≠ 0`.
2. By (M0), the `log d` terms cancel: `2 log d − (1/2π)(μ_ℝ(I_k) − 2αa_k) log d = 0`.
3. By (M1), `∫_{I_k} Re w_t dσ_α = Re((z − λ_k)⁻¹(4πλ_k − 4πλ_k)) = 0`.
4. By (N), `Re(w_+ + w_−) = 0`.
5. Hence
   `T_k(z) = [log|1−w_+| + Re w_+] + [log|1−w_−| + Re w_−] − (1/2π) ∫_{I_k} [log|1 − w_t| + Re w_t] dσ_α(t)`.
6. By the elementary bound:
   `|T_k(z)| ≤ 2 s² (a_k/d)² + (|σ_α|(I_k)/2π)(a_k/d)² ≤ (1/2 + (4π+26)/2π)(a_k/d)² ≤ 8 (a_k/d)²`.

In Lean, the signed integral is the difference of the `μ_ℝ`-integral and `2α ×` the interval integral. Both integrands are bounded continuous on `I_k`, since `z` is at distance `≥ a_k` from `I_k`.

**Near field, upper bound** (`d < 2a_k`, `z ∉ {ν^±}`). Let `x := Re z`.
1. **Distances.**
   - `|z − ν^±| ≤ d + a_k/2 < 3a_k`.
   - For `t ∈ I_k`: `|x − t| ≤ |z − t| ≤ d + a_k < 3a_k`, using `|z − t| ≥ |Re z − t|` since `t` is real.
   - Hence `I_k ⊆ I(x, 3a_k)`.
2. **The `μ` part.**
   `−(1/2π)∫_{I_k} log|z−t| dμ_ℝ ≤ −(1/2π)∫_{I_k} log|x−t| dμ_ℝ = (1/2π)∫_{I_k} log(3a_k/|x−t|) dμ_ℝ − (μ_ℝ(I_k)/2π) log(3a_k)`.
   - The integrand `log(3a_k/|x−t|)` is `> 0` on `I_k`.
   - So the integral is `≤ ∫⁻_{I(x,3a_k)} log⁺(3a_k/|x−t|) dμ_ℝ ≤ C_L μ(I(x,3a_k))` (M03-L8, radius `3a_k ≤ A₀`).
   - **Bounding `μ(I(x,3a_k))`.** We have `|x − m_k| ≤ d + a_k/2 < 2.5 a_k`, so `I(x, 3a_k) ⊆ I(m_k, 8a_k) = I(m_k, 2⁴ · a_k/2)`. Since `I(m_k, a_k/2) = (e_k, e_{k+1})`, four doublings give `μ(I(x,3a_k)) ≤ C_D⁴ (4π + 13) =: M_near`.
3. **The Lebesgue part.** `(α/π)∫_{I_k} log|z−t| dt ≤ (α/π) a_k log(3a_k)`.
4. **The node part.** `log|z − ν^±| ≤ log(3a_k)` each.
5. **Sum.** The coefficient of `log(3a_k)` is `2 − (μ_ℝ(I_k) − 2αa_k)/2π = 2 − 2 = 0` by (M0). Hence `T_k(z) ≤ C_L M_near/(2π) =: C_n'`.

The non-node hypothesis matters here. Lean's `log 0 = 0` could exceed `log(3a_k)` when `a_k < 1/3`, so at a node the junk value is not controlled.

**Near field, lower bound** (`d < 2a_k`, `0 < η ≤ 1`, `ηρ(ν^±) ≤ |z − ν^±|`).
1. **Node part.** `log|z − ν^±| ≥ log(η ρ(ν^±)) ≥ log(η a_k/C₂)`, by L7: `a_k ≤ C₂ ρ(t)` on `[e_k, e_{k+1}]`.
2. **The `μ` part.** `−(1/2π)∫_{I_k} log|z−t| dμ_ℝ ≥ −(μ_ℝ(I_k)/2π) log(3a_k)`.
3. **The Lebesgue part.**
   `(α/π)∫_{I_k} log|z−t| dt ≥ (α/π)∫_{I_k} log|x−t| dt ≥ (α/π)(a_k log a_k − 2a_k)`.
   - Indeed `∫_{I_k} log|x−t| dt = a_k log a_k + ∫_{I_k} log(|x−t|/a_k) dt`.
   - And `log(|x−t|/a_k) ≥ −log⁺(a_k/|x−t|)`, with `∫_ℝ log⁺(a/|x−t|) dt = 2a`.
4. **Sum** (by (M0)):
   `T_k ≥ 2 log(ηa_k/C₂) − (2 + αa_k/π) log(3a_k) + (αa_k/π)(log a_k − 2) = 2log η − 2log(3C₂) − (αa_k/π)(2 + log 3)`.
   
   Hence `T_k(z) ≥ 2 log η − C_n` with `C_n := 2 log(3C₂) + (α₁A/π)(2 + log 3)`.

### 3.6 The sum (13.6)

Fix `z`, put `x := Re z`, and let `K(z) := {k | ‖z − λ_k‖ < 2a_k}` (near cells).

**(a) `#K(z) ≤ N₀ := 6C₂C₅² + 1`, uniformly in `z`.**
- For `k ∈ K(z)`: `|x − λ_k| ≤ ‖z − λ_k‖ < 2a_k ≤ 2C₂ρ(λ_k)`.
- Claim 1 (L5, `K = 2C₂`, applied in both orders) gives `ρ(x)/C₅ ≤ ρ(λ_k) ≤ C₅ ρ(x)`.
- Hence `ρ(x)/C₅ ≤ a_k ≤ C₂C₅ ρ(x)`, using `ρ(λ_k) ≤ a_k` (L7).
- So the near cells are disjoint intervals of length `≥ ρ(x)/C₅` contained in `I(x, 3C₂C₅ρ(x))`, which bounds their number.

**(b) Far sum.** `Σ_{k∉K(z)} |T_k(z)| ≤ C_far` uniformly in `z`.
1. **From cells to an integral.** For `k ∉ K(z)` and `t ∈ I_k`:
   - `|z − t| ≥ |z − λ_k| − a_k ≥ a_k`;
   - `|z − t| ≥ |x − t|`;
   - `|z − t| ≤ |z − λ_k| + a_k ≤ (3/2)|z−λ_k|`.
   
   Hence `(a_k/|z−λ_k|)² = a_k⁻¹ ∫_{I_k} a_k²/|z−λ_k|² dt ≤ (9/4) ∫_{I_k} a(t)/max(|x−t|, a(t))² dt`. Here `a(t) := a_k` for `t ∈ I_k`; it is well defined by `existsUnique_lineKnot_mem`.
2. So `Σ_{k∉K(z)} |T_k(z)| ≤ 18 Φ(x)` with `Φ(x) := ∫_ℝ a(t)/max(|x−t|, a(t))² dt`.
3. **Bounding `Φ`.** Use `ρ(t) ≤ a(t) ≤ C₂ρ(t)` (L7) and split into three regions.
   - **R1: `|x−t| ≤ ρ(x)`.** The integrand is `≤ 1/a(t) ≤ 1/ρ(t) ≤ C₁/ρ(x)` (Claim 1, `K = 1`). The contribution is `≤ 2C₁`.
   - **R2: `ρ(x) < |x−t| ≤ 1`.** The integrand is `≤ C₂ρ(t)/|x−t|² ≤ C₂C_g ρ(x)^γ |x−t|^{−1−γ}` (Lemma 1, L6). The contribution is `≤ 2C₂C_g ρ(x)^γ ∫_{ρ(x)}^∞ u^{−1−γ} du = 2C₂C_g/γ`.
   - **R3: `|x−t| > 1`.** The integrand is `≤ A/|x−t|²`. The contribution is `≤ 2A`.
   
   So `C_far := 18(2C₁ + 2C₂C_g/γ + 2A)`.

*Equivalent dyadic form* (coordinator's note). Group the far cells into rings `d ∈ [2ⁿρ(x), 2ⁿ⁺¹ρ(x))`.
- In a ring, `Σ|I_k| ≲ d` (the cells are disjoint).
- `max|I_k|/d ≲ (ρ(x)/d)^γ = 2^{−nγ}` by L6.
- So the ring sum is `≲ 2^{−nγ}`, which sums over `n`.
- For `d ≥ 1`, use `|I_k| ≤ A` and `Σ|I_k|/d² ≲ ∫_{|t−x|≥1} dt/|t−x|²`.

The integral form above is the one to formalise: it avoids ring bookkeeping. **Any `γ > 0` suffices; the paper's Lemma 3 with `mγ > 1` is not needed.**

**(c) Conclusions.**
- **`summable_lineTerm`.** There are finitely many near terms, and `Σ_{far} |T_k(z)| < ∞` by (b) (`Summable.of_norm_bounded_eventually`, or split off the finite set `K(z)`).
- **`linePotential_bounds`, upper bound.** For `z ∉ lineZeroSet`: `S(z) ≤ C_far + N₀ max(C_n', 0)`.
- **`linePotential_bounds`, lower bound.** If `z` is `η`-far from all nodes (`0 < η ≤ 1`), each near term is `≥ 2 log η − C_n`, a negative quantity. So `S(z) ≥ −C_far − N₀(C_n + 2|log η|) ≥ −C(1 + |log η|)` with `C := C_far + N₀(C_n + 2) + C_n'`.
  - In Lean, the `tsum` is split as `∑' = ∑_{k∈K(z)} + ∑'_{k∉K(z)}` (`sum_add_tsum_compl`). `K(z)` is finite by (a); concretely it is a subset of an explicit `Finset.Icc` of indices, because `e_k → ±∞`.

**Far from ℝ.** If `|Im z| ≥ 2A`, then `K(z) = ∅` (as `‖z − λ_k‖ ≥ |Im z| ≥ 2a_k`), and `|S(z)| ≤ C_far`. No separate argument is needed: `φ` is harmonic there, and the estimate (b) is uniform in `Im z` because it only uses `|z − t| ≥ |Re z − t|`.

### 3.7 Laplacian, continuity, and the M07 input (13.7–13.9)

**13.7 (`∫|Im z| Δχ = 2∫_ℝ χ`).**
- Transport to `ℝ × ℝ` (`Complex.volume_preserving_equiv_real_prod`).
- Write `Δχ = ∂²_xχ + ∂²_yχ` (`laplacian_eq_iteratedFDeriv_complexPlane`; M01's `lap` calculus may already provide the coordinate form).
- Apply Fubini (compact support).
- **The `∂²_x` part.** `∫ ∂²_x χ(x,y) dx = 0` for each `y` (FTC, compact support).
- **The `∂²_y` part.** For fixed `x`, let `g(y) := χ(x,y)`. Integrating by parts on `[0,R]` with `R` beyond the support (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`):
  - `∫_0^∞ y g''(y) dy = [y g']_0^R − ∫_0^R g' = g(0)`;
  - similarly `∫_{−∞}^0 (−y) g''(y) dy = g(0)`.
  
  Sum: `2χ(x,0)`; then integrate in `x`.
- Consequently `Δ(α|Im z|) = 2α · (ι_* Leb)`.

**13.8 (continuity of `p(z) := ∫_{Ioc a b} log|z−t| dμ_ℝ`).** Fix `z₀` and `η ∈ (0,1)`.
1. **Split.** `log|z−t| = max(log|z−t|, log η) + min(0, log(|z−t|/η))`.
2. **First summand.** It is jointly continuous and bounded for `z` near `z₀` and `t ∈ [a,b]`, so its integral is continuous in `z` (`continuous_of_dominated` / `continuousAt_of_dominated`).
3. **Second summand.** It is `≤ 0`, and with `x = Re z` its absolute integral is
   `≤ ∫_{|x−t|<η} log(η/|x−t|) dμ_ℝ ≤ C_L μ(I(x,η)) ≤ C_L ω(η)`.
   Here `ω(η) := sup_{x ∈ [Re z₀ − 1, Re z₀ + 1]} μ_ℝ(I(x,η)) → 0` as `η → 0`: the distribution function `F` is uniformly continuous on compacts (it is continuous by 13.2), and `μ_ℝ(I(x,η)) ≤ F(x+η) − F(x−η)`.
4. **Conclude** with an `ε/3` argument.

The same proof, with `Leb` in place of `μ_ℝ`, gives continuity of `∫_a^b log|z−t| dt`. Alternatively, Lebesgue measure is itself a line measure.

Junk values: at `z = x ∈ [a,b]` the integrand has `log 0 = 0` at `t = x`, a `μ_ℝ`-null point (no atoms). Integrability of `log|x − ·|` on `[a,b]` is L8.

**13.9 (`IsWeakLogModulus univ n v`)** with `n := lineZeroCount μ α s` and `v := φ − α|Im| + S`, `S := linePotential μ α s`. There are four fields.
1. **`finite_support`.** The nodes lie in `[e_k, e_{k+1}]`, and only finitely many cells meet a compact set (`e_k → ±∞`).
2. **`locallyIntegrableOn`.** Fix a compact `Q`.
   - `φ` and `|Im|` are continuous.
   - On `Q`, all but finitely many `k` satisfy `dist(λ_k, Q) ≥ 2a_k` (as `a_k ≤ A` and `λ_k → ±∞`). Those terms are bounded by `8 a_k²/dist(λ_k,Q)²`, which is summable, so the tail converges uniformly on `Q`.
   - The finitely many remaining terms are each `L¹(Q)`: the node logs by M02 (`LogKernelStmt.1`), the potentials by 13.8.
3. **`continuousOn` off `supp n`.** The same uniform convergence (`continuousOn_tsum`), with each term continuous off its nodes (13.8).
4. **`laplacian_eq`.** For a test `χ`:
   - `∫ φ Δχ = ∫ χ dμ` (`hφ.laplacian_eq`);
   - `∫ α|Im| Δχ = 2α∫_ℝ χ` (13.7);
   - `∫ S Δχ = Σ_k ∫ T_k Δχ` (`integral_tsum`: on `supp χ` all but finitely many `T_k` are uniformly bounded by a summable sequence; the rest are integrable);
   - and for each `k`, by `LogKernelStmt` and `integral_logPotential_mul_laplacian` (M02), applied to `ν = ι_*(μ_ℝ|_{I_k})` and to `ν = ι_*(Leb|_{I_k})`:
     `∫ T_k Δχ = 2π(χ(ν_k^+) + χ(ν_k^-)) − ∫_{I_k} χ dμ_ℝ + 2α ∫_{I_k} χ dt`.
   
   Summing over `k`:
   - the cells partition `ℝ` (`existsUnique_lineKnot_mem`), so `Σ_k ∫_{I_k} χ dμ_ℝ = ∫ χ dμ` (13.1 `map_lineMeasure` and `integral_map`) and `Σ_k ∫_{I_k} χ dt = ∫_ℝ χ`;
   - only finitely many terms are nonzero.
   
   Total: `∫ v Δχ = 2π Σ_k (χ(ν_k^+) + χ(ν_k^-)) = 2π ∑ᶠ ζ, n(ζ) χ(ζ)`, because `n = 1_{Z⁺} + 1_{Z⁻}` and `k ↦ ν_k^±` is injective.

### 3.8 `lineMultipliers` and `theorem5` (13.10–13.11)

Let `α₀` be the minimum of the `α₁`'s, and `s₀` the minimum of the `s₁`'s, of 13.4–13.9. Let `0 ≤ α ≤ α₀`. For `i ∈ Fin 2` put `s_i := 0` if `i = 0` and `s_i := s₀` if `i = 1`; put `κ := s₀/2` and `ε := κ/2`.
1. **Construction.** `exists_analytic_norm_eq_exp_of_weak logKernel weylLaplacian (c := 0) … (13.9 with s = s_i ≤ s₁)` gives `h_i` analytic on `ℂ` with:
   - `‖h_i z‖ = exp(v_i z)` when `n_i z = 0`;
   - `analyticOrderAt h_i z = n_i z`.
   
   Put `f i := h_i`. Then `Differentiable ℂ (f i)` (`AnalyticOnNhd.differentiableOn`).
2. **Zeros.** `f i z = 0 ↔ n_i z ≠ 0 ↔ z ∈ lineZeroSet μ α s_i ⊆ ι '' ℝ` (`analyticOrderAt_eq_zero`). So zeros are real, and `f i z₀ ≠ 0` at any non-node `z₀` (e.g. `z₀ = I`).
3. **Upper bound.**
   - Off zeros: `‖f i z‖ = e^{φ − α|Im z| + S} ≤ e^{C} e^{φ − α|Im z|}` (13.6).
   - At zeros: `‖f i z‖ = 0`.
4. **Cover property** (`ε = κ/2`). By 13.4 with `s = s₀`, all nodes of both multipliers are `κ`-separated: `|ν − ν'| ≥ κ(ρ(ν)+ρ(ν'))`.
   - If `z` is not `ε`-far from `Z(f 0)`, pick `λ_k` with `‖z − λ_k‖ < ερ(λ_k)`.
   - For every node `ν' ≠ λ_k`: `‖z − ν'‖ ≥ |λ_k − ν'| − ερ(λ_k) ≥ κρ(ν') + (κ − ε)ρ(λ_k) ≥ ερ(ν')`.
   - Since `λ_k ∉ Z(f 1)` (the nodes `λ_k ± s₀a_k` differ from all `λ_j`), `z` is `ε`-far from `Z(f 1)`.
5. **Lower bound.** Given `η > 0`, put `η' := min(η, 1)`.
   - If `z` is `η`-far from the zeros of `f i`, it is `η'`-far: the hypothesis is monotone in `η`, since `η'ρ ≤ ηρ`. As `ρ > 0`, `z` is then not a zero.
   - By 13.6, `‖f i z‖ ≥ exp(−C(1 + |log η'|)) e^{φ − α|Im z|}`.
   - The hypothesis "for all real `x` with `f i x = 0`" matches "for all `ν ∈ lineZeroSet`", via `ν = ι(ν.re)`.

`theorem5` is `lineMultipliers` at `α = 0`, `i = 0`, with `C := max(C, c⁻¹)`. The Lean proof is in the scratch file and compiles.

---

## 4. Interface

### 4.1 Consumed by later modules
- **M14** uses only `lineMultipliers` (13.10). It needs `α₀ > 0` and the `Fin 2` family with:
  - the global upper bound `‖f i z‖ ≤ C e^{φ − α|Im z|}`;
  - the cover property;
  - the lower bound off the `η`-discs.
- `theorem5` feeds `Solution.lean` / comparator.

### 4.2 Assumed from earlier modules (Lean, typechecked in the scratch file)

**M02** (as already consumed by M07, plus two kernel lemmas that M08 also needs):
```lean
theorem logKernel : LogKernelStmt
theorem weylLaplacian : WeylLaplacianStmt
theorem integrableOn_log_norm_sub_uniform {K K' : Set ℂ} (hK : IsCompact K) (hK' : IsCompact K') :
    ∃ M : ℝ, ∀ a ∈ K', IntegrableOn (fun z ↦ Real.log ‖z - a‖) K ∧
      ∫ z in K, |Real.log ‖z - a‖| ≤ M
theorem integral_logPotential_mul_laplacian (ν : Measure ℂ) [IsFiniteMeasure ν] {L : Set ℂ}
    (hL : IsCompact L) (hνL : ν Lᶜ = 0) (χ : ℂ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) :
    ∫ z, (∫ ζ, Real.log ‖z - ζ‖ ∂ν) * Laplacian.laplacian χ z = 2 * Real.pi * ∫ ζ, χ ζ ∂ν
```
`integral_logPotential_mul_laplacian` is Fubini plus `LogKernelStmt`. Integrability of `(z,ζ) ↦ log|z−ζ| Δχ(z)` follows from `integrableOn_log_norm_sub_uniform` with `K = tsupport χ`, `K' = L`.

**M03, line forms** (Lemma 1, Claim 1, Claim 2, [Chr91, Lemma 2.3], reverse doubling, no atoms):
```lean
theorem IsLineMeasure.doubling_le {μ : Measure ℂ} (hμ : IsLineMeasure μ) (A : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x r : ℝ, 0 < r → r ≤ A →
      μ (lineInterval x (2 * r)) ≤ C * μ (lineInterval x r)                        -- L1
theorem IsLineMeasure.lineInterval_pos {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) {r : ℝ}
    (hr : 0 < r) : 0 < μ (lineInterval x r)                                        -- L2
theorem IsLineMeasure.lineInterval_lt_top {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x r : ℝ) :
    μ (lineInterval x r) < ∞                                                      -- L2
theorem IsLineMeasure.measure_singleton {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) :
    μ {(x : ℂ)} = 0                                                               -- L2
theorem IsLineMeasure.reverse_doubling {μ : Measure ℂ} (hμ : IsLineMeasure μ) {A : ℝ}
    (hA : 0 < A) :
    ∃ q : ℝ≥0, q < 1 ∧ ∀ x r : ℝ, 0 < r → r ≤ A →
      μ (lineInterval x (r / 2)) ≤ q * μ (lineInterval x r)                        -- L3
theorem IsLineMeasure.massRadiusLine_pos {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) :
    0 < massRadiusLine μ x                                                        -- L4
theorem massRadiusLine_le_of_mass {μ : Measure ℂ} {r : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (x : ℝ) : massRadiusLine μ x ≤ r     -- L4
theorem IsLineMeasure.measure_massRadiusLine {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) :
    μ (lineInterval x (massRadiusLine μ x)) = 1                                   -- L4
theorem IsLineMeasure.massRadiusLine_comparable {μ : Measure ℂ} (hμ : IsLineMeasure μ) (K : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x t : ℝ, |x - t| ≤ K * max (massRadiusLine μ x) (massRadiusLine μ t) →
      massRadiusLine μ t ≤ C * massRadiusLine μ x                                 -- L5 (Claim 1)
theorem IsLineMeasure.massRadiusLine_le_rpow {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ γ C : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < C ∧ ∀ x t : ℝ, massRadiusLine μ x ≤ |x - t| → |x - t| ≤ 1 →
      massRadiusLine μ t ≤ C * massRadiusLine μ x ^ γ * |x - t| ^ (1 - γ)        -- L6 (Lemma 1)
theorem IsLineMeasure.length_comparable {μ : Measure ℂ} (hμ : IsLineMeasure μ) {m₁ m₂ : ℝ}
    (hm₁ : 1 ≤ m₁) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : ℝ, a < b →
      ENNReal.ofReal m₁ ≤ μ ((fun t : ℝ ↦ (t : ℂ)) '' Ioc a b) →
      μ ((fun t : ℝ ↦ (t : ℂ)) '' Ioc a b) ≤ ENNReal.ofReal m₂ →
      ∀ t ∈ Icc a b, massRadiusLine μ t ≤ b - a ∧ b - a ≤ C * massRadiusLine μ t  -- L7 (Claim 2)
theorem IsLineMeasure.lintegral_log_le {μ : Measure ℂ} (hμ : IsLineMeasure μ) (A : ℝ) :
    ∃ C : ℝ≥0, ∀ x R : ℝ, 0 < R → R ≤ A →
      ∫⁻ ζ in lineInterval x R, ENNReal.ofReal (Real.log (R / ‖ζ - (x : ℂ)‖)) ∂μ ≤
        C * μ (lineInterval x R)                                                  -- L8 ([Chr91, 2.3])
```
If M03 does not cover the line, these go into `Line/Basic.lean`. Proof sketches:
- **L1** (doubling at scales `≤ A` from scales `< 1/2`). For `r ∈ [1/8, A]`, cover `I(x,2r)` by `⌈16r⌉+1` intervals `I(y,1/8)`. Chain `y → x` in steps `≤ 1/16`, using `μ(I(y,1/8)) ≤ μ(I(y',1/4)) ≤ Cμ(I(y',1/8))` for `|y−y'| ≤ 1/16`. Each piece is `≤ C^{32A+1} μ(I(x,1/8)) ≤ C^{32A+1}μ(I(x,r))`.
- **L2.**
  - If `μ(I(x,r)) = 0`, doubling propagates the zero to all of `ℝ`, contradicting the mass condition.
  - Finiteness: `finite_of_compact`.
  - Atoms: `μ{x} ≤ μ(I(x,2^{−j})) ≤ q^j μ(I(x,1))` by L3.
- **L3.** `I(x,r) \ I(x,r/2) ⊇ I(x + 3r/4, r/4)`, and `μ(I(x+3r/4, r/4)) ≥ C⁻³ μ(I(x+3r/4, 2r)) ≥ C⁻³ μ(I(x, r/2))`. So `q = 1/(1 + C⁻³)`.
- **L4.**
  - `ρ ≤ r`: `r` is in the set.
  - `ρ > 0`: `μ(I(x,δ)) → μ{x} = 0`.
  - `μ(I(x,ρ)) = 1`: `r' ↦ μ(I(x,r'))` is continuous, since spheres `{x±r'}` are null.
- **L5.** Reverse doubling (L3) and doubling (L1), as in [Chr91]/Claim 1.
- **L6.** Let `s := |x−t| ∈ [ρ(x),1]`.
  - `μ(I(t,2s)) ≥ μ(I(x,s)) ≥ (1/q)^{log₂(s/ρ(x))}`.
  - `ρ(t) ≤ 2s`; otherwise `I(x,ρ(x)) ⊆ I(t,2s) ⊊ I(t,ρ(t))` would give a contradiction via `ρ(t)/2 ≤ ρ(x)`.
  - `μ(I(t,2s)) ≤ C^{log₂(2s/ρ(t))+1}`.
  - Compare the two: `γ = log₂(1/q)/log₂ C`.
- **L7.**
  - `I(t, b−a) ⊇ (a,b)` gives `ρ(t) ≤ b−a`.
  - If `b − a ≥ 2^{j+2}ρ(t)`, then `(a,b]` contains a half-length interval adjacent to `t` of mass `≥ C⁻²(1/q)^{j}`. This bounds `j` in terms of `m₂`.
- **L8.** `Σ_j (j+1) log 2 · μ(I(x, 2^{−j}R)) ≤ Σ_j (j+1)log 2 · q^j μ(I(x,R))`.

**M07** (`LogModulus.lean`, compiled): `IsWeakLogModulus`, `exists_analytic_norm_eq_exp_of_weak`.

**Not used:** M05 (its `ℝ` partition is for a positive measure with integer masses; ours is for `σ_α`, with masses `4π`), M06 (quadrature), M08, M09.

---

### 4.3 Interface (reconciled)

Lean files: `Line/Basic.lean`, `Line/Partition.lean`, `Line/Potential.lean`, `Theorem5.lean`.
- **`lineMeasure` → `linePull`.** M13's `lineMeasure` is literally M03's `linePull`, so the Lean files use `linePull`. In the blocks above, `lineMeasure` is replaced by `linePull`; the renamed lemmas are `map_linePull`, `IsLineMeasure.linePull_Ioc_lt_top` and `linePull_Ioc_lineKnot`. `lineMeasure_apply` is M03's `linePull_apply`. In the prose, `μ_ℝ` is `linePull μ`.
- **§4.2, M03 items.** `IsLineMeasure` and L1–L8 are stated in M03 (`Doubling/LineMeasure.lean`), exactly as in §4.2. `IsLineMeasure.of_weight`, `IsLineMeasure.doubling_le` and `massRadiusLine_le_of_mass` are proved there.
- **§4.2, M02 items.**
  - `integrableOn_log_norm_sub_uniform` and `integral_logPotential_mul_laplacian` are in `Potential/Fundamental.lean`.
  - `logKernel : LogKernelStmt` and `weylLaplacian : WeylLaplacianStmt` are in `LogModulusWeak.lean`, proved from M02.
  - The M07 entry point without hypotheses is `exists_analytic_norm_eq_exp_of_isWeakLogModulus`.
- **`theorem5`** is verbatim the comparator statement, proved from `lineMultipliers` as in §1.2.

## 5. Issues found (for the NOTEBOOK)

1. **p. 375, proof of Theorem 5: the literal argument does not give real zeros.** "The same as Theorem 4" means `N = mk` nodes per interval from Lemma 5 (Chebyshev quadrature) and `κ`-shifts by `m`-th roots of unity (Proposition 2).
   - On `ℝ` the quadrature nodes need not be real: M06's nodes are roots of a real polynomial. Equal-weight quadrature with real nodes inside the interval fails in general (Bernstein).
   - The `κ`-shifts `λ + τe^{2πil/m}` are non-real.
   - **Replacement:** moment order `m = 2` suffices on the line. Use barycentres (`N = 2` per cell) and, for the second multiplier, the real pair `λ ± s₀a`. All zeros are real and the exceptional sets are disjoint.
2. **p. 375: Lemma 3 (`mγ > 1`) is not needed on the line.** The far-field sum converges with second-order decay for any `γ > 0` (§3.6(b)): cells grow linearly in number and sublinearly in size.
3. **p. 375, "These two ingredients together prove Theorem 3": Theorem 5 is not the ingredient actually needed.** Theorem 3 needs multipliers for `φ − α|Im z|` (`α > 0`) to absorb the factor `e^{α|Im z|}` of the Ortega-Cerdà–Seip solution (M14 §2.2). `Δ(φ − α|Im z|) = μ − 2α dx` is not a positive measure in general (`μ` may be singular). The paper's model (Theorems 1–2 with the auxiliary weight `ψ = φ − (ε/2)|z|²`) relies on Lemma 6, whose line analogue is not stated. **Fix:** run the construction for the signed measure `μ − 2α dx` with `α ≤ α₀` (this module, 13.10).
4. **p. 375: "it is trivial to split the real line into intervals all of mass N".** True for `μ`, by continuity and strict monotonicity of the distribution function (no atoms, positivity on intervals, both from local doubling). For the signed measure one needs the first-hitting-time construction of §3.3, since `G_α` is not monotone.
5. **2π normalisation** (as in M07): cells must have `σ`-mass `2π ×` (number of zeros); here `4π` for two zeros.
6. **Scales.** Local doubling is assumed only for radii `< 1/2`, but the mass condition holds at an arbitrary `r`, possibly `≫ 1`. Every doubling argument here runs at scales up to `512 r`, which requires the "doubling at bounded scales" lemma (L1). The paper uses this implicitly.

## 6. Formalisation risks
- **The near/far split inside `tsum`.** Represent `K(z)` as a `Finset` (via `e_k → ±∞`), and use `sum_add_tsum_compl`.
- **Signed integrals.** Never form `μ − 2α·Leb` as a `SignedMeasure`. Always carry the pair (`μ_ℝ`-integral, `2α ×` interval integral).
- **`log 0 = 0` junk at nodes.** Every upper bound must exclude nodes (13.5, 13.6 do).
- **13.9 `laplacian_eq`.** This is the longest proof: `integral_tsum` plus two Fubini applications per cell.
- **13.8 continuity of potentials.** Needed for `continuousOn` in `IsWeakLogModulus`; the uniform `ω(η)` argument is routine but fiddly.
