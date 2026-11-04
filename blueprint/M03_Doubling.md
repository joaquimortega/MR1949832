# M03 — §2: locally doubling measures

**Lean files:**
- `OrtegaCerdaMultipliers/Doubling/Abstract.lean`: the whole theory on an abstract metric space `X`: `IsLocDoublingM`, `BallGeometry`, `IsPorous`, `massRadiusM`, scale-up, Lemma 1, Lemma 2, ρ, Claim 1, Lemma 3, [Chr91, Lemma 2.3], growth, decay, bounded count.
- `Doubling/Plane.lean`: `BallGeometry` for finite-dimensional real normed spaces (so `ℂ` and `ℝ`); porous lines and segments in `ℂ`; `IsDoubling → IsLocallyDoubling`.
- `Doubling/Line.lean`: `linePull μ = μ.comap ofReal`, transfer of `IsLocallyDoublingLine` and `massRadiusLine`.
- `Doubling/HypDisc.lean`: the type `HDisc` (𝔻 with `hypDist`), its metric/measurable instances, `BallGeometry HDisc`, `discPull`, Euclidean ⇒ hyperbolic porosity.
- `Doubling/Export.lean`: the `ℂ`-level statements consumed downstream (plane, disc, line) and the finiteness bridge from `IsSubharmonicWeight`.

**Paper:**
- §2, pp. 359–362: definition, Lemma 1, Lemma 2, definition of `ρ`, Claim 1, Lemma 3.
- [Chr91, Lemma 2.3], invoked on p. 368 (radius `< 1`) and p. 372 (radius `2R`, large).
- Growth of `μ(B(z,r))` (used by M11 for `theorem2_printed`).
- Coordinator additions for M08/M13 (moment order 3 in 2D, 2 on `ℝ`): decay of `ρ(ζ)/d(z,ζ)` and the bounded count of disjoint fat sets meeting a ball.

**Depends on:**
- M00 (`Defs.lean`);
- M01: hyperbolic distance and Möbius maps. The exact list is in §4.2 (typechecked as statements).
- Mathlib:
  - metric spaces and measures: `Metric.ball`, `Metric.sphere`, `Metric.infDist`, `continuous_infDist_pt`, `MetricSpace.ofDistTopology`, `MeasurableEmbedding.comap_apply`, `MeasurableEmbedding.subtype_coe`, `Complex.isometry_ofReal` (→ `isClosedEmbedding.measurableEmbedding`), `Set.PairwiseDisjoint.countable_of_isOpen`, `zorn_subset_nonempty` (or `Vitali.exists_disjoint_subfamily_covering_enlargement`);
  - measure continuity and additivity: `measure_biUnion_le`, `measure_biUnion`, `measure_iUnion_null`, `tendsto_measure_iInter_atTop`, `tendsto_measure_iUnion_atTop`, `Monotone.leftLim`, `Monotone.rightLim`, `Monotone.continuousAt_iff_leftLim_eq_rightLim`;
  - integrals: `lintegral_mono`, `setLIntegral_mono'`, `lintegral_iUnion`, `MeasurableEmbedding.lintegral_map`, `Measure.restrict_apply`;
  - real analysis: `Real.logb`, `Real.rpow_logb`, `Real.rpow_natCast`, `Real.artanh`, `Real.tanh`, `tsum_geometric_of_lt_one`, `tsum_coe_mul_geometric_of_norm_lt_one`;
  - compactness: `IsCompact.elim_finite_subcover`, `TotallyBounded`, `ProperSpace` of finite-dimensional spaces.

---

## 0. Design decisions

### 0.1 One abstract theory, three geometries
Every argument of §2 uses only the following:
- balls and the triangle inequality;
- **intermediate points:** for `0 ≤ s ≤ d(x,y)` there is `m` with `d(x,m) ≤ s` and `d(m,y) ≤ d(x,y) − s`;
- **unboundedness;**
- **uniform covering numbers at bounded scales:** a ball of radius `R` is covered by `K(R,ε)` balls of radius `ε`, uniformly in the centre;
- **separability** (only for Lemma 2).

These are the fields of the class `BallGeometry X` (plus `[SeparableSpace X]`). We state the theory once for `[MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]` and instantiate it three times.

| geometry | `X` | measure on `X` | ball ↔ paper's ball |
|---|---|---|---|
| plane | `ℂ` | `μ` | `IsLocallyDoubling μ` is **definitionally** `IsLocDoublingM μ`; `massRadius = massRadiusM` (`rfl`) |
| line | `ℝ` | `linePull μ := μ.comap ofReal` | `linePull μ (ball x r) = μ (lineInterval x r)` |
| disc | `HDisc` | `discPull μ := μ.comap val` | `discPull μ (ball a r) = μ (hypBall a r)` |

**`HDisc`** is `def HDisc : Type := {z : ℂ // z ∈ 𝔻}`. It is a `def`, not an `abbrev`, so instance search does not see the Euclidean subtype metric. Its instances:
- **`MetricSpace`:** `dist a b := hypDist a b`, built with `MetricSpace.ofDistTopology`. The topology is therefore *definitionally* the subspace topology. The proof obligation `H` is the local comparability of hyperbolic and Euclidean balls (M01).
- **`MeasurableSpace`, `BorelSpace`, `SecondCountableTopology`:** by `inferInstanceAs` from the subtype. This typechecks (§2.3), so no diamond arises.

**Why this rather than proving the 𝔻 versions directly.** Done directly, every lemma would be written twice with hand-rolled triangle inequalities for `hypDist`: chains, scale-up, Lemma 1, ρ, Claim 1, Lemma 3, Chr 2.3, growth, decay, counting and porosity. The type synonym costs one metric instance, one `BallGeometry` instance (Möbius invariance) and a few transfer lemmas. Each `ℂ`-level statement of `Export.lean` is then a short transfer:
- `discPull_ball`;
- `MeasurableEmbedding.lintegral_map` for integrals;
- `massRadiusDisc_eq`.

**Alternative considered and rejected:** a bespoke "distance `d` on a subset `Ω ⊆ ℂ`" structure. It would avoid `comap`, but we would have to reprove Mathlib's ball API.

### 0.2 Scales
The definition only gives `μ(B(x,2r)) ≤ C μ(B(x,r))` for `2r < 1`, but the paper uses balls of radius `≥ 1` repeatedly:
- Lemma 1 with `B' ⊂ B`, `r(B) < 1`, needs `B(x', 2r)`;
- p. 367: `M = 2 sup ρ`;
- p. 372: `D(z, 2R)`;
- the mass radius `R` itself.

The **scale-up lemma** (§3.2) gives `μ(B(x,2r)) ≤ C₁(R₁) μ(B(x,r))` for all `r ≤ R₁`. It uses chains along intermediate points plus a covering by `1/4`-balls, so it genuinely uses the geometry (it fails in general metric spaces). All statements take the scale `R₁` as a parameter, and their constants depend on it.

### 0.3 Standing hypotheses and junk values
- **`hfin : ∀ x r, μ (ball x r) < ∞`** is needed. The measure `∞ • vol + ∞ • δ₀` is locally doubling and has an atom. Downstream it comes from `IsSubharmonicWeight` (`…measure_ball_lt_top`, `…measure_hypBall_lt_top`, `…measure_lineInterval_lt_top`).
- **`hm : ∃ R > 0, ∀ x, 1 ≤ μ (ball x R)`** is assumed wherever ρ is used. We take `≤`, weaker than the paper's `>`.
- **`massRadiusM`** is `sInf {r | 0 < r ∧ 1 ≤ μ (ball x r)}`. It is `0` exactly when the set is empty (junk), and every ρ-lemma assumes `hm` or a pointwise `hne`.
  - `massRadiusM_le`, `measure_ball_massRadiusM_le_one` and `lipschitzWith_massRadiusM` need no doubling at all.
- **Lemma 1 (paper form)** compares `toReal`s of measures under the hypotheses `0 < μ B'` and `μ B < ∞`.
- **Chr 2.3:** at `y = x` the integrand is `log (R / 0) = log 0 = 0`, a harmless junk value. The proof therefore does not even need `μ {x} = 0`.
- Measures of balls are `ℝ≥0∞`. Every inequality is multiplicative (`≤ C * μ …`), so no `ENNReal` subtraction appears in the statements. In proofs, use `toReal` only after `hfin`.

### 0.4 Lemma 2 via porosity (the "think carefully" point of the brief)
**The naive argument fails.** Cover a thin neighbourhood of a segment by `n` balls of radius `|I|/n`; each has mass `≲ n^{-γ}` by the *upper* bound. The total is then `n^{1-γ}`, which is useless unless `γ > 1`.

**The paper's argument.** Push μ forward to a transversal interval `J`; then "ν is doubling, hence has no atoms". This is correct in spirit, but ν is not literally doubling: near the ends of the square, the strips over `I(x,2r)` and `I(x,r)` are not comparable with balls.

**The clean version is a porosity lemma (§3.9).** If every point `y` of `E` has, at every small scale `s`, a ball `B(y', κs)` with `d(y,y') ≤ s` missing `E`, then:
- for each scale `s`, the mass of `E` is controlled, via doubling, by `C^k` times the mass of the shell `{κs/2 ≤ dist(·,E) < 2s}`;
- the shells at scales `s₀θⁿ` (`θ = κ/4`) are pairwise disjoint and lie in a bounded set of finite mass;
- so infinitely many disjoint shells each carry mass `≥ C^{-k} μ(E)`, which forces `μ(E) = 0`.

This is exactly the paper's "no atoms for doubling measures" mechanism, made two-dimensional. It covers in one go:
- segments, lines, circles and arcs in `ℂ`;
- in 𝔻, every Euclidean-porous set: horocycles, geodesic arcs, circles centred at `0`, radial segments, hyperbolic circles. This uses `IsPorous.preimage_hDisc`: Euclidean porosity implies hyperbolic porosity.
- spheres `S(x,r)` in any `BallGeometry` space. These are porous with `κ = 1`: move from `y` towards the centre.

---

## 1. The paper (pp. 359–362)

- **Definition.** "`μ(B) ≤ C μ(B')` for all balls `B ⊂ Ω` of radius smaller than 1, where `B` has the same center as `B'` and twice its radius."
- **Lemma 1.** "There is a `γ > 0` such that for any balls `B' ⊂ B` of radius `r(B')` and `r(B) < 1` respectively,
  `(μ(B)/μ(B'))^γ ≲ r(B)/r(B') ≲ (μ(B)/μ(B'))^{1/γ}`."
  *Proof:* "The left inequality is essentially [Chr91, Lemma 2.1] and the right inequality follows directly from the definition." **The attributions are swapped** (see §5).
- **Lemma 2.** "Given any segment `I ⊂ Ω` and any locally doubling measure μ in Ω, then `μ(I) = 0`."
- **Definition of ρ.** "`μ(B(z, ρ(z))) = 1` … well defined since … the measure of any sphere is 0 … `r ↦ μ(B(z,r))` is continuous and strictly increasing."
- **Claim 1.** "If ρ has an upper bound, then for any `K > 0` there is `C_K` with `1/C_K < ρ(z)/ρ(w) < C_K` whenever `d(z,w) ≤ K max{ρ(z), ρ(w)}`."
- **Lemma 3.** "There is an `m ∈ ℕ` such that for any `δ > 0`, `sup_w ∫_{δρ(w) ≤ d(z,w) < 1} (ρ(z)/d(z,w))^m dμ(z) < C_δ`." The proof ends with "provided that we choose `m` so that `mγ > 1`".

---

## 2. Formal statements (all typecheck; proofs `sorry`)

Checked in `scratchpad/m0305_check.lean` with the brief's header (`import OrtegaCerdaMultipliers.Defs`, `namespace OC`). Definitions introduced by M03 (not in `Defs.lean`):
- `IsLocDoublingM`, `massRadiusM`, `BallGeometry`, `IsPorous`;
- `linePull`;
- `HDisc` and its instances, `HDisc.val`, `HDisc.mk`, `discPull`.

### 2.1 `Doubling/Abstract.lean`
```lean
section Abstract

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Local doubling on a metric space at scales `< 1`. -/
def IsLocDoublingM (μ : Measure X) : Prop :=
  ∃ C : ℝ≥0, ∀ x : X, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball x (2 * r)) ≤ C * μ (ball x r)

/-- Mass radius in a metric space: `ρ(x) = inf {r > 0 : μ(B(x,r)) ≥ 1}`. -/
def massRadiusM (μ : Measure X) (x : X) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ 1 ≤ μ (ball x r)}

/-- Geometric hypotheses of §2 (satisfied by `ℂ`, `ℝ`, `HDisc`). -/
class BallGeometry (X : Type*) [MetricSpace X] : Prop where
  exists_between : ∀ (x y : X) (s : ℝ), 0 ≤ s → s ≤ dist x y →
    ∃ m, dist x m ≤ s ∧ dist m y ≤ dist x y - s
  exists_far : ∀ (x : X) (r : ℝ), ∃ y, r ≤ dist x y
  covering : ∀ R ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ x : X, ∃ s : Finset X, s.card ≤ K ∧
    ball x R ⊆ ⋃ y ∈ s, ball y ε

/-- Porosity (uniform, at scales `≤ s₀`, ratio `κ`). -/
def IsPorous (E : Set X) : Prop :=
  ∃ κ s₀ : ℝ, 0 < κ ∧ 0 < s₀ ∧ ∀ y ∈ E, ∀ s : ℝ, 0 < s → s ≤ s₀ →
    ∃ y', dist y y' ≤ s ∧ ∀ e ∈ E, κ * s ≤ dist y' e

theorem exists_dist_eq [BallGeometry X] (x : X) {r : ℝ} (hr : 0 ≤ r) : ∃ y, dist x y = r := sorry

theorem IsLocDoublingM.exists_const_of_le [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r → r ≤ R₁ →
      μ (ball x (2 * r)) ≤ C * μ (ball x r) := sorry

theorem IsLocDoublingM.measure_ball_le_of_dist_le [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ x y : X, ∀ r : ℝ, 0 < r → r ≤ R₁ → dist x y ≤ r →
      μ (ball y r) ≤ C * μ (ball x r) := sorry

theorem IsLocDoublingM.measure_ball_le_pow [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ (x x' : X) (r r' : ℝ) (k : ℕ), 0 < r' → r ≤ R₁ → dist x x' ≤ r →
      r ≤ 2 ^ k * r' → μ (ball x r) ≤ C ^ (k + 1) * μ (ball x' r') := sorry

theorem IsLocDoublingM.reverse_doubling [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ x : X, ∀ t : ℝ, 0 < t → t ≤ R₁ →
      (1 + η) * μ (ball x t) ≤ μ (ball x (2 * t)) := sorry

theorem IsLocDoublingM.measure_ball_le_rpow [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (x x' : X) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist x x' ≤ r → μ (ball x r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (ball x' r') := sorry

theorem IsLocDoublingM.rpow_le_measure_ball [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (x x' : X) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist x x' ≤ r → ENNReal.ofReal (c * (r / r') ^ δ) * μ (ball x' r') ≤ μ (ball x r) := sorry

/-- **Lemma 1** in the paper's form. -/
theorem IsLocDoublingM.lemma1 [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ γ A : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < A ∧
      ∀ (x x' : X) (r r' : ℝ), 0 < r' → r ≤ R₁ → dist x x' + r' ≤ r →
        0 < μ (ball x' r') → μ (ball x r) < ∞ →
        ((μ (ball x r)).toReal / (μ (ball x' r')).toReal) ^ γ ≤ A * (r / r') ∧
        r / r' ≤ A * ((μ (ball x r)).toReal / (μ (ball x' r')).toReal) ^ (1 / γ) := sorry

theorem IsLocDoublingM.measure_singleton {μ : Measure X} (hd : IsLocDoublingM μ)
    [BallGeometry X] (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) (x : X) : μ {x} = 0 := sorry

theorem IsLocDoublingM.measure_ball_pos [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R))
    (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (ball x r) := sorry

theorem IsPorous.mono {E F : Set X} (hF : IsPorous F) (hEF : E ⊆ F) : IsPorous E := sorry

/-- **Lemma 2 (abstract)**: porous sets are null. -/
theorem IsLocDoublingM.measure_eq_zero_of_isPorous [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    {E : Set X} (hE : IsPorous E) : μ E = 0 := sorry

theorem isPorous_sphere [BallGeometry X] (x : X) (r : ℝ) : IsPorous (sphere x r) := sorry

theorem IsLocDoublingM.measure_sphere [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (x : X) (r : ℝ) : μ (sphere x r) = 0 := sorry

theorem IsLocDoublingM.measure_closedBall [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (x : X) (r : ℝ) : μ (closedBall x r) = μ (ball x r) := sorry

theorem IsLocDoublingM.continuous_measure_ball [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) (x : X) :
    Continuous fun r : ℝ ↦ μ (ball x r) := sorry

/-! ### The mass radius -/

theorem massRadiusM_le {μ : Measure X} {x : X} {R : ℝ} (hR : 0 < R) (h : 1 ≤ μ (ball x R)) :
    massRadiusM μ x ≤ R := sorry

theorem massRadiusM_nonneg (μ : Measure X) (x : X) : 0 ≤ massRadiusM μ x := sorry

theorem measure_ball_massRadiusM_le_one (μ : Measure X) (x : X) :
    μ (ball x (massRadiusM μ x)) ≤ 1 := sorry

theorem one_le_measure_ball_of_massRadiusM_lt {μ : Measure X} {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) {r : ℝ} (hr : massRadiusM μ x < r) :
    1 ≤ μ (ball x r) := sorry

theorem measure_ball_lt_one_of_lt_massRadiusM {μ : Measure X} {x : X} {r : ℝ}
    (hr : r < massRadiusM μ x) : μ (ball x r) < 1 := sorry

theorem one_le_measure_closedBall_massRadiusM {μ : Measure X} {x : X}
    (hfin : ∀ r, μ (ball x r) < ∞) (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) :
    1 ≤ μ (closedBall x (massRadiusM μ x)) := sorry

theorem IsLocDoublingM.massRadiusM_pos [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) : 0 < massRadiusM μ x := sorry

theorem IsLocDoublingM.measure_ball_massRadiusM [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) : μ (ball x (massRadiusM μ x)) = 1 := sorry

theorem lipschitzWith_massRadiusM {μ : Measure X} (hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) :
    LipschitzWith 1 (massRadiusM μ) := sorry

/-- `μ(B(x,r)) ≍ (r/ρ(x))^{s or δ}` for `ρ(x) ≤ r ≤ R₁`. -/
theorem IsLocDoublingM.measure_ball_massRadiusM_bounds [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ (x : X) (r : ℝ),
      massRadiusM μ x ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusM μ x) ^ δ) ≤ μ (ball x r) ∧
        μ (ball x r) ≤ ENNReal.ofReal (C * (r / massRadiusM μ x) ^ s) := sorry

/-- **Claim 1**. -/
theorem IsLocDoublingM.claim1 [BallGeometry X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : X,
      dist x y ≤ K * max (massRadiusM μ x) (massRadiusM μ y) →
        massRadiusM μ x ≤ C * massRadiusM μ y := sorry

/-- **Lemma 3**, truncated form (contains the paper's statement on `δρ(w) ≤ d < R₁`). -/
theorem IsLocDoublingM.lemma3 [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w : X,
      ∫⁻ z in ball w R₁,
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ ≤ C :=
  sorry

/-- **Lemma 3** as printed (region `δρ(w) ≤ d(z,w) < R₁`). -/
theorem IsLocDoublingM.lemma3_paper [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w : X,
      ∫⁻ z in {z | δ * massRadiusM μ w ≤ dist z w ∧ dist z w < R₁},
        ENNReal.ofReal ((massRadiusM μ z / dist z w) ^ m) ∂μ ≤ C := sorry

/-- **[Chr91, Lemma 2.3]**. -/
theorem IsLocDoublingM.christ_lemma23 [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ (x : X) (R : ℝ), 0 < R → R ≤ R₁ →
      ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ ≤ C * μ (ball x R) := sorry

theorem IsLocDoublingM.integrableOn_log_dist [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) (x : X) (R : ℝ) :
    IntegrableOn (fun y ↦ Real.log (dist x y)) (ball x R) μ := sorry

/-- **Growth**: balls of a fixed large radius have mass `> p`. No doubling needed. -/
theorem exists_radius_lt_measure_ball [BallGeometry X] {μ : Measure X}
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (p : ℝ≥0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : X, (p : ℝ≥0∞) < μ (ball x r) := sorry

theorem IsLocDoublingM.smul {μ : Measure X} (hd : IsLocDoublingM μ) (c : ℝ≥0∞) :
    IsLocDoublingM (c • μ) := sorry

/-- Mass radius for `N⁻¹ μ` versus `μ` (reduction of mass-`N` pieces to mass-`1` pieces). -/
theorem IsLocDoublingM.massRadiusM_inv_smul [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : X, massRadiusM μ x ≤ massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ∧
      massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ≤ C * massRadiusM μ x := sorry

/-- **Decay of `ρ(ζ)/d(z,ζ)`** (coordinator addition (1)), power form. -/
theorem IsLocDoublingM.massRadiusM_div_dist_le [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α ≤ 1 ∧ ∀ z ζ : X, massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
      massRadiusM μ ζ / dist z ζ ≤ C * (massRadiusM μ z / dist z ζ) ^ α := sorry

/-- **Decay**, geometric form: `d(z,ζ) ≥ 2ⁿ ρ(z)`, `d ≤ M₀` ⟹ `ρ(ζ)/d(z,ζ) ≤ C θⁿ`. -/
theorem IsLocDoublingM.decay [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (z ζ : X) (n : ℕ),
      2 ^ n * massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * θ ^ n := sorry

/-- Disjoint open balls of radius `a` in a `BallGeometry` space have `2a`-separated centres. -/
theorem le_dist_of_disjoint_ball [BallGeometry X] {x y : X} {a : ℝ}
    (h : Disjoint (ball x a) (ball y a)) : 2 * a ≤ dist x y := sorry

/-- **Bounded count** (coordinator addition (2)), abstract form: disjoint sets containing a ball
of radius `a` and contained in a ball of radius `D` around the same centre; at most `M` of them
meet a ball of radius `b`. -/
theorem BallGeometry.encard_le_of_disjoint [BallGeometry X] (a b D : ℝ) (ha : 0 < a) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set X) (c : ι → X) (z : X), Pairwise (Function.onFun Disjoint E) →
      (∀ i, ball (c i) a ⊆ E i) → (∀ i, E i ⊆ ball (c i) D) →
        {i | (E i ∩ ball z b).Nonempty}.encard ≤ M := sorry

end Abstract
```

### 2.2 `Doubling/Plane.lean`, `Doubling/Line.lean`
```lean
/-! ####################################################################
## M03 — `Doubling/Plane.lean` and `Doubling/Line.lean` (geometry instances, transfer)
#################################################################### -/

instance ballGeometry_normed (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] : BallGeometry E := sorry

example : BallGeometry ℂ := inferInstance
example : BallGeometry ℝ := inferInstance

theorem isLocallyDoubling_iff (μ : Measure ℂ) : IsLocallyDoubling μ ↔ IsLocDoublingM μ :=
  Iff.rfl

theorem massRadius_eq (μ : Measure ℂ) : massRadius μ = massRadiusM μ := rfl

theorem IsDoubling.isLocallyDoubling {μ : Measure ℂ} (h : IsDoubling μ) : IsLocallyDoubling μ :=
  sorry

/-- Real affine lines in `ℂ` are porous. -/
theorem isPorous_line (p v : ℂ) : IsPorous {z : ℂ | ∃ t : ℝ, z = p + t * v} := sorry

theorem isPorous_segment (a b : ℂ) : IsPorous (segment ℝ a b) := sorry

/-- The pull-back of `μ` to `ℝ`. -/
def linePull (μ : Measure ℂ) : Measure ℝ := μ.comap fun x : ℝ ↦ (x : ℂ)

theorem linePull_ball (μ : Measure ℂ) (x r : ℝ) : linePull μ (ball x r) = μ (lineInterval x r) :=
  sorry

theorem linePull_apply (μ : Measure ℂ) (s : Set ℝ) :
    linePull μ s = μ ((fun x : ℝ ↦ (x : ℂ)) '' s) := sorry

theorem IsLocallyDoublingLine.isLocDoublingM {μ : Measure ℂ} (h : IsLocallyDoublingLine μ) :
    IsLocDoublingM (linePull μ) := sorry

theorem massRadiusLine_eq (μ : Measure ℂ) (x : ℝ) :
    massRadiusLine μ x = massRadiusM (linePull μ) x := sorry

theorem IsLocallyDoublingLine.measure_image_eq {μ : Measure ℂ} (h : IsLocallyDoublingLine μ)
    (s : Set ℂ) : μ s = μ (s ∩ range fun x : ℝ ↦ (x : ℂ)) := sorry
```

### 2.3 `Doubling/HypDisc.lean`
```lean
/-! ####################################################################
## M03 — `Doubling/HypDisc.lean`: the disc with the hyperbolic metric
#################################################################### -/

/-- The unit disc as a type, to be equipped with the hyperbolic distance `hypDist`. -/
def HDisc : Type := {z : ℂ // z ∈ 𝔻}

namespace HDisc

instance : TopologicalSpace HDisc := inferInstanceAs (TopologicalSpace {z : ℂ // z ∈ 𝔻})

/-- The hyperbolic metric on `HDisc`; its topology is (definitionally) the subspace topology. -/
instance : MetricSpace HDisc :=
  MetricSpace.ofDistTopology (fun a b : HDisc ↦ hypDist a.1 b.1)
    (fun a ↦ hypDist_self a.1) (fun a b ↦ hypDist_comm a.1 b.1)
    (fun a b c ↦ hypDist_triangle a.2 b.2 c.2) isOpen_iff_hypDist
    (fun a b h ↦ Subtype.ext ((hypDist_eq_zero_iff a.2 b.2).1 h))
-- (scaffold) proved; `isOpen_iff_hypDist` is stated and proved just before the instance:
-- theorem isOpen_iff_hypDist (s : Set HDisc) :
--     IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y : HDisc, hypDist x.1 y.1 < ε → y ∈ s

instance : MeasurableSpace HDisc := inferInstanceAs (MeasurableSpace {z : ℂ // z ∈ 𝔻})
instance : BorelSpace HDisc := inferInstanceAs (BorelSpace {z : ℂ // z ∈ 𝔻})
instance : SecondCountableTopology HDisc :=
  inferInstanceAs (SecondCountableTopology {z : ℂ // z ∈ 𝔻})

/-- The point of `ℂ`. -/
def val (z : HDisc) : ℂ := Subtype.val z

/-- A point of `𝔻` as a point of `HDisc`. -/
def mk (z : ℂ) (hz : z ∈ 𝔻) : HDisc := ⟨z, hz⟩

theorem dist_eq (a b : HDisc) : dist a b = hypDist a.val b.val := rfl

theorem val_mem (a : HDisc) : a.val ∈ 𝔻 := a.2

theorem measurableEmbedding_val : MeasurableEmbedding val := sorry

theorem image_ball (a : HDisc) (r : ℝ) : val '' ball a r = hypBall a.val r := sorry

instance : BallGeometry HDisc := sorry

instance : TopologicalSpace.SeparableSpace HDisc := inferInstance

end HDisc

/-- The pull-back of `μ` to `HDisc`. -/
def discPull (μ : Measure ℂ) : Measure HDisc := μ.comap HDisc.val

theorem discPull_apply (μ : Measure ℂ) (s : Set HDisc) : discPull μ s = μ (HDisc.val '' s) :=
  sorry

theorem discPull_ball (μ : Measure ℂ) (a : HDisc) (r : ℝ) :
    discPull μ (ball a r) = μ (hypBall a.val r) := sorry

theorem isLocallyDoublingDisc_iff (μ : Measure ℂ) :
    IsLocallyDoublingDisc μ ↔ IsLocDoublingM (discPull μ) := sorry

theorem massRadiusDisc_eq (μ : Measure ℂ) (a : HDisc) :
    massRadiusDisc μ a.val = massRadiusM (discPull μ) a := sorry

/-- Euclidean porosity implies hyperbolic porosity. -/
theorem IsPorous.preimage_hDisc {E : Set ℂ} (hE : IsPorous E) :
    IsPorous (HDisc.val ⁻¹' E) := sorry
```

### 2.4 `Doubling/Export.lean` (`ℂ`-level statements)
```lean
/-! ####################################################################
## M03 — `Doubling/Export.lean`: the statements in `ℂ`-terms (plane, disc, line)
#################################################################### -/

/-! ### Finiteness from `IsSubharmonicWeight` -/

theorem IsSubharmonicWeight.measure_ball_lt_top {φ : ℂ → ℝ} {μ : Measure ℂ}
    (h : IsSubharmonicWeight univ φ μ) (z : ℂ) (r : ℝ) : μ (ball z r) < ∞ := sorry

theorem IsSubharmonicWeight.measure_hypBall_lt_top {φ : ℂ → ℝ} {μ : Measure ℂ}
    (h : IsSubharmonicWeight 𝔻 φ μ) {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) : μ (hypBall z r) < ∞ := sorry

theorem IsSubharmonicWeight.measure_lineInterval_lt_top {φ : ℂ → ℝ} {μ : Measure ℂ}
    (h : IsSubharmonicWeight univ φ μ) (x r : ℝ) : μ (lineInterval x r) < ∞ := sorry

/-! ### Plane -/

section Plane
variable {μ : Measure ℂ}

theorem lemma1_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ γ A : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < A ∧
      ∀ (z z' : ℂ) (r r' : ℝ), 0 < r' → r ≤ R₁ → dist z z' + r' ≤ r →
        0 < μ (ball z' r') → μ (ball z r) < ∞ →
        ((μ (ball z r)).toReal / (μ (ball z' r')).toReal) ^ γ ≤ A * (r / r') ∧
        r / r' ≤ A * ((μ (ball z r)).toReal / (μ (ball z' r')).toReal) ^ (1 / γ) := sorry

theorem doubling_upTo_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ R₁ →
      μ (ball z (2 * r)) ≤ C * μ (ball z r) := sorry

theorem measure_ball_le_rpow_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (z z' : ℂ) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist z z' ≤ r → μ (ball z r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (ball z' r') := sorry

theorem rpow_le_measure_ball_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (z z' : ℂ) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist z z' ≤ r → ENNReal.ofReal (c * (r / r') ^ δ) * μ (ball z' r') ≤ μ (ball z r) := sorry

theorem measure_ball_le_of_dist_le_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ z w : ℂ, ∀ r : ℝ, 0 < r → r ≤ R₁ → dist z w ≤ r →
      μ (ball w r) ≤ C * μ (ball z r) := sorry

/-- **Lemma 2** (plane): porous sets, in particular lines, segments and circles, are null. -/
theorem measure_eq_zero_of_isPorous_plane (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) {E : Set ℂ} (hE : IsPorous E) : μ E = 0 := sorry

theorem lemma2_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞) (a b : ℂ) :
    μ (segment ℝ a b) = 0 := sorry

theorem measure_sphere_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (z : ℂ) (r : ℝ) : μ (sphere z r) = 0 := sorry

theorem continuous_measure_ball_plane (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (z : ℂ) : Continuous fun r : ℝ ↦ μ (ball z r) := sorry

theorem massRadius_pos (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (z : ℂ) : 0 < massRadius μ z := sorry

theorem massRadius_le {R : ℝ} (hR : 0 < R) (hm : ∀ z, 1 ≤ μ (ball z R)) (z : ℂ) :
    massRadius μ z ≤ R := sorry

theorem measure_ball_massRadius (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (z : ℂ) :
    μ (ball z (massRadius μ z)) = 1 := sorry

theorem lipschitzWith_massRadius (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) :
    LipschitzWith 1 (massRadius μ) := sorry

theorem measure_ball_massRadius_bounds_plane (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ (z : ℂ) (r : ℝ),
      massRadius μ z ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadius μ z) ^ δ) ≤ μ (ball z r) ∧
        μ (ball z r) ≤ ENNReal.ofReal (C * (r / massRadius μ z) ^ s) := sorry

theorem claim1_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z w : ℂ, dist z w ≤ K * max (massRadius μ z) (massRadius μ w) →
      massRadius μ z ≤ C * massRadius μ w := sorry

theorem lemma3_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w : ℂ,
      ∫⁻ z in ball w R₁,
        ENNReal.ofReal ((massRadius μ z / max (dist z w) (δ * massRadius μ w)) ^ m) ∂μ ≤ C :=
  sorry

theorem christ_lemma23_plane (hd : IsLocallyDoubling μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ (z : ℂ) (R : ℝ), 0 < R → R ≤ R₁ →
      ∫⁻ ζ in ball z R, ENNReal.ofReal (Real.log (R / dist z ζ)) ∂μ ≤ C * μ (ball z R) := sorry

theorem exists_radius_lt_measure_ball_plane (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R))
    (p : ℝ≥0) : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, (p : ℝ≥0∞) < μ (ball z r) := sorry

end Plane

/-! ### Disc (hyperbolic balls) -/

section Disc
variable {μ : Measure ℂ}

theorem lemma1_disc (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ γ A : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < A ∧
      ∀ (z z' : ℂ) (r r' : ℝ), z ∈ 𝔻 → z' ∈ 𝔻 → 0 < r' → r ≤ R₁ → hypDist z z' + r' ≤ r →
        0 < μ (hypBall z' r') → μ (hypBall z r) < ∞ →
        ((μ (hypBall z r)).toReal / (μ (hypBall z' r')).toReal) ^ γ ≤ A * (r / r') ∧
        r / r' ≤ A * ((μ (hypBall z r)).toReal / (μ (hypBall z' r')).toReal) ^ (1 / γ) := sorry

theorem doubling_upTo_disc (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → r ≤ R₁ →
      μ (hypBall z (2 * r)) ≤ C * μ (hypBall z r) := sorry

theorem measure_hypBall_le_rpow (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (z z' : ℂ) (r r' : ℝ), z ∈ 𝔻 → z' ∈ 𝔻 → 0 < r' → r' ≤ r →
      r ≤ R₁ → hypDist z z' ≤ r →
        μ (hypBall z r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (hypBall z' r') := sorry

theorem rpow_le_measure_hypBall (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (z z' : ℂ) (r r' : ℝ), z ∈ 𝔻 → z' ∈ 𝔻 → 0 < r' → r' ≤ r →
      r ≤ R₁ → hypDist z z' ≤ r →
        ENNReal.ofReal (c * (r / r') ^ δ) * μ (hypBall z' r') ≤ μ (hypBall z r) := sorry

theorem measure_hypBall_le_of_hypDist_le (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ z ∈ 𝔻, ∀ w ∈ 𝔻, ∀ r : ℝ, 0 < r → r ≤ R₁ → hypDist z w ≤ r →
      μ (hypBall w r) ≤ C * μ (hypBall z r) := sorry

/-- **Lemma 2** (disc): Euclidean-porous sets (segments, lines, circles, horocycles, geodesic
arcs) meet `𝔻` in a null set. -/
theorem measure_inter_disc_eq_zero_of_isPorous (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {E : Set ℂ} (hE : IsPorous E) :
    μ (E ∩ 𝔻) = 0 := sorry

theorem lemma2_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (a b : ℂ) : μ (segment ℝ a b ∩ 𝔻) = 0 := sorry

theorem measure_hypSphere (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    μ {w | w ∈ 𝔻 ∧ hypDist z w = r} = 0 := sorry

theorem continuous_measure_hypBall (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {z : ℂ} (hz : z ∈ 𝔻) :
    Continuous fun r : ℝ ↦ μ (hypBall z r) := sorry

theorem massRadiusDisc_pos (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {z : ℂ} (hz : z ∈ 𝔻) :
    0 < massRadiusDisc μ z := sorry

theorem massRadiusDisc_le {R : ℝ} (hR : 0 < R) (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {z : ℂ}
    (hz : z ∈ 𝔻) : massRadiusDisc μ z ≤ R := sorry

theorem measure_hypBall_massRadiusDisc (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) {z : ℂ} (hz : z ∈ 𝔻) :
    μ (hypBall z (massRadiusDisc μ z)) = 1 := sorry

theorem abs_massRadiusDisc_sub_le (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R))
    {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    |massRadiusDisc μ z - massRadiusDisc μ w| ≤ hypDist z w := sorry

theorem continuousOn_massRadiusDisc (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ContinuousOn (massRadiusDisc μ) 𝔻 := sorry

theorem measure_hypBall_massRadiusDisc_bounds (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ z ∈ 𝔻, ∀ r : ℝ,
      massRadiusDisc μ z ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusDisc μ z) ^ δ) ≤ μ (hypBall z r) ∧
        μ (hypBall z r) ≤ ENNReal.ofReal (C * (r / massRadiusDisc μ z) ^ s) := sorry

theorem claim1_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ 𝔻, ∀ w ∈ 𝔻,
      hypDist z w ≤ K * max (massRadiusDisc μ z) (massRadiusDisc μ w) →
        massRadiusDisc μ z ≤ C * massRadiusDisc μ w := sorry

theorem lemma3_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w ∈ 𝔻,
      ∫⁻ z in hypBall w R₁,
        ENNReal.ofReal
          ((massRadiusDisc μ z / max (hypDist z w) (δ * massRadiusDisc μ w)) ^ m) ∂μ ≤ C :=
  sorry

theorem christ_lemma23_disc (hd : IsLocallyDoublingDisc μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ z ∈ 𝔻, ∀ R : ℝ, 0 < R → R ≤ R₁ →
      ∫⁻ ζ in hypBall z R, ENNReal.ofReal (Real.log (R / hypDist z ζ)) ∂μ ≤
        C * μ (hypBall z R) := sorry

theorem exists_radius_lt_measure_hypBall
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (p : ℝ≥0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, (p : ℝ≥0∞) < μ (hypBall z r) := sorry

end Disc

/-! ### Line (intervals) -/

section Line
variable {μ : Measure ℂ}

theorem doubling_upTo_line (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x r : ℝ, 0 < r → r ≤ R₁ →
      μ (lineInterval x (2 * r)) ≤ C * μ (lineInterval x r) := sorry

theorem measure_lineInterval_le_rpow (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (x x' r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ → |x - x'| ≤ r →
      μ (lineInterval x r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (lineInterval x' r') :=
  sorry

theorem rpow_le_measure_lineInterval (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (x x' r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ → |x - x'| ≤ r →
      ENNReal.ofReal (c * (r / r') ^ δ) * μ (lineInterval x' r') ≤ μ (lineInterval x r) :=
  sorry

theorem measure_singleton_line (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞) (z : ℂ) : μ {z} = 0 := sorry

theorem continuous_measure_lineInterval (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞) (x : ℝ) :
    Continuous fun r : ℝ ↦ μ (lineInterval x r) := sorry

theorem massRadiusLine_pos (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (x : ℝ) :
    0 < massRadiusLine μ x := sorry

theorem massRadiusLine_le {R : ℝ} (hR : 0 < R) (hm : ∀ x : ℝ, 1 ≤ μ (lineInterval x R))
    (x : ℝ) : massRadiusLine μ x ≤ R := sorry

theorem measure_lineInterval_massRadiusLine (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (x : ℝ) :
    μ (lineInterval x (massRadiusLine μ x)) = 1 := sorry

theorem lipschitzWith_massRadiusLine (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) :
    LipschitzWith 1 (massRadiusLine μ) := sorry

theorem measure_lineInterval_massRadiusLine_bounds (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ x r : ℝ,
      massRadiusLine μ x ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusLine μ x) ^ δ) ≤ μ (lineInterval x r) ∧
        μ (lineInterval x r) ≤ ENNReal.ofReal (C * (r / massRadiusLine μ x) ^ s) := sorry

theorem claim1_line (hd : IsLocallyDoublingLine μ) (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, |x - y| ≤ K * max (massRadiusLine μ x) (massRadiusLine μ y) →
      massRadiusLine μ x ≤ C * massRadiusLine μ y := sorry

/-- **Lemma 3** on the line; the integral is over `μ` on `ℂ` (carried by `ℝ`). -/
theorem lemma3_line (hd : IsLocallyDoublingLine μ) (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ x : ℝ,
      ∫⁻ z in lineInterval x R₁,
        ENNReal.ofReal
          ((massRadiusLine μ z.re / max |z.re - x| (δ * massRadiusLine μ x)) ^ m) ∂μ ≤ C :=
  sorry

theorem christ_lemma23_line (hd : IsLocallyDoublingLine μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ x R : ℝ, 0 < R → R ≤ R₁ →
      ∫⁻ z in lineInterval x R, ENNReal.ofReal (Real.log (R / |z.re - x|)) ∂μ ≤
        C * μ (lineInterval x R) := sorry

theorem exists_radius_lt_measure_lineInterval
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (p : ℝ≥0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, (p : ℝ≥0∞) < μ (lineInterval x r) := sorry

end Line


/-! ### Decay and bounded count in `ℂ`-terms (coordinator additions) -/

theorem decay_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (z ζ : ℂ) (n : ℕ),
      2 ^ n * massRadius μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadius μ ζ / dist z ζ ≤ C * θ ^ n := sorry

theorem decay_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (z ζ : ℂ) (n : ℕ), z ∈ 𝔻 → ζ ∈ 𝔻 →
      2 ^ n * massRadiusDisc μ z ≤ hypDist z ζ → hypDist z ζ ≤ M₀ →
        massRadiusDisc μ ζ / hypDist z ζ ≤ C * θ ^ n := sorry

theorem decay_line {μ : Measure ℂ} (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (x y : ℝ) (n : ℕ),
      2 ^ n * massRadiusLine μ x ≤ |x - y| → |x - y| ≤ M₀ →
        massRadiusLine μ y / |x - y| ≤ C * θ ^ n := sorry

/-- Bounded count in `ℂ` for convex sets (no upper size bound needed). -/
theorem encard_le_of_disjoint_convex (a b L : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set ℂ) (c : ι → ℂ) (r : ι → ℝ) (z : ℂ),
      Pairwise (Function.onFun Disjoint E) → (∀ i, Convex ℝ (E i)) → (∀ i, a ≤ r i) →
      (∀ i, ball (c i) (r i) ⊆ E i) → (∀ i, E i ⊆ ball (c i) (L * r i)) →
        {i | (E i ∩ ball z b).Nonempty}.encard ≤ M := sorry

/-- Bounded count in `𝔻` (hyperbolic balls). -/
theorem encard_le_of_disjoint_disc (a b D : ℝ) (ha : 0 < a) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set ℂ) (c : ι → ℂ) (z : ℂ), z ∈ 𝔻 → (∀ i, c i ∈ 𝔻) →
      Pairwise (Function.onFun Disjoint E) → (∀ i, hypBall (c i) a ⊆ E i) →
      (∀ i, E i ⊆ hypBall (c i) D) → {i | (E i ∩ hypBall z b).Nonempty}.encard ≤ M := sorry

/-- Bounded count in `ℂ` (Euclidean balls, bounded size). -/
theorem encard_le_of_disjoint_plane (a b D : ℝ) (ha : 0 < a) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set ℂ) (c : ι → ℂ) (z : ℂ),
      Pairwise (Function.onFun Disjoint E) → (∀ i, ball (c i) a ⊆ E i) →
      (∀ i, E i ⊆ ball (c i) D) → {i | (E i ∩ ball z b).Nonempty}.encard ≤ M := sorry

theorem lineInterval_eq (x r : ℝ) :
    lineInterval x r = ball (x : ℂ) r ∩ range fun t : ℝ ↦ (t : ℂ) := sorry
```

---

## 3. Proofs

Notation: `B(x,r) = ball x r`. `C ≥ 1` is the local doubling constant; replace `C` by `max C 2` at the start, so that `log₂ C ≥ 1`. `C₁(R₁)` is the scale-up constant of §3.2. All constants are explicit functions of `C`, `R₁`, the covering numbers `K(R, ε)`, and (where ρ appears) the mass radius `R`.

### 3.1 `exists_dist_eq`
1. `exists_far x r` gives `y` with `r ≤ d(x,y)`.
2. `exists_between x y r` gives `m` with `d(x,m) ≤ r` and `d(m,y) ≤ d(x,y) − r`.
3. Hence `d(x,m) ≥ d(x,y) − d(m,y) ≥ r`, so `d(x,m) = r`.

### 3.2 Chains and scale-up (`IsLocDoublingM.exists_const_of_le`)
**Chain lemma (internal).** Let `0 < δ`, `2δ < 1`. If `d(x,y) ≤ nδ` then `μ(B(y,δ)) ≤ Cⁿ μ(B(x,δ))`.

*Proof,* by induction on `n`.
- `n = 0`: then `x = y`.
- Step `n + 1`:
  - If `d(x,y) ≤ δ`: `B(y,δ) ⊆ B(x,2δ)`, so `μ(B(y,δ)) ≤ C μ(B(x,δ)) ≤ C^{n+1} μ(B(x,δ))`, since `C ≥ 1`.
  - Otherwise: take `m` from `exists_between x y δ`. Then `d(m,y) ≤ d(x,y) − δ ≤ nδ`. The induction hypothesis at `(m,y)` gives `μ(B(y,δ)) ≤ Cⁿ μ(B(m,δ))`, and `B(m,δ) ⊆ B(x,2δ)` gives `μ(B(m,δ)) ≤ C μ(B(x,δ))`.

**Scale-up.** Given `R₁`:
- If `R₁ < 1/2`, take `C₁ = C`.
- Otherwise let `K := K(2R₁, 1/4)` (the covering field with `R = 2R₁`, `ε = 1/4`) and `n₀ := ⌈8R₁ + 1⌉`. Take `C₁ := max C (K · C^{n₀})`.

*Proof.* Let `0 < r ≤ R₁`.
1. If `2r < 1`, use the definition.
2. Otherwise `r ≥ 1/2`. Cover `B(x,2r) ⊆ B(x,2R₁)` by `B(y,1/4)`, `y ∈ s`, with `#s ≤ K`.
3. Each `y` whose ball meets `B(x,2r)` has `d(x,y) < 2R₁ + 1/4 ≤ n₀/4`.
4. The chain lemma with `δ = 1/4` gives `μ(B(y,1/4)) ≤ C^{n₀} μ(B(x,1/4)) ≤ C^{n₀} μ(B(x,r))`.
5. Sum over `s` (`measure_biUnion_finset_le`).

No finiteness is needed: `ℝ≥0∞` arithmetic suffices.

### 3.3 Neighbouring balls (`measure_ball_le_of_dist_le`)
If `d(x,y) ≤ r ≤ R₁`, then `B(y,r) ⊆ B(x,2r)`, so `μ(B(y,r)) ≤ C₁(R₁) μ(B(x,r))`.

### 3.4 Lemma 1, upper inequality (`measure_ball_le_pow`, `measure_ball_le_rpow`)
**ℕ form**, with `C := C₁(2R₁)`.
1. `d(x,x') ≤ r` gives `B(x,r) ⊆ B(x',2r)`.
2. If `2r ≤ r'`, then `μ(B(x,r)) ≤ μ(B(x',r')) ≤ C^{k+1} μ(B(x',r'))`.
3. Otherwise let `j` be least with `2r ≤ 2^j r'`. Then `1 ≤ j ≤ k+1`, and every base radius `2^i r'` with `i < j` is `< 2r ≤ 2R₁`. So `μ(B(x',2^j r')) ≤ C^j μ(B(x',r'))`.

**rpow form.** Let `s := log₂ C₁(2R₁)` (`≥ 1`) and `k := ⌈log₂(r/r')⌉₊`. Then:
- `r ≤ 2^k r'` and `k ≤ log₂(r/r') + 1`;
- `C₁^{k+1} ≤ C₁^{log₂(r/r') + 2} = C₁² (r/r')^s`.

So the constant is `C₁(2R₁)²` and the exponent is `s = log₂ C₁(2R₁)`. Lean: `Real.rpow_logb`, `Real.rpow_natCast`, `Nat.ceil_lt_add_one`.

### 3.5 Reverse doubling step (`reverse_doubling`)
Let `C₁ := C₁(2R₁)` and `η := C₁^{-3}`. Let `0 < t ≤ R₁`, and pick `y` with `d(x,y) = 3t/2` (§3.1).
- `B(y,t/2) ⊆ B(x,2t) \ B(x,t)`: for `w ∈ B(y,t/2)`, `d(w,x) > 3t/2 − t/2 = t` and `< 3t/2 + t/2 = 2t`.
- `B(x,t) ⊆ B(y,4t)`, since `t + 3t/2 < 4t`. With base radii `t/2, t, 2t ≤ 2R₁`, this gives `μ(B(x,t)) ≤ C₁³ μ(B(y,t/2))`.
- Hence `μ(B(x,2t)) ≥ μ(B(x,t)) + μ(B(y,t/2)) ≥ (1 + C₁^{-3}) μ(B(x,t))`. This uses `measure_union` with disjoint measurable sets and `ENNReal.mul_le_iff_le_inv`. No finiteness is needed.

**Where connectivity and unboundedness enter (brief's question).** The point `y` at distance exactly `3t/2` is where they are used (`exists_far` + `exists_between`).
- Reverse doubling fails without them: for `δ_a + δ_b` on a two-point space, or for a measure on a bounded component, the annulus `B(x,2t) \ B(x,t)` can be empty.
- In `ℂ`, `ℝ` and `(𝔻, hypDist)` such points exist at every scale, so Lemma 1 holds at every bounded scale `R₁`, not only for radii `< 1`.
- For balls of radius `< 1` in `ℂ` or `𝔻` nothing more is needed.

### 3.6 Lemma 1, lower inequality (`rpow_le_measure_ball`)
Let `η` be as in §3.5 for the scale `R₁`, `δ := log₂(1+η)` and `c := 1 / (C₁(R₁)(1+η))`. Let `r' ≤ r ≤ R₁` with `d(x,x') ≤ r`, and `k := ⌊log₂(r/r')⌋₊`, so that `2^k r' ≤ r`.
1. Iterate §3.5 at `x'` with base radii `2^i r' ≤ r/2 ≤ R₁`: `(1+η)^k μ(B(x',r')) ≤ μ(B(x',2^k r'))`.
2. `B(x',2^k r') ⊆ B(x',r) ⊆ B(x,2r)`, so `μ(B(x',2^k r')) ≤ C₁(R₁) μ(B(x,r))`.
3. `(1+η)^k ≥ (1+η)^{log₂(r/r') − 1} = (r/r')^δ/(1+η)`.

Note that `B(x',r') ⊆ B(x,r)` is **not** needed; `d(x,x') ≤ r` suffices.

### 3.7 Lemma 1, paper form (`IsLocDoublingM.lemma1`), explicit γ
Let `C₁ := C₁(2R₁) ≥ 2`, `s := log₂ C₁`, and `δ`, `c` as in §3.6. Take
- `γ := min(1, 1/s, δ)`;
- `A := max(4, c^{-1/δ})`.

Given `d(x,x') + r' ≤ r`:
- `B' := B(x',r') ⊆ B := B(x,r)`, so the ratio `Q := μB/μB' ∈ [1,∞)`;
- the hypotheses make both measures finite and positive;
- `r' ≤ r` and `d(x,x') ≤ r`.

Then:
- **left:** `Q ≤ C₁²(r/r')^s` (§3.4), so `Q^γ ≤ Q^{1/s} ≤ C₁^{2/s}(r/r') = 4(r/r')`;
- **right:** `c(r/r')^δ ≤ Q` (§3.6), so `r/r' ≤ c^{-1/δ} Q^{1/δ} ≤ c^{-1/δ} Q^{1/γ}`.

Both use `Q ≥ 1` and the monotonicity of `Q ↦ Q^p` in `p`.

### 3.8 Positivity of balls, no atoms
- **`measure_ball_pos`.** `1 ≤ μ(B(x,R))`. By §3.4 at scale `R`, `μ(B(x,R)) ≤ C^{k+1} μ(B(x,r))` with `2^k r ≥ R`. So `μ(B(x,r)) ≥ C^{-k-1} > 0`.
- **`measure_singleton`.** `{x} ⊆ B(x,2^{-k})`. By §3.5 at scale 1, `μ(B(x,2^{-k})) ≤ (1+η)^{-k} μ(B(x,1)) → 0`, since `μ(B(x,1)) < ∞` (`ENNReal.Tendsto.mul_const`, `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`).

### 3.9 Lemma 2, abstract (`measure_eq_zero_of_isPorous`)
Let `E` be porous with `(κ, s₀)`. WLOG `E ≠ ∅`; then `κ ≤ 1`, since `κs ≤ d(y',y) ≤ s`. Shrink `s₀` to `≤ 1/20`.

**Reduction to bounded `E`.** Fix `x₀`. Then `E = ⋃ₙ E ∩ B(x₀,n)`; each piece is porous (`IsPorous.mono`) and bounded. Use `measure_iUnion_null`.

So let `E ⊆ B(x₀,R₀)`. Let `k := ⌈log₂(10/κ)⌉₊`.

**One scale `s ∈ (0, s₀]`.**
1. Let `T ⊆ E` be a maximal `4s`-separated subset (`zorn_subset_nonempty` on `{T ⊆ E | T.Pairwise (4s ≤ d)}`). For `y ∈ T` choose `y'` by porosity.
2. **Disjointness.** For `y ≠ z ∈ T`, `d(y',z') ≥ 4s − 2s = 2s ≥ κs`. So the open balls `B(y',κs/2)` are pairwise disjoint. They are nonempty, so `T` is countable (`Set.PairwiseDisjoint.countable_of_isOpen`, `SeparableSpace`).
3. **Covering.** By maximality, `E ⊆ ⋃_{y∈T} B(y,4s)`.
4. **Doubling.** `B(y,4s) ⊆ B(y',5s)`, so `μ(B(y,4s)) ≤ C^k μ(B(y',κs/2))`: the base radii go from `κs/2` up to `< 10s ≤ 1/2`, and `2^k κs/2 ≥ 5s`.
5. **Localisation.** For `ζ ∈ B(y',κs/2)`: `infDist ζ E > κs − κs/2 = κs/2`, and `infDist ζ E ≤ d(ζ,y) < κs/2 + s ≤ 2s`. So `B(y',κs/2) ⊆ Sh(s) := {ζ ∈ B(x₀,R₀+1) | κs/2 ≤ infDist ζ E < 2s}`.
6. **Conclusion.** `μ(E) ≤ ∑_{y∈T} μ(B(y,4s)) ≤ C^k ∑ μ(B(y',κs/2)) = C^k μ(⋃ B(y',κs/2)) ≤ C^k μ(Sh(s))`. This uses `measure_biUnion_le`, then `measure_biUnion` with disjointness and measurability.

**Many scales.** Let `sₙ := s₀ θⁿ` with `θ := κ/4`.
- Then `2s_{n+1} = κsₙ/2`, so the shells `Sh(sₙ)` are pairwise disjoint.
- They are measurable (`continuous_infDist_pt`) and contained in `B(x₀,R₀+1)`.
- So `∑ₙ μ(Sh(sₙ)) ≤ μ(B(x₀,R₀+1)) < ∞` (`measure_iUnion` + `hfin`).
- But each term is `≥ C^{-k} μ(E)`. Hence `μ(E) = 0` (`ENNReal.tsum_const_eq_top_of_ne_zero` gives the contradiction).

`E` need not be measurable: only `measure_mono` is applied to it.

### 3.10 Spheres, closed balls, continuity
- **`isPorous_sphere`:**
  - `r > 0`: take `κ = 1`, `s₀ = r`. For `y ∈ S(x,r)` and `s ≤ r`, `exists_between y x s` gives `y'` with `d(y,y') ≤ s` and `d(y',x) ≤ r − s`. For `e ∈ S`, `d(y',e) ≥ d(x,e) − d(x,y') ≥ s`.
  - `r = 0`: the sphere is `{x}`; take `y'` at distance exactly `s` (§3.1).
  - `r < 0`: the sphere is `∅`.
- **`measure_sphere`:** Lemma 2.
- **`measure_closedBall`:** `closedBall = ball ∪ sphere`.
- **`continuous_measure_ball`.** `f(r) := μ(B(x,r))` is monotone, and continuous at every `r` because:
  - `leftLim f r = μ(⋃_{r'<r} B(x,r')) = μ(B(x,r))` (`tendsto_measure_iUnion_atTop` along `r − 1/n`);
  - `rightLim f r = μ(⋂_{r'>r} B(x,r')) = μ(closedBall x r)`. For `r < 0` the intersection is `∅`, and for `r = 0` it is `{x}`. This uses `tendsto_measure_iInter_atTop` with `hfin`.
  - These agree by `measure_closedBall`; conclude with `Monotone.continuousAt_iff_leftLim_eq_rightLim`.

### 3.11 The mass radius
Let `S_x := {r | 0 < r ∧ 1 ≤ μ(B(x,r))}`. It is upward closed (monotonicity) and bounded below by `0`.
- **`massRadiusM_le`:** `csInf_le`.
- **`massRadiusM_nonneg`:** `Real.sInf_nonneg`.
- **`measure_ball_lt_one_of_lt_massRadiusM`:**
  - if `r ≤ 0`, the ball is empty;
  - else `r ∉ S_x`, since otherwise `ρ ≤ r`.
- **`measure_ball_massRadiusM_le_one`:** if `ρ = 0` the ball is empty. Otherwise `B(x,ρ) = ⋃ₙ B(x, ρ − ρ/(n+2))` is an increasing union of balls of mass `< 1`; use `tendsto_measure_iUnion_atTop` and `le_of_tendsto'`. No hypotheses are needed.
- **`one_le_measure_ball_of_massRadiusM_lt`:** `csInf_lt_iff` gives `r' ∈ S_x` with `r' < r`.
- **`one_le_measure_closedBall_massRadiusM`:** `closedBall x ρ = ⋂ₙ B(x, ρ + 1/(n+1))`. These balls have finite mass `≥ 1`, so `tendsto_measure_iInter_atTop` applies.
- **`massRadiusM_pos`:**
  - `μ(B(x,1/(n+1))) → μ{x} = 0` (§3.8, `hfin`);
  - so some `r₀ > 0` has `μ(B(x,r₀)) < 1`;
  - then every `r ∈ S_x` has `r > r₀`, and `le_csInf` with `hne` gives `ρ ≥ r₀`.
- **`measure_ball_massRadiusM`:** `≤ 1`, `closedBall ≥ 1`, and `closedBall = ball` (§3.10).
- **`lipschitzWith_massRadiusM`** (new; not in the paper). If `r ∈ S_x` then `B(x,r) ⊆ B(y, r + d(x,y))`, so `r + d(x,y) ∈ S_y`. Hence `ρ(y) ≤ ρ(x) + d(x,y)`; symmetrise (`LipschitzWith.of_le_add`).
  - This makes ρ continuous and measurable: `continuousOn_massRadiusDisc` follows from `abs_massRadiusDisc_sub_le` and `continuousOn_hypDist`.
  - It is used repeatedly below in the form `ρ(ζ) ≤ ρ(z) + d(z,ζ)`.
- **`measure_ball_massRadiusM_bounds`:** apply §3.6 and §3.4 with `x = x'` and `r' = ρ(x)`, using `μ(B(x,ρ(x))) = 1`. The constants are `c, δ` of §3.6 and `C₁², s` of §3.4, both at scale `max R₁ R`.
- **`massRadiusM_inv_smul`.**
  - `ρ_μ ≤ ρ_{N⁻¹μ}`: if `1 ≤ N⁻¹ μ(B)` then `1 ≤ N ≤ μ(B)`.
  - Conversely, at `r := ρ_μ(x) (N/c)^{1/δ}` the lower bound gives `μ(B(x,r)) ≥ N`. So `ρ_{N⁻¹μ}(x) ≤ (N/c)^{1/δ} ρ_μ(x)`, at scale `R_N := R (N/c)^{1/δ}`.
  - Also `N⁻¹ μ` satisfies `hm` at radius `r_N` from the growth lemma §3.16.

### 3.12 Claim 1 (`claim1`)
Fix `K ≥ 0` (for `K < 0` the hypothesis is void, since `ρ > 0`). Every radius used is `≤ (K+2)R`; take the constants of §3.4 and §3.6 at this scale.
- **Case `ρ(y) ≥ ρ(x)`,** so `d ≤ Kρ(y)`: by Lipschitz, `ρ(x) ≤ ρ(y) + d ≤ (1+K)ρ(y)`.
- **Case `ρ(x) ≥ ρ(y)`,** so `d(x,y) ≤ Kρ(x)`. If `2ρ(y) ≥ ρ(x)` we are done with constant 2. Otherwise:
  1. `μ(B(y,2ρ(y))) ≥ μ(closedBall y ρ(y)) ≥ 1`.
  2. Lower bound (§3.6) at centre `y`, from `2ρ(y)` to `ρ(x)`: `μ(B(y,ρ(x))) ≥ c(ρ(x)/2ρ(y))^δ`.
  3. `B(y,ρ(x)) ⊆ B(x,(K+1)ρ(x))`, and by the upper bound (§3.4), `μ(B(x,(K+1)ρ(x))) ≤ C₁²(K+1)^s μ(B(x,ρ(x))) ≤ C₁²(K+1)^s`.
  4. Hence `ρ(x) ≤ 2 (C₁²(K+1)^s/c)^{1/δ} ρ(y)`.
- `C_K := max(1+K, 2, 2(C₁²(K+1)^s/c)^{1/δ})`.

Spheres need not be null here: only `ball ≤ 1 ≤ closedBall` is used.

### 3.13 Decay (coordinator addition (1)): `massRadiusM_div_dist_le`, `decay`
Let `ρ(z) ≤ d := d(z,ζ) ≤ M₀`, and take the constants of §3.4 and §3.6 at scale `3M₀` (`≥ 3R` WLOG).
1. `ρ(ζ) ≤ ρ(z) + d ≤ 2d`.
2. Upper bound with `(x,x',r,r') = (z, ζ, 3d, ρ(ζ))`, valid since `d(z,ζ) ≤ 3d`: `μ(B(z,3d)) ≤ C_U (3d/ρ(ζ))^s μ(B(ζ,ρ(ζ))) ≤ C_U(3d/ρ(ζ))^s`.
3. Lower bound with `(z, z, 3d, 2ρ(z))`: `μ(B(z,3d)) ≥ c (3d/2ρ(z))^δ μ(B(z,2ρ(z))) ≥ c(3d/2ρ(z))^δ`, using closed ball `≥ 1`.
4. All quantities are finite (`hfin`), so pass to reals: `ρ(ζ)/d ≤ 3 (C_U/c)^{1/s} (2/3)^{δ/s} (ρ(z)/d)^{δ/s}`.
5. Take `α := min(1, δ/s)` and `C := 3(C_U/c)^{1/s}`. Since `ρ(z)/d ≤ 1`, `(ρ(z)/d)^{δ/s} ≤ (ρ(z)/d)^α`.

**Geometric form.** `θ := 2^{-α}`. If `2ⁿρ(z) ≤ d`, then `(ρ(z)/d)^α ≤ θⁿ`.

This uses both Lemma 1 inequalities, the reverse doubling (inside §3.6), and the Lipschitz half of Claim 1, as the coordinator anticipated. Its main use, by M08/M13, is with `n ≈ log₂(d/ρ(z))`. The sums over rectangles at distance `≈ 2ⁿρ(z)` are counted by area, not by μ-mass.

### 3.14 Lemma 3 (`lemma3`, `lemma3_paper`)
Let `s := log₂ C` (the **local** constant, `C ≥ 2`) and `m₀ := ⌊s⌋₊ + 1`. Fix `m ≥ m₀`, `δ > 0`, `R₁`. Write `ρ = massRadiusM μ`, let `R` be the mass radius of `hm` (so `ρ ≤ R`), and fix the **fine scale** `r₀ := 1/40`.

**(F) Fine part: `F(w, δ) := ∫_{B(w,r₀)} (ρ(z)/max(d(z,w), δρ(w)))^m dμ(z) ≤ C_F(δ)`, uniformly in `w`.**
- **Inner piece `d(z,w) < ρ(w)`.**
  - `ρ(z) ≤ 2ρ(w)` (Lipschitz) and `max ≥ δρ(w)`, so the integrand is `≤ (2/δ)^m`.
  - The mass is `≤ μ(B(w,ρ(w))) ≤ 1`.
- **Annuli `Aₙ := {2ⁿρ(w) ≤ d < 2^{n+1}ρ(w)}` with `t := 2ⁿρ(w) < r₀`.** Then `5t < 1/8`, so §3.4 and §3.6 at scale `1/8` involve only the local constant `C`, since `C₁(1/4) = C`.
  1. On `Aₙ`, `ρ(z) ≤ ρ(w) + d < 3t`, and `d(w,z) ≤ 5t`. The upper bound gives `μ(B(w,5t)) ≤ C_U(5t/ρ(z))^s μ(B(z,ρ(z))) ≤ C_U(5t/ρ(z))^s`.
  2. So `(ρ(z)/max(…))^m ≤ (ρ(z)/t)^m ≤ 5^m C_U^{m/s} μ(B(w,5t))^{-m/s}`.
  3. Hence `∫_{Aₙ} ≤ 5^m C_U^{m/s} μ(B(w,2t)) μ(B(w,5t))^{-m/s} ≤ 5^m C_U^{m/s} μ(B(w,5t))^{1-m/s}`.
  4. Since `m > s`, the exponent is negative. The lower bound §3.6 from radius `2ρ(w)` (where `μ ≥ μ(closedBall) ≥ 1`) gives `μ(B(w,5t)) ≥ c(5·2^{n-1})^δ`.
  5. So `∫_{Aₙ} ≤ C' 2^{-nδ(m/s-1)}`, a geometric series in `n`.

  This is the paper's argument with its exponents sorted out. The upper exponent `s` decides `m`; the reverse-doubling exponent `δ` only gives the rate. In Lean, pass to reals (`ENNReal.toReal`, finite by `hfin`) before taking the power `-m/s`.

**(G) Coarse part: `B(w,R₁) \ B(w,r₀)`** (not in the paper, which stops at `d < 1`).
- The doubling exponent at scale `R₁` is worse, so (F) does not extend. Use a covering instead.
- Here `max(d, δρ(w)) ≥ d ≥ r₀`, so the integrand is `≤ (ρ(z)/r₀)^m`.
- Cover `B(w,R₁)` by `K := K(R₁, r₀)` balls `B(y,r₀)` (`BallGeometry.covering`).
- For `z ∈ B(y,r₀)`, with `δ' := r₀/R`, we have `max(d(z,y), δ'ρ(y)) ≤ r₀`. So `ρ(z)^m ≤ r₀^m (ρ(z)/max(d(z,y), δ'ρ(y)))^m`, and (F) at centre `y` gives `∫_{B(y,r₀)} ρ^m dμ ≤ r₀^m C_F(δ')`.
- Hence the coarse part is `≤ r₀^{-m} · K · r₀^m C_F(δ') = K · C_F(r₀/R)`.

**Assembling.**
- `lemma3` is (F) + (G): `C := C_F(δ) + K(R₁,r₀) C_F(r₀/R)`.
- `lemma3_paper` follows: on `{δρ(w) ≤ d < R₁}` the max equals `d`. Use `setLIntegral_mono_set` and `lintegral_mono`.
- Measurability of the integrand: ρ is Lipschitz, hence continuous; `Measurable.ennreal_ofReal`.

*Alternative via decay (§3.13):* `∫_{Aₙ} ≤ C^m θ^{nm} μ(B(w,2^{n+1}ρ(w)))`. This needs `m > s²/δ`, which is worse. Do not use it.

### 3.15 [Chr91, Lemma 2.3] (`christ_lemma23`, `integrableOn_log_dist`)
Let `η` be as in §3.5 at scale `R₁`, and `q := (1+η)^{-1}`. Write `B(x,R) = {x} ∪ ⋃_{k≥0} Aₖ` with `Aₖ := B(x,2^{-k}R) \ B(x,2^{-k-1}R)`.
- On `Aₖ`, `log(R/d) ≤ (k+1) log 2`.
- At `x` the integrand is `0` (junk).
- By §3.5 iterated, `μ(Aₖ) ≤ μ(B(x,2^{-k}R)) ≤ q^k μ(B(x,R))`.
- Hence `∫ ≤ log 2 · ∑ₖ (k+1)q^k · μ(B(x,R)) = log 2 · (1+η)²/η² · μ(B(x,R))`. Use `lintegral_iUnion` over the disjoint `Aₖ`, `setLIntegral_mono'`, and `tsum_coe_mul_geometric_of_norm_lt_one`.

So `C := log 2 · (1+η)²/η²`. No `hfin` is needed.

**Integrability (with `hfin`).** On `B(x,R)`, `|log d| ≤ log(R/d) + |log R|`. The lintegral is finite and `log ∘ dist x` is measurable; use `integrableOn_iff`/`hasFiniteIntegral_iff_ofReal` (split into positive and negative parts).

### 3.16 Growth (`exists_radius_lt_measure_ball`); no doubling needed
Given `p`, let `k := ⌊p⌋₊ + 1`.
1. Choose `yᵢ` with `d(x,yᵢ) = 2iR` for `i = 1..k` (§3.1).
2. `|d(x,yᵢ) − d(x,yⱼ)| ≥ 2R` gives `d(yᵢ,yⱼ) ≥ 2R`, so the balls `B(yᵢ,R)` are pairwise disjoint and lie inside `B(x,(2k+1)R)`.
3. Hence `μ(B(x,(2k+1)R)) ≥ ∑ μ(B(yᵢ,R)) ≥ k > p`. Take `r := (2k+1)R`.

The brief suggested exponential growth of hyperbolic area. This is not needed: linear growth suffices for `theorem2_printed`.

### 3.17 Bounded count (coordinator addition (2)): `le_dist_of_disjoint_ball`, `BallGeometry.encard_le_of_disjoint`
- **Separation.** If `d(x,y) < 2a`, `exists_between x y (d/2)` gives a common point of `B(x,a)` and `B(y,a)`.
- **Count.** Let `K := K(b + D, a)`.
  1. Every `i` with `Eᵢ ∩ B(z,b) ≠ ∅` has `cᵢ ∈ B(z, b + D)`.
  2. Cover `B(z,b+D)` by `K` balls `B(y,a)`, and send `i` to a ball containing `cᵢ`.
  3. This map is injective: two centres in one `B(y,a)` are `< 2a` apart, but they are `≥ 2a` apart by separation.
  4. So `encard ≤ K` (`Set.encard_le_card` via `Set.InjOn`).

  This is the "area" count with Euclidean or hyperbolic area replaced by covering numbers. It is the same in all three geometries and needs no Möbius normalisation inside the proof: that sits in the instance `BallGeometry HDisc`.
- **`encard_le_of_disjoint_convex` (ℂ, no size bound).** Pick `pᵢ ∈ Eᵢ ∩ B(z,b)` and `tᵢ := min(1, b/(|cᵢ−pᵢ| + rᵢ))`.
  1. By convexity, the homothety of ratio `tᵢ` centred at `pᵢ` maps `B(cᵢ,rᵢ)` onto `B(pᵢ + tᵢ(cᵢ−pᵢ), tᵢrᵢ) ⊆ Eᵢ ∩ B(z,2b)`.
  2. Since `|cᵢ−pᵢ| < Lrᵢ`, the new radius is `≥ a' := min(a, b/(L+1))`.
  3. Apply the bounded version to `E'ᵢ := Eᵢ ∩ B(z,2b)` with `(a', b, D) = (a', b, 4b)`.
- **`encard_le_of_disjoint_disc`/`_plane`:** transfer of the abstract version (via `HDisc.image_ball`; for the plane, verbatim).

### 3.18 Instances and transfers
- **`ballGeometry_normed`** (`E` finite-dimensional, nontrivial):
  - between: `m := x + (s/‖y−x‖)•(y−x)`, or `m := x` if `x = y`;
  - far: `x + (max r 0/‖v‖)•v` for some `v ≠ 0`;
  - covering: `closedBall 0 R` is compact, so `finite_cover_balls_of_compact` gives a finite set `s₀`; translate by `x` (`Finset.image (x + ·)`), with `K := #s₀`.
- **`isPorous_line`.**
  - `v = 0`: the set is `{p}`.
  - `v ≠ 0`: take `y' := y + s·(I·v/‖v‖)`. For `e = p + tv`: `(y' − e)·conj v/‖v‖ = (real) + I·s`, so `‖y' − e‖ ≥ s`, with `κ = 1`.
  - Segments: `segment ℝ a b ⊆ line(a, b − a)`.
- **`linePull`:** `MeasurableEmbedding` of `ofReal` (closed isometric embedding) gives `comap_apply`. Use `Real.ball_eq_Ioo` and `lineInterval = ofReal '' Ioo`.
  - `IsLocallyDoublingLine.isLocDoublingM`: rewrite.
  - `massRadiusLine_eq`: the defining sets agree pointwise.
  - `measure_image_eq`: `μ {im ≠ 0} = 0` and `range ofReal = {im = 0}` (`measure_inter_conull`).
- **`HDisc`.**
  - **Metric axioms:**
    - `dist_self`: `artanh 0 = 0`;
    - `dist_comm`: `pseudoHyp_comm`;
    - `dist_triangle`: `hypDist_triangle` (M01);
    - `eq_of_dist_eq_zero`: `hypDist_eq_zero_iff` (M01).
  - **`H` (topology compatibility):**
    - (⇒) if `U` is open in the subspace and `x ∈ U`, pick a Euclidean `ε`. Then `hypBall x r ⊆ ball x (tanh r (1−|x|²)/(1−tanh r)) ⊆ ball x ε` for small `r` (`hypBall_subset_ball`).
    - (⇐) `ball x (tanh r(1−|x|²)/2) ⊆ hypBall x r` (`ball_subset_hypBall`).
  - **`measurableEmbedding_val`:** `MeasurableEmbedding.subtype_coe measurableSet_ball`.
  - **`image_ball`:** `dist b a = hypDist b a = hypDist a b` (comm), and the points lie in 𝔻.
- **`BallGeometry HDisc`.**
  - **between:**
    1. Let `w := mobius x y`; then `hypDist 0 w = d(x,y)` (`hypDist_mobius`, `mobius_self`… note `mobius x x = 0`).
    2. Take `m₀ := tanh(s)·w/‖w‖` (or `0`). Then `hypDist 0 m₀ = s` and `hypDist m₀ w = d − s` (`hypDist_radial`).
    3. Set `m := mobius x m₀` (an involution, `mobius_zero`).
  - **far:** take `y = t` real with `artanh t ≥ r + hypDist 0 x`; then `d(x,y) ≥ hypDist 0 y − hypDist 0 x`.
  - **covering:**
    1. `hypBall 0 R = ball 0 (tanh R)` has compact closure in 𝔻; cover it by finitely many `hypBall wᵢ ε` (`IsCompact.elim_finite_subcover`, `isOpen_hypBall`). This gives `K`.
    2. For a general centre `x`, `mobius x` maps `hypBall 0 R` onto `hypBall x R` and `hypBall wᵢ ε` onto `hypBall (mobius x wᵢ) ε`.
- **`isLocallyDoublingDisc_iff`, `massRadiusDisc_eq`:** rewrite with `discPull_ball`.
- **`IsPorous.preimage_hDisc`.** Let `(κ, s₀)` be Euclidean porosity data. Then `(κ/16, min 1 s₀)` is hyperbolic porosity data. Given `y ∈ 𝔻 ∩ E` and `s ≤ min 1 s₀`, put `e := s(1−|y|²)/4 ≤ s₀`.
  1. **Choose `y'`.** Euclidean porosity gives `y'` with `|y−y'| ≤ e` and `B_E(y',κe) ∩ E = ∅`.
  2. **`y' ∈ 𝔻`:** `e < 1 − |y|`.
  3. **`hypDist(y,y') ≤ s`:** `tanh s ≥ s/2` on `[0,1]` gives `B_E(y,e) ⊆ ball y (tanh s (1−|y|²)/2) ⊆ hypBall y s`.
  4. **Bound `1 − |y'|²`:** `1 − |y'|² ≤ (1−|y|²) + 2|y−y'| ≤ (3/2)(1−|y|²)`.
  5. **The hyperbolic ball misses `E`:** with `tanh(κs/16) ≤ κs/16 ≤ 1/16`, `hypBall y' (κs/16) ⊆ B_E(y', (κs/16)(16/15)(3/2)(1−|y|²)) = B_E(y', κs(1−|y|²)/10) ⊆ B_E(y', κe)`, which misses `E`.
- **Export lemmas:** transfer with `discPull_ball`, `HDisc.image_ball`, `massRadiusDisc_eq`, and for integrals `MeasurableEmbedding.lintegral_map` (`map val (comap val μ) = μ.restrict 𝔻`).
  - The 𝔻 versions quantify over `z ∈ 𝔻` and apply the abstract lemma at `HDisc.mk z hz`.
  - Lemma 2 in 𝔻: `μ(E ∩ 𝔻) = discPull μ (val ⁻¹' E) = 0`.
- **`IsSubharmonicWeight.*_lt_top`:** use `finite_of_compact` on a compact superset inside Ω:
  - `closedBall z r` for the plane;
  - `closedBall 0 (tanh(artanh‖z‖ + r)) ⊆ 𝔻` for the disc (triangle inequality through `0`, `hypBall_zero`);
  - `closedBall (x:ℂ) r` for the line.
- **`IsDoubling.isLocallyDoubling`:** immediate.

---

## 4. Interface

### 4.1 Exported to later modules
| consumer | uses |
|---|---|
| M02 (potentials) | `christ_lemma23_*`, `IsLocDoublingM.integrableOn_log_dist` (and its plane/disc transfers), `measure_singleton*`, `IsSubharmonicWeight.*_lt_top` |
| M04 (Lemma 6) | `doubling_upTo_*`, `measure_ball_le_of_dist_le_plane`, `measure_hypBall_le_of_hypDist_le` (masses of neighbouring squares), `christ_lemma23_*` at radius `2R` (bounded-scale version), `exists_radius_lt_measure_*`, `IsLocDoublingM.smul` |
| M05 (partition) | everything on ρ; Lemma 2 (`measure_eq_zero_of_isPorous_plane`, `measure_inter_disc_eq_zero_of_isPorous`, `isPorous_line`, `isPorous_sphere`, `IsPorous.mono`); `continuous_measure_*`; Lemma 1 (`*_le_rpow`, `rpow_le_*`); `doubling_upTo_*`; `claim1_*`; `massRadiusM_inv_smul`; growth; `BallGeometry.encard_le_of_disjoint` |
| M08 (Theorem 4) | `massRadius*_pos/_le`, `measure_*_massRadius*` (= 1), `lipschitzWith_massRadius*`, `claim1_*`, `lemma3_*` (paper form *and* max form), `decay_*`, `encard_le_of_disjoint_*`, `christ_lemma23_*`, `measure_*_massRadius*_bounds` |
| M09 (Prop. 2) | `encard_le_of_disjoint_*` / M05's neighbour counts |
| M11 (Theorem 2) | `exists_radius_lt_measure_hypBall` (`theorem2_printed`: apply `theorem2` to `φ/p`, `μ/p`; the mass condition for `μ/p` is `p < μ(D(z,r))`), `IsSubharmonicWeight.measure_hypBall_lt_top` |
| M12 (Theorem 1) | `IsDoubling.isLocallyDoubling`, plane lemmas |
| M13 (Theorem 5) | line lemmas: `lemma3_line` (stated with `max |z.re − x| (δρ(x))`; for `z ∈ ℂ` off the line, `|z − ζ| ≥ |Re z − ζ|`), `christ_lemma23_line`, `decay_line`, `lineInterval_eq`, `IsLocallyDoublingLine.measure_image_eq`, `measure_singleton_line` |

**Coordinator note (moment order).** M08/M13 plan to use `m = 3` (2D) and `m = 2` (`ℝ`). The ingredients are:
- **decay:** `decay_plane/disc/line`, or the power form `massRadiusM_div_dist_le` (`ρ(ζ)/d ≤ C(ρ(z)/d)^α`);
- **bounded count:** `encard_le_of_disjoint_plane/disc/convex` and the abstract `BallGeometry.encard_le_of_disjoint`. The fatness hypothesis is "contains `B(cᵢ, a)` and is contained in `B(cᵢ, D)`". M05 provides exactly this for its pieces (field `inner` and `dist_le` of `IsMassPartition`, with radii `≍ ρ`).

The paper's Lemma 3 is still formalised as printed (`lemma3_paper`), with `m₀ = ⌊log₂ C⌋ + 1`.

### 4.2 Assumed from M01 (statements typechecked in `scratchpad/m0305_m01assumed.lean`)
`mobius a z = (a − z)/(1 − ā z)` and its lemmas come from BOC M15 (copied by M01). The `hypDist` lemmas are the "new: `β = artanh ρ` (metric, balls, invariance)" items of M01. If M01's names differ, adapt the names only.
```lean
def mobius (a z : ℂ) : ℂ := (a - z) / (1 - conj a * z)
theorem mobius_mobius {a z : ℂ} (ha : a ∈ 𝔻) (hz : z ∈ 𝔻) : mobius a (mobius a z) = z := sorry
theorem mobius_zero (a : ℂ) : mobius a 0 = a := sorry
theorem mobius_mem_disc {a z : ℂ} (ha : a ∈ 𝔻) (hz : z ∈ 𝔻) : mobius a z ∈ 𝔻 := sorry
theorem hypDist_comm (z w : ℂ) : hypDist z w = hypDist w z := sorry
theorem hypDist_self (z : ℂ) : hypDist z z = 0 := sorry
theorem hypDist_nonneg (z w : ℂ) : 0 ≤ hypDist z w  -- (reconciled) M01 form, no hypotheses
theorem hypDist_eq_zero_iff {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) : hypDist z w = 0 ↔ z = w := sorry
theorem hypDist_triangle {u v w : ℂ} (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) (hw : w ∈ 𝔻) :
    hypDist u w ≤ hypDist u v + hypDist v w := sorry
theorem hypDist_mobius {a u v : ℂ} (ha : a ∈ 𝔻) (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) :
    hypDist (mobius a u) (mobius a v) = hypDist u v := sorry
theorem hypDist_zero_left (z : ℂ) : hypDist 0 z = Real.artanh ‖z‖ := sorry
theorem hypDist_radial {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {u : ℂ} (hu : ‖u‖ = 1) :
    hypDist (s * u) (t * u) = Real.artanh t - Real.artanh s := sorry
-- (reconciled) M01 name `ball_subset_hypBall_tanh` (`ball_subset_hypBall` is the `r ≤ 1` form)
theorem ball_subset_hypBall_tanh {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 < r) :
    ball z (Real.tanh r * (1 - ‖z‖ ^ 2) / 2) ⊆ hypBall z r := sorry
-- (reconciled) M01 name `hypBall_subset_ball_tanh` (`hypBall_subset_ball` is the `r ≤ 1` form)
theorem hypBall_subset_ball_tanh {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    hypBall z r ⊆ ball z (Real.tanh r * (1 - ‖z‖ ^ 2) / (1 - Real.tanh r)) := sorry
theorem hypBall_zero (r : ℝ) : hypBall 0 r = ball 0 (Real.tanh r) := sorry
theorem isOpen_hypBall (z : ℂ) (r : ℝ) : IsOpen (hypBall z r)  -- (reconciled) M01 form
theorem continuousOn_hypDist : ContinuousOn (fun p : ℂ × ℂ ↦ hypDist p.1 p.2) (𝔻 ×ˢ 𝔻) := sorry
end OC
```

---

### 4.3 Interface (reconciled)

Lean files: `Doubling/Abstract.lean`, `Plane.lean`, `Line.lean`, `HypDisc.lean`, `Export.lean` as in §2, plus two new files:
- `Doubling/Quant.lean`: the uniform forms (README §3a.6, M08 §4.1);
- `Doubling/LineMeasure.lean`: the line forms that M13 §4.2 needs.

**Definitions moved here from M08.** The explicit-constant predicates, the classes and `lapNorm` are written in M08 §2.1. They are defined in `Quant.lean` because the uniform M03 and M05 lemmas are stated with them. Line and abstract analogues are added:

```lean
/-- Local doubling with an explicit constant (plane). -/
def IsLocallyDoublingWith (μ : Measure ℂ) (Cd : ℝ≥0) : Prop :=
  ∀ z : ℂ, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball z (2 * r)) ≤ Cd * μ (ball z r)
/-- Local doubling with an explicit constant (disc, hyperbolic balls). -/
def IsLocallyDoublingDiscWith (μ : Measure ℂ) (Cd : ℝ≥0) : Prop :=
  ∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (hypBall z (2 * r)) ≤ Cd * μ (hypBall z r)
/-- Local doubling with an explicit constant (line; `μ` carried by `ℝ`). -/
def IsLocallyDoublingLineWith (μ : Measure ℂ) (Cd : ℝ≥0) : Prop :=
  μ {z : ℂ | z.im ≠ 0} = 0 ∧ ∀ x : ℝ, ∀ r : ℝ, 0 < r → 2 * r < 1 →
    μ (lineInterval x (2 * r)) ≤ Cd * μ (lineInterval x r)
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
/-- The class of measures with parameters `(Cd, R₀)` (line). -/
structure MeasClassLine (ν : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocallyDoublingLineWith ν Cd
  mass : ∀ x : ℝ, 1 < ν (lineInterval x R₀)
  finite : ∀ K : Set ℂ, IsCompact K → ν K < ∞
/-- `Δψ/(2π)`.  With this normalisation a zero of `h` contributes exactly one unit of mass:
`Δ log|h| = 2π Σ δ_λ` and `Δψ = 2π · lapNorm μ`. -/
def lapNorm (μ : Measure ℂ) : Measure ℂ := (ENNReal.ofReal (2 * Real.pi))⁻¹ • μ
/-- Local doubling on a metric space with an explicit constant. -/
def IsLocDoublingMWith (μ : Measure X) (Cd : ℝ≥0) : Prop :=
  ∀ x : X, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball x (2 * r)) ≤ Cd * μ (ball x r)
/-- The abstract class with parameters `(Cd, R₀)`: explicit doubling constant, every ball of
radius `R₀` has mass `≥ 1`, balls have finite mass. -/
structure MeasClassM (μ : Measure X) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocDoublingMWith μ Cd
  mass : ∀ x : X, 1 ≤ μ (ball x R₀)
  finite : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞
```

**Uniform lemmas.** In every lemma the constants are chosen after `(Cd, R₀)` and the displayed auxiliary parameters, and before the measure.
- **M08 §4.1 forms**, exactly as requested:

```lean
/-- (M03, growth + scaling) `lapNorm` stays in a class; `ρ` and `ρ̃` are comparable. -/
theorem MeasClassPlane.lapNorm {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} (h : MeasClassPlane μ Cd R₀) :
    MeasClassPlane (lapNorm μ) Cd (15 * R₀)
theorem MeasClassDisc.lapNorm {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} (h : MeasClassDisc μ Cd R₀) :
    MeasClassDisc (lapNorm μ) Cd (15 * R₀)
theorem massRadius_lapNorm_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure ℂ, MeasClassPlane μ Cd R₀ → ∀ z,
      massRadius μ z ≤ massRadius (lapNorm μ) z ∧ massRadius (lapNorm μ) z ≤ C * massRadius μ z
theorem massRadiusDisc_lapNorm_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure ℂ, MeasClassDisc μ Cd R₀ → ∀ z ∈ 𝔻,
      massRadiusDisc μ z ≤ massRadiusDisc (lapNorm μ) z ∧
        massRadiusDisc (lapNorm μ) z ≤ C * massRadiusDisc μ z
/-- (M03, quantitative Claim 1 + positivity/upper bound of `ρ`). -/
theorem claim1_plane_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z w : ℂ,
      0 < massRadius ν z ∧ massRadius ν z ≤ R₀ ∧
      (dist z w ≤ K * max (massRadius ν z) (massRadius ν w) →
        massRadius ν z ≤ C * massRadius ν w)
theorem claim1_disc_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ w ∈ 𝔻,
      0 < massRadiusDisc ν z ∧ massRadiusDisc ν z ≤ R₀ ∧
      (hypDist z w ≤ K * max (massRadiusDisc ν z) (massRadiusDisc ν w) →
        massRadiusDisc ν z ≤ C * massRadiusDisc ν w)
/-- (M03, quantitative) mass of comparable balls. -/
theorem measure_ball_massRadius_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z, ν (ball z (K * massRadius ν z)) ≤ C
theorem measure_hypBall_massRadius_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻,
      ν (hypBall z (K * massRadiusDisc ν z)) ≤ C
/-- (M03, quantitative decay; `massRadiusM_div_dist_le` with `M₀ = 1/4`). -/
theorem decay_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z ζ : ℂ,
      massRadius ν z ≤ dist z ζ → dist z ζ ≤ 1 / 4 →
        massRadius ν ζ / dist z ζ ≤ C * (massRadius ν z / dist z ζ) ^ α
theorem decay_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻,
      massRadiusDisc ν z ≤ hypDist z ζ → hypDist z ζ ≤ 1 / 4 →
        massRadiusDisc ν ζ / hypDist z ζ ≤ C * (massRadiusDisc ν z / hypDist z ζ) ^ α
/-- (M03, quantitative [Chr91, Lemma 2.3]). -/
theorem christ_plane_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z : ℂ, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ ζ in ball z s, ENNReal.ofReal (Real.log (s / dist z ζ)) ∂ν ≤ C * ν (ball z s)
theorem christ_disc_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ ζ in hypBall z s, ENNReal.ofReal (Real.log (s / hypDist z ζ)) ∂ν ≤
        C * ν (hypBall z s)
```
- **Abstract forms** (on `X` with `BallGeometry`, for `MeasClassM μ Cd R₀`): `doubling_upTo_quant`, `measure_ball_le_rpow_quant`, `rpow_le_measure_ball_quant`, `lemma1_quant`, `measure_ball_massRadiusM_bounds_quant`, `measure_ball_massRadiusM_quant`, `claim1_quant`, `massRadiusM_div_dist_le_quant`, `decay_quant`, `lemma3_quant`, `christ_lemma23_quant`, `massRadiusM_inv_smul_quant`. Some examples:

```lean
theorem doubling_upTo_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ μ : Measure X, IsLocDoublingMWith μ Cd → ∀ x : X, ∀ r : ℝ, 0 < r →
      r ≤ R₁ → μ (ball x (2 * r)) ≤ C * μ (ball x r)
/-- **Claim 1**, uniform form, with `0 < ρ ≤ R₀`. -/
theorem claim1_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ K : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ x y : X,
      0 < massRadiusM μ x ∧ massRadiusM μ x ≤ R₀ ∧
      (dist x y ≤ K * max (massRadiusM μ x) (massRadiusM μ y) →
        massRadiusM μ x ≤ C * massRadiusM μ y)
/-- **Decay**, geometric form, uniform. -/
theorem decay_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ →
      ∀ (z ζ : X) (n : ℕ), 2 ^ n * massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * θ ^ n
/-- **[Chr91, Lemma 2.3]**, uniform form. -/
theorem christ_lemma23_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ μ : Measure X, IsLocDoublingMWith μ Cd → ∀ (x : X) (R : ℝ), 0 < R → R ≤ R₁ →
      ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ ≤ C * μ (ball x R)
```
- **Transfers:** `MeasClassPlane.measClassM` (proved), `MeasClassDisc.measClassM_discPull`, `MeasClassLine.measClassM_linePull`, `MeasClassPlane.of_weight`, `MeasClassDisc.of_weight` (proved).
- **Line forms:** `claim1_line_quant`, `decay_line_quant`, `christ_line_quant`.

**Additions to `Export.lean`** (requested by M04 and M11; `logSmall_*` moved from M04, so that M08 does not depend on M04):

```lean
/-- No atoms, plane (M04's (A4)). -/
theorem measure_singleton_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (z : ℂ) : μ {z} = 0
/-- No atoms, disc (M04's (A4')). -/
theorem measure_singleton_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) {z : ℂ} (hz : z ∈ 𝔻) : μ {z} = 0
/-- **Growth of hyperbolic balls, explicit radius**: if every hyperbolic ball of radius `r` has
mass `≥ m₀ > 0`, then every ball of radius `(2k + 1) r`, `k = ⌈M/m₀⌉₊`, has mass `> M`: it
contains `k + 1` disjoint balls of radius `r` centred on a geodesic through its centre.  No
doubling needed; the radius depends only on `r`, `m₀` and the target mass `M`, not on `μ`. -/
theorem ofReal_lt_measure_hypBall {μ : Measure ℂ} {r m₀ : ℝ} (hr : 0 < r) (hm₀ : 0 < m₀)
    (h : ∀ z ∈ 𝔻, ENNReal.ofReal m₀ ≤ μ (hypBall z r)) (M : ℝ) {z : ℂ} (hz : z ∈ 𝔻) :
    ENNReal.ofReal M < μ (hypBall z ((2 * ⌈M / m₀⌉₊ + 1) * r))
/-- **Growth of hyperbolic balls** (M11 §2.1): a uniform positive lower bound on the balls of one
radius gives arbitrarily large mass on the balls of a larger radius.  No doubling needed. -/
theorem exists_hypBall_measure_gt {μ : Measure ℂ} {r m₀ : ℝ} (hr : 0 < r) (hm₀ : 0 < m₀)
    (h : ∀ z ∈ 𝔻, ENNReal.ofReal m₀ ≤ μ (hypBall z r)) (M : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, ENNReal.ofReal M < μ (hypBall z R)
/-- Uniform smallness of the logarithmic integral near a compact set (plane).  Moved here from
M04 (`Regularization.lean`), so that M08 can use it without depending on M04. -/
theorem logSmall_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ K : Set ℂ, IsCompact K → μ K < ∞) {K : Set ℂ} (hK : IsCompact K) {η : ℝ}
    (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
      ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂μ ≤ ENNReal.ofReal η
/-- Uniform smallness of the logarithmic integral near a compact subset of `𝔻` (disc).  Moved
here from M04. -/
theorem logSmall_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ K ⊆ 𝔻, IsCompact K → μ K < ∞) {K : Set ℂ} (hK𝔻 : K ⊆ 𝔻) (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
      ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂μ ≤ ENNReal.ofReal η
```

**For M13** (`LineMeasure.lean`): the structure `IsLineMeasure`, `IsLineMeasure.of_weight` (proved) and L1–L8 exactly as in M13 §4.2. `IsLineMeasure.doubling_le` and `massRadiusLine_le_of_mass` are proved from `doubling_upTo_line` and `massRadiusLine_le`.

**`HDisc`.** The metric-space instance is fully proved (§2.3 block). It carries real data and no `sorry`.

**Used under M03 names by later modules:**
- M04's (A1)–(A4) become `doubling_upTo_*`, `christ_lemma23_*`, `rpow_le_measure_*`, `measure_singleton_plane/disc`;
- M11's `exists_hypBall_measure_gt` is stated above;
- M12's `IsDoubling.isLocallyDoubling` is M03's.

## 5. Issues found (for the NOTEBOOK)

1. **p. 360, proof of Lemma 1: the attributions are swapped.**
   - The left inequality `(μB/μB')^γ ≲ r(B)/r(B')`, an *upper* bound for the mass ratio, follows from the definition by iteration (§3.4).
   - The right inequality `r/r' ≲ (μB/μB')^{1/γ}` is reverse doubling, i.e. [Chr91, Lemma 2.1] (§3.5–3.6).
   - Lemma 3's proof (p. 362) uses them in this corrected sense.
2. **p. 360, Lemma 1 at radius `< 1`.** `B' ⊂ B` with `r(B) < 1` requires comparing with `B(x',2r)`, of radius up to 2. Local doubling (scale 1) must first be **scaled up** (chain + covering, §3.2). This uses the geometry (geodesic, uniformly locally compact); it is not automatic for a general metric space. The same scale-up is needed for every use at radius `≥ 1`: p. 367 (`M = 2 sup ρ`), p. 372 (`D(z,2R)`).
3. **p. 360, proof of Lemma 2.** The projected measure ν on `J` is not literally doubling (end effects of the square).
   - Correct argument: porosity + reverse doubling on disjoint shells (§3.9).
   - The paper also needs more than segments. Continuity of `r ↦ μ(B(z,r))` (p. 361) needs spheres, i.e. hyperbolic circles in 𝔻. The partition (M05) needs lines in `ℂ`, and horocycles/geodesic arcs (or circles and radii for polar rectangles) in 𝔻. All are covered by "porous ⇒ null".
   - The naive covering argument fails (`n·n^{-γ}`).
4. **p. 361, "continuous and strictly increasing".**
   - Strict increase needs positive mass on every ball: true under the mass condition (`measure_ball_pos`), false for general locally doubling measures (`μ = 0`).
   - `ρ(z) > 0` needs local finiteness (`∞·δ₀`-type counterexamples).
5. **New: ρ is 1-Lipschitz** (`lipschitzWith_massRadiusM`). This gives continuity and measurability of ρ for free and the easy half of Claim 1. It also simplifies Lemma 3: "`C d(z,w) ≥ ρ(z) + d(z,w)`" holds with `C = 3`, since `ρ(z) ≤ ρ(w) + d ≤ 2d`.
6. **p. 361, Lemma 3 is stated for `d(z,w) < 1` but used on p. 367 up to `M = 2 sup ρ`,** which may exceed 1.
   - The coarse range needs a separate (covering) argument: the doubling exponent at large scales is worse, and the paper's estimate does not extend verbatim (§3.14).
   - The exponent bookkeeping `(mγ−1)/γ` mixes the two exponents of Lemma 1. Correctly, `m > log₂ C` (local doubling exponent) decides convergence, and the reverse-doubling exponent only gives the rate.
7. **p. 368 / p. 372: [Chr91, Lemma 2.3]** is used at radius `2R` (large) on p. 372. It needs the bounded-scale version (`christ_lemma23` with `R ≤ R₁`).
8. **Growth for `theorem2_printed`** follows from the mass condition alone (disjoint balls along a geodesic). No doubling or exponential area growth is needed.
