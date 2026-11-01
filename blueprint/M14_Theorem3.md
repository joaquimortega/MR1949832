# M14 — Theorem 3 (degenerate weights), from Theorem 5 and the Ortega-Cerdà–Seip theorem

**Paper.**
- Statement: p. 358.
- The cited theorem [OCS99] is quoted on p. 375.
- The proof is one sentence on p. 375: "These two ingredients together prove Theorem 3 in the same way as we proved Theorem 1 and Theorem 2". It is reconstructed below.

**Lean files:** `OrtegaCerdaMultipliers/Theorem3.lean`; `OrtegaCerdaMultipliers/TheoremOCSProof.lean` (added 2026-11-02).

**Status (2026-11-02):** proved, no `sorry`. `theorem3_weighted` and `theorem3_of_lowerBound` are unconditional: `TheoremOCS` is proved in MR1682065 (`OCS.theoremOCS`, vendored in `OrtegaCerdaSeip/`), and `TheoremOCSProof.lean` gives `theoremOCS_holds`. The statements of §1.3 with the hypothesis `hOCS` are kept as `theorem3_weighted_of_theoremOCS` and `theorem3_of_lowerBound_of_theoremOCS`. The printed `theorem3` is false (`theorem3_printed_false`); now that `TheoremOCS` is proved, the equivalence `theorem3 ↔ ¬ TheoremOCS` of §0.1 just says so.

**Depends on:**
- **M13**: `lineMultipliers` (two multipliers for `φ − α|Im z|`, disjoint exceptional sets);
- **M01**: `dbar_mul`, `dbar_eq_zero_of_differentiableAt` (`Foundations/Wirtinger.lean`);
- **Defs**: `TheoremOCS`, `IsWeakDbarSolMeasure`;
- **Mathlib:**
  - `withDensity_apply`, `lintegral_withDensity_eq_lintegral_mul₀`, `integral_withDensity_eq_integral_toReal_smul₀`, `Measure.restrict_restrict`;
  - `integral_finset_biUnion` (or `integral_union` twice), `LocallyIntegrable.integrable_smul_right_of_hasCompactSupport` (or M01's `integrable_mul_of_locallyIntegrableOn`);
  - `Differentiable.contDiff`, `ContDiff.restrict_scalars`, `HasCompactSupport.mul_left`;
  - `squeeze_zero'`, `Filter.Tendsto.add`, `IsCompact.exists_bound_of_continuousOn`.

Scratch file (all statements typecheck, proofs `sorry`):
`/tmp/claude-1000/-home-quim-cloud-papers-Lean-1995ReineAngewMath/c37e0653-2eb9-4b15-945d-8755a676cb36/scratchpad/m1314_check.lean`.

---

## 0. Verdict on the fixed statements (read first)

### 0.1 `theorem3` (comparator) is **false**: it is equivalent to `¬ TheoremOCS`

The printed Theorem 3, and `theorem3` which transcribes it faithfully, bound `|u(x)| e^{−φ(x)}` by `C(1 + ∫_{|z−x|<1} d|μ|(z)/|x−z|)`, with **no weight inside the integral**. This RHS is not invariant under `φ ↦ φ + h`, `h` harmonic, whereas the problem is: with `Re H = h`, `u ↦ u e^{H}` is a bijection of solutions preserving the hypotheses and the left side.

The correct (and provable) form has `e^{−φ(z)} d|μ|(z)` in the integral. The two forms agree when `φ` is bounded below on `{|Im z| < 1}` (e.g. `φ = α|Im z|`), but not in general.

**Counterexample** (§4): `φ₀(z) = |Im z| + Re z · Im z`, `μ₀ = Δφ₀ = 2·dx` on `ℝ`, `K = 2`. It satisfies every hypothesis, and for every `C` there is admissible data (a segment measure near `x₀ = 1/δ`) for which no `u` satisfies the conclusions. The proof uses only Weyl's lemma, the Cauchy transform and Bernstein's inequality.
- Formally, `not_theorem3_printed` (§1.3) is an unconditional `¬ (conclusion for φ₀, μ₀, 2)`.
- Hence `theorem3 hOCS φ₀ μ₀ … 2` yields `False`, i.e. **`theorem3 → ¬ TheoremOCS`**. Conversely `¬ TheoremOCS → theorem3` trivially.
- Since `TheoremOCS` is true (§5), `theorem3` is false, and it is unprovable unless `TheoremOCS` is refutable.

**Proposed replacement** (do not edit `comparator/` without the coordinator):
- `theorem3_weighted`: the integrand becomes `ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖)`. It is proved below from `TheoremOCS` and M13.
- `theorem3_of_lowerBound`: the printed form, under the extra hypothesis `∃ B, ∀ z, |Im z| < 1 → −B ≤ φ z`. It is a corollary.

### 0.2 `TheoremOCS` is **stronger** than the theorem it cites

Source checked: the postprint of [OCS99] (UB repository, hdl 2445/164425), **Lemma 4** (§4, p. 8 of the postprint).

> **Lemma 4** [OCS99]. Let `μ ∈ M(ℂ)` be a compactly supported measure such that `e^{−ε|Im z|} dμ(z)` is a two-sided Carleson measure. Then there is a solution `u` to `∂̄u = μ` such that `limsup_{z→∞} |u(z)| e^{−ε|Im z|} < ∞` and `|u(x)| ≤ C(1 + ∫_{|z−x|<1} d|μ|(z)/|x−z|)` for any `x ∈ ℝ`, where `C` depends only on `ε` and on the Carleson constant of `μ`.

Comparison, clause by clause ([OCS99, Lemma 4] / quote on RMI p. 375 / `TheoremOCS`):
- **Data.** Complex `μ` with compact support / same / `σν` with `‖σ‖ = 1`, `ν` finite, `ν Lᶜ = 0`, `L` compact. **Same**, by the polar decomposition of a complex measure.
- **Carleson hypothesis.** `∫_{D(x,r)} e^{−ε|Im|} d|μ| ≤ K r` for `x ∈ ℝ` / same / same with open balls. **Same.**
- **Decay.** `limsup |u| e^{−ε|Im z|} < ∞` / `= 0` / `Tendsto … (cocompact) (𝓝 0)`. **`TheoremOCS` is stronger than [OCS99].**
- **Pointwise bound.** All `x ∈ ℝ` / all `x ∈ ℝ` / `x ∈ ℝ \ L`. Weaker, and harmless: off `supp μ` is where `u(x)` is meaningful.
- **Regularity.** — / — / `DifferentiableOn ℂ u Lᶜ`. Implied by Weyl: choose the holomorphic representative off `supp μ`.
- **Constant.** `C(ε, K)` / `C(K)` / `C(α, K)`. Same.

- **The decay clause is genuinely stronger.** It is used: Theorem 3's conclusion `|u|e^{−φ} → 0` cannot be obtained from `< ∞` by our argument (§2.2). This is because the weight in the Carleson hypothesis and in the decay must be the same `α`.
- **It is nevertheless true; it follows from the proof in [OCS99].** The solution there is `u = u₁ + u₂ − u₃`:
  - **`u₁`.** `u₁ = (1/π)∫ sin ε(z−ζ)/(ε(z−ζ)²) dμ₁(ζ)` with `supp μ₁` compact in `|Im| ≤ 10`. It satisfies `|u₁|e^{−ε|Im z|} ≤ (e^{10ε}/πε)∫ d|μ₁|/|z−ζ|² → 0`.
  - **`u₂`.** `u₂ = φ_cut e^{∓iεz} v_{1,2}`, where `v₁, v₂` are Jones' solutions; [OCS99] states they decay like `|z|^{−2}`. Hence `|u₂| e^{−ε|Im z|} ≤ |v| → 0`.
  - **`u₃`.** `u₃` is the sinc-kernel integral of `∂̄u₂ = O(|ζ|^{−2})` over two strips. Using `|sin ε(z−ζ)/(ε(z−ζ)²)| ≲ e^{ε|Im(z−ζ)|}/(|z−ζ|(1+|z−ζ|))`, `|u₃|e^{−ε|Im z|} → 0` by dominated convergence.
  
  So `TheoremOCS` is "[OCS99, Lemma 4] with the decay read off its proof", exactly as quoted on RMI p. 375.
- **Recommendation:** record this in `formalization.yaml` / NOTEBOOK as an assumption slightly stronger than the published statement, justified by the published proof.

---

## 1. Statements

### 1.1 Paper (p. 358)

> **Theorem 3.** Let `φ` be subharmonic in `ℂ` with `Δφ` a locally doubling measure supported in `ℝ` and `Δφ(I(x,r)) > 1` for some `r > 0`. Consider `∂̄u = μ`, `μ` compactly supported with `e^{−φ} d|μ|` two-sided Carleson. Then there is a solution `u` with `limsup_{z→∞} |u(z)| e^{−φ(z)} = 0` and `|u(x)| e^{−φ(x)} ≤ C(1 + ∫_{|z−x|<1} d|μ|(z)/|x−z|)` for any `x ∈ ℝ`, where `C` does not depend on the support of `μ`.

### 1.2 Fixed comparator statement (false, §0.1)
```lean
-- (reconciled) NOT declared in `Theorem3.lean` (known false); kept there only as a comment.
theorem theorem3 (hOCS : TheoremOCS) (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingLine μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ), … →
      ∃ u, … ∧ ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-φ x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν)
```

### 1.3 Formal statements of this module (namespace `OC`)

```lean
/-- The measure `|χ_Ω ν / f|`. -/
def divMeasure (ν : Measure ℂ) (Ω : Set ℂ) (f : ℂ → ℂ) : Measure ℂ :=
  (ν.restrict Ω).withDensity fun z ↦ ENNReal.ofReal (1 / ‖f z‖)

/-- The phase of `σ / f` (junk value `1` at the zeros of `f`, which `divMeasure` never charges). -/
def divPhase (σ f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if f z = 0 then 1 else σ z * ((‖f z‖ : ℂ) / f z)

theorem norm_divPhase (σ f : ℂ → ℂ) (hσ : ∀ z, ‖σ z‖ = 1) (z : ℂ) : ‖divPhase σ f z‖ = 1
theorem measurable_divPhase {σ f : ℂ → ℂ} (hσ : Measurable σ) (hf : Continuous f) :
    Measurable (divPhase σ f)

-- 14.1 finiteness and the Carleson transfer
theorem isFiniteMeasure_divMeasure {ν : Measure ℂ} [IsFiniteMeasure ν] {L Ω : Set ℂ}
    (hL : IsCompact L) (hνL : ν Lᶜ = 0) {f : ℂ → ℂ} {g : ℂ → ℝ} (hg : Continuous g)
    (hfg : ∀ z ∈ Ω, g z ≤ ‖f z‖) (hg0 : ∀ z, 0 < g z) :
    IsFiniteMeasure (divMeasure ν Ω f)
theorem divMeasure_withDensity_le {ν : Measure ℂ} {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    {f : ℂ → ℂ} {φ : ℂ → ℝ} {α c : ℝ} (hf : Continuous f) (hφ : Continuous φ) (hc : 0 < c)
    (hlow : ∀ z ∈ Ω, c * Real.exp (φ z - α * |z.im|) ≤ ‖f z‖) (s : Set ℂ) (hs : MeasurableSet s) :
    ((divMeasure ν Ω f).withDensity fun z ↦ ENNReal.ofReal (Real.exp (-α * |z.im|))) s ≤
      ENNReal.ofReal c⁻¹ * (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) s
theorem lintegral_ball_divMeasure_le {ν : Measure ℂ} {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    {f : ℂ → ℂ} {φ : ℂ → ℝ} {α c : ℝ} (hf : Continuous f) (hφ : Continuous φ) (hc : 0 < c)
    (hα : 0 ≤ α)
    (hlow : ∀ z ∈ Ω, c * Real.exp (φ z - α * |z.im|) ≤ ‖f z‖) (x : ℝ) :
    ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂divMeasure ν Ω f ≤
      ENNReal.ofReal (c⁻¹ * Real.exp α) *
        ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν

-- 14.2 gluing: u = Σ f_i v_i solves ∂̄u = σν
theorem isWeakDbarSolMeasure_sum_mul {ι : Type*} [Fintype ι] {ν : Measure ℂ}
    [IsFiniteMeasure ν] {σ : ℂ → ℂ} (hσ : Measurable σ) (hσ1 : ∀ z, ‖σ z‖ = 1)
    (Ω : ι → Set ℂ) (hΩm : ∀ i, MeasurableSet (Ω i)) (hΩd : Pairwise (Function.onFun Disjoint Ω))
    (hΩc : ⋃ i, Ω i = univ) (f : ι → ℂ → ℂ) (hf : ∀ i, Differentiable ℂ (f i))
    (hf0 : ∀ i, ∀ z ∈ Ω i, f i z ≠ 0) (hfin : ∀ i, IsFiniteMeasure (divMeasure ν (Ω i) (f i)))
    (v : ι → ℂ → ℂ) (hv : ∀ i, IsWeakDbarSolMeasure (v i) (divMeasure ν (Ω i) (f i))
      (divPhase σ (f i))) :
    IsWeakDbarSolMeasure (fun z ↦ ∑ i, f i z * v i z) ν σ

-- 14.3 MAIN: Theorem 3, corrected (weight inside the integral)
theorem theorem3_weighted (hOCS : TheoremOCS) (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingLine μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) (ball (x : ℂ) r) ≤
          K * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-φ z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-φ x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1,
              ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν)

-- 14.4 the printed form, when φ is bounded below on the strip |Im z| < 1
theorem theorem3_of_lowerBound (hOCS : TheoremOCS) (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingLine μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r))
    (hlow : ∃ B : ℝ, ∀ z : ℂ, |z.im| < 1 → -B ≤ φ z) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) (ball (x : ℂ) r) ≤
          K * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-φ z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-φ x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν)

-- 14.5 the counterexample (documentation; optional, needs Bernstein's inequality)
def cexWeight (z : ℂ) : ℝ := |z.im| + z.re * z.im
def cexMeasure : Measure ℂ := (2 : ℝ≥0∞) • (volume : Measure ℝ).map (fun t : ℝ ↦ (t : ℂ))
theorem cex_isSubharmonicWeight : IsSubharmonicWeight univ cexWeight cexMeasure
theorem cex_doubling : IsLocallyDoublingLine cexMeasure
theorem cex_mass : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < cexMeasure (lineInterval x r)
theorem not_theorem3_printed :
    ¬ ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-cexWeight z))) (ball (x : ℂ) r) ≤
          (2 : ℝ≥0) * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-cexWeight z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-cexWeight x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν)
```

---

## 2. The reconstructed proof of `theorem3_weighted`

### 2.1 Data from M13 and from `TheoremOCS` (all independent of `ν, σ, L`)

1. **Multipliers.** `lineMultipliers φ μ hφ hd hm` gives `α₀ > 0`. Put `α := α₀`. It provides `f : Fin 2 → ℂ → ℂ`, `ε > 0`, `C_up > 0` with:
   - (F1) `f i` entire, zeros real;
   - (F2) `‖f i z‖ ≤ C_up e^{φ(z) − α|Im z|}` for **all** `z`;
   - (F3) every `z` lies in `G₀ ∪ G₁`, where `G_i := {z | ∀ x : ℝ, f i x = 0 → ε ρ(x) ≤ ‖z − x‖}`;
   - (F4) with `η := ε`: there is `c > 0` such that `z ∈ G_i ⟹ ‖f i z‖ ≥ c e^{φ(z) − α|Im z|}`.
2. **Partition of `ℂ`.** `Ω₀ := G₀` and `Ω₁ := G₀ᶜ`. Then `Ω₁ ⊆ G₁` by (F3), the pieces are disjoint with union `univ`, and both are measurable: `G₀` is closed, being an intersection of the closed sets `{z | ερ(x) ≤ ‖z−x‖}`.
   - On `Ω_i`: `‖f i z‖ ≥ c e^{φ(z) − α|Im z|} > 0`. In particular **`f i` has no zeros on `Ω_i`**.
3. **The cited theorem.** `hOCS α α₀_pos K'` with `K' := (c⁻¹).toNNReal * K` gives `C_O`.
4. **The constant.** `C := 2 · C_up · C_O · max(1, c⁻¹ e^{α})` (as `ℝ≥0`).

### 2.2 Where `α|Im z|` comes from, and why Theorem 5 alone is not enough

Off `ℝ`, `φ` is harmonic, and `log|f i| − φ = −α|Im z| + S_i` with `S_i` bounded on `Ω_i` (M13 §3.6). So `φ − log|f i| = α|Im z| + O(1)` on `Ω_i`. Dividing by `f i` turns the weight `e^{−φ}` into exactly the flat weight `e^{−α|Im z|}` of the Ortega-Cerdà–Seip theorem, and multiplying back by `f i` turns OCS's `|v_i| e^{−α|Im z|} → 0` into `|f i v_i| e^{−φ} → 0`.
- **With `α = 0`** (Theorem 5 as stated): `|f_i v_i| e^{−φ} ≃ |v_i|`, and OCS only gives `|v_i| = o(e^{α'|Im z|})` for its own `α' > 0`. The decay conclusion would then fail in the directions `|Im z| → ∞`.
- **Matching the two weights.** The Carleson hypothesis forces the OCS weight `α' ≥ α`: `e^{−α'|y|}/|f_i| ≲ e^{(α−α')|y|} e^{−φ}`. The decay forces `α' ≤ α`. So `α' = α`, and the decay must be `o(e^{α|y|})`, which is the `= 0` clause of `TheoremOCS` (§0.2).

### 2.3 The construction for given data `(ν, σ, L)`

Let `ν` be finite with `ν Lᶜ = 0`, `L` compact, `σ` measurable with `‖σ‖ ≡ 1`, and `(ν.withDensity e^{−φ})(ball x r) ≤ K r` for all `x ∈ ℝ`, `r > 0`.

For `i ∈ Fin 2` put `ν_i := divMeasure ν (Ω i) (f i)` (i.e. `|χ_{Ω_i} ν / f_i|`) and `σ_i := divPhase σ (f i)`. Then `σ_i ν_i = χ_{Ω_i} σ ν / f_i` as complex measures, because `f_i ≠ 0` on `Ω_i`.

**Hypotheses of `TheoremOCS` for `(ν_i, σ_i, L)`:**
1. **`IsFiniteMeasure ν_i`.** Apply `isFiniteMeasure_divMeasure` with `g := c e^{φ − α|Im|}` (continuous, `> 0`, `≤ ‖f_i‖` on `Ω_i`).
   - *Proof.* `ν_i(ℂ) = ∫⁻_{Ω_i} ofReal(1/‖f_i‖) dν ≤ ∫⁻_L ofReal(1/g) dν ≤ (sup_L 1/g) · ν(L) < ∞`. This uses `ν Lᶜ = 0`, and `1/g` is continuous on the compact `L` (`IsCompact.exists_bound_of_continuousOn`).
2. **Support and phase.**
   - `IsCompact L` ✓.
   - `ν_i Lᶜ = 0`: `ν_i ≪ ν` (`withDensity_absolutelyContinuous`, `restrict` monotone).
   - `Measurable σ_i` (`measurable_divPhase`; `f_i` is continuous).
   - `‖σ_i‖ = 1` (`norm_divPhase`: if `f z = 0` the value is `1`, otherwise `‖σ‖ · ‖f‖/‖f‖ = 1`).
3. **Carleson with weight `α|Im z|` and constant `K'`.** By `divMeasure_withDensity_le` with `s = ball x r`:
   `(ν_i.withDensity e^{−α|Im|})(ball x r) = ∫⁻_{ball ∩ Ω_i} e^{−α|Im z|}/‖f_i z‖ dν ≤ ∫⁻_{ball} c⁻¹ e^{−φ(z)} dν ≤ c⁻¹ K r`.
   - *Proof of the lemma.*
     - `withDensity_apply` twice and `lintegral_withDensity_eq_lintegral_mul₀`; the densities are measurable since `f, φ` are continuous.
     - `Measure.restrict_restrict`.
     - Pointwise on `Ω_i`: `e^{−α|y|}/‖f‖ ≤ e^{−α|y|}/(c e^{φ − α|y|}) = c⁻¹ e^{−φ}`.
     - Monotonicity of `∫⁻` in the set (`Ω_i ∩ s ⊆ s`).

`TheoremOCS` yields `v_i` with:
- `IsWeakDbarSolMeasure v_i ν_i σ_i`;
- `DifferentiableOn ℂ v_i Lᶜ`;
- `‖v_i z‖ e^{−α|Im z|} → 0` along `cocompact`;
- `ofReal ‖v_i x‖ ≤ C_O (1 + ∫⁻_{ball x 1} 1/‖x − z‖ dν_i)` for real `x ∉ L`.

**Definition.** `u := fun z ↦ f 0 z * v 0 z + f 1 z * v 1 z` (`= Σ_i f i z * v i z`).

### 2.4 Verification of the four conclusions

**(a) `IsWeakDbarSolMeasure u ν σ`** (`isWeakDbarSolMeasure_sum_mul`).
1. **`LocallyIntegrable u`.** Each `f_i` is continuous and `v_i` is locally integrable (`LocallyIntegrable.continuous_mul`-type lemma: integrable on each compact since `f_i` is bounded there).
2. **The weak equation.** Fix a test `χ` (smooth, compactly supported). For each `i` put `β_i := f_i · χ`.
   - `β_i` is a test function: `f_i` is entire, so `ContDiff ℂ ⊤ f_i` (`Differentiable.contDiff`), hence `ContDiff ℝ ⊤ f_i` (`restrict_scalars`); the product is smooth; `HasCompactSupport.mul_left`.
   - `dbar β_i = dbar f_i · χ + f_i · dbar χ = f_i · dbar χ` (M01 `dbar_mul`, `dbar_eq_zero_of_differentiableAt`).
   - So `∫ v_i f_i dbar χ = ∫ v_i dbar β_i = −∫ β_i σ_i dν_i` (by `hv i`).
   - `∫ β_i σ_i dν_i = ∫_{Ω_i} (1/‖f_i‖) · f_i χ σ_i dν` (`integral_withDensity_eq_integral_toReal_smul₀`; `(ofReal(1/‖f_i‖)).toReal = 1/‖f_i‖`).
   - On `Ω_i`, `f_i ≠ 0` and `(1/‖f_i‖) f_i σ (‖f_i‖/f_i) = σ`. So this is `∫_{Ω_i} χ σ dν` (`setIntegral_congr_fun`).
   - Summing over `i`: `∫ u dbar χ = Σ_i ∫ v_i f_i dbar χ`. Each summand is integrable: `v_i` is `L¹_loc` and `f_i dbar χ` is continuous with compact support (M01 `integrable_mul_of_locallyIntegrableOn`).
   - Hence `∫ u dbar χ = −Σ_i ∫_{Ω_i} χσ dν = −∫ χσ dν`, by `integral_union` for the disjoint measurable `Ω₀ ∪ Ω₁ = univ`; `χσ` is bounded measurable and `ν` is finite.

**(b) `DifferentiableOn ℂ u Lᶜ`.** Products and sums of `f_i` (entire) and `v_i` (holomorphic on `Lᶜ`).

**(c) Decay.** By (F2), `‖u z‖ e^{−φ(z)} ≤ Σ_i ‖f_i z‖ e^{−φ(z)} ‖v_i z‖ ≤ C_up Σ_i e^{−α|Im z|} ‖v_i z‖ → 0` (`squeeze_zero'`, `Tendsto.add`, `Tendsto.const_mul`).

**(d) Pointwise bound at real `x ∉ L`.**
1. **Multipliers on `ℝ`.** Since `Im x = 0`, (F2) gives `‖f_i x‖ e^{−φ(x)} ≤ C_up`. Hence
   `ofReal(‖u x‖ e^{−φ x}) ≤ Σ_i ofReal(C_up) · ofReal ‖v_i x‖ ≤ C_up C_O Σ_i (1 + ∫⁻_{ball x 1} 1/‖x−z‖ dν_i)`.
2. **Ball integrals** (`lintegral_ball_divMeasure_le`). On `ball x 1 ∩ Ω_i`, `|Im z| < 1`, so
   `1/‖f_i z‖ ≤ c⁻¹ e^{−φ(z)} e^{α|Im z|} ≤ c⁻¹ e^{α} e^{−φ(z)}`.
   Hence `∫⁻_{ball x 1} 1/‖x−z‖ dν_i ≤ c⁻¹e^{α} ∫⁻_{ball x 1} e^{−φ(z)}/‖x−z‖ dν =: c⁻¹ e^{α} J(x)`.
3. **Total.** `≤ 2 C_up C_O (1 + c⁻¹e^{α} J(x)) ≤ C (1 + J(x))`.

**Uniformity.** `C` depends on `(φ, μ, K)` only, through `α, c, C_up, C_O(α, c⁻¹K)`; not on `ν, σ, L`. ∎

**Zeros of `f_i` and division.** The data near a zero `λ` of `f₀` (inside `D(λ, ερ(λ))`, possibly inside `supp ν`) lies in `Ω₁`, where `f₁` is bounded below. No division by zero occurs.
- `divMeasure ν (Ω i) (f i)` never charges `{f_i = 0} ⊆ Ω_iᶜ`.
- So the junk values `1/‖0‖ = 0` and `divPhase = 1` there are irrelevant.

### 2.5 `theorem3_of_lowerBound`

Apply `theorem3_weighted`. On `ball x 1`, `|Im z| < 1`, so `e^{−φ(z)} ≤ e^{B}`. Hence `J(x) ≤ e^{B} ∫⁻_{ball x 1} 1/‖x−z‖ dν`, and `C' := C · max(1, e^{B})`.

---

## 3. Proofs of the auxiliary lemmas (14.1–14.2)

- **`norm_divPhase`.** Split on `f z = 0`. Otherwise `‖σ z · (‖f z‖/f z)‖ = 1 · ‖f z‖/‖f z‖ = 1`.
- **`measurable_divPhase`.**
  - `{z | f z = 0}` is closed, hence measurable.
  - `Measurable.ite`; `σ` is measurable; `‖f‖/f` is measurable (continuous `f`; `Measurable.div` on `ℂ`).
- **`isFiniteMeasure_divMeasure`, `divMeasure_withDensity_le`, `lintegral_ball_divMeasure_le`.** As in §2.3–2.4. They are pure `lintegral` monotonicity: `ENNReal.ofReal_le_ofReal`, `ENNReal.ofReal_mul`, `lintegral_mono`, `setLIntegral_mono`, `Measure.restrict_mono`.
  - `ENNReal.ofReal (1 / ‖f z‖)` is measurable since `f` is continuous.
- **`isWeakDbarSolMeasure_sum_mul`.** As in §2.4(a), with `Finset.sum` over `Fintype ι`:
  - `integral_finset_sum` for the left side;
  - `integral_finset_biUnion` / `integral_iUnion_fintype` for `Σ_i ∫_{Ω_i} = ∫`;
  - `hΩc` and `hΩd` give the partition.

---

## 4. The counterexample to the printed statement (§0.1), in detail

**Hypotheses.** `φ₀(z) = |y| + xy` (`z = x+iy`), `μ₀ = 2·ι_*Leb`.
- `Δ|y| = 2 dx ⊗ δ_{y=0}` (M13 13.7), and `Δ(xy) = 0`.
- `IsLocallyDoublingLine`: `μ₀(I(x,r)) = 4r`, doubling constant `2`.
- Mass: `r = 1` gives `4 > 1`.
- `φ₀` is continuous.

Let `H(z) := −(i/2)z²`, so `Re H = xy =: h`, and put `σ := e^{H}/|e^{H}| = exp(i Im H)` (continuous, unimodular).

**Data.** For `δ ∈ (0, 1/4)` put `x₀ := 1/δ` and `L := {x₀ − is : δ ≤ s ≤ 1}` (compact, disjoint from `ℝ`). Let `ν` be the image of `e^{φ₀(x₀−is)} 1_{[δ,1]}(s) ds` under `s ↦ x₀ − is`. Here `φ₀(x₀ − is) = s − x₀ s`.
- `ν` is finite, `ν Lᶜ = 0`.
- `e^{−φ₀} dν` is arc length on `L`, so `(ν.withDensity e^{−φ₀})(ball x r) ≤ 2r`: **Carleson with `K = 2`**.

**Suppose `C` works** and let `u` be the solution provided. Put `u₀ := u e^{−H}`.
1. **The transformed equation.** `∂̄u₀ = e^{−H}σν = e^{−h}ν =: ν₀ ≥ 0` (product of a weak solution with an entire function). `ν₀` is the image of `e^{s} 1_{[δ,1]}(s) ds`.
2. **Real points.** For real `x`, `h(x) = φ₀(x) = 0`, so `|u₀(x)| = |u(x)| e^{−φ₀(x)}`. Since `|x − z| ≥ s` on `L` and `x₀ = 1/δ`,
   `∫_{ball(x,1)} dν/|x−z| ≤ ∫_δ^1 e^{(1−x₀)s} ds/s ≤ e ∫_1^∞ e^{−v} dv/v = e E₁(1) < 0.6`.
   Hence `|u₀(x)| ≤ C₁ := 1.6 C` for **all** real `x`.
3. **Decay.** `|u₀(z)| e^{−|Im z|} = |u(z)| e^{−φ₀(z)} → 0`.
4. **Entire part.** Let `𝒞(z) := π⁻¹ ∫ dν₀(w)/(z − w)`, the Cauchy transform of the compactly supported `ν₀`. Then `𝒞 → 0` at `∞` and `∂̄𝒞 = ν₀`.
   - By Weyl, `g₀ := u₀ − 𝒞` agrees on `Lᶜ` with an entire function (both sides are continuous on `Lᶜ`).
   - From step 3, `|g₀(z)| ≤ B e^{|Im z|}`, and `g₀` is bounded on `ℝ`.
5. **Bernstein's inequality** (exponential type `1`): `sup_ℝ |g₀'| ≤ sup_ℝ |g₀| ≤ C₁ + sup_ℝ|𝒞| ≤ C₁ + (e/π) log(1/δ)`.
6. **Size of `𝒞`.** `𝒞(x₀ + t) = π⁻¹∫_δ^1 e^{s} ds/(t + is)`, so `Im 𝒞(x₀+t) = −π⁻¹ ∫_δ^1 e^{s} s/(t²+s²) ds`. For `δ < τ < 1`:
   `|𝒞(x₀) − 𝒞(x₀+τ)| ≥ π⁻¹∫_δ^1 e^s τ²/(s(τ²+s²)) ds ≥ π⁻¹ ∫_δ^τ ds/(2s) = (1/2π) log(τ/δ)`.
7. **Contradiction.**
   `2C₁ ≥ |u₀(x₀) − u₀(x₀+τ)| ≥ (1/2π)log(τ/δ) − τ(C₁ + (e/π)log(1/δ))`.
   With `τ := 1/log(1/δ)` the right side is `≥ (1/2π)(log(1/δ) − log log(1/δ)) − C₁ − e/π → ∞` as `δ → 0`.

The data live near `x₀ = 1/δ → ∞`: this is precisely the "C independent of the support" that fails. For the corrected statement, `J(x₀) ≍ log(1/δ)` matches `|u₀(x₀)| ≍ log(1/δ)`.

**Formalisation of §4 is optional.** Mathlib has no Bernstein inequality; the argument is documentation for the NOTEBOOK.

---

## 5. Interface

### 5.1 Consumed from M13 (Lean, typechecked)
```lean
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
```
This is used at `α = α₀ > 0`. The upstream needs of M13 (M02, M03 line forms, M07) are listed in M13 §4.2.

### 5.2 Consumed from M01 (exist in `Foundations/Wirtinger.lean`, `Foundations/Weyl.lean`)
```lean
theorem dbar_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w ↦ f w * g w) z = dbar f z * g z + f z * dbar g z
theorem dbar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    dbar f z = 0
lemma integrable_mul_of_locallyIntegrableOn …   -- for ∫ v_i · (f_i dbar χ)
```
For §4 only (optional): the Cauchy transform and Weyl (`Pompeiu.lean`, `Weyl.lean`), and Bernstein's inequality (new).

### 5.3 Not needed
M02, M03, M05–M12 directly (only through M13).

### 5.4 Exports
`theorem3_weighted`, the proposed comparator statement; `theorem3_of_lowerBound`; `theorem3` itself cannot be proved (§0.1).

---

### 5.5 Interface (reconciled)

Lean file `Theorem3.lean`; the statements of §1.3 are unchanged.
- **The printed `theorem3` is not declared.** It is known false (`not_theorem3_printed`). The comparator statement is kept in the file inside a comment, so that the build contains no `sorry` theorem that is known to be false.
- **`theorem3_weighted`** has the shape of a main statement:
  - hypothesis `TheoremOCS`;
  - the same hypotheses and quantifiers as `theorem3`;
  - the weighted integral `∫_{|z−x|<1} e^{−φ(z)} d|μ|(z)/|x − z|` in the conclusion.

  It is the intended replacement of `theorem3` in `comparator/statements.lean`.
- **Upstream.** M14 consumes only `lineMultipliers` from M13, together with M01's `dbar_mul`, `dbar_eq_zero_of_differentiableAt` and `integrable_mul_of_locallyIntegrableOn`.

## 6. Issues found (for the NOTEBOOK)

1. **p. 358, Theorem 3 is false as printed.** The integral must carry the weight: `|u(x)|e^{−φ(x)} ≤ C(1 + ∫_{|z−x|<1} e^{−φ(z)} d|μ|(z)/|x−z|)`. The counterexample `φ₀ = |Im z| + Re z Im z` is in §4. The printed form holds if `φ` is bounded below on `{|Im z| < 1}` (§2.5). The same text is in the arXiv version (math/9912139).
   - **Consequence for the formalisation:** `theorem3` in `comparator/statements.lean` is equivalent to `¬ TheoremOCS`. It must be replaced by `theorem3_weighted` (coordinator decision).
2. **p. 375, quote of [OCS99]: the decay is misquoted.** [OCS99, Lemma 4] states `limsup |u|e^{−ε|Im z|} < ∞`, not `= 0`. The `= 0` version follows from the proof in [OCS99] (§0.2) and is what Theorem 3 needs. `TheoremOCS` adopts `= 0`: it is stronger than the published statement and must be flagged as such in `formalization.yaml`.
3. **p. 375, "These two ingredients together prove Theorem 3": the ingredients do not fit.** One needs multipliers for `φ − α|Im z|`, not for `φ` (§2.2). Their Laplacian `μ − 2α dx` need not be positive. The paper's analogous step (Theorems 1–2) uses Lemma 6 (regularisation), which has no stated line version. M13 resolves this with the signed construction.
4. **p. 375:** "the same way as Theorem 1 and Theorem 2" also requires several multipliers with disjoint exceptional sets (Proposition 2 on the line). Its zeros must stay real: M13 uses the pair `λ ± s₀a` instead of the roots-of-unity shift `κ(R)`.
5. **Minor:**
   - "for any `x ∈ ℝ`" in Theorem 3 and in the quoted theorem should read `x ∈ ℝ \ supp μ`; for `x ∈ supp μ`, `u(x)` is not defined pointwise.
   - The quoted theorem's constant depends on `α` as well as on the Carleson constant ([OCS99] says "on `ε` and on the Carleson constant").

## 7. Formalisation risks
- **The integral identity in §2.4(a).** It needs `integral_withDensity_eq_integral_toReal_smul₀` (densities `ofReal(1/‖f‖)` are finite everywhere) together with the junk values at zeros of `f_i`. Restrict to `Ω_i` early, where `f_i ≠ 0`.
- **ENNReal bookkeeping in (d).** Keep `C_up`, `c⁻¹e^{α}` as `ℝ≥0` coercions; avoid `ENNReal` subtraction.
- **Low overall risk.** Once M13's `lineMultipliers` and `TheoremOCS` are available, the module is short (≈ 250 lines).
