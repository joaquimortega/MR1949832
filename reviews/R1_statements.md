# Referee report rv1: formal statements of Ortega-Cerdà, *Multipliers and weighted ∂̄-estimates* (RMI 18, 2002)

**Scope.**
- **Read:**
  - `OrtegaCerdaMultipliers/Defs.lean` and `comparator/statements.lean` (12 theorems). `Challenge.lean` was checked to equal Defs plus statements, up to whitespace.
  - `blueprint/M00_Defs.md`, `blueprint/README.md`, `M14_Theorem3.md`, and the relevant parts of `M08` and `M11`.
  - The journal PDF. All 23 pages were rendered at 160 dpi, and p. 356 again at 300 dpi.
  - The [OCS99] postprint (UB repository), pp. 8–9 rendered.
- **Typechecked:** `rv1_check.lean` in the scratchpad.
  - It contains the proposed fixes, plus sanity lemmas on the junk values: `edistSet z ∅ = ⊤`, `0^0 = 1`, `x/0 = ⊤`, `(0:ℝ≥0)⁻¹ = ⊤`.
  - It compiles; the only warnings are the expected `sorry`s.
- **Numerical check of the Theorem 3 counterexample:** `rv1_cex_num.py`.

**Summary of verdicts**

| Statement | Verdict |
|---|---|
| `theorem3` | **FALSE** (given that `TheoremOCS` is true, which it is). Replace. |
| `TheoremOCS` | True. Matches the RMI p. 375 quote. Stronger than the *statement* of [OCS99, Lemma 4], but follows from its proof. Document it. |
| `theorem4_disc/plane` | Faithful to the corrected Theorem 4. The printed order is an erratum. Not vacuous. |
| `prop2_disc/plane` | Faithful. Not vacuous. |
| `theorem2` | Stronger than the paper (normalisation, single `u`, uniform `C`) and true, with the corrected sign of the auxiliary weight. |
| `theorem2_printed` | Documented weakening (`u` depends on `p`). Follows from `theorem2` applied to `φ/p`. |
| `theorem2_uniform` | Plausible from the proof. |
| `theorem1`, `theorem1_christ` | Stronger than the paper (uniform `C`). True. |
| `prop1` | Upper bound only. Justified: the printed `≃` is false for *every* kernel (stronger than the blueprint's reason). |
| `theorem5` | Faithful. Not vacuous. |
| Weight class `IsSubharmonicWeight` | Equivalent to the paper's class. Intended examples satisfy it. |

---

## 1. `theorem3` is false (Theorem 3, p. 358, is false as printed). Severity: **FALSE**

**Paper (p. 358).** `|u(x)| e^{−φ(x)} ≤ C (1 + ∫_{|z−x|<1} d|μ|(z)/|x−z|)`, with no weight in the integral, and "C does not depend on the support of μ".
- `theorem3` transcribes this faithfully: `C` is chosen after `φ, μ, K` and before `(ν, σ, L)`.

**Verification of the M14 §4 counterexample.** I re-derived every step independently.
- **Weight.** `φ₀(z) = |y| + xy` and `μ₀ = 2·(Lebesgue on ℝ)`.
  - `∫|y| χ_yy dy = 2χ(x,0)` and `Δ(xy) = 0`, so `IsSubharmonicWeight univ φ₀ μ₀` holds.
  - `μ₀(I(x,r)) = 4r`, so local doubling holds with constant 2, and the mass condition holds with `r = 1`.
- **Data.**
  - `L = {x₀ − is : δ ≤ s ≤ 1}` with `x₀ = 1/δ`.
  - `ν = e^{φ₀} · (arc length on L)`, where `φ₀(x₀ − is) = s(1 − x₀)`.
  - `σ = exp(i Im H)` with `H = −(i/2)z²`, so that `Re H = xy`.
  - Then `e^{−φ₀}ν` is arc length on a segment, hence Carleson with `K = 2`. `ν` is finite, `L` is compact, and `σ` is continuous and unimodular.
- **Bound on ℝ.** `φ₀ = 0` on ℝ. With `|x − z| ≥ s` on `L`, `∫_{B(x,1)} dν/|x−z| ≤ ∫_δ^1 e^{(1−x₀)s} ds/s ≤ e·E₁(1) < 0.6`. Numerically ≈ 0.22 for `δ = 10⁻²…10⁻⁶`.
  - So any `u` as in the conclusion has `|u(x)| ≤ 1.6 C` on all of ℝ (`L ∩ ℝ = ∅`).
- **Gauge.** `u₀ = u e^{−H}` solves `∂̄u₀ = e^{s} ds` on `L`, a positive measure of mass `< e`, independent of `x₀`.
  - On ℝ, `|u₀| = |u|`.
  - `|u₀| e^{−|y|} = |u| e^{−φ₀} → 0`.
- **Entire part.** `g₀ = u₀ − 𝒞`, with `𝒞` the Cauchy transform of `e^{s}ds`, is entire (Weyl). On `Lᶜ` it equals the holomorphic representative, which is what `DifferentiableOn ℂ u Lᶜ` provides.
  - `|g₀| ≤ B e^{|y|}`.
  - `sup_ℝ |g₀| ≤ 1.6C + (e/π) log(1/δ)`.
  - Bernstein's inequality gives `sup_ℝ |g₀′| ≤ sup_ℝ |g₀|`. Alternatively, Phragmén–Lindelöf plus Cauchy estimates give the same up to a factor `e`.
- **Contradiction.**
  - `|𝒞(x₀) − 𝒞(x₀+τ)| ≥ |Im| = π⁻¹∫_δ^1 e^s τ²/(s(τ²+s²)) ds ≥ (2π)⁻¹ log(τ/δ)`. Checked numerically: e.g. for `δ = 10⁻⁶` it is `3.60 ≥ 1.78`.
  - With `τ = 1/log(1/δ)`: `3.2C ≥ (2π)⁻¹(log(1/δ) − log log(1/δ)) − O(1) − 1.6C/log(1/δ) → ∞`.
- **Conclusion.** The conclusion of `theorem3` fails *unconditionally* for `(φ₀, μ₀, K = 2)`.

**Consequence.**
- `theorem3 → ¬TheoremOCS`, and trivially `¬TheoremOCS → theorem3`. So `theorem3 ↔ ¬TheoremOCS`.
- `TheoremOCS` is true (finding 2), so `theorem3` is false and unprovable.
- It cannot be rescued by weakening `TheoremOCS` (e.g. to the published `limsup < ∞`): the counterexample does not use `TheoremOCS` at all.

**Diagnosis.** The problem is invariant under `φ ↦ φ + Re H`, `u ↦ u e^{H}`, `μ ↦ e^{H}μ` (with `H` entire). The printed right-hand side is not invariant; the weighted one, `∫ e^{−φ(z)} d|μ|(z)/|x−z|`, is. The two agree up to constants when `φ` is bounded below on `{|Im z| < 1}`, e.g. `φ = α|Im z|`, the case of the quoted [OCS99] theorem.

**Fix (typechecked in `rv1_check.lean`).**
- Replace `theorem3` in `comparator/statements.lean` with the statement below and keep the name `OC.theorem3` in `config.json`. Alternatively rename it to `theorem3_weighted` and update `theorem_names`.
- Record it in the NOTEBOOK/yaml as a correction of a false printed statement.

```lean
theorem theorem3 (hOCS : TheoremOCS) (φ : ℂ → ℝ) (μ : Measure ℂ)
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
              ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν) := sorry
```

- **Optional addition:** M14's `theorem3_of_lowerBound`. It is the printed right-hand side under `hlow : ∃ B, ∀ z, |z.im| < 1 → -B ≤ φ z`, also typechecked.
- **Plausibility of the fix.** I checked the M14 §2 reduction:
  - multipliers `f_i` with `|f_i| ≃ e^{φ−α|Im z|}` (M13) turn the weighted Carleson hypothesis into the flat one with constant `c⁻¹K`;
  - on `B(x,1)`: `1/|f_i| ≤ c⁻¹e^{α}e^{−φ}`;
  - the decay transfers because the same `α` is used.

  The reduction is sound, given M13's `lineMultipliers`, which is not reviewed here.
- **Junk values.** The real-division value at `z = x` (`/0 = 0`) is harmless: `x ∉ L` and `ν Lᶜ = 0` give `ν{x} = 0`.

---

## 2. `TheoremOCS`: true, but stronger than the published statement of [OCS99, Lemma 4]. Severity: **MINOR** (documented and justified)

**Evidence.** In the UB postprint of OCS99 (rendered p. 8), Lemma 4 reads `limsup_{z→∞} |u(z)| e^{−ε|Im z|} < ∞`. RMI p. 375 quotes it as `= 0`.
- The print version in J. Funct. Anal. 162 (1999) was not checked; the postprint is presumably identical.

**Is `TheoremOCS` implied by the p. 375 quotation?** Yes, clause by clause:
- **Data.** `σν` with `ν = |μ|`, `L ⊇ supp μ` compact. Same as the quote.
- **Carleson hypothesis.** Open balls versus the paper's unspecified discs: equivalent up to a factor 2 in `K`.
- **Constant.** `C = C(α, K)` is weaker than the quote's `C(K)`.
- **Pointwise bound.** Asserted only for `x ∈ ℝ \ L`, which is weaker.
- **Regularity.** `DifferentiableOn ℂ u Lᶜ` holds for the holomorphic representative off `supp μ` (Weyl). That is the only reading under which the quote's pointwise `u(x)` is meaningful; the decay clause transfers to it by the mean value property.

**Does `= 0` follow from the [OCS99] proof (pp. 8–9)?** Yes:
- `u₁ = π⁻¹∫ sin ε(z−ζ)/(ε(z−ζ)²) dμ₁` gives `|u₁|e^{−ε|y|} ≤ (e^{10ε}/πε)∫ d|μ₁|/|z−ζ|² → 0`.
- `u₂ = φ_cut e^{∓iεz} v` gives `|u₂|e^{−ε|y|} ≤ |v| = O(|z|^{−2})`, from Jones' formula with compactly supported `σ`.
- `u₃` is the sinc-kernel integral of `∂̄u₂ = O(|ζ|^{−2})` over two horizontal strips. Use `|sin εw/(εw²)| ≲ e^{ε|Im w|}/(|w|(1+|w|))`; dominated convergence gives `→ 0`.

So `TheoremOCS` is true. `theorem3` therefore really is false, not vacuously true.

**Fix (documentation only).** Add to the `TheoremOCS` docstring and the yaml: "the decay clause `= 0` is as quoted on RMI p. 375. [OCS99, Lemma 4] states `< ∞`, and `= 0` follows from its proof (u₁, u₂, u₃ on pp. 8–9 of the postprint)." M14 §2.2 is correct that `< ∞` would not suffice: the Carleson transfer forces the OCS exponent `α′ ≥ α`, and the decay forces `α′ < α`.

---

## 3. Theorem 4: printed inequalities reversed (p. 363, and again p. 372). Severity: **CONFIRMED-ERRATUM** (formal statements correct)

**Evidence.**
- p. 363 prints `d/ρ ≲ |h|e^{−ψ} ≲ (d/ρ)^M`.
- The Remark gives `d ≲ ρ`, and zeros have multiplicity `m ≥ 1` (p. 366: "all the points `λ_j` appear with a multiplicity `m`"). As `z → λ`, `d/ρ ≲ (d/ρ)^M` fails for `M > 1`.
- The proof bounds (2)–(3) on pp. 366–367 and the sentence "the sum accounts for the term `(d/ρ)^M`" (p. 368) give `(d/ρ)^M ≲ |h|e^{−ψ} ≲ d/ρ`.
- The same reversal appears at p. 372 for `g`.
- (2)/(3) also bound `∫ log|z−ζ|(Δψ−Σδ)` with the wrong sign and without the `2π` on the point masses (p. 366); the `2π` is the M08 claim, which I agree with.

**Non-vacuity of `theorem4_*`, `prop2_*`.**
- `h ≡ 0` is excluded by `∃ z₀, h z₀ ≠ 0`.
- `C = 0` forces `h ≡ 0`.
- `massRadius*` is positive and finite: hm makes the set nonempty; there are no atoms, because local doubling excludes them; and `μ` is finite on compacts.
- `M = 0` forces `h` zero-free (`0^0 = 1` at a zero).
- A zero-free `h` makes `edistSet = ⊤`, which forces `M = 0`. That leaves the case `M = 0` with a zero-free `h` and `|h| ≥ C⁻¹e^{ψ}`, which is impossible:
  - in ℂ, `ψ − log|h|` would be subharmonic and bounded above, hence constant, so `μ = 0`;
  - in 𝔻, `ψ − log|h| ≤ c` forces the Blaschke condition `∫(1−|ζ|)dμ < ∞`, but the mass condition gives `≳ Σ_k 2^k · 2^{−k} = ∞`.

**Fix.** None in Lean. Add a NOTEBOOK entry (already planned in M08 §924).

---

## 4. Theorem 2 proof: sign of the auxiliary weight, and the printed `L^p` normalisation. Severity: **CONFIRMED-ERRATUM**

**Evidence (pp. 372–374).**
- **The sign of `ψ`.** `ψ = φ − (ε/2) log(1−|z|²)` appears at p. 372 l. −12 and p. 373 l. −13. With it, `e^{ψ−φ} = (1−|z|²)^{−ε/2}`. The step "`|g| ≲ e^ψ`, thus `∫|u|^p e^{−φ}/(1−|z|) ≲ ∫|u/g|^p (1−|z|)^{ε/2}/(1−|z|)`" needs `|g|^p e^{−φ} ≲ (1−|z|)^{ε/2}`. That holds only for `p = 1` and `ψ = φ + (ε/2)log(1−|z|)`, i.e. with the opposite sign.
- **Only `p = 1`.** For general `p` the factor `e^{(p−1)φ}` is uncontrolled. The next display, `|f/g|^p (1−|z|)^{ε/2} ≃ |f|^p e^{−φ}`, likewise needs `p = 1`.
- **The kernel bound on p. 374.** It inherits the sign: `((1−|ζ|)/(1−|z|))^{ε/2}`. With it, the Schur row integral is `(1−|z|²)^{−ε/2} · O(1) → ∞` and the column integral diverges (exponent `−1−ε/2 < −1`). The positive majorant therefore gives no `p = ∞` and no `p = 1` bound.
- **The paper's own `> ε/2` confirms a typo.** "`(1−|z|²)²Δψ > ε/2`" is consistent only with the corrected sign.

**Correct version (verified).** Take `ψ = φ̃ + c log(1−|z|²)`, where `φ̃` is from Lemma 6 and `0 < c ≤ ε/8` for the standard Laplacian, since `Δ log(1−|z|²) = −4/(1−|z|²)²`.
- On `dλ = dm/(1−|z|²)`, the conjugated kernel is `K(z,ζ) ≲ (1−|ζ|²)/(|1−ζ̄z||z−ζ|) · ((1−|z|²)/(1−|ζ|²))^{c}`.
- Both Schur integrals are `O(1)` by Forelli–Rudin:
  - row: `t = −c`, `s = c`;
  - column: `t = c−1`, `s = 1−c`;
  - plus the local `1/|z−ζ|` part.
- Hence `L^p(dλ)` bounds for all `p ∈ [1,∞]`, uniformly in `p`.

**Fix.** NOTEBOOK entries only (M11 §524–528 already has them; I confirm them).

---

## 5. `theorem2`: stronger than the paper, and true. Severity: **STRONGER-THAN-PAPER** (acceptable)

**Differences from the paper.**
- **Normalisation.** `‖u e^{−φ}‖_{L^p(dλ)}` instead of `∫|u|^p e^{−φ} dλ`. The two coincide at `p = 1`.
- **One `u` and one `C`** for all `p ∈ [1, ∞]`.
- **`p = ∞` as essential suprema**, with `(1−|ζ|²)` in place of `(1−|ζ|)`. The factor ≤ 2 is absorbed in `C`. The ess sup on the right is ≤ the sup, so on `f` this is stronger, and the right notion for a.e.-defined `u`.

**Truth.** It follows from finding 4 (Schur with the corrected `ψ`).

**Admissibility.** `∃ p ≥ 1` with `‖f(1−|z|²)e^{−φ}‖_{L^p(dλ)} < ∞`.
- This gives `f ∈ L^p_loc(𝔻) ⊂ L¹_loc(𝔻)`, since `φ` is continuous on 𝔻.
- It gives a.e. absolute convergence of `∫κ f`, since `T|F| ∈ L^{p}`.
- The same pointwise integral serves every other `p` with finite right-hand side.

`IsWeakDbarSol` is a.e.-insensitive, so junk values of the Bochner integral on a null set are harmless.

**Hypotheses.** Quantifier order, `discMeasure`, and the mass condition `1 < μ(hypBall z r)` (paper: `> 1`) are all faithful.

---

## 6. `theorem2_printed`: `u` depends on `p`. Severity: **UNFAITHFUL** (documented, justified weakening; derivation verified)

**Derivation.** Apply `theorem2` to `(φ/p, p⁻¹•μ)`:
- `IsSubharmonicWeight` scales.
- Local doubling has the same constant.
- **Mass condition.** `hypBall z (2⌈p⌉r)` contains `⌈p⌉` disjoint balls `hypBall w_j r`, with `w_j` on a geodesic at distance `2jr` (β is a metric). So `μ(hypBall z (2⌈p⌉r)) > ⌈p⌉ ≥ p`.
- **Admissibility at exponent `p`** is exactly the printed finiteness.
- Raising to the `p`-th power gives the printed estimate with `C_printed = C(φ/p)^p`.

**What is lost.** The printed text "there is a solution `u` … for any `p ∈ [1,∞)` and [sup bound]" can be read as one `u` for all `p` in the printed normalisation. Neither the formal statements nor the proof give that. `theorem2` gives one `u` for the sup bound and for `p = 1` in the printed form.

**Fix.** None required. Keep the docstring remark "solution allowed to depend on `p`", and say so in the yaml.

---

## 7. `theorem2_uniform`. Severity: **STRONGER-THAN-PAPER** (plausible)

**Constants traced through the proof.** Every constant depends only on `(Cd, r)`:
- Lemma 1 `γ`, Claim 1 `C_K`, Lemma 3 (or the area-counting replacement), and the partition eccentricity `L(N)`;
- Lemma 6: `sup|φ−φ̃| ≲` the [Chr91, Lemma 2.3] constant times a bounded number of cubes, and `ε < (1−|z|²)²μ̃₁ < K` with `ε, K` depending on `R`;
- the choice `c = c(ε)` and the Forelli–Rudin constants, which depend on `c`;
- the multiplier constants, which depend on the doubling constant and `sup ρ ≤ r`.

**Large Riesz measure.** A large `μ` (small `ρ`) only helps, by analogy with the scaling of `A|z|²` in ℂ, where the constant improves like `A^{−1/2}`. No upper bound on `μ` is needed.

**Edge case.** `Cd < 1` makes the hypotheses unsatisfiable (finite, nonzero ball masses), which is harmless.

**Fix.** None.

---

## 8. Proposition 1: the printed lower bound is false for every kernel. Severity: **CONFIRMED-ERRATUM** (stronger than the blueprint's reason)

**Blueprint's reason (correct).** The paper's kernel `k = e^{φ(ζ)−φ(z)}κ′` vanishes at the zeros of `h_i` (p. 374).

**Stronger fact.** No kernel satisfies the two-sided bound for general admissible `φ`.
- **Reduction.** Suppose `u = ∫e^{φ(z)−φ(ζ)}k f` solves `∂̄u = f` for all test `f`.
  - Then `K(·,ζ) = e^{φ(·)−φ(ζ)}k(·,ζ)` satisfies `∂̄_z K = δ_ζ` for a.e. `ζ`.
  - So `G_ζ(z) = π(z−ζ)K(z,ζ)` is a.e. an entire function.
  - Under `|k| ≃ e^{−ε|z−ζ|²}/|z−ζ|`, `G_ζ` is zero-free with `log|G_ζ| = φ(z) − ε|z|² + (harmonic) + O(1)`.
  - Hence `w := φ − ε|z|² − (harmonic)` is bounded on ℂ.
- **Counterexample weight.** `φ = |z|² + 2x₊²`, so `Δφ = 4 + 4·1_{x>0}`. It is doubling and satisfies the mass condition, so it meets the hypotheses of Theorem 1.
- **Contradiction.** Circle means give `M_w(z₀,R) − w(z₀) = (2π)⁻¹∫_0^R Δw(D(z₀,t)) dt/t`.
  - At `z₀ = 0` this is `(6−4ε)R²/4`.
  - At `z₀ = −T` with `R = T` it is `(4−4ε)T²/4`.
  - Both cannot be bounded for any `ε`.
- **Note.** For `φ = |z|²` the two-sided bound does hold, with `ε = 1`.

**Formal `prop1`.** It keeps only the upper bound, with `k` fixed before `f`, which is correct. Admissibility and the a.e. junk values of the Bochner integral are harmless.

**Fix.** None in Lean. The NOTEBOOK entry should say "false for any kernel (example `φ = |z|² + 2x₊²`)", not only "at zeros of the multipliers".

---

## 9. `theorem1`, `theorem1_christ`. Severity: **STRONGER-THAN-PAPER** (true)

**Faithful parts.**
- The paper's Theorem 1 already has one `u` for all `p ∈ [1,∞]`.
- `theorem1` uses local doubling, as the p. 357 remark allows. `theorem1_christ` follows from it, since doubling implies local doubling.
- The mass condition `1 ≤ μ(ball z r)` is faithful (p. 356 has `≥ 1`).

**Strengthening: `C` uniform in `p`.**
- It is true by the Schur test with the kernel `e^{−(ε/2)|z−ζ|²}/|z−ζ| ∈ L¹`.
- The plane computation `ψ = φ − (ε/2)|z|²` has the correct sign. I checked that `e^{ψ(z)−ψ(ζ)}·|e^{ε(ζ̄z−|ζ|²)}| = e^{φ(z)−φ(ζ)}e^{−(ε/2)|z−ζ|²}`.

**Fix.** None.

---

## 10. Weight class (`IsSubharmonicWeight`). Severity: **CONFIRMED** (equivalence holds); **MINOR** wording issue in M00 §2

**Formal ⇒ paper.** If `φ` is continuous and `Δφ = μ ≥ 0` in `𝒟′`, then the mollifications `φ*ρ_ε` decrease to `φ` (pointwise, by continuity), so `φ` is subharmonic. Its Riesz measure is `μ`, in the paper's normalisation `Δφ` (no `1/2π`). Mathlib's `Laplacian.laplacian` on ℂ is `∂²ₓ + ∂²ᵧ` (`laplacian_eq_iteratedFDeriv_complexPlane`), which is correct.

**Paper ⇒ formal.** Locally, `φ = (2π)⁻¹∫_B log|z−ζ| dμ + h`.
- [Chr91, Lemma 2.3] in the form `∫_{B(z,δ)} log(δ/|z−ζ|) dμ = ∫_0^δ μ(B(z,t)) dt/t ≲ μ(B(z,δ))` uses reverse doubling, i.e. the right inequality of Lemma 1.
- Combined with `log(1/δ)·μ(B(z,δ)) ≲ δ^γ log(1/δ)`, the truncated potentials converge *uniformly* on compacts, so the potential is continuous.
- The line case reduces to the 1-D lemma via `|z−t| ≥ |Re z − t|`.

**Wording issue.** M00 says the bound at a single radius "together with dominated convergence gives continuity". Strictly, the bound must be applied at all small radii, which gives uniform integrability. Suggested wording: "applied at every scale `δ → 0`, uniformly for `z` in a compact set, it shows that the truncated potentials converge uniformly".

**Junk values.** None: `φ·Δχ` vanishes on a neighbourhood of `Ωᶜ` and is continuous, and `χ` is integrable for `μ`. `carried` is only a normalisation.

---

## 11. The intended examples satisfy the hypotheses. Severity: **CONFIRMED**

**Disc: `φ = α log(1/(1−|z|²))`.**
- `Δφ = 4α/(1−|z|²)² dm`. Take `μ = (volume.restrict 𝔻).withDensity (4α/(1−‖z‖²)²)`: it is carried by 𝔻 and finite on compacts of 𝔻. Junk values of `φ` off 𝔻 are irrelevant.
- With `β = artanh ρ`, `hypBall z r = {ρ < tanh r}`. By Möbius invariance, `μ(hypBall z r) = 4πα·tanh²r/(1−tanh²r) = 4πα sinh²r`.
- Mass condition: `> 1` for large `r`.
- Local doubling: `sinh²2s/sinh²s = 4cosh²s ≤ 4cosh²(1/2)`.

**Plane and line.**
- Plane: `φ = |z|²` with `μ = 4 dm`.
- Line: `φ = α|Im z|` with `μ = 2α·Leb_ℝ`. Here `IsLocallyDoublingLine` holds and the mass condition holds with `r > 1/(4α)`.

---

## 12. Hyperbolic normalisation and "radius < 1". Severity: **CONFIRMED** (no issue)

**Normalisation.** `β = artanh ρ` is the Poincaré metric `|dz|/(1−|z|²)`. Other normalisations are scalar multiples `cβ`, which give `ρ_new = cρ_old`; the ratios `d/ρ` and `ερ(λ) ≤ d` are invariant.

**Local doubling at different scales.** Local doubling at scales `< 1` implies local doubling at any bounded scale `S`. Cover `B(z,2S)` by `N(S)` balls of radius 1/8, which is uniform by homogeneity, and chain-compare along geodesics with steps `< 1/8`. So "radius `< 1`" is normalisation-independent. The same holds in ℂ and on ℝ.

---

## 13. `theorem5`, `prop2_*`. Severity: faithful (the nonvanishing clause is added and justified)

**`theorem5`** matches p. 374–375 exactly: `∀ ε ∃ C`, Euclidean exceptional discs `|z−λ| ≥ ερ(λ)`, zeros real.
- `f ≢ 0` is needed. A zero-free `f` would need `φ − Re g` bounded, so `φ` subharmonic and bounded relative to a harmonic function, hence `μ = 0`. Together with `f ≢ 0`, the statement is not vacuous.
- Sanity check: `φ₀ = |y| + xy` has the multiplier `sin z · e^{−iz²/2}`.

**`prop2_*`.**
- "`∀ z ∃ i`, `z ∉ E_{h_i}`" is exactly `⋂E_{h_i} = ∅`.
- `n = 0` is excluded because the domain is nonempty.
- `∃ ε` is appropriate: the paper's construction works for small `ε`.
- The last clause is the Remark after Theorem 4.

---

## 14. Documentation errors in the blueprint. Severity: **MINOR**

1. **`README.md` §4, first bullet ("p. 356, Example: `∫ f dm = 0` should be `≠ 0`") is spurious.**
   - The journal prints `∫_𝔻 f(z) dm(z) ≠ 0` (rendered at 300 dpi). `pdftotext` drops the overlaid slash of `≠`.
   - Fix: delete the bullet. It must not go into NOTEBOOK.md as a paper erratum.
2. **`M00_Defs.md` §3, Proposition 2** says "The full Theorem-4 bounds for each `h_i` are not restated". `statements.lean` restates them, as README §3a.7 says. Fix: delete that sentence.
3. **`IsTwoSidedCarleson` is defined in `Defs.lean` but unused** (`TheoremOCS` and `theorem3` inline it). It is harmless. Fix (optional): either delete it from Defs/Challenge, or use it in `TheoremOCS` and `theorem3` for readability.
4. **`M00_Defs.md` §3, Theorem 3** says that `TheoremOCS` "must be *implied by* the published theorem". It is implied by the RMI p. 375 quotation, not by the published [OCS99, Lemma 4] (finding 2). Update the wording accordingly.

---

## 15. Items checked with no issue found

- **Distances.** `edistSet`/`hypDistSet` equal `⊤` on `∅`, so there is no junk 0 (sanity lemma typechecked). The quotient `d/ρ` in `ℝ≥0∞` is genuine because `ρ ∈ (0, R]`.
- **`IsWeakDbarSol` and `IsWeakDbarSolMeasure`.** The signs are correct: `−∫u∂̄α = ∫ασdν`. The integrals are genuine, since test functions have compact support, `σ` is bounded and `ν` is finite. `ContDiff ℝ (⊤ : ℕ∞)` means smooth.
- **`dbar`.** It equals `½(∂ₓ + i∂ᵧ)`, and `artanh x = ½ log((1+x)/(1−x))` on `[−1, 1]`.
- **Quantifier order.** In every statement, `C` (and `M`, `ε`, `n`) come after the weight data and before `f` or `(ν, σ, L)`. In `theorem3` and `TheoremOCS`, `K` comes before `C`, as "C does not depend on the support" requires.
