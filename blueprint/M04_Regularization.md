# M04 — Lemma 6: regularization of the weight

**Lean file:** `OrtegaCerdaMultipliers/Regularization.lean` (namespace `OC`).

**Paper:** §4.1, Lemma 6 and its proof, pp. 370–372.

**Depends on:**
- **M02** (`Potential/Local.lean`, `Potential/Weyl.lean`):
  - `bumpKernel` API (`bumpKernel_le`, `le_bumpKernel`, `measurable_bumpKernel`);
  - `IsLocalPotData` and its lemmas, `localPot`, `smoothedDensity`, `exists_localPot_le`;
  - `IsSubharmonicWeight.integrable_mul`, `IsSubharmonicWeight.sigmaFinite`.
- **M03:** local doubling at all scales, [Chr91, Lemma 2.3], reverse doubling (Lemma 1), no atoms. The exact statements assumed are in §2.
- **M01:** hyperbolic balls versus pseudo-hyperbolic and Euclidean balls, and the triangle inequality for `β`. Exact statements in §2.
- **Mathlib:**
  - `withDensity` API: `withDensity_apply`, `withDensity_add_left`, `withDensity_mono`, `lintegral_withDensity_eq_lintegral_mul`, `withDensity_smul`;
  - `measurable_measure_prodMk_left`, `integral_add_measure`;
  - `Real.tendsto_log_mul_rpow_nhds_zero`.

**Used by:**
- **M11** (Theorem 2): `lemma6_disc`.
- **M12** (Theorem 1, Proposition 1): `lemma6_plane`.

Lemma 6 is **not** used by Theorem 4, Proposition 2 or Theorems 3 and 5 (§7).

## 1. The paper

**Lemma 6** (p. 370). "If the measure `Δφ` is a locally doubling measure in `Ω` and `Δφ(D(z,r)) > 1` for some large radius `r > 0` and any point `z ∈ Ω` then there is a subharmonic weight `ψ` equivalent to the original, i.e. `sup_Ω |φ − ψ| < +∞`, such that `Δψ` is a locally doubling measure and moreover `Δψ > ε dm(z)` for some `ε > 0`."

In `𝔻` the proof gives, and Theorem 2 needs, the invariant form `(1 − |z|²)² Δψ > ε` (p. 371, "when `Ω = 𝔻`, it satisfies `ε < (1−|z|²)² μ̃₁ < K`").

**The paper's proof** (pp. 370–372):
1. Tile `Ω` by squares `Q_j` of diameter `R` (dyadic squares in the disc) with `μ(Q_j) > 2`.
2. Split `μ = μ₁ + μ₂` with `μ₁|_{Q_j} = μ/μ(Q_j)`. Then `μ/2 ≤ μ₂ ≤ μ`, so `μ₂` is locally doubling. Also `μ₁` is locally doubling and `μ₁(Q_j) = 1`.
3. Put `μ̃₁ = μ₁ ⋆ χ_{D(0,2R)}/|D(0,2R)|`, the invariant convolution in `𝔻`. Then `ε dm < μ̃₁ < K dm`, respectively `ε < (1−|z|²)² μ̃₁ < K`.
4. Put `ψ = φ + K[μ̃₁] − K[μ₁]`, with the global potentials `K` (M02, Appendix A). Then `Δψ = μ̃₁ + μ₂`.
5. Bound `|φ − ψ| = |K[μ₁] − K[μ̃₁]| ≲ ∫_{D(z,2R)} log(2R/d(z,ζ)) dμ₁(ζ) ≲ μ₁(D(z,2R))` by [Chr91, Lemma 2.3]. This is bounded, since `D(z,2R)` meets boundedly many `Q_j`.

## 2. Formal statements

### 2.1 Main results

```lean
/-- **Lemma 6 (plane).** -/
theorem lemma6_plane {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ (ψ : ℂ → ℝ) (ν₀ : Measure ℂ) (g : ℂ → ℝ≥0∞) (ε K M : ℝ), 0 < ε ∧ Measurable g ∧
      IsSubharmonicWeight univ ψ (ν₀ + volume.withDensity g) ∧
      IsLocallyDoubling (ν₀ + volume.withDensity g) ∧
      (∀ z, |ψ z - φ z| ≤ M) ∧
      (∀ z, ENNReal.ofReal ε ≤ g z ∧ g z ≤ ENNReal.ofReal K) ∧
      ν₀ ≤ μ ∧ μ ≤ (2 : ℝ≥0∞) • ν₀

/-- **Lemma 6 (disc).** -/
theorem lemma6_disc {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ (ψ : ℂ → ℝ) (ν₀ : Measure ℂ) (g : ℂ → ℝ≥0∞) (ε K M : ℝ), 0 < ε ∧ Measurable g ∧
      IsSubharmonicWeight 𝔻 ψ (ν₀ + volume.withDensity g) ∧
      IsLocallyDoublingDisc (ν₀ + volume.withDensity g) ∧
      (∀ z ∈ 𝔻, |ψ z - φ z| ≤ M) ∧
      (∀ z ∈ 𝔻, ENNReal.ofReal (ε / (1 - ‖z‖ ^ 2) ^ 2) ≤ g z ∧
        g z ≤ ENNReal.ofReal (K / (1 - ‖z‖ ^ 2) ^ 2)) ∧
      (∀ z ∉ 𝔻, g z = 0) ∧
      ν₀ ≤ μ ∧ μ ≤ (2 : ℝ≥0∞) • ν₀
```

**Choices.**
- **Mass hypothesis.** It is `1 ≤ μ(B(z,R))`. This is weaker than the paper's `> 1` and than the `1 < …` of `theorem2`/`theorem4_*`, and equal to the `1 ≤ …` of `theorem1`.
- **Shape of the new Laplacian.** It is exposed as `ν₀ + volume.withDensity g`, an "old part" plus an absolutely continuous part. This is exactly what M11/M12 need in order to subtract `c log(1/(1−|z|²))` or `c|z|²` with M02 `IsSubharmonicWeight.sub_contDiffOn`.
- **Extra conclusions** for downstream use:
  - `ν₀ ≤ μ ≤ 2ν₀`;
  - the upper bound `g ≤ K` (resp. `K/(1−|z|²)²`);
  - `g = 0` off `𝔻`.
- **`ψ` need not be `C²`.** It is only continuous, which `IsSubharmonicWeight` requires anyway. No smoothness is claimed.

### 2.2 Definitions and auxiliary lemmas (exported)

```lean
/-- The weight `w(ζ) = 1/(2 μ(B(ζ,R)))` (plane). -/
def massWeight (μ : Measure ℂ) (R : ℝ) (ζ : ℂ) : ℝ≥0∞ := (2 * μ (ball ζ R))⁻¹
/-- The weight `w(ζ) = 1/(2 μ(D(ζ,R)))` (disc, hyperbolic balls). -/
def massWeightDisc (μ : Measure ℂ) (R : ℝ) (ζ : ℂ) : ℝ≥0∞ := (2 * μ (hypBall ζ R))⁻¹
/-- Smoothing radius in the disc: `s(ζ) = (1 − |ζ|²)/4`. -/
def discRadius (ζ : ℂ) : ℝ := (1 - ‖ζ‖ ^ 2) / 4

-- (reconciled) `logSmall_plane`, `logSmall_disc` are stated in M03 (`Doubling/Export.lean`),
-- unchanged, so that M08 can use them without importing M04.
theorem logSmall_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ K : Set ℂ, IsCompact K → μ K < ∞) {K : Set ℂ} (hK : IsCompact K) {η : ℝ}
    (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
      ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂μ ≤ ENNReal.ofReal η
theorem logSmall_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ K ⊆ 𝔻, IsCompact K → μ K < ∞) {K : Set ℂ} (hK𝔻 : K ⊆ 𝔻) (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ K,
      ∫⁻ ζ in ball z δ, ENNReal.ofReal (1 + Real.log (1 / ‖z - ζ‖)) ∂μ ≤ ENNReal.ofReal η

theorem measurable_massWeight {μ : Measure ℂ} [SFinite μ] (R : ℝ) :
    Measurable (massWeight μ R)
theorem measurable_massWeightDisc {μ : Measure ℂ} [SFinite μ] (R : ℝ) :
    Measurable (massWeightDisc μ R)

theorem isLocalPotData_plane {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    IsLocalPotData univ (μ.withDensity (massWeight μ R)) (fun _ ↦ R)
theorem isLocalPotData_disc {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    IsLocalPotData 𝔻 (μ.withDensity (massWeightDisc μ R)) discRadius

theorem smoothedDensity_plane_bounds {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoubling μ) {R : ℝ} (hR : 0 < R)
    (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ ε K : ℝ, 0 < ε ∧ ∀ x : ℂ,
      ENNReal.ofReal ε ≤ smoothedDensity (μ.withDensity (massWeight μ R)) (fun _ ↦ R) x ∧
      smoothedDensity (μ.withDensity (massWeight μ R)) (fun _ ↦ R) x ≤ ENNReal.ofReal K
theorem smoothedDensity_disc_bounds {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight 𝔻 φ μ) (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R)
    (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ ε K : ℝ, 0 < ε ∧ ∀ x ∈ 𝔻,
      ENNReal.ofReal (ε / (1 - ‖x‖ ^ 2) ^ 2) ≤
        smoothedDensity (μ.withDensity (massWeightDisc μ R)) discRadius x ∧
      smoothedDensity (μ.withDensity (massWeightDisc μ R)) discRadius x ≤
        ENNReal.ofReal (K / (1 - ‖x‖ ^ 2) ^ 2)

theorem localPot_plane_le {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z : ℂ, 1 ≤ μ (ball z R)) :
    ∃ M : ℝ, ∀ z : ℂ, localPot (μ.withDensity (massWeight μ R)) (fun _ ↦ R) z ≤ M
theorem localPot_disc_le {φ : ℂ → ℝ} {μ : Measure ℂ} (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) {R : ℝ} (hR : 0 < R) (hm : ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) :
    ∃ M : ℝ, ∀ z ∈ 𝔻, localPot (μ.withDensity (massWeightDisc μ R)) discRadius z ≤ M
```

**Junk values.**
- **`massWeight`.** It is `ℝ≥0∞`-valued. With `1 ≤ μ(B(ζ,R)) < ∞` it lies in `(0, 1/2]`.
- **`massWeightDisc` off `𝔻`.** Its values there are arbitrary (possibly `∞`). They are irrelevant, because `μ 𝔻ᶜ = 0` and all uses are `μ`-a.e.
- **`discRadius` off `𝔻`.** It is `≤ 0` there; `IsLocalPotData` only requires positivity on `Ω`.

### 2.3 Assumed from M03 (to be reconciled with `M03_Doubling.md`)

```lean
-- (reconciled) M04 uses M03's statements (`Doubling/Export.lean`):
--   (A1) `doubling_upTo_plane`, `doubling_upTo_disc` (identical shape);
--   (A2) `christ_lemma23_plane`, `christ_lemma23_disc` (`dist z ζ` for `‖z - ζ‖`);
--   (A3) `rpow_le_measure_ball_plane`, `rpow_le_measure_hypBall` (reverse doubling, with
--        `ENNReal.ofReal (c * (r / r') ^ δ) * μ (ball z r') ≤ μ (ball z r)`);
--   (A4) `measure_singleton_plane`, `measure_singleton_disc` (finiteness on balls).
-- The stubs below are kept only to document the original request.
/-- (A1) doubling up to any fixed scale. -/
theorem IsLocallyDoubling.exists_doubling_le {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (R₁ : ℝ) : ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ R₁ →
      μ (ball z (2 * r)) ≤ C * μ (ball z r)
/-- (A2) [Chr91, Lemma 2.3]. -/
theorem IsLocallyDoubling.exists_lintegral_log_le {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (R₁ : ℝ) : ∃ C : ℝ≥0, ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ R₁ →
      ∫⁻ ζ in ball z r, ENNReal.ofReal (Real.log (r / ‖z - ζ‖)) ∂μ ≤ C * μ (ball z r)
/-- (A3) Lemma 1, reverse doubling. -/
theorem IsLocallyDoubling.exists_reverse_doubling {μ : Measure ℂ} (hd : IsLocallyDoubling μ) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ≥0, ∀ z : ℂ, ∀ s r : ℝ, 0 < s → s ≤ r → r < 1 →
      μ (ball z s) ≤ C * ENNReal.ofReal ((s / r) ^ γ) * μ (ball z r)
/-- (A4) no atoms. -/
theorem IsLocallyDoubling.measure_singleton {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ K : Set ℂ, IsCompact K → μ K < ∞) (z : ℂ) : μ {z} = 0
```

The disc versions `IsLocallyDoublingDisc.exists_doubling_le`, `.exists_lintegral_log_le` (integrand `log(r / hypDist z ζ)`), `.exists_reverse_doubling`, `.measure_singleton` are the same statements with `hypBall` and `z ∈ 𝔻` (see the check file). Notes:
- **(A2) is weaker than the true lemma.** At `ζ = z` the integrand is the junk `log(r/0) = 0`.
- **(A1) for `r ≥ 1/2`** follows from local doubling by a chaining/covering argument; the constant grows exponentially in `R₁`.
- **(A3) and (A4)** are the paper's Lemma 1 (right inequality) and "no atoms" (p. 360).

### 2.4 Assumed from M01 (hyperbolic geometry; BOC names in brackets)

Here `pB(a, t) := {w ∈ 𝔻 | pseudoHyp a w < t}`.
- **(G0)** `hypBall_eq`: for `z ∈ 𝔻` and `r > 0`, `hypBall z r = pB(z, tanh r)`.
- **(G1)** `ball(a, t(1−|a|²)/2) ⊆ pB(a, t)` for `a ∈ 𝔻`, `0 < t < 1` [`ball_subset_pseudoBall`].
- **(G2)** `pB(a, t) ⊆ ball(a, t(1−|a|²)/(1−t))` [`pseudoBall_subset_ball`].
- **(G3)** `w ∈ pB(a, t) ⇒ ((1−t)/(1+t))(1−|a|²) ≤ 1−|w|² ≤ ((1+t)/(1−t))(1−|a|²)` [`one_sub_normSq_comparable`].
- **(G4)** `pseudoHyp` is symmetric [`pseudoHyp_comm`].
- **(G5)** `hypDist_triangle` on `𝔻`, and `hypDist 0 w = artanh ‖w‖`.
- **(G6)** `‖1 − z̄ζ‖ ≥ 1 − ‖z‖‖ζ‖` [`one_sub_mul_le_norm_one_sub_conj_mul`].

**Elementary helper (M04-local).** `t ↦ artanh(t)/t = Σ_k t^{2k}/(2k+1)` is increasing on `(0,1)`. So for `0 < ρ ≤ tanh r`: `tanh r / ρ ≤ r / artanh ρ`.

## 3. The construction (both settings)

Let `(φ, μ)` satisfy the hypotheses, with `R > 0` the mass radius. Write `B(ζ, r)` for `ball ζ r` (plane) or `hypBall ζ r` (disc).
1. **Weight.**
   - `w(ζ) := (2 μ(B(ζ,R)))⁻¹`, i.e. `massWeight`/`massWeightDisc`.
   - On `Ω`, `1 ≤ μ(B(ζ,R)) < ∞`, so `0 < w ≤ 1/2`. Finiteness holds because the closure of `B(ζ,R)` is a compact subset of `Ω` (disc: (G5), `closedBall 0 (tanh(artanh|ζ| + R))`) and `finite_of_compact`.
   - **Measurable.** `ζ ↦ μ(B(ζ,R))` is measurable by `measurable_measure_prodMk_left` (needs `SFinite μ`, from `IsSubharmonicWeight.sigmaFinite`). It is applied to the measurable set `{(ζ,x) | dist ζ x < R}`, resp. `{(ζ,x) | x ∈ 𝔻 ∧ hypDist ζ x < R}`. Then compose with `x ↦ (2x)⁻¹` (`Measurable.inv`, `ENNReal.continuous_inv`).
2. **Split.** `μ₁ := μ.withDensity w`, `μ₂ := ν₀ := μ.withDensity (1 − w)`.
   - Since `w ≤ 1/2` `μ`-a.e. (on `Ω`; `μ Ωᶜ = 0`): `μ₁ + μ₂ = μ` (`withDensity_add_left`, `withDensity_one`, `withDensity_congr_ae`), and `μ/2 ≤ μ₂ ≤ μ` (`withDensity_mono` with `1/2 ≤ 1 − w ≤ 1`).
   - This replaces the paper's tiles. `μ₁` has "mass `≍ 1` per ball of radius `≍ R`", which is all the proof uses. This is checked in §4 and §5.
3. **Smoothing radius.** `s ≡ R` (plane), `s := discRadius` (disc).
4. **Smoothed measure.** `g := smoothedDensity μ₁ s`, `μ̃₁ := volume.withDensity g`.
5. **New weight.** `V := localPot μ₁ s` and `ψ := φ + V`, `ν := ν₀ + volume.withDensity g`.

**Comparison with the paper.** `ψ − φ = V` plays the role of `K[μ̃₁] − K[μ₁]`. The tiling `μ₁|_{Q_j} = μ/μ(Q_j)` becomes the continuous normalisation `μ₁ = μ/(2μ(B(ζ,R)))`.
- **Tiles are not needed.** In the disc the paper's "dyadic squares" are never specified. Polar dyadic boxes would need a separate argument for the central region and for "two disjoint `R₀`-balls per tile" (for `μ(Q_j) > 2`).
- **Mass hypothesis.** With the factor `1/2` in `w`, one only needs `μ(B(ζ,R)) ≥ 1` to get `μ₂ ≥ μ/2`.
- **`μ₁` locally doubling.** The paper claims it, and it is true, but it is never used: §4.4 only uses the doubling of `μ`.

## 4. Proofs in the plane

Fix:
- `C ≥ 1` from (A1) with `R₁ = R`, so `μ(B(z,2r)) ≤ C μ(B(z,r))` for `r ≤ R`;
- `C_d` from `hd` (local doubling);
- `C_L` from (A2) with `R₁ = R`;
- `C₀` from M02 `exists_localPot_le`.

### 4.1 `isLocalPotData_plane` (σ = μ₁, s ≡ R, Ω = univ)

- `isOpen`, `measurable` (constant), `pos`, `bdd` (`S = R`), `ball_subset`: trivial.
- `carried`: `univᶜ = ∅`.
- `sFinite`: `μ` is σ-finite (M02), hence so is `μ.withDensity w` (instance `SFinite (μ.withDensity f)`).
- `noAtoms`: `μ₁{z} ≤ μ{z} = 0`, by (A4) with `hfin` from `hφ.finite_of_compact`.
- `locFin`: `{ζ | ∃ z ∈ K, dist z ζ < R} ⊆ cthickening R K`, which is compact (`IsCompact.cthickening`). So `μ₁(·) ≤ μ(·) < ∞`.
- `logSmall`: `logSmall_plane` for `μ` (§6), and `μ₁ ≤ μ` (`withDensity` with `w ≤ 1`): `setLIntegral_mono_measure`-type monotonicity in the measure.

### 4.2 `smoothedDensity_plane_bounds`

By `lintegral_withDensity_eq_lintegral_mul`, `g(x) = ∫⁻ ofReal(k_R(x − ζ)) w(ζ) dμ(ζ)`.

**Lower bound.** Restrict to `ζ ∈ B(x, R/2)`.
- There `k_R(x − ζ) ≥ 1/(πR²)` (`le_bumpKernel`, `‖x − ζ‖ < R/2`).
- Also `B(ζ,R) ⊆ B(x, 3R/2) ⊆ B(x, 2R)`, so `μ(B(ζ,R)) ≤ μ(B(x,2R)) ≤ C² μ(B(x,R/2))`, by (A1) at radii `R/2` and `R`, both `≤ R`.
- Hence `w(ζ) ≥ (2C² μ(B(x,R/2)))⁻¹`.
- So `g(x) ≥ (πR²)⁻¹ μ(B(x,R/2)) (2C² μ(B(x,R/2)))⁻¹ = (2πR²C²)⁻¹ =: ε`.
- **Side conditions in `ℝ≥0∞`.**
  - `μ(B(x,R/2)) < ∞`: bounded set.
  - `μ(B(x,R/2)) > 0`: `1 ≤ μ(B(x,R)) ≤ C μ(B(x,R/2))`.
  - Then `ENNReal.mul_inv_cancel` applies.

**Upper bound.**
- `k_R(x − ζ) ≤ 4/(πR²)` for `ζ ∈ B(x,R)`, and `0` otherwise (`bumpKernel_le`).
- For `ζ ∈ B(x,R)`: `B(x,R) ⊆ B(ζ,2R)`, so `μ(B(x,R)) ≤ C μ(B(ζ,R))`, i.e. `w(ζ) ≤ C (2μ(B(x,R)))⁻¹`.
- Hence `g(x) ≤ 4/(πR²) · μ(B(x,R)) · C (2μ(B(x,R)))⁻¹ = 2C/(πR²) =: K`.

### 4.3 `localPot_plane_le`

By `exists_localPot_le` and `lintegral_withDensity_eq_lintegral_mul`:

`ofReal V(z) ≤ ∫⁻_{B(z,R)} ofReal((4π)⁻¹(2 log(R/‖z−ζ‖) + C₀)) w(ζ) dμ(ζ)`.

The rewrite `log(R²/‖z−ζ‖²) = 2 log(R/‖z−ζ‖)` holds for `ζ ≠ z` (`Real.log_pow`, `div_pow`); the point `ζ = z` is `μ`-null.
- **Bound `w`.** On `B(z,R)`, `w(ζ) ≤ C(2μ(B(z,R)))⁻¹`, as in 4.2.
- **Split the integrand.** `ofReal(a + b) ≤ ofReal a + ofReal b`. Then:
  - `∫⁻_{B(z,R)} ofReal(log(R/‖z−ζ‖)) dμ ≤ C_L μ(B(z,R))` by (A2);
  - `∫⁻_{B(z,R)} ofReal(C₀) dμ = C₀ μ(B(z,R))`.
- So `ofReal V(z) ≤ (4π)⁻¹ C (2μ(B(z,R)))⁻¹ (2C_L + C₀) μ(B(z,R)) = C(2C_L + C₀)/(8π) =: M`.
- Since `V(z) ≥ 0` (M02 `localPot_nonneg`), `V(z) ≤ M` (`ENNReal.ofReal_le_ofReal_iff`).

### 4.4 `lemma6_plane`

Take:
- `R` from `hm`;
- `ψ := φ + V`, `ν₀ := μ₂`, `g := smoothedDensity μ₁ (fun _ ↦ R)`;
- `ε, K` from 4.2 and `M` from 4.3.

Let `h := isLocalPotData_plane …`.
- **`Measurable g`:** `h.measurable_smoothedDensity`.
- **`|ψ − φ| = V ≤ M`:** `0 ≤ V` (`h.localPot_nonneg`).
- **Bounds on `g`:** 4.2.
- **`ν₀ ≤ μ ≤ 2ν₀`:** §3 item 2. For the second, `2 • μ.withDensity(1−w) = μ.withDensity(2(1−w)) ≥ μ.withDensity 1 = μ`.
- **`IsSubharmonicWeight univ ψ ν`:**
  - `continuousOn`: `hφ.continuousOn.add h.continuousOn_localPot`.
  - `finite_of_compact`: `ν₀ K ≤ μ K < ∞`, and `∫⁻_K g < ∞` (`h.lintegral_smoothedDensity_lt_top`).
  - `carried`: `univᶜ = ∅`.
  - `laplacian_eq`. For a test `χ`:
    `∫ ψΔχ = ∫ φΔχ + ∫ VΔχ`. Both products are integrable (M02 `integrable_mul`, applied to `φ` and to `V`; `V` is continuous). Then
    `∫ φΔχ + ∫ VΔχ = ∫χ dμ + (∫χ d(vol.withDensity g) − ∫χ dμ₁)` (`hφ.laplacian_eq`, `h.integral_localPot_mul_laplacian`).
    With `∫χ dμ = ∫χ dμ₁ + ∫χ dμ₂` (`μ = μ₁ + μ₂`, `integral_add_measure`), this equals `∫χ dμ₂ + ∫χ d(vol.withDensity g) = ∫χ dν`.
    Integrability of `χ` for each measure: bounded, compact support, and finite measure on `tsupport χ`.
- **`IsLocallyDoubling ν`** with constant `max(2C_d, 4K/ε)`. Let `0 < r`, `2r < 1`.
  - `ν₀(B(z,2r)) ≤ μ(B(z,2r)) ≤ C_d μ(B(z,r)) ≤ 2C_d ν₀(B(z,r))`.
  - `μ̃₁(B(z,2r)) ≤ K · vol(B(z,2r)) = 4πKr²`, and `μ̃₁(B(z,r)) ≥ ε πr²` (`volume_ball_complex`, `setLIntegral_mono`, `setLIntegral_const`). So `μ̃₁(B(z,2r)) ≤ (4K/ε) μ̃₁(B(z,r))`.
  - Add the two inequalities. ∎

## 5. Proofs in the disc

Write `pB(a,t)` as in (G1–G3), `r₁ := artanh(1/9)` and `r₂ := artanh(1/2)`, so that `hypBall a r₁ = pB(a, 1/9)` and `hypBall a r₂ = pB(a, 1/2)` (G0). Let `s(ζ) = (1−|ζ|²)/4`.

**Geometric facts used repeatedly** (`a, ζ, x ∈ 𝔻`):
- **(D1)** `ball(ζ, s(ζ)) ⊆ pB(ζ, 1/2) ⊆ 𝔻`. This is (G1) with `t = 1/2`.
- **(D2)** `pB(ζ, 1/9) ⊆ ball(ζ, s(ζ)/2)`. By (G2) with `t = 1/9`: radius `(1/9)(1−|ζ|²)/(8/9) = (1−|ζ|²)/8`.
- **(D3)** If `‖x − ζ‖ < s(ζ)`, then:
  - `ρ(x,ζ) < 1/2`, by (D1) and (G4), i.e. `ζ ∈ hypBall x r₂`;
  - `1 − |ζ|² ≥ (1/3)(1 − |x|²)`, by (G3) with `t = 1/2`;
  - hence `s(ζ) ≥ (1−|x|²)/12`.
- **(D4)** If `ζ ∈ hypBall x r₁`, then:
  - `‖x − ζ‖ < s(ζ)/2`, by (D2) and (G4);
  - `1 − |ζ|² ≤ (5/4)(1 − |x|²)`, by (G3) with `t = 1/9`;
  - hence `s(ζ) ≤ (5/16)(1−|x|²)`.
- **(D5)** Compactness. If `|z| ≤ ρ_K < 1` and `ζ ∈ hypBall z r`, then `|ζ| ≤ tanh(artanh ρ_K + r) < 1`, by (G5). So `⋃_{z ∈ K} hypBall z r` has compact closure in `𝔻`.

**Constants.** Let `C_d` be from `hd`.
- `D₁ := C^{m₁}`, with `C` from (A1') at `R₁ = R + r₁`, and `m₁` minimal with `2^{m₁} r₁ ≥ R + r₁`. Then `μ(hypBall x (R + r₁)) ≤ D₁ μ(hypBall x r₁)`.
- `D₂ := C'^{m₂}`, with `C'` from (A1') at `R₁ = max(R, 2r₂)`, and `m₂` minimal with `2^{m₂} R ≥ 2r₂` (`m₂ = 0` if `2r₂ ≤ R`). Then `μ(hypBall ζ (2r₂)) ≤ D₂ μ(hypBall ζ R)`.
- `C_L` from (A2') at `R₁ = r₂`, and `C₀` from M02.

### 5.1 `isLocalPotData_disc` (σ = μ₁, s = discRadius, Ω = 𝔻)

- `isOpen`: `isOpen_ball`.
- `measurable`: continuous.
- `pos`: `‖ζ‖ < 1`.
- `bdd`: `S = 1/4`.
- `ball_subset`: (D1).
- `carried`: `μ₁ 𝔻ᶜ ≤ …`; `withDensity` of a `μ`-null set is `0` (`withDensity_absolutelyContinuous`).
- `sFinite`: as in the plane.
- `noAtoms`:
  - `z ∈ 𝔻`: (A4') with `μ₁ ≤ μ` on `𝔻`, a.e.
  - `z ∉ 𝔻`: `μ₁{z} ≤ μ₁ 𝔻ᶜ = 0`.
- `locFin`. The set `{ζ | ∃ z ∈ K, dist z ζ < s ζ}`:
  - contains no `ζ ∉ 𝔻`, since there `s ζ ≤ 0`;
  - for `ζ ∈ 𝔻` it is contained in `⋃_{z∈K} hypBall z r₂`, by (D3) and (G4).

  By (D5) this has compact closure in `𝔻`, so it has finite `μ`- and hence `μ₁`-measure.
- `logSmall`: `logSmall_disc` (§6), and `μ₁ ≤ μ` a.e.

### 5.2 `smoothedDensity_disc_bounds`

For `x ∈ 𝔻`: `g(x) = ∫⁻ ofReal(k_{s(ζ)}(x − ζ)) w(ζ) dμ(ζ)`, and only `ζ ∈ 𝔻` matter.

**Lower bound.** Restrict to `ζ ∈ hypBall x r₁`.
- **Kernel.** By (D4), `k_{s(ζ)}(x − ζ) ≥ 1/(π s(ζ)²) ≥ 256/(25π(1−|x|²)²)` (`le_bumpKernel`).
- **Weight.**
  - By (G5), `hypBall ζ R ⊆ hypBall x (R + r₁)`.
  - So `w(ζ) ≥ (2μ(hypBall x (R+r₁)))⁻¹ ≥ (2D₁ μ(hypBall x r₁))⁻¹`.
- **Combine.**
  `g(x) ≥ 256/(25π(1−|x|²)²) · μ(hypBall x r₁) · (2D₁ μ(hypBall x r₁))⁻¹ = (128/(25πD₁)) / (1−|x|²)²`.
- **Side conditions.**
  - `μ(hypBall x r₁) < ∞`: (D5), compact closure in `𝔻`.
  - `μ(hypBall x r₁) > 0`: `1 ≤ μ(hypBall x R) ≤ μ(hypBall x (R+r₁)) ≤ D₁ μ(hypBall x r₁)`.
- Set `ε := 128/(25πD₁)`.

**Upper bound.**
- **Kernel.** `k_{s(ζ)}(x − ζ) ≤ 4/(πs(ζ)²) · 1_{‖x−ζ‖ < s(ζ)}` (`bumpKernel_le`). On that set, (D3) gives `ζ ∈ hypBall x r₂` and `4/(πs(ζ)²) ≤ 576/(π(1−|x|²)²)`.
- **Weight.** For `ζ ∈ hypBall x r₂`:
  - by (G5), `hypBall x r₂ ⊆ hypBall ζ (2r₂)`;
  - so `μ(hypBall x r₂) ≤ D₂ μ(hypBall ζ R)`, i.e. `w(ζ) ≤ D₂ (2μ(hypBall x r₂))⁻¹`.
- **Combine.** `g(x) ≤ 576/(π(1−|x|²)²) · μ(hypBall x r₂) · D₂(2μ(hypBall x r₂))⁻¹ = (288D₂/π)/(1−|x|²)²`. If `μ(hypBall x r₂) = 0`, the integral is `0`; in fact it is positive.
- Set `K := 288D₂/π`.

### 5.3 `localPot_disc_le`

Let `z ∈ 𝔻`. By `exists_localPot_le`, the integration set is `{ζ ∈ 𝔻 : ‖z − ζ‖ < s(ζ)} ⊆ hypBall z r₂` (D3). On it, for `ζ ≠ z`:
- **Rewrite `s(ζ)/‖z−ζ‖`.** `‖z − ζ‖ = ρ(z,ζ) ‖1 − z̄ζ‖`. Also `1 − |ζ|² ≤ 2(1 − |ζ|) ≤ 2‖1 − z̄ζ‖` (G6, since `|z| < 1`). Hence
  `s(ζ)/‖z−ζ‖ ≤ 1/(2ρ(z,ζ)) = tanh r₂ / ρ(z,ζ) ≤ r₂ / hypDist z ζ`.
  The last step is the artanh helper with `ρ < 1/2 = tanh r₂`.
- So `log(s(ζ)²/‖z−ζ‖²) ≤ 2 log(r₂ / hypDist z ζ)`, where `r₂/β > 1`.
- **Bound `w` on `hypBall z r₂`.** `w ≤ D₂(2μ(hypBall z r₂))⁻¹`, exactly as in 5.2.
- **Combine** with (A2') at radius `r₂`:
  `ofReal V(z) ≤ (4π)⁻¹ D₂ (2μ(hypBall z r₂))⁻¹ (2C_L + C₀) μ(hypBall z r₂) = D₂(2C_L + C₀)/(8π) =: M`.

### 5.4 `lemma6_disc`

The assembly is identical to 4.4, with `Ω = 𝔻`. Additional points:
- **`carried`.** `ν₀ 𝔻ᶜ ≤ μ 𝔻ᶜ = 0`, and `∫⁻_{𝔻ᶜ} g = 0` because `g = 0` off `𝔻` (`h.smoothedDensity_eq_zero`). The latter also gives the conclusion `∀ z ∉ 𝔻, g z = 0`.
- **`finite_of_compact`.** For `K ⊆ 𝔻` compact: `∫⁻_K g < ∞` (`h.lintegral_smoothedDensity_lt_top`).
- **`IsLocallyDoublingDisc ν`.** Let `z ∈ 𝔻`, `0 < r`, `2r < 1`, `t₁ := tanh r < 1/2` and `t₂ := tanh 2r`. Then `t₂ ≤ 2t₁` (`tanh 2r = 2t₁/(1+t₁²)`) and `t₂ < tanh 1 < 4/5`.
  - **`ν₀` part:** `ν₀(hypBall z 2r) ≤ 2C_d ν₀(hypBall z r)`, as in the plane.
  - **Upper bound on `μ̃₁(hypBall z 2r)`.** On `hypBall z (2r) = pB(z,t₂)`, (G3) gives `1−|x|² ≥ ((1−t₂)/(1+t₂))(1−|z|²)`, and (G2) gives `pB(z,t₂) ⊆ ball(z, t₂(1−|z|²)/(1−t₂))`. Hence
    `μ̃₁(hypBall z 2r) ≤ K (1+t₂)²/((1−t₂)²(1−|z|²)²) · π t₂²(1−|z|²)²/(1−t₂)² ≤ 8100 π K t₁²`.
  - **Lower bound on `μ̃₁(hypBall z r)`.** By (G1), `hypBall z r ⊇ ball(z, t₁(1−|z|²)/2)`. On that ball, (G3) gives `1−|x|² ≤ 3(1−|z|²)`. Hence
    `μ̃₁(hypBall z r) ≥ ε/(9(1−|z|²)²) · π t₁²(1−|z|²)²/4 = επ t₁²/36`.
  - **Ratio** `≤ 291600 K/ε`. The constant of `ν` is `max(2C_d, 291600 K/ε)`. ∎

## 6. `logSmall_plane`, `logSmall_disc`

**Plane.** Let `K` be compact and `η > 0`. Take:
- `C_L` from (A2) with `R₁ = 1`;
- `γ, C_r` from (A3);
- `M_K := μ(cthickening 1 K) < ∞`.

For `z ∈ K`, `0 < δ ≤ 1/2`, and a.e. `ζ ∈ B(z,δ)` (`ζ ≠ z` by (A4)), all terms below are `≥ 0`:

`1 + log(1/‖z−ζ‖) = (1 + log(1/δ)) + log(δ/‖z−ζ‖)`.

Splitting `ofReal` (`ENNReal.ofReal_add`), then (A2) and (A3) with `s = δ`, `r = 1/2`:
`∫⁻_{B(z,δ)} … ≤ (1 + log(1/δ) + C_L) μ(B(z,δ)) ≤ (1 + log(1/δ) + C_L) C_r (2δ)^γ M_K`.

The right side `→ 0` as `δ → 0⁺` (`Real.tendsto_log_mul_rpow_nhds_zero`). Choose `δ` with right side `≤ η`.

**Disc.** Let `K ⊆ 𝔻` be compact, `ρ_K := max_K ‖·‖ < 1`, and `η > 0`. Take:
- `C_L` from (A2') at `R₁ = 1/2`;
- `γ, C_r` from (A3');
- `M_K := μ(closure ⋃_{z∈K} hypBall z (1/2)) < ∞` (D5).

For `0 < δ ≤ tanh(1/2)(1 − ρ_K²)/2`, put `τ := artanh(2δ/(1−ρ_K²)) ≤ 1/2`. Then, for `z ∈ K`:
- `ball z δ ⊆ ball(z, (2δ/(1−ρ_K²))(1−|z|²)/2) ⊆ hypBall z τ`, by (G1) and (G0).
- For `ζ ∈ ball z δ`, `ζ ≠ z`:
  - `‖z − ζ‖ = ρ(z,ζ)‖1 − z̄ζ‖ ≥ ρ(z,ζ)(1−ρ_K)` (G6);
  - `ρ ≥ (3/4) artanh ρ` for `ρ ≤ 1/2`;
  - hence `1 + log(1/‖z−ζ‖) ≤ c_K + log(1/τ) + log(τ / hypDist z ζ)`, with `c_K := 1 + log(1/(1−ρ_K)) + log(4/3)`, and every term `≥ 0`.
- As in the plane:
  `∫⁻_{ball z δ} … ≤ (c_K + log(1/τ) + C_L) μ(hypBall z τ) ≤ (c_K + log(1/τ) + C_L) C_r (2τ)^γ M_K → 0`. ∎

## 7. Where Lemma 6 and the lower bound `ν ≥ ε dm` are used

- **Theorem 2 (M11), p. 372.**
  - "We take an arbitrary weight `φ` under the hypothesis of Theorem 2, that is `(1−|z|²)²Δφ > ε`": this is `lemma6_disc` applied to `φ`.
  - The auxiliary weight is `ψ' := ψ + c log(1 − |z|²)`. The printed `ψ = φ − (ε/2) log(1−|z|²)` has the wrong sign (README §4).
  - With the standard Laplacian, `Δ(−c log(1−|z|²)) = 4c/(1−|z|²)²`. M02 `IsSubharmonicWeight.sub_contDiffOn` with `u = −c log(1−|z|²)` and `c := ε/8` gives `Δψ' = ν₀ + (g − 4c(1−|z|²)^{-2}) dm`, where `g − 4c(1−|z|²)^{-2} ≥ g/2`.
  - **This is the only place where the lower bound on `g` is used.** It guarantees that `Δψ'` is still a positive measure, comparable to `ν`, hence locally doubling.
  - `|ψ − φ| ≤ M` transfers the estimates back to `φ` at the cost of a factor `e^{M}` (`p`-independent).
  - **Needed from M03 (flag).** The mass condition for `Δψ' ≥ ν/2 ≥ μ/4` requires `μ(hypBall z r') > 4` for some `r'`, i.e. the "growth of `μ(B(z,R))`" lemma.
- **Theorem 1 and Proposition 1 (M12), p. 374.** `ψ' := ψ − c|z|²`, `Δ(c|z|²) = 4c`, `c := ε/8`. Same mechanism, using `lemma6_plane`.
- **Not used:**
  - Theorem 4 and Proposition 2 (multipliers): they work directly with `φ` and only need local doubling and the mass condition;
  - Theorems 3 and 5: the weight there is degenerate, `μ` is carried by `ℝ`, so Lemma 6 does not even apply.

## 8. Interface

**Consumes:**
- M02: §4 local potentials, §3 `integrable_mul`, `sigmaFinite`.
- M03: (A1)–(A4) and (A1')–(A4') as stated in §2.3.
- M01: (G0)–(G6).

**Exports:**
- `lemma6_plane` (to M12), `lemma6_disc` (to M11).
- `logSmall_plane`, `logSmall_disc`: generic facts about locally doubling measures, possibly useful to M07/M08 (continuity of potentials).

### 8a. Interface (reconciled)

Lean file `Regularization.lean`. Definitions and statements of §2.1–§2.2 are unchanged, except that `logSmall_*` moved to M03. The doc's assumptions map to upstream names:
- **M03.** (A1)–(A4) map to M03 names (see the comment in the §2.3 block).
- **M01.**
  - (G0) is `hypBall_eq_pseudoBall` (no `0 < r` needed).
  - (G1)–(G3) are `ball_subset_pseudoBall`, `pseudoBall_subset_ball`, `one_sub_normSq_comparable`.
  - (G5) is `hypDist_triangle` and `hypDist_zero_left`.
  - `hypArea` is M01's (`Foundations/HyperbolicExtra.lean`).

**Added** for M11/M12 and for `theorem2_uniform`:
- the two corollaries in the shape that M11 §2.1 and M12 §2.1 assumed (they assumed the name `lemma6_*` for a different statement);
- a uniform Lemma 6 in the disc (constants after `(Cd, R)`, before the measure);
- `Measure.exists_add_eq_of_le`, moved from M11 so that M12 need not import M11.

```lean
/-- Lemma 6 (disc) in the form M11 consumes: `μ' ≥ ε · hypArea` and `|φ − φ'| ≤ B`.  Follows
from `lemma6_disc` (`μ' = ν₀ + volume.withDensity g`, `g ≥ ε/(1-|z|²)²` on `𝔻`; `1 < ·`
implies the hypothesis `1 ≤ ·` of `lemma6_disc`). -/
theorem lemma6_disc_hypArea (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ) (ε B : ℝ), 0 < ε ∧ IsSubharmonicWeight 𝔻 φ' μ' ∧
      IsLocallyDoublingDisc μ' ∧ ENNReal.ofReal ε • hypArea ≤ μ' ∧
      ∀ z ∈ 𝔻, |φ z - φ' z| ≤ B
/-- Lemma 6 (plane) in the form M12 consumes: `μ' ≥ ε · dm` and `|φ − φ'| ≤ B`.  Follows from
`lemma6_plane`. -/
theorem lemma6_plane_volume (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 < μ (ball z r)) :
    ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ) (ε B : ℝ), 0 < ε ∧ IsSubharmonicWeight univ φ' μ' ∧
      IsLocallyDoubling μ' ∧ ENNReal.ofReal ε • volume ≤ μ' ∧ ∀ z, |φ z - φ' z| ≤ B
/-- **Lemma 6 (disc), uniform form** (requested for `theorem2_uniform`): the constants `ε`, `B`
and the class `(Cd', R')` of the regularized measure depend only on the class `(Cd, R)` of `μ`,
not on the weight.  (The construction of `lemma6_disc` is uniform: the bounds come from
[Chr91, Lemma 2.3] and doubling at bounded scales, `christ_disc_quant`, `doubling_upTo_disc`.) -/
theorem lemma6_disc_quant (Cd : ℝ≥0) (R : ℝ) (hR : 0 < R) :
    ∃ (ε B : ℝ) (Cd' : ℝ≥0) (R' : ℝ), 0 < ε ∧ 0 ≤ B ∧ 0 < R' ∧
      ∀ (φ : ℂ → ℝ) (μ : Measure ℂ), IsSubharmonicWeight 𝔻 φ μ → MeasClassDisc μ Cd R →
        ∃ (φ' : ℂ → ℝ) (μ' : Measure ℂ), IsSubharmonicWeight 𝔻 φ' μ' ∧
          MeasClassDisc μ' Cd' R' ∧ ENNReal.ofReal ε • hypArea ≤ μ' ∧
          ∀ z ∈ 𝔻, |φ z - φ' z| ≤ B
/-- Splitting a σ-finite measure dominating another (used by M11 and M12 to write `μ' = ν + ε·m`;
moved here from M11 so that M12 need not import M11). -/
theorem Measure.exists_add_eq_of_le {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [SigmaFinite μ] (h : ν ≤ μ) : ∃ d : Measure X, d + ν = μ
```

## 9. Issues found (for NOTEBOOK)

1. **p. 370, statement of Lemma 6, disc.** "`Δψ > ε dm(z)`" is what the plane needs. In the disc, the proof (p. 371) and the use (p. 372) need the invariant form `(1−|z|²)²Δψ > ε`. Plain `ε dm` would not allow subtracting `c log(1/(1−|z|²))`.
2. **p. 370, tiling.**
   - In the disc, "dyadic squares" are not specified. A tiling by polar dyadic boxes must handle the central region and must ensure `μ(Q_j) > 2`, which needs two disjoint `R₀`-balls per tile.
   - The formalization avoids tiles with the weight `w(ζ) = 1/(2μ(B(ζ,R)))`. This also weakens the hypothesis to `μ(B(z,R)) ≥ 1`.
3. **p. 370, "`μ₁` is locally doubling".** True but unused.
4. **p. 371–372, `sup|φ − ψ| < ∞` with the global `K`.**
   - In `ℂ` it fails as written: there is an unbounded harmonic polynomial error from the cut-off `χ_{D(0,1)}`, and the plane kernel has a sign error (M02 §6, items 1–2).
   - The precise erratum is the last display of p. 371, `K[μ₁] − K[μ̃₁] = K[μ₁] − K[μ₁] ⋆ χ_{D(0,2R)}/|D(0,2R)|`. It commutes `K` with the convolution, which holds only for the (translation-invariant) logarithmic part. In `𝔻` the bound is therefore not justified for the non-invariant correction term (M02 §6, item 3).
   - The formalization replaces `K[μ̃₁] − K[μ₁]` by the compactly supported local potential `V`. Then `0 ≤ V ≲ μ₁(B(z,R))`-type bounds follow from [Chr91, Lemma 2.3] exactly as the paper intends.
5. **p. 371, growth of `μ₁`.** "`μ₁(D(0,r)) ≲ (1−r)⁻²`" is too weak for the convergence of the disc `K[ν]` (M02 §6, item 3). Irrelevant for the formal route.
6. **p. 372, proof of Theorem 2.** The sign of the auxiliary weight is already in README §4. Also, the mass condition of the auxiliary weight needs the growth lemma of M03 (§7).
