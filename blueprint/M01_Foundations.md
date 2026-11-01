# M01 — Foundations

**Lean files:** `OrtegaCerdaMultipliers/Foundations/*.lean`. There are nine files:
- `Basic.lean`: the definition gap;
- seven files copied from BOC;
- `Hyperbolic.lean`: new.

**Status:** everything is proved. There is no `sorry`, `axiom`, `admit` or `native_decide`, and `lake build` passes. `#print axioms` on the main results shows only `propext`, `Classical.choice` and `Quot.sound`.

**Depends on:**
- M00 (`Defs.lean`): `dbar`, `IsWeakDbarSol`, `𝔻`, `pseudoHyp`, `hypDist`, `hypBall`;
- Mathlib. The specific lemmas are listed per file in §5.

**Used by:**
- M02 (potentials: Wirtinger/`lap` calculus, polar coordinates, Weyl);
- M03 and M05 (hyperbolic discs `hypBall`, their Euclidean size, Möbius invariance);
- M04 and M10 (Pompeiu/Cauchy transform, `IsWeakDbarSol` calculus);
- M07 (Weyl's lemma, removable singularities);
- M08, M11.

Notation:
- `φ_a := mobius a`, with `φ_a(ζ) = (a − ζ)/(1 − āζ)`;
- `ρ := pseudoHyp`, the pseudo-hyperbolic distance;
- `β := hypDist = artanh ρ`, the hyperbolic distance;
- `D(z, r) := hypBall z r = {w ∈ 𝔻 : β(z, w) < r}`.

---

## 0. Provenance

All copied files come from the companion project `../MR1340337`:
- library `BerndtssonOrtegaCerda`, namespace `BOC`;
- same author, Apache-2.0 license;
- **commit `22104d9`** (`git -C ../MR1340337 rev-parse --short HEAD`). The working tree was clean, and the files were taken with `git show 22104d9:<path>`.

The copy is needed because RMI must not depend on BOC: BOC will later `require` RMI (BOC module M23). Each copied file has a **Provenance** paragraph in its module docstring.

| RMI file (`Foundations/`) | BOC source (`BerndtssonOrtegaCerda/`) | BOC module / blueprint | Changes |
|---|---|---|---|
| `Basic.lean` | `Defs.lean` (selected definitions) | M00 | new file, see §1 |
| `Wirtinger.lean` | `Calculus/Wirtinger.lean` | M01 `M01_Wirtinger.md` | namespace, imports, header |
| `Polar.lean` | `Calculus/Polar.lean` | M02 `M02_Polar.md` | namespace, imports, header |
| `LocalEstimates.lean` | `Complex/LocalEstimates.lean` | M03 `M03_LocalEstimates.md` | namespace, imports, header |
| `Separated.lean` | `Geometry/Separated.lean` | M04 `M04_Separated.md` | namespace, imports, header |
| `Pompeiu.lean` | `Complex/Pompeiu.lean` | M05 `M05_Pompeiu.md` | namespace, imports, header |
| `Weyl.lean` | `Complex/Weyl.lean` | M06 `M06_Weyl.md` | namespace, imports, header |
| `DiscGeometry.lean` | `Disc/Geometry.lean` | M15 `M15_DiscGeometry.md` | namespace, imports, header, `pseudoHyp` patches (§1.3) |
| `Hyperbolic.lean` | — | — | new (§3) |

**How the copies were made.**
- Namespace `BOC` → `OC`, also in docstring references such as `` `OC.lintegral_eq_lintegral_circle` ``.
- Imports: `BerndtssonOrtegaCerda.Defs` → `OrtegaCerdaMultipliers.Foundations.Basic`, and `BerndtssonOrtegaCerda.X.Y` → `OrtegaCerdaMultipliers.Foundations.Y`.
- The `# Mxx — …` titles became `# M01 (Foundations) — …`, and a provenance paragraph was added.
- No proof was changed, except the `pseudoHyp` spots in `DiscGeometry.lean` listed in §1.3 (12 lemmas).
- The unused-variable linter warnings are inherited unchanged from BOC.

**Import closure.** `Disc/Geometry.lean` imports `Calculus/Wirtinger`, `Calculus/Polar` and `Geometry/Separated`. `Complex/Weyl.lean` imports `Wirtinger`, `Polar`, `LocalEstimates` and `Pompeiu`. Nothing else is needed: the closure of the requested files is exactly the seven copied files plus `Defs`.

**Re-synchronisation.**
- If BOC fixes or extends one of these files before M23, re-copy it with the recipe above.
- When BOC starts to `require` RMI, BOC should delete its own copies and import these (BOC module M23).
- Name clashes are then avoided by the different namespaces (`BOC` vs `OC`).

---

## 1. The definition gap (`Basic.lean`)

### 1.1 Definitions present in both `Defs.lean`

| name | BOC | RMI | status |
|---|---|---|---|
| `dbar` | `(1/2 : ℂ) * (fderiv ℝ f z 1 + I * fderiv ℝ f z I)` | same | textually identical |
| `IsWeakDbarSol Ω u g` | `LocallyIntegrableOn u Ω ∧ LocallyIntegrableOn g Ω ∧ ∀ α smooth, compact support in Ω, ∫ u ∂̄α = -∫ g α` | same | textually identical |
| `𝔻` | `abbrev 𝔻 : Set ℂ := ball (0 : ℂ) 1` | same | textually identical |
| `pseudoHyp` | `‖mobius z ζ‖ = ‖(z - ζ)/(1 - conj z * ζ)‖` | `‖z - w‖ / ‖1 - conj z * w‖` | **different terms, equal values** (§1.3) |

### 1.2 Missing definitions, copied verbatim from BOC `Defs.lean`

```lean
/-- BOC's Laplacian `∂²/∂z∂z̄ = ¼ Δ`. -/
def lap (φ : ℂ → ℝ) (z : ℂ) : ℝ := (1 / 4 : ℝ) * Laplacian.laplacian φ z

def IsSeparated (Γ : Set ℂ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b

/-- `φ_z(ζ) = (z - ζ) / (1 - z̄ ζ)`. -/
def mobius (z ζ : ℂ) : ℂ := (z - ζ) / (1 - conj z * ζ)

def IsDiskSeparated (Γ : Set ℂ) : Prop :=
  Γ ⊆ 𝔻 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ pseudoHyp a b

/-- `Δ̃ = (1 - |z|²)² ∂²/∂z∂z̄`. -/
def invLap (φ : ℂ → ℝ) (z : ℂ) : ℝ := (1 - ‖z‖ ^ 2) ^ 2 * lap φ z

/-- `dλ = dm / (π (1 - |z|²)²)`. -/
def invDensity (ζ : ℂ) : ℝ := (Real.pi * (1 - ‖ζ‖ ^ 2) ^ 2)⁻¹
```

These are exactly the BOC definitions that the copied files use. The BOC `Defs.lean` identifiers used by the seven copied files are:
- `lap`;
- `IsSeparated`, `IsDiskSeparated`;
- `mobius`, `pseudoHyp`;
- `invLap`, `invDensity`;
- `dbar`, `IsWeakDbarSol`, `𝔻`.

`IsDiskSeparated` is written with RMI's `pseudoHyp`. It is therefore *propositionally* (not definitionally) equal to BOC's `IsDiskSeparated`.

**Laplacian convention.**
- RMI's M00 uses the standard Laplacian `Laplacian.laplacian`, with `Δ log|z| = 2πδ₀`.
- The copied Wirtinger calculus is written for `lap = ¼Δ = ∂∂̄`.
- The bridge is:

```lean
theorem laplacian_eq_four_mul_lap (φ : ℂ → ℝ) (z : ℂ) :
    Laplacian.laplacian φ z = 4 * lap φ z
```

### 1.3 `pseudoHyp`

```lean
theorem pseudoHyp_eq_norm_mobius (z ζ : ℂ) : pseudoHyp z ζ = ‖mobius z ζ‖
```
*Proof.* `rw [pseudoHyp, mobius, norm_div]`. The argument order is the same in both definitions, `z − ζ` over `1 − z̄ζ`, so no `norm_sub_rev` is needed.

**Patched proofs in `DiscGeometry.lean`.** These proofs unfolded BOC's `pseudoHyp` to `‖mobius _ _‖`; each now starts with `rw [pseudoHyp_eq_norm_mobius]`, or unfolds RMI's quotient directly:
- `pseudoHyp_comm`, `pseudoHyp_self`, `pseudoHyp_zero_left`, `pseudoHyp_zero_right`;
- `pseudoHyp_nonneg`, `pseudoHyp_lt_one`;
- `pseudoHyp_mobius`, `pseudoHyp_le_norm_add_norm`;
- the two `hwn` steps in `pseudoBall_subset_ball` and `one_sub_normSq_comparable`;
- `ball_subset_pseudoBall`, `norm_sub_ge_of_le_pseudoHyp`, `measurableSet_pseudoBall`.

The statements are unchanged.

---

## 2. Copied files: main lemmas

The mathematics and full proofs are in the BOC blueprints cited in §0. Only the main statements are listed here, in their `OC` form.

### 2.1 `Wirtinger.lean`, from BOC M01

`∂ = dz`, `∂̄ = dbar`, the complexification `cplx`, and the `lap` calculus. It also contains integration by parts against test functions.

```lean
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f z 1 - I * fderiv ℝ f z I)
def cplx (φ : ℂ → ℝ) : ℂ → ℂ := fun z ↦ (φ z : ℂ)

theorem fderiv_apply_eq_dz_dbar {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (w : ℂ) :
    fderiv ℝ f z w = dz f z * w + dbar f z * conj w
theorem differentiableAt_iff_dbar_eq_zero {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ f z ↔ dbar f z = 0
theorem dbar_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w ↦ f w * g w) z = dbar f z * g z + f z * dbar g z
theorem dbar_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dbar (fun w ↦ conj (f w)) z = conj (dz f z)
theorem dz_dbar_eq_laplacian {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    dz (dbar f) z = (1 / 4 : ℂ) * Laplacian.laplacian f z
theorem dz_dbar_cplx {φ : ℂ → ℝ} {z : ℂ} (hφ : ContDiffAt ℝ 2 φ z) :
    dz (dbar (cplx φ)) z = (lap φ z : ℂ)
theorem lap_add {φ ψ : ℂ → ℝ} {z : ℂ} (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z) :
    lap (fun w ↦ φ w + ψ w) z = lap φ z + lap ψ z
theorem lap_const_mul (c : ℝ) {φ : ℂ → ℝ} {z : ℂ} (hφ : ContDiffAt ℝ 2 φ z) :
    lap (fun w ↦ c * φ w) z = c * lap φ z
theorem lap_comp_normSq {F : ℝ → ℝ} {z : ℂ} (hF : ContDiffAt ℝ 2 F (‖z‖ ^ 2)) :
    lap (fun w ↦ F (‖w‖ ^ 2)) z = deriv F (‖z‖ ^ 2) + ‖z‖ ^ 2 * deriv (deriv F) (‖z‖ ^ 2)
theorem lap_log_normSq {z : ℂ} (hz : z ≠ 0) : lap (fun w ↦ Real.log (‖w‖ ^ 2)) z = 0
theorem lap_normSq_mul_exp {h : ℂ → ℂ} {ψ : ℂ → ℝ} {z : ℂ} (hh : Differentiable ℂ h)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    lap (fun w ↦ ‖h w‖ ^ 2 * Real.exp (-ψ w)) z =
      ‖deriv h z - h z * dz (cplx ψ) z‖ ^ 2 * Real.exp (-ψ z)
        - ‖h z‖ ^ 2 * Real.exp (-ψ z) * lap ψ z
theorem integral_mul_dbar {Ω : Set ℂ} (hΩ : IsOpen Ω) {u α : ℂ → ℂ} (hu : ContDiffOn ℝ 1 u Ω)
    (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) (hs : tsupport α ⊆ Ω) :
    ∫ z, u z * dbar α z = -∫ z, dbar u z * α z
theorem isWeakDbarSol_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ 1 u Ω) : IsWeakDbarSol Ω u (dbar u)
theorem integral_mul_lap {g U : ℂ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hU : ContDiff ℝ 2 U) : ∫ z, g z * lap U z = ∫ z, lap g z * U z
```

### 2.2 `Polar.lean`, from BOC M02

Polar coordinates around any centre, radial integrals, and local integrability of the Cauchy kernel.

```lean
theorem lintegral_eq_lintegral_circle (c : ℂ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z = ∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal s * ∫⁻ θ in Ioc 0 (2 * Real.pi), f (circleMap c s θ)
theorem lintegral_ball_eq_lintegral_circle (c : ℂ) (r : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in ball c r, f z = ∫⁻ s in Ioo (0 : ℝ) r,
      ENNReal.ofReal s * ∫⁻ θ in Ioc 0 (2 * Real.pi), f (circleMap c s θ)
theorem setIntegral_ball_eq_intervalIntegral_circleAverage (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    {f : ℂ → E} (hf : IntegrableOn f (ball c r)) :
    ∫ z in ball c r, f z = ∫ s in (0 : ℝ)..r, (2 * Real.pi * s) • Real.circleAverage f c s
theorem lintegral_comp_norm_sub (a : ℂ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z : ℂ, F ‖z - a‖ =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal s * F s
theorem integral_comp_normSq_sub (a : ℂ) {F : ℝ → ℝ} (hF : IntegrableOn F (Set.Ioi 0)) :
    ∫ z : ℂ, F (‖z - a‖ ^ 2) = Real.pi * ∫ t in Set.Ioi (0 : ℝ), F t
theorem volume_ball_complex (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball a r) = ENNReal.ofReal (Real.pi * r ^ 2)
theorem lintegral_inv_norm_sub_ball (a : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∫⁻ z in Metric.ball a R, ENNReal.ofReal ‖z - a‖⁻¹ = ENNReal.ofReal (2 * Real.pi * R)
theorem locallyIntegrable_inv_sub (a : ℂ) : LocallyIntegrable (fun z : ℂ ↦ (z - a)⁻¹)
theorem lintegral_inv_norm_sub_le {c w : ℂ} {R : ℝ} (hw : w ∈ Metric.closedBall c R) :
    ∫⁻ z in Metric.closedBall c R, ENNReal.ofReal ‖z - w‖⁻¹ ≤
      ENNReal.ofReal (4 * Real.pi * R)
theorem lintegral_inv_normSq_sub_ball_eq_top (a : ℂ) {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in Metric.ball a R, ENNReal.ofReal (‖z - a‖⁻¹ ^ 2) = ∞
```

### 2.3 `LocalEstimates.lean`, from BOC M03

Mean-value estimates for holomorphic functions.

```lean
theorem norm_sq_le_lintegral_ball {g : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.ball a r)) :
    ENNReal.ofReal (Real.pi * r ^ 2 * ‖g a‖ ^ 2) ≤
      ∫⁻ z in Metric.ball a r, ENNReal.ofReal (‖g z‖ ^ 2)
theorem norm_deriv_sq_le {g : ℂ → ℂ} {a z : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (Metric.ball a R)) (hz : z ∈ Metric.ball a (R / 2)) :
    ENNReal.ofReal (‖deriv g z‖ ^ 2) ≤
      ENNReal.ofReal (256 / (Real.pi * R ^ 4)) *
        ∫⁻ w in Metric.ball a R, ENNReal.ofReal (‖g w‖ ^ 2)
theorem integral_re_ball {G : ℂ → ℂ} {a : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hG : DifferentiableOn ℂ G (Metric.ball a R)) :
    ∫ z in Metric.ball a r, (G z).re = Real.pi * r ^ 2 * (G a).re
```

### 2.4 `Pompeiu.lean`, from BOC M05

The Cauchy transform, the Pompeiu formula, and the weak `∂̄` equation for the Cauchy kernel.

```lean
def cauchyTransform (f : ℂ → ℂ) (w : ℂ) : ℂ := (1 / Real.pi : ℂ) * ∫ z, f z / (w - z)

theorem pompeiu {α : ℂ → ℂ} (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) (w : ℂ) :
    cauchyTransform (dbar α) w = α w
theorem continuous_cauchyTransform {f : ℂ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous (cauchyTransform f)
theorem norm_cauchyTransform_le {f : ℂ → ℂ} {M R : ℝ} {c w : ℂ} (hf : Continuous f)
    (hM : ∀ z, ‖f z‖ ≤ M) (hsupp : tsupport f ⊆ Metric.closedBall c R)
    (hw : w ∈ Metric.closedBall c R) :
    ‖cauchyTransform f w‖ ≤ 4 * M * R
theorem isWeakDbarSol_cauchyTransform {f : ℂ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) :
    IsWeakDbarSol Set.univ (cauchyTransform f) f
theorem contDiff_cauchyTransform {β : ℂ → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hc : HasCompactSupport β) :
    ContDiff ℝ (⊤ : ℕ∞) (cauchyTransform β)
theorem dbar_cauchyTransform {β : ℂ → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hc : HasCompactSupport β)
    (w : ℂ) : dbar (cauchyTransform β) w = β w
theorem differentiableOn_cauchyTransform {f : ℂ → ℂ} (hf : Integrable f)
    (hc : HasCompactSupport f) {U : Set ℂ} (hU : IsOpen U) (hdisj : Disjoint (tsupport f) U) :
    DifferentiableOn ℂ (cauchyTransform f) U
lemma integral_mul_cauchyTransform_comm {f g : ℂ → ℂ} (hf : Integrable f) (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    ∫ w, g w * cauchyTransform f w = -∫ z, f z * cauchyTransform g z
```

### 2.5 `Weyl.lean`, from BOC M06

Weyl's lemma for `∂̄`, the algebra of `IsWeakDbarSol`, and L² removability.

```lean
theorem weyl_dbar {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ} (hu : LocallyIntegrableOn u Ω)
    (h : ∀ α : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) α → HasCompactSupport α → tsupport α ⊆ Ω →
      ∫ z, u z * dbar α z = 0) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H Ω ∧ ∀ᵐ z ∂(volume.restrict Ω), u z = H z
theorem IsWeakDbarSol.exists_holomorphic {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ}
    (h : IsWeakDbarSol Ω u 0) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H Ω ∧ ∀ᵐ z ∂(volume.restrict Ω), u z = H z
theorem IsWeakDbarSol.sub {Ω : Set ℂ} {u₁ u₂ g₁ g₂ : ℂ → ℂ} (h₁ : IsWeakDbarSol Ω u₁ g₁)
    (h₂ : IsWeakDbarSol Ω u₂ g₂) : IsWeakDbarSol Ω (u₁ - u₂) (g₁ - g₂)
theorem IsWeakDbarSol.mono {Ω Ω' : Set ℂ} {u g : ℂ → ℂ} (h : IsWeakDbarSol Ω u g)
    (hΩ : Ω' ⊆ Ω) : IsWeakDbarSol Ω' u g
theorem IsWeakDbarSol.congr {Ω : Set ℂ} (hΩ : IsOpen Ω) {u g g' : ℂ → ℂ}
    (h : IsWeakDbarSol Ω u g) (hg : Set.EqOn g g' Ω) : IsWeakDbarSol Ω u g'
theorem differentiableOn_of_isWeakDbarSol_zero {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ}
    (hc : ContinuousOn u Ω) (h : IsWeakDbarSol Ω u 0) : DifferentiableOn ℂ u Ω
theorem removable_of_lintegral_div_normSq {u : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : DifferentiableOn ℂ u (Metric.ball a R \ {a}))
    (hL2 : ∫⁻ z in Metric.ball a R, ENNReal.ofReal (‖u z‖ ^ 2 / ‖z - a‖ ^ 2) < ∞) :
    ∃ U : ℂ → ℂ, DifferentiableOn ℂ U (Metric.ball a R) ∧ U a = 0 ∧
      ∀ z ∈ Metric.ball a R \ {a}, U z = u z
```

### 2.6 `Separated.lean`, from BOC M04

Counting by area for Euclidean-separated sets in `ℂ`. Throughout, `variable {Γ : Set ℂ} {ε : ℝ}`.

```lean
theorem ncard_inter_ball_le_of_sep (hε0 : 0 < ε) (hε : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b)
    (z : ℂ) (R : ℝ) : (Γ ∩ Metric.ball z R).ncard ≤ ⌊(2 * R / ε + 1) ^ 2⌋₊
theorem finite_inter_ball_of_sep (hε0 : 0 < ε) (hε : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b)
    (z : ℂ) (R : ℝ) : (Γ ∩ Metric.ball z R).Finite
theorem IsSeparated.countable (hΓ : IsSeparated Γ) : Γ.Countable
theorem IsSeparated.volume_eq_zero (hΓ : IsSeparated Γ) : volume Γ = 0
theorem IsSeparated.isClosed (hΓ : IsSeparated Γ) : IsClosed Γ
theorem IsSeparated.exists_tsum_lintegral_ball_le (hΓ : IsSeparated Γ) (R : ℝ) :
    ∃ N : ℕ, ∀ F : ℂ → ℝ≥0∞, Measurable F →
      ∑' a : Γ, ∫⁻ z in Metric.ball (a : ℂ) R, F z ≤ (N : ℝ≥0∞) * ∫⁻ z, F z
theorem IsSeparated.locallyFinite_ball (hΓ : IsSeparated Γ) (R : ℝ) :
    LocallyFinite (fun a : Γ ↦ Metric.ball (a : ℂ) R)
```

### 2.7 `DiscGeometry.lean`, from BOC M15

Möbius maps, pseudo-hyperbolic distance (weak triangle inequality, invariance), the invariant Laplacian and measure, and pseudo-hyperbolically separated sets.

```lean
theorem norm_one_sub_conj_mul_sq_sub (a ζ : ℂ) :
    ‖1 - conj a * ζ‖ ^ 2 - ‖a - ζ‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖ζ‖ ^ 2)
theorem one_sub_normSq_mobius {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    1 - ‖mobius a ζ‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖ζ‖ ^ 2) / ‖1 - conj a * ζ‖ ^ 2
theorem mobius_mem_disc {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) : mobius a ζ ∈ 𝔻
theorem mobius_mobius {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) : mobius a (mobius a ζ) = ζ
theorem mobius_image_disc {a : ℂ} (ha : a ∈ 𝔻) : mobius a '' 𝔻 = 𝔻
theorem deriv_mobius {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    deriv (mobius a) ζ = -(1 - ‖a‖ ^ 2 : ℂ) / (1 - conj a * ζ) ^ 2
theorem norm_deriv_mobius {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    ‖deriv (mobius a) ζ‖ = (1 - ‖mobius a ζ‖ ^ 2) / (1 - ‖ζ‖ ^ 2)
theorem pseudoHyp_comm (z ζ : ℂ) : pseudoHyp z ζ = pseudoHyp ζ z
theorem pseudoHyp_self (z : ℂ) : pseudoHyp z z = 0
theorem pseudoHyp_zero_left (ζ : ℂ) : pseudoHyp 0 ζ = ‖ζ‖
theorem pseudoHyp_nonneg (z ζ : ℂ) : 0 ≤ pseudoHyp z ζ
theorem pseudoHyp_lt_one {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) : pseudoHyp z ζ < 1
theorem mobius_mobius_mobius {a u v : ℂ} (ha : a ∈ 𝔻) (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) :
    mobius (mobius a u) (mobius a v) = -((1 - a * conj u) / (1 - conj a * u)) * mobius u v
theorem pseudoHyp_mobius {a u v : ℂ} (ha : a ∈ 𝔻) (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) :
    pseudoHyp (mobius a u) (mobius a v) = pseudoHyp u v
theorem pseudoHyp_triangle {u v w : ℂ} (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) (hw : w ∈ 𝔻) :
    pseudoHyp u w ≤ pseudoHyp u v + pseudoHyp v w
theorem lap_comp_holomorphic {u : ℂ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hF : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w)
    (hu : ContDiffAt ℝ 2 u (F z)) (hF2 : ContDiffAt ℝ 2 F z) :
    lap (u ∘ F) z = lap u (F z) * ‖deriv F z‖ ^ 2
theorem invLap_comp_mobius {u : ℂ → ℝ} {a z : ℂ} (ha : a ∈ 𝔻) (hz : z ∈ 𝔻)
    (hu : ContDiffAt ℝ 2 u (mobius a z)) :
    invLap (u ∘ mobius a) z = invLap u (mobius a z)
theorem ball_subset_pseudoBall {a : ℂ} (ha : a ∈ 𝔻) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Metric.ball a (s * (1 - ‖a‖ ^ 2) / 2) ⊆ {z ∈ 𝔻 | pseudoHyp a z < s}
theorem pseudoBall_subset_ball {a : ℂ} (ha : a ∈ 𝔻) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    {z ∈ 𝔻 | pseudoHyp a z < s} ⊆ Metric.ball a (s * (1 - ‖a‖ ^ 2) / (1 - s))
theorem one_sub_normSq_comparable {a z : ℂ} (ha : a ∈ 𝔻) (hz : z ∈ 𝔻) {s : ℝ} (hs1 : s < 1)
    (hρ : pseudoHyp a z < s) :
    (1 - s) / (1 + s) * (1 - ‖a‖ ^ 2) ≤ 1 - ‖z‖ ^ 2 ∧
      1 - ‖z‖ ^ 2 ≤ (1 + s) / (1 - s) * (1 - ‖a‖ ^ 2)
theorem integral_comp_mobius {f : ℂ → ℝ} {a : ℂ} (ha : a ∈ 𝔻) :
    ∫ ζ in 𝔻, f (mobius a ζ) * invDensity ζ = ∫ ζ in 𝔻, f ζ * invDensity ζ
theorem IsDiskSeparated.exists_ncard_le {Γ : Set ℂ} (hΓ : IsDiskSeparated Γ) {s : ℝ}
    (hs1 : s < 1) : ∃ N : ℕ, ∀ z ∈ 𝔻, {w ∈ Γ | pseudoHyp z w < s}.ncard ≤ N
theorem IsDiskSeparated.exists_tsum_lintegral_le {Γ : Set ℂ} (hΓ : IsDiskSeparated Γ) {s : ℝ}
    (hs1 : s < 1) : ∃ N : ℕ, ∀ F : ℂ → ℝ≥0∞, Measurable F →
      ∑' w : Γ, ∫⁻ z in {z ∈ 𝔻 | pseudoHyp w z < s}, F z ≤ (N : ℝ≥0∞) * ∫⁻ z in 𝔻, F z
theorem lap_neg_log_one_sub_normSq {z : ℂ} (hz : z ∈ 𝔻) :
    lap (fun w ↦ -Real.log (1 - ‖w‖ ^ 2)) z = (1 - ‖z‖ ^ 2)⁻¹ ^ 2
theorem invLap_log_bergman (α : ℝ) {z : ℂ} (hz : z ∈ 𝔻) :
    invLap (fun w ↦ α * Real.log (1 / (1 - ‖w‖ ^ 2))) z = α
```

BOC's file contains only the *weak* triangle inequality `ρ(u,w) ≤ ρ(u,v) + ρ(v,w)`. The strong (Möbius-addition) form, needed for `β`, is new; see H2 below.

---

## 3. New: the hyperbolic distance `β = artanh ρ` (`Hyperbolic.lean`)

This section is new material, not copied. All statements are proved; there is no `sorry`.

**Junk values.** Mathlib defines `artanh x = log √((1+x)/(1−x))`. Off `(−1, 1)` this is junk, equal to `0` (`Real.artanh_eq_zero_iff`). Every metric statement below therefore assumes that the points lie in `𝔻`, where `ρ ∈ [0, 1)`. The one exception is `isOpen_hypBall`, where the junk is analysed (H5).

### H1. Addition formulas

**Claim.** For all real `a, b`:
`tanh(a + b) = (tanh a + tanh b)/(1 + tanh a tanh b)`.

For `x, y ∈ (−1, 1)`:
`artanh x + artanh y = artanh((x + y)/(1 + xy))`.

*Proof.*
- **tanh.** Write `tanh = sinh/cosh`, and expand `sinh(a+b) = sinh a cosh b + cosh a sinh b` and `cosh(a+b) = cosh a cosh b + sinh a sinh b`. Then divide numerator and denominator by `cosh a cosh b > 0`. The new denominator `cosh a cosh b + sinh a sinh b = cosh(a+b)` is positive. In Lean: `field_simp`.
- **artanh.** Put `a = artanh x` and `b = artanh y`, so `tanh a = x` and `tanh b = y` (`Real.tanh_artanh`, using `x, y ∈ (−1,1)`). Then `tanh(a+b) = (x+y)/(1+xy)`, and `a + b = artanh(tanh(a+b))` (`Real.artanh_tanh`). ∎

Also: `tanh r = (e^{2r} − 1)/(e^{2r} + 1)`, by multiplying `Real.tanh_eq` through by `e^r`. Hence `tanh r ≥ 0` for `r ≥ 0`. Mathlib has no `tanh_nonneg`.

### H2. Strong triangle inequality for `ρ`

**Claim.** For `p, q ∈ 𝔻`:
`ρ(p, q) ≤ (|p| + |q|)/(1 + |p||q|)`.

Consequently, for `u, v, w ∈ 𝔻`:
`ρ(u, w) ≤ (ρ(u,v) + ρ(v,w))/(1 + ρ(u,v)ρ(v,w))`.

*Proof.* Let `x = |p|`, `y = |q|` and `D = |1 − p̄q|`, so that `D > 0`.

1. The key identity (BOC G2, `one_sub_normSq_mobius`) gives
   `1 − ρ(p,q)² = 1 − |φ_p(q)|² = (1 − x²)(1 − y²)/D²`.
2. By the triangle inequality, `D ≤ 1 + xy`. The numerator is `≥ 0`, so
   `1 − ρ² ≥ (1 − x²)(1 − y²)/(1 + xy)²`.
3. The algebraic identity `(1 + xy)² − (1 − x²)(1 − y²) = (x + y)²` turns this into
   `ρ² ≤ ((x + y)/(1 + xy))²`.
4. Both sides are `≥ 0`, so taking square roots gives the first claim.

This is BOC's `pseudoHyp_le_norm_add_norm` stopped before its last, lossy step `(x+y)/(1+xy) ≤ x + y`.

*General form.* Möbius invariance (`pseudoHyp_mobius`) is used with `a = v`, together with `φ_v(v) = 0`:
- `ρ(u, w) = ρ(φ_v u, φ_v w)`;
- `ρ(u, v) = ρ(φ_v u, 0) = |φ_v u|`;
- `ρ(v, w) = ρ(0, φ_v w) = |φ_v w|`.

Now apply the first claim to `p = φ_v u` and `q = φ_v w`, both in `𝔻` (`mobius_mem_disc`). ∎

### H3. `β` is a metric on `𝔻`

**Claims.**
- `β(z,w) ≥ 0` for all `z, w`.
- `β(z,w) = β(w,z)` for all `z, w`.
- `β(z,z) = 0` for all `z`.
- For `z, w ∈ 𝔻`: `β(z,w) = 0 ⟺ z = w`.
- For `u, v, w ∈ 𝔻`: `β(u,w) ≤ β(u,v) + β(v,w)`.

*Proof.*
- **Basic properties.**
  - *Nonnegativity:* `ρ ≥ 0` and `artanh ≥ 0` on `[0, ∞)` (`Real.artanh_nonneg`, which holds even with the junk values).
  - *Symmetry:* `pseudoHyp_comm`.
  - *Diagonal:* `artanh 0 = 0`.
  - *Definiteness:* on `𝔻` we have `ρ ∈ [0,1) ⊆ (−1,1)`, where `artanh` vanishes only at `0`. Moreover `ρ(z,w) = |z−w|/|1−z̄w| = 0` iff `z = w`, because the denominator does not vanish on `𝔻 × 𝔻`.
- **Triangle inequality.** Let `a = ρ(u,v)` and `b = ρ(v,w)`, both in `[0,1)`.
  1. By H1, `β(u,v) + β(v,w) = artanh a + artanh b = artanh((a+b)/(1+ab))`.
  2. By H2, `ρ(u,w) ≤ (a+b)/(1+ab)`.
  3. The bound is `< 1`, because `1 + ab − a − b = (1−a)(1−b) > 0` (`add_div_one_add_mul_lt_one`).
  4. Also `ρ(u,w) > −1`.
  5. `artanh` is monotone on `(−1,1)` (`Real.artanh_le_artanh`), which concludes. ∎

### H4. `β < r ⟺ ρ < tanh r`

**Claim.** For `z, w ∈ 𝔻` and **every** real `r`:
- `β(z,w) < r ⟺ ρ(z,w) < tanh r`;
- `β(z,w) ≤ r ⟺ ρ(z,w) ≤ tanh r`;
- `tanh β(z,w) = ρ(z,w)`.

*Proof.* We have `ρ(z,w) ∈ (−1,1)` and `tanh r ∈ (−1,1)` (`Real.neg_one_lt_tanh`, `Real.tanh_lt_one`). On `(−1,1)`, `artanh` is strictly increasing (`Real.artanh_lt_artanh_iff`), and `artanh(tanh r) = r`. No sign condition on `r` is needed: for `r ≤ 0` both sides are false. ∎

### H5. Hyperbolic discs are open and lie in `𝔻`

**Claims.**
- `D(z, r) ⊆ 𝔻`.
- For `z ∈ 𝔻`: `D(z, r) = {w ∈ 𝔻 : ρ(z,w) < tanh r}`.
- `D(z, r)` is open for **all** `z ∈ ℂ` and `r ∈ ℝ`.

*Proof.*
- **Inclusion.** This holds by definition.
- **Description for `z ∈ 𝔻`.** This is H4.
- **Openness, `z ∈ 𝔻`.** `ρ(z, ·) = |z − ·|/|1 − z̄ ·|` is continuous on `𝔻`, where the denominator is `> 0` (`norm_one_sub_conj_mul_pos`). So `D(z,r) = 𝔻 ∩ ρ(z,·)⁻¹(−∞, tanh r)` is open (`ContinuousOn.isOpen_inter_preimage`).
- **Openness, `z ∉ 𝔻` (junk case).** For every `w ∈ 𝔻`, `β(z, w) = 0`:
  - Either `1 − z̄w = 0`, and then `ρ = 0` because `x/0 = 0`.
  - Or the identity `|1 − z̄w|² − |z − w|² = (1 − |z|²)(1 − |w|²) ≤ 0` gives `ρ ≥ 1`.

  In both cases `artanh ρ = 0` (`Real.artanh_eq_zero_iff`). Hence `D(z, r) = 𝔻 ∩ {_ | 0 < r}`, which is `𝔻` or `∅`, and is open (`hypDist_eq_zero_of_notMem`). ∎

Also `z ∈ D(z, r)` for `z ∈ 𝔻` and `r > 0`.

### H6. Möbius invariance

**Claim.** For `a, z, w ∈ 𝔻`: `β(φ_a z, φ_a w) = β(z, w)`.

*Proof.* This is `artanh` applied to `pseudoHyp_mobius` (BOC G5). G5 rests on the identity `φ_{φ_a u}(φ_a v) = −((1 − a ū)/(1 − ā u)) · φ_u(v)`, where the prefactor is unimodular. ∎

### H7. Hyperbolic discs as images and as Euclidean discs

**Claim (image).** For `z ∈ 𝔻` and any `r`:
`D(z, r) = φ_z(B(0, tanh r))`.

*Proof.* Let `t = tanh r < 1`, so that `B(0,t) ⊆ 𝔻`.
- (⊆) If `w ∈ 𝔻` and `|φ_z(w)| < t`, put `u = φ_z(w) ∈ B(0,t)`. Then `φ_z(u) = w`, since `φ_z` is an involution on `𝔻`.
- (⊇) Conversely, if `u ∈ B(0,t)`, then `u ∈ 𝔻`, `φ_z(u) ∈ 𝔻`, and `ρ(z, φ_z(u)) = |φ_z(φ_z u)| = |u| < t`. ∎

**Claim (explicit centre and radius).** Let `z ∈ 𝔻` and `0 ≤ t < 1`. Put
`A = 1 − t²|z|² > 0`, `c = (1 − t²) z / A`, `R = t(1 − |z|²)/A`.

Then `{w ∈ 𝔻 : ρ(z,w) < t} = B(c, R)`. In particular, for `r ≥ 0`, `D(z, r) = B(c, R)` with `t = tanh r`.

*Proof.*
1. **Identity.** For all `w ∈ ℂ`:
   `|w − z|² − t²|1 − z̄w|² = A(|w − c|² − R²)`.
   Both sides equal `A|w|² − 2(1 − t²) Re(w z̄) + |z|² − t²`. The constant term uses
   `(1−t²)²|z|² − t²(1−|z|²)² = (|z|² − t²) A`.
   In Lean the identity is checked by expanding into real and imaginary parts, then `field_simp; ring`.
2. **Equivalence on `𝔻`.** For `w ∈ 𝔻` we have `|1 − z̄w| > 0`. Hence
   `ρ(z,w) < t ⟺ |w − z| < t|1 − z̄w| ⟺ |w−z|² < t²|1−z̄w|² ⟺ |w − c| < R`.
   The last step divides by `A > 0`.
3. **`B(c, R) ⊆ 𝔻`.** With `s = |z|` we have `|c| = (1 − t²)s/A`, and
   `A(1 − |c| − R) = 1 − t²s² − (1 − t²)s − t(1 − s²) = (1 − t)(1 − s)(1 − ts) > 0`.
   So `|w| ≤ |c| + |w − c| < |c| + R < 1`. ∎

### H8. Euclidean size of hyperbolic discs

**Claim.** For `z ∈ 𝔻` and `0 < r ≤ 1`:
`B(z, r(1 − |z|)/10) ⊆ D(z, r) ⊆ B(z, 18 r (1 − |z|))`.

*Proof.* Let `s = tanh r ∈ (0, 1)`.

1. **BOC G7 bounds.** BOC G7 (`ball_subset_pseudoBall`, `pseudoBall_subset_ball`) gives
   `B(z, s(1−|z|²)/2) ⊆ {ρ(z,·) < s} = D(z, r) ⊆ B(z, s(1−|z|²)/(1 − s))`.
2. **Exponential form.** Put `E = e^{2r}`. Then `s = (E−1)/(E+1)` and `1 − s = 2/(E+1)`, so `s/(1−s) = (E−1)/2`.
3. **Bound on `E`.** Since `r ≤ 1`, `E ≤ e² < 9` (`Real.exp_one_lt_three`).
4. **Lower bound on `s`.** `E − 1 ≥ 2r` (`Real.add_one_le_exp`), so `s ≥ 2r/(E+1) ≥ r/5`.
5. **Upper bound on `s/(1−s)`.** `e^{−2r} ≥ 1 − 2r` gives `E − 1 ≤ 2rE`, so `s/(1−s) ≤ rE ≤ 9r`.
6. **Combine.** Use `1 − |z| ≤ 1 − |z|² ≤ 2(1 − |z|)`:
   - `r(1−|z|)/10 = (r/5)(1−|z|)/2 ≤ s(1−|z|²)/2`;
   - `s(1−|z|²)/(1−s) ≤ 9r · 2(1−|z|)`. ∎

The constants `1/10` and `18` are not optimised. Any `0 < r ≤ r₀` works in the same way, with constants depending on `r₀`.

### Lean statements (`Hyperbolic.lean`)

```lean
-- H1
theorem tanh_add (a b : ℝ) :
    Real.tanh (a + b) = (Real.tanh a + Real.tanh b) / (1 + Real.tanh a * Real.tanh b)
theorem tanh_eq_exp_two_mul (r : ℝ) :
    Real.tanh r = (Real.exp (2 * r) - 1) / (Real.exp (2 * r) + 1)
theorem tanh_nonneg_of_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Real.tanh r
theorem artanh_add_artanh {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh x + Real.artanh y = Real.artanh ((x + y) / (1 + x * y))
-- ρ on 𝔻, H2
theorem pseudoHyp_mem_Ioo {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    pseudoHyp z w ∈ Ioo (-1 : ℝ) 1
theorem pseudoHyp_eq_zero_iff {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    pseudoHyp z w = 0 ↔ z = w
theorem pseudoHyp_le_norm_add_norm_div {p q : ℂ} (hp : p ∈ 𝔻) (hq : q ∈ 𝔻) :
    pseudoHyp p q ≤ (‖p‖ + ‖q‖) / (1 + ‖p‖ * ‖q‖)
theorem pseudoHyp_triangle_strong {u v w : ℂ} (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) (hw : w ∈ 𝔻) :
    pseudoHyp u w ≤ (pseudoHyp u v + pseudoHyp v w) / (1 + pseudoHyp u v * pseudoHyp v w)
theorem add_div_one_add_mul_lt_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) : (a + b) / (1 + a * b) < 1
-- H3, H4, H6
theorem hypDist_nonneg (z w : ℂ) : 0 ≤ hypDist z w
theorem hypDist_comm (z w : ℂ) : hypDist z w = hypDist w z
@[simp] theorem hypDist_self (z : ℂ) : hypDist z z = 0
theorem hypDist_zero_left (w : ℂ) : hypDist 0 w = Real.artanh ‖w‖
theorem hypDist_eq_zero_iff {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) : hypDist z w = 0 ↔ z = w
theorem tanh_hypDist {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    Real.tanh (hypDist z w) = pseudoHyp z w
theorem hypDist_lt_iff {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) (r : ℝ) :
    hypDist z w < r ↔ pseudoHyp z w < Real.tanh r
theorem hypDist_le_iff {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) (r : ℝ) :
    hypDist z w ≤ r ↔ pseudoHyp z w ≤ Real.tanh r
theorem hypDist_triangle {u v w : ℂ} (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) (hw : w ∈ 𝔻) :
    hypDist u w ≤ hypDist u v + hypDist v w
theorem hypDist_mobius {a z w : ℂ} (ha : a ∈ 𝔻) (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    hypDist (mobius a z) (mobius a w) = hypDist z w
theorem hypDist_eq_zero_of_notMem {z w : ℂ} (hz : z ∉ 𝔻) (hw : w ∈ 𝔻) : hypDist z w = 0
-- H5, H7
theorem mem_hypBall {z w : ℂ} {r : ℝ} : w ∈ hypBall z r ↔ w ∈ 𝔻 ∧ hypDist z w < r
theorem hypBall_subset_disc (z : ℂ) (r : ℝ) : hypBall z r ⊆ 𝔻
theorem hypBall_eq_pseudoBall {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    hypBall z r = {w ∈ 𝔻 | pseudoHyp z w < Real.tanh r}
theorem continuousOn_pseudoHyp {z : ℂ} (hz : z ∈ 𝔻) : ContinuousOn (pseudoHyp z) 𝔻
theorem isOpen_hypBall (z : ℂ) (r : ℝ) : IsOpen (hypBall z r)
theorem self_mem_hypBall {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 < r) : z ∈ hypBall z r
theorem hypBall_eq_image_mobius {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    hypBall z r = mobius z '' ball 0 (Real.tanh r)
theorem norm_sub_sq_sub_sq_mul_norm_one_sub_sq (z w : ℂ) (t : ℝ)
    (hA : 1 - t ^ 2 * ‖z‖ ^ 2 ≠ 0) :
    ‖w - z‖ ^ 2 - t ^ 2 * ‖1 - conj z * w‖ ^ 2 =
      (1 - t ^ 2 * ‖z‖ ^ 2) *
        (‖w - (((1 - t ^ 2) / (1 - t ^ 2 * ‖z‖ ^ 2) : ℝ) : ℂ) * z‖ ^ 2 -
          (t * (1 - ‖z‖ ^ 2) / (1 - t ^ 2 * ‖z‖ ^ 2)) ^ 2)
theorem pseudoBall_eq_ball {z : ℂ} (hz : z ∈ 𝔻) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    {w ∈ 𝔻 | pseudoHyp z w < t} =
      ball ((((1 - t ^ 2) / (1 - t ^ 2 * ‖z‖ ^ 2) : ℝ) : ℂ) * z)
        (t * (1 - ‖z‖ ^ 2) / (1 - t ^ 2 * ‖z‖ ^ 2))
theorem hypBall_eq_ball {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 ≤ r) :
    hypBall z r =
      ball ((((1 - Real.tanh r ^ 2) / (1 - Real.tanh r ^ 2 * ‖z‖ ^ 2) : ℝ) : ℂ) * z)
        (Real.tanh r * (1 - ‖z‖ ^ 2) / (1 - Real.tanh r ^ 2 * ‖z‖ ^ 2))
-- H8
theorem exp_two_mul_lt_nine {r : ℝ} (hr1 : r ≤ 1) : Real.exp (2 * r) < 9
theorem div_five_le_tanh {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : r / 5 ≤ Real.tanh r
theorem tanh_div_one_sub_tanh_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.tanh r / (1 - Real.tanh r) ≤ 9 * r
theorem hypBall_subset_ball {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    hypBall z r ⊆ ball z (18 * r * (1 - ‖z‖))
theorem ball_subset_hypBall {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ball z (r * (1 - ‖z‖) / 10) ⊆ hypBall z r
```

---

## 4. Basic definitions (`Basic.lean`): Lean statements

```lean
def lap (φ : ℂ → ℝ) (z : ℂ) : ℝ
theorem laplacian_eq_four_mul_lap (φ : ℂ → ℝ) (z : ℂ) :
    Laplacian.laplacian φ z = 4 * lap φ z
def IsSeparated (Γ : Set ℂ) : Prop
def mobius (z ζ : ℂ) : ℂ
theorem pseudoHyp_eq_norm_mobius (z ζ : ℂ) : pseudoHyp z ζ = ‖mobius z ζ‖
def IsDiskSeparated (Γ : Set ℂ) : Prop
def invLap (φ : ℂ → ℝ) (z : ℂ) : ℝ
def invDensity (ζ : ℂ) : ℝ
```

---

## 5. Dependencies

### Inside M01 (Lean imports)

```
Defs (M00)
 └─ Basic
     ├─ Polar
     │   ├─ LocalEstimates
     │   └─ Separated
     ├─ Wirtinger
     ├─ Pompeiu        ← Wirtinger, Polar
     ├─ Weyl           ← Wirtinger, Polar, LocalEstimates, Pompeiu
     └─ DiscGeometry   ← Wirtinger, Polar, Separated
         └─ Hyperbolic
```

### Mathematical dependencies of the new lemmas

- **H1**:
  - `Real.tanh_eq_sinh_div_cosh`, `Real.sinh_add`, `Real.cosh_add`, `Real.cosh_pos`, `Real.tanh_eq`;
  - `Real.tanh_artanh`, `Real.artanh_tanh`.
- **H2**:
  - G2 `one_sub_normSq_mobius` and `norm_one_sub_conj_mul_le` (BOC M15, copied);
  - G5 `pseudoHyp_mobius`, `mobius_self`, `pseudoHyp_zero_left/right`, `mobius_mem_disc`.
- **H3**:
  - H1, H2;
  - `Real.artanh_nonneg`, `Real.artanh_eq_zero_iff`, `Real.artanh_le_artanh`;
  - `pseudoHyp_comm`, `pseudoHyp_self`, `one_sub_conj_mul_ne_zero_of_mem`.
- **H4**: `Real.artanh_lt_artanh_iff`, `Real.artanh_le_artanh_iff`, `Real.neg_one_lt_tanh`, `Real.tanh_lt_one`.
- **H5**:
  - H4;
  - `norm_one_sub_conj_mul_pos`, `ContinuousOn.isOpen_inter_preimage`, `isOpen_const`;
  - `norm_one_sub_conj_mul_sq_sub`, used for the case `z ∉ 𝔻`.
- **H6**: `pseudoHyp_mobius`.
- **H7**:
  - H4, `mobius_mobius`, `mobius_mem_disc`, `pseudoHyp_eq_norm_mobius`;
  - for the explicit form: an algebraic identity in `re`/`im`, then `sq_lt_sq₀`.
- **H8**:
  - H5;
  - G7 `ball_subset_pseudoBall`, `pseudoBall_subset_ball` (BOC M15, copied);
  - `Real.exp_one_lt_three`, `Real.add_one_le_exp`.

### Mathlib dependencies of the copied files

See the corresponding BOC blueprints:
- M01: `fderiv` calculus, symmetric second derivatives, integration by parts;
- M02: `Complex.lintegral_comp_polarCoord_symm`;
- M03: `DiffContOnCl.circleAverage`, Cauchy estimates;
- M04: `Set.ncard`, `lintegral_tsum`;
- M05: convolution, differentiation under the integral, Fubini;
- M06: `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, removable singularities;
- M15: `integral_image_eq_integral_abs_det_fderiv_smul`.

---

## 5a. Interface (reconciled)

The scaffold adds one M01 file, `Foundations/HyperbolicExtra.lean` (proofs `sorry`; `hypArea` is
a real definition). It contains the M01-type statements that later docs assume and that
`Hyperbolic.lean` does not state:
- `hypArea` (the shared hyperbolic area measure, M11's name and formula; used by M08, M09, M11) and `hypArea_hypBall` (M08 §4.1);
- `hypDist_radial`, `hypBall_zero`, `continuousOn_hypDist` (assumed by M03 §4.2);
- `ball_subset_hypBall_tanh`, `hypBall_subset_ball_tanh`: M03 §4.2 assumed these under the names `ball_subset_hypBall`, `hypBall_subset_ball`, which `Hyperbolic.lean` already uses for the `r ≤ 1` forms with constants `1/10` and `18`. The existing statements are unchanged; the `tanh` forms get new names;
- the disc geometry lemmas of M08 §2.2 (`norm_sub_le_of_hypDist_le`, `norm_one_sub_conj_mul_comparable`, `convex_closedHypBall`), moved here from M08.

Assumed names that already exist in a stronger form are not duplicated: `hypDist_nonneg` and `isOpen_hypBall` (no membership hypotheses), `hypBall_eq_pseudoBall` (M04's `hypBall_eq`, which also had `0 < r`).

```lean
/-- The hyperbolic area measure `dm(z) / (1 - |z|²)²` on `𝔻` (shared definition; M11's form). -/
def hypArea : Measure ℂ :=
  (volume.restrict 𝔻).withDensity fun z ↦ ENNReal.ofReal ((1 - ‖z‖ ^ 2)⁻¹ ^ 2)
/-- Hyperbolic area of a hyperbolic disc: `hypArea (D(z, r)) = π sinh² r` (Möbius invariance and
the computation at `0`: `∫_{|w|<t} dm/(1-|w|²)² = π t²/(1 - t²)` with `t = tanh r`). -/
theorem hypArea_hypBall {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 ≤ r) :
    hypArea (hypBall z r) = ENNReal.ofReal (Real.pi * Real.sinh r ^ 2)
theorem hypDist_radial {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {u : ℂ} (hu : ‖u‖ = 1) :
    hypDist (s * u) (t * u) = Real.artanh t - Real.artanh s
theorem hypBall_zero {r : ℝ} (hr : 0 < r) : hypBall 0 r = ball 0 (Real.tanh r)
theorem continuousOn_hypDist : ContinuousOn (fun p : ℂ × ℂ ↦ hypDist p.1 p.2) (𝔻 ×ˢ 𝔻)
theorem ball_subset_hypBall_tanh {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 < r) :
    ball z (Real.tanh r * (1 - ‖z‖ ^ 2) / 2) ⊆ hypBall z r
theorem hypBall_subset_ball_tanh {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 < r) :
    hypBall z r ⊆ ball z (Real.tanh r * (1 - ‖z‖ ^ 2) / (1 - Real.tanh r))
theorem norm_sub_le_of_hypDist_le {c w : ℂ} (hc : c ∈ 𝔻) (hw : w ∈ 𝔻) {s : ℝ}
    (hs : hypDist c w ≤ s) (hs1 : Real.tanh s < 1) :
    ‖w - c‖ ≤ Real.tanh s / (1 - Real.tanh s) * (1 - ‖c‖ ^ 2)
theorem norm_one_sub_conj_mul_comparable {z c ξ : ℂ} (hz : z ∈ 𝔻) (hc : c ∈ 𝔻) (hξ : ξ ∈ 𝔻)
    {s : ℝ} (hs : hypDist c ξ ≤ s) :
    ‖1 - conj z * ξ‖ ≤ Real.exp (2 * s) * ‖1 - conj z * c‖ ∧
      ‖1 - conj z * c‖ ≤ Real.exp (2 * s) * ‖1 - conj z * ξ‖
theorem convex_closedHypBall {c : ℂ} (hc : c ∈ 𝔻) (s : ℝ) :
    Convex ℝ {w | w ∈ 𝔻 ∧ hypDist c w ≤ s}
```

## 6. Notes

- **Laplacian.** RMI's `IsSubharmonicWeight` uses `Laplacian.laplacian`. The copied `lap` lemmas (`lap_comp_normSq`, `lap_log_normSq`, `lap_comp_holomorphic`, `integral_mul_lap`, …) transfer through `laplacian_eq_four_mul_lap`. Example: `Δ log|z|² = 0` off `0`, and `Δ(α|z|²) = 4α`.
- **`hypBall` for `z ∉ 𝔻`.** By H5, `hypBall z r ∈ {𝔻, ∅}`. RMI's statements quantify over `z ∈ 𝔻` (`IsLocallyDoublingDisc`), so this junk case never matters. It is recorded only to make `isOpen_hypBall` unconditional.
- **Measurability.** `hypBall z r` is open, hence measurable. `measurableSet_pseudoBall` (copied) covers the pseudo-hyperbolic discs.
