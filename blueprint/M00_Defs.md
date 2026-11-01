# M00 — Definitions and main statements

**Lean:**
- `OrtegaCerdaMultipliers/Defs.lean` (definitions; imports only Mathlib, copied verbatim into `Challenge.lean`);
- `comparator/statements.lean` (the main statements).

**Depends on:** Mathlib only.

## 1. Definitions

| Lean | Paper | Notes |
|---|---|---|
| `dbar f z = ½(∂ₓf + i ∂ᵧf)` | `∂̄` | Same as in the companion BOC project. |
| `IsWeakDbarSol Ω u g` | "`u` is a solution of `∂̄u = g`" | Distributional: `u, g ∈ L¹_loc(Ω)` and `∫ u ∂̄α = −∫ g α` for test `α` supported in `Ω`. The paper's solutions are explicit integrals that are locally integrable. |
| `IsSubharmonicWeight Ω φ μ` | "`φ` subharmonic in `Ω` with Laplacian `Δφ = μ`" | See §2. |
| `𝔻`, `pseudoHyp`, `hypDist = artanh ∘ pseudoHyp`, `hypBall` | the disc with "hyperbolic distance", "hyperbolic disk `D(z,r)`" | The paper does not fix a normalisation. Changing it rescales radii. Every hypothesis has the form "for some `r`" or "radius `< 1`", and the latter is equivalent under rescaling by the doubling property. So the choice does not matter. |
| `IsLocallyDoubling μ` | locally doubling (p. 359) | `μ(B(z,2r)) ≤ C μ(B(z,r))` whenever `2r < 1`. This matches "for all balls `B` of radius smaller than 1, `B` the double of `B′`". |
| `IsDoubling μ` | doubling (Theorem 1, as cited from [Chr91]) | All radii. |
| `IsLocallyDoublingDisc μ` | locally doubling with respect to hyperbolic distance (Theorem 2) | Hyperbolic balls in `𝔻`. |
| `lineInterval`, `IsLocallyDoublingLine μ` | "`Δφ` is a locally doubling measure supported in the real line" (Theorems 3, 5) | Doubling with respect to intervals of `ℝ`, and `μ` carried by `ℝ`. A measure carried by a line is never doubling for discs of `ℂ`, so the paper must mean intervals. |
| `massRadius`, `massRadiusDisc`, `massRadiusLine` | `ρ(z)`: the radius with `μ(B(z,ρ(z))) = 1` (p. 361) | Defined as `sInf {r > 0 : μ(B(z,r)) ≥ 1}`. For locally doubling `μ` with the mass condition, `r ↦ μ(B(z,r))` is continuous and strictly increasing, so this is the paper's `ρ(z)` (M03). |
| `edistSet`, `hypDistSet` | `d(z, Λ)` | `ℝ≥0∞`-valued `⨅`, equal to `∞` for `Λ = ∅`. Real `infDist` would give the junk value `0`. |
| `discMeasure = dm/(1−|z|²)` on `𝔻` | the measure in Theorem 2 | |
| `IsTwoSidedCarleson`, `IsWeakDbarSolMeasure`, `TheoremOCS` | Definition p. 358; the theorem of [OCS99] quoted on p. 375 | See §4. |

## 2. Weights

The paper's weights are subharmonic functions `φ` whose Riesz measure `Δφ` (standard Laplacian) is locally doubling. Mathlib has no subharmonic functions or Riesz measures. We use the pair `(φ, μ)` with:
- `φ` continuous on the open set `Ω`;
- `μ` a measure, finite on compact subsets of `Ω`, carried by `Ω`;
- `∫ φ Δχ dm = ∫ χ dμ` for every real `χ ∈ C_c^∞(Ω)`.

Both integrals are genuine (no junk values):
- `φ Δχ` is continuous with compact support in `Ω`;
- `χ` is bounded with compact support and `μ` is finite there.

**Fidelity.**
- **Formal ⇒ paper.** A continuous function with positive distributional Laplacian is subharmonic: its averages over circles increase. So every formal weight is a paper weight.
- **Paper ⇒ formal.** Conversely, if `φ` is subharmonic with locally doubling Riesz measure, then `φ` is continuous. Write `φ = (1/2π)∫ log|z−ζ| dμ(ζ) + h` locally. The potential is continuous by [Chr91, Lemma 2.3]: `∫_{B(z,R)} log(R/|z−ζ|) dμ(ζ) ≲ μ(B(z,R))`, uniformly for `z` in a compact set, which together with dominated convergence gives continuity. Its distributional Laplacian is `μ`.

So for the class of weights in the theorems, the formal hypothesis is equivalent to the paper's. The implication "paper ⇒ formal" (continuity) is not formalized: it would need the Riesz decomposition of an arbitrary subharmonic function. This is recorded as a divergence in `formalization.yaml`.

`μ` is a positive measure, so `φ` is subharmonic. The hypothesis "carried by `Ω`" only normalises `μ`: the identity determines `μ` on `Ω`, and any `μ` can be replaced by `μ.restrict Ω`.

## 3. Main statements (`comparator/statements.lean`)

### Theorem 4 (`theorem4_disc`, `theorem4_plane`)
**Paper (p. 363):** there is a holomorphic `h` with zero set `Λ` and `(d(z,Λ)/ρ(z))^M ≲ |h|e^{-ψ} ≲ d(z,Λ)/ρ(z)`.

**Formal additions.**
- **`h ≢ 0`** (`∃ z₀, h z₀ ≠ 0`). Without it, `h ≡ 0` satisfies both bounds (`Λ = Ω`, so `d = 0`) and the statement would be vacuous.
- **Distances in `ℝ≥0∞`.** `hypDistSet` is the hyperbolic distance in `𝔻` (the paper: "the distance in the appropriate metric"). The ratio `d/ρ` and the power `M` are computed in `ℝ≥0∞`; `ρ(z) > 0` is a theorem (M03), so the division is genuine.

### Proposition 2 (`prop2_disc`, `prop2_plane`)
**Paper (p. 369):** multipliers `h₁, …, h_n` as in Theorem 4 with `E_{h₁} ∩ … ∩ E_{h_n} = ∅`, where `E_h = ⋃_{λ ∈ Z(h)} D(λ, ερ(λ))`.

**Formal version.** It states what the proof of Theorem 2 uses:
- every `z` lies outside some `E_{h_i}`;
- outside `E_{h_i}`, `|h_i| ≃ e^ψ`.

The second item is the remark after Theorem 4, and it is part of the conclusion here. The full Theorem-4 bounds for each `h_i` are not restated.

### Theorem 2 (`theorem2`, `theorem2_printed`)
**Paper (p. 357):**
- `∫_𝔻 |u|^p e^{-φ} dm/(1−|z|²) ≲ ∫_𝔻 |f(1−|z|²)|^p e^{-φ} dm/(1−|z|²)` for `p ∈ [1,∞)`;
- `sup|u|e^{-φ} ≲ sup|f(ζ)(1−|ζ|)|e^{-φ(ζ)}`.

The proof (p. 373) only gives the `L^p` part for `p = 1` in this normalisation. In the normalisation `‖u e^{-φ}‖_{L^p}`, the one used by Theorem 1, the same construction gives all `p ∈ [1,∞]` at once (Schur test). We state:
- **`theorem2`.** One solution `u` with `‖u e^{-φ}‖_{L^p(dm/(1−|z|²))} ≤ C ‖f(1−|z|²)e^{-φ}‖_{L^p(dm/(1−|z|²))}` for every `p ∈ [1,∞]`.
  - `p = ∞` is the sup estimate, as essential suprema; the factor `1−|ζ|` versus `1−|ζ|²` changes `C` by at most 2.
  - **Admissible data:** `f` measurable with the right-hand side finite for *some* `p`. This guarantees the defining integral converges a.e. and `f ∈ L¹_loc(𝔻)`.
  - **Constant:** `C` is uniform in `p`.
- **`theorem2_printed`.** For each `p ∈ [1,∞)`, the printed `L^p` estimate with weight `e^{-φ}`, and a solution `u` that may depend on `p`. It follows from `theorem2` applied to `φ/p`, which satisfies the hypotheses with a larger mass radius.

### Theorem 1 (`theorem1`, `theorem1_christ`)
**Paper (p. 356):** `‖ue^{-φ}‖_p ≲ ‖fe^{-φ}‖_p` for all `p ∈ [1,∞]`. It is stated for doubling `Δφ`, and the paper remarks (p. 357) that the proof works for locally doubling `Δφ`.
- **`theorem1`** is the locally doubling version.
- **`theorem1_christ`** is the printed one; doubling ⇒ locally doubling.
- Admissibility and uniformity in `p` are as for Theorem 2.

### Proposition 1 (`prop1`)
**Paper (p. 359):** `|k(z,ζ)| ≃ e^{-ε|z−ζ|²}/|z−ζ|`. Only `≲` is stated:
- the kernel `κ′(z,ζ) = Σ h_i(z) χ_{Ω_i}(ζ)/h_i(ζ) · …` vanishes when `z` is a zero of `h_i` and `ζ ∈ Ω_i`;
- so the lower bound is false in general (NOTEBOOK).

### Theorem 5 (`theorem5`)
**Paper (p. 374):** an entire function `f` with zero set in `ℝ` and, for every `ε > 0`, `|f| ≃ e^φ` off `⋃ D(λ_n, ερ(λ_n))`.
- **Constants** may depend on `ε`.
- **Nonvanishing:** `f ≢ 0` is added for non-vacuity.
- **Exceptional discs** are Euclidean discs `|z−λ| ≥ ερ(λ)`, as printed.

### Theorem 3 (`theorem3 : TheoremOCS → …`)
**Paper (p. 358):** `∂̄u = μ` for a compactly supported complex measure with `e^{-φ}d|μ|` two-sided Carleson. The conclusions are:
- `limsup_{z→∞} |u(z)|e^{-φ(z)} = 0`;
- `|u(x)|e^{-φ(x)} ≤ C(1 + ∫_{|z−x|<1} d|μ|(z)/|x−z|)` for `x ∈ ℝ`;
- `C` does not depend on the support.

**Formal choices.**
- **The data:** the complex measure is `σ ν` with `ν = |μ|` finite, carried by a compact `L`, and `|σ| = 1`.
- **The Carleson constant** `K` is fixed before `C`, since `C` "does not depend on the support of `μ`". `C` depends on `φ` and `K`.
- **Regularity of `u`.** `u` is required to be holomorphic off `L`. The pointwise bound is asserted only for `x ∈ ℝ \ L`.
  - Pointwise values of an `L¹_loc` solution are otherwise meaningless: changing `u` on the null set `ℝ` would make the bound vacuous.
  - Off `L` the solution is holomorphic, so its values are determined.
  - On `L ∩ ℝ` no meaningful pointwise statement is possible without further regularity.
- **`TheoremOCS`** is the [OCS99] theorem in the same form, as a hypothesis. It must be *implied by* the published theorem (to be checked by review, M14).

## 4. Checks performed
- All statements typecheck against `Defs.lean`. Check: `lake env lean` on `Defs` plus `statements.lean`, with proofs `sorry`.
- Review for falsity and vacuity is pending (blueprint review round).
