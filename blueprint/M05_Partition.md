# M05 — Lemma 4 and Claim 2: partitions into pieces of mass `N`

**Lean files:**
- `OrtegaCerdaMultipliers/Partition/Rectangles.lean`: rectangle combinatorics for an arbitrary measure `ν` on `ℂ`:
  - `rect`, `IsRectLE`, `midThird`, `swapReIm`;
  - continuity of masses, the coarse strip cuts, slab reverse doubling, `rect_inner_outer`;
  - the core bisection-and-slicing theorem `exists_rect_partition`.
- `Partition/Cayley.lean`: Cayley coordinates for 𝔻:
  - `cayley`, `cayleyInv`, `cayleyPre`, `discBox`;
  - the isometry identity, null level sets, inner/outer hyperbolic balls, Euclidean doubling of `cayley_*(μ|𝔻)`.
- `Partition/Lemma4.lean`: `IsMassPartition`, `lemma4_plane`, `lemma4_disc`, `lemma4_line`.
- `Partition/Properties.lean`: Claim 2 and the facts M08/M09/M13 consume:
  - bounded number of near pieces and of neighbours;
  - far comparability;
  - Euclidean size in 𝔻;
  - sums over pieces versus integrals.

**Paper:**
- pp. 363–365: Lemma 4, the Remark, its proof, Claim 2.
- The partition is used on pp. 365–369 (Theorem 4, M08), p. 369 (Proposition 2, M09) and p. 375 (Theorem 5, M13).

**Depends on:**
- M03: everything on ρ, Lemma 1 (`doubling_upTo_*`, `*_le_rpow`, `rpow_le_*`), Lemma 2 (`measure_eq_zero_of_isPorous_plane`, `measure_inter_disc_eq_zero_of_isPorous`, `isPorous_line`, `isPorous_sphere`, `IsPorous.mono`), `continuous_measure_*`, `claim1_*`, `measure_*_massRadius*_bounds`, `exists_radius_lt_measure_*`, `IsLocDoublingM.smul`, `massRadiusM_inv_smul`, `lipschitzWith_massRadius*`/`abs_massRadiusDisc_sub_le`.
- M01: `pseudoHyp`, `hypDist`, `ball_subset_hypBall`, `hypBall_subset_ball`.
- Mathlib:
  - existence and induction: `intermediate_value_Icc`, `intermediate_value_Ioo`, `Nat.strong_induction_on`, `finSumFinEquiv`, `Int.exists_greatest_of_bdd`;
  - countability and reindexing: `nonempty_equiv_of_countable` (`ι ≃ ℕ`);
  - measures: `Measure.map_apply`, `measure_union`, `measure_biUnion_finset`, `Monotone.continuousAt_iff_leftLim_eq_rightLim`;
  - integrals: `lintegral_biUnion`, `setLIntegral_const`, `setLIntegral_mono'`;
  - counting: `Set.encard_le_coe_iff_finite_ncard_le`;
  - special functions: `Real.artanh`, `Real.tanh`.

---

## 0. Design decisions

### 0.1 What the later modules really need from the partition
Reading pp. 365–369 and 375 (and the coordinator's plan of counting pieces by area), the partition must provide the following.
1. **Basic structure:** pieces `R_i` that are measurable, pairwise disjoint, countable, cover Ω, and have `μ(R_i) = N` exactly (moments are matched with `N` points of weight 1).
2. **Upper size bound** (Claim 2, first bullet): `d(z,w) ≤ A ρ(z)` for `z, w ∈ R_i`. The *lower* bound is automatic from `μ(R_i) = N ≥ 1` (`claim2_lower_*`).
3. **Fatness:** `R_i` contains the ball `B(c_i, a ρ(c_i))` for some `c_i ∈ R_i`. This replaces "bounded eccentricity". It is what area counting needs: `encard_le_of_disjoint_*` in M03. M06 also uses it to place `κ(R)`.
4. Only boundedly many pieces meet `B(z, Kρ(z))`; only boundedly many neighbours (M09's colouring).
5. **Far comparability:** if `R_i ∩ B(z, ηρ(z)) = ∅` then `d(z,w') ≤ C d(z,w)` for `w, w' ∈ R_i` (`|z − w| ≃ |z − ζ|`, p. 367).
6. `ρ(ζ) ≃ ρ(λ₀)` for `ζ, λ₀ ∈ R_i`, i.e. Claim 1. In 𝔻, also the Euclidean size `|ζ − λ₀| ≲ (1 − |ζ|²) ρ(ζ)`.
7. Sums of `N·f(λ₀^i)` over pieces compared with `∫ f dμ`.

All of this is packaged as `IsMassPartition μ Ω d ρ N a A R` with `R : ℕ → Set ℂ` (fields 1–3), plus the lemmas of `Properties.lean` (4–7). We use ℕ-indexing: the constructions give a countable infinite index type, reindexed by `nonempty_equiv_of_countable`.

### 0.2 Disc: horocyclic boxes, not polar rectangles
The paper uses polar rectangles with "hyperbolic eccentricity". Two problems:
- **(a) The centre.** Polar rectangles degenerate at `0`, and the central disc is not treated.
- **(b) Large scales.** For large `R` the pieces are hyperbolically large, and polar eccentricity is meaningless there. A polar rectangle of radial length `a` has its outer arc `≈ e^{2a}` times its inner arc. The bisection's invariant "ratio ≤ 3" is not preserved by radial cuts.

**Fix.** Map 𝔻 to ℍ by the Cayley map and use **Euclidean rectangles in ℍ-coordinates**:
`discBox x₁ x₂ y₁ y₂ = {z ∈ 𝔻 : cayley z ∈ [x₁,x₂) × [y₁,y₂)}`. These are regions bounded by two horocycles and two geodesics through `1`. Advantages:
- No point of 𝔻 is special: `cayley` is a bijection `𝔻 → ℍ`, and `0` is just `i`.
- The rectangle combinatorics is **literally the plane's**, applied to `ν := cayley_*(μ|𝔻)`. The hyperbolic geometry enters only through four facts (§3.7):
  1. level sets of `Re cayley`, `Im cayley` are circles or lines, hence null;
  2. inner/outer hyperbolic balls of *admissible* rectangles (`y₂ − y₁ ≤ Λ y₁`, ratio `≤ L`);
  3. `ν` is Euclidean-doubling below the scale `Im w / 16`;
  4. the coarse rows `[Λ_c^j, Λ_c^{j+1})` cut into squares contain hyperbolic balls of radius `R`.

### 0.3 Mass `N`
The core construction produces pieces of mass 1 for any measure with the mass condition. For mass `N`, apply it to `μ' := N⁻¹ • μ`:
- `μ'` is locally doubling with the same constant (`IsLocDoublingM.smul`);
- `μ'` satisfies the mass condition at the radius `r_N` given by `exists_radius_lt_measure_*` with `p = N`;
- `ρ_μ ≤ ρ_{μ'} ≤ C_N ρ_μ` (`massRadiusM_inv_smul`).

The paper does the same ("use `σ = μ/N`").

### 0.4 Bisection: the middle-third rule
The paper uses an auxiliary sub-rectangle `R'` of mass exactly 1 and the alternative "`h > w/3` ⇒ `μ(R) ≤ C`". This is replaced by an equivalent but simpler rule:
- If `μ(Q) > C₀`, the **middle third** of `Q` along its longer side has mass `> 1`. This is by doubling, via an inner ball of the middle third and an outer ball of `Q` (`hC₀`).
- So `F(t) = μ([x₁,t) × [y₁,y₂))` increases by more than 1 on the middle third, and crosses the integer `⌊F(x₁ + w/3)⌋ + 1` there.

Both halves get positive integer mass and side ratio `≤ 3` (§3.5).

The paper's "`μ(R) ≤` the doubling constant `C`" is not right as stated: rectangles are not balls. The correct threshold is `C₀ = C₁(scale)^5` (plane) or `C₁^{⌈log₂ A⌉}` (disc).

### 0.5 The final slicing: the gap behind "we use Lemma 1" (p. 365)
A block of mass `k ≤ C₀` is cut into `k` slices of mass 1 along its longer side. The paper says all slices "will be essentially of the same proportion (we use Lemma 1)". Lemma 1 is about balls, and a thin slab is not comparable to a ball. What is needed is **reverse doubling for slabs**, `slab_reverse_doubling_right/left` (§3.3):

> a slab `[u, u+s) × [y₁, y₂)` with `s ≤ y₂ − y₁` has mass `≤ 2C_E` times that of the next slab `[u+s, u+3s) × [y₁, y₂)`.

It is proved by covering the slab with `⌈l/s⌉` balls of radius `s` and shifting each by `2s`. Iterating `k₀` times, with `(1 + 1/(2C_E))^{k₀} > C₀`, shows that a slice of mass 1 inside a block of mass `≤ C₀` has width `≥ 3^{-k₀} min(1/4, κ) w`. Hence the slices have side ratio `≤ L` (§3.5, Case B).

Bounded eccentricity of the slices is needed for fatness (0.1.3), and hence for area counting.

---

## 1. The paper (pp. 363–365)

- **Lemma 4.** "Assume that μ is a locally doubling measure in Ω with `μ(D(z,R)) > 1`. Given any `N ∈ ℕ` there is a partition of Ω into rectangles `{R_i}` such that `μ(R_i) = N` and … `sup L_i/l_i = L(N) < +∞`." Remark: in the disc, "rectangles in polar coordinates"; "basically the partition theorem from [Yul85]".
- **Proof (summary):**
  1. strips of width `R`, sliced into integer-mass rectangles of length in `[R, 2R]` (annuli and polar rectangles in the disc);
  2. bisect while the mass exceeds the doubling constant `C`, keeping ratio `≤ 3`;
  3. cut each piece of mass `≤ C` into mass-1 pieces "along the direction of the longest side … we use Lemma 1".
- **Claim 2.**
  - "The ratio between the diameter of `R` and `ρ(z)` for any `z ∈ R` is bounded above and below."
  - "For any `K > 0` there is `C_K` such that whenever `KR_i ∩ KR_j ≠ ∅` the ratio between the diameters of `R_i` and `R_j` is bounded by `C_K`."

---

## 2. Formal statements (all typecheck; proofs `sorry`)

Same check file as M03 (`scratchpad/m0305_check.lean`). New definitions:
- `rect`, `IsRectLE`, `midThird`, `swapReIm`;
- `cayley`, `cayleyInv`, `cayleyPre`, `discBox`;
- the structure `IsMassPartition`.

### 2.1 `Partition/Rectangles.lean`
```lean
/-! ####################################################################
## M05 — `Partition/Rectangles.lean`: rectangle combinatorics for a measure on `ℂ`
#################################################################### -/

/-- The half-open coordinate rectangle `[x₁, x₂) × [y₁, y₂)`. -/
def rect (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ := {w : ℂ | w.re ∈ Ico x₁ x₂ ∧ w.im ∈ Ico y₁ y₂}

/-- Non-degenerate rectangle with side ratio at most `L`. -/
def IsRectLE (L x₁ x₂ y₁ y₂ : ℝ) : Prop :=
  x₁ < x₂ ∧ y₁ < y₂ ∧ x₂ - x₁ ≤ L * (y₂ - y₁) ∧ y₂ - y₁ ≤ L * (x₂ - x₁)

/-- The middle third of a rectangle along its longer side. -/
def midThird (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ :=
  if y₂ - y₁ ≤ x₂ - x₁ then rect (x₁ + (x₂ - x₁) / 3) (x₂ - (x₂ - x₁) / 3) y₁ y₂
  else rect x₁ x₂ (y₁ + (y₂ - y₁) / 3) (y₂ - (y₂ - y₁) / 3)

theorem measurableSet_rect (x₁ x₂ y₁ y₂ : ℝ) : MeasurableSet (rect x₁ x₂ y₁ y₂) := sorry

/-- Continuity of the mass of a rectangle in its right edge. -/
theorem continuous_measure_rect_right {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {x₁ y₁ y₂ : ℝ} (hfin : ∀ x₂, ν (rect x₁ x₂ y₁ y₂) < ∞) :
    Continuous fun x₂ : ℝ ↦ ν (rect x₁ x₂ y₁ y₂) := sorry

/-- Coarse step: slicing a horizontal strip into blocks of integer mass and width in `[h, 2h]`. -/
theorem exists_strip_cuts {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {y₁ y₂ h : ℝ} (hh : 0 < h) (hfin : ∀ a b : ℝ, ν (rect a b y₁ y₂) < ∞)
    (hmass : ∀ a : ℝ, 1 ≤ ν (rect a (a + h) y₁ y₂)) :
    ∃ x : ℤ → ℝ, StrictMono x ∧ (∀ k, h ≤ x (k + 1) - x k ∧ x (k + 1) - x k ≤ 2 * h) ∧
      (∀ t : ℝ, ∃ k, t ∈ Ico (x k) (x (k + 1))) ∧
      ∀ k, ∃ n : ℕ, 1 ≤ n ∧ ν (rect (x k) (x (k + 1)) y₁ y₂) = n := sorry

/-- Slab reverse doubling (the missing argument behind "we use Lemma 1", p. 365): a vertical slab
of width `s` in a rectangle has a neighbouring slab of comparable mass, provided `s` is at most
the height and the scale `σ` at which `ν` is Euclidean doubling. -/
theorem slab_reverse_doubling_right {ν : Measure ℂ} {C_E u s y₁ y₂ : ℝ} (hs : 0 < s)
    (hsl : s ≤ y₂ - y₁)
    (hED : ∀ w ∈ rect (u + s) (u + 3 * s) y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ s →
      ν (ball w (4 * r)) ≤ ENNReal.ofReal C_E * ν (ball w (r / 2))) :
    ν (rect u (u + s) y₁ y₂) ≤ ENNReal.ofReal (2 * C_E) * ν (rect (u + s) (u + 3 * s) y₁ y₂) :=
  sorry

theorem slab_reverse_doubling_left {ν : Measure ℂ} {C_E u s y₁ y₂ : ℝ} (hs : 0 < s)
    (hsl : s ≤ y₂ - y₁)
    (hED : ∀ w ∈ rect (u - 2 * s) u y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ s →
      ν (ball w (4 * r)) ≤ ENNReal.ofReal C_E * ν (ball w (r / 2))) :
    ν (rect u (u + s) y₁ y₂) ≤ ENNReal.ofReal (2 * C_E) * ν (rect (u - 2 * s) u y₁ y₂) := sorry

/-- The coordinate swap `x + iy ↦ y + ix`, used to reduce vertical cuts to horizontal ones. -/
def swapReIm (z : ℂ) : ℂ := I * conj z

theorem preimage_swapReIm_rect (x₁ x₂ y₁ y₂ : ℝ) :
    swapReIm ⁻¹' rect x₁ x₂ y₁ y₂ = rect y₁ y₂ x₁ x₂ := sorry

/-- Euclidean inner/outer balls of a rectangle of side ratio `≤ L`. -/
theorem rect_inner_outer {L : ℝ} (hL : 1 ≤ L) {x₁ x₂ y₁ y₂ : ℝ} (h : IsRectLE L x₁ x₂ y₁ y₂) :
    ∃ (p : ℂ) (r : ℝ), 0 < r ∧ 6 * r ≤ max (x₂ - x₁) (y₂ - y₁) ∧
      ball p r ⊆ midThird x₁ x₂ y₁ y₂ ∧ rect x₁ x₂ y₁ y₂ ⊆ ball p (6 * L * r) := sorry

/-- The number of slab doublings in the proof of `exists_rect_partition` (M05 §3.5):
`k₀ = ⌈log(C₀ + 1) / log(1 + η_s)⌉₊` with `η_s = 1/(2 max C_E 1)`. -/
def rectRatioK₀ (C₀ : ℕ) (C_E : ℝ) : ℕ :=
  ⌈Real.log (C₀ + 1) / Real.log (1 + 1 / (2 * max C_E 1))⌉₊
/-- The explicit side-ratio bound of `exists_rect_partition` (M05 §3.5): `L = max 3 (1/c_*)`
with `c_* = 3^{-k₀} min(1/4, κ)`.  It depends only on `C₀`, `C_E` and `κ`, not on the measure. -/
def rectRatioBound (C₀ : ℕ) (C_E κ : ℝ) : ℝ :=
  max 3 (3 ^ rectRatioK₀ C₀ C_E / min (1 / 4) κ)
theorem one_le_rectRatioBound (C₀ : ℕ) (C_E κ : ℝ) : 1 ≤ rectRatioBound C₀ C_E κ  -- proved

/-- **Bisection + slicing** (the core of Lemma 4).  `P` is a hereditary admissibility predicate,
`C₀` is such that admissible good rectangles of mass `> C₀` have middle third of mass `> 1`, and
`ν` is Euclidean doubling at the scale `σ` inside admissible rectangles; then every admissible
good rectangle of integer mass `n ≥ 1` splits into `n` rectangles of mass `1`, each of side ratio
`≤ L` and contained in an admissible good rectangle of mass `≤ C₀`. -/
theorem exists_rect_partition {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    (him : ∀ y : ℝ, ν {w | w.im = y} = 0)
    (P : ℝ → ℝ → ℝ → ℝ → Prop)
    (hP : ∀ x₁ x₂ y₁ y₂ x₁' x₂' y₁' y₂' : ℝ, P x₁ x₂ y₁ y₂ → x₁ ≤ x₁' → x₂' ≤ x₂ → y₁ ≤ y₁' →
      y₂' ≤ y₂ → P x₁' x₂' y₁' y₂')
    (C₀ : ℕ) (hC₀ : ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE 3 x₁ x₂ y₁ y₂ → P x₁ x₂ y₁ y₂ →
      (C₀ : ℝ≥0∞) < ν (rect x₁ x₂ y₁ y₂) → 1 < ν (midThird x₁ x₂ y₁ y₂))
    (σ : ℝ → ℝ → ℝ → ℝ → ℝ) (C_E κ : ℝ) (hκ : 0 < κ)
    (hσ : ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE 3 x₁ x₂ y₁ y₂ → P x₁ x₂ y₁ y₂ →
      κ * max (x₂ - x₁) (y₂ - y₁) ≤ σ x₁ x₂ y₁ y₂ ∧
      ∀ w ∈ rect x₁ x₂ y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ σ x₁ x₂ y₁ y₂ →
        ν (ball w (4 * r)) ≤ ENNReal.ofReal C_E * ν (ball w (r / 2))) :
    ∀ (n : ℕ) (x₁ x₂ y₁ y₂ : ℝ), 1 ≤ n → IsRectLE 3 x₁ x₂ y₁ y₂ →
      P x₁ x₂ y₁ y₂ → ν (rect x₁ x₂ y₁ y₂) = n →
      ∃ q : Fin n → ℝ × ℝ × ℝ × ℝ,
        Pairwise (Function.onFun Disjoint fun i ↦ rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) ∧
        (⋃ i, rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = rect x₁ x₂ y₁ y₂ ∧
        ∀ i, ν (rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = 1 ∧
          IsRectLE (rectRatioBound C₀ C_E κ) (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2 ∧
          ∃ x₁' x₂' y₁' y₂' : ℝ, IsRectLE 3 x₁' x₂' y₁' y₂' ∧ P x₁' x₂' y₁' y₂' ∧
            ν (rect x₁' x₂' y₁' y₂') ≤ C₀ ∧
            rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2 ⊆ rect x₁' x₂' y₁' y₂' := sorry
```

### 2.2 `Partition/Cayley.lean`
```lean
/-! ####################################################################
## M05 — `Partition/Cayley.lean`: horocyclic boxes in `𝔻`
#################################################################### -/

/-- The Cayley map `𝔻 → ℍ`, `z ↦ i(1+z)/(1-z)`. -/
def cayley (z : ℂ) : ℂ := I * (1 + z) / (1 - z)

/-- Its inverse `ℍ → 𝔻`, `w ↦ (w - i)/(w + i)`. -/
def cayleyInv (w : ℂ) : ℂ := (w - I) / (w + I)

/-- The preimage in `𝔻` of a set of the upper half-plane. -/
def cayleyPre (S : Set ℂ) : Set ℂ := {z | z ∈ 𝔻 ∧ cayley z ∈ S}

/-- A horocyclic box: two horocycles and two geodesics through `1`. -/
def discBox (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ := cayleyPre (rect x₁ x₂ y₁ y₂)

theorem cayley_im_pos {z : ℂ} (hz : z ∈ 𝔻) : 0 < (cayley z).im := sorry
theorem cayleyInv_cayley {z : ℂ} (hz : z ∈ 𝔻) : cayleyInv (cayley z) = z := sorry
theorem cayley_cayleyInv {w : ℂ} (hw : 0 < w.im) : cayley (cayleyInv w) = w := sorry
theorem cayleyInv_mem {w : ℂ} (hw : 0 < w.im) : cayleyInv w ∈ 𝔻 := sorry
theorem measurable_cayley : Measurable cayley := sorry

/-- The Cayley map is an isometry onto the half-plane metric. -/
theorem pseudoHyp_cayleyInv {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im) :
    pseudoHyp (cayleyInv w₁) (cayleyInv w₂) = ‖w₁ - w₂‖ / ‖w₁ - conj w₂‖ := sorry

/-- Level sets of `Re ∘ cayley` and `Im ∘ cayley` lie on circles or lines, hence are porous. -/
theorem isPorous_cayley_re (x : ℝ) : IsPorous (cayleyPre {w | w.re = x}) := sorry
theorem isPorous_cayley_im (y : ℝ) : IsPorous (cayleyPre {w | w.im = y}) := sorry

/-- Inner/outer hyperbolic balls of an admissible box (`l ≤ Λ y₁`, side ratio `≤ L`). -/
theorem discBox_inner_outer (Λ L : ℝ) (hΛ : 0 < Λ) (hL : 1 ≤ L) :
    ∃ A D : ℝ, 1 ≤ A ∧ 0 < D ∧ ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ → 0 < y₁ →
      y₂ - y₁ ≤ Λ * y₁ → ∃ p ∈ 𝔻, ∃ β : ℝ, 0 < β ∧ A * β ≤ D ∧
        hypBall p β ⊆ cayleyPre (midThird x₁ x₂ y₁ y₂) ∧
        discBox x₁ x₂ y₁ y₂ ⊆ hypBall p (A * β) := sorry

/-- Euclidean doubling of the push-forward `cayley_* (μ|𝔻)` below the scale `Im w / 16`. -/
theorem euclid_doubling_cayley {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ) :
    ∃ C_E : ℝ, 0 < C_E ∧ ∀ w : ℂ, 0 < w.im → ∀ r : ℝ, 0 < r → r ≤ w.im / 16 →
      (μ.restrict 𝔻).map cayley (ball w (4 * r)) ≤
        ENNReal.ofReal C_E * (μ.restrict 𝔻).map cayley (ball w (r / 2)) := sorry
```

### 2.3 `Partition/Lemma4.lean`
```lean
/-! ####################################################################
## M05 — `Partition/Lemma4.lean`: the partitions and their properties
#################################################################### -/

/-- `R : ℕ → Set ℂ` partitions `Ω` into measurable pieces of `μ`-mass `N`; each piece has
`d`-diameter `≤ A ρ(z)` (any `z` in it) and contains the `d`-ball of radius `a ρ(c)` around one
of its points `c`. -/
structure IsMassPartition (μ : Measure ℂ) (Ω : Set ℂ) (d : ℂ → ℂ → ℝ) (ρ : ℂ → ℝ) (N : ℕ)
    (a A : ℝ) (R : ℕ → Set ℂ) : Prop where
  measurableSet : ∀ i, MeasurableSet (R i)
  pairwise_disjoint : Pairwise (Function.onFun Disjoint R)
  iUnion_eq : ⋃ i, R i = Ω
  measure_eq : ∀ i, μ (R i) = N
  dist_le : ∀ i, ∀ z ∈ R i, ∀ w ∈ R i, d z w ≤ A * ρ z
  inner : ∀ i, ∃ c ∈ R i, {w | w ∈ Ω ∧ d c w < a * ρ c} ⊆ R i

/-- **Lemma 4 (plane).** -/
theorem lemma4_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R))
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (a A L : ℝ) (R : ℕ → Set ℂ), 0 < a ∧ 0 < A ∧ 1 ≤ L ∧
      IsMassPartition μ univ dist (massRadius μ) N a A R ∧
      ∀ i, ∃ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ ∧ R i = rect x₁ x₂ y₁ y₂ := sorry

/-- **Lemma 4 (disc)**: horocyclic boxes (preimages of rectangles under Cayley). -/
theorem lemma4_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (a A L Λ : ℝ) (R : ℕ → Set ℂ), 0 < a ∧ 0 < A ∧ 1 ≤ L ∧ 0 < Λ ∧
      IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R ∧
      ∀ i, ∃ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ ∧ 0 < y₁ ∧ y₂ - y₁ ≤ Λ * y₁ ∧
        R i = discBox x₁ x₂ y₁ y₂ := sorry

/-- **Lemma 4 (line)**: intervals of mass `N`. -/
theorem lemma4_line {μ : Measure ℂ} (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (a A : ℝ) (R : ℕ → Set ℂ), 0 < a ∧ 0 < A ∧
      IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R ∧
      ∀ i, ∃ s t : ℝ, s < t ∧ R i = (fun u : ℝ ↦ (u : ℂ)) '' Ico s t := sorry
```

### 2.4 `Partition/Properties.lean`
```lean
/-! ### Claim 2 and the consequences used by M08/M09 (plane; disc and line analogous) -/

section PartitionProps
variable {μ : Measure ℂ} {N : ℕ} {a A : ℝ} {R : ℕ → Set ℂ}

/-- **Claim 2**, lower bound: a piece is not inside a ball of radius `< ρ(z)` around `z`. -/
theorem claim2_lower_plane (hP : IsMassPartition μ univ dist (massRadius μ) N a A R)
    (hN : 1 ≤ N) (i : ℕ) {z : ℂ} (hz : z ∈ R i) {r : ℝ} (hr : R i ⊆ closedBall z r) :
    massRadius μ z ≤ r := sorry

/-- **Claim 2**, comparability of `ρ` inside a piece (diameters of neighbours, via Claim 1). -/
theorem claim2_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j, ∀ z ∈ R i, ∀ w ∈ R j,
      dist z w ≤ K * max (massRadius μ z) (massRadius μ w) → massRadius μ w ≤ C * massRadius μ z :=
  sorry

/-- Pieces meeting `B(z, Kρ(z))` are boundedly many. -/
theorem finite_near_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀))
    (hP : IsMassPartition μ univ dist (massRadius μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ z : ℂ, {i | ∃ w ∈ R i, dist z w ≤ K * massRadius μ z}.encard ≤ M := sorry

/-- Bounded number of neighbours of a piece. -/
theorem finite_neighbours_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀))
    (hP : IsMassPartition μ univ dist (massRadius μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ i, {j | ∃ z ∈ R i, ∃ w ∈ R j, dist z w ≤ K * massRadius μ z}.encard ≤ M := sorry

/-- For a piece missing `B(z, ηρ(z))`, all its points are at comparable distance from `z`. -/
theorem far_comparable_plane (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀))
    (hP : IsMassPartition μ univ dist (massRadius μ) N a A R) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (i : ℕ), (∀ w ∈ R i, η * massRadius μ z ≤ dist z w) →
      ∀ w ∈ R i, ∀ w' ∈ R i, dist z w' ≤ C * dist z w := sorry

theorem far_comparable_disc (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ 𝔻, ∀ i : ℕ, (∀ w ∈ R i, η * massRadiusDisc μ z ≤ hypDist z w) →
      ∀ w ∈ R i, ∀ w' ∈ R i, hypDist z w' ≤ C * hypDist z w := sorry

theorem finite_near_disc (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ z ∈ 𝔻, {i | ∃ w ∈ R i, hypDist z w ≤ K * massRadiusDisc μ z}.encard ≤ M := sorry

theorem claim2_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j, ∀ z ∈ R i, ∀ w ∈ R j,
      hypDist z w ≤ K * max (massRadiusDisc μ z) (massRadiusDisc μ w) →
        massRadiusDisc μ w ≤ C * massRadiusDisc μ z := sorry

theorem claim2_lower_disc (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R)
    (hN : 1 ≤ N) (i : ℕ) {z : ℂ} (hz : z ∈ R i) {r : ℝ}
    (hr : R i ⊆ {w | w ∈ 𝔻 ∧ hypDist z w ≤ r}) : massRadiusDisc μ z ≤ r := sorry

theorem finite_neighbours_disc (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ i, {j | ∃ z ∈ R i, ∃ w ∈ R j, hypDist z w ≤ K * massRadiusDisc μ z}.encard ≤ M :=
  sorry

/-! Line versions (`Ω = ℝ ⊆ ℂ`, `ρ(z) = massRadiusLine μ z.re`). -/

theorem claim2_lower_line
    (hP : IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R)
    (hN : 1 ≤ N) (i : ℕ) {z : ℂ} (hz : z ∈ R i) {r : ℝ} (hr : R i ⊆ closedBall z r) :
    massRadiusLine μ z.re ≤ r := sorry

theorem finite_near_line (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R₀))
    (hP : IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R)
    (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ x : ℝ, {i | ∃ w ∈ R i, dist (x : ℂ) w ≤ K * massRadiusLine μ x}.encard ≤ M := sorry

theorem far_comparable_line (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R₀))
    (hP : IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (i : ℕ), (∀ w ∈ R i, η * massRadiusLine μ x ≤ dist (x : ℂ) w) →
      ∀ w ∈ R i, ∀ w' ∈ R i, dist (x : ℂ) w' ≤ C * dist (x : ℂ) w := sorry

/-- Euclidean size of the disc pieces. -/
theorem euclid_size_disc (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, ∀ z ∈ R i, ∀ w ∈ R i,
      ‖z - w‖ ≤ C * (1 - ‖z‖ ^ 2) * massRadiusDisc μ z := sorry

/-- Sum over pieces versus integral (generic). -/
theorem IsMassPartition.mass_mul_le_setLIntegral {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) (i : ℕ) {c : ℝ≥0∞} {f : ℂ → ℝ≥0∞}
    (hc : ∀ z ∈ R i, c ≤ f z) : (N : ℝ≥0∞) * c ≤ ∫⁻ z in R i, f z ∂μ := sorry

theorem IsMassPartition.lintegral_biUnion {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) (S : Set ℕ) (f : ℂ → ℝ≥0∞) :
    ∫⁻ z in ⋃ i ∈ S, R i, f z ∂μ = ∑' i : S, ∫⁻ z in R i, f z ∂μ := sorry

theorem IsMassPartition.existsUnique_mem {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) {z : ℂ} (hz : z ∈ Ω) : ∃! i, z ∈ R i := sorry

end PartitionProps
```

---

## 3. Proofs

Notation: `w := x₂ − x₁`, `l := y₂ − y₁`. A *good* rectangle is `IsRectLE 3`.

### 3.1 Rectangles: measurability, additivity, continuity, swap
- **`measurableSet_rect`:** preimages of `Ico` under the continuous `re`, `im`.
- **Additivity.** For `x₁ ≤ x₂ ≤ x₃`: `rect x₁ x₃ = rect x₁ x₂ ∪ rect x₂ x₃`, a disjoint union. Hence `ν(rect x₁ x₃) = ν(rect x₁ x₂) + ν(rect x₂ x₃)` (`measure_union`). Likewise in `y`. All masses below are finite (`hfin`), so differences are taken in `ℝ` after `toReal`.
- **`continuous_measure_rect_right`.** `f(t) := ν(rect x₁ t y₁ y₂)` is monotone. Then:
  - `leftLim f t = ν(⋃_{t'<t} rect x₁ t') = f t`;
  - `rightLim f t = ν(⋂_{t'>t} rect x₁ t') = ν(rect x₁ t ∪ ({re = t} ∩ strip)) = f t`, since the line is null; this uses `hfin` for `tendsto_measure_iInter_atTop`;
  - for `t ≤ x₁` the rectangles are empty;
  - conclude with `Monotone.continuousAt_iff_leftLim_eq_rightLim`.

  The same holds in the left edge and in `y`.
- **`swapReIm z = I * conj z = z.im + I z.re`** is a linear isometric involution, so balls map to balls. `preimage_swapReIm_rect` follows by `simp`.

  **Use:** prove the one-step lemmas (the bisection step in §3.5 Case A and the slicing step in Case B) only for cuts along `x`. Obtain the `y` versions by applying them to `ν.map swapReIm` and pulling back. Do **not** try to transport `midThird` through the swap: at ties `l = w` its orientation is not swap-equivariant. The one-step lemmas take "`ν(middle third along x) > 1`" directly as hypothesis.

### 3.2 Coarse strip cuts (`exists_strip_cuts`)
Let `G(t) := ν(rect 0 t y₁ y₂).toReal` for `t ≥ 0` and `G(t) := −ν(rect t 0 y₁ y₂).toReal` for `t < 0`.
- For `a ≤ b`: `ν(rect a b) = G(b) − G(a)` (additivity, `hfin`).
- `G` is monotone and continuous (§3.1).

**Construction.**
1. Define `x : ℕ → ℝ` recursively with `x 0 := 0`, and `x (n+1) :=` a point `t ∈ [x n + h, x n + 2h]` with `G t ∈ ℤ`.
   - It exists because `G(x n + 2h) − G(x n + h) = ν(rect (x n + h) (x n + 2h)) ≥ 1` (`hmass`).
   - So `⌈G(x n + h)⌉ ∈ [G(x n + h), G(x n + 2h)]`, and `intermediate_value_Icc` applies.
2. Symmetrically define `x' : ℕ → ℝ` going left, in `[x' n − 2h, x' n − h]`.
3. Glue them along `ℤ` (`Int.rec`: `ofNat n ↦ x n`, `negSucc n ↦ x' (n+1)`).

**Properties.**
- Gaps lie in `[h, 2h]`, so `x` is strictly monotone.
- Each block mass `G(x(k+1)) − G(x k)` is an integer, `≥ ν(rect (x k) (x k + h)) ≥ 1`.
- Covering: `x k ≥ kh` for `k ≥ 0` and `x k ≤ kh` for `k ≤ 0`. So for each `t`, `{k | x k ≤ t}` is nonempty and bounded above; take `k` maximal (`Int.exists_greatest_of_bdd`).
- The `ℝ≥0∞` statement `ν(…) = n` comes from `ENNReal.ofReal_toReal` with `hfin`.

### 3.3 Slab reverse doubling (`slab_reverse_doubling_right/left`)
Let `0 < s ≤ l` and `J := ⌈l/s⌉₊ ≥ 1`. For `j < J` set:
- `h_j := min (y₁ + (j + 1/2)s) (y₂ − s/2) ∈ [y₁ + s/2, y₂ − s/2]`;
- `c_j := (u + s/2) + I h_j`;
- `c'_j := c_j + 2s`.

Steps:
1. **Cover.** `rect u (u+s) y₁ y₂ ⊆ ⋃_{j<J} B(c_j, s)`. For `w` in the slab let `j := ⌊(w.im − y₁)/s⌋₊ < J`; then `|w.re − (u+s/2)| ≤ s/2` and `|w.im − h_j| ≤ s/2`.
   - If `h_j` is clamped, then `w.im ≥ y₁ + js > y₂ − s = h_j − s/2`.
   - In both cases `|w − c_j| ≤ s/√2 < s`.
2. **Shift.** `B(c_j,s) ⊆ B(c'_j, 4s)`, because `2s + s < 4s`. Since `c'_j ∈ rect (u+s) (u+3s) y₁ y₂` (re `= u + 5s/2`), `hED` with `r = s` gives `ν(B(c_j,s)) ≤ C_E ν(B(c'_j, s/2))`.
3. **Placement.** `B(c'_j, s/2) ⊆ rect (u+s) (u+3s) y₁ y₂`: re `∈ (u+2s, u+3s)`, im `∈ (h_j − s/2, h_j + s/2) ⊆ [y₁, y₂)`.
4. **Overlaps.** Only `h_{J−1}` can be clamped: for `j ≤ J − 2`, `(j+1)s < l`. So the balls `B(c'_j, s/2)` with `j ≤ J−2` are pairwise disjoint (heights differ by `≥ s`). Hence `∑_{j} ν(B(c'_j,s/2)) ≤ ν(⋃_{j≤J−2}) + ν(B(c'_{J−1},s/2)) ≤ 2 ν(rect (u+s) (u+3s) y₁ y₂)` (`measure_biUnion_finset`).
5. **Combine:** `ν(slab) ≤ ∑_j ν(B(c_j,s)) ≤ 2C_E ν(rect (u+s) (u+3s))`.

The left version is the mirror image: `c'_j := c_j − 2s`, with re `= u − 3s/2 ∈ [u−2s, u)`.

### 3.4 `rect_inner_outer`
Let `m := min(w,l)`, `M := max(w,l) ≤ Lm`, `p :=` the centre, `r := m/6`. Then:
- `6r = m ≤ M`.
- `B(p,r) ⊆ midThird`. In the horizontal case (`l ≤ w`) the middle third is `[x₁ + w/3, x₂ − w/3) × [y₁, y₂)`; points of `B(p, m/6)` have `|re − p.re| < m/6 ≤ w/6` and `|im − p.im| < m/6 ≤ l/2`. The vertical case is symmetric.
- `rect ⊆ B(p, 6Lr) = B(p, Lm)`, because `|z − p| ≤ √((w/2)² + (l/2)²) ≤ M/√2 < M ≤ Lm`.

### 3.5 Core theorem `exists_rect_partition`
**Constants.**
- WLOG `C_E ≥ 1` (replace it by `max C_E 1`; `hσ` survives).
- `η_s := 1/(2C_E)`.
- `k₀ := ⌈log(C₀+1)/log(1+η_s)⌉₊`, so `(1+η_s)^{k₀} > C₀`.
- `c_* := 3^{-k₀} · min(1/4, κ)`.
- `L := max 3 (1/c_*)`.

**Statement proved by strong induction on `n`** (`Nat.strong_induction_on`): for every good, admissible (`P`) rectangle `Q` with `ν(Q) = n ≥ 1`, there are `n` disjoint rectangles of mass 1, with ratio `≤ L` and union `Q`, each contained in a good admissible rectangle of mass `≤ C₀`.

WLOG `l ≤ w`; cut along `x`. The other case is the same lemma applied to `ν.map swapReIm` (§3.1).

**Case A: `n > C₀`.**
1. **The cut point.** By `hC₀`, `ν(mid) > 1`, where `mid = rect (x₁ + w/3) (x₂ − w/3) y₁ y₂`.
   - Let `F(t) := ν(rect x₁ t y₁ y₂).toReal`, which is continuous (§3.1). Then `F(x₂ − w/3) − F(x₁ + w/3) = ν(mid) > 1`.
   - Let `n₁ := ⌊F(x₁ + w/3)⌋₊ + 1`. Then `F(x₁ + w/3) < n₁ < F(x₂ − w/3)`, and `intermediate_value_Ioo` gives `t* ∈ (x₁ + w/3, x₂ − w/3)` with `F(t*) = n₁`.
2. **The two halves.** Let `Q₁ := rect x₁ t* y₁ y₂` and `Q₂ := rect t* x₂ y₁ y₂`.
   - `ν(Q₁) = n₁ ≥ 1`.
   - `ν(Q₂) = n − n₁ > n − F(x₂ − w/3) = ν(rect (x₂ − w/3) x₂) ≥ 0`, so `n − n₁ ≥ 1`, and `n₁ < n`.

   No positivity of balls is needed here, unlike the paper's version.
3. **Shape.** The widths `t* − x₁` and `x₂ − t*` lie in `(w/3, 2w/3)`.
   - If the width `≥ l`: ratio `≤ (2w/3)/l ≤ 2`.
   - If the width `< l`: ratio `≤ l/(w/3) ≤ 3`.

   So both halves are good, and admissible because `P` is hereditary (`hP`).
4. **Recursion.** Apply the induction hypothesis to `Q₁` and `Q₂`. Concatenate along `finSumFinEquiv : Fin n₁ ⊕ Fin (n − n₁) ≃ Fin n` (with `n₁ + (n − n₁) = n`). Pieces from `Q₁` and `Q₂` are disjoint because `Q₁ ∩ Q₂ = ∅`.

**Case B: `1 ≤ n ≤ C₀`.**
1. **Cut points.** Let `F(t) := ν(rect x₁ t y₁ y₂).toReal` on `[x₁, x₂]`, so `F(x₁) = 0` and `F(x₂) = n`. Set `t₀ := x₁` and `t_n := x₂`. For `0 < j < n`, `intermediate_value_Ioo` gives `t_j ∈ (x₁, x₂)` with `F(t_j) = j`.
   - `F` is monotone with distinct values at the `t_j`, so the `t_j` are strictly increasing.
2. **Pieces.** `S_j := rect t_{j−1} t_j y₁ y₂` for `j = 1..n`.
   - Each has mass 1 and lies in the block `Q` (good, admissible, `ν(Q) = n ≤ C₀`).
   - The `S_j` are disjoint and their union is `Q` (telescoping additivity).
3. **Eccentricity of a slice** `S = rect t t' y₁ y₂`, `s := t' − t`. Claim: `s ≥ c_* w`.
   - Suppose `s < c_* w ≤ w/4`. Then the room on one side is `≥ (w − s)/2 ≥ w/4`; say on the right, `x₂ − t' ≥ w/4`. (On the left, use `slab_reverse_doubling_left` with `T_i := rect (t' − 3^i s) t'`.)
   - Let `T_i := rect t (t + 3^i s) y₁ y₂` for `i ≤ k₀`. For `i < k₀` apply `slab_reverse_doubling_right` with width `s_i := 3^i s`:
     - `s_i ≤ 3^{k₀−1} s ≤ w/4 ≤ 3l/4 ≤ l` (`hsl`);
     - the centres used lie in `rect (t + s_i) (t + 3s_i) ⊆ Q`, by the room;
     - radii `r ≤ s_i ≤ κw ≤ κ max(w,l) ≤ σ(Q)`, so `hED` holds by `hσ`.
   - Therefore `ν(T_{i+1}) = ν(T_i) + ν(rect (t + s_i) (t + 3s_i)) ≥ (1 + η_s) ν(T_i)`.
   - Hence `C₀ < (1+η_s)^{k₀} = (1+η_s)^{k₀} ν(T₀) ≤ ν(T_{k₀}) ≤ ν(Q) = n ≤ C₀`, a contradiction.
4. **Conclusion.** `S` has width `∈ [c_* w, w]` and height `l ∈ [w/3, w]`. Its ratio is `≤ max(3, 1/c_*) = L`.

### 3.6 Plane: `lemma4_plane`
Let `μ' := N⁻¹ • μ`.
- `IsLocDoublingM.smul` gives local doubling.
- `exists_radius_lt_measure_ball_plane` with `p = N` gives `R'` with `1 ≤ μ'(B(z,R'))`.
- Let `S := 2R'`.

**Null lines.** `{w | w.re = x}` is the line `x + tI`, and `{w | w.im = y}` is the line `Iy + t`. Both are null by `isPorous_line` and `measure_eq_zero_of_isPorous_plane`.

**Coarse step.** For each row `j ∈ ℤ`, apply `exists_strip_cuts` to `[jS, (j+1)S)` with `h := S`.
- `hmass`: `rect a (a+S) jS (j+1)S ⊇ B(a + S/2 + I(jS + S/2), R')`.
- `hfin`: bounded rectangles lie in balls.
- Blocks: `Q_{jk} := rect (x_j k) (x_j (k+1)) (jS) ((j+1)S)`, of ratio `≤ 2` and integer mass `n_{jk} ≥ 1`.

**Hypotheses of §3.5.**
- **Admissibility:** `P x₁ x₂ y₁ y₂ := x₂ − x₁ ≤ 2S ∧ y₂ − y₁ ≤ 2S` (hereditary).
- **`C₁`** is `doubling_upTo_plane` for `μ'` at scale `16S`.
- **`C₀ := ⌈C₁⁵⌉₊`.** For a good admissible rectangle, `rect_inner_outer` (L = 3) gives `B(p,r) ⊆ mid` and `rect ⊆ B(p,18r)` with `r ≤ S/3`. Then `μ'(rect) ≤ μ'(B(p,18r)) ≤ C₁⁵ μ'(B(p,r)) ≤ C₁⁵ μ'(mid)`, with `2⁵ ≥ 18` and base radii `≤ 16r`.
- **`σ(Q) := max(w,l)`, `κ := 1`, `C_E := C₁³`:** `μ'(B(w,4r)) ≤ C₁³ μ'(B(w,r/2))` for `r ≤ 2S`.

**Pieces.** Apply §3.5 to every block. The index type is `ι := Σ jk : ℤ × ℤ, Fin (n_{jk})`, which is countable and infinite; reindex by `ℕ`.
- **Mass:** `μ = N • μ'`, so `μ(piece) = N`.
- **Upper size (`dist_le`).** A piece lies in a block `B` that is good, admissible and has `μ'(B) ≤ C₀`. Take `p, r` for `B` from `rect_inner_outer`.
  1. For `z, w` in the piece, `d(z,w) < 36r`, and `B(z,36r) ⊆ B(p,54r)`.
  2. So `μ'(B(z,36r)) ≤ C₁⁶ μ'(B(p,r)) ≤ C₁⁶ C₀`.
  3. `measure_ball_massRadius_bounds_plane` for `μ'` at scale `12S` gives: if `36r ≥ ρ'(z)` then `c(36r/ρ'(z))^δ ≤ C₁⁶C₀`.
  4. Hence `d(z,w) ≤ A' ρ'(z)` with `A' := max(1, (C₁⁶C₀/c)^{1/δ})`, and `ρ'(z) ≤ C_N ρ(z)`. Take `A := A' C_N`.
- **Fatness (`inner`).** A piece is `rect` with ratio `≤ L`. `rect_inner_outer` (L) gives `p ∈ B(p,r) ⊆ mid ⊆ piece ⊆ B(p, 6Lr)`.
  - So `μ(B(p,6Lr)) ≥ N ≥ 1`, and `massRadius μ p ≤ 6Lr` (`massRadius_le`).
  - Take `a := 1/(6L)` and `c := p`.

### 3.7 Cayley geometry (`Partition/Cayley.lean`)
- **Formulas.** For `z ∈ 𝔻`:
  - `cayley z = −2 Im z/|1−z|² + I (1 − |z|²)/|1−z|²`, so `Im cayley z > 0`;
  - `cayleyInv` is the inverse on ℍ (`field_simp`);
  - `cayleyInv w ∈ 𝔻` because `|w − I| < |w + I| ⟺ Im w > 0`;
  - `cayley` is measurable as a quotient of measurable maps; the junk value at `z = 1` is irrelevant.
- **Isometry `pseudoHyp_cayleyInv`.** With `zₖ = cayleyInv wₖ`:
  - `z₁ − z₂ = 2I(w₁ − w₂)/((w₁ + I)(w₂ + I))`;
  - `1 − conj z₁ · z₂ = 2I(conj w₁ − w₂)/((conj w₁ − I)(w₂ + I))`.

  Since `|conj w₁ − I| = |w₁ + I|` and `|conj w₁ − w₂| = |w₁ − conj w₂|`, the quotient is `τ(w₁,w₂) := |w₁ − w₂|/|w₁ − conj w₂|`.
- **Consequence.** For `p = cayleyInv c`, `hypBall p β = cayleyPre {w | τ(c,w) < tanh β}`. Points with `Im w ≤ 0` have `τ ≥ 1`, so they are excluded automatically.
- **Two Euclidean facts about `τ`** (from `|w − conj c| ≤ |w − c| + 2 Im c` and `≥ Im w + Im c`):
  - `τ(c,w) < t ⟹ |w − c| < 2t Im c/(1−t)`;
  - `|w − c| < t·(2 Im c − |w−c|) ⟹ τ(c,w) < t`.
- **`isPorous_cayley_re`.** For `z ∈ 𝔻`, `Re cayley z = x ⟺ −2 Im z = x|1 − z|²`.
  - If `x = 0`, this is the real line (`isPorous_line 0 1`).
  - Otherwise it is `|z − (1 − I/x)|² = 1/x²`, a sphere (`isPorous_sphere`).

  In both cases use `IsPorous.mono`.
- **`isPorous_cayley_im`.** `Im cayley z = y ⟺ 1 − |z|² = y|1−z|² ⟺ (1+y)|z|² − 2y Re z + (y − 1) = 0`.
  - If `y ≠ −1`: the sphere `|z − y/(1+y)| = 1/|1+y|` (a horocycle at `1`).
  - If `y = −1`: the line `Re z = 1`.
- **`discBox_inner_outer`** (`Λ, L` given). Let `Q` satisfy `IsRectLE L`, `y₁ > 0`, `l ≤ Λy₁`. Let `c` be its centre, `y_c := y₁ + l/2`, `p := cayleyInv c`, `m := min(w,l)` and `M := max(w,l) ≤ Lm`.
  - **Inner.** `t₁ := m/(12y_c + m)` gives `2t₁y_c/(1−t₁) = m/6`. So `{τ(c,·) < t₁} ⊆ B_E(c, m/6) ⊆ midThird` (§3.4). Set `β := artanh t₁`.
  - **Outer.** For `w' ∈ Q`:
    1. `τ(c,w') ≤ M/(y₁ + y_c)`.
    2. From `τ² = 1 − 4 Im w'·y_c/|w' − conj c|²`, using `|w' − conj c|² ≤ (w/2)² + (y₂ + y_c)²`, `w ≤ LΛy₁`, `y₂ ≤ (1+Λ)y₁`, `y_c ≤ (1+Λ/2)y₁`, we get `1 − τ² ≥ ε_Λ := 4/(L²Λ²/4 + (2 + 3Λ/2)²)`.
    3. So `artanh τ ≤ τ/(1 − τ²) ≤ τ/ε_Λ`. Since `artanh t₁ ≥ t₁` and `m ≤ Λy_c`: `artanh τ / β ≤ (M/y_c)(12y_c + m)/(m ε_Λ) ≤ L(12 + Λ)/ε_Λ`.
  - **Constants.** `A := 2L(12+Λ)/ε_Λ` (the factor 2 makes the inclusion into the open ball strict) and `D := A · artanh(Λ/(12+Λ))`, because `t₁ ≤ Λ/(12+Λ)`.
- **`euclid_doubling_cayley`.** Let `y := Im w > 0` and `r ≤ y/16`.
  - **Containments.**
    - `B_E(w,4r) ⊆ {τ(w,·) < t_o}` with `t_o := 4r/(2y − 4r) ≤ 1/6`;
    - `B_E(w,r/2) ⊇ {τ(w,·) < t_i}` with `t_i := r/(4y + r)`, since `2t_i y/(1−t_i) = r/2`.
  - **Comparison of radii.** `t_o/t_i ≤ 12` and `artanh t_o ≤ (36/35) t_o`, so `β_o/β_i < 16`, with `16β_i < 1/2`.
  - **Conclusion.** Four local doublings give `ν(B_E(w,4r)) ≤ μ(hypBall p β_o) ≤ C⁴ μ(hypBall p β_i) ≤ C⁴ ν(B_E(w,r/2))`, where `ν = cayley_*(μ|𝔻)` and `ν(S) = μ(cayleyPre S)`. So `C_E := C⁴`.
- **Coarse rows** (used in §3.8). `Λ_c := 64 e^{4R}`, rows `[Λ_c^j, Λ_c^{j+1})`, `h_j := (Λ_c − 1)Λ_c^j`.
  - Claim: the square `[a, a + h_j) × [Λ_c^j, Λ_c^{j+1})` contains `{τ(c,·) < tanh R}` with `c := a + h_j/2 + I Λ_c^{j+1/2}`.
  - **Vertically:** `τ < t` gives `|Im w − y_c| < t(Im w + y_c)`, so `Im w ∈ (y_c e^{−2R}, y_c e^{2R}) ⊆ (Λ_c^j, Λ_c^{j+1})`. This uses `(1+t)/(1−t) = e^{2R}` and `Λ_c^{1/2} ≥ e^{2R}`.
  - **Horizontally:** `|w − c| < 2t y_c/(1−t) ≤ 2e^{2R}Λ_c^{j+1/2} ≤ h_j/2`. This holds since `8e^{2R}Λ_c^{1/2} ≤ Λ_c` and `Λ_c − 1 ≥ Λ_c/2`.
  - Hence `ν(square) ≥ μ(hypBall (cayleyInv c) R) ≥ 1`.

### 3.8 Disc: `lemma4_disc`
**Set-up.**
- `μ' := N⁻¹ • μ`.
- `R'` from `exists_radius_lt_measure_hypBall` with `p = N`.
- `Λ := Λ_c(R')`.
- `ν := (μ'.restrict 𝔻).map cayley`, so `ν(rect …) = μ'(discBox …)` (`Measure.map_apply`).
- Null lines: `ν {re = x} = μ'(cayleyPre {re = x}) = 0` by `isPorous_cayley_re` and `measure_inter_disc_eq_zero_of_isPorous`; likewise for `im`.

**Hypotheses of §3.5.**
- **Admissibility:** `P x₁ x₂ y₁ y₂ := 0 < y₁ ∧ y₂ − y₁ ≤ Λy₁ ∧ x₂ − x₁ ≤ 2Λy₁` (hereditary). `hfin`: the `discBox` of a `P`-rectangle lies in a hyperbolic ball of bounded radius (the outer estimate of §3.7 with ratio replaced by the width bound).
- **Coarse blocks:** from §3.7's rows via `exists_strip_cuts` with `h := h_j`. Their ratio is `≤ 2`, `l = (Λ − 1)y₁`, and width `≤ 2h_j ≤ 2Λy₁`, so they satisfy `P`.
- **Cover:** for `z ∈ 𝔻`, `cayley z ∈ ℍ` lies in the row `j := ⌊log_Λ Im cayley z⌋` and in some block.
- **`hC₀`:** `discBox_inner_outer(Λ, 3)` gives `A, D`. Then `μ'(discBox Q) ≤ μ'(hypBall p (Aβ)) ≤ C₁^{⌈log₂ A⌉₊} μ'(hypBall p β) ≤ C₁^{…} ν(mid)`, with `C₁ := doubling_upTo_disc` for `μ'` at scale `D`. Set `C₀ := ⌈C₁^{⌈log₂ A⌉₊}⌉₊`.
- **`hσ`:** `σ(Q) := y₁/16` and `κ := 1/(48Λ)`, since `max(w,l) ≤ 3l ≤ 3Λy₁`. `hED` follows from `euclid_doubling_cayley`, because points of `Q` have `Im ≥ y₁`.

**Pieces.** The pieces are `discBox` of the rectangles produced by §3.5.
- **Upper size.** As in the plane, with hyperbolic balls.
  1. Take `p, β` for the block `B`. For `z, w` in the piece, `hypDist z w < 2Aβ`.
  2. `hypBall z (2Aβ) ⊆ hypBall p (3Aβ)`, so its `μ'`-mass is `≤ C₁^{⌈log₂ 3A⌉₊} C₀`.
  3. The lower bound of `measure_hypBall_massRadiusDisc_bounds` at scale `3D` gives `2Aβ ≤ A' ρ'(z) ≤ A' C_N ρ(z)`.
- **Fatness:** `discBox_inner_outer(Λ, L)` gives `p ∈ hypBall p β ⊆ piece ⊆ hypBall p (A_L β)`. So `massRadiusDisc μ p ≤ A_L β`, and `a := 1/A_L`.

### 3.9 Line: `lemma4_line`
Work with `ν := linePull μ` on `ℝ` and `G(t) := ν(Ico 0 t).toReal` (negative side as in §3.2).
- **Properties of `G`.**
  - `G` is continuous: `ν` has no atoms (`measure_singleton_line`) and is finite on bounded intervals.
  - `G` is monotone.
  - `G(t) → ±∞`: by the mass condition, `ν(Ico a (a + 2R)) ≥ 1`.
- **Cut points.** For `k ∈ ℤ` choose `t_k` with `G(t_k) = kN` (`intermediate_value_Icc`). The `t_k` are strictly increasing, and `t_k → ±∞` because `G` is bounded on bounded sets.
- **Pieces.** `ofReal '' Ico t_k t_{k+1}`, of mass `N`.
- **Length bound.** If `L_k := t_{k+1} − t_k > 2r_N`, where `ν(ball x r_N) > N` for all `x` (growth with `p = N`), then the interval would contain a ball of mass `> N`. So `L_k ≤ 2r_N`.
- **Upper size.** For `z ∈ I_k`: `ball z L_k ⊆ ball(mid, 3L_k/2)`, so `μ(ball z L_k) ≤ C₁³ μ(ball(mid, L_k/2)) ≤ C₁³ N`, because `ball(mid, L_k/2) = Ioo ⊆ I_k`. The lower bound then gives `L_k ≤ (C₁³N/c)^{1/δ} ρ(z)` when `L_k ≥ ρ(z)`.
- **Fatness.** `c := mid`. Then `I_k ⊆ closedBall(mid, L_k/2)`, so `ρ(mid) ≤ L_k` and the ball of radius `L_k/2 ≥ ρ(mid)/2` lies in `I_k`. Take `a := 1/2`.
- **Reindex** `ℤ ≃ ℕ`.

### 3.10 Claim 2 and the consequences (`Properties.lean`)
- **`claim2_lower_*`** (diam `≥ ρ`). We have `μ(closedBall z r) ≥ μ(R_i) = N ≥ 1`, and `r ≥ 0` since `z ∈ R_i`. For every `r' > r`, `1 ≤ μ(B(z,r'))`, so `ρ(z) ≤ r'` (`massRadiusM_le`). Let `r' ↓ r`. No doubling is needed.
- **`claim2_*` (second bullet).** This is Claim 1 (`claim1_*`) restricted to points of the pieces; the partition plays no role. Combined with `dist_le` and `claim2_lower`, the diameters of pieces with `d(R_i, R_j) ≤ K max(ρ)` are comparable, which is the paper's "`KR_i ∩ KR_j ≠ ∅`".
- **`finite_near_*`.**
  1. Let `K' := K + A(1+K)`. If `w ∈ R_i` and `d(z,w) ≤ Kρ(z)`, then for `w' ∈ R_i`: `d(w,w') ≤ Aρ(w) ≤ A(1+K)ρ(z)` (Lipschitz). So `R_i ⊆ B(z, 2K'ρ(z))`.
  2. For any finite set `F` of such `i`: `#F ≤ ∑_F μ(R_i) = μ(⋃_F R_i) ≤ μ(B(z, 2K'ρ(z))) ≤ C(2K')^s`. The last step uses `measure_*_massRadius*_bounds` at scale `2K'R₀`.
  3. Conclude with `Set.encard_le_coe_iff_finite_ncard_le`, or by contradiction with a finite subset of size `M+1`.
- **`finite_neighbours_*`.** Pick `z₀ ∈ R_i` (nonempty since `μ(R_i) = N ≥ 1`). For `z ∈ R_i` and `w ∈ R_j` with `d(z,w) ≤ Kρ(z)`:
  - `ρ(z) ≤ (1+A)ρ(z₀)`;
  - `d(z₀,w) ≤ (A + K(1+A))ρ(z₀)`.

  Apply `finite_near` at `z₀`.
- **`far_comparable_*`.** If `R_i ∩ B(z,ηρ(z)) = ∅` and `w, w' ∈ R_i`, then `d(z,w') ≤ d(z,w) + Aρ(w) ≤ d(z,w) + A(ρ(z) + d(z,w)) ≤ (1 + A + A/η) d(z,w)`, using `ρ(z) ≤ d(z,w)/η`.
- **`euclid_size_disc`.** `hypDist z w ≤ Aρ(z) < 2Aρ(z) ≤ 2AR₀`. By `hypBall_subset_ball`, `‖z − w‖ < tanh(2Aρ(z))(1−|z|²)/(1 − tanh(2AR₀)) ≤ 2Aρ(z)(1−|z|²)/(1 − tanh(2AR₀))`.
- **`mass_mul_le_setLIntegral`:** `setLIntegral_const` and `setLIntegral_mono'`.
- **`lintegral_biUnion`:** Mathlib's `lintegral_biUnion` (countable `S ⊆ ℕ`, measurable, pairwise disjoint).
- **`existsUnique_mem`:** cover plus disjointness.

---

## 4. Interface

### 4.1 Consumers
- **M06 (Lemma 5).** For every piece `R_i` and every `z ∈ R_i`:
  - `R_i ⊆ {w : d(z,w) ≤ Aρ(z)}`;
  - `R_i ⊇ {w : d(c_i, w) < aρ(c_i)}` with `c_i ∈ R_i`.

  Shapes:
  - plane: pieces are coordinate rectangles of ratio `≤ L`;
  - disc: `discBox` of an ℍ-rectangle of ratio `≤ L`, admissible (`y₂ − y₁ ≤ Λy₁`), with Euclidean diameter `≤ C(1−|z|²)ρ(z)` (`euclid_size_disc`);
  - line: intervals.

  **Coordination point:** the paper's "`R` with ratio of sides `≤ K`" and the dilates "`CR`, `4CKR`" should be read as discs. Use `B(c_i, C·Aρ(c_i))` (or the Euclidean disc of radius `C · diam R_i`) rather than dilated rectangles. In 𝔻 the Euclidean shape of a horocyclic box is not a rectangle.
- **M08 (Theorem 4).**
  - `existsUnique_mem`: the piece containing `z`.
  - `finite_near_*`, defining the near pieces as those meeting `{w : d(z,w) ≤ ηρ(z)}`: the paper's "rectangle containing `z` and its immediate neighbours". They are boundedly many and lie in `B(z, C ρ(z))`.
  - For the other ("far") pieces, every point satisfies `d(z,ζ) ≥ ηρ(z)`. This is exactly the region of Lemma 3 (`δ := η`), so no "uniform δ by Claim 1" argument is needed.
  - `far_comparable_*`: `|z − w| ≃ |z − ζ|` (p. 367).
  - `dist_le` + `claim2_*`: `|ζ − λ₀| ≲ ρ(ζ) ≃ ρ(λ₀)`.
  - `mass_mul_le_setLIntegral` and `lintegral_biUnion`: "both the integral and the sum are comparable".
  - `euclid_size_disc`.
  - Fatness (`inner`) with M03's `encard_le_of_disjoint_*` and `decay_*`: area counting with moment order 3.
  - **Getting `area(R_i) ≍ ρ²`.**
    - Plane: `ball c (aρ(c)) ⊆ R_i ⊆ closedBall c (Aρ(c))`, so `area(R_i) ≍ ρ(c)²`.
    - Disc: by `ball_subset_hypBall`/`hypBall_subset_ball` (hyperbolic radii `≤ A R₀`), the Euclidean area is `≍ (1 − |c|²)² ρ(c)²`. The hyperbolic area is `≍ ρ(c)²`.
    - Pass from `ρ(c_i)` to `ρ(ζ)`, `ζ ∈ R_i`, with `claim2_*`. The count lemmas take a *uniform* inner radius `a`, so apply them with `a := (min over the relevant pieces)`, which is bounded below by Claim 1 when the pieces meet `B(z, Kρ(z))`.
    - M03's count is stated with covering numbers instead of area. This is equivalent for our three geometries and avoids defining hyperbolic area.
- **M09 (Proposition 2).** `finite_neighbours_*` gives a graph of bounded degree on `ℕ`. Greedy colouring along `ℕ` uses `M+1` colours; this replaces the paper's appeal to Besicovitch. `κ(R_i)` placed at distance `≥ (A + K C_K)ρ(c_i)` from `c_i` misses `R_i` and its `K`-neighbours.
- **M13 (Theorem 5):** `lemma4_line`, `claim2_lower_line`, `finite_near_line`, `far_comparable_line`.

### 4.2 Assumed from M03 and M01
- **From M03:** all lemmas named in the header, with the statements of `M03_Doubling.md` §2.
- **From M01:**
  - `ball_subset_hypBall`, `hypBall_subset_ball` (in `euclid_size_disc` and, through M03, in porosity);
  - the definition of `pseudoHyp`/`hypDist` from `Defs.lean` (for `pseudoHyp_cayleyInv`).

---

### 4.3 Interface (reconciled)

Lean files: `Partition/Rectangles.lean`, `Cayley.lean`, `Lemma4.lean`, `Properties.lean`.
- **`exists_rect_partition`: explicit side-ratio bound.** The statement no longer has `∃ L` after the measure. The ratio bound is the explicit `rectRatioBound C₀ C_E κ = max 3 (3^{k₀} / min(1/4, κ))` of §3.5, with `k₀ = rectRatioK₀ C₀ C_E`. It depends only on `C₀`, `C_E`, `κ` (block in §2.1).
- **Uniform Lemma 4** (requested by M08 §4.1). The constants `a`, `A` come after `(Cd, R₀, N)` and before the measure. The classes `MeasClassPlane/Disc/Line` are M03's (`Doubling/Quant.lean`).

```lean
/-- (M05, quantitative Lemma 4). -/
theorem lemma4_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) : ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν univ dist (massRadius ν) N a A R
theorem lemma4_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) : ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν 𝔻 hypDist (massRadiusDisc ν) N a A R
theorem lemma4_line_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) : ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν (range fun t : ℝ ↦ (t : ℂ)) dist
        (fun z ↦ massRadiusLine ν z.re) N a A R
```
- `IsMassPartition` is defined once, here; M08's stub is removed.

## 5. Issues found (for the NOTEBOOK)

1. **p. 365, final cut ("we use Lemma 1").** Lemma 1 concerns balls; it does not control thin slabs. The missing ingredient is reverse doubling for slabs, `slab_reverse_doubling_*` (§3.3, §3.5 Case B). With it, slices of mass 1 in a block of mass `≤ C₀` have width `≥ 3^{-k₀} min(1/4, κ)` times the block's length. Without it, only `diam ≲ ρ` holds (inherited from the block), not bounded eccentricity.
2. **p. 364, the disc.**
   - (a) The region near the origin is not treated: polar rectangles degenerate.
   - (b) For large `R`, polar "eccentricity" is not meaningful (outer/inner arc ratio `e^{2a}`), and the bisection invariant "ratio ≤ 3" is not preserved by radial cuts.
   - Both are fixed by horocyclic boxes, i.e. Cayley preimages of rectangles in ℍ (§0.2, §3.7–3.8). Their boundaries are horocycles and geodesics, which are circles and lines, hence null by porosity.
3. **p. 364, coarse step.** "Any square of size `R × R` has mass at least 1" does not follow from `μ(D(z,R)) > 1`: the square only contains `D(z, R/2)`. Use strips of width `2R`.
4. **p. 364–365, bisection.**
   - "`R ⊂ 2R'` and `μ(R)` is already smaller than the doubling constant" compares a rectangle with a rectangle. The correct threshold is `C₀ = C₁^5` (plane) or `C₁^{⌈log₂ A⌉}` (disc), obtained via inner/outer balls.
   - Also `R ⊂ 2R'` needs `h ≥ w/2`, not `h > w/3`.
   - The paper does not check that both halves get **positive** integer mass. With the cut inside the middle third this is automatic (§3.5 Case A).
   - Termination: the masses strictly decrease, so strong induction on the integer mass applies.
5. **p. 365, Claim 2.**
   - The lower bound `diam R ≥ ρ(z)` is immediate from `μ(R) ≥ 1`; no eccentricity is needed.
   - The second bullet is Claim 1 and does not depend on the construction.
   - "`KR_i`" (dilated rectangle) is replaced by metric neighbourhoods `{d(·, R_i) ≤ Kρ}`.
6. **p. 369, Proposition 2.** "This is possible with the Besicovitch covering lemma": the bounded number of neighbours (`finite_neighbours_*`) plus greedy colouring suffices.
7. **p. 375, Theorem 5.** "It is trivial to split the real line into intervals all of mass `N`" holds via the continuous CDF (no atoms). The intervals also satisfy `|I| ≍ ρ` by the same doubling argument (§3.9).
