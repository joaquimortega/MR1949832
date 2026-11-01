import OrtegaCerdaMultipliers.Multiplier.Kernel
import OrtegaCerdaMultipliers.Multiplier.Cells
import OrtegaCerdaMultipliers.Multiplier.NearField

/-!
# M08 (Multiplier) — Per-cell bounds and the non-near sum (§3.4, §3.7)

See `blueprint/M08_Multiplier.md` §3.4, §3.7.  Helper file (not in the blueprint's file list),
shared by `Potential.lean` and `Estimates.lean`:

* elementary facts on cells (`R i ⊆ Ω`, boundedness, finiteness);
* integrability of the kernels on cells;
* the per-cell bounds (P), (D-near), (D-far) for non-near cells;
* the uniform bound on `Σ_{non-near} |cellPot|` (§3.7), and summability of `cellPot`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ### Elementary facts on cells -/

theorem IsCells.subset_univ {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {η A : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells Ω d ρ ν N η A R c) (i : ℕ) :
    R i ⊆ Ω := by
  rw [← hC.iUnion_eq]; exact subset_iUnion R i

theorem IsCells.center_mem' {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {η A : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells Ω d ρ ν N η A R c) (i : ℕ) :
    c i ∈ Ω :=
  hC.subset_univ i (hC.center_mem i)

theorem IsCells.measure_lt_top {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {η A : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells Ω d ρ ν N η A R c) (i : ℕ) :
    ν (R i) < ∞ := by
  rw [hC.measure_eq i]; exact ENNReal.natCast_lt_top N

theorem IsCells.isBounded_plane {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells univ dist ρ ν N η A R c) (i : ℕ) :
    Bornology.IsBounded (R i) :=
  (isBounded_closedBall (x := c i) (r := A * ρ (c i))).subset fun w hw ↦ by
    rw [mem_closedBall, dist_comm]; exact hC.subset i w hw

theorem IsCells.isBounded_disc {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells 𝔻 hypDist ρ ν N η A R c) (i : ℕ) :
    Bornology.IsBounded (R i) :=
  isBounded_ball.subset (hC.subset_univ i)

theorem IsCells.mono_A {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {η A A' : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hC : IsCells Ω d ρ ν N η A R c)
    (hρ : ∀ i, 0 ≤ ρ (c i)) (hA : A ≤ A') : IsCells Ω d ρ ν N η A' R c :=
  ⟨hC.measurableSet, hC.pairwise_disjoint, hC.iUnion_eq, hC.center_mem,
    fun i w hw ↦ (hC.subset i w hw).trans (mul_le_mul_of_nonneg_right hA (hρ i)), hC.inner,
    hC.measure_eq⟩

theorem IsNodes.mono_B {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ} {ν : Measure ℂ} {N : ℕ}
    {B B' : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hN : IsNodes Ω d ρ ν N B R c m Λ) (hρ : ∀ i, 0 ≤ ρ (c i)) (hB : B ≤ B') :
    IsNodes Ω d ρ ν N B' R c m Λ :=
  ⟨hN.card, hN.mem,
    fun i w hw ↦ (hN.near i w hw).trans (mul_le_mul_of_nonneg_right hB (hρ i)), hN.moments⟩

/-! ### Integrability of the kernels on cells -/

theorem integrableOn_kerPlane_cell {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hν : MeasClassPlane ν Cd R₀)
    (hC : IsCells univ dist (massRadius ν) ν N η A R c) (i : ℕ) (z : ℂ) :
    IntegrableOn (kerPlane z) (R i) ν := sorry

theorem integrableOn_kerDisc_cell {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hν : MeasClassDisc ν Cd R₀)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c) (i : ℕ) {z : ℂ} (hz : z ∈ 𝔻) :
    IntegrableOn (kerDisc z) (R i) ν := sorry

/-! ### Per-cell bounds for non-near cells (§3.4) -/

/-- (P): plane, order-3 moments. -/
theorem abs_cellPot_le_plane {ν : Measure ℂ} {N : ℕ} {η A B : ℝ} {R : ℕ → Set ℂ}
    {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hC : IsCells univ dist (massRadius ν) ν N η A R c)
    (hN : IsNodes univ dist (massRadius ν) ν N B R c m Λ) (hA : 0 < A) (hB : 0 ≤ B) {i : ℕ}
    (hm : 3 ≤ m i) {z : ℂ} (hint : IntegrableOn (kerPlane z) (R i) ν)
    (hρ : 0 < massRadius ν (c i))
    (hfar : 2 * (A + B) * massRadius ν (c i) ≤ dist z (c i)) :
    |cellPot kerPlane ν R Λ i z| ≤
      4 * N * (A + B) ^ 3 * (massRadius ν (c i) / dist z (c i)) ^ 3 := sorry

/-- (D-near): disc, small cells, order-3 moments. -/
theorem abs_cellPot_le_disc_near {ν : Measure ℂ} {N : ℕ} {η A B : ℝ} {R : ℕ → Set ℂ}
    {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c)
    (hN : IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ) (hA : 0 < A) (hB : 0 ≤ B)
    {i : ℕ} (hm : 3 ≤ m i) {z : ℂ} (hz : z ∈ 𝔻) (hint : IntegrableOn (kerDisc z) (R i) ν)
    (hρ : 0 < massRadiusDisc ν (c i)) (hs : (A + B) * massRadiusDisc ν (c i) ≤ 1 / 8)
    (hβ : hypDist z (c i) ≤ 1 / 4)
    (hβ' : 64 * (A + B) * massRadiusDisc ν (c i) ≤ hypDist z (c i)) :
    |cellPot kerDisc ν R Λ i z| ≤
      8 * N * (12 * (A + B)) ^ 3 * (massRadiusDisc ν (c i) / hypDist z (c i)) ^ 3 := sorry

/-- (D-far): disc, any cell (order-2 moments), hyperbolically far from `z`. -/
theorem abs_cellPot_le_disc_far (A B R₀ M₀ : ℝ) (N : ℕ) (hA : 0 < A) (hB : 0 ≤ B)
    (hM₀ : 0 < M₀) :
    ∃ CD : ℝ, 0 ≤ CD ∧ ∀ (ν : Measure ℂ) (η : ℝ) (R : ℕ → Set ℂ) (c : ℕ → ℂ) (m : ℕ → ℕ)
      (Λ : ℕ → Multiset ℂ), IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ → ∀ i, 2 ≤ m i → ∀ z ∈ 𝔻,
      IntegrableOn (kerDisc z) (R i) ν → 0 ≤ massRadiusDisc ν (c i) →
      massRadiusDisc ν (c i) ≤ R₀ → M₀ ≤ hypDist z (c i) →
      2 * (A + B) * massRadiusDisc ν (c i) ≤ hypDist z (c i) →
      |cellPot kerDisc ν R Λ i z| ≤
        CD * ((1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
          ‖1 - conj z * c i‖ ^ 3) := sorry

/-! ### The non-near part is uniformly bounded (§3.7) -/

theorem nonNear_sum_le_plane (Cd : ℝ≥0) (R₀ η A B : ℝ) (N : ℕ) (hη : 0 < η) (hA : 0 < A)
    (hB : 0 ≤ B) :
    ∃ K₀ C : ℝ, 2 * (A + B) ≤ K₀ ∧ 0 ≤ C ∧ ∀ (ν : Measure ℂ) (R : ℕ → Set ℂ) (c : ℕ → ℂ)
      (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassPlane ν Cd R₀ →
      IsCells univ dist (massRadius ν) ν N η A R c →
      IsNodes univ dist (massRadius ν) ν N B R c m Λ → (∀ i, 3 ≤ m i) →
      ∀ z : ℂ, ∀ F : Finset ℕ, (∀ i ∈ F, K₀ * massRadius ν (c i) ≤ dist z (c i)) →
        ∑ i ∈ F, |cellPot kerPlane ν R Λ i z| ≤ C := sorry

theorem nonNear_sum_le_disc (Cd : ℝ≥0) (R₀ η A B ρ₀ : ℝ) (N : ℕ) (hη : 0 < η) (hA : 0 < A)
    (hB : 0 ≤ B) (hρ₀ : 0 < ρ₀) :
    ∃ K₀ C : ℝ, 2 * (A + B) ≤ K₀ ∧ 0 ≤ C ∧ ∀ (ν : Measure ℂ) (R : ℕ → Set ℂ) (c : ℕ → ℂ)
      (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassDisc ν Cd R₀ →
      IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ → (∀ i, 2 ≤ m i) →
      (∀ i, massRadiusDisc ν (c i) ≤ ρ₀ → 3 ≤ m i) →
      ∀ z ∈ 𝔻, ∀ F : Finset ℕ, (∀ i ∈ F, K₀ * massRadiusDisc ν (c i) ≤ hypDist z (c i)) →
        ∑ i ∈ F, |cellPot kerDisc ν R Λ i z| ≤ C := sorry

/-! ### Summability of `cellPot` -/

theorem summable_cellPot_plane {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A B : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hν : MeasClassPlane ν Cd R₀) (hη : 0 < η) (hA : 0 < A) (hB : 0 ≤ B)
    (hC : IsCells univ dist (massRadius ν) ν N η A R c)
    (hN : IsNodes univ dist (massRadius ν) ν N B R c m Λ) (hm : ∀ i, 3 ≤ m i) (z : ℂ) :
    Summable fun i ↦ |cellPot kerPlane ν R Λ i z| := sorry

theorem summable_cellPot_disc {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A B ρ₀ : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hν : MeasClassDisc ν Cd R₀) (hη : 0 < η) (hA : 0 < A) (hB : 0 ≤ B) (hρ₀ : 0 < ρ₀)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c)
    (hN : IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ) (hm2 : ∀ i, 2 ≤ m i)
    (hm3 : ∀ i, massRadiusDisc ν (c i) ≤ ρ₀ → 3 ≤ m i) {z : ℂ} (hz : z ∈ 𝔻) :
    Summable fun i ↦ |cellPot kerDisc ν R Λ i z| := sorry

end OC
