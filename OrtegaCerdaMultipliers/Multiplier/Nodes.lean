import OrtegaCerdaMultipliers.Multiplier.Basic
import OrtegaCerdaMultipliers.Multiplier.Defs
import OrtegaCerdaMultipliers.Quadrature

/-!
# M08 (Multiplier) — Node configurations from M06 (Lemma 5)

See `blueprint/M08_Multiplier.md` §2.7.  Scaffold: statements, proofs `sorry`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Nodes from Lemma 5 with `m = 3`, `k = 4`, `N = 12`; on cells with `sel i = true` the
alternative set `κ` (distance `≥ B·A·ρ(c i)` from the centre). -/
theorem exists_nodes_plane {ν : Measure ℂ} {η A : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ}
    (hC : IsCells univ dist (massRadius ν) ν 12 η A R c) (hA : 0 ≤ A) (B : ℝ) (hB : 0 ≤ B)
    (sel : ℕ → Bool) :
    ∃ Λ : ℕ → Multiset ℂ, IsNodes univ dist (massRadius ν) ν 12 ((B + 12) * A) R c (fun _ ↦ 3) Λ ∧
      (∀ i, sel i = false → ∀ w ∈ Λ i, dist (c i) w ≤ 6 * A * massRadius ν (c i)) ∧
      ∀ i, sel i = true → ∀ w ∈ Λ i, B * A * massRadius ν (c i) ≤ dist (c i) w := by
  have hρ : ∀ i, 0 ≤ massRadius ν (c i) := fun i ↦ Real.sInf_nonneg fun x hx ↦ hx.1.le
  have hex : ∀ i, ∃ L : Multiset ℂ, Multiset.card L = 12 ∧
      (∀ j < 3, ∫ ζ in R i, ζ ^ j ∂ν = (L.map (· ^ j)).sum) ∧
      (∀ w ∈ L, dist (c i) w ≤ (B + 12) * A * massRadius ν (c i)) ∧
      (sel i = false → ∀ w ∈ L, dist (c i) w ≤ 6 * A * massRadius ν (c i)) ∧
      (sel i = true → ∀ w ∈ L, B * A * massRadius ν (c i) ≤ dist (c i) w) := by
    intro i
    set r := A * massRadius ν (c i) with hr
    have hr0 : 0 ≤ r := mul_nonneg hA (hρ i)
    have hsupp : ν.restrict (R i) (closedBall (c i) r)ᶜ = 0 := by
      rw [Measure.restrict_apply isClosed_closedBall.isOpen_compl.measurableSet]
      convert measure_empty (μ := ν)
      ext w
      simp only [mem_inter_iff, mem_compl_iff, mem_closedBall, mem_empty_iff_false, iff_false,
        not_and]
      intro h1 h2
      exact h1 (by rw [dist_comm]; exact hC.subset i w h2)
    have hmass : ν.restrict (R i) univ = ((3 * 4 : ℕ) : ℝ≥0∞) := by
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, hC.measure_eq i]
    obtain ⟨L, K, hL, hK, hLn, hKn, hmom⟩ :=
      lemma5_moments 3 4 (by norm_num) (by norm_num) (ν.restrict (R i)) (c i) r hr0 hsupp hmass
        B hB
    have hmL : ∀ j < 3, ∫ ζ in R i, ζ ^ j ∂ν = (L.map (· ^ j)).sum := fun j hj ↦ (hmom j hj).1
    have hmK : ∀ j < 3, ∫ ζ in R i, ζ ^ j ∂ν = (K.map (· ^ j)).sum := fun j hj ↦ (hmom j hj).2
    have hLd : ∀ w ∈ L, dist (c i) w ≤ 6 * r := fun w hw ↦ by
      rw [dist_comm, dist_eq_norm]; have := hLn w hw; push_cast at this; linarith
    have hKd : ∀ w ∈ K, B * r ≤ dist (c i) w ∧ dist (c i) w ≤ (B + 12) * r := fun w hw ↦ by
      rw [dist_comm, dist_eq_norm]; have := hKn w hw; push_cast at this
      constructor <;> linarith [this.1, this.2]
    cases hsel : sel i
    · refine ⟨L, by rw [hL], hmL, fun w hw ↦ ?_, fun _ ↦ fun w hw ↦ ?_, fun h ↦ by simp at h⟩
      · calc dist (c i) w ≤ 6 * r := hLd w hw
          _ ≤ (B + 12) * A * massRadius ν (c i) := by rw [hr]; nlinarith [mul_nonneg hA (hρ i)]
      · calc dist (c i) w ≤ 6 * r := hLd w hw
          _ = 6 * A * massRadius ν (c i) := by rw [hr]; ring
    · refine ⟨K, by rw [hK], hmK, fun w hw ↦ ?_, fun h ↦ by simp at h, fun _ ↦ fun w hw ↦ ?_⟩
      · calc dist (c i) w ≤ (B + 12) * r := (hKd w hw).2
          _ = (B + 12) * A * massRadius ν (c i) := by rw [hr]; ring
      · calc B * A * massRadius ν (c i) = B * r := by rw [hr]; ring
          _ ≤ dist (c i) w := (hKd w hw).1
  choose Λ hcard hmom hnear hfalse htrue using hex
  exact ⟨Λ, ⟨hcard, fun _ _ _ ↦ mem_univ _, hnear, hmom⟩, hfalse, htrue⟩

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

end OC
