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
      ∀ i, sel i = true → ∀ w ∈ Λ i, B * A * massRadius ν (c i) ≤ dist (c i) w := sorry

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
