import OrtegaCerdaMultipliers.LogModulus
import OrtegaCerdaMultipliers.Potential.Fundamental
import OrtegaCerdaMultipliers.Potential.Weyl

/-!
# M07 (LogModulus) — unconditional weak entry point

See `blueprint/M07_LogModulus.md` §4.  `LogModulus.lean` (proved, unchanged) takes the two M02
statements `WeylLaplacianStmt` and `LogKernelStmt` as hypotheses.  Here they are discharged from
M02 (`Potential/Fundamental.lean`, `Potential/Weyl.lean`), and the weak entry point loses the
two arguments.  The proofs in this file are complete term proofs.
-/

open MeasureTheory Metric Set Complex InnerProductSpace

noncomputable section

namespace OC

/-- **M02 → M07: Weyl's lemma for `Δ`** (from `exists_harmonicOnNhd_ae_eq_of_weakHarmonic`). -/
theorem weylLaplacian : WeylLaplacianStmt :=
  fun _U hU _f hf h ↦ exists_harmonicOnNhd_ae_eq_of_weakHarmonic hU hf h

/-- **M02 → M07: the logarithmic kernel** (from `locallyIntegrable_log_norm_sub` and
`integral_log_norm_sub_mul_laplacian`). -/
theorem logKernel : LogKernelStmt :=
  fun a ↦ ⟨locallyIntegrable_log_norm_sub a, fun _χ hχ hc ↦
    integral_log_norm_sub_mul_laplacian (hχ.of_le (WithTop.coe_le_coe.2 le_top)) hc a⟩

/-- `IsWeakLogModulus.ballwise` without the M02 hypotheses. -/
theorem IsWeakLogModulus.logModulusBallwise {Ω : Set ℂ} {n : ℂ → ℕ} {v : ℂ → ℝ}
    (hd : IsWeakLogModulus Ω n v) (c : ℂ) : LogModulusBallwise Ω c n v :=
  hd.ballwise weylLaplacian logKernel c

/-- **M07, weak form, unconditional**: the statement M08 and M13 call. -/
theorem exists_analytic_norm_eq_exp_of_isWeakLogModulus {Ω : Set ℂ} {c : ℂ}
    (hΩ : ∀ z ∈ Ω, ∃ r, dist z c < r ∧ closedBall c r ⊆ Ω)
    {n : ℂ → ℕ} {v : ℂ → ℝ} (hd : IsWeakLogModulus Ω n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω ∧ (∀ z ∈ Ω, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z ∈ Ω, analyticOrderAt h z = n z :=
  exists_analytic_norm_eq_exp_of_weak weylLaplacian logKernel hΩ hd

end OC
