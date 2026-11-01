# Checking the main results with comparator

[comparator](https://github.com/leanprover/comparator) is a trustworthy judge for Lean proofs. It checks that every theorem in `config.json`:
1. is stated in `Solution` exactly as in `Challenge` (all declarations used in the statements must coincide);
2. uses no axioms beyond `propext`, `Quot.sound` and `Classical.choice`;
3. is accepted by the Lean kernel.

## Files

| File | Role |
|---|---|
| `../Challenge.lean` | **The self-contained file with the main results.** It imports only `Mathlib`, contains every definition used in the statements (a verbatim copy of `OrtegaCerdaMultipliers/Defs.lean`), and states the thirteen main theorems with `sorry`. |
| `statements.lean` | The main-theorem statements, copied verbatim from the project. |
| `../scripts/make_challenge.py` | Regenerates `Challenge.lean` and `config.json` from `Defs.lean` and `statements.lean`. |
| `../Solution.lean` | `import OrtegaCerdaMultipliers`. The project proves the theorems with the same names (namespace `OC`). |
| `config.json` | The comparator configuration (13 theorems). |

## The thirteen theorems

| Name | Paper |
|---|---|
| `OC.theorem4_disc`, `OC.theorem4_plane` | Theorem 4: multipliers in `𝔻` and `ℂ` (inequalities in the corrected order, NOTEBOOK N-02) |
| `OC.prop2_disc`, `OC.prop2_plane` | Proposition 2: multipliers with disjoint exceptional sets |
| `OC.theorem2` | Theorem 2: one solution, `‖u e^{-φ}‖_{L^p(dm/(1−|z|²))}` bounds for all `p ∈ [1,∞]`; `p = ∞` is the printed sup estimate |
| `OC.theorem2_uniform` | Theorem 2 with a constant depending only on the doubling constant and the mass radius |
| `OC.theorem2_printed` | Theorem 2's printed `L^p` estimate (weight `e^{-φ}`), with the solution depending on `p` (NOTEBOOK N-04) |
| `OC.theorem1`, `OC.theorem1_christ` | Theorem 1 (Christ), locally doubling and doubling versions |
| `OC.prop1` | Proposition 1, upper bound (the printed `≃` is false, N-03) |
| `OC.theorem5` | Theorem 5: multipliers with real zeros |
| `OC.theorem3_weighted` | Theorem 3, corrected (weighted integral), with hypothesis `TheoremOCS` (the [OCS99] theorem quoted on p. 375) |
| `OC.theorem3_printed_false` | the printed Theorem 3 fails (formal counterexample, N-01) |

## How to run

Prerequisites (see the comparator README):
- `landrun` built from its `main` branch: `GOBIN=$PWD/bin go install github.com/zouuup/landrun/cmd/landrun@main`;
- `lean4export` and `comparator`, built from a checkout of the comparator repository: `lake build lean4export comparator`.

From the repository root:

```sh
lake exe cache get                     # prebuilt Mathlib
python3 scripts/make_challenge.py      # (re)generate Challenge.lean and comparator/config.json
export COMPARATOR_LANDRUN=/path/to/landrun
export COMPARATOR_LEAN4EXPORT=/path/to/lean4export
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pipe --wait -E PATH="$PATH" \
  -E COMPARATOR_LANDRUN -E COMPARATOR_LEAN4EXPORT --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator comparator/config.json'
```

Expected final output:

```
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

This was obtained on 2026-11-01 with Lean v4.35.0 and Mathlib v4.35.0, for all thirteen theorems (log: `comparator/last_run.log`).
