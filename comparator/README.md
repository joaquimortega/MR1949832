# Checking the main results with comparator

[comparator](https://github.com/leanprover/comparator) is a trustworthy judge for Lean proofs; Lean v4.35 ships it as `lake comparator`. It checks that every theorem in `config.json`:
1. is stated in `OCSolution` exactly as in `OCChallenge` (all declarations used in the statements must coincide);
2. uses no axioms beyond `propext`, `Quot.sound` and `Classical.choice`;
3. is accepted by the Lean kernel.

## Files

| File | Role |
|---|---|
| `../OCChallenge.lean` | **The self-contained file with the main results.** It imports only `Mathlib`, contains every definition used in the statements (a verbatim copy of `OrtegaCerdaMultipliers/Defs.lean`), and states the fourteen main theorems with `sorry`. |
| `statements.lean` | The main-theorem statements, copied verbatim from the project. |
| `../scripts/make_challenge.py` | Regenerates `OCChallenge.lean` and `config.json` from `Defs.lean` and `statements.lean`. |
| `../OCSolution.lean` | `import OrtegaCerdaMultipliers`. The project proves the theorems with the same names (namespace `OC`); `OC.theorem3_weighted` uses the vendored library `OrtegaCerdaSeip` (`../OrtegaCerdaSeip/VENDORED.md`). |
| `config.json` | The comparator configuration (14 theorems). |

## The fourteen theorems

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
| `OC.theorem3_weighted` | Theorem 3, corrected (weighted integral), unconditional (`TheoremOCS` is proved in MR1682065, vendored) |
| `OC.theorem3_weighted_of_theoremOCS` | the same, from the hypothesis `TheoremOCS` (the [OCS99] theorem quoted on p. 375): the paper's route |
| `OC.theorem3_printed_false` | the printed Theorem 3 fails (formal counterexample, N-01) |

## How to run

From the repository root:

```sh
lake exe cache get                     # prebuilt Mathlib
python3 scripts/make_challenge.py      # (re)generate OCChallenge.lean and comparator/config.json
lake build OCChallenge OCSolution      # optional: writes lake-manifest.json, warms the cache
lake comparator --config comparator/config.json
```

`lake comparator` builds and exports `OCChallenge` and `OCSolution` inside a `bwrap` sandbox (bubblewrap must be installed) and runs the Lean kernel on the export.

**Symlinked packages.** The sandbox covers `/home` and binds only the project read-only and its `.lake` read-write. If `.lake/packages` is a symlink to a directory outside the project (as in the worktrees of this project, which share a prebuilt Mathlib), the symlink dangles inside the sandbox and dependency resolution fails with `already exists … .lake/packages`. Then bind the target read-only through `COMPARATOR_BWRAP`, with a wrapper that adds one `--ro-bind` before bwrap's `--`:

```sh
#!/bin/bash
# bwrap-pkgs: /usr/bin/bwrap plus a read-only bind of the shared package directory
PKGS=$(readlink -f "$PWD/.lake/packages")
args=(); done=0
for a in "$@"; do
  if [[ $done == 0 && $a == "--" ]]; then args+=(--ro-bind "$PKGS" "$PKGS"); done=1; fi
  args+=("$a")
done
exec /usr/bin/bwrap "${args[@]}"
```

```sh
COMPARATOR_BWRAP=/path/to/bwrap-pkgs lake comparator --config comparator/config.json
```

Expected final output:

```
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

This was obtained on 2026-11-02 with Lean v4.35.0 and Mathlib v4.35.0, for all fourteen theorems, with `lake comparator` and the wrapper above (log: `comparator/last_run.log`). The earlier run (2026-11-01, thirteen theorems, `theorem3_weighted` still conditional) used the standalone comparator with `landrun` and `lean4export`.
