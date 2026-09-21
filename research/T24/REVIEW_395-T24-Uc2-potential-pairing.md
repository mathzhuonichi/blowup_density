ACCEPT-WITH-NOTES

## 1. What the lane claims

`REPORT_395.md:3-16` claims one theorem, `potential_pairing`, with the first
`ConservativeForcingAPI` field and the Haar pairing equal to zero.  The Lean
statement at `formalization/NSFormalization/Section3/T24/PotentialPairing.lean:65-72`
matches `research/T24/Spec.lean:1391-1398` exactly: `∀ ν T`, `0 < T`, the
globally smooth/unit-periodic `φ`, `S : ClassicalSolutionT ν 0
(conservativeForceT φ) T`, then `∀ t ∈ Ico 0 T`, and the explicit
`torusLift`/real inner product integral.  The paper's displayed pairing is
indeed `∫ f·u = -∫∇φ·u = 0` at `paper/sections/03-torus.tex:729-731`, within
the conservative proposition at `:723-725`.

The two local vocabulary definitions at `PotentialPairing.lean:50-56` are
token-for-token the Spec definitions at `Spec.lean:1367-1373`.  No additional
positivity of `ν`, PDE hypothesis, or endpoint hypothesis was added.  The
theorem intentionally does not use `ν` or the already-required `0 < T`
(`PotentialPairing.lean:73`); this is honest because the displayed identity is
pure integration by parts, while `0 < T` remains part of the requested API
statement.

## 2. What is in Lean

The proof transports Haar to the cube at `PotentialPairing.lean:74-75`, gets
the spatial velocity slice from the slab field at `:77-79`, gets the potential
slice smoothness and periods at `:81-87`, and uses the divergence field at
`:89`.  These inputs correspond to the canonical `ClassicalSolutionT` fields
(`PeriodicData.lean:263-299`).  The analytic call is exactly
`NavierStokes.PeriodicUniqueness.cubeIntegral_pressure_energy_zero` at
`vendor/NavierStokesAndEuler/NavierStokes/PeriodicUniqueness.lean:435-447`;
the Haar/cube bridge is `Paper1/TorusCube.lean:40-42`, and the final sign
rewrite is `PotentialPairing.lean:95-101` using
`PeriodicIntegration.lean:71-73`.  The cited slice construction also agrees
with `T11/EnergyIdentity.lean:482-486`.

The positive probe copies the field statement and closes it by `exact
potential_pairing` (`research/T24/probes/potential_pairing_closes.lean:32-40`).
It proves the concrete nonconstant periodic potential `cos (2π x₁)` at
`:44-86` and computes the integral for a zero velocity field at `:90-101`.
The axiom file is present (`research/T24/axioms_uc2.lean:1-11`) and the rerun
prints exactly the permitted three axioms.  The changed Lean additions contain
no `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats`; `git diff
--name-only origin/erenup/integration-section3...HEAD` lists only the new
T24 module/probe/axiom files plus lane records, with no pre-existing module
modified.

## 3. Gaps

There is no Uc2 theorem or proof gap.  Two assembly/documentation notes remain:

1. The positive probe does **not** construct an inhabitant of
   `ClassicalSolutionT`; its zero field in `:90-101` is only an integrand
   computation.  The worker is honest about this at `REPORT_395.md:70-76`,
   assigning the actual rest-solution witness (including the heavy `sobolev`
   field) to Uc3.  Thus this should not be described as a full solution
   non-vacuity witness until Uc3 supplies one.
2. `PeriodicPotentialT` and `conservativeForceT` are duplicated locally because
   `Section3/T24/Conservative.lean` is absent on this branch (the HEAD tree has
   only `Section3/T24/PotentialPairing.lean`).  This is explicitly disclosed at
   `PotentialPairing.lean:26-33` and `REPORT_395.md:67-69`; Uc3 must retain one
   canonical copy when lane 392 lands.

I searched the whole Section 4 tree for the claimed missing pairing/rest lemmas:
`grep -RniE 'potential_pairing|potential pairing|conservativeForceT|PeriodicPotentialT|zero.*conservative|conservative.*zero' formalization/NSFormalization/Section4`
returned no matches.  The only nearby pressure-potential results are unrelated
radial-potential gradient lemmas at
`formalization/NSFormalization/Section4/A01/RadialPotential.lean:223-226`.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6` for the build:

```text
LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.PotentialPairing
⚠ ... replayed pre-existing NSFormalization.Source/Paper3 warnings ...
Build completed successfully (9353 jobs).

lake env lean ../formalization/NSFormalization/Section3/T24/PotentialPairing.lean
[no output; exit 0]

lake env lean ../research/T24/axioms_uc2.lean
'NSFormalization.Section3.T24.potential_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]

lake env lean ../research/T24/probes/potential_pairing_closes.lean
[no output; exit 0]
```

`make check` exited 0.  Its exact run produced 47,563 lines; the final gate
summary was:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The same global check reports the repository's pre-existing copied-source
`BoundaryCorollary.lean:90` admission token; it is not in this lane's diff or
the imported Uc2 module.  `verification/` was untouched, so the conditional
`scripts/gates.sh`/base-ref contract gate was not applicable.

For the required substantive negative check I added
`research/T24/probes/rev395_mutated_constant.lean:1-27`, changing only the main
conclusion's constant from `0` to `1`.  `lake env lean` exits 1 with the
expected error at line 26:

```text
error: Type mismatch
  potential_pairing ... = 0
but is expected to have type
  ... = 1
MUTATION_EXIT=1
```

No argument was dropped or merely renamed.  No `scripts/gates.sh` invocation
was needed under the stated “if `verification/` was touched” condition.

The hygiene checks were also clean for the lane additions:

```text
git diff --check origin/erenup/integration-section3...HEAD
DIFF_CHECK_EXIT=0
git diff --name-only origin/erenup/integration-section3...HEAD -- '*.lean'
formalization/NSFormalization/Section3/T24/PotentialPairing.lean
research/T24/axioms_uc2.lean
research/T24/probes/potential_pairing_closes.lean
```

The forbidden-token and `maxHeartbeats` scans over changed Lean additions
printed no matches.

Verdict: ACCEPT-WITH-NOTES

Fixes (one line each):

- Uc3: deduplicate the two T24c vocabulary definitions against lane 392's canonical `Conservative.lean`.
- Uc3: add an actual `ClassicalSolutionT` rest witness for the non-vacuity claim, or label the current probe explicitly as zero-integrand-only.
