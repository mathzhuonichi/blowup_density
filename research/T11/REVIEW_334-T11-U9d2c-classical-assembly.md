ACCEPT-WITH-NOTES

## 1. What the lane claims

The report claims that `NSFormalization.Section3.T11.mild_to_classical` closes
the U9d existential target verbatim (`research/T11/REPORT_334.md:11-25`),
that the two residual fields are proved (`REPORT_334.md:27-36`), and that
`exists_classical_of_picard` supplies the restart-shaped positive-horizon
corollary (`REPORT_334.md:44-50`).  It also claims a non-vacuous affine
constant-force instance (`REPORT_334.md:99-103`) and no named peeling input
(`REPORT_334.md:5-7,121-122`).

These statements match the Lean declarations:

- `mild_to_classical` has precisely the quantifier order, positivity, datum,
  Leray, mild-solution, `ClassicalSolutionT`, `PeriodicLocalRegularity`, and
  `Ico` path clauses at `formalization/NSFormalization/Section3/T11/MildClassical.lean:1280-1289`.
- The velocity and pressure fields are exactly the structure fields declared
  in `formalization/NSFormalization/Section3/T10/PeriodicData.lean:265-302`,
  and are supplied by `MildClassical.lean:1296-1311`; the three local-regularity
  fields have the exact shapes in `Section3/T11/LocalTheory.lean:79-100` and
  are assembled at `MildClassical.lean:1312-1319`.
- The residual smoothness lemmas have the claimed slab statements at
  `MildClassical.lean:767-774` and `1222-1229`; the `sobolev_smooth` witness is
  constructed at `MildClassical.lean:1312-1316`.
- The corollary statement is exactly `exists_classical_of_picard` at
  `MildClassical.lean:1323-1327`, and the affine non-vacuity theorem is at
  `MildClassical.lean:1353-1359`.  The probe supplies the coordinate-vector
  nonzero instance and a genuine mild witness in
  `research/T11/probes/mild_classical_closes.lean:87-111`.

The paper’s corresponding requirements are consistent: one-sided smoothness
at time zero is explicit in `paper/sections/02-preliminaries.tex:22-35`, the
torus pressure Poisson/gauge equations are at `paper/sections/02-preliminaries.tex:75-103`,
and the local proposition asks for a common all-order interval and continuation
at `paper/sections/02-preliminaries.tex:105-120`.  The appendix’s mild equation,
repeated time differentiation, and one-sided endpoint statement are at
`paper/sections/appendix-a-local-theory.tex:60-77,109-116`.

## 2. What is in Lean

`persistence_unconditional` is an actual theorem, not a named input, at
`formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean:511-529`; the
bridge to the older `PersistenceInput` shape is proved at
`MildClassical.lean:1208-1219`.  Force persistence and projected-force
continuity are similarly discharged at `MildClassical.lean:1200-1206` and
`1181-1198`.  The pressure, gradient, gauge, Poisson, and projected/momentum
dependencies used by the assembly are genuine upstream lemmas at
`MildPressure.lean:665-706` and `MildMomentum.lean:1423-1461`.

The module has 74 public named declarations plus three explicitly named local
instances (77 guarded declarations); no `def ... : Prop` peeling input is
present.  The only heartbeat override is the commented per-declaration option
at `MildClassical.lean:412-415`, with value 400000.  The forbidden-token scan
over the module, probe, and axiom file produced exactly one line:
`MildClassical.lean:414:set_option maxHeartbeats 400000 in`.
The formalization diff against the integration branch contains only the new
Lean module (`git diff --name-status ... -- formalization/NSFormalization`
reports `A .../MildClassical.lean`); no existing Lean module is modified.

The axiom audit has 77 `#guard_msgs`/`#print axioms` pairs in
`research/T11/axioms_mild_classical.lean:1-314`; the file typechecks, so each
reports exactly `[propext, Classical.choice, Quot.sound]`.

## 3. Gaps and negative checks

The report’s substantive gap claims are honest: the Picard horizon depends on
the datum and force bounds (`MildClassical.lean:1336-1346`, with the quantitative
source at `Section3/T11/LocalExistence.lean:604-628`), so it does not discharge
the named quantitative input still consumed by `Restart.lean:70-103`.
Uniqueness and continuation are not asserted by this lane.

The required substantive mutation was made in the read-only probe
`research/T11/probes/rev334_widen_interval.lean:12-19`, changing the affine
conclusion from `Ico 0 1` to the wider `Icc 0 1`.  Running it gives the expected
failure (exit 1), exactly:

```text
../research/T11/probes/rev334_widen_interval.lean:18:2: error: Type mismatch: After simplification, term
  mild_to_classical_affine_constant hν C 1 one_pos c
 has type
  ∃ w,
    PeriodicLocalRegularity ν (fun x => c) (fun x => c) 1 w ∧
      (IsPeriodicSobolevPathOn 3 (Ico 0 1) w.velocity fun t => (1 + t) • torusConstantDatum 3 c) ∧
        ∀ (x : Space), w.velocity (0, x) = c
but is expected to have type
  ∃ w,
    PeriodicLocalRegularity ν (fun x => c) (fun x => c) 1 w ∧
      IsPeriodicSobolevPathOn 3 (Icc 0 1) w.velocity fun t => (1 + t) • torusConstantDatum 3 c
```

The non-vacuity instance in the ordinary probe passes and proves the recovered
velocity is nonzero at the origin.

For the report’s “not in the tree” wording, the mandated whole-Section4 grep
found `formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean:715-729`
(`datumPath_contDiffOn_all_orders`) and its use at
`Section4/A01/JointRepresentative.lean:590`.  Those declarations are an R3/
Euler cylinder result with different carriers and a strong `hall` hypothesis;
they do not provide the torus `Section3/T10.ForcePaths.continuous_datum_path`
upgrade (whose exact global statement is `Section3/T10/ForcePaths.lean:82-105`).
Thus the gap is substantively real for this torus route, but the report’s
literal “no ... variant in the tree” sentence should be qualified.

Two exact one-line documentation fixes are requested:

1. Change `1354 lines` to `1384 lines` in `research/T11/REPORT_334.md:73-75`
   and `research/T11/EXISTENCE_ROUTE.md:547-548`.
2. At `REPORT_334.md:113-116`, say “no **torus-specific** slab variant is
   available; Section4/A01 has the differently typed R3 lemma ...” (and make
   the same qualification in the corresponding `EXISTENCE_ROUTE.md` prose if
   retained).

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6`.

```text
lake build NSFormalization.Section3.T11.MildClassical
RC=0
Build completed successfully (9993 jobs).
```
The build log contains only pre-existing warnings in upstream Paper1/Source/
HeliCorgi files; no warning points into `MildClassical.lean`.

```text
lake env lean ../formalization/NSFormalization/Section3/T11/MildClassical.lean
exit=0
lake env lean ../research/T11/probes/mild_classical_closes.lean
exit=0
lake env lean ../research/T11/axioms_mild_classical.lean
exit=0
```
All three commands produced no output.  The first probe closes the verbatim
target, residual fields, restart-shaped corollary, and nonzero instance; the
axiom file’s 77 guards pass.

`make check` exited 0.  Its exact summaries include:

```text
test_contract_policy ... OK
45 work items: ownership, contract registration and task cards consistent.
```

`make test` exited 0; its final contract replay line is:

```text
info: Tests/CompletedDensity.lean:20:0: Contract BlowupDensity.Tests.checkedCompletedDensity: checked; standard logical axioms only
```

The additional gate replay, run with the required Section3 base, was:

```text
BASE_REF=origin/erenup/integration-section3 scripts/gates.sh NSFormalization.Section3.T11.MildClassical
RC=0
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
== gates OK
```

The lane did not touch `verification/`; nevertheless this explicitly reran the
contract check against `origin/erenup/integration-section3`.

Verdict: ACCEPT-WITH-NOTES. Fixes: (1) correct the two stale 1354-line counts
to 1384; (2) qualify the “not in tree” slab-datum claim as torus-specific and
mention the differently typed Section4/A01 result.
