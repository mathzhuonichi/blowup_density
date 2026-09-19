ACCEPT

# Review of lane 445-T18-U11-sobolev-rate

## 1. What the lane claims

The worker claims the selected constant and all five propositional U11 fields,
with no hypotheses beyond the `InsertionData` projections
(`research/T18/REPORT_445.md:5-35`).  It also claims nine supporting
path-algebra/order-lowering declarations (`research/T18/REPORT_445.md:38-48`),
no residual mathematical gap (`research/T18/REPORT_445.md:63-79`), and clean
build/axiom/policy gates (`research/T18/REPORT_445.md:81-99`).

The claimed mathematics is the requested one.  The paper has

- `F_ε`: `C_s(ε^(1/2)+ε^(1/2-s))` on `0≤s≤1`
  (`paper/sections/03-torus.tex:133-138`);
- `H_ε`: `C_s(ε^(3/2)+ε^(3/2-s))` on `0≤s≤1`
  (`paper/sections/03-torus.tex:232-242`);
- `g_ε-g`: `C_s(ε^(1/2-s)+ε^(3/2-s))` on `0≤s<1/2`, plus convergence for
  `s<0` (`paper/sections/03-torus.tex:304-310`); and
- the stated proof route: absorb the lower-order terms using `0<ε≤1`, then
  lower the order from zero for the negative tail
  (`paper/sections/03-torus.tex:341-345`).

These are exactly the six reconciled Spec fields, including quantifier order,
strict positivity of the selected constant, honest `MemForceSobolevT` guards,
the `Ioc 0 ε₀` scale range, and the right-neighborhood limit
(`research/T18/Spec.lean:1925-1967`; `research/T18/T18_SPLIT.md:190-201`).

## 2. What is in Lean

Statement fidelity is exact:

- `forceDiffSobolevConst` is the reported
  `2 * (scaling.sobolevConst s + correction.sobolevConst s)`
  (`formalization/NSFormalization/Section3/T18/SobolevRate.lean:194-197`).
- `forceDiffSobolevConst_pos` has precisely the Spec range `0≤s<1/2`
  (`formalization/NSFormalization/Section3/T18/SobolevRate.lean:199-208`).
- `forceDifference_sobolev_memLp` is exactly the positive-order honesty field
  (`formalization/NSFormalization/Section3/T18/SobolevRate.lean:210-224`).
- `forceDifference_sobolev_bound` has exactly the two requested exponents and
  no additional argument (`formalization/NSFormalization/Section3/T18/SobolevRate.lean:226-232`).
- `forceDifference_negativeSobolev_tendsto` uses `s<0`, `𝓝[>] 0`, the actual
  force difference, and target zero in `ℝ≥0∞`
  (`formalization/NSFormalization/Section3/T18/SobolevRate.lean:299-328`).
- `negative_s_memLp` is exactly the negative-order honesty guard
  (`formalization/NSFormalization/Section3/T18/SobolevRate.lean:330-337`).

The standalone conformance record copies the six field types
(`research/T18/probes/u11_closes.lean:75-103`) and discharges each canonical-to-
Spec bridge (`research/T18/probes/u11_closes.lean:166-213`).  Its direct Lean
check is silent.  Thus the report does not merely paraphrase the declarations.

The proof consumes the exact upstream record fields.  T15 supplies positivity,
an honest path, and the packet bound at
`formalization/NSFormalization/Section3/T15/Scaling.lean:403-437`; T17 supplies
the corresponding correction fields at
`formalization/NSFormalization/Section3/T17/Correction.lean:265-281`.  The
force decomposition is definitionally the paper's `g+H+F`
(`formalization/NSFormalization/Section3/T18/Insertion.lean:70-73`) and is
cancelled honestly at
`formalization/NSFormalization/Section3/T18/SobolevRate.lean:184-192`.
The absorption uses `place.eps_le_one`, both positivity fields, and both exact
bounds (`formalization/NSFormalization/Section3/T18/SobolevRate.lean:233-297`).

The supporting infrastructure is substantive rather than a named input:
datum/path addition is proved at lines 31-98, path-infimum evaluation and
Minkowski at lines 100-136, and T11-based order lowering at lines 138-180.
T11's multiplier and reweight theorem are genuine checked-in declarations
(`formalization/NSFormalization/Section3/T11/Persistence.lean:47-68,90-111`).
The negative tail then squeezes the order-`s` norm by the proved order-zero
bound (`formalization/NSFormalization/Section3/T18/SobolevRate.lean:310-328`).

There is no vacuity trap.  `ε₀` is a positive minimum
(`formalization/NSFormalization/Section3/T18/Insertion.lean:98-110`), there is
no `toReal`/`⊤` shortcut in the lane module, and all named main-theorem
hypotheses are used.  The reviewer non-vacuity probe witnesses `ε=ε₀`, honest
paths at `s=0` and `s=-1`, and strict positivity at `s=0`
(`research/T18/probes/rev445_nonvacuity.lean:12-32`); it elaborates silently.
As already documented for U1, the tree still has no fully concrete
`InsertionData` assembly, so this is the strongest in-scope non-vacuity check
available without assuming the later T15/T17 assembly lanes.

Hygiene is clean.  The base diff adds one new formalization module and five
research/record files; no existing Lean module is modified.  The only existing
file changed is the brief-required U11 status record
(`research/T18/T18_SPLIT.md:203-206`).  There is no `sorry`, `admit`, `axiom`,
`native_decide`, or `maxHeartbeats` in the module, conformance probe, axiom
file, or reviewer probes.  All citations checked above point to the claimed
paper or record statement.

## 3. Gaps

There is no theorem, statement, axiom, or build gap in this lane.

The report's sole absence claim is accurate: `research/T17/REPORT_438.md` is
not on this base (`research/T18/REPORT_445.md:70-79`), and `rg --files | rg
'REPORT_438'` returns no match.  The required whole-Section4 exact-name search
for `norm_datum_mono`, `periodicSobolevSq_mono`,
`periodicVectorSobolevNorm_mono`, `forceSobolevENormT_mono_order`, and
`memForceSobolevT_mono_order` returns no match (exit 1).  A broader search does
find the Euclidean, non-torus analogue `forceSobolevENorm_mono_order`
(`formalization/NSFormalization/Section4/R41/NonDensityL1.lean:40-55`), which
does not operate on T10's `PeriodicSobolev`/`forceSobolevENormT`.  The lane
therefore correctly builds the torus theorem from the available T11
`persistenceDown`; it does not make a false "not in the tree" claim.

The substantive negative check halves the absorbing constant
(`research/T18/probes/rev445_mutation.lean:14-24`).  Reusing the accepted proof
then fails at the changed conclusion, as required; this is a constant mutation,
not a dropped argument.

## 4. Commands and results

All Lake commands below were run from `verification/` after
`. ../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

`lake build NSFormalization.Section3.T18.SobolevRate` exited 0.  It replayed
warnings only from pre-existing dependencies (for example
`Source.FiniteHilbertBochner`, `Paper1.PeriodicSobolevHilbert`, and vendor
`Formal.EndpointSafeTwoSpacePicard`); there was no output attributed to
`SobolevRate`.  The exact concluding output was:

```text
Build completed successfully (10019 jobs).
```

Both required direct checks exited 0 with exactly zero output:

```text
lake env lean ../formalization/NSFormalization/Section3/T18/SobolevRate.lean
<no output>

lake env lean ../research/T18/probes/u11_closes.lean
<no output>
```

`lake env lean ../research/T18/axioms_u11.lean` exited 0.  Its exact output
(line wrapping retained where Lean emitted it) was:

```text
'NSFormalization.Section3.T18.periodicFourierCoeff_add_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T18.periodicDatum_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.memForceSobolevT_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.forceSobolevENormT_eq_of_path_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T18.forceSobolevENormT_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.persistenceDown_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.forceSobolevENormT_mono_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.memForceSobolevT_mono_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.force_difference_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.forceDiffSobolevConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.forceDiffSobolevConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.forceDifference_sobolev_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.forceDifference_sobolev_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.forceDifference_negativeSobolev_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T18.negative_s_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus every one of the 15 audited declarations depends on exactly
`[propext, Classical.choice, Quot.sound]`.

`make check` exited 0.  The command emits a roughly 1.1 MB registered-closure
inventory; the following are the selected verbatim invariant-bearing lines
(the closure lists are omitted):

```text
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The pre-existing inventory also printed `"source_hashes_match": false` and the
known copied `Paper1/BoundaryCorollary.lean:90` `sorry`; neither is in this
lane's import/module diff, and the checker deliberately exited 0.

Reviewer checks:

```text
$ lake env lean ../research/T18/probes/rev445_nonvacuity.lean
<no output>
exit 0

$ lake env lean ../research/T18/probes/rev445_mutation.lean
../research/T18/probes/rev445_mutation.lean:24:2: error: Type mismatch
  forceDifference_sobolev_bound data s hs hsHalf ε hε
has type
  (forceSobolevENormT 1 s fun z => force data ε z - data.g z) ≤
    ENNReal.ofReal (forceDiffSobolevConst data s * (ε ^ (1 / 2 - s) + ε ^ (3 / 2 - s)))
but is expected to have type
  (forceSobolevENormT 1 s fun z => force data ε z - data.g z) ≤
    ENNReal.ofReal (smallerForceDiffSobolevConst data s * (ε ^ (1 / 2 - s) + ε ^ (3 / 2 - s)))
exit 1
```

Changed-file and hygiene outputs:

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD
formalization/NSFormalization/Section3/T18/SobolevRate.lean
research/T18/ATTEMPTS_U11.md
research/T18/REPORT_445.md
research/T18/T18_SPLIT.md
research/T18/axioms_u11.lean
research/T18/probes/u11_closes.lean

$ git diff --check origin/erenup/integration-section3...HEAD
<no output>

$ forbidden-token grep over all lane/reviewer Lean files
<no output>

$ grep -rnE 'norm_datum_mono|periodicSobolevSq_mono|periodicVectorSobolevNorm_mono|forceSobolevENormT_mono_order|memForceSobolevT_mono_order' formalization/NSFormalization/Section4
<no output>
exit 1
```

No file under `verification/` was touched, so the conditional
`scripts/gates.sh` and `check_contracts.py --base-ref
origin/erenup/integration-section3` gates were not applicable.  `make check`
did run the ordinary contract architecture check successfully.

Fixes: none.
