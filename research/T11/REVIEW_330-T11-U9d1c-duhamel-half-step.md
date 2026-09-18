ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims `NSFormalization.Section3.T11.torusHalfStepInput : TorusHalfStepInput`
is proved outright, together with the two unconditional persistence consumers and a
non-vacuity witness (`research/T11/REPORT_330.md:3-44`).  The claimed target is the
`Persistence.lean` target verbatim: `TorusHalfStepInput` quantifies
`ν > 0`, a `TorusTwoSpaceContract`, `a,g,T`, the order-three datum/force/mild
hypotheses, then `r ≥ 3` and a continuous reweighted realization `v`, and concludes
an order-`r+1/2` continuous path reweighting `v` (`formalization/NSFormalization/Section3/T11/Persistence.lean:165-186`).
The independent probe copies that full binder sequence and discharges it with the
lane theorem (`research/T11/probes/duhamel_half_step_closes.lean:33-54`).

The report’s route is a top-order smooth force integral plus a fractional endpoint-safe
nonlinear Duhamel integral (`research/T11/REPORT_330.md:46-68`).  This is implemented by
the continuous real-order Leray force path (`formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean:182-218`),
the endpoint-safe contract (`:264-298`), continuity on `Ico` (`:300-339`), and the
coefficient identity transporting the order-three mild equation (`:373-471`).

## 2. What is in Lean

Statement fidelity is good.  The public theorem is exactly
`theorem torusHalfStepInput : TorusHalfStepInput` (`formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean:473-492`),
and the two advertised consumers have the same hypotheses and conclusions as
`Persistence.lean` (`formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean:494-526`; compare
`formalization/NSFormalization/Section3/T11/Persistence.lean:188-243`).  No hypothesis was
silently added: the only assumptions in the target are the source target’s `hν`, `hT`,
datum/path/Leray/mild hypotheses, and `hr`, `hv`, `hvu` (`Persistence.lean:173-186`).
There is no named `Prop` input or alias in the new module (the only instances are the
explicitly named `halfStepNormedGroup` and `halfStepNormedSpace`,
`DuhamelHalfStep.lean:22-28`).

The mathematical vocabulary matches the cited source definitions: the paper gives the
torus weight `(1+4π²|k|²)^s` and Fourier realization (`paper/sections/01-introduction.tex:80-96`),
the Leray/heat projected equation and torus pressure convention (`paper/sections/02-preliminaries.tex:80-114`),
and the T11 reconciliation records the exact API field locations and quantifier choices
(`research/T11/RECONCILIATION.md:50-63`).  The tree lemmas used by the proof are the
real-order convolution transport (`formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:714-747`),
fractional smoothing and its endpoint kernel (`formalization/NSFormalization/Section3/T11/FractionalSmoothing.lean:251-317`),
and integer-order continuous datum paths (`formalization/NSFormalization/Section3/T10/ForcePaths.lean:82-107`).

Non-vacuity is substantive: the module supplies the constant initial/force/mild family
(`DuhamelHalfStep.lean:529-577`), and the probe proves every produced order datum is
nonzero for a nonzero constant component (`research/T11/probes/duhamel_half_step_closes.lean:108-143`).
The contract premise is independently inhabitable from the predecessor lane:
`torusConvolutionInput_ofReal` (`formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:784-788`)
feeds `torusTwoSpaceContract_nonempty` (`formalization/NSFormalization/Section3/T11/LocalExistence.lean:237-239`).

## 3. Gaps and hygiene

The worker correctly limits the conclusion to coefficient-level persistence and does not
claim physical Fourier inversion, pressure, time regularity, or the momentum equation
(`research/T11/REPORT_330.md:96-118`; the target itself only asks for the coefficient
reweighting, `Persistence.lean:181-186`).  The module has no `sorry`, `admit`, `axiom`,
`native_decide`, or `maxHeartbeats`; the only grep matches are the audit comments using
the word “axiom” (`DuhamelHalfStep.lean:1-577`,
`research/T11/probes/duhamel_half_step_closes.lean:1-159`,
`research/T11/axioms_duhamel_half_step.lean:1-186`).  The axioms audit contains 45
`#print axioms` checks (`research/T11/axioms_duhamel_half_step.lean:8-186`), matching the
45 declarations in the module (`DuhamelHalfStep.lean:24-561`); the checks require exactly
`[propext, Classical.choice, Quot.sound]`.

The required whole-Section4 searches were performed before accepting the “not in tree”
claims.  There are no `PeriodicMeanReduction`, `Torus.*Duhamel`, or `torus.*persistence`
matches in `formalization/NSFormalization/Section4`.  However, Section4 does contain a
different whole-space cylinder result named `exists_continuous_datum_path_of_cylinder`
(`formalization/NSFormalization/Section4/A01/ConstructorDatumPath.lean:116-127`) and
whole-space Fourier-jet reconstruction references (`formalization/NSFormalization/Section4/D01/DatumToJets.lean:60-70`).
Therefore the worker’s sentence that “there is no ... version in the tree”
(`research/T11/REPORT_330.md:105-109`) needs one exact documentation fix: qualify it as
“there is no corresponding T10/torus `PeriodicSobolev` slab lemma”; likewise qualify the
Fourier-inversion gap (`REPORT_330.md:101-104`) as the torus-carrier gap.  These are
scope/citation notes, not proof defects.

The lane commit itself adds the new module and records only; no canonical pre-existing
Lean module is modified.  The requested diff check was:

```
PLAN.md
formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean
formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean
logs/AGENT_RUNS.csv
research/T11/ATTEMPTS_CONVOLUTION_BOUND_REAL.md
research/T11/ATTEMPTS_DUHAMEL_HALF_STEP.md
research/T11/EXISTENCE_ROUTE.md
research/T11/REPORT_328.md
research/T11/REPORT_330.md
research/T11/T11_SPLIT.md
research/T11/axioms_convolution_bound_real.lean
research/T11/axioms_duhamel_half_step.lean
research/T11/probes/convolution_bound_real_closes.lean
research/T11/probes/duhamel_half_step_closes.lean
```
The extra predecessor-lane files are present because this branch contains the required
328/329 base merges; the 330 commit changes no existing canonical module.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`, and
`lake` only from `verification/`.

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.DuhamelHalfStep
  warning output only from pre-existing Source/Paper1/vendor files
  Build completed successfully (9987 jobs).

cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean
  [no output; exit 0]

cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/duhamel_half_step_closes.lean
  [no output; exit 0]

cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_duhamel_half_step.lean
  [no output; exit 0]
```

For an unguarded audit generated from the 45 `#print axioms` lines:

```
exit=0 lines=61
'NSFormalization.Section3.T11.halfStepNormedGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
...
'NSFormalization.Section3.T11.persistence_unconditional_constant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
All 45 checks have that same three-axiom set; the line wrapping is Lean’s formatter.

```
make check
  exit 0
  .............
  OK
  45 work items: ownership, contract registration and task cards consistent.

BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T11.DuhamelHalfStep
  extra_axiom: rejected as required
  weakened_hypothesis: rejected as required
  Mutation suite passed. This is an infrastructure check, not a PDE proof.
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
  == gates OK

python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
  exit 0
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
```

The mandatory substantive negative probe is
`research/T11/probes/rev330_negative.lean:1-34`: it changes the target order from
`r + 1/2` to `r + 1` and keeps every hypothesis.  Lean rejects the attempted reuse with
the expected mismatch:

```
exit=1
error: Type mismatch
  torusHalfStepInput ...
has type
  ∃ w, ContinuousOn w (Ico 0 T) ∧ ∀ t ∈ Ico 0 T,
    IsPeriodicReweight r (r + 1 / 2) (v t) (w t)
but is expected to have type
  ∃ w, ContinuousOn w (Ico 0 T) ∧ ∀ t ∈ Ico 0 T,
    IsPeriodicReweight r (r + 1) (v t) (w t)
```

The mutation is therefore substantive and load-bearing, and the lane is accepted with
the two one-line scope qualifications above.
