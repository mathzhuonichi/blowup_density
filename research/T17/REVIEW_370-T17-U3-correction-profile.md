REJECT

## What the lane claims

The lane’s worker report is missing: neither `research/T17/REPORT_370.md` nor
`/data_8T/ping/blowup_density/tmp/codex/370-T17-U3-correction-profile.last.md`
exists.  The committed attempt log claims the six `CorrectionAPI` fields are
delivered (`research/T17/ATTEMPTS_U3.md:3-10`) and the split status calls the
lane done (`research/T17/T17_SPLIT.md:82-105`).  The paper clause is the fixed
cylinder/profile discussion at `paper/sections/03-torus.tex:245-260`; the
specific source estimates are `CorrectionProfile.lean:49-51,
187-189,201-206,223-228`.

## What is in Lean

The bridge and the analytic transport proofs are real Lean proofs.  The module
defines the profile using bare `x₀,T` at
`formalization/NSFormalization/Section3/T17/CorrectionProfile.lean:64-83`,
proves the curl-slice bridge at `:89-115`, smoothness at `:133-140`, support at
`:145-163`, the chosen constants/nonnegativity at `:171-185`, and the slice
derivative/uniform estimate at `:190-233`.  The identity is proved from the
T16 `LocalPotentialAPI` formulas at `:241-260` and `:263-287`; the cited T16
fields are indeed present at `Section3/T16/LocalPotential.lean:115-145`, and
the Euclidean support/uniform/identity declarations are present at
`Paper1/CorrectionProfile.lean:187-216` and `:223-228`.

However, these declarations are not the exact `CorrectionAPI` field
statements:

* The Spec definitions and chart all take `place : PlacementData P` at
  `research/T17/Spec.lean:684-709`, whereas the module substitutes bare
  `x₀,T` (`CorrectionProfile.lean:64-83`).  The required fields are therefore
  about a different term, not a namespace-only restatement.
* The exact smooth field is `∀ ε ∈ Ioc 0 D.ε₀, ...` at
  `research/T17/Spec.lean:784-786`, but the exported theorem adds
  `hv`, `hθ`, and `hη` (`CorrectionProfile.lean:133-140`).
* The exact support field at `Spec.lean:789-790` has no premises, while the
  theorem adds global smoothness plus both cutoff smoothness and both support
  inclusions (`CorrectionProfile.lean:145-151`).
* The Spec data field is simply `correctionProfileConst : ℕ → ℝ`
  (`Spec.lean:791-796`).  The delivered `def` instead depends on `hv`, cutoff
  smoothness, and compact supports (`CorrectionProfile.lean:171-176`), and its
  nonnegativity theorem carries the same extra inputs (`:179-185`).
* The exact uniform field at `Spec.lean:797-802` has no `D.ε₀ ≤ 1` premise,
  but the delivered theorem requires `hv`, both cutoff smoothness/compactness
  hypotheses, and `hε₀ : D.ε₀ ≤ 1` (`CorrectionProfile.lean:217-224`).
* The exact identity at `Spec.lean:824-830` uses
  `correctionChartPoint place ε z`; the delivered theorem instead uses bare
  `correctionChartPoint x₀ T ε z` and additionally requires `hv` and a
  `LocalPotentialAPI` witness (`CorrectionProfile.lean:263-268`).

The probe itself confirms this is a substitution rather than token-for-token
fidelity: it explicitly says it replaces `place.x₀/place.T` at
`research/T17/probes/correction_profile_closes.lean:6-18`, and its field
theorems visibly retain the added premises at `:37-84`.  The attempt log
acknowledges both unresolved issues: global smoothness is absent from
`CorrectionAPI` (`research/T17/ATTEMPTS_U3.md:67-79`), and placement bundling
is deferred (`:93-104`).  The requested identity route was
`physicalCorrection_eq_profile` via `inverseScale` (`T17_SPLIT.md:85-90`);
the module instead calls `physicalCorrection_rescale` directly
(`CorrectionProfile.lean:285-287`).

The non-vacuity claim is also overstated.  The probe comments call `constRef`
“smooth and divergence-free” (`correction_profile_closes.lean:94-104`), but
the existential only proves `v ≠ 0`, smoothness, `D.ε₀ ≤ 1`, and five profile
properties (`:107-131`); it proves neither a divergence-free nor a periodic
hypothesis, and it does not witness the identity field.  The attempt log
concedes that identity non-vacuity waits for an unlanded assembly
(`ATTEMPTS_U3.md:81-91`).

## Gaps

1. **Blocking statement-fidelity failure.**  The six exported declarations do
   not have the Spec types: they add hypotheses and replace `place` by two
   unrelated parameters.  Fix by copying the exact `PlacementData` block
   (the source block is `research/T17/Spec.lean:571-660`) when no canonical T15
   module is available, and expose exact field-shaped theorems/constructor
   lemmas.  Resolve the missing global `ContDiff` obligation either by adding
   the corresponding API field or by implementing the local truncation route;
   the current `reference_periodic`-only API is at `Spec.lean:776-779`.

2. **Blocking deliverable/non-vacuity failure.**  There is no worker report,
   and the probe has no concrete `LocalPotentialAPI` witness for the identity.
   Add the report and a genuine identity non-vacuity instance after the T16
   assembly lands.  If retaining the constant example, prove its divergence
   and periodicity explicitly rather than leaving them only in a comment.

3. **Requested identity route not followed.**  Rework (or explicitly bridge)
   the proof through `Paper1.CorrectionProfile.physicalCorrection_eq_profile`
   and `inverseScale` (`Paper1/CorrectionProfile.lean:218-228`) so it matches
   the brief’s chart-point requirement, rather than silently using the direct
   rescaling lemma.

The “not in tree” searches were performed over the required trees.  They found
the existing zero-only constructor `localPotential_zero` at
`Section3/T16/LocalPotential.lean:295` but no general `localPotential` assembly,
and no `PlacementData` declaration under `formalization/NSFormalization`; the
absence claims are therefore only valid with that qualification.  No existing
module is modified in the lane diff, and the changed Lean files contain no
`sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` token.

## Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6` and one Lake process at a time.

* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.CorrectionProfile` — exit 0; exact final output: `Build completed successfully (9358 jobs).`  The replay emitted pre-existing dependency linter warnings, not warnings from this module.
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T17/CorrectionProfile.lean` — exit 0, no output.
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/correction_profile_closes.lean` — exit 0, no output.
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T17/axioms_u3.lean` — exit 0.  Every printed declaration reports exactly `[propext, Classical.choice, Quot.sound]` (12 declarations; no other axioms).
* `make check` — exit 0; final output was `45 work items: ownership, contract registration and task cards consistent.`
* `LEAN_NUM_THREADS=6 BASE_REF=origin/erenup/integration-section3 scripts/gates.sh NSFormalization.Section3.T17.CorrectionProfile` — exit 0; final lines were `Mutation suite passed. This is an infrastructure check, not a PDE proof.`, `base_compatibility_checked: true`, and `== gates OK`.
* `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` — exit 0; exact tail: `"base_compatibility_checked": true,` and `"scope": "Architecture checks only; run lake test for Lean type and axiom checks."`.
* Reviewer negative probe `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/rev370_support_mutation.lean` — expected exit 1 after widening `Icc (-2) 2` to `Icc (-3) 3`; exact error: `Type mismatch ... correction_profile_support ... has type ... ⊆ fixedProfileCylinder D but is expected to have type ... ⊆ Icc (-3) 3 ×ˢ Metric.closedBall 0 D.θRadius` (`rev370_support_mutation.lean:24`).

REJECT — fixes: restore exact `PlacementData`-based field signatures and resolve
global smoothness; add the missing report and identity non-vacuity witness;
follow the specified `physicalCorrection_eq_profile`/`inverseScale` route.
