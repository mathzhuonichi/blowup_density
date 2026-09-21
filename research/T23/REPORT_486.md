# Lane 486 — T23 U8 interior blow-up and lifespan

## 1. Statements

All four U8 API fields are proved over the authorized upstream family facts:
`U8.blowup`, `U8.blowup_limsup`, `U8.lifespan`, and `U8.maximal`, in namespace
`NSFormalization.Section3.T23`. They retain the actual `DomainPlacementData`,
reference solution, cutoff `D`, family threshold and total velocity/pressure/force.
The probe supplies each exact canonical field target with `exact`.

`scaledPacket_speedUnbounded` consumes the existing I03 implementation
`speed_unbounded_at_target` and `zeroPastField_speed`. The packet's raw
`SpeedUnboundedAtOne` clause is its only blow-up input. `interior_blowup` and
`U8.interior` strengthen each positive-level witness to membership in both the
prescribed packet ball and Ω. A positive norm makes the packet value nonzero;
`packet_slice_zero` forces the time past activation; spatial support and
cancellation then identify the inserted velocity with the packet there.

`ofReal_le_eLpNormTop_of_continuousAt` proves the local measure step: a strict
superlevel set is a neighborhood of the witness, hence has positive volume.
Only continuity at this interior point is needed. The domain solution's
`SmoothOnClosedSlab.contDiffAt_slice` provides it. No global slice continuity
or regularity of exterior reference values is assumed. The frequently/limsup
argument yields the literal whole-space `A02.speedENorm` limsup at T.

`ClassicalSolutionOmega.speed_bound` bounds every longer solution on the compact
`Icc 0 T × closure Ω`. `domainLifespan_eq_of_interior` obtains the lower bound
from the full-horizon solution and the defining supremum. For the upper bound,
U7's proved `velocity_eq_of_ibp` identifies the two velocities in Ω; the interior
witness contradicts the compact-slab bound. This is the same proved U7 engine
used by `noSlip_uniqueness_of_ibp` and `noSlip_uniqueness_box`.
`restrictHorizon` retains the literal total velocity and pressure fields and
all ten solution clauses, giving maximality on every shorter positive horizon.
`U8.lifespan_box` and `U8.maximal_box` discharge IBP using `ibp_box` and derive
openness/boundedness from the box. No continuation/existence theorem is assumed.

## 2. Files

- `formalization/NSFormalization/Section3/T23/InteriorBlowup.lean`: scaling,
  interior witnesses, local essential supremum, limsup, and two API fields.
- `formalization/NSFormalization/Section3/T23/Lifespan.lean`: compact bound,
  lifespan lower/upper bounds, horizon restriction, two API fields and their
  box specializations.
- `research/T23/probes/T23-U8-interior-blowup_closes.lean`: four exact field
  targets corresponding to canonical `Boundary.lean` and Spec:847,857,863,868,
  plus the two box targets. It assumes no `BoundaryInsertionAPI` witness.
- `research/T23/axioms_T23-U8-interior-blowup.lean` and `axioms_486.log`: all
  **15** production declarations print exactly
  `[propext, Classical.choice, Quot.sound]`.
- `research/T23/ATTEMPTS_T23-U8-interior-blowup.md`: four failed elaboration
  approaches, exact diagnostics and fixes; all subsequently closed.
- `research/T23/T23_SPLIT.md`: U8 status; this report and `imports_486.log`.

No existing Lean module, contract, registry or other lane module was changed.
Skeleton commit `cda74e54` preceded the proofs; every closed declaration was
checkpointed. The pre-existing untracked lane brief was left untouched.

## 3. Gaps and error text

**No residual U8 Lean error.** The four fields close under exactly the permitted
threading: packet speed; family-to-placement scale inclusion; prescribed-ball
containment; U3's literal velocity formula and full-horizon solution with both
field identities; U4's packet slice support; U2's cancellation on that support.
These hypotheses are concrete upstream mathematical facts, not new records,
unconstrained propositions, lifespan inputs or assumed inserted blow-up fields.
U9 must supply them for its chosen matching family.

The smooth-domain G1 dependency remains explicit, as authorized. Its exact
unproved upstream statement is:

```lean
∀ (Ω : Set Space), IsOpen Ω → Bornology.IsBounded Ω →
  IsRegularLevelDomain Ω → IBP Ω
```

This is not a declaration or an added logical assumption in the environment.
The box specializations have no such premise. G0's arbitrary-cutoff repair and
owner decisions on final U9 registration remain outside this lane. The literal
universally arbitrary-D boundary statement is not claimed proved.

Representative resolved diagnostics (full attempted error text is in ATTEMPTS):
`Application type mismatch` for spacetime versus spatial-slice `tsupport`;
`Unknown identifier measure_pos_of_mem_nhds` (fixed namespace);
`Tactic assumption failed` at `⊢ t < T` (fixed conjunction projection);
section proof hypotheses absent without `include` (fixed explicit inclusion).

## 4. Commands and results

Every Lean command sourced `. scripts/lean-env.sh`, ran with
`LEAN_NUM_THREADS=6`, and invoked Lake from `verification/`.

- Prerequisite `lake build NSFormalization.Section3.T23.Boundary
  NSFormalization.Section3.T23.BoxIntegration
  NSFormalization.Section3.T23.LocalCorrectionBridge
  NSFormalization.Section3.T23.StatementRepair`: exit 0, 10087 jobs; includes
  placement, domain solution, local/spatial correction and U7 energy closure.
- `lake build NSFormalization.Section3.T23.InteriorBlowup
  NSFormalization.Section3.T23.Lifespan`: exit 0, 10089 jobs. Existing dependency
  warnings were replayed; neither new module emits a warning.
- `lake env lean` on each new module: exit 0, **zero output**.
- `lake env lean ../research/T23/probes/T23-U8-interior-blowup_closes.lean`:
  exit 0, **zero output**.
- `lake env lean ../research/T23/axioms_T23-U8-interior-blowup.lean`:
  exit 0; all 15 exact three-axiom lists checked programmatically.
- Existing `boundary_api_on_canonical.lean`: exit 0, **zero output**. This
  independently rechecks the existing literal Spec-to-canonical record and
  definition adapters used by the field probe.
- `make check`: exit 0; 54 registered contracts, 13 policy tests, 45 consistent
  work items. The existing broad umbrella inventory still reports its historical
  BoundaryCorollary admission and `source_hashes_match: false`; these are not
  failures in this lane's import closure.
- `cd verification && LEAN_NUM_THREADS=6 lake test`: exit 0, 11015 jobs
  (the `make test` recipe's Lake action, run inside verification as required).
- `LEAN_NUM_THREADS=6 make test-mutations`: exit 0; implementation refactor
  accepted, admission/extra-axiom/weakened-hypothesis cases rejected as required.
- `git diff --check`: exit 0. Forbidden-token/heartbeat grep on the two new
  modules: no matches. Comment-aware recursive import traversal: 1652 modules,
  no unresolved imports and no `Paper1.BoundaryCorollary` import.

No push, merge or rebase was performed.
