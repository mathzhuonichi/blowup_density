# Lane 197 — second review fixes and gates

## Rebase

Ran `git fetch origin && git rebase origin/erenup/integration` after temporarily
stashing the supplied review artifacts, then restored them. Integration tip:
`2536a9d`. Default rebase dropped the merge commit; skipped lane 194's replayed
content commit because its content is already landed. Markdown conflicts kept
integration's `A3_SPLIT.md`. The final net patch has only the bridge module and
lane-local records/probes, with no deletions relative to integration.

## Elaboration attempts

The old 800000 allowance was noncompliant. Merely extracting the value formula,
or replacing its linear-map rewrites with a small helper, still exhausted 400000
when later rewriting the expanded dependent path. The successful proof isolates
linear evaluation in `value_residual_linear`, transports values in
`unprojectedResidual_value`, and combines equalities using `congrArg₂` and
transitivity. `residual_difference_gradient` separately cancels the common
Laplacian and applies cylinder-gradient range membership. Both larger lemmas
pass with local `maxHeartbeats 400000`; no global limit was raised.

The lift and datum steps remain separate lemmas. Landed `InteriorMomentum`
replaces the former copied time-derivative helper module. The fix6 wrapper uses
`ha`, the all-order family before `hpaths`, and the order-q pair chosen from
`hpairs q hq`. Its positive probe uses exactly that binder order.

The consumer probe now imports and calls the landed complement-path adapter.
Its two missing inputs are proved locally: physical residual agreement from
lane 194, and the projected identity from the new export after datum uniqueness.
The sign probe keeps the wrong-sign rewrite as a required failure inside
`fail_if_success`, then checks the correct theorem, so every probe is a passing
gate rather than retaining an intentionally uncompilable file.

## Final gates

Source `. scripts/lean-env.sh`; run Lake commands from `verification/` with
`LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section4.A01.LerayBridge`: exit 0,
  `Build completed successfully (10249 jobs).`
- `lake env lean ../formalization/NSFormalization/Section4/A01/LerayBridge.lean`:
  exit 0, no output.
- `lake env lean ../research/A01/axioms_leray_bridge.lean`: exit 0; every audited
  declaration prints exactly `[propext, Classical.choice, Quot.sound]`.
  Original zero-carrier examples also pass.
- `lake env lean ../research/A01/probes/leray_bridge_195.lean`: exit 0;
  the canonical consumer composition prints only the three standard axioms.
- `lake env lean ../research/A01/probes/rev197_consumer_gap.lean`: exit 0.
- `lake env lean ../research/A01/probes/rev197_heartbeat_400k.lean`: exit 0;
  the refactored membership proof body passes under the hard ceiling.
- `lake env lean ../research/A01/probes/rev197_sign_mutation.lean`: exit 0;
  the wrong-sign rewrite is rejected by the negative assertion.
- `LEAN_NUM_THREADS=6 make check`: exit 0, including all 13 policy tests and
  `30 work items: ownership, contract registration and task cards consistent.`
- Diff whitespace and scope checks pass. No verification files changed and no
  pre-existing module was edited. No push was performed.

Logs from these runs: `/tmp/197-build.log`, `/tmp/197-lean.log`,
`/tmp/197-consumer.log`, `/tmp/197-check.log`. The supplied second review is
preserved and staged together with the updated heartbeat and consumer probes.
