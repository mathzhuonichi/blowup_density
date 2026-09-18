ACCEPT-WITH-NOTES

## What the lane claims

The current (r1) portion of the worker report claims the all-
`p : ℝ≥0∞` Haar/cube identity, API bridges, scalar and gradient-tensor
specializations, and `Function.support`/`tsupport` whole-space transfer
(`research/T12/REPORT_366.md:19-42`). Those are exactly the obligations in U1
(`research/T12/T12_SPLIT.md:50-56`), including the forms consumed by U4/U5
(`research/T12/T12_SPLIT.md:82-103`). The worker's initial r0 preamble still says
that the general identity is open and that the full gates were not run
(`research/T12/REPORT_366.md:3-13`); that text is superseded by the r1 completion,
but should be removed or explicitly labelled historical.

The cited paper content is correctly identified. The paper gives the localized
periodic/fundamental-cube calculation and the order-zero/order-one endpoint
identities at `paper/sections/03-torus.tex:22-30` and
`paper/sections/03-torus.tex:95-98`; its periodic tiling argument is at
`paper/sections/03-torus.tex:53-72`. The cited tree lemmas exist with the
advertised statements: closed versus half-open cube a.e. equality at
`formalization/NSFormalization/Section3/T13/TorusIdentity.lean:402-415`, the
continuous cube `lintegral` bridge at `formalization/NSFormalization/Section3/T13/TorusIdentity.lean:419-445`, the
torus-point/lift identities at `formalization/NSFormalization/Section3/T13/TorusIdentity.lean:456-461`, and the prior
supported `p = 2` endpoint at
`formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean:364-374`.
The general-`p` result is a legitimate strengthening of those cited endpoints,
as requested by the lane brief.

## What is in Lean

The API bridge is definitionally exact:
`periodicLpENorm_eq_eLpNorm_torusLift` is `rfl`
(`formalization/NSFormalization/Section3/T12/HaarCube.lean:60-62`), matching
`periodicLpENorm` in `formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean:69-73`.
The private chart is definitionally `torusLift = v ∘ torusChart`
(`formalization/NSFormalization/Section3/T12/HaarCube.lean:70-74`). Its measurable embedding is constructed from the
torus measurable equivalence, subtype inclusion, and `toSpace`
(`formalization/NSFormalization/Section3/T12/HaarCube.lean:85-93`), and the pushforward identity to
`volume.restrict fundamentalCube` is proved in `formalization/NSFormalization/Section3/T12/HaarCube.lean:98-138`.
The half-open/closed replacement used there is the cited a.e. equality, not an
empty-interval or endpoint-zero shortcut.

The public theorem statements are faithful and complete:

* all `p`, generic normed target, with the periodic interface hypothesis, at
  `formalization/NSFormalization/Section3/T12/HaarCube.lean:150-154`;
* smooth periodic corollary at `formalization/NSFormalization/Section3/T12/HaarCube.lean:158-162`;
* scalar specialization at `formalization/NSFormalization/Section3/T12/HaarCube.lean:166-170`;
* exact gradient carrier `Space → WithLp 2 (Fin 3 → Space)` at
  `formalization/NSFormalization/Section3/T12/HaarCube.lean:175-179` (the carrier is the T12 definition at
  `formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean:82-85`);
* API-to-cube bridges, scalar/generic and gradient forms, at
  `formalization/NSFormalization/Section3/T12/HaarCube.lean:183-193`;
* generic support transfer at `formalization/NSFormalization/Section3/T12/HaarCube.lean:199-204`, vector specialization
  at `formalization/NSFormalization/Section3/T12/HaarCube.lean:207-211`, and the requested `tsupport` scalar/vector
  forms at `formalization/NSFormalization/Section3/T12/HaarCube.lean:215-226`.

The proof uses Mathlib's measurable-embedding norm-change theorem, whose source
explicitly handles `p = 0`, `p = ⊤`, and finite `p`
(`verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:888-895`).
Thus no extra measurability premise is silently omitted. The periodicity
hypotheses are deliberately interface hypotheses: the canonical torus chart
reads one fundamental representative, so the equality is in fact valid for any
field. They are named `_hv` in the main proof (`formalization/NSFormalization/Section3/T12/HaarCube.lean:150-154`) and
are documented as such (`formalization/NSFormalization/Section3/T12/HaarCube.lean:146-149`); this is a stronger theorem,
not a vacuous hypothesis. The vector theorem asks for periodicity of the exact
`gradientTensor v` carrier (`formalization/NSFormalization/Section3/T12/HaarCube.lean:175-179`), which is honest and
leaves any derivative-periodicity lemma to the downstream U5 lane.

The required two-mode probe is substantive: it constructs the two-mode field,
proves its periodicity, and instantiates the transfer at `p = 3`, `p = 6`, and
`p = ⊤` (`research/T12/probes/haar_cube_closes.lean:90-118`), then checks the
API-to-cube bridge at 3 and 6 (`research/T12/probes/haar_cube_closes.lean:120-137`) and nonzero
Fourier coefficients (`research/T12/probes/haar_cube_closes.lean:139-149`). The independent
support probe constructs a nonzero smooth bump and proves strict interior support
before applying the theorem at 3 and 6
(`research/T12/probes/rev366_nonvacuity.lean:17-82`).

## Gaps

No mathematical gap remains in the current r1 module. There are no named goal
inputs, aliases of the target, endpoint exclusions, or vacuous cube hypotheses.
The recursive search over `formalization/NSFormalization/Section3/T10`, `T12`,
and `T13` found only the earlier `p = 2`/endpoint and periodic-kernel results
outside this module; no pre-existing all-`p` Haar/cube theorem was being silently
duplicated. The recursive `Section4` search likewise found no missing direct
Haar/cube bridge relevant to the claim.

Hygiene passes. `git diff --name-only origin/erenup/integration-section3...HEAD
-- formalization` contains only the new
`formalization/NSFormalization/Section3/T12/HaarCube.lean`; no existing
formalization module was modified. Anchored scans of the module, probe, and axiom
file find no code-level `sorry`, `admit`, `axiom`, or `native_decide`; there is no
`maxHeartbeats`, and `git diff --check` is clean. The only fix requested is
editorial: delete or label the obsolete r0 preambles in
`research/T12/REPORT_366.md:3-13` and `research/T12/ATTEMPTS_HAAR_CUBE.md:3-7`,
since they precede and contradict the completed r1 block.

## Commands and results

All Lean commands were run after `. scripts/lean-env.sh`; `lake` was run from
`verification/` with `LEAN_NUM_THREADS=6`.

Module build:

```text
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.HaarCube
RC=0
Build completed successfully (9920 jobs).
```

The build replayed warnings from unrelated imported modules, but no warning was
emitted from `HaarCube.lean`. Direct module typecheck was silent:

```text
cd verification && lake env lean ../formalization/NSFormalization/Section3/T12/HaarCube.lean
RC=0
(empty output)
```

The required probe was also silent and successful:

```text
cd verification && lake env lean ../research/T12/probes/haar_cube_closes.lean
RC=0
(empty output)
```

The axiom audit was successful. Every printed declaration has exactly the
standard three axioms (line wrapping is Lean's formatter):

```text
'NSFormalization.Section3.T12.periodicLpENorm_eq_eLpNorm_torusLift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_torusLift_eq_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_torusLift_eq_restrict_smooth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_torusLift_eq_restrict_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_torusLift_eq_restrict_gradientTensor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.periodicLpENorm_eq_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.periodicLpENorm_eq_restrict_gradientTensor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_restrict_eq_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_restrict_eq_of_support_vector' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_restrict_eq_of_tsupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_restrict_eq_of_tsupport_vector' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` exited 0. Its exact first/last output (the middle architecture
JSON is 46,316 lines) was:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 608,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The standard gate script also passed with its default base
`origin/erenup/integration`:

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
== gates OK
RC=0
```

The conditional `check_contracts.py --base-ref origin/erenup/integration-section3`
was not required because `verification/` is untouched. For diagnosis, the same
script against that base fails only on the unrelated missing stable
`verification/Contracts/V1/Localization.lean`; the default-base gate above is
green.

The substantive negative mutation changes the conclusion by adding `+ 1` (not
by dropping an argument) and fails as expected:

```text
../research/T12/probes/rev366_mutation.lean:13:2: error: Type mismatch
  eLpNorm_restrict_eq_of_support w hw p
has type
  eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume
but is expected to have type
  eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume + 1
```

The mutation command exited 1; `rev366_nonvacuity.lean`,
`rev366_required_name.lean`, and `rev366_vector_axioms.lean` exited 0. The
vector axiom probe printed the same standard three axioms.

Verdict: ACCEPT-WITH-NOTES — remove or label the stale r0 preambles in
`research/T12/REPORT_366.md:3-13` and `research/T12/ATTEMPTS_HAAR_CUBE.md:3-7`;
no Lean or mathematical fix is required.
