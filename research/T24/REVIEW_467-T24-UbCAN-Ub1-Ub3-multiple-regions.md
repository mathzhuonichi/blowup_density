ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims a canonical raw-field `MultipleRegionsAPI` with the 30 fields
of `research/T24/Spec.lean`, the raw-clause `multipleRegionsStatement`, and
Ub1--Ub3: prescribed per-region placement/scaling, selected component
solutions, and velocity/force support on the fundamental cube
(`research/T24/REPORT_467.md:3-20`). It explicitly does not claim Ub4--Ub7 or
an inhabitant of the complete 30-field API (`research/T24/REPORT_467.md:41-46`).

That scope matches the brief. The paper prescribes finitely many disjoint
interior balls, positive `nu,T`, small positive scales with
`epsilon_j^2 < T`, a finite superposition, separated supports, separate
blow-up, and the energy/dissipation formulas
(`paper/sections/03-torus.tex:697-722`). The approved split assigns exactly
placement/scaling to Ub1, component selection to Ub2, and single-copy supports
to Ub3 (`research/T24/T24_SPLIT.md:293-307`); it leaves assembly, blow-up, and
energy additivity to Ub4--Ub7 (`research/T24/T24_SPLIT.md:308-326`).

## 2. What is in Lean

### Statement fidelity

The canonical structure is `Type`-valued and has exactly the claimed 30
fields (`formalization/NSFormalization/Section3/T24/Multiple.lean:50-204`).
Field-for-field, it matches the Spec structure
(`research/T24/Spec.lean:1176-1329`), with only the required indexing change:
the Spec's `P : PacketImportAPI nu` is replaced by raw
`u p f K M D`, `PlacementData u p f K`, and
`ScalingAPI u p f K M D`. The two conversions enumerate all 30 fields
(`research/T24/probes/multiple_api_on_canonical.lean:147-209`), and the 30
projection examples check the Spec-side types independently
(`research/T24/probes/multiple_api_on_canonical.lean:211-349`). The raw
universal statement includes the complete imported-packet clause list and
then the prescribed geometry (`formalization/NSFormalization/Section3/T24/Multiple.lean:206-256`);
the probe transports it to the Spec statement without a new premise
(`research/T24/probes/multiple_api_on_canonical.lean:390-403`). This agrees
with the Spec statement (`research/T24/Spec.lean:1331-1345`).

There is no hidden `toReal` finiteness premise or empty interval. The record
has `T_pos`, `N_pos`, and positive radii
(`formalization/NSFormalization/Section3/T24/Multiple.lean:53-67`), and its
chosen scales lie in `Ioc 0 epsilon_0` with strict time smallness
(`formalization/NSFormalization/Section3/T24/Multiple.lean:96-105`). The raw
statement also quantifies `0 < nu`, `0 < T`, `0 < N`, and positive radii
before producing `Nonempty` (`formalization/NSFormalization/Section3/T24/Multiple.lean:207-256`).

`RegionsData` honestly bundles the raw clauses needed by T15 plus the geometry;
it does not assume a placement, scaling record, or component solution
(`formalization/NSFormalization/Section3/T24/MultipleComponents.lean:13-39`).
Its `N_pos` and disjointness fields are intentionally unused by Ub1--Ub3 but
are exactly the carrier fields required by the brief and later Ub4--Ub7, not
named analytic inputs.

Ub1 is present with the claimed statements. `placement` fixes the common
horizon, prescribed center/radius, compact carrier
`K union Prod.snd '' tsupport f`, and a positive radius-dependent threshold
(`formalization/NSFormalization/Section3/T24/MultipleComponents.lean:45-83`).
The carrier and radius facts come from the cited T15 construction
(`formalization/NSFormalization/Section3/T15/Assembly.lean:17-32`), and the
threshold proof is the prescribed-chart adaptation of lane 459
(`formalization/NSFormalization/Section3/T15/Assembly.lean:53-83`).
`placement_time`, `placement_chart`, `scaling`, `epsilon`,
`eps_admissible`, and `eps_time` have the exact field statements
(`formalization/NSFormalization/Section3/T24/MultipleComponents.lean:85-110`).
The scaling constructor really supplies all T15 fields from raw packet clauses
(`formalization/NSFormalization/Section3/T15/Assembly.lean:90-127`).

Ub2 is the actual `Classical.choose` from `ScalingAPI.solution`, followed by
its two field pins
(`formalization/NSFormalization/Section3/T24/MultipleComponents.lean:112-121`).
The consumed T15 field has exactly the existential solution and velocity/
pressure equalities claimed (`formalization/NSFormalization/Section3/T15/Scaling.lean:289-305`).

Ub3 has the exact cube-local statements: velocity for `t in Ico 0 T` and
force for every real `t`
(`formalization/NSFormalization/Section3/T24/MultipleComponents.lean:123-149`).
The proofs use the actual T15 single-copy lemmas with those time domains
(`formalization/NSFormalization/Section3/T15/SingleCopy.lean:144-159` and
`:178-191`), then the actual support transport and `eps_space` containment
(`formalization/NSFormalization/Section3/T15/Placement.lean:76-84`,
`:128-157`, and `:197-227`). This is the support mechanism described by the
paper at `paper/sections/03-torus.tex:706-714` and by the split at
`research/T24/T24_SPLIT.md:303-306`.

The reviewer non-vacuity probe uses the registered packet-import witness,
`N = 1`, the concrete center `(1/2,1/2,1/2)`, radius `3/8`, and T15's proved
interior-ball geometry; it constructs an actual `RegionsData` and exhibits an
index with `0 < epsilon_j` and `epsilon_j^2 < T`
(`research/T24/probes/rev467_nonvacuity.lean:45`). It typechecks with zero
output. Thus the delivered positive scale/time conclusions are not merely
vacuous conditionals over an empty family.

### Hygiene and axioms

The lane adds the two Lean modules rather than modifying an existing Lean
module. The base diff is:

```text
A formalization/NSFormalization/Section3/T24/Multiple.lean
A formalization/NSFormalization/Section3/T24/MultipleComponents.lean
A research/T24/ATTEMPTS_UB1_UB3.md
A research/T24/REPORT_467.md
M research/T24/T24_SPLIT.md
A research/T24/axioms_ub1_ub3.lean
A research/T24/probes/multiple_api_on_canonical.lean
```

`git diff --diff-filter=M --name-only origin/erenup/integration-section3...HEAD -- '*.lean'`
printed nothing. The forbidden-token/heartbeat scan over the delivered Lean
files printed nothing, and `git diff --check` printed nothing. There is no
`set_option maxHeartbeats`.

The 19 canonical audit entries are exactly the required set:

```text
'NSFormalization.Section3.T24.finiteVelocitySum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.finitePressureSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.finiteForceSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.SpeedUnboundedAtOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.MultipleRegionsAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.multipleRegionsStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.placement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.placement_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.placement_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.ε' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.eps_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.eps_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.component' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.component_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.component_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.component_force_support' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The worker report's nine named probe declarations were also re-audited; exact
output was:

```text
'BlowupDensity.T24.Multiple.finiteVelocitySum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T24.Multiple.finitePressureSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T24.Multiple.finiteForceSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T24.Multiple.SpeedUnboundedAtOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T24.Multiple.MultipleRegionsAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T24.Multiple.multipleRegionsStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultipleCanonicalProbe.ofSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultipleCanonicalProbe.toSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultipleCanonicalProbe.regionsData' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Gaps and review note

Ub4--Ub7 remain genuinely outside this lane, exactly as the worker says. The
lane does not provide the finite-sum classical solution, region agreement and
blow-up, or energy/dissipation additivity. It also does not claim
`multipleRegionsStatement` is inhabited.

The required whole-Section4 searches for a pre-existing multiple-regions or
bounded-domain/no-slip implementation found no matches:

```text
$ grep -rniE 'no.?slip|bounded.?domain|boundary collar|restriction norm|homogeneous.*boundary|Dirichlet|vanish.*boundary' formalization/NSFormalization/Section4
[no output; exit 1]
$ grep -rniE 'MultipleRegions|multiple.?regions|prescribed.*regions|prescribed.*balls|single.?copy|affineImage_subset_ball' formalization/NSFormalization/Section4
[no output; exit 1]
```

There is one documentation-only correction. The canonical header says that no
bounded-domain carrier, restriction norm, or no-slip class exists "anywhere in
the current tree" (`formalization/NSFormalization/Section3/T24/Multiple.lean:46-49`).
That is too broad: `BoundedFlowData` is an explicit bounded-domain/no-slip
carrier (`formalization/NSFormalization/Paper1/BoundaryAnalyticBridge.lean:21-42`),
and the registered restriction-norm vocabulary includes `restrictDatum`,
`domainSobolevENorm`, and `restrictField`
(`verification/Contracts/V1/BoundedDomainNorm.lean:25-50`). This does not
change the mathematical verdict: the reconciled T24b Spec deliberately omits
the bounded-domain branch (`research/T24/Spec.lean:1172-1175`), and the lane is
faithful to that Spec. Exact fix: replace the sentence at `Multiple.lean:46-49`
with “The paper's bounded-domain / homogeneous-no-slip branch is outside this
torus API; existing bounded-domain/no-slip vocabulary is not yet threaded into
the reconciled T24b V1 scope.”

The negative check substantively flips the main scale-time inequality rather
than dropping an argument (`research/T24/probes/rev467_negative_eps_time.lean:12-16`).
It fails for the expected reason:

```text
../research/T24/probes/rev467_negative_eps_time.lean:16:2: error: Type mismatch
  RegionsData.eps_time d j
has type
  d.ε j ^ 2 < d.T
but is expected to have type
  d.T < d.ε j ^ 2
```

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake only from `verification/`.

1. Required T15 closure:

```text
$ lake build NSFormalization.Section3.T15.Assembly NSFormalization.Section3.T15.Solution NSFormalization.Section3.T15.SingleCopy
[only replayed dependency linter warnings]
Build completed successfully (10048 jobs).
```

2. Module builds:

```text
$ lake build NSFormalization.Section3.T24.Multiple
[only replayed dependency linter warnings; no Multiple.lean output]
Build completed successfully (10049 jobs).

$ lake build NSFormalization.Section3.T24.MultipleComponents
[only replayed dependency linter warnings; no MultipleComponents.lean output]
Build completed successfully (10050 jobs).
```

3. Direct elaboration and probes:

```text
$ lake env lean ../formalization/NSFormalization/Section3/T24/Multiple.lean
[0 output; exit 0]
$ lake env lean ../formalization/NSFormalization/Section3/T24/MultipleComponents.lean
[0 output; exit 0]
$ lake env lean ../research/T24/probes/multiple_api_on_canonical.lean
[0 output; exit 0]
$ lake env lean ../research/T24/probes/rev467_nonvacuity.lean
[0 output; exit 0]
$ lake env lean ../research/T24/axioms_ub1_ub3.lean
[the 19 exact lines pasted in section 2; exit 0]
$ lake env lean ../research/T24/probes/rev467_negative_eps_time.lean
[the exact expected error pasted in section 3; exit 1]
```

4. `make check` exited 0. Its machine-readable contract-closure listing is
about 1.4 MB. `check_formalization_plan.py` also reported the pre-existing
copied-source `BoundaryCorollary.lean:90` `sorry`,
`source_hashes_match: false`, and `Explicit axiom/admission tokens, all copied
sources: 11`; the lane-local forbidden-token scan above is empty. The exact
terminal checks were:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

5. Full gate script:

```text
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T24.Multiple NSFormalization.Section3.T24.MultipleComponents
== make check
[passed; same checks as above]
== lake build NSFormalization.Section3.T24.Multiple NSFormalization.Section3.T24.MultipleComponents
Build completed successfully (10050 jobs).
== make test
[all 50 registered contract tests reported standard logical axioms only]
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

No file under `verification/` is changed by the lane, so the brief's
standalone conditional contract check did not apply; nevertheless the full
gate script ran `check_contracts.py --base-ref origin/erenup/integration-section3`
and reported `base_compatibility_checked: true` above.

Fix required before merge: narrow the inaccurate current-tree claim in
`formalization/NSFormalization/Section3/T24/Multiple.lean:46-49` to the exact
torus/T24b-scope sentence given in section 3. No Lean statement or proof change
is required.
