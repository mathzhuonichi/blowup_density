ACCEPT

## 1. What the lane claims

The lane claims a canonical `PlacementData` at every prescribed positive
horizon, assembly of all 21 `ScalingAPI` fields from the raw packet clauses,
the canonical and registered `scalingStatement`, fieldwise structure bridges,
registration as `T02.scaling`, and nonzero source/periodized instances.  Those
claims are accurate.

The manuscript first fixes one compact `K_*`, chart ball, point `x_0`, and one
small-scale interval before defining the rescaling
(`paper/sections/03-torus.tex:101-120`).  It then states the unchanged-viscosity
solution/blowup conclusion, the two `epsilon^(1/2)` energy identities, the
mixed exponent `-3+3/p+2/q`, the two-term Sobolev bound, and the `q=1`,
`s<1/2` limit (`paper/sections/03-torus.tex:122-138`).  The contract represents
exactly these data and honesty guards.  The extra `q=2`, `s<-1/2` branch is not
present in the manuscript sentence at line 138, but is the explicit reconciled
field required by this lane's brief; it is identified as a promoted conclusion
in the contract itself (`verification/Contracts/V1/Scaling3.lean:485`) and has
the required threshold and right-neighborhood limit
(`verification/Contracts/V1/Scaling3.lean:497`).

Statement fidelity checks:

- A byte-for-byte comparison of `research/T15/Spec.lean:421-922` with
  `verification/Contracts/V1/Scaling3.lean:15-516` produced no diff.  Independent
  counts give 17 fields in `PlacementData` and 21 in `ScalingAPI`.  The
  registered quantifier order is exactly `PacketImportFamily`, `nu`, `0 < nu`,
  already-fixed placement, then `Nonempty (ScalingAPI ...)`
  (`verification/Contracts/V1/Scaling3.lean:513`).
- `placementData` uses the cube centre, radius `3/8`, compact union
  `K union Prod.snd '' tsupport f`, and one positive threshold
  (`formalization/NSFormalization/Section3/T15/Assembly.lean:16`, `:17`, `:34`,
  `:53`).  Compactness and both support inclusions are proved at lines 20-25
  and 62-65; `eps_time` and `eps_space` are proved at lines 69-83.  Its horizon
  is definitionally the prescribed `T` (`Assembly.lean:86`).  Thus neither the
  time interval nor the scale interval is empty.
- The 21-field constructor is literal and in the contract order
  (`Assembly.lean:93-127`).  Its first eight hypotheses are exactly the fields
  of `Section4.I03.PacketData` (`formalization/NSFormalization/Section4/I03/Energy.lean:101-118`);
  the remaining eight named hypotheses are pressure support/smoothness, force
  smoothness/support/past vanishing, the extended equation/divergence, and
  speed blowup (`Assembly.lean:96-105`).  Each is passed to a source theorem at
  lines 108-127 rather than used as an unconstrained `Prop`.
- The source statements agree with the corresponding fields: lattice and
  single-copy theorems are at `Section3/T15/SingleCopy.lean:97-191`, force
  membership at `ForceMem.lean:45-51`, the pinned solution at
  `Solution.lean:151-174`, pressure integrability at `Pressure.lean:96-109`,
  blowup at `Blowup.lean:26-35`, the energy fields at `Energy.lean:129-137` and
  `:170-215`, mixed fields at `Mixed.lean:317-365`, the Sobolev fields at
  `SobolevBound.lean:29-55` and `:198-206`, and combined convergence at
  `ConvergenceTwo.lean:486-497`.  The localization field is the six-field
  canonical witness (`Section3/T13/Assembly.lean:328-336`).
- The raw theorem introduces the pre-existing raw `scalingStatement` and
  constructs exactly the eight-field energy subrecord before calling the
  constructor (`Assembly.lean:129-133`).  Some original packet clauses are not
  needed by this final constructor, but they were not newly or silently added:
  they are the canonical raw restatement already declared at
  `Section3/T15/Scaling.lean:459-501`.  In the registered theorem there are no
  extra premises at all (`verification/Bindings/Scaling3.lean:188-191`).
- Both placement and scaling structures are converted fieldwise in both
  directions, with `rfl` round trips (`verification/Bindings/Scaling3.lean:13-127`).
  The 16 non-structure vocabulary bridges are all `rfl` at lines 129-151.
  The contract statement conversion is explicit at lines 155-166.
- Non-vacuity is substantive: the registered packet is constructed at every
  positive viscosity (`verification/Bindings/Packet.lean:101-130`), its selected
  energy-enhanced family is built at `verification/Bindings/PacketImport.lean:26-42`,
  and the tests prove a nonzero source velocity and a nonzero periodized velocity
  at an actual `epsilon in (0, epsilon_0]` and `t in (0,T)`
  (`verification/Tests/Scaling3.lean:50-76`).  This rules out an empty interval,
  zero-packet, or totalized-norm-only proof of the headline result.

## 2. What is in Lean

The implementation contains the claimed declarations with the claimed types:

- canonical placement, definitional horizon identity, 21-field assembly, and
  canonical theorem: `formalization/NSFormalization/Section3/T15/Assembly.lean:53`,
  `:86`, `:93`, and `:130`;
- exact registered structures and proposition:
  `verification/Contracts/V1/Scaling3.lean:154`, `:248`, and `:513`;
- conversions, registered assembly, theorem, and packet instance:
  `verification/Bindings/Scaling3.lean:13`, `:41`, `:70`, `:95`, `:169`,
  `:178`, `:189`, and `:194`;
- the universal check, three independent field-shape checks, prescribed-horizon
  instance, and two nonzero theorems:
  `verification/Tests/Scaling3.lean:11-79`;
- the raw-clause probe and horizon check:
  `research/T15/probes/assembly_closes.lean:10-54`;
- the V1 registry entry with parent `T02`, honest scope, binding/test modules,
  and checked declaration: `verification/contracts.json:544-552`.  The T15 work
  item records that contract at `collaboration/work_items.json:352-359`.

The contract imports only other contracts (`verification/Contracts/V1/Scaling3.lean:1-4`).
The base-compatibility gate passes.  The base registry has 49 IDs and this tree
has 50.

Hygiene passes.  There is no executable `sorry`, `admit`, `axiom`, or
`native_decide`, and no `maxHeartbeats` setting, in any lane-459 Lean file or
reviewer probe.  The imported U14 module's sole pre-existing override is local
to one declaration, exactly 400000, and immediately documented
(`formalization/NSFormalization/Section3/T15/Convergence.lean:42-44`).  All 68
`#print axioms` declarations report exactly
`[propext, Classical.choice, Quot.sound]`.

The requested triple-dot diff warns that this branch has multiple merge bases
and therefore also lists earlier accepted T18/T19 additions.  Its Lean entries
are all status `A`; the modified-Lean-only query is empty.  The lane commit
itself adds exactly the six claimed Lean files and modifies no existing Lean
module.  This is branch topology, not a lane-459 hygiene defect.

## 3. Gaps

No mathematical, statement, build, registration, or axiom gap was found.
There is no "not in the tree" or missing-lemma claim in `REPORT_459.md` or
`ATTEMPTS_U15.md`; both explicitly say that no gap remains
(`research/T15/REPORT_459.md:47`, `research/T15/ATTEMPTS_U15.md:54`).  The
Section4 missing-lemma grep requirement is therefore not applicable.

The substantive reviewer mutation changes the main packet-energy exponent
from `1/2` to `3/2` (`research/T15/probes/rev459_mutated_energy_exponent.lean:11-20`).
Lean rejects it because the assembled field has the original `1/2` exponent.
This changes mathematical content and does not merely drop an argument.

No fixes are required.

## 4. Commands and results

All Lean/Lake commands were run after `. scripts/lean-env.sh`; every `lake`
command was run from `verification/` with `LEAN_NUM_THREADS=6`.

```text
$ lake build NSFormalization.Section3.T15.Assembly
[Lake replayed pre-existing dependency linter diagnostics; there was no
 diagnostic from NSFormalization.Section3.T15.Assembly.]
Build completed successfully (10048 jobs).
exit 0

$ lake env lean ../formalization/NSFormalization/Section3/T15/Assembly.lean
[no output]
exit 0
```

The direct test-module check gives the complete output:

```text
$ lake env lean Tests/Scaling3.lean
Contract BlowupDensity.Tests.checkedScaling3: checked; standard logical axioms only
Contract BlowupDensity.Tests.checkedScaling3Packet: checked; standard logical axioms only
Contract BlowupDensity.Tests.scaling3_source_nonzero: checked; standard logical axioms only
Contract BlowupDensity.Tests.scaling3_periodized_nonzero: checked; standard logical axioms only
exit 0
```

`lake build Tests.Scaling3` also exits 0 with `Build completed successfully
(10667 jobs)` after replaying dependency diagnostics, and repeats the same four
target-owned standard-axiom lines above.

```text
$ lake env lean ../research/T15/probes/assembly_closes.lean
'NSFormalization.Section3.T15.AssemblyProbe.registeredRawScaling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit 0
```

The axiom file exits 0 and emits 68 declaration blocks.  Every block has exactly
the following axiom list (several long declaration names cause only line
wrapping):

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

The declarations audited are exactly those listed in
`research/T15/axioms_u15.lean:4-71`; there were 68 `depends on axioms` blocks
and zero blocks with any other axiom.

```text
$ lake env lean ../research/T15/axioms_u15.lean 2>&1 | perl -0ne '$all = () = /depends on axioms:/g; $std = () = /depends on axioms: \[propext,\s*Classical\.choice,\s*Quot\.sound\]/g; print "axiom_blocks=$all\nstandard_blocks=$std\nnonstandard_blocks=", ($all-$std), "\n"'
axiom_blocks=68
standard_blocks=68
nonstandard_blocks=0
exit 0
```

Negative check, complete output:

```text
$ lake env lean ../research/T15/probes/rev459_mutated_energy_exponent.lean
../research/T15/probes/rev459_mutated_energy_exponent.lean:20:2: error: Type mismatch
  (Bindings.Scaling3.scalingAPI P place).packetEnergyIdentity
has type
  ∀ ε ∈ Ioc 0 place.ε₀,
    energyEssSupT place.T (Scaling3.periodizedScaledVelocity P place.x₀ place.T ε) =
      ENNReal.ofReal (ε ^ (1 / 2) * P.energyBound)
but is expected to have type
  ∀ epsilon ∈ Ioc 0 place.ε₀,
    energyEssSupT place.T (Scaling3.periodizedScaledVelocity P place.x₀ place.T epsilon) =
      ENNReal.ofReal (epsilon ^ (3 / 2) * P.energyBound)
exit 1 (expected)
```

`make check` emits a 1.4 MB contract-closure map; the executor truncates that
array.  Its exact terminal summary was:

```text
$ LEAN_NUM_THREADS=6 make check
"registered_contracts": 50,
"base_compatibility_checked": false,
"scope": "Architecture checks only; run lake test for Lean type and axiom checks."
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
exit 0
```

The same command also reports the known copied-source inventory entry
`NSFormalization.Paper1.BoundaryCorollary.lean:90` and the repository-wide
diagnostic `source_hashes_match: false`; neither trips this gate, and the check
exits 0.  The copied-source token is not introduced by this lane.

The material terminal lines of the required aggregate gate were:

```text
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh
== make test
[all registered tests checked; the four Scaling3 lines are reproduced above]
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
exit 0
```

Standalone base comparison (the omitted middle value is only the 1.4 MB
closure map):

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
{
  "registered_contracts": 50,
  "closures": { ... },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
exit 0
```

The base registry count was checked independently:

```text
$ git show origin/erenup/integration-section3:verification/contracts.json | rg -c '^\s+"id":'
49
$ rg -c '^\s+"id":' verification/contracts.json
50
```

The exact-Spec and field-count checks were:

```text
$ diff -u <(sed -n '421,922p' ../research/T15/Spec.lean) <(sed -n '15,516p' Contracts/V1/Scaling3.lean)
[no output]
exit 0
$ sed -n '154,238p' Contracts/V1/Scaling3.lean | grep -P -c '^  [\p{L}_][\p{L}\p{N}_₀]*\s*:'
17
$ sed -n '248,503p' Contracts/V1/Scaling3.lean | grep -P -c '^  [\p{L}_][\p{L}\p{N}_₀]*\s*:'
21
```

```text
$ git diff --stat verification/contracts.json
[no output; the lane is committed]
$ git diff --stat HEAD^ HEAD -- verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
$ git diff --check HEAD^ HEAD
[no output]
$ git diff --check
[no output]
```

The exact requested triple-dot command begins with the repository warning
below and lists the current branch's earlier merged additions as well as lane
459.  Restricting it to modified Lean files gives no path.

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 6eaa5bf0dfc146d89e9a4bfceba856db6ef6cb5b
[45 paths, including the lane-459 files and earlier accepted T18/T19 lane files]
$ git diff --name-only --diff-filter=M origin/erenup/integration-section3...HEAD -- '*.lean'
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 6eaa5bf0dfc146d89e9a4bfceba856db6ef6cb5b
[no paths]
$ git show --name-status --format='' HEAD -- '*.lean'
A formalization/NSFormalization/Section3/T15/Assembly.lean
A research/T15/axioms_u15.lean
A research/T15/probes/assembly_closes.lean
A verification/Bindings/Scaling3.lean
A verification/Contracts/V1/Scaling3.lean
A verification/Tests/Scaling3.lean
```
