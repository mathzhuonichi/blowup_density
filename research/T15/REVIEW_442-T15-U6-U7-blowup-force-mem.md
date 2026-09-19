ACCEPT

## 1. What the lane claims

The worker claims three declarations: the canonical U6 theorem
`unboundedSpeed`, the U7 helper `scaledForce_supportedInCube`, and the
canonical U7 theorem `force_mem` (`research/T15/REPORT_442.md:5`,
`research/T15/REPORT_442.md:20`).  It also claims that the U6 proof transports
the source blow-up and then uses the single-copy identity, while U7 obtains the
three clauses of `MemForceT` from scaled smoothness, lattice periodicity, and a
compact positive-time projection (`research/T15/REPORT_442.md:41`).  Finally it
claims no residual gap or named/repackaged input
(`research/T15/REPORT_442.md:66`).

These claims accurately describe the submitted files.  The status record says
the same and marks only U6/U7 complete (`research/T15/T15_SPLIT.md:112`,
`research/T15/T15_SPLIT.md:125`).

## 2. What is in Lean

### Statement fidelity

1. `unboundedSpeed` exists at
   `formalization/NSFormalization/Section3/T15/Blowup.lean:26`.  Its conclusion
   at `Blowup.lean:33` is literally the canonical `ScalingAPI.unboundedSpeed`
   field at `formalization/NSFormalization/Section3/T15/Scaling.lean:329`:
   `∀ ε ∈ Ioc 0 place.ε₀, SpeedUnboundedAt place.T
   (periodizedScaledVelocity u place.x₀ place.T ε)`.  The conformance example
   closes this exact target by bare `exact` at
   `research/T15/probes/blowup_force_mem_closes.lean:39`.

   This is the mathematics requested by the paper: the rescaled fields are
   defined at `paper/sections/03-torus.tex:108`, the torus contains a single
   support copy at `paper/sections/03-torus.tex:120`, and Proposition 3.3 asks
   for unbounded speed at `T` at `paper/sections/03-torus.tex:122`, justified by
   the speed scaling at `paper/sections/03-torus.tex:141`.  The predicate is
   non-totalized and has the expected positive threshold, positive
   neighbourhood, `t ∈ Ioo 0 T`, and point witness
   (`formalization/NSFormalization/Source/PacketScaling.lean:22`).  Its
   source-time-one spelling is the same predicate with `T = 1`
   (`verification/Contracts/V1/Packet.lean:142`).

   Every substantive premise is used.  `place.eps_time` supplies the delay
   inequality (`Blowup.lean:37`), `hspeed` feeds
   `zeroPastField_speed`/`speed_unbounded_at_target` (`Blowup.lean:42`), and
   compactness plus the slice-support clause put each nonzero witness in the
   cube before `velocity_singleCopy` is applied (`Blowup.lean:47`).  The source
   transport theorem is exactly the expected one
   (`formalization/NSFormalization/Source/PacketScaling.lean:177`), and the
   Section 4 binding is only a wrapper around it
   (`verification/Bindings/Scaling.lean:109`).  There is no `⊤.toReal`, empty
   interval, or unrelated field in the conclusion.  `PlacementData.eps_pos`
   makes the quantified scale interval inhabited and `eps_time` makes the
   physical delay positive (`Scaling.lean:165`, `Scaling.lean:178`).

2. `force_mem` exists at
   `formalization/NSFormalization/Section3/T15/ForceMem.lean:45`.  Its
   conclusion at `ForceMem.lean:50` is literally the canonical
   `ScalingAPI.force_mem` field at `Scaling.lean:286`; the bare-`exact`
   conformance check is at
   `research/T15/probes/blowup_force_mem_closes.lean:44`.

   `MemForceT` is the concrete conjunction of global smoothness, unit spatial
   periodicity, and a compact time set contained in `Ioi 0` supporting the
   force (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:237`).
   This matches `C_c^∞(T³ × (0,∞))` and the manuscript's explanation that such
   forces vanish near zero and outside a compact time interval
   (`paper/sections/02-preliminaries.tex:7`,
   `paper/sections/02-preliminaries.tex:22`).  It also matches the scaled force
   and single-copy periodization described at `paper/sections/03-torus.tex:101`
   and `paper/sections/03-torus.tex:108`.

   The two named raw hypotheses are honest and isolated:
   `hforce_support` proves positivity/compactness after rescaling
   (`ForceMem.lean:53`), and `hforce_smooth` proves scaled smoothness
   (`ForceMem.lean:61`).  Vendor local finiteness supplies smoothness
   (`vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean:153`),
   lattice reindexing supplies the exact unit periods
   (`vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean:191`),
   and `time_support_periodize` proves that periodization introduces no new
   time (`formalization/NSFormalization/Paper1/PeriodicBridge.lean:496`).  The
   proof constructs the actual compact projection and proves both positivity
   and support containment (`ForceMem.lean:74`); it is not a restated goal.

3. `scaledForce_supportedInCube` exists with exactly the report's type at
   `ForceMem.lean:28`.  Its only purpose is to turn U2's strict slice support
   (`formalization/NSFormalization/Section3/T15/Placement.lean:309`) into the
   vendor's explicit coordinate bound; the premise and conclusion are both
   used at `ForceMem.lean:33`.  It is a genuine support helper, not a named
   analytic input.

### Non-vacuity and negative check

The submitted probe supplies a concrete `PlacementData` with `T = 1` and
`ε₀ = 1/2` (`research/T15/probes/blowup_force_mem_closes.lean:165`).  Its bump
velocity is proved to satisfy `SpeedUnboundedAtOne` by explicit witnesses
(`research/T15/probes/blowup_force_mem_closes.lean:90`), and both lane theorems
are instantiated at `ε = 1/2`
(`research/T15/probes/blowup_force_mem_closes.lean:200`).  The force in that
instance is the zero member of the nonempty force class, while the U6 field is
genuinely nonzero and unbounded; this is sufficient to show consistency of all
raw premises, and the general U7 proof does not specialize its force.

The reviewer mutation changes the asserted terminal time from `place.T` to
`place.T + 1` (`research/T15/probes/rev442_negative.lean:24`).  Reusing the lane
proof fails for the intended semantic reason, not because an argument was
dropped:

```text
../research/T15/probes/rev442_negative.lean:27:2: error: Type mismatch
  unboundedSpeed hK hu hspeed place
has type
  ∀ ε ∈ Ioc 0 place.ε₀, SpeedUnboundedAt place.T (periodizedScaledVelocity u place.x₀ place.T ε)
but is expected to have type
  ∀ ε ∈ Ioc 0 place.ε₀, SpeedUnboundedAt (place.T + 1) (periodizedScaledVelocity u place.x₀ place.T ε)
```

### Axioms and hygiene

All three declarations print exactly
`[propext, Classical.choice, Quot.sound]`; the audit file covers all three at
`research/T15/axioms_u6_u7.lean:4`.  A case-insensitive scan of both new
modules, both probes, and the audit file found no
`sorry`/`admit`/`axiom`/`native_decide` token and no `maxHeartbeats` setting.
`git diff --check origin/erenup/integration-section3...HEAD` produced no output.

The baseline diff adds the two requested Lean modules and changes no existing
Lean module.  The only modified pre-existing file is the requested status
record `research/T15/T15_SPLIT.md`; all other lane files are additions.  The
citations in the module docstrings are accurate: U6 points to the proposition
and speed identity (`Blowup.lean:22`; `paper/sections/03-torus.tex:122`), while
U7 points to the scaling/force-class passage (`ForceMem.lean:42`;
`paper/sections/02-preliminaries.tex:7`).

## 3. Gaps

No proof, statement-fidelity, non-vacuity, axiom, hygiene, or build gap was
found.  The worker makes no "not in the tree" claim: both its report and
attempts explicitly say there is no residual gap
(`research/T15/REPORT_442.md:66`, `research/T15/ATTEMPTS_U6_U7.md:60`).  For
completeness, the required whole-tree search

```text
rg -n "scaled_blowup|SpeedUnboundedAt" formalization/NSFormalization/Section4 formalization/NSFormalization/Source
```

finds the canonical definition and transport lemmas in
`formalization/NSFormalization/Source/PacketScaling.lean:22`,
`formalization/NSFormalization/Source/PacketScaling.lean:147`, and
`formalization/NSFormalization/Source/PacketScaling.lean:179`, plus downstream
Section 4 uses such as
`formalization/NSFormalization/Section4/R42/BlowupEssSup.lean:101`.  Thus there
is no missing-lemma assertion to accept or reject.

The build replays pre-existing upstream linter warnings, but neither submitted
module emits a warning under direct elaboration.  This is not a lane defect.
Because the baseline diff contains no path under `verification/`, the
conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates are
not applicable.

## 4. Commands and results

All Lake commands were run from `verification/` after
`. ../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.  The build command was
run raw first; the exact stable diagnostic summary below was obtained by
filtering only replay headers, errors, and the completion line from a second
successful run:

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Blowup NSFormalization.Section3.T15.ForceMem
⚠ [8778/9118] Replayed NSFormalization.Source.FiniteHilbertBochner
⚠ [9820/10005] Replayed NSFormalization.Paper1.PeriodicSobolevHilbert
⚠ [9821/10005] Replayed NSFormalization.Paper1.PeriodicH2Embedding
⚠ [9831/10005] Replayed NSFormalization.Paper1.LocalizationBoundary
⚠ [9840/10005] Replayed Formal.EndpointSafeTwoSpacePicard
⚠ [9842/10005] Replayed NSFormalization.Paper1.PeriodicWeightShift
⚠ [9864/10005] Replayed NSFormalization.Source.RealSobolev
⚠ [9868/10005] Replayed NSFormalization.Paper3.SpatiallyCompactTime
⚠ [9875/10005] Replayed NSFormalization.Paper3.RealPositiveDensity
⚠ [9878/10005] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
⚠ [9888/10005] Replayed NSFormalization.Source.PacketForceExtension
⚠ [9891/10005] Replayed NSFormalization.Source.ViscosityPacket
ℹ [9903/10005] Replayed NSFormalization.Source.PhysicalBesselSobolev
⚠ [9920/10005] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
⚠ [9962/10005] Replayed NSFormalization.Paper1.PeriodicScalarForceEndpoints
⚠ [9966/10005] Replayed NSFormalization.Paper1.PeriodicForceConvergence
⚠ [9967/10005] Replayed NSFormalization.Paper1.PeriodicInsertionSupport
⚠ [9969/10005] Replayed NSFormalization.Paper1.PeriodicPacketEndpointRates
⚠ [9970/10005] Replayed NSFormalization.Paper1.PeriodicCorrectionEndpointRates
⚠ [9978/10005] Replayed NSFormalization.Paper1.PeriodicDensityFiber
⚠ [9982/10005] Replayed NSFormalization.Paper1.PeriodicLocalLifespan
Build completed successfully (10005 jobs).
EXIT 0
```

Direct elaboration and the positive conformance probe all produced exactly no
output:

```text
$ lake env lean ../formalization/NSFormalization/Section3/T15/Blowup.lean
EXIT 0
$ lake env lean ../formalization/NSFormalization/Section3/T15/ForceMem.lean
EXIT 0
$ lake env lean ../research/T15/probes/blowup_force_mem_closes.lean
EXIT 0
```

The axiom audit output was:

```text
$ lake env lean ../research/T15/axioms_u6_u7.lean
'NSFormalization.Section3.T15.unboundedSpeed' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaledForce_supportedInCube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.force_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT 0
```

The negative mutation output was exactly the type mismatch quoted in part 2,
with `EXIT 1` as expected.

The raw `make check` run exited 0.  It emits more than 500 KB of contract
closure JSON; this is the exact stable completion-line extraction from the
second successful run:

```text
$ LEAN_NUM_THREADS=6 make check
python3 experiments/check_formalization_plan.py --check
  "task_count": 45,
  "source_hashes_match": false
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
  "registered_contracts": 46,
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s
OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
EXIT 0
```

The baseline diff was:

```text
$ git diff --name-status origin/erenup/integration-section3...HEAD
A formalization/NSFormalization/Section3/T15/Blowup.lean
A formalization/NSFormalization/Section3/T15/ForceMem.lean
A research/T15/ATTEMPTS_U6_U7.md
A research/T15/REPORT_442.md
M research/T15/T15_SPLIT.md
A research/T15/axioms_u6_u7.lean
A research/T15/probes/blowup_force_mem_closes.lean
```

Fixes: none.
