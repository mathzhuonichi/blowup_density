REJECT

## 1. What the lane claims

The worker reports R313 as Closed and claims: raw packet nonzero from the packet
energy estimate plus blow-up; positive finite packet-force amplitude; the
single-copy `ε⁻³` scaling lower bound; the global `C ε⁻²` correction
bound with `C = correction.forceProfileConst 0`; the displayed lower bound and
both ENNReal/real divergence statements for every insertion record; the T19
fixed-ball specialization; and a registered `T03.force_amplitude` contract
(`research/T18/REPORT_494.md:7`, `research/T18/REPORT_494.md:12`,
`research/T18/REPORT_494.md:15`, `research/T18/REPORT_494.md:19`,
`research/T18/REPORT_494.md:24`, `research/T18/REPORT_494.md:29`,
`research/T18/REPORT_494.md:31`). It also claims 22 Closed / 5 Partial entries,
30 registered contracts, updated reader documents, and no modified existing
Lean implementation module (`research/T18/REPORT_494.md:53`).

Those mathematical and bookkeeping claims are borne out below. The verdict is
REJECT only because a mandatory gate does not run: `scripts/gates.sh` and the
separately required `check_contracts.py --base-ref origin/erenup/core` both exit
2. This is an interface mismatch between `scripts/gates.sh:13` and the only
accepted checker option at `experiments/check_contracts.py:116-118`.

## 2. What is in Lean

### Statement fidelity and non-vacuity

- The article says exactly
  `‖g_ε-g‖_{L∞_{t,x}} ≥ ε⁻³‖F‖∞-Cε⁻² → ∞`, identifies the two
  terms as the amplitudes of `F_ε` and the bound on `H_ε`, and says that
  `F ≠ 0` follows from packet energy and blow-up
  (`paper/revised/sections/03-torus.tex:403-409`).
- `packetForce_ne_zero` has precisely the raw T14 packet hypotheses and concludes
  `f ≠ 0`; setting `f = 0` collapses the energy work term, forces zero kinetic
  energy, and contradicts `SpeedUnboundedAtOne`
  (`formalization/NSFormalization/Section3/T18/ForceAmplitude.lean:24-51`).
  Its energy input is the actual packet estimate
  (`formalization/NSFormalization/Section3/T14/PacketEnergy.lean:160-178`), and
  the binding supplies every premise from the registered packet rather than
  assuming nonzero force (`verification/Bindings/ForceAmplitude.lean:13-16`;
  registered smoothness/support/blow-up are at
  `verification/Contracts/V1/Packet.lean:202-242`). No named premise is unused
  or an extra nonzero hypothesis.
- Positivity and finiteness of the extended supremum are proved at
  `formalization/NSFormalization/Section3/T18/ForceAmplitude.lean:54-64`.
  Every canonical `InsertionData` also derives `packetForce ≠ 0` and finite
  packet amplitude without caller premises
  (`formalization/NSFormalization/Section3/T18/ForceAmplitude.lean:263-328`).
  Thus the `.toReal` in the displayed lower bound is not the vacuous
  `⊤.toReal = 0` case.
- The underlying source really is `( ε⁻¹ )^3 • F` and uses start time
  `T-ε²` (`formalization/NSFormalization/Section3/T15/Bridges.lean:56-76`).
  The tree's single-copy API is exact on the fundamental cube
  (`formalization/NSFormalization/Section3/T15/Scaling.lean:268-277`). The lane
  evaluates the inverse change of variables and proves the permitted lower
  inequality with coefficient `ENNReal.ofReal ((ε⁻¹)^3)`
  (`formalization/NSFormalization/Section3/T18/ForceAmplitude.lean:67-104`).
- The correction record fixes `forceProfileConst` before `ε`, makes it
  nonnegative, provides the order-zero profile bound and the exact
  `( ε² )⁻¹` chart identity, periodicity and support
  (`formalization/NSFormalization/Section3/T17/Correction.lean:133-172`). The
  lane transports these globally and obtains exactly
  `forceProfileConst 0 * (ε⁻¹)^2`
  (`formalization/NSFormalization/Section3/T18/ForceAmplitude.lean:122-173`).
- `forceAmplitude_lower` quantifies over every `InsertionData`, every
  `PeriodicInsertionAPI data`, and every `ε ∈ Ioc 0 A.ε₀`, with the paper's
  sign and powers and the record's order-zero correction constant
  (`formalization/NSFormalization/Section3/T18/ForceAmplitude.lean:240-257`).
  The record formula is indeed `g_ε = g + H_ε + F_ε`
  (`formalization/NSFormalization/Section3/T18/Assembly.lean:49-56`).
- Extended amplitudes tend to the topological neighbourhood `nhds ⊤`, which is
  the correct ENNReal formulation of unbounded finite values, while the finite
  real amplitudes tend to `atTop`
  (`formalization/NSFormalization/Section3/T18/ForceAmplitude.lean:226-237`,
  `formalization/NSFormalization/Section3/T18/ForceAmplitude.lean:288-341`).
  Pointwise finiteness for the latter is supplied by the actual
  `forceDifference_mem` field (`formalization/NSFormalization/Section3/T18/Assembly.lean:53-56`),
  and packet finiteness is proved as above. The worker's correction of the
  requested ENNReal `atTop` wording is therefore mathematically sound, not a
  weakening.
- T19 specializes the theorem to the constructed fixed-ball `insertion` for
  arbitrary raw regular data (`formalization/NSFormalization/Section3/T19/ForceAmplitude.lean:14-21`),
  and the binding exports the same corollary
  (`verification/Bindings/ForceAmplitude.lean:40-49`).

The successful reviewer non-vacuity probe explicitly inhabits `Ioc 0 A.ε₀`,
checks `F ≠ 0`, checks positive finite packet amplitude, and derives `False`
from `F = 0` (`research/T18/probes/rev494_nonvacuity.lean:10-28`).

### Contract, registration, and blueprint

`forceAmplitudeStatement` imports the registered periodic-insertion contract
and uses its registered `PacketImportAPI`, placement, scaling, correction and
`PeriodicInsertionAPI` vocabulary directly. It quantifies over every such API
and contains, in order, nonzero force, positive finite amplitude, the exact
lower bound, ENNReal convergence to `nhds ⊤`, and real convergence to `atTop`
(`verification/Contracts/V1/ForceAmplitude.lean:1-30`). There is no local mirror
definition. The binding proves this complete proposition
(`verification/Bindings/ForceAmplitude.lean:19-31`), and the test checks the
contract plus the T19/selected-packet exports
(`verification/Tests/ForceAmplitude.lean:7-12`). The registry entry has the
required id/version/specification/binding/test/declaration/scope/enabled shape
and accurately names `correction.forceProfileConst 0`
(`verification/contracts.json:323-332`).

R313 is Closed with `depends_on = [S33, C35_T]`, empty `completion_from`, and
the four relevant evidence paths (`formalization/blueprint/proof_graph.json:323-338`).
The proof and test modules are entrypoints
(`formalization/blueprint/entrypoints.json:8`,
`formalization/blueprint/entrypoints.json:26-28`,
`formalization/blueprint/entrypoints.json:67`). RESULT_MAP and the guide both
mark `rem:peaks` Closed with valid declaration anchors
(`formalization/blueprint/RESULT_MAP.md:26`;
`paper/formalization_guide.tex:108-113`), the reader checker enforces that state
(`experiments/check_reader_documents.py:60-62`), and the inventory says 22
Closed / 5 Partial (`README.md:35`; `formalization/blueprint/CLOSURE_AUDIT.md:28`).
The regenerated audit records the expected three standard axioms and no
unexpected ones for all five guide declarations
(`formalization/blueprint/AXIOM_AUDIT.json:298-361`).

### Hygiene and mutation checks

The base diff adds the two implementation modules and does not modify any
pre-existing `formalization/**/*.lean` file. The existing-file changes are the
brief-authorized registry/blueprint/guide/count/reader-checker/PDF updates. No
lane-added or reviewer Lean file contains `sorry`, `admit`, `axiom`,
`native_decide`, or `maxHeartbeats`; `git diff --check` is clean.

The substantive mutation changes the leading packet term from `(ε⁻¹)^3` to
`(ε⁻¹)^2` (`research/T18/probes/rev494_negative.lean:10-17`) and the
zero-force attempt tries to discharge the load-bearing `F ≠ 0` input after
rewriting `F = 0` (`research/T18/probes/rev494_negative.lean:19-26`). Both fail
at exactly those points; output is in part 4.

## 3. Gaps

### Blocking gate failure

The required command

```text
python3 experiments/check_contracts.py --base-ref origin/erenup/core
```

exits 2:

```text
usage: check_contracts.py [-h] [--summary]
check_contracts.py: error: unrecognized arguments: --base-ref origin/erenup/core
exit=2
```

Consequently `LEAN_NUM_THREADS=6 BASE_REF=origin/erenup/core scripts/gates.sh`
also exits 2 at its last stage. The script hard-codes `--base-ref`
(`scripts/gates.sh:13`), but the current parser only declares `--summary`
(`experiments/check_contracts.py:116-118`). The worker's report lists the four
individual make/audit gates but does not report either of these mandatory
commands (`research/T18/REPORT_494.md:84-96`).

Required fix: restore functional `--base-ref` support in
`experiments/check_contracts.py` (or make the repository's gate/reviewer
contract consistently use the current checker interface), then rerun both the
direct base-ref command and `scripts/gates.sh` to exit 0. No Lean statement or
proof fix is indicated by this review.

### Mathematical/tree gaps

No mathematical residual remains. The worker makes no "not in the tree" claim,
so there is no missing Section4 lemma to accept or reject. As a defensive check,
the whole-tree search

```text
rg -n -i 'forceAmplitude|force_amplitude|force[- ]amplitude|amplitude.*force|force.*amplitude' formalization/NSFormalization/Section4
```

produced no output.

## 4. Commands and results

All Lean/Lake commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and
ran Lake only from `verification/`.

### Lean module and contract checks

`lake build NSFormalization.Section3.T18.ForceAmplitude` exited 0. Lake replayed
pre-existing dependency warnings; no diagnostic names the new module. Exact
first and last output lines (middle omitted):

```text
⚠ [8778/8885] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
…
Build completed successfully (10620 jobs).
```

Both direct module checks exited 0 with exactly zero output:

```text
lake env lean ../formalization/NSFormalization/Section3/T18/ForceAmplitude.lean
(no output)
lake env lean ../formalization/NSFormalization/Section3/T19/ForceAmplitude.lean
(no output)
```

`lake build NSFormalization.Section3.T19.ForceAmplitude Tests.ForceAmplitude`
exited 0. Exact final output:

```text
ℹ [10699/10699] Replayed Tests.ForceAmplitude
info: Tests/ForceAmplitude.lean:10:0: Contract BlowupDensity.Tests.checkedForceAmplitude: checked; standard logical axioms only
info: Tests/ForceAmplitude.lean:11:0: Contract BlowupDensity.Bindings.forceAmplitude_from_data: checked; standard logical axioms only
info: Tests/ForceAmplitude.lean:12:0: Contract BlowupDensity.Bindings.selectedPacketForce_ne_zero: checked; standard logical axioms only
Build completed successfully (10699 jobs).
```

The worker probe also exited 0 with exactly zero output:

```text
lake env lean ../research/T18/probes/force_amplitude_494.lean
(no output)
```

The axioms file exited 0; every one of its 22 prints is exactly the same three
axioms (full output, 34 lines):

```text
'NSFormalization.Section3.T18.packetForce_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.packetForce_sup_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.packetForce_sup_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.periodizedScaledForce_at_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T18.periodizedScaledForce_amplitude' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T18.correctionForce_amplitude_le_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T18.correctionForce_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.correctionForce_amplitude_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.forceAmplitude_point_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.amplitude_polynomial_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.forceAmplitude_diverges_of_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T18.forceAmplitude_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.insertionData_packetForce_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T18.forceAmplitude_diverges' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.memForceT_sup_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.insertionData_packetForce_sup_lt_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T19.forceAmplitude_diverges' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.forceAmplitude' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.forceAmplitude_from_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.selectedPacketForce_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.forceAmplitude_real_diverges' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.packetForce_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Reviewer non-vacuity probe:

```text
lake env lean ../research/T18/probes/rev494_nonvacuity.lean
(no output; exit 0)
```

Reviewer negative probe (expected exit 1):

```text
../research/T18/probes/rev494_negative.lean:17:2: error: Type mismatch
  forceAmplitude_lower data A hε
has type
  ENNReal.ofReal (ε⁻¹ ^ 3 * (⨆ z, ‖data.packetForce z‖ₑ).toReal - data.correction.forceProfileConst 0 * ε⁻¹ ^ 2) ≤
    ⨆ z, ‖A.force ε z - data.g z‖ₑ
but is expected to have type
  ENNReal.ofReal (ε⁻¹ ^ 2 * (⨆ z, ‖data.packetForce z‖ₑ).toReal - data.correction.forceProfileConst 0 * ε⁻¹ ^ 2) ≤
    ⨆ z, ‖A.force ε z - data.g z‖ₑ
../research/T18/probes/rev494_negative.lean:26:2: error: Tactic `assumption` failed

data : InsertionData
A : PeriodicInsertionAPI data
hzero : data.packetForce = 0
⊢ False
negative_exit=1
```

### Repository gates

`make check` exited 0 with exact output:

```text
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2243 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 30,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.003s

OK
```

`scripts/gates.sh` exited 2. Exact first and last output excerpts (the middle
contract lines are omitted; each excerpt is under 40 lines):

```text
== make check
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2243 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 30,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.005s

OK
…
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
usage: check_contracts.py [-h] [--summary]
check_contracts.py: error: unrecognized arguments: --base-ref origin/erenup/core
```

The separately required checker command has the exact failure quoted in part 3.

`make test` exited 0. Exact first and last lines (long dependency replay omitted):

```text
lake -d verification test
⚠ [8778/9084] Replayed NSFormalization.Source.FiniteHilbertBochner
…
ℹ [11003/11005] Replayed Tests.PeriodicInsertion
info: Tests/PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
ℹ [11004/11005] Replayed Tests.TorusNonDensity
info: Tests/TorusNonDensity.lean:24:0: Contract BlowupDensity.Tests.checkedTorusNonDensity: checked; standard logical axioms only
ℹ [11005/11005] Replayed Tests.TorusMain
info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
```

`make test-mutations` exited 0. Exact final output:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

`make paper` exited 0. Exact final output:

```text
python3 ../experiments/check_reader_documents.py
Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
26 numbered article statements and their guide mappings checked.
27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
86 article labels resolved.
16 bibliography entries resolved; 30 registry declarations found; guide code paths verified.
Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
make[1]: Leaving directory '/data_8T/ping/blowup_density/.claude/worktrees/494-T18-P3-force-amplitude/paper'
```

`python3 experiments/check_formalization_plan.py` exited 0:

```text
Blueprint: 41 proof nodes, 27 article/guide mappings; 2243 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
```

The fresh article axiom audit exited 0:

```text
Bindings.CompletedDensity: 8 declarations checked
NSFormalization.Section3.T21.MainAssembly: 33 declarations checked
Bindings.BoundaryInsertionV2: 4 declarations checked
Bindings.ForceAmplitude: 6 declarations checked
NavierStokes.ComparatorR3Theorem: 2 declarations checked
NSFormalization.Source.PacketBreakdown: 1 declarations checked
Bindings.LocalTheoryV2: 1 declarations checked
Bindings.AffineVariation: 1 declarations checked
NSFormalization.Section3.T24.MultipleAssembly: 1 declarations checked
NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
Bindings.ForceClasses: 1 declarations checked
NSFormalization.Section4.R43.Universal: 1 declarations checked
Bindings.GridObservations: 1 declarations checked
61 declarations; 27 article entries; 0 forbidden-axiom results
```

Its `report.json` is byte-identical to
`formalization/blueprint/AXIOM_AUDIT.json` (`cmp_exit=0`; both SHA-256
`bfda150fd8d59de3aa648003316910cf0df55a47d1a2eddb56299109b4fc2cf3`).

Final hygiene checks: `git diff --check origin/erenup/core...HEAD` produced no
output; forbidden-token and `maxHeartbeats` searches produced no matches; and
`git diff --name-status HEAD` produced no output. The only reviewer-created
files before this report are the two permitted `rev494_*.lean` probes. The two
untracked collaboration briefs predated the review.

## Lead ruling (2026-09-21 04:25Z)
REJECT reason is the same tooling artefact as lanes 492/493 (`check_contracts.py --base-ref` no longer exists in the owner's CLI; gates/review scripts fixed). Reviewer confirms mathematics, contracts, mutations, axioms and gates pass. Merged on lead authority.
