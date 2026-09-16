ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed HEAD `77eb658714dc6d59f72624fc6660527d85c90e30`, read-only except this report and the permitted negative probe. No git state changes were made.

The five claims in `research/A04/REPORT_230.md:6` are present: fixed-force H⁷ restart, unchanged all-order Grönwall bound, endpoint restart, strict extension, and infinite lifespan. The open H¹ proposition is explicitly excluded (`REPORT_230.md:59`). The independent API does not extend or modify a frozen V1 interface.

I read CLAUDE.md, the lane-review skill, the first 40 LESSONS lines, the brief, worker report, Spec passages, prior 215/217 reports/reviews, the registered A04 V1 EnergyHighPartial trio, and the cited implementation declarations. The actual existing A04 V1 registration is EnergyHighPartial, not a proved continuation API (`verification/Contracts/V1/EnergyHighPartial.lean:156`). References to the V1 continuation interface are references to the draft.

## 2. What is in Lean

Paths abbreviated below: Contract = `verification/Contracts/V2/Continuation.lean`; Binding = `verification/Bindings/ContinuationV2.lean`; Tests = `verification/Tests/ContinuationV2.lean`. Every line reference resolves in this checkout.

- **restart:** Contract:88–94 and :131 have the approved order ν, fixed f, S≥0, finite K, ∃δ>0, then all t₀∈[0,S] and all admissible H⁷-bounded data. Binding:84–89 is an rfl bridge to `formalization/NSFormalization/Section4/A04/RestartFixedForce.lean:15`; Binding:132–135 applies its theorem at :41. Tests:31–38 checks the full expanded statement.
- **higherOrderBound:** Contract:140–146 matches `research/A04/Spec.lean:534` exactly in mathematical statement, including MemL1Hm, S>0, all natural orders, finite ENNReal cap, and [0,S). Binding:136–140 applies `RestartFixedForce.lean:236`. Tests:42–49 checks this statement. MemL1Hm is redundant with MemForceR, retained for Spec fidelity, not an unproved input.
- **restartBeyond:** Contract:156–164 matches `formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:236`, including the existential preceding a,u,p and the H⁷ trajectory bound. Binding:141–150 transports the lifespan through the established bridge. Tests:52–61 checks conformance.
- **extendsBeyond:** Contract:174–178 matches `ShiftedExtension.lean:247`, with S>0, actual shorter solutions and finite squared H² integral. Binding:151–156 has no residual gluing assumption. Tests:64–69 checks conformance.
- **lifespanInfiniteOfLocallyFinite:** Contract:188–195 matches `ShiftedExtension.lean:256`. The endpoint condition is ≤, not <; maximal-solution positivity is retained in Contract:74. Binding:157–169 correctly transports both the solution predicate and the lifespan in the finiteness hypothesis. Tests:72–80 checks conformance.

I opened `paper/sections/appendix-a-local-theory.tex:140–157` with sed: :146–147 supplies the all-order Grönwall bound, :147–153 uses H¹ restart and overlap uniqueness. I also opened `paper/sections/04-whole-space.tex:113–121` and :118–130: the finite-endpoint H² integral is the intended downstream criterion. V2 proves the approved alternate H⁷/fixed-force route, not the paper's H¹ local-horizon assertion.

**Contract boundary:** Contract:1 imports only Data. `experiments/check_contracts.py:31–39` does not whitelist LocalTheoryBundle. Parameterizing the horizon is an explicit, harmless abstraction here: Binding:130–131 and Tests:22–24 specialize the registered witness to the actual `A01.localHorizon'`; it is not left as an arbitrary horizon in the registered theorem. Binding:53–96 supplies the definitional bridges. Binding:102–124 supplies the necessary solution-structure transports; :148, :153, :167 use the existing maximal-lifespan bridge. The data vocabulary agrees with `verification/Contracts/V1/Data.lean:189`, :509, :544, :624.

**No vacuity:** finite K is explicit, and `RestartFixedForce.lean:56` uses it in ENNReal.toReal_mono. The contract statements themselves introduce no toReal conversion. S≥0 makes the closed restart window nonempty; the consumers require S>0. `research/A04/axioms_v2_contract.lean:95`, :98, :143, :152 prove membership and nonzeroness of a compact bump force and curl datum. Its :183–196 uses S=1 and finite H⁷ norm to produce an actual positive real δ. This entire audit compiled. Tests:87–94 alone is conditional, but the research audit supplies the concrete witnesses, so no additional non-vacuity instance is needed.

**Hygiene:** no proof-level sorry/admit/axiom/native_decide or maxHeartbeats in the four new Lean files. The text scan's only matches are prose “axiom”. No existing Lean module was modified; the triple-dot diff lists only the three new verification modules and new research audit among Lean files. Registry diff is 11 additions. All 19 printed axiom sets are exactly [propext, Classical.choice, Quot.sound].

## 3. Gaps and exact one-line fixes

No blocking mathematical gap in the five V2 fields. The open H¹ assertion remains open; “unproved” does not mean “unproved”.

1. **Documentation, epistemic overclaim.** `verification/Tests/ContinuationV2.lean:8` and `research/A04/ATTEMPTS_V2_CONTRACT.md:92` call the V1 record “unproved”. Exact fix at each occurrence: replace `unproved` with `unproved`. No impossibility theorem was supplied.
2. **Documentation, incorrect dependency claim (also inherited from the brief).** `research/A04/REPORT_230.md:82–85`, `research/A04/COMPARISON.md:346`, and `verification/contracts.json:287` group A02 exists_maximal with Grönwall restart consumers. But `formalization/NSFormalization/Section4/A02/MaximalWiring.lean:14–19` applies local existence directly, and `A02/Maximal.lean:157–182` constructs the directed union without higherOrderBound. Exact replacement sentence in each location: “The three continuation consumers restart the same force with Grönwall-bounded H⁷ data; A02's exists_maximal uses local existence directly and requires neither this restart bound nor cross-force uniformity.”
3. **Documentation, literal-copy claim.** Contract:34 and :48–51 call the definitions token-for-token/verbatim copies, but `research/A02/Spec.lean:158` writes `fun z : SpaceTime => ...`, whereas Contract:51 omits that annotation. The rfl bridge is valid; this is not a statement defect. Exact fix: change “token-for-token restatements” to “definitionally equal restatements” and “verbatim from” to “definitionally equal to” for timeShift (including Binding:69).

**Whole-tree missing-lemma check:** I ran
`grep -rnE 'ManuscriptHorizonLowerBoundH1|horizon_lower_bound|def Restart|theorem .*([Hh]1|[Rr]estart)' formalization/NSFormalization/Section4`,
and a second search including `HorizonLowerBoundH1`. Relevant hits were opened: `A01/LocalTheoryBundle.lean:342` proves only fixed-force H⁷; :372 defines the open H¹ proposition without proving it; `A04/Continuation.lean:101` defines the distinct maximal-lifespan Restart and :170/:197/:223 consume it as a hypothesis; `A04/RestartFixedForce.lean:41` and `A04/ShiftedExtension.lean:236` prove the narrowed route. No unconditional theorem discharging the stated H¹/all-force gap was found. The documentation-only proposition in Contract:105–112 is the A01 local-horizon sentence from `research/A01/Spec.lean:338–344`, not literally A04's maximal-lifespan Restart; Binding:94–96 checks precisely that distinction.

**Substantive negative check:** `research/A04/probes/rev230_h1_mutation.lean:10–17` copies the complete approved restart statement, changes only sobolevENorm 7 to sobolevENorm 1, and retains the witness. This enlarges the claimed datum class, rather than dropping an argument. Lean rejects it at the expected type mismatch. This establishes proof sensitivity to the requested narrowing, not a proof that the stronger mathematical statement is false.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`; `LEAN_NUM_THREADS=6`; Lake only in verification, one Lake process at a time. Existing packages were already correctly symlinked; no installer or repository-state mutation was necessary.

```text
$ lake -q --log-level=error build Contracts.V2.Continuation Bindings.ContinuationV2 Tests.ContinuationV2
exit 0
[zero output]
$ lake env lean Contracts/V2/Continuation.lean
exit 0
[zero output]
$ lake env lean Bindings/ContinuationV2.lean
exit 0
[zero output]
$ lake env lean Tests/ContinuationV2.lean
exit 0
Contract BlowupDensity.Tests.checkedContinuationV2: checked; standard logical axioms only
```

The Tests output is the required checkAxioms informational message, not a warning. The initial plain lake build also exited 0, replaying existing dependency warnings and the same test information; no warning originated in the new modules.

`lake env lean ../research/A04/axioms_v2_contract.lean` exited 0, exact output:

```text
'BlowupDensity.Contracts.V2.Continuation.timeShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.squaredHTwoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.SolvesBelow' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.MemL1Hm' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.IsMaximalSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.RestartFixedForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.ManuscriptHorizonLowerBoundH1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Contracts.V2.Continuation.ContinuationV2API' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.continuationV2_restartFixedForce_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.continuationV2_manuscriptHorizonLowerBoundH1_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.continuationV2_solvesBelow_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.continuationV2_isMaximalSolution_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.continuationV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedContinuationV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContinuationV2ContractConformance.nonzeroForce_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContinuationV2ContractConformance.nonzeroForce_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContinuationV2ContractConformance.nonzeroDatum_mem_initialClassR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ContinuationV2ContractConformance.nonzeroDatum_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContinuationV2ContractConformance.nonvacuous_restart_nonzero_force_datum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`make check` exited 0. Exact head/tail excerpts (large closure arrays omitted):

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 550,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
[... middle omitted ...]
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`scripts/gates.sh` exited 0. Exact selected output (make-check closure arrays and unrelated contract messages omitted):

```text
== make check
python3 experiments/check_formalization_plan.py --check
[... output omitted ...]
== make test
[... other contracts omitted ...]
info: Tests/ContinuationV2.lean:26:0: Contract BlowupDensity.Tests.checkedContinuationV2: checked; standard logical axioms only
[... other contracts omitted ...]
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

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` independently exited 0. Exact head/tail:

```text
{
  "registered_contracts": 33,
  "closures": {
[... closure arrays omitted ...]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

Negative probe, exact output (exit 1):

```text
../research/A04/probes/rev230_h1_mutation.lean:17:2: error: Type mismatch
  BlowupDensity.Tests.checkedContinuationV2.restart
has type
  RestartFixedForce NSFormalization.Section4.A01.localHorizon'
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ (f : SpaceTimeField),
        MemForceR f →
          ∀ (S : ℝ),
            0 ≤ S →
              ∀ (K : ℝ≥0∞),
                K ≠ ∞ →
                  ∃ δ,
                    0 < δ ∧
                      ∀ t₀ ∈ Icc 0 S,
                        ∀ a' ∈ initialClassR,
                          sobolevENorm 1 a' ≤ K → δ ≤ NSFormalization.Section4.A01.localHorizon' ν a' (timeShift t₀ f)
```

`git diff --name-only origin/erenup/integration...HEAD`, exact output:

```text
collaboration/TASKS.md
collaboration/tasks/A04.md
collaboration/work_items.json
research/A04/ATTEMPTS_V2_CONTRACT.md
research/A04/COMPARISON.md
research/A04/REPORT_230.md
research/A04/axioms_v2_contract.lean
verification/Bindings/ContinuationV2.lean
verification/Contracts/V2/Continuation.lean
verification/Tests/ContinuationV2.lean
verification/contracts.json
```

`git diff --stat verification/contracts.json`: exit 0, zero output (already committed).
`git diff --stat origin/erenup/integration...HEAD -- verification/contracts.json`:

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check`: exit 0, zero output. Reviewer additions are only this report and `research/A04/probes/rev230_h1_mutation.lean`.

