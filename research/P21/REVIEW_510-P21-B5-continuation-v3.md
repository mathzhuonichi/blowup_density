ACCEPT

## 1. What the lane claims

The worker claims the whole-space B5 unit only: an H¹-ball restart theorem,
the strict uniform endpoint theorem, and their V3 registration, while leaving
the periodic half and `L21_H1` closure to lane 511
(`research/P21/REPORT_510.md:3-5`, `research/P21/REPORT_510.md:9-31`). That is
the scope actually delivered.

Statement fidelity is exact. The authoritative registered targets are
`h1RestartR` at `research/P21/Targets.lean:26-35` and
`h1UniformEndpointR` at `research/P21/Targets.lean:51-59`. The V3 fields at
`verification/Contracts/V3/Continuation.lean:28-37` and
`verification/Contracts/V3/Continuation.lean:42-50` have the same quantifier
order and hypotheses:

- `ν`, the fixed `f ∈ MemForceR`, `S`, and `K ≠ ⊤` all precede `∃ δ`;
- the single `δ > 0` precedes both `t₀ ∈ Icc 0 S` and the restart datum;
- the datum remains in `initialClassR`, the bound is exactly
  `sobolevENorm 1 a' ≤ K`, and the returned
  `ManuscriptLocalRegularity` is on that same `δ`;
- the endpoint premise uses exactly `Ico 0 S` and order one, and the conclusion
  is the strict `ENNReal.ofReal (S + δ) < maximalLifespanR`, not `≤`.

The assessment says explicitly that this is smooth admissible data in an H¹
ball, not rough-H¹ existence (`research/P21/ASSESSMENT.md:23-25`), and records
the same one-δ ordering and same-interval regularity requirement
(`research/P21/ASSESSMENT.md:55`). Its endpoint target is verbatim at
`research/P21/ASSESSMENT.md:57-68`.

The paper citation was checked. The live streamlined paper states that every
high norm is uniformly bounded, a uniform positive restart time is obtained as
`t₀ ↑ S`, and the fixed force is smooth on the common compact window
(`paper/revised/sections/02-preliminaries.tex:178-182`). The contract's
`appendix-a-local-theory.tex:146-151` citation is a historical path removed by
the streamlining commit; inspecting its parent snapshot gives at lines 146-151
the same H¹-bounded restart and same-interval higher regularity text. This is
also the established citation convention in
`verification/Contracts/V1/TorusLocalTheory.lean:468-481`. The lane does not
misdescribe the H¹ sentence as a displayed clause of the current proposition;
the assessment makes that distinction at `research/P21/ASSESSMENT.md:17-21`.

## 2. What is in Lean

The implementation has every declaration claimed by the report:

- `RestartFixedForceH1` is the named fixed-force body at
  `formalization/NSFormalization/Section4/A04/H1RestartBeyond.lean:23-30`, and
  `restartFixedForceH1` discharges it from the unconditional lane-507 theorem
  at lines 32-36.
- `restartBeyondH1_le` has the full non-strict margin at lines 38-53. It feeds
  lane 507's `h1RestartAt` (`Section4/A04/H1Restart.lean:276-290`) into the
  endpoint lemma `restartBeyond_of_restartAt`
  (`Section4/A04/Continuation.lean:41-62`).
- `restartBeyondH1` has exactly the target statement at
  `Section4/A04/H1RestartBeyond.lean:55-66`; lines 67-73 return `δ / 2` and
  prove the strict `ofReal` inequality before composing with the non-strict
  theorem. There is no `⊤.toReal = 0` shortcut or empty-interval trick.
- The independent kernel probe imports the actual targets and proves both
  target Props directly from the checked V3 fields
  (`research/P21/probes/rev510_fidelity.lean:13-17`). It exits 0 with no output.

The endpoint proof spells the target's `a ∈ initialClassR` premise as `_ha`
at `H1RestartBeyond.lean:50`. This is not a hidden added hypothesis: it is
present in the authoritative target, and `SolvesBelow` already supplies genuine
shorter classical solutions from which `h1RestartAt` obtains each restart datum
(`H1Restart.lean:285-290`). In particular the statement is inhabited. The
worker's probe constructs `SolvesBelow 1 0 0 1 0 0` and applies the strict field
with `ν = S = 1`, `K = 0` on the nonempty interval `[0,1)`
(`research/P21/probes/b5r_registered.lean:26-42`); it exits 0. The inherited
restart probe also gives a zero-force/zero-datum instance on `Icc 0 1`
(`research/P21/probes/b4_closes.lean:41-49`) and was rerun successfully.

The contract boundary is clean:

- `Contracts/V3/Continuation.lean` imports only `Contracts.V2.*` and introduces
  no local restated definitions (`verification/Contracts/V3/Continuation.lean:1-24`).
  Thus V3 itself owes no new `rfl` bridge.
- The reused registered definitions already have explicit `rfl` bridges for
  `initialClassR`, `MemForceR`, `sobolevENorm`, and `timeShift`
  (`verification/Bindings/ContinuationV2.lean:48-69`). The non-definitional
  `ClassicalSolutionR` boundary is transported fieldwise through
  `continuationV2_solvesBelow_iff` (`ContinuationV2.lean:91-104`),
  `localTheoryV2_regularity_ofA02` (`LocalTheoryV2.lean:70-79`), and the proved
  lifespan `iSup` equality (`Bindings/MaximalPartial.lean:127-138`). V3 uses
  exactly those conversions at `verification/Bindings/ContinuationV3.lean:29-46`.
- The test imports only Contract/Binding/TestSupport modules, defines
  `checkedContinuationV3`, audits it, and projects both fields at
  `verification/Tests/ContinuationV3.lean:1-46`.
- The registry leaves V2 at `verification/contracts.json:114-123`, adds the
  well-formed V3 entry at lines 125-134, and contains 35 enabled entries.
  `L21_H1` remains `Partial` at
  `formalization/blueprint/proof_graph.json:78-90`; the new proof/binding/test
  are compiled entrypoints at `formalization/blueprint/entrypoints.json:8`,
  `:63`, and `:85`.

Hygiene passes. The lane-specific Lean files contain no
`sorry`/`admit`/`axiom`/`native_decide` tokens and no `maxHeartbeats` setting.
The four authorized edits in `EnstrophyInequality.lean` only replace
`tac1 <;> tac2` by `(tac1; tac2)` at lines 143, 249, 256, and 465; direct Lean
is silent, so the cleanup is semantically neutral.

`git diff --name-only origin/erenup/core...HEAD` lists 32 files because this
branch intentionally contains the unmerged 503/506/507 ancestry. Using the
lane-start merge commit `d559c66d` isolates 13 lane-510 files, and

```text
git diff --name-only d559c66d..HEAD -- \
  formalization/NSFormalization/Section3/T11/H1Bridges.lean \
  formalization/NSFormalization/Section4/A04/EnstrophyBarrier.lean \
  formalization/NSFormalization/Section4/A04/H1Bridges.lean \
  formalization/NSFormalization/Section4/A04/H1BridgesSmooth.lean \
  formalization/NSFormalization/Section4/A04/H1Restart.lean
```

has empty output. Thus lane 510 did not edit the 503/506/507 modules. Its only
existing Lean-module edit is the explicitly authorized four-line linter cleanup.

## 3. Gaps

There is no remaining whole-space B5 goal. The honest remaining gap is the
periodic half, exactly as the report says at
`research/P21/REPORT_510.md:63-69` and the handoff enumerates at
`research/P21/P6_SPLIT.md:196-212`.

The required whole-tree searches were performed before accepting that gap:

```text
$ grep -rn -E 'h1RestartT|h1UniformEndpointT' formalization/NSFormalization/Section4
[no output; exit 1]
$ grep -rn -E 'h1RestartT|h1UniformEndpointT' formalization/NSFormalization
[no output; exit 1]
```

The nearby periodic endpoint theorem is not the missing unconditional result:
it explicitly takes `H : PeriodicQuantitativeLocalInput'`
(`formalization/NSFormalization/Section3/T11/RestartBeyond.lean:408-424`), and
that input is itself only a target definition
(`Section3/T11/LocalExistence.lean:23-37`). Therefore leaving the periodic
registration and final `L21_H1` recoloring to lane 511 is correct.

The substantive negative check flips the strict endpoint inequality at
`research/P21/probes/rev510_mutation.lean:21-30`; it does not remove an argument.
Lean rejects the checked theorem with exit 1:

```text
../research/P21/probes/rev510_mutation.lean:30:2: error: Type mismatch
  Tests.checkedContinuationV3.restartBeyondH1
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ (f : SpaceTimeField),
        MemForceR f →
          ∀ (S : ℝ),
            0 < S →
              ∀ (K : ℝ≥0∞),
                K ≠ ∞ →
                  ∃ δ,
                    0 < δ ∧
                      ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
                        a ∈ initialClassR →
                          SolvesBelow ν a f S u p →
                            (∀ t ∈ Ico 0 S, (sobolevENorm 1 fun x => u (t, x)) ≤ K) →
                              ENNReal.ofReal (S + δ) < maximalLifespanR ν a f
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ (f : SpaceTimeField),
        MemForceR f →
          ∀ (S : ℝ),
            0 < S →
              ∀ (K : ℝ≥0∞),
                K ≠ ∞ →
                  ∃ δ,
                    0 < δ ∧
                      ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
                        a ∈ initialClassR →
                          SolvesBelow ν a f S u p →
                            (∀ t ∈ Ico 0 S, (sobolevENorm 1 fun x => u (t, x)) ≤ K) →
                              maximalLifespanR ν a f < ENNReal.ofReal (S + δ)
```

## 4. Commands and results

All Lean invocations sourced `scripts/lean-env.sh`, set
`LEAN_NUM_THREADS=6`, and ran Lake from `verification/`.

`lake build NSFormalization.Section4.A04.H1RestartBeyond` exited 0. Lake replayed
only pre-existing upstream/vendor warnings; there was no warning from the lane
module, and the exact final line was:

```text
Build completed successfully (10508 jobs).
```

Direct checks of `H1RestartBeyond.lean`, `Contracts/V3/Continuation.lean`,
`Bindings/ContinuationV3.lean`, and the authorized
`EnstrophyInequality.lean` each exited 0 with zero output. The test emitted:

```text
Contract BlowupDensity.Tests.checkedContinuationV3: checked; standard logical axioms only
```

`lake env lean ../research/P21/axioms_b5r.lean` exited 0 with the exact output:

```text
'NSFormalization.Section4.A04.restartFixedForceH1' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.restartFixedForceH1: checked; standard logical axioms only
'NSFormalization.Section4.A04.restartBeyondH1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.restartBeyondH1_le: checked; standard logical axioms only
'NSFormalization.Section4.A04.restartBeyondH1' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.restartBeyondH1: checked; standard logical axioms only
'BlowupDensity.Bindings.continuationV3_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract BlowupDensity.Bindings.continuationV3_holds: checked; standard logical axioms only
'BlowupDensity.Tests.checkedContinuationV3' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract BlowupDensity.Tests.checkedContinuationV3: checked; standard logical axioms only
```

The actual-target build and fidelity probe both exited 0 with zero output.
`lake env lean ../research/P21/probes/b5r_registered.lean` exited 0:

```text
'BlowupDensity.Tests.checkedContinuationV3' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract BlowupDensity.Tests.checkedContinuationV3: checked; standard logical axioms only
```

`python3 experiments/check_contracts.py --summary` exited 0:

```text
{
  "registered_contracts": 35,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

`make check` exited 0 with its complete output:

```text
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2275 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 35,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.003s

OK
```

`make test` exited 0. Its output begins with `lake -d verification test` and its
last V3-specific lines are:

```text
ℹ [10972/11036] Replayed Tests.ContinuationV3
info: Tests/ContinuationV3.lean:21:0: Contract BlowupDensity.Tests.checkedContinuationV3: checked; standard logical axioms only
```

`make test-mutations` exited 0; the exact final lines were:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

The required article audit exited 0; its exact final summary was:

```text
72 declarations; 27 article entries; 0 forbidden-axiom results
```

`make paper` exited 0. Both PDFs were already up to date, and the reader check
reported:

```text
Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
26 numbered article statements and their guide mappings checked.
27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
86 article labels resolved.
16 bibliography entries resolved; 35 registry declarations found; guide code paths verified.
Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
```

The same six lines were obtained from the independent
`python3 experiments/check_reader_documents.py` run. The full lane gate

```text
scripts/gates.sh NSFormalization.Section4.A04.H1RestartBeyond Contracts.V3.Continuation Bindings.ContinuationV3 Tests.ContinuationV3
```

exited 0; its exact final lines were:

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "registered_contracts": 35,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

Finally, `git diff --check` exited 0 with zero output. All tracked files remained
unchanged by this review; the only reviewer additions are the two permitted
`rev510_*.lean` probes and this review file.
