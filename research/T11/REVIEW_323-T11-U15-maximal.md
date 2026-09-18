ACCEPT

## What the lane claims

The worker report claims the exact `exists_maximal` field, the exact
`maximal_unique` field, and the additional equality
`maximalLifespanT ν a f = Paper1.PeriodicLifespan.lifespan ν a f`
(`research/T11/REPORT_323.md:3-25`).  It explicitly identifies one residual
input, `PeriodicMaximalExistenceInput`, because U11 is not on this branch
(`research/T11/REPORT_323.md:60-65`; `research/T11/ATTEMPTS_MAXIMAL.md:55-70`).

## What is in Lean

The canonical API target is reproduced exactly:
`research/T11/probes/api_on_canonical.lean:85-99`
has the same quantifier order, `I`/`ENNReal.ofReal` strict guard, and
pointwise velocity/pressure conjunction as `Maximal.lean:270-304`.  The only
extra parameter is the explicitly named residual input on `exists_maximal`;
its statement is a direct positive-horizon `ClassicalSolutionT` existential
(`Maximal.lean:260-275`), matching the permitted fallback in the brief.

The lifespan equality is proved in both directions over the two defining
suprema (`Maximal.lean:239-256`): `toFlow` supplies the easy inequality, and
`flowToClassical` supplies the reverse conversion.  The conversion really
fills all three extra T10 fields (`Maximal.lean:175-235`), rather than
postulating an equality of structures.  This is consistent with the cited
Paper 1 definitions (`Paper1/PeriodicLifespan.lean:25-32`) and with the
unconditional gluing theorem
`exists_maximal_periodic_solution_of_lifespan_pos`
(`Paper1/PeriodicLocalLifespan.lean:409-413`).

`exists_maximal` derives positive lifespan from the named input, invokes that
gluing theorem, and converts every shorter normalized flow back to a
`ClassicalSolutionT` (`Maximal.lean:276-292`).  `maximal_unique` obtains a
realized horizon strictly above a presingular time and applies the previously
proved velocity/pressure uniqueness fields (`Maximal.lean:295-336`), matching
the Paper 1 maximal-agreement theorem’s common-interval conclusion
(`Paper1/PeriodicLocalLifespan.lean:513-529`).

The probe discharges all three claimed statements verbatim
(`research/T11/probes/maximal_closes.lean:17-39`) and includes a nonzero datum,
nonzero compact positive-time force, and nonzero initial velocity instance
under the one named input (`research/T11/probes/maximal_closes.lean:41-86`).
The axiom audit guards every declaration introduced by the module
(`research/T11/axioms_maximal.lean:5-67`).

## Gaps

There is one intentional, honestly isolated gap: the local-existence input
remains a hypothesis.  The existing Section 3 local-existence file only
declares the quantitative input and its lifespan lower-bound consequence
(`formalization/NSFormalization/Section3/T11/LocalExistence.lean:23-44`); it
does not provide the U11 `solution`/`horizon` assembly.  The whole-tree grep
over `formalization/NSFormalization/Section4` found no
`PeriodicMaximalExistenceInput`, `maximalLifespanT_eq_lifespan`, or T11
maximal theorem; the only similarly named declarations are the older whole-
space A02 results (`formalization/NSFormalization/Section4/A02/Maximal.lean:157-164,192-219`),
which use a different `IsMaximalSolution`.  Thus the report’s “U11 has not
landed” claim is correct for this branch and is the permitted single named
input, not a hidden weakening or vacuous theorem.

No forbidden declaration occurs in the module, probe, or audit file.  The one
`maxHeartbeats` setting is `400000` and is immediately commented as bounded
elaboration headroom (`Maximal.lean:151-154`).  The committed diff against
`origin/erenup/integration-section3` contains only the new module and the
announced research/audit records; no existing Lean module is modified.  The
scratch negative probe is the additionally permitted untracked file
`research/T11/probes/rev323_mutation.lean`.

## Commands and results

All commands were run after `. scripts/lean-env.sh`; Lake commands were run
from `verification/` with `LEAN_NUM_THREADS=6`, one Lake process at a time.

```text
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Maximal
exit=0
Build completed successfully (9976 jobs).
```
The build emitted only pre-existing upstream linter warnings (for example
`Source/FiniteHilbertBochner.lean:24`); there were no diagnostics from
`Maximal.lean`.

```text
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/Maximal.lean
exit=0 lines=0

cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/maximal_closes.lean
probe exit=0 lines=0

cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_maximal.lean
axioms exit=0 lines=0
```
The guarded `#print axioms` lines all expect exactly
`[propext, Classical.choice, Quot.sound]`.

`make check` exited 0 (43333 output lines).  Per the review hygiene limit, the
exact first and last 40 lines were:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 574,
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
{
  "registered_contracts": 38,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
      "NSFormalization.Section4.I01.Extension",
--- middle omitted (output is 43333 lines) ---
      "NavierStokes.TransitionRamp",
      "NavierStokes.TransportPrimitive",
      "NavierStokes.TrueConeLoop",
      "NavierStokes.UniformAngularReset",
      "NavierStokes.UniformBlockBounds",
      "NavierStokes.UniformCone",
      "NavierStokes.UniformFourierAlias",
      "NavierStokes.UniformHarmonicInteraction",
      "NavierStokes.UniformPrimaryWeights",
      "NavierStokes.ValidBandGluing",
      "NavierStokes.ValidDyadicBandCover",
      "NavierStokes.VariableGaugeMean",
      "NavierStokes.ViscousPropagator",
      "NavierStokes.VolterraAnalyticBounds",
      "NavierStokes.VolterraParity",
      "NavierStokes.VolterraRegularity",
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.TorusData"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```
The `source_hashes_match: false` and copied-source admission count are
pre-existing repository-wide checks; they do not mention the lane files.

The full requested gate script was also run with the Section 3 base:

```text
BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T11.Maximal
exit=0
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

The requested diff audit was:

```text
git diff --name-only origin/erenup/integration-section3...HEAD
formalization/NSFormalization/Section3/T11/Maximal.lean
research/T11/ATTEMPTS_MAXIMAL.md
research/T11/REPORT_323.md
research/T11/T11_SPLIT.md
research/T11/axioms_maximal.lean
research/T11/probes/maximal_closes.lean
```

For the required substantive negative check, `rev323_mutation.lean` changes
the presingular guard from `< maximalLifespanT` to `≤ maximalLifespanT` and
tries the unchanged theorem.  Lean fails as expected (exit 1), reporting:

```text
error: Type mismatch
  maximal_unique
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassT,
        ∀ f ∈ forceClassT,
          ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
            IsMaximalPeriodicSolution ν a f u₁ p₁ →
              IsMaximalPeriodicSolution ν a f u₂ p₂ →
                ∀ (t : ℝ),
                  0 ≤ t →
                    ENNReal.ofReal t < maximalLifespanT ν a f →
                      ∀ (x : Space), u₁ (t, x) = u₂ (t, x) ∧ p₁ (t, x) = p₂ (t, x)
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassT,
        ∀ f ∈ forceClassT,
          ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
            IsMaximalPeriodicSolution ν a f u₁ p₁ →
              IsMaximalPeriodicSolution ν a f u₂ p₂ →
                ∀ (t : ℝ),
                  0 ≤ t →
                    ENNReal.ofReal t ≤ maximalLifespanT ν a f →
                      ∀ (x : Space), u₁ (t, x) = u₂ (t, x) ∧ p₁ (t, x) = p₂ (t, x)
```

The final verdict is ACCEPT.
