ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims that lane 471 closes T24b Ub7 by assembling the existing
Ub1--Ub6 results into the canonical 30-field `MultipleRegionsAPI`, proving the
raw universal `multipleRegionsStatement`, registering the packet-indexed V1
contract as `T04.multiple_regions`, and giving a concrete registered `N = 1`
instance that exposes `region_blowup 0`
(`research/T24/REPORT_471.md:3-44`, `research/T24/REPORT_471.md:46-70`).  It
claims no bounded-domain/no-slip theorem, T18 insertion consequence, density,
sharpness, or optimality result (`research/T24/REPORT_471.md:72-81`).

That is the right mathematical scope.  The paper fixes finitely many disjoint
interior balls and positive viscosity and terminal time, asks for separate
regional blow-up, and specifies a solution from rest with finite energy and
dissipation (`paper/sections/03-torus.tex:697-704`).  Its proof chooses positive
scales with `ε_j^2 < T`, forms the three finite sums, kills cross-advection by
support separation, and gives the energy inequality and exact dissipation
identity (`paper/sections/03-torus.tex:705-719`).  It also explicitly notes that
the component blow-up sequences may differ (`paper/sections/03-torus.tex:721`).
The approved split assigns exactly this assembly, registration, and concrete
one-region instance to Ub7 (`research/T24/T24_SPLIT.md:335-342`).

The registry entry exists with id `T04.multiple_regions`, parent `T04`, version
1, the claimed specification/binding/test modules, and the checked declaration
(`verification/contracts.json:554-563`).  The T24 work item includes the id
(`collaboration/work_items.json:435-444`).

## 2. What is in Lean

### Statement fidelity and assembly

The report's exact packet-indexed statement is present verbatim in the V1
contract (`verification/Contracts/V1/MultipleRegions.lean:115-128`) and agrees
with the approved Spec (`research/T24/Spec.lean:1331-1345`):

```lean
def multipleRegionsStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketImportAPI ν) (T : ℝ), 0 < T →
    ∀ (N : ℕ), 0 < N →
      ∀ (regionCenter : Fin N → Space) (regionRadius : Fin N → ℝ),
        (∀ j : Fin N, 0 < regionRadius j) →
        (∀ j : Fin N, closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆
          interior fundamentalCube) →
        Pairwise (fun i j : Fin N ↦
          Disjoint (Metric.ball (regionCenter i) (regionRadius i))
            (Metric.ball (regionCenter j) (regionRadius j))) →
        Nonempty (MultipleRegionsAPI P T regionCenter regionRadius)
```

The contract record has exactly the claimed 30 fields, in the reported order
(`verification/Contracts/V1/MultipleRegions.lean:58-113`), matching the Spec's
record field-for-field (`research/T24/Spec.lean:1176-1329`).  A mechanical count
gave `contract structure fields: 30`.  In particular, the final fields use the
unmodified packet constants, `≤` for energy, and `=` for dissipation
(`verification/Contracts/V1/MultipleRegions.lean:107-113`), exactly as the
paper does (`paper/sections/03-torus.tex:714-718`).  The four locally restated
definitions have the Spec bodies (`verification/Contracts/V1/MultipleRegions.lean:26-44`),
and their whole-function `rfl` guards elaborate in the binding
(`verification/Bindings/MultipleRegions.lean:17-29`).

The raw canonical record has the same 30 fields
(`formalization/NSFormalization/Section3/T24/Multiple.lean:51-205`), and its raw
universal statement has the full packet clause list followed by the prescribed
geometry and the same `Nonempty` conclusion
(`formalization/NSFormalization/Section3/T24/Multiple.lean:207-257`).  The new
constructor assigns all 30 fields exactly once from `RegionsData`; the source
range has 30 `:=` assignments
(`formalization/NSFormalization/Section3/T24/MultipleAssembly.lean:14-48`).
The theorem then builds only `PacketData` and `RegionsData` from raw packet and
geometry hypotheses and returns that constructor
(`formalization/NSFormalization/Section3/T24/MultipleAssembly.lean:50-87`).  It
does not assume a placement, scaling record, component, assembled solution,
regional blow-up, or energy result.

The cited component lemmas really have the required field statements:

- placement/scaling, positive admissible scales, and `ε_j^2 < T` are at
  `formalization/NSFormalization/Section3/T24/MultipleComponents.lean:45-110`;
- selected classical solutions, both field pins, and the two cube-local support
  statements are at
  `formalization/NSFormalization/Section3/T24/MultipleComponents.lean:112-149`;
- the explicit sums, formula fields, `rest`, and `force_mem` are at
  `formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:37-74`;
- the finite-sum momentum equation and actual pinned `ClassicalSolutionT` are at
  `formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:231-260`;
- region agreement and regional blow-up are at
  `formalization/NSFormalization/Section3/T24/MultipleRegions.lean:18-63`;
- the original packet energy constant and assembled energy bound are at
  `formalization/NSFormalization/Section3/T24/MultipleRegions.lean:110-147`;
- the original packet dissipation constant and exact assembled identity are at
  `formalization/NSFormalization/Section3/T24/MultipleRegions.lean:264-315`.

The authorized duplicate reconciliation is exactly what the report says.  The
lane commit changes `MultipleRegions.lean` only by importing
`MultipleAssembled` and deleting the local, definitionally identical
`assembledVelocity`; the subsequent theorem statements are unchanged
(`formalization/NSFormalization/Section3/T24/MultipleRegions.lean:1-21`,
`research/T24/ATTEMPTS_UB7.md:19-26`).

The binding transports all 30 fields in both directions and proves both round
trips by `rfl` (`verification/Bindings/MultipleRegions.lean:31-116`).  Its
`regionsData` uses raw projections of the registered packet
(`verification/Bindings/MultipleRegions.lean:118-153`), its constructor invokes
the canonical assembly (`verification/Bindings/MultipleRegions.lean:155-165`),
and both the internal and public existence theorems have the claimed contract
statement (`verification/Bindings/MultipleRegions.lean:167-190`).  The test's
checked theorem and its three independent blow-up/energy/dissipation shape
checks are present (`verification/Tests/MultipleRegions.lean:14-42`).

### Hypothesis honesty and non-vacuity

There is no `⊤.toReal = 0` device or empty-interval/family escape.  The statement
requires `0 < ν`, `0 < T`, `0 < N`, positive radii, interior containment, and
pairwise disjointness (`verification/Contracts/V1/MultipleRegions.lean:118-128`).
The record repeats the positive horizon/family/radius facts, chooses every
scale in `Ioc 0 ε₀`, and records strict `ε_j^2 < T`
(`verification/Contracts/V1/MultipleRegions.lean:60-76`).  Regional blow-up
quantifies every positive height and left-neighbourhood and produces a time in
`Ioo 0 T` and a point in the prescribed ball
(`verification/Contracts/V1/MultipleRegions.lean:38-44`, `:107-109`).  The
energy conclusion is an `ℝ≥0∞` upper bound by a finite `ofReal`, and the
dissipation conclusion is an exact `ℝ≥0∞` equality (`:110-113`); neither can be
satisfied by a junk `toReal` value.

Some raw packet hypotheses and `hν` are not syntactically used in the final
packaging proof (`formalization/NSFormalization/Section3/T24/MultipleAssembly.lean:52-59`).
They are the complete raw spelling of the registered `PacketImportAPI`, not
new named analytic assumptions, and removing their use from the packaging step
makes the theorem stronger rather than vacuous.  Every substantive Ub field is
obtained from the isolated `RegionsData` construction and the cited Ub1--Ub6
theorems (`formalization/NSFormalization/Section3/T24/MultipleAssembly.lean:60-87`).

The worker's concrete probe is genuine: it uses the registered packet at
viscosity one, `T = 1`, `N = 1`, centre `(1/2,1/2,1/2)`, radius `1/4`, proves
positive radius and closed-ball containment, obtains the registered API, and
reads `region_blowup 0`
(`research/T24/probes/multiple_nonvacuity.lean:14-62`).  Pairwise disjointness
is necessarily vacuous for `Fin 1`, but the family itself is nonempty and its
blow-up conclusion is not.

### Hygiene and axioms

The base triple-dot command is ambiguous because this branch has three merge
bases.  Its exact modified-Lean output was:

```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using db7c6938fce0556b31f84cd73f7a416297592dc4
formalization/NSFormalization/Section3/T24/Multiple.lean
formalization/NSFormalization/Section3/T24/MultipleRegions.lean
```

`Multiple.lean` is not changed by the lane commit; it is an artifact of that
criss-cross merge-base selection.  The exact lane-commit Lean diff is:

```text
A formalization/NSFormalization/Section3/T24/MultipleAssembly.lean
M formalization/NSFormalization/Section3/T24/MultipleRegions.lean
A research/T24/axioms_ub7.lean
A research/T24/probes/multiple_nonvacuity.lean
A verification/Bindings/MultipleRegions.lean
A verification/Contracts/V1/MultipleRegions.lean
A verification/Tests/MultipleRegions.lean
```

Thus the only existing Lean module edited by the lane is the explicitly
authorized `MultipleRegions.lean` deduplication.  `git diff --check HEAD^..HEAD`
printed no output.  A scan of every Lean file in the lane commit for the exact
tokens `sorry`, `admit`, `axiom`, `native_decide`, and `set_option
maxHeartbeats` printed no output.  There is no heartbeat override.

The axiom audit contains exactly 22 entries (`research/T24/axioms_ub7.lean:3-27`),
and direct elaboration printed exactly:

```text
'NSFormalization.Section3.T24.multipleRegionsAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.multipleRegionsStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.finiteVelocitySum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.finitePressureSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.finiteForceSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.SpeedUnboundedAtOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.MultipleRegionsAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.multipleRegionsStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.MultipleRegions.finiteVelocitySum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.MultipleRegions.finitePressureSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.MultipleRegions.finiteForceSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.MultipleRegions.speedUnboundedAtOn_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.MultipleRegions.ofContract' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.MultipleRegions.toContract' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.MultipleRegions.to_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.MultipleRegions.of_to' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.MultipleRegions.regionsData' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.MultipleRegions.multipleRegions' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.MultipleRegions.multipleRegionsStatement_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.multipleRegions' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.multipleRegionsStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedMultipleRegions' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Gaps and review notes

There is no remaining torus Ub7 proof gap.  The bounded-domain/no-slip branch
is deliberately outside this torus contract, as the report and registry state
(`research/T24/REPORT_471.md:72-81`, `verification/contracts.json:562`).  The
required searches of the entire Section 4 tree found neither such a carrier nor
a pre-existing multiple-regions theorem:

```text
$ grep -rniE 'no.?slip|bounded.?domain|boundary collar|restriction norm|homogeneous.*boundary|Dirichlet|vanish.*boundary' formalization/NSFormalization/Section4
bounded/no-slip search exit 1
$ grep -rniE 'MultipleRegions|multiple.?regions|prescribed.*regions|prescribed.*balls|single.?copy|affineImage_subset_ball' formalization/NSFormalization/Section4
multiple-regions search exit 1
```

The omission is worded honestly: V1 does have a bounded-domain norm layer, but
no bounded-domain solution/no-slip carrier is threaded through this T24b
contract (`verification/Contracts/V1/MultipleRegions.lean:10-13`).  The lane
does not import or invoke a T18 insertion theorem
(`formalization/NSFormalization/Section3/T24/MultipleAssembly.lean:1`,
`verification/Bindings/MultipleRegions.lean:1-4`).

The independent negative probe substantively changes the exact dissipation
constant from `D^2` to `D^2 + 1`, rather than dropping an argument
(`research/T24/probes/rev471_wrong_dissipation_constant.lean:10-18`).  It fails
for the expected reason:

```text
../research/T24/probes/rev471_wrong_dissipation_constant.lean:18:2: error: Type mismatch
  a.dissipation_bound
has type
  energyGradientT T a.assembled_velocity ^ 2 = ENNReal.ofReal (P.dissipationBound ^ 2 * ∑ j, a.ε j)
but is expected to have type
  energyGradientT T a.assembled_velocity ^ 2 = ENNReal.ofReal ((P.dissipationBound ^ 2 + 1) * ∑ j, a.ε j)
```

One documentation-only note prevents an unqualified `ACCEPT`.  The current
paper puts the bounded-domain premise at line 698, the proposition's
homogeneous-no-slip sentence at line 703, and the boundary-collar argument at
line 719 (`paper/sections/03-torus.tex:698-703`, `:714-719`).  The repeated
tuple `03-torus.tex:698,706,720` points instead to the scale construction and
the end of the proof.  Exact one-line fixes:

1. In `verification/Contracts/V1/MultipleRegions.lean:11` and `:55`, replace
   `03-torus.tex:698,706,720` with `03-torus.tex:698,703,719`.
2. In `verification/contracts.json:562`, make the same replacement in `scope`.
3. In `research/T24/REPORT_471.md:75`, make the same replacement.
4. The same stale tuple is inherited from the earlier canonical/spec work at
   `formalization/NSFormalization/Section3/T24/Multiple.lean:46` and
   `research/T24/Spec.lean:1172`; correct those documentation citations in an
   authorized documentation follow-up, since this lane was not authorized to
   edit the existing canonical module for that purpose.

No Lean statement or proof needs to change.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake only from `verification/`.

1. Required closure:

```text
$ lake build NSFormalization.Section3.T24.MultipleAssembled NSFormalization.Section3.T24.MultipleRegions
[pre-existing replayed dependency linter messages only; no output from either requested module]
Build completed successfully (10052 jobs).
```

Exit 0.  The replayed messages name only dependencies (for example
`NSFormalization.Source.FiniteHilbertBochner`,
`NSFormalization.Paper1.PeriodicSobolevHilbert`, and vendor
`Formal.EndpointSafeTwoSpacePicard`), not either requested module.

2. Assembly build and direct elaboration:

```text
$ lake build NSFormalization.Section3.T24.MultipleAssembly
[pre-existing replayed dependency linter messages only; no output from MultipleAssembly]
Build completed successfully (10053 jobs).

$ lake env lean ../formalization/NSFormalization/Section3/T24/MultipleAssembly.lean
[0 output; exit 0]
```

3. Concrete probe and axiom file:

```text
$ lake env lean ../research/T24/probes/multiple_nonvacuity.lean
[0 output; exit 0]

$ lake env lean ../research/T24/axioms_ub7.lean
[the exact 22 lines pasted in section 2; exit 0]
```

4. `make check` exited 0.  Its contract-closure JSON is approximately 1.5 MB;
the exact non-closure output was:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 705,
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
[closure JSON; "registered_contracts": 51, "base_compatibility_checked": false]
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The copied-source `BoundaryCorollary.lean` token and hash status are pre-existing
repository-plan diagnostics, not in the lane's import closure or changed Lean
files.  The lane-local forbidden-token scan is empty as recorded above.

5. `make test` exited 0.  It replayed pre-existing dependency warnings and all
registered contract lines.  The exact new line was:

```text
info: Tests/MultipleRegions.lean:18:0: Contract BlowupDensity.Tests.checkedMultipleRegions: checked; standard logical axioms only
```

6. `make test-mutations` exited 0.  Its exact decisive output was:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

7. Standalone base compatibility check exited 0.  The full output is the same
large closure JSON; an exact JSON readback of the decisive fields was:

```text
{
  "registered_contracts": 51,
  "base_registered_contracts": null,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

A separate read-only count of the two registries printed:

```text
base 50 False
head 51 True
```

8. Full gate script:

```text
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T24.MultipleAssembly
== make check
[passed; same plan/policy/work-queue and 51-contract output above]
== lake build NSFormalization.Section3.T24.MultipleAssembly
[pre-existing replayed dependency warnings only]
Build completed successfully (10053 jobs).
== make test
[all registered contract checks reported standard logical axioms only]
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

9. The deliberate mutation command exited 1 with the exact expected error
pasted in section 3.  The Section 4 searches exited 1 with no matches, as also
pasted in section 3.
