ACCEPT

## 1. What the lane claims

This is the re-review of commit `d087f07` on the rebased baseline `9825a35`, judged against the
later fix brief. The worker claims:

1. The divergence simplification was moved to the renamed lane module
   `A01/ConstructorDivergenceSlice`, leaving the owner's unsuffixed module untouched. It replaces
   the word-descent detour with the existing vendor weak-to-classical divergence bridge and keeps
   both public theorem statements unchanged (`research/MAINT/REPORT_176.md:5-9`).
2. The generalized scalar regularized-square-root argument is owned by
   `Paper1.sqrt_energy_le_primitive_general`; both the old Paper1 theorem and C01 wrapper keep their
   statements (`research/MAINT/REPORT_176.md:10-13`).
3. `SliceWiring` retires the pure `velocitySliceSmoothL2` alias, keeps the compatibility field
   theorem in definitionally equal vocabulary, adds an arbitrary-order finiteness theorem, and
   retains the old `q+1` theorem (`research/MAINT/REPORT_176.md:14-17,32-38`).
4. Two C01 manuscript citations are corrected from line 103 to line 104
   (`research/MAINT/REPORT_176.md:18`). Six other batch modules were inspected but not changed
   (`research/MAINT/REPORT_176.md:19-22`).
5. The owner's six-field `C01.energy_absorption_v4` is registered, lane 177 is cancelled, and the
   unregistered `Enstrophy`/`EnstrophyIdentityRaw` route is left for a future SIMP deduplication row
   (`research/MAINT/CLOSURE_PLAN.md:55-70`).

These claims are accurate, including the deliberately disclosed alias-retirement signature
exception.

## 2. What is in Lean

### Rebase ownership and statement invariance

The lead's two owner files are untouched. With `origin/erenup/integration` at the brief's pinned
`9825a35`, `git diff origin/erenup/integration --` on
`A01/ConstructorDivergence.lean` and `C01/EnstrophyIdentity.lean` is empty; their base and HEAD blob
IDs are respectively identical (`954b40c5...` and `0002157f...`). The owner's divergence module is
the six-theorem chain beginning with `ordinaryLift_eq_embedding` and ending with
`spatialDivergence_eq_zero_of_cylinder`
(`formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean:27-88`), while the owner's
enstrophy identity is at
`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:147-183`.

A mechanical token-normalized extraction of every top-level `theorem`/`def` header in the four
changed formalization modules, comparing the pinned baseline `9825a35` with HEAD, gives:

| module | token-identical retained declarations | added | removed / changed |
|---|---:|---|---|
| `Paper1/ScalarEnergy` | 7/7 | `sqrt_energy_le_primitive_general` | none |
| `A01/ConstructorDivergenceSlice` | 2/2 | none | none |
| `A01/SliceWiring` | 4/5 | `sobolevENorm_slice_ne_top_order` | removed alias `velocitySliceSmoothL2`; `velocitySliceSmoothL2_field` changed only to unfold it |
| `C01/EnergyBounds` | 14/14 | none | none |

In particular, a verbatim (not merely normalized) extraction of the two Slice divergence headers
at base and HEAD has an empty `diff`. The exact current statements are at
`ConstructorDivergenceSlice.lean:62-71` and `:112-126`. The compatibility-only `hu` premise is in
the same position at `:65`; it is explicitly isolated by `have _hu := hu` in the proof at `:72`.
This premise is not mathematically load-bearing after the simplification, but it is neither new nor
hidden: it is retained exactly to preserve the consumed signature, as required by the fix brief.
Direct Lean checking has no unused-variable warning.

The scalar declarations also match the report exactly. The new generalized statement is
`sqrt_energy_le_primitive_general` with endpoint hypothesis `sqrt (E 0) <= N 0`, nonnegativity,
continuity, derivative, and factor-2 differential hypotheses
(`formalization/NSFormalization/Paper1/ScalarEnergy.lean:26-34`). The old zero-endpoint theorem has
its base-token-identical statement and is now a direct corollary (`:77-88`). The C01 wrapper also
has its base-token-identical statement and is a direct call to the Paper1 owner
(`formalization/NSFormalization/Section4/C01/EnergyBounds.lean:180-190`).

The SliceWiring exception is honest and scoped. The retained compatibility theorem now mentions
the canonical carrier directly (`formalization/NSFormalization/Section4/A01/SliceWiring.lean:98-100`),
whose definition and identical field equation are at
`formalization/NSFormalization/Section4/C01/Evolution.lean:115-125`. The arbitrary-order theorem
uses `w.sobolev m` and concludes `sobolevENorm ... != top`; the old `q+1` statement is its one-line
corollary (`SliceWiring.lean:109-119`). A tree-wide search finds no production or verification term
consumer of the retired alias; the retained `_field` theorem is referenced only by research
`#print`/`#check` audits (`research/A01/axioms_slice_wiring.lean:23`,
`research/A01/probes/rev157_sigs.lean:8`).

### Mathematical fidelity and non-vacuity

The scalar mathematics matches the manuscript. The paper regularizes by
`(y^2 + zeta^2)^(1/2)` and obtains the forcing-primitive bound
(`paper/sections/04-whole-space.tex:100-104`); its ordinary energy estimate is exactly
`||u(t)||_2 <= ||a||_2 + integral_0^t ||f(s)||_2`
(`paper/sections/04-whole-space.tex:117-120`). Lean derives the endpoint square bound and the
regularized `G 0 <= delta` estimate from the sharp endpoint hypothesis
(`formalization/NSFormalization/Paper1/ScalarEnergy.lean:60-73`); it does not assume the conclusion.
The C01 `l2Bound` retains the genuine presingular interval `Ico 0 T`
(`formalization/NSFormalization/Section4/C01/EnergyBounds.lean:194-206`).

The divergence simplification also preserves the intended mathematics. It applies
`divergenceFree_classical_divergence_zero` to the existing cylinder `hdiv` membership
(`ConstructorDivergenceSlice.lean:75-94`). The vendor theorem assumes membership in the genuine
`divergenceFreeSpace` and concludes pointwise coordinate divergence zero
(`vendor/NavierStokesAndEuler/Euler/ClassicalDivergence.lean:15-21`); its proof uses the weak
divergence test identity (`:34-43`). No pointwise divergence hypothesis was added.

There is no `top.toReal = 0` escape or empty-interval trick. The new Slice theorem proves an
`ENNReal` value is genuinely not `top` from an actual Sobolev datum
(`SliceWiring.lean:109-113`; the datum-to-infimum lemma is
`formalization/NSFormalization/Section4/D01/SmoothDatum.lean:314-320`). The scalar hypotheses are
jointly satisfiable away from zero: the checked control uses `T=1`, constant `E=4`, `N=2`, and
evaluates at `t=1/2` (`research/MAINT/probes/rev176_nonvacuity.lean:14-26`).

The citation corrections are right: the sentence explicitly including zero-norm times is paper
line 104 (`paper/sections/04-whole-space.tex:104`), and the two corrected references are at
`research/C01/Spec.lean:362-363` and `:529-531`.

### Closure plan and hygiene

The repaired C01 plan is current. The registry names `C01.energy_absorption_v4` and its binding,
test, and six-field scope (`verification/contracts.json:291-299`). The contract fields are exactly
`enstrophyIdentity`, `enstrophyDifferentialBound`, `enstrophyIntegralBound`, `sobolevTwoFourier`,
`h2TimeIntegral`, and `h2TimeIntegralZeroDatum`
(`verification/Contracts/V4/EnergyAbsorption.lean:43-104`), and the binding uses the owner's C01
chain (`verification/Bindings/EnergyAbsorptionV4.lean:19-37`). Lane 177's cancellation is also
recorded independently (`PLAN.md:335`, `logs/AGENT_RUNS.csv:656`).

The proposed future deduplication is stated rather than performed. The Raw module contains the
strict-interior alternatives at
`formalization/NSFormalization/Section4/C01/EnstrophyIdentityRaw.lean:199-255`; the registered owner
chain contains the quantitative differential/integral bounds
(`C01/EnstrophyBounds.lean:32-39,109-119`), Fourier bound
(`C01/SobolevTwo.lean:75-88`), and terminal-horizon results
(`C01/H2TimeIntegral.lean:132-158`).

No changed Lean code uses `sorry`, `admit`, an `axiom` declaration, or `native_decide`; the only
text-search hits are prose containing the words “axiom” or “sorry” in research comments. No
changed file contains `maxHeartbeats`. The lane changes no `paper/`, `verification/`, frozen
contract, or existing test file. The four existing formalization edits are precisely the modules
authorized by this SIMP brief; the two protected owner modules remain untouched.

## 3. Gaps

No blocking or follow-up gap remains from the prior `ACCEPT-WITH-NOTES` review. The `hu` warning,
stale divergence/EnergyBounds prose, divergence numstat, alias-retirement disclosure, tester ledger,
and C01 closure-plan status are all corrected
(`research/MAINT/ATTEMPTS_SIMP_176.md:16-25,28-51`;
`research/MAINT/REPORT_176.md:5-17,32-38,87-93`;
`research/MAINT/CLOSURE_PLAN.md:55-70`).

There are no remaining “not in the tree” claims to accept. As a defensive whole-Section4 check,
the exact theorem-name search finds all five post-identity owner results:

```text
formalization/NSFormalization/Section4/C01/SobolevTwo.lean:77:theorem sobolevTwoFourier ...
formalization/NSFormalization/Section4/C01/EnstrophyBounds.lean:32:theorem enstrophyDifferentialBound ...
formalization/NSFormalization/Section4/C01/EnstrophyBounds.lean:109:theorem enstrophyIntegralBound ...
formalization/NSFormalization/Section4/C01/H2TimeIntegral.lean:133:theorem h2TimeIntegral ...
formalization/NSFormalization/Section4/C01/H2TimeIntegral.lean:148:theorem h2TimeIntegralZeroDatum ...
```

The identity itself is at `formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:147`.
No fix is requested.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`; `lake` ran only from `verification/` with
`LEAN_NUM_THREADS=6`.

### Ownership and signatures

```text
$ git diff --exit-code origin/erenup/integration -- formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean
[0 bytes]
owner_diff_exit=0

$ diff -u <(base Slice theorem headers) <(HEAD Slice theorem headers)
[0 bytes]
signature_diff_exit=0
```

The mechanical all-declaration comparison printed:

```text
Paper1/ScalarEnergy: identical=7 changed=0 removed=[] added=[sqrt_energy_le_primitive_general]
A01/ConstructorDivergenceSlice: identical=2 changed=0 removed=[] added=[]
A01/SliceWiring: identical=4 changed=[velocitySliceSmoothL2_field]
  removed=[velocitySliceSmoothL2] added=[sobolevENorm_slice_ne_top_order]
C01/EnergyBounds: identical=14 changed=0 removed=[] added=[]
```

### Builds and direct checks

The changed modules plus the required consumer were built together:

```text
$ lake build NSFormalization.Paper1.ScalarEnergy NSFormalization.Section4.A01.ConstructorDivergenceSlice NSFormalization.Section4.A01.SliceWiring NSFormalization.Section4.C01.EnergyBounds NSFormalization.Section4.A01.ForceBridge
Build completed successfully (10343 jobs).
exit 0
```

The build replayed warnings only from pre-existing `Source/`, `Paper3/`, and vendor modules; it
printed no warning from a lane-touched module. Direct checks were exactly:

```text
CMD lake env lean ../formalization/NSFormalization/Paper1/ScalarEnergy.lean
[0 bytes]
exit=0
CMD lake env lean ../formalization/NSFormalization/Section4/A01/ConstructorDivergenceSlice.lean
[0 bytes]
exit=0
CMD lake env lean ../formalization/NSFormalization/Section4/A01/SliceWiring.lean
[0 bytes]
exit=0
CMD lake env lean ../formalization/NSFormalization/Section4/C01/EnergyBounds.lean
[0 bytes]
exit=0
CMD lake env lean ../formalization/NSFormalization/Section4/A01/ForceBridge.lean
[0 bytes]
exit=0
```

The full Section4 build (therefore all Section4 dependents, not only direct importers) ended:

```text
module_count=154
✔ [10572/10575] Built NSFormalization.Section4.A01.ConstructorDivergence (3.3s)
✔ [10573/10575] Built NSFormalization.Section4.A01.ConstructorDatumPath (4.6s)
✔ [10574/10575] Built NSFormalization.Section4.A01.DatumPathDeriv (11s)
✔ [10575/10575] Built NSFormalization.Section4.A01.ForcedSourceUpgrade (10s)
Build completed successfully (10575 jobs).
exit 0
```

### Axiom audits and negative checks

All nine conformance files exited 0. Counts of printed declarations were 5, 2, 14, 10, 6, 9,
12, 5, and 9 respectively for `axioms_b1_ladder`, `axioms_c6`, `axioms_pressure_p3`,
`axioms_slice_wiring`, `axioms_e5`, `axioms_e6e7`, `axioms_energy_bounds`,
`axioms_r44_pieces`, and `axioms_g1`. Every declaration's exact axiom payload was:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

There were no other axiom payloads. In particular, the changed divergence declarations printed:

```text
'NSFormalization.Section4.A01.divergence_ae_of_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.divergence_of_cylinder_pointwise_of_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit=0
```

Four of the ten recorded substantive mutations were independently rerun (the fix brief required at
least three). Exact decisive output:

```text
../research/A01/probes/rev162_mutate_divergence_constant.lean:30:2: error: Type mismatch
  divergence_of_cylinder_pointwise_of_contDiff u U hu hU hdiv Z hZ velocity hslice hslice_contDiff
has type
  ∀ t ∈ Ico 0 T, ∀ (x : Space), spatialDivergence velocity t x = 0
but is expected to have type
  ∀ t ∈ Ico 0 T, ∀ (x : Space), spatialDivergence velocity t x = 1
exit=1

../research/A01/probes/rev157_mut2_const.lean:36:2: error: Type mismatch
...
has type
  ∀ (t : ↑(Icc 0 S)), ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt (↑(q + 1)) w.velocity ↑t
but is expected to have type
  ∀ (t : ↑(Icc 0 S)), ‖u t‖ ≤ 1 * sobolevNormAt (↑(q + 1)) w.velocity ↑t
exit=1

../research/C01/probes/rev154_mut_A_constant.lean:37:2: error: linarith failed to find a contradiction
...
a✝ : 1 * (l2Norm (slice f t) * l2Norm (slice w.velocity t)) <
  2 * pairing (slice w.velocity t) (slice f t)
⊢ False
failed
exit=1

../research/MAINT/probes/rev176_mutate_budget.lean:26:2: error: Type mismatch
  h (1 / 2) ...
has type
  √4 ≤ 2
but is expected to have type
  √4 ≤ 1
exit=1
```

The corresponding non-vacuity control was exact zero output:

```text
CMD lake env lean ../research/MAINT/probes/rev176_nonvacuity.lean
[0 bytes]
exit=0
```

### Repository gates

`scripts/gates.sh` was run with all changed/inspected modules plus `ForceBridge`. Its decisive exact
tail was:

```text
Build completed successfully (10364 jobs).
== make test
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
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

The standalone `make check` also exited 0; its final policy checks were:

```text
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
exit=0
```

Finally, the explicit base-compatibility command produced these exact result fields:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
{
  "registered_contracts": 28,
  ... closure listing ...
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
exit=0
```

The omitted middle is only the checker's 27,000-line closure listing; the displayed first and last
fields are copied verbatim from the saved output. At command time the remote-tracking ref was the
brief's pinned `9825a35`, and final status before writing this review was clean and one commit ahead.
During report writing, the shared remote-tracking ref advanced externally to `7b57a29`; the reviewed
commit and requested audit baseline remain `d087f07` over `9825a35`. Writing this mandated report is
the reviewer's only worktree change; no Lean, record, probe, index, or branch ref was changed.
