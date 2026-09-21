ACCEPT-WITH-NOTES

Exact one-line fix: in `formalization/NSFormalization/Section3/T24/MultipleOmegaComponents.lean:19`, replace the stale nonexistent revised-paper citation ``(`03-torus.tex:697-706`)`` with ``(`paper/revised/sections/03-torus.tex:511-520`)``.

## 1. What the lane claims

`research/T24/REPORT_497.md:5-16` claims the P5.1 construction of prescribed
placements, admissible scales, raw scaled no-slip components and their support,
and the P5.2 construction of literal finite sums, a
`ClassicalSolutionOmega`, force-class membership, rest, and no-slip. It
explicitly does not claim P5.3--P5.5 (`research/T24/REPORT_497.md:32-37`).

That scope is faithful to the revised article. The bounded-domain proposition
fixes positive `T`, positive viscosity and finitely many disjoint interior balls
at `paper/revised/sections/03-torus.tex:511-517`; chooses scaled packets starting
at `T-ε_j²` at `:519-520`; defines the three sums at `:521-524`; uses
disjoint support to kill cross transports and obtain the momentum equation at
`:525-526`; and obtains no-slip at `:533`. The lane does not claim the regional
blow-up or energy/dissipation clauses at `:528-531`.

The worker report's citation list is correct at
`research/T24/REPORT_497.md:17`. The copied internal comment at
`formalization/NSFormalization/Section3/T24/MultipleOmegaComponents.lean:19`
is the sole citation defect: the revised file has only 556 lines, so `697-706`
does not exist. This is documentation-only and has the exact one-line fix above.

## 2. What is in Lean

The canonical `MultipleRegionsOmegaAPI` declares the P5.1 fields verbatim at
`formalization/NSFormalization/Section3/T24/MultipleOmega.lean:51-99` and the
P5.2 fields at `:100-127,145-147`. The lane supplies exactly those types:

| Unit | Canonical statement | Implementation | Exact-field probe |
|---|---|---|---|
| P5.1 geometry and placement | `MultipleOmega.lean:51-79` | `MultipleOmegaComponents.lean:20-73` | `research/T24/probes/p5a_closes.lean:16-28,45-56` |
| P5.1 component and support | `MultipleOmega.lean:80-99` | `MultipleOmegaComponents.lean:75-155` | `p5a_closes.lean:30-42,57-59` |
| P5.2 sums and formulas | `MultipleOmega.lean:100-116` | `MultipleOmegaAssembled.lean:52-62` | `p5a_closes.lean:60-76` |
| P5.2 solution, pin, force, rest, no-slip | `MultipleOmega.lean:117-127,145-147` | `MultipleOmegaAssembled.lean:69-82,197-228` | `p5a_closes.lean:63-64,78-90` |

The exact-field probe elaborates with no output. In particular, the solution is
for the literal summed force and zero initial datum; momentum uses `Ioo 0 T` in
`Ω`; divergence/no-slip use `Ico 0 T`; pressure is the finite sum of the
individually `Ω`-normalized pressures; and support is global outside each
prescribed ball. These are the canonical types, not weakened variants.

There is no conclusion-shaped premise. `RegionsOmegaData` contains the genuine
upstream `Section4.I03.PacketData` plus raw pressure, force, PDE, blow-up, domain,
time, and region fields (`MultipleOmegaComponents.lean:20-46`); it contains no
solution, API, or existence field. This is also the approved explicit-upstream-
field pattern from the lead note, not a gap. Positivity/non-vacuity is explicit:
`hΩ`, `hT`, `N_pos`, `regionRadius_pos`, positive `ε`, and strict `ε²<T`
occur at `MultipleOmegaComponents.lean:33-43,64-73`; no empty interval,
`⊤.toReal = 0`, or analogous escape is used. The stored `blowup` field is unused
in P5.1--P5.2 because it is intentionally consumed by P5.3, not because a
P5.1--P5.2 conclusion was assumed (`MultipleOmegaComponents.lean:32`).

The torus proof was genuinely adapted: its non-overlap/cross-transport pattern
is at `formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:98-111,218-241`;
the domain proof uses global component support at
`MultipleOmegaAssembled.lean:94-116`, then consumes it in advection and momentum
at `:183-206`, and installs that momentum theorem in the solution at `:215-225`.

The required substantive mutation is
`research/T24/probes/rev497_drop_regions_disjoint.lean:16-35`. Its input
interface deletes `regions_disjoint` but retains the component support statement;
the copied momentum dependency then fails exactly where separated balls are
needed. This is not an arity error from merely omitting an argument. Exact result:

```text
../research/T24/probes/rev497_drop_regions_disjoint.lean:35:39: error: Application type mismatch: The argument
  hij
has type
  i ≠ j
but is expected to have type
  Disjoint ?m.35 ?m.36
in the application
  disjoint_left.mp hij
```

The non-vacuity probe constructs the registered singular packet on the open unit
box with `N=1` and a centered radius-`1/4` ball
(`research/T24/probes/rev497_nonvacuity.lean:17-85`), then constructs the actual
assembled domain solution at `:87-91` and witnesses an interior time, region
point, and domain point at `:93-97`. Its exact output is:

```text
'Rev497Nonvacuity.assembledSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev497Nonvacuity.domains_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Gaps

There is no mathematical residual in P5.1 or P5.2. P5.3 regional
agreement/blow-up, P5.4 energy/dissipation additivity, P5.5 final API assembly,
and V2 registration are accurately reported as later units, not as missing
library lemmas (`research/T24/REPORT_497.md:34-37` and
`research/T24/T24_SPLIT.md:414-416`). The lead's parallel-lane threading rule is
therefore respected.

The report makes no "not in the tree" claim. Nevertheless, I ran the required
whole-`Section4` search over every declared later-unit name and supplier name:

```text
$ grep -rnE 'region_agreement|region_blowup|energyEssSupOmega|energyGradientOmega|multipleRegionsOmegaStatement|MultipleRegionsOmegaAPI|scaled_total_dissipation|energyGradient_scaled_eq|energyEssSup_scaled_le|speed_unbounded_at_target|zeroPastField_speed' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/I03/Energy.lean:232:theorem energyEssSup_scaled_le (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
formalization/NSFormalization/Section4/I03/Energy.lean:262:theorem scaled_total_dissipation (hP : PacketData U K M D) (x₀ : Space)
formalization/NSFormalization/Section4/I03/Energy.lean:304:theorem energyGradient_scaled_eq (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
formalization/NSFormalization/Section4/I03/Energy.lean:325:  rw [hA, hB, scaled_total_dissipation hP x₀ hε hT,
formalization/NSFormalization/Section4/I03/Energy.lean:466:  have hle := energyEssSup_scaled_le hP x₀ hε hT
formalization/NSFormalization/Section4/I03/Energy.lean:492:  le_antisymm (energyEssSup_scaled_le hP x₀ hε hT) (le_energyEssSup_scaled hP x₀ hε hT)
```

Thus Section4 already has the P5.4 per-component suppliers; it does not contain
the later domain assembly fields. The lane correctly calls those later work,
not absent lemmas.

The only accepted note is the stale citation at
`MultipleOmegaComponents.lean:19`. It does not alter a statement or proof.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, only from
`verification/`, with `LEAN_NUM_THREADS=6`.

### Build and direct elaboration

```text
$ lake build NSFormalization.Section3.T24.MultipleOmegaComponents
⚠ [8778/8836] Replayed NSFormalization.Source.FiniteHilbertBochner
[middle: replayed dependency warnings only; target module emitted no diagnostic]
Build completed successfully (10134 jobs).

$ lake build NSFormalization.Section3.T24.MultipleOmegaAssembled
⚠ [8778/9189] Replayed NSFormalization.Source.FiniteHilbertBochner
[middle: replayed dependency warnings only; target module emitted no diagnostic]
Build completed successfully (10135 jobs).
```

Both exits were 0. The nonempty build output is entirely replayed pre-existing
dependency warnings; both lane modules themselves are silent.

```text
$ lake env lean ../formalization/NSFormalization/Section3/T24/MultipleOmegaComponents.lean
[no output; exit 0]
$ lake env lean ../formalization/NSFormalization/Section3/T24/MultipleOmegaAssembled.lean
[no output; exit 0]
$ lake env lean ../research/T24/probes/p5a_closes.lean
[no output; exit 0]
```

### Axioms

`research/T24/axioms_p5a.lean:2-46` has 45 `#print axioms` commands, one for
every definition/theorem in the two modules. The raw output begins and ends:

```text
'NSFormalization.Section3.T24.RegionsOmegaData.placement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsOmegaData.placement_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[middle records omitted under the review raw-output limit]
'NSFormalization.Section3.T24.RegionsOmegaData.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsOmegaData.solution_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The exact parser result was:

```text
axiom_records=45 bad_records=0
```

### Repository gates

```text
$ make check
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2241 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 29,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.003s

OK
```

The article axiom audit was also independently rerun, and its generated
`report.json` is byte-identical to the tracked
`formalization/blueprint/AXIOM_AUDIT.json`:

```text
Bindings.CompletedDensity: 8 declarations checked
NSFormalization.Section3.T21.MainAssembly: 33 declarations checked
NavierStokes.ComparatorR3Theorem: 2 declarations checked
Bindings.BoundaryInsertionV2: 4 declarations checked
NSFormalization.Source.PacketBreakdown: 1 declarations checked
Bindings.LocalTheoryV2: 1 declarations checked
Bindings.TorusLocalTheory: 1 declarations checked
Bindings.AffineVariation: 1 declarations checked
NSFormalization.Section3.T24.MultipleAssembly: 1 declarations checked
NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
NSFormalization.Section4.R43.Universal: 1 declarations checked
Bindings.ForceClasses: 1 declarations checked
Bindings.GridObservations: 1 declarations checked
56 declarations; 27 article entries; 0 forbidden-axiom results
```

Neither the committed lane diff nor current review additions touch
`verification/` (`git diff --name-only origin/erenup/core...HEAD -- verification`
and `git status --short -- verification` both emitted no output). Therefore the
brief's conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/core` gates are not applicable.

### Hygiene and change surface

The forbidden-token/heartbeat search over both production modules, the worker
probe/axiom file, and both reviewer probes emitted no output: no
`sorry`/`admit`/`axiom`/`native_decide`, and no `maxHeartbeats` setting.

The committed change surface is exactly:

```text
formalization/NSFormalization/Section3/T24/MultipleOmegaAssembled.lean
formalization/NSFormalization/Section3/T24/MultipleOmegaComponents.lean
formalization/blueprint/AXIOM_AUDIT.json
formalization/blueprint/entrypoints.json
research/T24/ATTEMPTS_P5A.md
research/T24/REPORT_497.md
research/T24/T24_SPLIT.md
research/T24/axioms_p5a.lean
research/T24/probes/p5a_closes.lean
```

The existing-module test reports only:

```text
NEW formalization/NSFormalization/Section3/T24/MultipleOmegaAssembled.lean
NEW formalization/NSFormalization/Section3/T24/MultipleOmegaComponents.lean
```

Thus no existing Lean module was edited. `git diff --check
origin/erenup/core...HEAD` also emitted no output. The review itself adds only
the two permitted `research/T24/probes/rev497_*.lean` files and this mandatory
review file; the already-present untracked lane brief was not touched.
