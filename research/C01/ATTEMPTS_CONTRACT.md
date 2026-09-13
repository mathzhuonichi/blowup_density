# C01 contract registration — attempts and decisions (lane 091)

Registering `C01.energy_absorption_partial`, the **proved part** of
`research/C01/Spec.lean`'s `EnergyAbsorptionAPI`, as a version-1 lemma-bundle
contract, following the lane 071 (`B01.bochner_partial`) precedent exactly:
`verification/Contracts/V1/EnergyAbsorptionPartial.lean` +
`Bindings/EnergyAbsorptionPartial.lean` + `Tests/EnergyAbsorptionPartial.lean` +
`verification/contracts.json` + the C01 work item.

## What went in, what stayed out

**Fields registered** (types copied verbatim from `research/C01/Spec.lean`):

| field | `Spec.lean` | discharging theorem (`NSFormalization.Section4.C01.…`) |
|---|---|---|
| `velocityJets` | :295-300 | `velocity_slice_memHInfty_and_smoothL2` (VelocityJets.lean) |
| `forceTimeRegularity` | :326-329 | `forceTimeRegularity` (ForceSlices.lean) |
| `trilinearHolder` | :410-414 | `trilinearHolder` (Trilinear.lean) |
| `trilinearAbsorbed` | :435-439 | `trilinearAbsorbed` (Trilinear.lean) |
| `laplacianSqENorm` | :471-473 | `laplacianSqENorm` (Trilinear.lean) |

These are **exactly** the five fields the conformance files
`research/C01/axioms_u1u3.lean`, `axioms_u2.lean`, `axioms_u6.lean` discharge as
`example`s whose type is a spec field verbatim. The other `example`s in those
files (`lintegral_advection_inner_laplacian_le`,
`integrable_advection_inner_laplacian` in `axioms_u6.lean`, and the U3 audit
declarations in `axioms_u1u3.lean`) are auxiliary certified facts, **not** fields
of `EnergyAbsorptionAPI`, so they are not registered.

**Note (lane 091 review finding 4).** `Trilinear.lean:214
integrable_advection_inner_laplacian` — the fact that `x ↦ ⟨(z·∇)z, Δz⟩` is
integrable on the jet class once `‖z‖₃ < ⊤`, i.e. that `advectionWork z` is the
true Bochner integral and not Mathlib's junk `0` — is **proved but not a field of
`Spec.lean`'s `EnergyAbsorptionAPI`**, so it is deliberately not exported now
(this partial contract mirrors `Spec.lean` field-for-field). It should ride along
with the enstrophy fields in a later version, since those are the fields that
actually consume the trilinear bound and need the non-junk guarantee.

**Data fields carried** (also verbatim from `Spec.lean`): `C₁` (:260),
`C₁_pos` (:262). `trilinearAbsorbed` refers to `C₁`, so it must be a field.
Following the full spec I paired it with `C₁_pos`; both are discharged by the
**registered** `A05.gradient_l6` binding — `C₁ := gradientL6.Csix`,
`C₁_pos := gradientL6.Csix_pos` — exactly as `axioms_u6.lean` takes
`C₁ = Bindings.gradientL6.Csix`. These are the only *data* fields, so
`EnergyAbsorptionPartialAPI` is a `Type` and its binding is a `def` (like B01's
`bochnerPartial`, which carries `χ : Space → ℝ`), not a `theorem`.

**Excluded, recorded in the module docstring + registry `scope` as gaps** — each
appears in `research/C01/Spec.lean` but is **not** discharged by any theorem in
`Section4/C01/*.lean` on this branch (they live in `Evolution.lean` only as the
draft's PDE displays with no proof):

* the ordinary-energy fields `energyIdentity`, `energyDifferentialBound`,
  `l2Bound` (`Spec.lean:344-387`);
* the enstrophy fields `enstrophyIdentity`, `enstrophyDifferentialBound`,
  `enstrophyIntegralBound` (`Spec.lean:487-541`);
* the Fourier inequality `sobolevTwoFourier` (`Spec.lean:555-558`) and the
  assembly `h2TimeIntegral`, `h2TimeIntegralZeroDatum` (`Spec.lean:576-607`);
* the constants `CRH1`, `CH2`, `Cassembly` and their `_pos` (mentioned only by
  the excluded fields), and the whole `gradientL6 : GradientL6API` record
  `Spec.lean` carries. The three C01 fields that touch the gradient/Laplacian use
  the **standalone** `Contracts.V1.GradientL6` defs `gradientTensor`, `laplacian`,
  `SmoothSquareIntegrableJets`, not any field of `GradientL6API`, so the bundled
  record is not needed and is not carried.

I verified the exclusion is honest: `Evolution.lean`'s theorems were checked, and
no `example` in any `axioms_*.lean` file states any of the excluded field types,
so none is discharged in the tree.

## Which vocabulary is canonical and which is spec-local

Confirmed against `verification/Contracts/V1/Data.lean` and
`Contracts/V1/GradientL6.lean`:

* `SpatialField` (Data:99), `SpaceTimeField` (Data:104), `ClassicalSolutionR`
  (Data:624), `initialClassR` (Data:509), `MemForceR` (Data:544), `MemHInfty`
  (Data:495) are used directly (opened, not restated) from `Contracts.V1.Data`.
* `lift` (GradientL6:78), `gradientTensor` (GradientL6:89), `laplacian`
  (GradientL6:94), `SmoothSquareIntegrableJets` (GradientL6:106) are used directly
  from `Contracts.V1.GradientL6`.
* Only the six spec-local time-slice `def`s — `slice` (:167), `l2Sq` (:172),
  `l2Norm` (:177), `laplacianSq` (:191), `criticalL3` (:212), `advectionWork`
  (:202) — have no `Data.lean`/`GradientL6.lean` declaration, so those six are
  restated token-for-token in the contract and each is bridged by `rfl` in the
  binding to `NSFormalization.Section4.C01.{slice,l2Sq,l2Norm,laplacianSq,
  criticalL3,advectionWork}`. `gradientSq`, `pairing`, `forcePrimitive`,
  `energyBudget` of `Spec.lean` are **not** restated: they are mentioned only by
  the excluded fields (the task-brief def list is narrowed accordingly, as B01
  narrowed away `scaledCutoff`/`schwartzVector`).

The contract's two imports are `Contracts.V1.Data` and `Contracts.V1.GradientL6`,
both `Contracts.*` — the import allowlist of `experiments/check_contracts.py` is
satisfied with no canonical-module extension.

## Binding shape

* `velocityJets := fun _ _ _ _ _ _ _ w _ ht => velocity_slice_memHInfty_and_smoothL2
  (uniqueness_toA02 w) ht`. `Contracts.V1.Data.ClassicalSolutionR` and the
  `Section4/A02/SolutionClass.lean` restatement are two separately declared
  `structure`s (distinct inductive types), so a `rfl` bridge for the structure is
  impossible; the solution is moved across **field by field** by the already-merged
  `Bindings.uniqueness_toA02` (reused from `Bindings/Uniqueness.lean`, not
  re-declared — the "one restatement" discipline of `CLAUDE.md`). Every field
  type is defeq, so the conversion typechecks and `A02.MemHInfty`/`A05.SmoothL2`
  match the contract's `MemHInfty`/`SmoothSquareIntegrableJets`. This is exactly
  the move `axioms_u1u3.lean`'s `toA02` performs.
* `forceTimeRegularity := …forceTimeRegularity` — direct assignment; the local
  `slice`/`l2Norm` are definitionally the contract's.
* `trilinearHolder`, `trilinearAbsorbed`, `laplacianSqENorm := fun z hz => …`
  eta over `(z, hz)`; the local `SmoothL2`/`advectionWork`/`criticalL3`/`laplacianSq`
  are definitionally the contract's (rfl bridges), and for `trilinearAbsorbed`
  `ENNReal.ofReal (gradientL6.Csix)` is defeq to the theorem's
  `ENNReal.ofReal gradientL6Const`.
* `C₁ := gradientL6.Csix`, `C₁_pos := gradientL6.Csix_pos` from `Bindings.GradientL6`.

## Failures / corrections

No mathematical dead ends: this lane registers already-merged proofs, so every
field had a known discharging theorem. The contract, binding and test each built
first try. I did **not** write a separate `research/C01/axioms_contract.lean`: the
existing conformance files already exercise the same defeq field-by-field, and
`Tests/EnergyAbsorptionPartial.lean`'s `run_cmd TestSupport.checkAxioms` audits
the assembled `checkedEnergyAbsorptionPartial` directly, so a fourth conformance
file would be redundant.

Two decisions worth flagging for the reviewer:

1. **`C₁`/`C₁_pos` carried, `gradientL6 : GradientL6API` not.** The five proved
   propositional fields never mention `gradientL6`; they mention the standalone
   `Contracts.V1.GradientL6` *defs*. Only `C₁` is referenced (by
   `trilinearAbsorbed`), so I carry `C₁` (+ its positivity for honesty) and drop
   the bundled record. A reviewer wanting the full `GradientL6API` bundled here
   should note it is separately registered as `A05.gradient_l6`.
2. **`C₁_pos` is registered though the `axioms_*.lean` files did not conformance-check
   it.** It is provable (`gradientL6.Csix_pos`) and keeps the data constant honest
   (a `C₁ ≤ 0` binding would make `trilinearAbsorbed` a *stronger*, unprovable
   claim, not a vacuous one). This matches the full-spec pairing of `C₁` with
   `C₁_pos` at `Spec.lean:260-262`.

## Commands and results

All from the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake from
`verification/`, one lake at a time.

```
lake build Contracts.V1.EnergyAbsorptionPartial   -> Built (3.2s)
lake build Bindings.EnergyAbsorptionPartial       -> Built (3.4s)
lake build Tests.EnergyAbsorptionPartial          -> Built; info: Contract
    BlowupDensity.Tests.checkedEnergyAbsorptionPartial: checked; standard
    logical axioms only
make check                                        -> plan/contracts/policy/work-queue OK
make test                                         -> every registered contract re-checked,
    incl. checkedEnergyAbsorptionPartial; standard logical axioms only
make test-mutations                               -> refactor accepted; admitted/extra_axiom/weakened rejected
check_contracts.py --base-ref origin/erenup/integration  -> registered_contracts 16;
    base_compatibility_checked True
```

No `sorry`, `admit`, `axiom`, `native_decide`, `maxHeartbeats` or `set_option` in
the three new files. Transitive axioms of `checkedEnergyAbsorptionPartial`:
`propext`, `Classical.choice`, `Quot.sound` only.
