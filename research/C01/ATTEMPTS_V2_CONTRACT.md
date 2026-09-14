# ATTEMPTS — lane 152-C01-v2-contract (register the ordinary energy identity as C01 V2)

Lane goal: register the now-unconditional ordinary energy identity
(`energyIdentity_classical_unconditional`, lane 150) as the C01 **V2** contract field
`energyIdentity`, following `research/C01/REVIEW_E4.md` §4's plan.  Registration-only lane:
no new mathematics, one `formalization` prerequisite (the clamp-free restatement) plus the
`verification` contract/binding/test/registry.

## What landed

1. `formalization/NSFormalization/Section4/C01/EnergySpec.lean` (new, 73 lines incl.
   docstrings): `def pairing` and `theorem energyIdentity_l2Sq` — the clamp-free
   `l2Sq`/`slice`/`pairing` form of `energyIdentity_classical_unconditional`, proved exactly
   as `research/C01/probes/rev150_gap.lean` (8-line body: `congr_of_eventuallyEq` +
   `projIcc_of_mem` + `norm_toLp_sq_eq_l2Sq`).  Std 3 axioms, 0 own warnings.
2. `verification/Contracts/V2/EnergyAbsorptionPartial.lean`:
   `EnergyAbsorptionPartialV2API extends EnergyAbsorptionPartialAPI` + the two spec-local
   defs `gradientSq`/`pairing` + the field `energyIdentity` token-for-token from
   `Spec.lean:344-350`.  Imports `Contracts.V1.EnergyAbsorptionPartial` only.
3. `verification/Bindings/EnergyAbsorptionPartialV2.lean`: `energyAbsorptionPartialV2` via
   `{ energyAbsorptionPartial with energyIdentity := … }`; the `pairing` `rfl` bridge; the
   one non-`rfl` `gradientSq` bridge (`PiLp.norm_sq_eq_of_L2` + `integral_congr_ae`, verbatim
   `rev150b_gradientsq.lean`); `energyAbsorptionPartial_of_v2 : … = energyAbsorptionPartial
   := rfl`.
4. `verification/Tests/EnergyAbsorptionPartialV2.lean`: `checkedEnergyAbsorptionPartialV2`
   + `run_cmd TestSupport.checkAxioms` + one `example` exercising `.energyIdentity`.
5. Registry `C01.energy_absorption_partial_v2` (version 2), and `C01.energy_absorption_partial_v2`
   added to the C01 item of `work_items.json` (re-rendered).

## Design choices (why)

* **`extends`, not verbatim restatement** (matching lane 141's `EnergyHighPartialV2API`):
  the six V1 fields plus `C₁`/`C₁_pos` are inherited unchanged through
  `toEnergyAbsorptionPartialAPI`, so the frozen V1 witness is reused (`{ … with … }`) and
  `energyAbsorptionPartial_of_v2 := rfl` guarantees no V1 field is silently dropped/weakened.
  Verbatim restatement would duplicate seven fields and lose that structural guarantee.
* **The `formalization` prerequisite `EnergyIdentity_l2Sq`** (REVIEW_E4 §4 step 1, the "N4"
  strictly-nicer statement): it moves the 8-line clamp/`norm_toLp_sq_eq_l2Sq` argument into
  `formalization/`, so the V2 binding is a pure assembly (one `rw` + one `exact`) instead of
  inlining analytic steps into the adapter.  The `pairing` side is `rfl` on both sides; the
  `gradientSq` side is the single non-`rfl` bridge (`gradientTensor` is a `Contracts.V1`
  object, so the `PiLp.norm_sq_eq_of_L2` step must live on the `verification` side).
* **`0 < ν` and `a ∈ initialClassR` are unused** in the binding field (`fun _ _ _ _ _ hf _ w
  _ ht => …`): the lane's theorem needs neither.  Recorded as a scope disclosure, not worked
  around.

## Negative examples / failures encountered

* **`def pairing (w z : SpatialField)` fails in `EnergySpec.lean`** — `SpatialField`
  (unqualified) resolved, under this module's *selective* `open NSFormalization.Section4.A02
  (ClassicalSolutionR MemForceR)`, to a non-function type from one of the vendor opens
  (`EulerLpTranslation`/`EulerOrdinarySobolev`/`NavierStokes.ProblemStatement`), so `w x`
  gave `Function expected at w but this term has type SpatialField`, and the downstream
  `HasDerivAt` value then failed to unify (spurious `EulerSmoothLimit.Space` vs `Space`
  mismatch, a *consequence* of the ill-formed `pairing`).  **Fix:** qualify the parameter as
  `A02.SpatialField` — exactly the return type of `C01.slice`, so `pairing (slice w.velocity
  t) (slice f t)` typechecks and the `pairing` `rfl` bridge to the contract still holds
  (`A02.SpatialField` defeq `Data.SpatialField`).  (Same class of hazard as LESSONS 09-14
  `autoImplicit`/`open` name-resolution: check what a bare type name resolves to before
  trusting it.)  The probe `rev150_gap.lean` never hit this because it never wrote
  `SpatialField` as a type annotation — it only applied `slice`.

## Gaps

None for `energyIdentity`.  `energyDifferentialBound` (`Spec.lean:364`) and `l2Bound`
(`Spec.lean:383`) are now unblocked but not proved on this branch, deliberately left out of
V2 (a future V3): the former is `HasDerivAt.unique` + `real_inner_le_norm` +
`norm_toLp_sq_eq_l2Sq` (REVIEW_E4 §4 close), the latter needs the
`Paper1.sqrt_energy_le_primitive` generalization.  The enstrophy fields and the assembly
remain out of scope as in V1.

## Commands and results

All from the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` from `verification/`.

| command | result |
|---|---|
| `lake build NSFormalization.Section4.C01.EnergySpec` | exit 0, `Built … EnergySpec` |
| `lake env lean …/EnergySpec.lean` | exit 0, 0 bytes (no own warnings) |
| `lake build Contracts.V2.EnergyAbsorptionPartial` / `Bindings.…V2` / `Tests.…V2` | exit 0 each |
| `lake env lean` on contract / binding / test | exit 0, 0 bytes each (test prints the checkAxioms info line only) |
| `lake env lean ../research/C01/axioms_v2_contract.lean` | `checkedEnergyAbsorptionPartialV2 depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `scripts/gates.sh NSFormalization.Section4.C01.EnergySpec` | `== gates OK`; make check clean, make test all contracts "standard logical axioms only" (incl. `checkedEnergyAbsorptionPartialV2`), `Mutation suite passed`, `base_compatibility_checked: true` |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | exit 0, `registered_contracts: 25`, `base_compatibility_checked: true` |
| `git diff --stat verification/contracts.json` | `1 file changed, 11 insertions(+)` (additions only) |
