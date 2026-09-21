# ATTEMPTS — lane 156-C01-v3-contract (register `energyDifferentialBound` + `l2Bound` as C01 V3)

Lane `156-C01-v3-contract`, worktree `.claude/worktrees/156-C01-v3-contract`, branch
`erenup/156-C01-v3-contract` off `origin/erenup/integration` `f7cd6db`.  Contract-registration
lane only: it wraps the two lane-154 theorems (`Section4/C01/EnergyBounds.lean`) as the 26th
versioned contract.  **No `formalization/` file added or changed.**

## What was registered

`C01.energy_absorption_partial_v3` (version 3), the two remaining ordinary-energy consequences
of the identity, each **token-for-token** from `research/C01/Spec.lean`:

* `energyDifferentialBound` (`Spec.lean:364-370`) — the Cauchy–Schwarz form
  `E' + 2ν·gradientSq(u(t)) ≤ 2·l2Norm(f(t))·l2Norm(u(t))` for any `E'` that is the derivative
  of `s ↦ l2Sq(u(s))` at every interior `t ∈ Ioo 0 T`.
* `l2Bound` = **eq:RL2** (`Spec.lean:383-387`) — `l2Norm(u(t)) ≤ energyBudget a f t` for every
  presingular `t ∈ Ico 0 T`, with `energyBudget a f t = l2Norm a + ∫₀ᵗ l2Norm(f(s)) ds`.

`EnergyAbsorptionPartialV3API extends EnergyAbsorptionPartialV2API` (so every V1/V2 field is
inherited verbatim), and the two new spec-local `def`s `forcePrimitive` (`Spec.lean:218-219`) /
`energyBudget` (`Spec.lean:224-225`) are restated in the contract vocabulary.

## Files added

* `verification/Contracts/V3/EnergyAbsorptionPartial.lean` — the record + two fields + two defs.
* `verification/Bindings/EnergyAbsorptionPartialV3.lean` — `energyAbsorptionPartialV3`, the two
  `rfl` def bridges, and the `energyAbsorptionPartialV2_of_v3` compatibility `rfl`.
* `verification/Tests/EnergyAbsorptionPartialV3.lean` — `checkedEnergyAbsorptionPartialV3`,
  `run_cmd TestSupport.checkAxioms`, one conformance `example` per field.
* `research/C01/axioms_v3_contract.lean` — `#print axioms` of the checked witness + the two
  lane-154 theorems, plus three `rfl`-bridge `example`s.
* Registry: `verification/contracts.json` (+1 entry, additions-only) and
  `collaboration/work_items.json` (C01 item's `contracts` list) + `tasks.py render`.

## Binding shape (as the reviewer dry run predicted, `probes/rev154_v3_binding_dryrun.lean`)

`energyAbsorptionPartialV3 = { energyAbsorptionPartialV2 with … }`:

* `l2Bound := fun _ hν _ _ _ hf _ w _ ht => C01.l2Bound (uniqueness_toA02 w) hf hν ht` — **no
  bridge**; the contract's `energyBudget`/`l2Norm`/`slice` are defeq to the tree's, and
  `(uniqueness_toA02 w).velocity = w.velocity` by `rfl`.
* `energyDifferentialBound := fun _ _ _ _ _ hf _ w _ ht E' hderiv => by
  rw [energyAbsorptionPartialV2_gradientSq_eq]; exact C01.energyDifferentialBound
  (uniqueness_toA02 w) hf ht E' hderiv` — **exactly one** `rw`, the already-existing V2
  `gradientSq` bridge; nothing else.
* `forcePrimitive`/`energyBudget` bridges are `rfl`
  (`energyAbsorptionPartialV3_{forcePrimitive,energyBudget}_eq`).

## Attempts / decisions (nothing failed to compile; recorded for the trail)

1. **Reused the verified dry run verbatim.**  `probes/rev154_v3_binding_dryrun.lean` (reviewer,
   lane 154) already stated the two fields in the contract's vocabulary and discharged them; the
   binding bodies here are that file's, moved from `example` to structure fields.  No new proof
   was invented — the point of the lane is registration, and the review had already confirmed
   the exact bridge count (one for `energyDifferentialBound`, zero for `l2Bound`, `rfl` for the
   two defs).
2. **`gradientSq`/`pairing` are NOT re-declared** in V3 — they are inherited from
   `Contracts.V2.EnergyAbsorptionPartial` (opened `(gradientSq)`), so the contract's `gradientSq`
   stays the registered `gradientTensor` (Frobenius) form, not a copy of the tree's raw-integral
   `NSFormalization.Section4.C01.gradientSq` (which carries the same *name* but a different
   *body* — see `logs/LESSONS.md`/REVIEW note 4).  Only `forcePrimitive`/`energyBudget`, which
   no earlier version restated, are new in V3.
3. **Import policy.**  The contract imports only `Contracts.V2.EnergyAbsorptionPartial` (which
   pulls `Contracts.V1.*`), satisfying `check_contracts.py`'s `contract_import_allowed`.  V1's
   `l2Norm` is opened alongside `slice l2Sq` (V2 opened only `slice l2Sq`, since its one field
   did not mention `l2Norm`; V3's fields do).
4. **Tests trust boundary.**  The Tests module imports only `Contracts.V3.*`,
   `Bindings.EnergyAbsorptionPartialV3`, `TestSupport.Axioms` — no `Formal.*` reaches it
   directly, so `warningAsError` is respected, exactly as V2's test.
5. **`autoImplicit` non-check note.**  Contract files are the frozen *statements*; the fidelity
   check here is token equivalence to `Spec.lean:364-370`/`:383-387` (done by eye and by the
   conformance `example`s in the Tests file, which restate both fields and are discharged by the
   witness), not a hypothesis-necessity mutation (that was lane 154's job, `REVIEW_ENERGY_BOUNDS.md`
   §5).

## Commands and results (from the worktree; `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` from `verification/`)

* `lake build Contracts.V3.EnergyAbsorptionPartial` → `Built … (3.8s)`, exit 0 (only vendor
  Paper3 warnings; none from the new file).
* `lake build Bindings.EnergyAbsorptionPartialV3` → `Built … (3.5s)`, exit 0.
* `lake build Tests.EnergyAbsorptionPartialV3` → exit 0;
  `Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3: checked; standard logical axioms only`.
* `lake env lean ../research/C01/axioms_v3_contract.lean` → exit 0; the checked witness and both
  lane-154 theorems each `depends on axioms: [propext, Classical.choice, Quot.sound]`; the three
  `rfl`-bridge `example`s emit nothing (they typecheck).
* `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` → exit 0,
  `registered_contracts: 26`, `base_compatibility_checked: true`.
* `git diff --stat verification/contracts.json` → additions only (11 insertions, 0 deletions).
