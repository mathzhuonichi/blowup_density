# D01 — registering `D01.datum_lemmas_v2` (lane 054)

V2 of the registered contract `D01.datum_lemmas` (lane 034). It `extends` the
frozen V1 record `Contracts.V1.DatumLemmas.DatumLemmasAPI` and adds the
half-order time-norm finiteness of lane 042
(`formalization/NSFormalization/Section4/D01/HalfOrder.lean`), so that R43/R44's
smallness hypotheses are certified non-vacuous through a contract and
`HalfOrder.lean` enters the tested build closure.

Precedent copied exactly: `I02.correction_v2` (lane 048) —
`Contracts/V2/Correction.lean` (`extends` V1 + new fields), `Bindings/CorrectionV2.lean`
(`{ V1witness with newField := … }` + `toV1` compatibility binding + `rfl`
bridges), `Tests/CorrectionV2.lean`, and the JSON entry `version: 2`.

## 1. What is bundled — theorem → field

All three new fields are theorems of `NSFormalization.Section4.D01` in
`HalfOrder.lean` (lane 042, reviewed `research/D01/REVIEW_HALFORDER.md`). Their
contract-vocabulary shape was already verified as `example`s in
`research/D01/axioms_halforder.lean:35,39,43`; the fields reproduce those
statements against `Contracts.V1.Data`.

| contract field | `HalfOrder.lean` theorem | consumer |
|---|---|---|
| `forceSobolevENorm_ne_top` (∀ real `s ≤ m`, `q ∈ {1,2}`) | `forceSobolevENorm_ne_top` (`:156`) | R44 S1/G6 at `m=0, s=-1/2, q=2`; general |
| `forceSobolevENormL1_half_ne_top` | `forceSobolevENormL1_half_ne_top` (`:178`) | R43 §4 G3 (`04-whole-space.tex:88`) |
| `forceSobolevENormL2_half_ne_top` | `forceSobolevENormL2_half_ne_top` (`:183`) | R43 `L²_t` companion |

Field types are stated with `Contracts.V1.Data`'s `SpaceTimeField`, `MemForceR`,
`forceSobolevENorm`, `forceSobolevENormL1`, `forceSobolevENormL2`. The `L2`
instance is stated with `Data.forceSobolevENormL2 (1/2) f`, which is by `abbrev`
`Data.forceSobolevENorm 2 (1/2) f`, defeq to `HalfOrder.forceSobolevENormL2_half_ne_top`'s
conclusion `forceSobolevENorm 2 (1/2) f ≠ ⊤`; the binding is therefore
`:= HalfOrder.…` with no `by` block, exactly like the L¹ and general fields.

### Bindings, zero `by` blocks
```
def datumLemmasV2 : Contracts.V2.DatumLemmas.DatumLemmasV2API :=
  { Bindings.datumLemmas with
    forceSobolevENorm_ne_top := fun _ hf _ _ hsm _ hq =>
      NSFormalization.Section4.D01.forceSobolevENorm_ne_top hf hsm hq
    forceSobolevENormL1_half_ne_top := fun _ hf =>
      NSFormalization.Section4.D01.forceSobolevENormL1_half_ne_top hf
    forceSobolevENormL2_half_ne_top := fun _ hf =>
      NSFormalization.Section4.D01.forceSobolevENormL2_half_ne_top hf }
```
The `fun … =>` argument permutations mirror the V1 binding style; no field is a
`by` proof.

### `rfl` bridges (anti-drift), following `axioms_halforder.lean`
`Bindings/DatumLemmasV2.lean` §1 commits two bridges into the build (in
`axioms_halforder.lean` they were only in a scratch file run by hand):
* `NSFormalization.Section4.D01.forceSobolevENorm = Contracts.V1.Data.forceSobolevENorm := rfl`
* `NSFormalization.Section4.D01.forceSobolevENormL1 = Contracts.V1.Data.forceSobolevENormL1 := rfl`

`MemForceR`'s bridge (`datumLemmas_memForceR_eq`) already lives in
`Bindings.DatumLemmas` and is imported, not repeated. `HalfOrder.lean` has no
local `forceSobolevENormL2` (it writes `forceSobolevENorm 2` directly), so there
is nothing to bridge for the L² name.

### Compatibility binding (precedent has one)
`Bindings/CorrectionV2.lean` has `correctionV1_of_v2`, so we add
`def datumLemmas_of_v2 : Contracts.V1.DatumLemmas.DatumLemmasAPI :=
datumLemmasV2.toDatumLemmasAPI`. Definitional; it makes "V2 drops or weakens no
V1 field" a typechecked fact. `Tests.checkedDatumLemmas` is untouched and keeps
running against `Bindings.datumLemmas`.

## 2. Left out, and why

* **The homogeneous half of G3.** `Data.forceHomogeneousENorm 1 (1/2) f ≠ ⊤`
  and the path-level monotonicity `forceHomogeneousENorm 1 (1/2) f ≤
  forceSobolevENormL1 (1/2) f` (G2, `04-whole-space.tex:132`) are **not** proved
  anywhere in the tree. Both need a *homogeneous* datum for a general `H^∞` slice
  — an `L²`-multiplier `ξ ↦ |ξ|^{1/2}(1+|ξ|²)^{-1/4}` construction beyond order
  monotonicity — while the only in-tree homogeneous-datum constructions
  (`Homogeneous.exists_isHomogeneousSliceDatum`, `isHomogeneousSliceDatum_compact`)
  cover Schwartz / compactly supported fields only. Recorded gap:
  `HalfOrder.lean`'s docstring §"What is not here" and
  `research/D01/ATTEMPTS_HALFORDER.md`. Not a field of V2.
* **The order shift / norm equivalence** and every other item on the V1
  out-of-scope list are inherited verbatim; V2 adds only the finiteness of the
  *inhomogeneous* time norms.

## 3. Notes for the lead

* `forceSobolevENorm_ne_top` is the general field and already covers R44's `s =
  -1/2, q = 2` (via `m = 0`), so R44 G6 ("register lane-042 `forceSobolevENorm_ne_top`
  into DatumLemmas V2") is fully served by this one field; the two half-order
  `s = 1/2` instances are the named specializations R43 cites.
* The JSON `scope` string states the honest boundary: general finiteness for `s ≤
  m`, `q ∈ {1,2}`; the two `1/2` instances; and that the homogeneous half of G3
  is not asserted.
* `HalfOrder.lean` now enters the tested closure through `Bindings.DatumLemmasV2`
  (confirmed: `Tests.DatumLemmasV2` closure printed by `check_contracts.py`
  includes it transitively; `make test` replays it).

## 4. Gates (all green)

```
cd verification && lake build Contracts.V2.DatumLemmas Bindings.DatumLemmasV2 Tests.DatumLemmasV2
  → Built all three; "Contract …checkedDatumLemmasV2: checked; standard logical axioms only"
make check            → check_formalization_plan / check_contracts / test_contract_policy (13 ok) / check_work_queue (30 items ok)
make test             → all 11 contracts "checked; standard logical axioms only", incl. checkedDatumLemmasV2
make test-mutations   → implementation_refactor accepted; admitted_proof / extra_axiom / weakened_hypothesis rejected; suite passed
python3 experiments/check_contracts.py --base-ref origin/erenup/integration  → exit 0, base_compatibility_checked: true
```
No `maxHeartbeats`; the contract imports only `Contracts.V1.DatumLemmas`.
