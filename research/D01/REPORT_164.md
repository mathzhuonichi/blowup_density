# Lane 164 report: D01 G1 datum-form homogeneous norm

## 1. What is defined and proved

In namespace `NSFormalization.Section4.D01`:

```lean
def dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ
```

The consumer lemmas are:

```lean
dotHomogeneousENorm_le_of_isHomogeneousSlice
  (hG : IsHomogeneousSliceDatum s z G) :
  dotHomogeneousENorm s z ≤ ‖G‖ₑ

le_of_isHomogeneousSlice
  (hG : IsHomogeneousSliceDatum s z G) :
  dotHomogeneousENorm s z ≤ ‖G‖ₑ

dotHomogeneousENorm_zero (s : ℝ) :
  dotHomogeneousENorm s (0 : SpatialField) = 0

dotHomogeneousENorm_ne_top_of_isHomogeneousSlice
  (hG : IsHomogeneousSliceDatum s z G) :
  dotHomogeneousENorm s z ≠ ⊤

dotHomogeneousENorm_ne_top
  (hz : ∃ G : RealVectorSobolev s, IsHomogeneousSliceDatum s z G) :
  dotHomogeneousENorm s z ≠ ⊤
```

The zero theorem constructs the zero tempered vector distribution and zero
homogeneous datum.  All other results follow directly from the ENNReal
infimum.  A05 and R43's definitions were identical; R44 intentionally has no
local spatial homogeneous norm because its initial datum is zero and its force
hypothesis is the inhomogeneous `L²_t H^{-1/2}_x` norm.  The complete comparison
is in `ATTEMPTS_G1.md`.

## 2. What is in Lean now

* `formalization/NSFormalization/Section4/D01/HomogeneousNorm.lean`: the
  definition and five theorem declarations above (including the short alias).
* `verification/Contracts/V1/HomogeneousNorm.lean`: the version-1 definition
  restated verbatim, importing only `Contracts.V1.Data`.
* `verification/Bindings/HomogeneousNorm.lean`:
  `theorem dotHomogeneousENorm_eq :
  Contracts.V1.HomogeneousNorm.dotHomogeneousENorm =
  NSFormalization.Section4.D01.dotHomogeneousENorm := rfl`.
* `verification/Tests/HomogeneousNorm.lean`: the checked public equality and
  `TestSupport.checkAxioms` audit.
* `verification/contracts.json`: one append-only registration,
  id `D01.homogeneous_norm`, component version 1.  The registry now has 27
  enabled contracts.
* `research/D01/ATTEMPTS_G1.md`: side-by-side spec reconciliation, reuse audit,
  and the reason the V1 pointwise quantities are unusable.
* `research/D01/axioms_g1.lean`: three non-vacuous consumer examples and axiom
  prints for every new declaration.

No existing contract, existing test, or existing formalization module was
changed.  `collaboration/work_items.json` did not need an edit: `make check`
accepted its existing D01 state, so no task-card render was run.

## 3. Gaps

G1 is closed.  The definition is not identified with
`Contracts.V1.Data.dotHHalfENorm` or `dotHThreeHalvesENorm`: those abbreviate a
pointwise `angularFourier` integral that is faithful only on `L¹ ∩ L²` slices
and may totalize to junk zero on a general non-`L¹` `H^∞` field.

The optional comparison

```lean
0 ≤ s → dotHomogeneousENorm s z ≤ sobolevENorm s z
```

is not added.  The current tree does not make it a short lemma: it requires the
new real-vector multiplier `|ξ|^s(1+|ξ|²)^(-s/2)`, its contraction bound,
preservation of the real subspace, and the realization identity.  This is the
already-recorded G2/homogeneous-G3 work in
`Section4/D01/HalfOrder.lean:38-56`, not an order-theoretic consequence of G1.
The time-integrated homogeneous force finiteness and comparison remain open for
the same reason.

## 4. Commands and results

All shells sourced `scripts/lean-env.sh`; every `lake` command ran from
`verification/`.

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.HomogeneousNorm
Build completed successfully (8816 jobs).
```

Lake replayed pre-existing linter warnings from imported modules
`FiniteHilbertBochner`, `RealSobolev`, `SpatiallyCompactTime`,
`RealPositiveDensity`, and `RealVectorPositiveDensity`; the new module itself
emitted no warning or error.

```text
$ lake env lean ../formalization/NSFormalization/Section4/D01/HomogeneousNorm.lean
<0 output; exit 0>
```

```text
$ scripts/gates.sh NSFormalization.Section4.D01.HomogeneousNorm
== make check
30 work items: ownership, contract registration and task cards consistent.
== lake build NSFormalization.Section4.D01.HomogeneousNorm
Build completed successfully (8816 jobs).
== make test
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
"base_compatibility_checked": true
== gates OK
```

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
"registered_contracts": 27
"base_compatibility_checked": true
<exit 0>
```

```text
$ lake env lean ../research/D01/axioms_g1.lean
'NSFormalization.Section4.D01.dotHomogeneousENorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.dotHomogeneousENorm_le_of_isHomogeneousSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.le_of_isHomogeneousSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.dotHomogeneousENorm_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.dotHomogeneousENorm_ne_top_of_isHomogeneousSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.dotHomogeneousENorm_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.dotHomogeneousENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedHomogeneousNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
```
