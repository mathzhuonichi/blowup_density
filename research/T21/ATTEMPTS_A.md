# T21 unit A — assembly and registration notes

## Successful route

The canonical final module imports lane 472's `Assembly.lean`, lane 474's
`Main.lean`, and the closed T20 assembly.  It uses
`criticalRegularityT` (whose `c` reduces to `criticalSmallnessH1`) and
`T19.periodicDensityAPI`.  The density/non-density adapter is exactly

```lean
fun _c D (N : NonDensityAPI _c) =>
  mainOfDensityAndNonDensity_holds D N.nonDensity
```

and the two-input arrow supplies `nonDensityAPI K` first.  The closed records
are therefore genuinely indexed by the selected T20 constant, while the
witness-independent claim remains only
`∃ c, Nonempty (NonDensityAPI c)`.

The registered non-density binding does not copy or convert all 23 fields of
an arbitrary registered T20 record.  It consumes `K.hc` and
`K.globalRegularity` directly, reuses the canonical order/openness lemmas, and
repeats the short disjointness/density contradiction in registered vocabulary.
The registered `breakdownSetTZero` drift guard uses
`Bindings.TorusLocalTheory.breakdownSetT_eq`; this is the same approved
lifespan seam as T20, not an `rfl` bridge.

## Parallel-lane duplicate resolved

Lane 474's `Main.lean` and lane 472's `Zero.lean` both declared
`NSFormalization.Section3.T21.zeroInitialClass`.  As authorized by the lead
note, `Main.lean` now imports `T21.Zero` and its duplicate theorem was deleted.
No N11/N13--N15 statement or proof was changed.

Lane 474 had already used the root name
`mainOfDensityAndNonDensity_holds` for its field-level helper.  Lean cannot
redeclare that name for the later arrow proposition.  The canonical arrow
inhabitant is consequently named
`mainOfDensityAndNonDensity_arrow_holds`, and its body is the required adapter
above.  The registered binding, where no collision exists, uses the exact
name `mainOfDensityAndNonDensity_holds`.  The other two canonical endpoints
retain the requested names `nonDensityOfCritical_holds` and
`mainOfInputs_holds`.

## Checks during development

The initial lane-472/474 closure built before edits.  The first targeted build
of `MainAssembly`, both contract modules, both bindings, and both tests passed
without an elaboration error.  The probe then closed
`zeroInitialNonDensity` at `ν = T = s = 1` and `fixedInitialDensity` at the zero
datum with `ν = T = 1`, `s = 0`.  Every declaration listed in `axioms_a.lean`
prints exactly `[propext, Classical.choice, Quot.sound]`.
