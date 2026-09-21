# Lane 191 report — A05 U4/U8 shifted critical data

## 1. Theorems and exact statements

The lane proves the physical `Λv` realization and the three derivative datum
columns required by R43.

```lean
def NSFormalization.Section4.A05.rieszLambda
    (v : SpatialField) (hv : A02.MemHInfty v) : SpatialField

theorem NSFormalization.Section4.A05.rieszLambda_memHInfty
    (v : SpatialField) (hv : A02.MemHInfty v) :
    A02.MemHInfty (rieszLambda v hv)

theorem NSFormalization.Section4.A05.rieszLambda_halfDatum
    (v : SpatialField) (hv : A02.MemHInfty v)
    (Z : RealVectorSobolev (3 / 2))
    (hZ : IsHomogeneousSliceDatum (3 / 2) v Z) :
    IsHomogeneousSliceDatum (1 / 2) (rieszLambda v hv) Z

def NSFormalization.Section4.A05.derivativeHalfDatum
    (j : Fin 3) (Z : RealVectorSobolev (3 / 2)) :
    RealVectorSobolev (1 / 2)

theorem NSFormalization.Section4.A05.derivativeHalfDatum_isDatum
    {v : SpatialField} (hv : A02.MemHInfty v)
    {Z : RealVectorSobolev (3 / 2)}
    (hZ : IsHomogeneousSliceDatum (3 / 2) v Z) (j : Fin 3) :
    IsHomogeneousSliceDatum (1 / 2) (dirDeriv j v)
      (derivativeHalfDatum j Z)

theorem NSFormalization.Section4.A05.derivativeHalfDatum_symbol
    (j i : Fin 3) (Z : RealVectorSobolev (3 / 2)) :
    ((((derivativeHalfDatum j Z) i : RealSobolevHilbert (1 / 2)) :
        FourierData) : Space → ℂ) =ᵐ[volume]
      fun ξ => R43.rieszCoordinateSymbol j ξ * (Z i : FourierData) ξ
```

The exact requested package is exported as:

```lean
def NSFormalization.Section4.A05.shiftedCriticalData_of_memHInfty
    (v : SpatialField) (hv : A02.MemHInfty v)
    (Z : RealVectorSobolev (3 / 2))
    (hZ : IsHomogeneousSliceDatum (3 / 2) v Z) :
    R43.ShiftedCriticalData v Z
```

The R43 slice wrapper is:

```lean
def NSFormalization.Section4.R43.criticalAdvectionLpBridge_shifted
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      ShiftedCriticalData (fun x => w.velocity (t, x))
        (hcrit.velocityThreeHalf t)
```

Lean requires the last two declarations to be `def`s: their codomains live in
`Type`, not `Prop`.  Their names and types are otherwise exactly the requested
interfaces.

The U4 construction is the literal real `L²` field
`-∑ j, R_j (∂_j v)`.  Its cycles-frequency multiplier is
`frequencyUnit * ‖ξ‖`; normalized angular dilation turns this into exactly
`‖ξ‖`.  Locally-integrable uniqueness then identifies the half-order datum
with `Z`.  U8 uses the exact R43 definition of `rieszCoordinateSymbol` and the
tree's distributional directional derivative formula.

## 2. Files

- `formalization/NSFormalization/Section4/A05/RieszShift.lean`: bounded Riesz
  transform, real physical realization, smooth-orbit closure, angular datum
  identity, derivative data, and `ShiftedCriticalData` package.
- `formalization/NSFormalization/Section4/R43/ShiftedData.lean`: interior-time
  classical velocity-slice wrapper.
- `research/A05/ATTEMPTS_U4_U8.md`: construction route, convention constants,
  discarded routes, diagnostics, and satisfiability explanation.
- `research/A05/axioms_u4_u8.lean`: every exported declaration is printed and
  has exactly `[propext, Classical.choice, Quot.sound]`; includes `v := 0`,
  `Z := 0` and a nonzero compact-Schwartz witness.
- `research/A05/COMPARISON.md`: U4/U8 status updated.
- `research/R43/R43_SPLIT.md`: S1b residual reduced to the one fractional
  Parseval identity.
- `research/A05/REPORT_191.md`: this report.

## 3. Gaps and diagnostics

There is no remaining U4/U8 carrier gap.  The `shifted` field of
`CriticalAdvectionLpBridge hcrit` is now constructed for every interior time.
The deliberately out-of-scope residual is its other field:

```lean
pairing_identity : ∀ t (ht : t ∈ Ioo (0 : ℝ) T),
  ⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫ =
    ∫ x, inner ℝ (advection ...) ((shifted t ht).lambda x)
```

That is the separate fractional Parseval/duality lemma specified by the lane.

The only interface diagnostic was produced by using the brief's requested
`theorem` syntax for a structure-valued constructor:

```text
error: type of theorem
`NSFormalization.Section4.A05.shiftedCriticalData_of_memHInfty`
is not a proposition
```

It is resolved by the required Lean form, `noncomputable def`.  No mathematical
hypothesis was added.  The anticipated special endpoint uniqueness theorem was
not needed: `D01.Homogeneous.homogeneousDatum_unique` already works at every
real order, including `3/2`.

For nonzero satisfiability, the audit uses
`v x = Cut.bump x • coordinateVector 0`.  This field is nonzero,
compact-smooth (hence componentwise Schwartz), is `MemHInfty` by standard jet
integrability, and has an order-`3/2` datum by the standard
`isHomogeneousSliceDatum_compact` theorem.  Thus every named input is a
restriction of a standard property.

## 4. Commands and results

All `lake` commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

```text
lake build NSFormalization.Section4.A05.RieszShift
lake build NSFormalization.Section4.R43.ShiftedData
```

Both exit `0`.  Lake replays warnings from pre-existing dependencies; neither
new target module emits a warning or error.

```text
lake env lean ../formalization/NSFormalization/Section4/A05/RieszShift.lean
lake env lean ../formalization/NSFormalization/Section4/R43/ShiftedData.lean
```

Both exit `0` with zero output.

```text
lake env lean ../research/A05/axioms_u4_u8.lean
```

Exit `0`.  Every printed declaration—including all helper definitions and the
two structure-valued constructors—reports exactly
`[propext, Classical.choice, Quot.sound]`; both satisfiability examples close.

```text
make check
```

Exit `0`; plan, contract architecture, policy tests, and work queue checks all
pass.

Static checks also find no `sorry`, `admit`, `axiom` declaration,
`native_decide`, or `set_option maxHeartbeats` in the new Lean files, and
`git diff --check` exits `0`.
