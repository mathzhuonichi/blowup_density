# Report 308 — T11 U1 flow conversion

## 1. Theorems and definitions proved

All declarations below are in `NSFormalization.Section3.T11`.

```lean
theorem source_residual_eq_navierStokesResidual
    (ν : ℝ) (u : SpaceTimeField) (p : SpaceTimeScalar) (t : ℝ) (x : Space) :
    Source.residual ν u p t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x

theorem isPeriodicOn_iff_unitSpatialPeriodsOn
    {E : Type*} (I : Set ℝ) (z : SpaceTime → E) :
    IsPeriodicOn I z ↔ UnitSpatialPeriodsOn I z

def toFlow {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    Paper1.PeriodicLifespan.Flow ν a f T

def ofFlow {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (U : Paper1.PeriodicLifespan.Flow ν a f T)
    (hs : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) T) ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          IsPeriodicDatum (m : ℝ) (fun x ↦ U.velocity (t, x)) (G t))
    (hg : ∀ t ∈ Ico (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ pressureGradient U.pressure t x)) 2
        periodicTorusMeasure)
    (hn : PressureGaugeT (Ico (0 : ℝ) T) U.pressure) :
    ClassicalSolutionT ν a f T

theorem toFlow_ofFlow (U : Paper1.PeriodicLifespan.Flow ν a f T) (hs hg hn) :
    toFlow (ofFlow U hs hg hn) = U

theorem ofFlow_toFlow (w : ClassicalSolutionT ν a f T) :
    ofFlow (toFlow w) w.sobolev w.pressure_gradient w.pressure_gauge = w

theorem memForceT_to_isSmoothPeriodicForce {f : SpaceTimeField}
    (hf : MemForceT f) :
    Paper1.PeriodicLocalLifespan.IsSmoothPeriodicForce f
```

The module also exports the four definitional data-field simp lemmas
`toFlow_velocity`, `toFlow_pressure`, `ofFlow_velocity`, and
`ofFlow_pressure`; each states equality with the corresponding source field
and is proved by `rfl`.

## 2. Files

- `formalization/NSFormalization/Section3/T11/FlowConversion.lean` — canonical
  spelling bridges, conversions, round trips, and force transport.
- `research/T11/probes/flow_conversion_roundtrip.lean` — verbatim target-shape
  checks plus a concrete zero-force non-vacuity example.
- `research/T11/axioms_flow_conversion.lean` — every exported declaration is
  audited and prints exactly `[propext, Classical.choice, Quot.sound]`.
- `research/T11/ATTEMPTS_FLOW_CONVERSION.md` — explored paths and scope record.
- `research/T11/T11_SPLIT.md` — one-line U1 completion status appended.

## 3. Gaps

No proof gap and no named input.  No target produced an error.  The lifespan
equality is intentionally not part of U1: the binding split assigns it to U15,
where the three fields absent from `Flow` can be supplied for every horizon.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.FlowConversion`
  — passed, 0 errors.
- `cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/FlowConversion.lean`
  — passed, 0 errors.
- `cd verification && lake env lean ../research/T11/probes/flow_conversion_roundtrip.lean`
  — passed, 0 errors.
- `cd verification && lake env lean ../research/T11/axioms_flow_conversion.lean`
  — passed; every declaration printed exactly the permitted three axioms.
- `make check` — passed (plan, contract-policy, contract-closure, and work-queue checks all green).
