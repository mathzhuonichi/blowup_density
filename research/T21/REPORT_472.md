# Lane 472 report: T21 N0--N10 and N12

## 1. Theorems proved, with exact statements

The canonical namespace is `NSFormalization.Section3.T21`.  The nine field
endpoints have the following types (with `K : CriticalRegularityTAPI` and
`c : ℝ` as displayed by their declarations):

```lean
theorem criticalGlobalRegularity
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν →
      ∀ g : SpaceTimeField, g ∈ forceClassT →
        forceSobolevENormT 1 (1 / 2) g < ENNReal.ofReal (K.c * ν) →
          maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤

theorem zeroMemBall (c : ℝ) (hc : 0 < c) : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    (0 : SpaceTimeField) ∈ criticalBallT c ν s

theorem ballRelativelyOpen (c : ℝ) : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    ∀ g ∈ criticalBallT c ν s,
      ∃ r : ℝ≥0∞, 0 < r ∧
        ∀ f ∈ forceClassT, forceSobolevENormT 1 s (f - g) < r →
          f ∈ criticalBallT c ν s

theorem sliceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ z : SpatialField,
    periodicSobolevENorm (1 / 2) z ≤ periodicSobolevENorm s z

theorem forceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ f : SpaceTimeField,
    forceSobolevENormT 1 (1 / 2) f ≤ forceSobolevENormT 1 s f

theorem criticalBallDisjoint
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Disjoint (criticalBallT K.c ν (1 / 2)) (breakdownSetTZero ν T)

theorem ballDisjoint
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ, 1 / 2 ≤ s →
      Disjoint (criticalBallT K.c ν s) (breakdownSetTZero ν T)

theorem nonDensity
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)
```

The supporting N1/N4/N5/N12 endpoints are:

```lean
theorem reweightContraction (s t : ℝ) (hst : s ≤ t)
    (A : PeriodicSobolev t) (B : PeriodicSobolev s)
    (hAB : IsPeriodicReweight t s A B) : ‖B‖ ≤ ‖A‖

theorem exists_orderLoweringDatum (s t : ℝ) (hst : s ≤ t)
    (z : SpatialField) (A : PeriodicSobolev t) (hA : IsPeriodicDatum t z A) :
    ∃ B : PeriodicSobolev s,
      IsPeriodicReweight t s A B ∧ IsPeriodicDatum s z B ∧ ‖B‖ ≤ ‖A‖

theorem zero_mem_forceClassT : (0 : SpaceTimeField) ∈ forceClassT

theorem forceSobolevENormT_zero (q : ℝ≥0∞) (s : ℝ) :
    forceSobolevENormT q s (0 : SpaceTimeField) = 0

theorem zeroInitialClass : (fun _ : Space ↦ 0) ∈ initialClassT
```

N6 is reused, not reproved:
`NSFormalization.Section3.T18.forceSobolevENormT_add_le`.  The final canonical
inhabitant is:

```lean
def nonDensityAPI
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    NonDensityAPI K.c
```

## 2. Files delivered

- `formalization/NSFormalization/Section3/T21/Definitions.lean`
- `formalization/NSFormalization/Section3/T21/CriticalBridge.lean`
- `formalization/NSFormalization/Section3/T21/OrderLowering.lean`
- `formalization/NSFormalization/Section3/T21/ForceMonotonicity.lean`
- `formalization/NSFormalization/Section3/T21/Zero.lean`
- `formalization/NSFormalization/Section3/T21/Ball.lean`
- `formalization/NSFormalization/Section3/T21/Disjointness.lean`
- `formalization/NSFormalization/Section3/T21/NonDensity.lean`
- `formalization/NSFormalization/Section3/T21/Assembly.lean`
- `research/T21/probes/nondensity_closes.lean`
- `research/T21/axioms_n0_n12.lean`
- `research/T21/ATTEMPTS_N0_N12.md`
- status update in `research/T21/T21_SPLIT.md`
- this report

The probe copies the reconciled registered record shape, closes every field by
`exact`, and instantiates `BlowupDensity.T21.nonDensityOfCritical`.  It uses
`Bindings.TorusLocalTheory.maximalLifespanT_eq` and `breakdownSetT_eq` exactly
at the two solution-structure seams.

## 3. Gaps and failed approaches

There are no residual mathematical or Lean goals in N0--N10 or N12.
Registration remains deliberately outside this lane.

One resolved elaboration failure is recorded in
`ATTEMPTS_N0_N12.md`.  Exact error text:

```text
error: NSFormalization/Section3/T21/Ball.lean:37:2: Type mismatch: After simplification, term
  T18.memForceT_add hf (memForceT_neg hg)
 has type
  MemForceT fun z => f z + -g z
but is expected to have type
  MemForceT (f + -g)
```

The fix was an explicit eta-expanded `change` before using the existing T18
addition theorem; no new premise or placeholder was introduced.

## 4. Commands and results

- Dependency closure:
  `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.Assembly NSFormalization.Section3.T19.Bookkeeping NSFormalization.Section3.T18.SobolevRate NSFormalization.Section3.T15.Convergence`
  — success, 10,689 jobs.
- All nine new canonical modules built together with
  `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T21.{Definitions,CriticalBridge,OrderLowering,ForceMonotonicity,Zero,Ball,Disjointness,NonDensity,Assembly}`
  — success after the single recorded eta-expansion fix.
- `lake env lean` on each new canonical module — success, zero output.
- `lake env lean ../research/T21/Spec.lean` — success, zero output.
- `lake env lean ../research/T21/probes/nondensity_closes.lean` — success,
  zero output.
- `lake env lean ../research/T21/axioms_n0_n12.lean` — success; every printed
  declaration reports exactly `[propext, Classical.choice, Quot.sound]`.
- `git diff --check` and forbidden-token/max-heartbeat scans — clean.
- `make check` — success (architecture checks, contract-policy tests, and
  work-queue consistency all passed).
