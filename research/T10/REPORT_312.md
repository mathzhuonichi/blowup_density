# Lane 312 — ForcePaths

## 1. Theorems with exact statements

All declarations are in `NSFormalization.Section3.T10`. The module proves
continuous (not coefficient-valued `ContDiff`) paths, which is the regularity
accepted in the lane goal. Paths represent **every real time**, including the
integrability conjunct, and have compact support. Finiteness holds for every
`q : ℝ≥0∞`, so in particular for `q = 1` and `q = 2`. There is no named input.
The energy identity only assumes smooth periodic **spatial slices** on `(0,T)`;
there is no time regularity or measurability hypothesis, and `T : ℝ` is arbitrary.

`periodicAngularFrequencySq k = 4 * Real.pi ^ 2 * ∑ i, (k i : ℝ) ^ 2`.
The gradient is the canonical T12 Frobenius tensor, and the energy quantities
are the canonical T10 definitions. Their equality is proved by constructing
actual homogeneous data, including their real symmetry and mean-zero condition.

```lean
theorem memForceT_iff_isTestForce (f : SpaceTimeField) :
    MemForceT f ↔ NSFormalization.Paper1.PeriodicForceSpace.IsTestForce f
```

```lean
theorem smooth_periodic_datum (s : ℝ) {v : SpatialField}
    (hs : ContDiff ℝ ∞ v) (hp : IsPeriodicSpatial v) :
    ∃ A : PeriodicSobolev s, IsPeriodicDatum s v A
```

```lean
theorem force_coefficient_path {f : SpaceTimeField} (hf : MemForceT f) (m : ℕ) :
    ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      (∀ t, IsPeriodicDatum (m : ℝ) (fun x ↦ f (t, x)) (G t)) ∧
      Continuous G ∧ HasCompactSupport G ∧ StronglyMeasurable G ∧
      IsPeriodicSobolevPath (m : ℝ) f G ∧
      (∀ q : ℝ≥0∞, MemLp G q forceTimeMeasure)
```

```lean
theorem forceSobolevENormT_ne_top {f : SpaceTimeField} (hf : MemForceT f)
    (m : ℕ) (q : ℝ≥0∞) : forceSobolevENormT q (m : ℝ) f ≠ ⊤
```

```lean
theorem gradientTensor_parseval {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ ∞ v) :
    eLpNorm (torusLift (NSFormalization.Section3.T12.gradientTensor v)) 2 periodicTorusMeasure =
      ENNReal.ofReal (Real.sqrt (∑' k, periodicAngularFrequencySq k *
        ∑ i : Fin 3, ‖periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k‖ ^ 2))
```

```lean
theorem gradient_eq_homogeneousENorm {v : SpatialField}
    (hs : ContDiff ℝ ∞ v) (hp : IsPeriodicSpatial v) :
    eLpNorm (torusLift (NSFormalization.Section3.T12.gradientTensor v)) 2 periodicTorusMeasure =
      periodicHomogeneousENorm 1 (meanZeroPartT v)
```

```lean
theorem energyENormT_eq (T : ℝ) (z : SpaceTimeField)
    (hs : ∀ t ∈ Ioo (0 : ℝ) T, ContDiff ℝ ∞ (fun x ↦ z (t, x)))
    (hp : IsPeriodicOn (Ioo (0 : ℝ) T) z) :
    energyENormT T z = coefficientEnergyENormT T z
```

```lean
theorem periodicFourierCoeff_component_derivative {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ 1 v) (i j : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (spatialPartial j (fun x ↦ (v x i : ℂ))) k =
      periodicDerivativeSymbol j k * periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k
```

```lean
theorem periodicFourierCoeff_component_decay {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ ∞ v) (i : Fin 3) (N : ℕ) :
    ∃ C : ℝ, ∀ k, periodicFrequencyWeight k ^ N *
      ‖periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k‖ ≤ C
```

```lean
theorem periodicFourierCoeff_component_laplacian {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ 2 v) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ∑ j : Fin 3,
      spatialPartial j (spatialPartial j (fun y ↦ (v y i : ℂ))) x) k =
      (-periodicAngularFrequencySq k : ℂ) * periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k
```

```lean
theorem periodicFourierCoeff_vector_gradient_sq {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ 1 v) (k : PeriodicFrequency) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ‖periodicFourierCoeff (spatialPartial j (fun x ↦ (v x i : ℂ))) k‖ ^ 2) =
      periodicAngularFrequencySq k * ∑ i : Fin 3,
        ‖periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k‖ ^ 2
```

```lean
theorem periodicFourierCoeff_gradientTensor {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ 1 v) (i j : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ (NSFormalization.Section3.T12.gradientTensor v x j i : ℂ)) k =
      periodicDerivativeSymbol j k * periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k
```

```lean
theorem periodicFourierCoeff_vector_laplacian {v : SpatialField}
    (hp : IsPeriodicSpatial v) (hs : ContDiff ℝ ∞ v) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ (NSFormalization.Section3.T12.laplacian v x i : ℂ)) k =
      (-periodicAngularFrequencySq k : ℂ) * periodicFourierCoeff (fun x ↦ (v x i : ℂ)) k
```

The other exported lemmas provide vector torus `MemLp`, datum subtraction and
uniqueness of its norm, coefficient path continuity, scalar component integer
energy, tensor entry identification, angular summability, construction and
norm of homogeneous data, zero-mode invariance, the order-zero physical norm,
and a separated smooth-profile constructor for concrete forces. Every one of
the 29 declarations has a `#check` conformance line and an axiom audit.

## 2. Files

- `formalization/NSFormalization/Section3/T10/ForcePaths.lean`: 29 proved theorems.
- `research/T10/probes/force_paths_examples.lean`: zero force and a nonzero
  cosine mode times a smooth bump centered at time 2, supported in `[3/2,5/2]`.
  Proves force membership, nonzero value at `(2,0)`, nonzero spatial frequency,
  path existence, both finite norms, and the energy identity.
- `research/T10/axioms_force_paths.lean`: conformance and axiom audit for all 29.
- `research/T10/ATTEMPTS_FORCE_PATHS.md`: attempted routes and exact error excerpts.
- `research/T10/REPORT_312.md`: this report.
- `research/T10/COMPARISON.md`: requested “Registered/proved by lane 312” notes
  under items 11 and 12; the only existing file edited.

No existing Lean module, contract, registry, or shared status file was edited.
No instances or heartbeat overrides were added.

## 3. Gaps and error text

No unresolved Lean errors and no named mathematical inputs. All numbered
module goals are proved with continuous coefficient paths. Higher time
regularity (`ContDiff ℝ ∞ G`) is not asserted. The additional inhomogeneous
intersection sum-norm comparison in the broader COMPARISON item 12 is separate
from the physical/coefficient identities requested under Goal 2 and remains
unclaimed; the comparison notes explicitly preserve this distinction.

Resolved errors, including the accidental complex-module instance search on
the real coefficient submodule, are recorded verbatim in ATTEMPTS. The final
module and probe elaborate with **zero output**.

## 4. Commands and results

All Lean commands source `. scripts/lean-env.sh`, run from `verification/`,
and set `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T10.ForcePaths`: exit 0;
  `Build completed successfully (9945 jobs).` Existing dependency warnings
  were replayed; the new module has no warnings.
- `lake env lean ../formalization/NSFormalization/Section3/T10/ForcePaths.lean`:
  exit 0, zero output.
- `lake env lean ../research/T10/probes/force_paths_examples.lean`:
  exit 0, zero output.
- `lake env lean ../research/T10/axioms_force_paths.lean`: exit 0.
  All **29** theorem axiom sets are exactly
  `[propext, Classical.choice, Quot.sound]`, also checked programmatically.
- Root `make check`: exit 0; 13 contract-policy tests pass and 45 work items
  are consistent. The pre-existing copied-source audit reports 11 explicit
  axiom/admission tokens outside this lane; none is introduced here.
- `lake test` from `verification/` (the root `make test` target's test action):
  exit 0, registered contract tests pass.
- Root `LEAN_NUM_THREADS=6 make test-mutations`: exit 0; implementation
  refactor accepted, all three negative mutations rejected as required.
- `git diff --check`: exit 0.

No push, merge, or rebase. Commit title: `[312-T10] ForcePaths`.
