# Lane 309 — T11 U2

## 1. Theorems: exact statements

Namespace `NSFormalization.Section3.T11`; U2 supplies bridge lemmas, not the PDE continuation API fields. Time measurability is restricted to the solution interval, outside which the velocity is unconstrained.

```lean
theorem periodicSobolevENorm_eq_datum {s : ℝ} {z : SpatialField}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s z A) :
    periodicSobolevENorm s z = ‖A‖ₑ

theorem exists_periodicDatum_smooth (s : ℝ) {z : SpatialField}
    (hs : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    ∃ A : PeriodicSobolev s, IsPeriodicDatum s z A

theorem periodicSobolevENorm_ne_top_smooth (s : ℝ) {z : SpatialField}
    (hs : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    periodicSobolevENorm s z ≠ ⊤

theorem norm_periodicDatum {s : ℝ} {u : SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A) :
    ‖A‖ = periodicVectorSobolevNorm s u t

theorem periodicSobolevENorm_eq_of_datum {s : ℝ} {u : SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A) :
    periodicSobolevENorm s (fun x ↦ u (t, x)) =
      ENNReal.ofReal (periodicVectorSobolevNorm s u t)

theorem periodicSobolevENorm_eq_smooth (s : ℝ) (u : SpaceTimeField) (t : ℝ)
    (hs : ContDiff ℝ ∞ (fun x ↦ u (t, x)))
    (hp : IsPeriodicSpatial (fun x ↦ u (t, x))) :
    periodicSobolevENorm s (fun x ↦ u (t, x)) =
      ENNReal.ofReal (periodicVectorSobolevNorm s u t)

theorem continuousOn_periodicSobolevENorm {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) (m : ℕ) :
    ContinuousOn (fun t ↦ periodicSobolevENorm (m : ℝ) (fun x ↦ w.velocity (t, x)))
      (Ico (0 : ℝ) T)

theorem aemeasurable_periodicSobolevENorm {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) :
    AEMeasurable (fun t ↦ periodicSobolevENorm 2 (fun x ↦ w.velocity (t, x)))
      (volume.restrict (Ioo (0 : ℝ) T))

theorem continuousOn_h2SquaredProfile {ν S : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f S) :
    ContinuousOn (h2SquaredProfile (toFlow w)) (Ico (0 : ℝ) S)

theorem squaredHTwoIntegralT_ne_top_iff_finiteH2Energy
    {ν S : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f S) :
    squaredHTwoIntegralT S w.velocity ≠ ⊤ ↔ FiniteH2Energy (toFlow w)

```

## 2. Files

- `formalization/NSFormalization/Section3/T11/CriterionBridge.lean`: ten theorems and arbitrary-constant non-vacuity example.
- `research/T11/probes/criterion_bridge_closes.lean`: exact statement probes for all ten theorems and non-vacuity at `coordinateVector 0`.
- `research/T11/axioms_criterion_bridge.lean`: all ten declarations print exactly `[propext, Classical.choice, Quot.sound]`.
- `research/T11/ATTEMPTS_CRITERION_BRIDGE.md`: proof routes and resolved errors.
- `research/T11/T11_SPLIT.md`: one added U2 status line. No existing Lean module changed.

## 3. Gaps and errors

No residual gap or named input. Resolved elaboration errors are recorded in ATTEMPTS. No instances or heartbeat overrides added. Canonical `datum_unique` is the implementation bound to registered `T01.torus_data` (`verification/Bindings/TorusData.lean:149`). Norm identification holds for every datum using `lp.norm_eq_tsum_rpow` and `norm_periodicWeightedCoeff_sq`, strengthening the smooth-only route through `norm_smoothPeriodicWeightedFourierLp`. The predicate imported through `PeriodicFiniteH2Bridge` is unfolded to its exact integrability definition, with endpoints handled by `restrict_Ioo_eq_restrict_Ioc`.

## 4. Commands and results

Lean commands source `scripts/lean-env.sh`, run from `verification/`, with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T11.CriterionBridge`: PASS, 9967 jobs, zero errors; existing dependency warnings only.
- `lake env lean ../formalization/NSFormalization/Section3/T11/CriterionBridge.lean`: PASS, no diagnostics.
- `lake env lean ../research/T11/probes/criterion_bridge_closes.lean`: PASS, no diagnostics.
- `lake env lean ../research/T11/axioms_criterion_bridge.lean`: PASS, all ten exact standard-three axiom sets.
- `make check` from root: PASS (13 policy tests; 45 work items consistent).
- `lake test` from verification: PASS, 10743 targets; registered contract audits pass.
- `make test-mutations` from root: PASS; implementation refactor accepted, three invalid mutations rejected.
