# Lane 310 report — T11/U3 Galilean classes

## 1. Theorems with exact statements

```lean
theorem translation_preserves_sobolev : ∀ (s : ℝ) (z : SpatialField),
    IsPeriodicSpatial z → ∀ y : Space,
      periodicSobolevENorm s (fun x ↦ z (x + y)) =
        periodicSobolevENorm s z
```

```lean
theorem transformed_classes : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (_w : ClassicalSolutionT ν a f T),
          meanZeroPartT a ∈ initialClassT ∧
            galileanForceT a f ∈ forceClassT
```

```lean
theorem transformed_mean_zero : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          meanT (meanZeroPartT a) = 0 ∧
            (∀ t ∈ Ico (0 : ℝ) T,
              meanT (fun x ↦ galileanVelocityT a f w.velocity (t, x)) = 0) ∧
            (∀ t ∈ Ico (0 : ℝ) T,
              meanT (fun x ↦ galileanForceT a f (t, x)) = 0)
```

The module also contains one explicitly named measure-invariance instance and
private supporting lemmas for Haar translation, datum isometries, smooth torus
means/primitives, compact time support, periodic derivative integrals, and the
solution mean evolution.

## 2. Files

- `formalization/NSFormalization/Section3/T11/GalileanClasses.lean` — all three
  canonical target theorems and their supporting proofs.
- `research/T11/probes/galilean_classes_closes.lean` — verbatim target closure
  checks plus a concrete nonzero stationary classical solution with admissible
  datum and compactly supported force.
- `research/T11/axioms_galilean_classes.lean` — guarded transitive-axiom audit
  for every exported declaration.
- `research/T11/ATTEMPTS_GALILEAN_CLASSES.md` — explored routes, exact errors,
  and peeling-input record.
- `research/T11/T11_SPLIT.md` — appended U3 completion status.

## 3. Gaps with error text

No proof gap and no named input.  The intermediate elaboration failures and
their exact messages are recorded in `ATTEMPTS_GALILEAN_CLASSES.md`; none remains
in the deliverables.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.GalileanClasses`
  — passed, 0 errors.
- `cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/GalileanClasses.lean`
  — passed, 0 errors.
- `cd verification && lake env lean ../research/T11/probes/galilean_classes_closes.lean`
  — passed, 0 errors.
- `cd verification && lake env lean ../research/T11/axioms_galilean_classes.lean`
  — passed; all four exported declarations print exactly
  `[propext, Classical.choice, Quot.sound]`.
- `make check` — passed.
