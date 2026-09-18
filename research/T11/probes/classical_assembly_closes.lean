import NSFormalization.Section3.T11.ClassicalAssembly

/-! Partial delivery probe: the general U9d existential target does NOT close.
This file checks the exact delivered fields and the full nonzero constant-family
witness. See REPORT_320.md for the unchanged general target and remaining work.
-/
noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10 NSFormalization.Section3.T11
open scoped ContDiff

example {T : ℝ} {u : ℝ → PeriodicSobolev 3} (h : PersistenceInput T u) :
    ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) T) ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          IsPeriodicDatum (m : ℝ) (fun x ↦ torusPhysicalVelocity u (t, x)) (G t) :=
  persistence_physical_sobolev h

example {T : ℝ} {u : ℝ → PeriodicSobolev 3} (h : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    ContDiff ℝ ∞ (fun x ↦ torusPhysicalVelocity u (t, x)) :=
  persistence_physical_spatial_smooth h ht

example {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {a : SpatialField} {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
    (ha : a ∈ initialClassT) (hA : IsPeriodicDatum 3 a A)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) (hp : PersistenceInput T u) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDivergence (torusPhysicalVelocity u) t x = 0 :=
  persistence_mild_physical_divergence ha hA hP hu hp

-- The exact `projected` field, discharged for an existing classical solution.
example {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      temporalDerivative w.velocity t x - ν • spatialLaplacian w.velocity t x =
        (f (t, x) - convectionDivergenceT w.velocity t x) -
          pressureGradient w.pressure t x := classicalSolutionT_projected w

-- Actual mild semantics, persistence, full recovery, and nonzero velocity AND force.
example :
    ∃ C : TorusTwoSpaceContract 1,
      let c := coordinateVector 0
      let u := fun t : ℝ ↦ (1+t) • torusConstantDatum 3 c
      PersistenceInput 1 u ∧
      TorusForcedMildOn C (torusConstantDatum 3 c)
        (fun _ ↦ torusConstantDatum 3 c) 1 u ∧
      (∃ w : ClassicalSolutionT 1 (fun _ ↦ c) (fun _ ↦ c) 1,
        PeriodicLocalRegularity 1 (fun _ ↦ c) (fun _ ↦ c) 1 w ∧
        IsPeriodicSobolevPathOn 3 (Ico 0 1) w.velocity u) ∧
      torusPhysicalVelocity u (0, 0) ≠ 0 ∧ c ≠ 0 := classicalAssembly_nonzero
