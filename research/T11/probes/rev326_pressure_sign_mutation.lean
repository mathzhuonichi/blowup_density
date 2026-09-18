import NSFormalization.Section3.T11.MildPressure

/-! Reviewer mutation: changing the Poisson equation's nonlinear sign from
subtraction to addition must not be accepted by the delivered proof. -/
noncomputable section

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10 NSFormalization.Section3.T11
open scoped ContDiff

variable {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3} {T : ℝ}

example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      scalarSpatialLaplacianT (mildPressure g u) t x =
        spatialDivergence g t x +
          spatialDivergence (fun z : SpaceTime ↦
            convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2) t x := by
  exact mildPressure_poisson hg hgp hu
