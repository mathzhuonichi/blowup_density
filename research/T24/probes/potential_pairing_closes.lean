import NSFormalization.Section3.T24.PotentialPairing

/-!
# T24c Uc2 probe — `potential_pairing` statement fidelity and non-vacuity

* Part 1 restates the `ConservativeForcingAPI.potential_pairing` field
  (`research/T24/Spec.lean:1391-1406`) over the canonical vocabulary and closes
  it with the shipped `potential_pairing`, witnessing that the shipped theorem
  has exactly the field's statement.
* Part 2 exhibits the nonzero smooth unit-periodic potential `φ = cos(2πx₁)`
  requested by the lane brief, proving `PeriodicPotentialT` at it and that it is a
  genuinely nonconstant potential, so the hypothesis class is non-degenerate.
* Part 3 evaluates the pairing conclusion at that potential and the zero
  ("from rest") velocity, showing the conclusion is a real `∫ = 0` identity.

`research/` is not a Lean root; run with
`cd verification && lake env lean ../research/T24/probes/potential_pairing_closes.lean`.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators RealInnerProductSpace

/-! ## Part 1 — statement fidelity. -/

example :
    ∀ (ν : ℝ) (T : ℝ), 0 < T → ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
      ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
        ∀ t ∈ Ico (0 : ℝ) T,
          ∫ y : PeriodicTorus,
              torusLift (fun x : Space ↦
                (inner ℝ (conservativeForceT φ (t, x)) (S.velocity (t, x)) : ℝ))
                y ∂periodicTorusMeasure = 0 :=
  potential_pairing

/-! ## Part 2 — a nonzero smooth periodic potential `φ = cos(2πx₁)`. -/

/-- `φ(z) = cos(2π x₁)`, the paper's canonical conservative potential. -/
def probePotential : SpaceTimeScalar := fun z ↦ Real.cos (2 * Real.pi * z.2 0)

theorem probePotential_contDiff : ContDiff ℝ ∞ probePotential := by
  have hproj : ContDiff ℝ ∞ (fun z : SpaceTime ↦ z.2 0) :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  exact Real.contDiff_cos.comp (contDiff_const.mul hproj)

theorem probePotential_periodic : IsPeriodicOn univ probePotential := by
  intro t _ x i
  show Real.cos (2 * Real.pi * (x + coordinateVector i) 0)
      = Real.cos (2 * Real.pi * x 0)
  -- The `i`-th unit shift changes the first coordinate by `1` when `i = 0`, else `0`.
  have hcoord : (coordinateVector i) 0 = (if (0 : Fin 3) = i then (1 : ℝ) else 0) := by
    simp [coordinateVector]
  have hc : (x + coordinateVector i) 0 = x 0 + (if (0 : Fin 3) = i then (1 : ℝ) else 0) := by
    rw [show (x + coordinateVector i) 0 = x 0 + (coordinateVector i) 0 from rfl, hcoord]
  rw [hc]
  split_ifs with h0
  · -- first coordinate shifted by the full period `2π`.
    rw [show 2 * Real.pi * (x 0 + 1) = 2 * Real.pi * x 0 + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  · -- no shift in the first coordinate.
    rw [add_zero]

theorem probePotential_isPeriodicPotential : PeriodicPotentialT probePotential :=
  ⟨probePotential_contDiff, probePotential_periodic⟩

/-- The potential is genuinely nonconstant: `φ(0)=1` while `φ` at a half-period
point in the first coordinate is `-1`.  Hence `-∇φ` is not identically zero and
the pairing statement is not degenerate. -/
theorem probePotential_nonconstant :
    probePotential (0, 0) ≠ probePotential (0, (1 / 2 : ℝ) • coordinateVector 0) := by
  have h0 : probePotential (0, 0) = 1 := by
    simp [probePotential]
  have h1 : probePotential (0, (1 / 2 : ℝ) • coordinateVector 0) = -1 := by
    have hx : ((1 / 2 : ℝ) • coordinateVector 0) 0 = 1 / 2 := by
      simp [coordinateVector]
    rw [probePotential]
    simp only [hx]
    rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.cos_pi]
  rw [h0, h1]
  norm_num

/-! ## Part 3 — the conclusion is a genuine `∫ = 0` at the from-rest velocity. -/

example (_ν t : ℝ) :
    ∫ y : PeriodicTorus,
        torusLift (fun x : Space ↦
          (inner ℝ (conservativeForceT probePotential (t, x))
            ((0 : SpaceTimeField) (t, x)) : ℝ))
          y ∂periodicTorusMeasure = 0 := by
  have hz : (fun x : Space ↦
      (inner ℝ (conservativeForceT probePotential (t, x))
        ((0 : SpaceTimeField) (t, x)) : ℝ)) = (fun _ : Space ↦ (0 : ℝ)) := by
    funext x; simp
  rw [hz, NSFormalization.Paper1.integral_torusLift]
  exact NavierStokes.PeriodicIntegration.cubeIntegral_zero

end NSFormalization.Section3.T24
