import NSFormalization.Section4.A01.ConvectionDivergence
import NSFormalization.Section4.A01.RadialPotential
import NSFormalization.Section4.A01.PressureGauge

noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open NSFormalization.Section4.A01.RadialPotential
open NSFormalization.Section4.A01.PressureGauge
open NSFormalization.Section4.A02 (PressureGaugeEquivOn)
open scoped ContDiff RealInnerProductSpace

-- NV1: HasSymmetricJacobian is inhabited by the identity (Jacobian = id, symmetric)
example : HasSymmetricJacobian (fun x : Space => x) := by
  refine ⟨differentiable_id, ?_⟩
  intro x i j
  simp only [fderiv_fun_id]
  simp [coordinateVector, eq_comm]

-- NV2: the (HasSymmetricJacobian ∧ ContDiff ∞) bundle of radialPotential is inhabited
example : HasSymmetricJacobian (fun x : Space => x) ∧ ContDiff ℝ ∞ (fun x : Space => x) := by
  refine ⟨⟨differentiable_id, ?_⟩, contDiff_id⟩
  intro x i j
  simp only [fderiv_fun_id]
  simp [coordinateVector, eq_comm]

-- NV3: ContDiffOn ℝ ∞ p (slab) — hyp of hasSymmetricJacobian_pressureGradient — inhabited (p = 0)
example (T : ℝ) : ContDiffOn ℝ ∞ (fun _ : SpaceTime => (0:ℝ))
    (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := contDiffOn_const

-- NV4: pressure_potential_of_pointwise's three hyps are inhabited (p = 0), via the lane's own
-- lemmas, producing a concrete PressureGaugeEquivOn.  Also exercises hasSymmetricJacobian_pressureGradient
-- and contDiff_gradSlice non-vacuously with a concrete smooth pressure.
example (T : ℝ) :
    PressureGaugeEquivOn (Ico (0:ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient (fun _ => (0:ℝ)) z.1 z.2))
      (fun _ => 0) :=
  pressure_potential_of_pointwise (fun _ => 0)
    (fun t ht => hasSymmetricJacobian_pressureGradient (T := T) contDiffOn_const ht)
    (fun t ht => contDiff_gradSlice (T := T) contDiffOn_const ht)
    (fun t ht => (NSFormalization.Section4.D01.contDiff_slice_scalar (T := T) contDiffOn_const ht).differentiable (by simp))

-- NV5: navierStokesResidual_eq_iff_projected's hyps inhabited (zero velocity field)
example (t : ℝ) (x : Space) :
    DifferentiableAt ℝ (fun y : Space => (fun _ : SpaceTime => (0:Space)) (t, y)) x ∧
    spatialDivergence (fun _ : SpaceTime => (0:Space)) t x = 0 := by
  refine ⟨differentiableAt_const 0, ?_⟩
  simp [spatialDivergence, spatialDerivative, fderiv_fun_const]

end
