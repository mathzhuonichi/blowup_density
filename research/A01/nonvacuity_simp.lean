import NSFormalization.Section4.A01.ConvectionDivergence
import NSFormalization.Section4.A01.RadialPotential
import NSFormalization.Section4.A01.PressureGauge

/-!
# A01 non-vacuity checks (lane 113 SIMP/tester)

One `example` per hypothesis-heavy A01 export, showing the hypothesis class is
inhabited (so the theorem is not vacuously about an empty class).  This file
must elaborate **silently** (exit 0, no errors, no warnings).

`ClassicalSolutionR` (the hypothesis of `projected_of_classicalSolution` and
`pressure_potential_of_classicalSolution`) is deliberately NOT inhabited here:
its `sobolev`/`pressure_gradient` fields make inhabitation an A02-level
construction, out of this SIMP lane's scope.  Its non-vacuity is A02's concern;
here NV4/NV5 instead inhabit the *pointwise engines* those two theorems reduce
to (`pressure_potential_of_pointwise`, `navierStokesResidual_eq_iff_projected`).
-/

noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open NSFormalization.Section4.A01.RadialPotential
open NSFormalization.Section4.A01.PressureGauge
open NSFormalization.Section4.A02 (PressureGaugeEquivOn)
open scoped ContDiff RealInnerProductSpace

-- NV1: `HasSymmetricJacobian` is inhabited by the identity field (Jacobian = id, symmetric).
example : HasSymmetricJacobian (fun x : Space => x) := by
  refine ⟨differentiable_id, ?_⟩
  intro x i j
  simp only [fderiv_fun_id]
  simp [coordinateVector, eq_comm]

-- NV2: the `HasSymmetricJacobian G ∧ ContDiff ℝ ∞ G` hypothesis bundle of
-- `hasFDerivAt_radialPotential` / `pressureGradient_pressurePotential` is inhabited (G = id).
example : HasSymmetricJacobian (fun x : Space => x) ∧ ContDiff ℝ ∞ (fun x : Space => x) := by
  refine ⟨⟨differentiable_id, ?_⟩, contDiff_id⟩
  intro x i j
  simp only [fderiv_fun_id]
  simp [coordinateVector, eq_comm]

-- NV3: `ContDiffOn ℝ ∞ p (slab)`, the hypothesis of `hasSymmetricJacobian_pressureGradient`
-- and `contDiff_gradSlice`, is inhabited by the zero pressure.
example (T : ℝ) : ContDiffOn ℝ ∞ (fun _ : SpaceTime => (0:ℝ))
    (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := contDiffOn_const

-- NV4: the three per-time hypotheses of `pressure_potential_of_pointwise` are jointly
-- inhabited (zero pressure), via the lane's own lemmas — this simultaneously exercises
-- `hasSymmetricJacobian_pressureGradient` and `contDiff_gradSlice` on a concrete smooth
-- pressure and produces a concrete `PressureGaugeEquivOn`.
example (T : ℝ) :
    PressureGaugeEquivOn (Ico (0:ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient (fun _ => (0:ℝ)) z.1 z.2))
      (fun _ => 0) :=
  pressure_potential_of_pointwise (fun _ => 0)
    (fun t ht => hasSymmetricJacobian_pressureGradient (T := T) contDiffOn_const ht)
    (fun t ht => contDiff_gradSlice (T := T) contDiffOn_const ht)
    (fun t ht => (NSFormalization.Section4.D01.contDiff_slice_scalar (T := T) contDiffOn_const ht).differentiable (by simp))

-- NV5: the hypotheses of `navierStokesResidual_eq_iff_projected` (spatial differentiability
-- and divergence-freeness) are inhabited by the zero velocity field.
example (t : ℝ) (x : Space) :
    DifferentiableAt ℝ (fun y : Space => (fun _ : SpaceTime => (0:Space)) (t, y)) x ∧
    spatialDivergence (fun _ : SpaceTime => (0:Space)) t x = 0 := by
  refine ⟨differentiableAt_const 0, ?_⟩
  simp [spatialDivergence, spatialDerivative, fderiv_fun_const]

-- NV6 (REVIEW_SIMP.md F5): a NON-degenerate witness `P(t,y) = y₀y₁`, for which `∇P(t,·) ≠ 0`,
-- so the Clairaut content of `hasSymmetricJacobian_pressureGradient` is genuinely exercised
-- (NV1..NV4 above use only the identity / zero fields, whose ∇ is trivial).  Reviewer's §6.4.
namespace Rev113.NonVac
open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01.RadialPotential
open NSFormalization.Section4.A01.PressureGauge
open scoped ContDiff RealInnerProductSpace

/-- Coordinate projection with its type pinned (otherwise `𝕜` stays a metavariable). -/
def pr (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj i

theorem pr_apply (i : Fin 3) (y : Space) : pr i y = y i := rfl

/-- `p(t,y) = y₀ y₁`. -/
def P : PressureField := fun z => z.2 0 * z.2 1

theorem P_slice (t : ℝ) : (fun y : Space => P (t, y)) = fun y : Space => (y 0 : ℝ) * y 1 := rfl

theorem P_contDiff : ContDiff ℝ ∞ (fun z : SpaceTime => P z) := by
  have h0 : ContDiff ℝ ∞ (fun z : SpaceTime => (z.2 0 : ℝ)) :=
    (pr 0).contDiff.comp contDiff_snd
  have h1 : ContDiff ℝ ∞ (fun z : SpaceTime => (z.2 1 : ℝ)) :=
    (pr 1).contDiff.comp contDiff_snd
  exact h0.mul h1

theorem P_contDiffOn (T : ℝ) :
    ContDiffOn ℝ ∞ P (Ico (0:ℝ) T ×ˢ (univ : Set Space)) := P_contDiff.contDiffOn

/-- The gradient really is nonzero: `(∇P(t,·))₀ (e₁) = 1`. -/
theorem P_grad_ne_zero (t : ℝ) : pressureGradient P t (coordinateVector 1) ≠ 0 := by
  intro h
  have h0 : pressureGradient P t (coordinateVector (1 : Fin 3)) 0 = (0 : Space) 0 := by rw [h]
  rw [pressureGradient_apply] at h0
  have hp0 : HasFDerivAt (fun y : Space => (y 0 : ℝ)) (pr 0)
      (coordinateVector 1) := (pr 0).hasFDerivAt
  have hp1 : HasFDerivAt (fun y : Space => (y 1 : ℝ)) (pr 1)
      (coordinateVector 1) := (pr 1).hasFDerivAt
  have hd : HasFDerivAt (fun y : Space => (y 0 : ℝ) * y 1)
      ((coordinateVector (1 : Fin 3) : Space) 0 • (pr 1)
        + (coordinateVector (1 : Fin 3) : Space) 1 • (pr 0))
      (coordinateVector 1) := hp0.mul hp1
  rw [P_slice, hd.fderiv] at h0
  simp [pr, coordinateVector] at h0

/-- The Clairaut output is about a genuinely non-constant gradient field. -/
theorem P_symm_jac (T : ℝ) {t : ℝ} (ht : t ∈ Ico (0:ℝ) T) :
    HasSymmetricJacobian (fun x : Space => pressureGradient P t x)
      ∧ pressureGradient P t (coordinateVector 1) ≠ 0 :=
  ⟨hasSymmetricJacobian_pressureGradient (P_contDiffOn T) ht, P_grad_ne_zero t⟩

/-- A non-degenerate instance of the m4 conclusion. -/
theorem P_gauge (T : ℝ) :
    NSFormalization.Section4.A02.PressureGaugeEquivOn (Ico (0:ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient P z.1 z.2)) P :=
  pressure_potential_of_pointwise P
    (fun t ht => hasSymmetricJacobian_pressureGradient (P_contDiffOn T) ht)
    (fun t ht => contDiff_gradSlice (P_contDiffOn T) ht)
    (fun t ht => (NSFormalization.Section4.D01.contDiff_slice_scalar (P_contDiffOn T) ht).differentiable (by simp))

end Rev113.NonVac

end
