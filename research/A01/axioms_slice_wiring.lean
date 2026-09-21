import NSFormalization.Section4.A01.SliceWiring
import NSFormalization.Section4.A04.ZeroSolution

/-!
Conformance for lane 157 (`Section4/A01/SliceWiring.lean`).  Every declaration must print exactly the
standard three axioms `[propext, Classical.choice, Quot.sound]`, and the row theorems must fire on a
concrete instance — the zero classical solution `A04.zeroSol` with the zero cylinder pair
`u := 0`, `U := 0` — yielding genuine, non-vacuous conclusions.
-/

noncomputable section

open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.A04 (zeroSol sobolevNormAt)
open NSFormalization.Section4.D01 (IsSobolevDatum jetSobolevConst sobolevENorm)
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerLpTranslation
open scoped ENNReal ContDiff

#print axioms velocitySliceSmoothL2_field
#print axioms sobolevENorm_slice_ne_top_order
#print axioms sobolevENorm_slice_ne_top
#print axioms sobolevSpace_norm_le_sobolevNormAt_of_solution
#print axioms isSobolevDatum_ordinary_of_hslice
#print axioms apriori_rows_of_hslice

/-! ## Non-vacuity on the zero classical solution, zero cylinder pair -/

/-- The concrete zero classical solution on `[0,2)` and the zero cylinder pair on `[0,1]`. -/
private def w0 : NSFormalization.Section4.A02.ClassicalSolutionR 1 0 0 2 :=
  zeroSol 1 2 (by norm_num) (by norm_num)

private def u0 (q : ℕ) : C(Icc (0 : ℝ) 1, SobolevSpace 1 (q + 1)) := 0
private def U0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2) := 0

private theorem hu0 (q : ℕ) :
    ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u0 q t) = u0 q t := by
  intro θ t; simp [u0]

private theorem hU0 (q : ℕ) : ∀ t, ordinaryLift (U0 t) = value 1 (u0 q t) := by
  intro t; simp [u0, U0, value]

private theorem hslice0 :
    ∀ t : Icc (0 : ℝ) 1, (fun x : Space => w0.velocity (↑t, x)) =ᵐ[volume] ⇑(U0 t) := by
  intro t
  have hv : (fun x : Space => w0.velocity (↑t, x)) = (0 : Space → Space) := by funext x; rfl
  rw [hv]
  simp only [U0, ContinuousMap.zero_apply]
  exact (Lp.coeFn_zero Space 2 volume).symm

/-- The slice finiteness fires on the zero solution: `sobolevENorm (q+1) 0 ≠ ⊤`. -/
theorem nonvacuous_slice_ne_top (q : ℕ) :
    sobolevENorm ((q + 1 : ℕ) : ℝ) (fun x : Space => w0.velocity ((0 : ℝ), x)) ≠ ⊤ :=
  sobolevENorm_slice_ne_top (q := q) w0 (by norm_num)

#print axioms nonvacuous_slice_ne_top

/-- The row-(ii) converse fires on the zero solution and the zero cylinder pair, giving the genuine
`‖0‖ ≤ jetSobolevConst (q+1) · sobolevNormAt (q+1) 0 ↑t` at every `t`. -/
theorem nonvacuous_converse (q : ℕ) :
    ∀ t : Icc (0 : ℝ) 1,
      ‖u0 q t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w0.velocity ↑t :=
  sobolevSpace_norm_le_sobolevNormAt_of_solution (by norm_num) w0 (u0 q) U0
    (hu0 q) (hU0 q) hslice0

#print axioms nonvacuous_converse

/-- The datum transport fires: `⇑(U t)` has an order-`m` datum at every order, via `hslice`. -/
theorem nonvacuous_datum_transport (m : ℕ) (t : Icc (0 : ℝ) 1) :
    ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) (⇑(U0 t)) A :=
  isSobolevDatum_ordinary_of_hslice (by norm_num) w0 U0 hslice0 m t

#print axioms nonvacuous_datum_transport

/-- Both a-priori rows fire at once on the zero solution and the zero cylinder pair. -/
theorem nonvacuous_apriori_rows :
    (∀ t : Icc (0 : ℝ) 1, sobolevNormAt (2 : ℝ) w0.velocity ↑t ≤ 16 * ‖u0 6 t‖) ∧
      (∀ t : Icc (0 : ℝ) 1,
        ‖u0 6 t‖ ≤ jetSobolevConst (6 + 1) * sobolevNormAt ((6 + 1 : ℕ) : ℝ) w0.velocity ↑t) :=
  apriori_rows_of_hslice (by norm_num) (by norm_num) w0 (u0 6) U0 (hu0 6) (hU0 6) hslice0

#print axioms nonvacuous_apriori_rows
