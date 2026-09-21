import NSFormalization.Section3.T24.ConservativeOmega

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokesR3.ProblemStatement (navierStokesResidual)
open NSFormalization.Section3.T23 NSFormalization.Section3.T24
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff RealInnerProductSpace

/- Mutation of the main pairing input: this copies `ClassicalSolutionOmega`
field-for-field except that homogeneous no-slip is removed. -/
structure PairingSolutionWithoutNoSlip (nu : ℝ) (Omega : Set Space)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ) where
  velocity : SpaceTimeField
  pressure : SpaceTimeScalar
  horizon_pos : 0 < T
  velocity_smooth : SmoothOnClosedSlab (Ico (0 : ℝ) T) Omega velocity
  pressure_smooth : SmoothOnClosedSlab (Ico (0 : ℝ) T) Omega pressure
  initial : ∀ x ∈ Omega, velocity (0, x) = a x
  divergence : ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ Omega,
    spatialDivergence velocity t x = 0
  momentum : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Omega,
    navierStokesResidual nu velocity pressure t x = g (t, x)
  pressure_gauge : ∀ t ∈ Ico (0 : ℝ) T,
    (∫ x in Omega, pressure (t, x)) = 0

/- The reviewed proof cannot establish the mutated theorem: the boundary term
has no zero trace with which to close. This file is expected not to compile. -/
theorem potential_pairingOmega_without_no_slip
    (nu T : ℝ) (_hT : 0 < T) (Omega : Set Space)
    (hOmega : IsBoundedBoxOrSmoothDomain Omega) (phi : SpaceTimeScalar)
    (hphi : ContDiff ℝ ∞ phi)
    (S : PairingSolutionWithoutNoSlip nu Omega 0 (conservativeForceOmega phi) T)
    (t : ℝ) (ht : t ∈ Ico 0 T) :
    (∫ x in Omega, inner ℝ (conservativeForceOmega phi (t, x))
      (S.velocity (t, x))) = 0 := by
  have h := (ibp_boundedDomain hOmega).integral_pressure_energy_zero hOmega.2.1
    hOmega.1.measurableSet (fun _ hx ↦ S.velocity_smooth.contDiffAt_slice ht hx)
    (fun x _ ↦ (hphi.comp (contDiff_const.prodMk contDiff_id)).contDiffAt)
    (S.no_slip t ht) (S.divergence t ht)
  simpa only [conservativeForceOmega, inner_neg_left, real_inner_comm,
    integral_neg, neg_eq_zero] using h
