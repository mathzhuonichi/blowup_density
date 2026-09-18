import NSFormalization.Section4.D01.FiniteOrderNorm

/-!
# The order-0 vector Plancherel isometry (T22 · unit U-A4)

`Section4/D01/OrderZeroDatum.lean` constructs the explicit order-0 angular real-vector
Sobolev datum `orderZeroDatum hz : RealVectorSobolev 0` of a square-integrable field
(`hz : MemLp z 2 volume`) and proves it *realizes* `z`, but its "Scope: the norm identity
is NOT proved here" note explicitly leaves the **Plancherel norm identity** open.
`Section4/D01/FiniteOrderNorm.lean` supplied only the `≤` half
(`norm_orderZeroDatum_le : ‖orderZeroDatum hz‖ ≤ ‖hz.toLp‖`).

This module closes it with the exact order-0 identity in `ℝ≥0∞`:

`norm_orderZeroDatum_eq : ‖orderZeroDatum hz‖ₑ = eLpNorm z 2 volume`.

## Route

The order-0 realization pipeline
`orderZeroDatum hz = cyclesToAngularRealVector 0 (WithLp.toLp 2 (i ↦ realProjectionTo 0 (𝓕 (componentLp hz i))))`
is an **isometry chain** at `s = 0`:

* the angular transport is a genuine isometry at order `0`.  At the `Lp` level both
  `Paper3.cyclesToAngular_norm_le` and `Paper3.cyclesToAngular_symm_norm_le` collapse to
  `frequencyUnit ^ |0| = 1`, forcing `cyclesToAngular_zero_norm`
  (`‖cyclesToAngular 0 g‖ = ‖g‖`); the real-subspace transport `cyclesToAngularReal 0`
  coincides with it under the closed-subspace coercion (`Contracts`-free `ofSubmodules_apply`
  rewrite, `coe_cyclesToAngularReal_zero`), which upgrades it to the scalar real isometry
  `cyclesToAngularReal_zero_norm` and, componentwise through `PiLp.norm_sq_eq_of_L2`, to the
  Euclidean-vector isometry `cyclesToAngularRealVector_zero_norm`;
* on each component `𝓕 (componentLp hz i)` is conjugate-symmetric
  (`D01.fourier_componentLp_mem`), so `Paper3.realProjectionTo 0` acts as the identity
  (`realProjection_eq_self`) and loses no norm, and `MeasureTheory.Lp.norm_fourier_eq`
  (Plancherel) turns `‖𝓕 (componentLp hz i)‖` into `‖componentLp hz i‖`;
* `D01.norm_toLp_component_sq_sum` reassembles `∑ᵢ ‖componentLp hz i‖²` into `‖hz.toLp‖²`
  (the Euclidean Pythagoras identity `D01.eLpNorm_component_sq_sum`), and `Lp.enorm_toLp`
  identifies `‖hz.toLp‖ₑ` with `eLpNorm z 2 volume`.

The `.ofSubmodules`/`.restrictScalars` unification behind `cyclesToAngularReal` on the closed
real subspace is heartbeat-heavy (flagged in `OrderZeroDatum.lean` and
`AngularRealVectorBochner.lean`, which itself runs at 800000): the reverse (`symm`) bound on
the *subspace* overflows even 400000.  Routing the isometry through the plain-`Lp`
`cyclesToAngular` and two definitional coercion bridges pays each heavy `isDefEq` exactly once,
so every declaration fits inside a commented `maxHeartbeats 400000`.

No `sorry`, no `axiom`; every declaration prints `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01

variable {z : Space → Space}

/-! ## 1. The angular transport is a genuine isometry at order `0` -/

-- Plain-`Lp` reverse (`symm`) unification, no closed-subspace diamond: fits inside 400000.
set_option maxHeartbeats 400000 in
/-- At order `0` the cycles-to-angular transport of the plain `L²` Sobolev data is
norm-preserving: `frequencyUnit ^ |0| = 1` collapses both one-sided bounds to equality. -/
theorem cyclesToAngular_zero_norm (g : SobolevHilbert (0 : ℝ)) :
    ‖cyclesToAngular 0 g‖ = ‖g‖ := by
  refine le_antisymm ?_ ?_
  · have hle := cyclesToAngular_norm_le 0 g
    rwa [abs_zero, Real.rpow_zero, one_mul] at hle
  · have hle := cyclesToAngular_symm_norm_le 0 (cyclesToAngular 0 g)
    rwa [abs_zero, Real.rpow_zero, one_mul,
      ContinuousLinearEquiv.symm_apply_apply] at hle

-- Definitional (`Submodule` subtype norm); isolating it pays the closed-subspace `isDefEq` once.
set_option maxHeartbeats 400000 in
/-- The `RealSobolevHilbert 0` norm is the ambient `L²` norm of the closed-subspace coercion. -/
theorem norm_coe_realSobolev (h : RealSobolevHilbert (0 : ℝ)) :
    ‖h‖ = ‖(h : FourierData)‖ := rfl

-- Definitional (`ContinuousLinearEquiv.ofSubmodules_apply`); pays the heavy `isDefEq` once.
set_option maxHeartbeats 400000 in
/-- The real-subspace angular transport is the plain-`Lp` transport of the coercion. -/
theorem coe_cyclesToAngularReal_zero (h : RealSobolevHilbert (0 : ℝ)) :
    (cyclesToAngularReal 0 h : FourierData) = cyclesToAngular 0 (h : FourierData) := rfl

-- Composition of the three preceding facts as opaque rewrites: no fresh heavy `isDefEq`.
set_option maxHeartbeats 400000 in
/-- At order `0` the real-subspace cycles-to-angular transport is a genuine isometry. -/
theorem cyclesToAngularReal_zero_norm (h : RealSobolevHilbert (0 : ℝ)) :
    ‖cyclesToAngularReal 0 h‖ = ‖h‖ := by
  rw [norm_coe_realSobolev (cyclesToAngularReal 0 h), coe_cyclesToAngularReal_zero h,
    cyclesToAngular_zero_norm, ← norm_coe_realSobolev h]

-- The `PiLp` view of `cyclesToAngularRealVector` is heartbeat-heavy; kept inside 400000.
set_option maxHeartbeats 400000 in
/-- The vector angular transport `cyclesToAngularRealVector 0` is a genuine isometry: the
scalar isometry on each of the three `PiLp 2` components lifts through
`PiLp.norm_sq_eq_of_L2`. -/
theorem cyclesToAngularRealVector_zero_norm (v : RealVectorSobolev (0 : ℝ)) :
    ‖cyclesToAngularRealVector 0 v‖ = ‖v‖ := by
  have hsq : ‖cyclesToAngularRealVector 0 v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖cyclesToAngularReal 0 (v i)‖ ^ 2 = ‖v i‖ ^ 2
    rw [cyclesToAngularReal_zero_norm]
  have h := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-! ## 2. The order-0 Plancherel identity -/

-- Uses the heavy `cyclesToAngularRealVector` defeq via the opaque lemma above; inside 400000.
set_option maxHeartbeats 400000 in
/-- **U-A4 — the order-0 vector Plancherel isometry.**  The Plancherel norm identity that
`Section4/D01/OrderZeroDatum.lean` leaves open: the order-0 angular real-vector Sobolev datum
of a square-integrable field has extended `L²` norm exactly `eLpNorm z 2 volume` (constant `1`). -/
theorem norm_orderZeroDatum_eq (hz : MemLp z 2 volume) :
    ‖orderZeroDatum hz‖ₑ = eLpNorm z 2 volume := by
  -- Each component: `realProjectionTo 0` is the identity on the real subspace, then Plancherel.
  have hcomp : ∀ i : Fin 3,
      ‖realProjectionTo 0 (𝓕 (componentLp hz i))‖ = ‖componentLp hz i‖ := by
    intro i
    have hmem : realProjection (𝓕 (componentLp hz i)) = 𝓕 (componentLp hz i) :=
      realProjection_eq_self (fourier_componentLp_mem hz i)
    have h1 : ‖realProjectionTo 0 (𝓕 (componentLp hz i))‖
        = ‖realProjection (𝓕 (componentLp hz i))‖ := rfl
    rw [h1, hmem, Lp.norm_fourier_eq]
  -- The real-norm identity `‖orderZeroDatum hz‖ = ‖hz.toLp‖`.
  have hnorm : ‖orderZeroDatum hz‖ = ‖hz.toLp‖ := by
    have hsq : ‖orderZeroDatum hz‖ ^ 2 = ‖hz.toLp‖ ^ 2 := by
      have h0 : ‖orderZeroDatum hz‖
          = ‖(WithLp.toLp 2 (fun i => realProjectionTo 0 (𝓕 (componentLp hz i))) :
              RealVectorSobolev (0 : ℝ))‖ := by
        rw [show orderZeroDatum hz
              = cyclesToAngularRealVector 0
                  (WithLp.toLp 2 (fun i => realProjectionTo 0 (𝓕 (componentLp hz i)))) from rfl,
          cyclesToAngularRealVector_zero_norm]
      rw [h0, PiLp.norm_sq_eq_of_L2, norm_toLp_component_sq_sum hz]
      refine Finset.sum_congr rfl fun i _ => ?_
      change ‖realProjectionTo 0 (𝓕 (componentLp hz i))‖ ^ 2 = ‖componentLp hz i‖ ^ 2
      rw [hcomp i]
    have h := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  rw [← ofReal_norm (orderZeroDatum hz), hnorm, ofReal_norm, Lp.enorm_toLp]

end NSFormalization.Section3.T22
