import NSFormalization.Section4.D01.OrderZeroDatum
import Euler.MeanSolenoidalSpace
import Euler.LpSmoothField

/-!
# C1b (order 0): the carrier bridge for the order-0 Sobolev datum

Unit **C1b** of `research/A01/A01_SPLIT.md` (§b row `A1`, §c rows `c5`/`c6`/`c8`)
and `research/A01/COMPARISON.md` §3 is the carrier bridge between D01's angular
Sobolev datum `IsSobolevDatum m z A`
(`verification/Contracts/V1/Data.lean:160`, restated verbatim as
`NSFormalization.Section4.D01.IsSobolevDatum`, `SmoothDatum.lean:237`) and the
ordinary `L²` coordinate `EulerMeanSolenoidal.L2`
(`vendor/NavierStokesAndEuler/Euler/MeanSolenoidalSpace.lean:22`,
`= Lp Space 2 volume`) carried by the forced local existence path
`NSFormalization.Source.OrdinaryForcedLocal.exists_local`
(`Source/OrdinaryForcedLocal.lean:32`), whose output `U : C(Icc 0 T,
EulerMeanSolenoidal.L2)` satisfies `U 0 = a.toLp`.

This module discharges the **order-0** sub-unit **C1b-0** of the split table
`research/A01/C1B_SPLIT.md` — the row every higher-order row depends on.

## Why order 0 is the first S unit

At order `0` the `ordinaryLift` adjoint plays no role: the order-0 coordinate is
the `L²` field itself
(`ordinarySobolev_value`, `Euler/MeanOrbitSobolev.lean:75`,
`value 1 (ordinarySobolev q u hu) = ordinaryLift u`), so the bridge collapses to
D01's own order-0 seed `NSFormalization.Section4.D01.orderZeroDatum`
(`OrderZeroDatum.lean:96`) applied to the `L²` element of the path.  The Fourier
normalization at order 0 is trivial: `angularRealization 0` is Mathlib's genuine
`L²` (inverse) Fourier embedding (`Paper3.sobolevRealization_zero`), so the
constant relating the D01 angular convention
(`Source.angularFourier = (2π)^{-3/2}·𝓕((2π)⁻¹·)`, `FourierConvention.lean:23`)
to the plain `L²` field is exactly `1`.  This is the only C1b row where no
convention constant has to be settled first.

## What is proved

* `IsSobolevDatum.congr_field` — the pairing predicate `IsSobolevDatum s z A`
  reads the physical field `z` only through the Bochner integrals `∫ ψ · z_i`,
  so it is invariant under a.e. equality of `z`, at **every** order.  Pure
  bookkeeping (integral congruence); no analysis.
* `isSobolevDatum_zero_ordinaryL2` — the C1b-0 bridge: an Euler ordinary `L²`
  field `U` has the D01 order-0 datum `orderZeroDatum (Lp.memLp U)`, i.e. its own
  componentwise `L²` Fourier transform in the angular convention.
* `exists_isSobolevDatum_zero_ordinaryL2` — the `∃` corollary.
* `isSobolevDatum_zero_initial` — the C1b-0 slice of unit **c5**: the initial
  clause `U 0 = a.toLp` of `exists_local`, transported to a pointwise order-0
  datum for the physical initial field `a.field`.

## Scope: order 0 only

The order-`m` rows (`m ≥ 1`) route derivative tensors through the `ordinaryLift`
adjoint (`ordinaryValue`, `Source/OrdinaryCylinderDescent.lean:56`) and must
reconcile the homogeneous derivative multiplier `(2πiξ)^{⊗m}` with D01's
inhomogeneous Bessel weight `(1+(2π)²‖ξ‖²)^{m/2}`; that is the real-analysis gap
of C1b and is **not** proved here (see `research/A01/C1B_SPLIT.md`).  Continuity
of the order-0 datum path (row `c8-0`) is likewise deferred: it needs
`orderZeroDatum` expressed as a continuous map of its `L²` argument.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space)

/-- The order-`s` datum pairing `IsSobolevDatum s z A` reads the physical field
`z` only through the Bochner integrals `∫ ψ x · (z x i)`, so it is invariant
under a.e. equality of `z`.  All real orders; no analytic content.

This is the bookkeeping step that lets an `L²`-valued path's a.e. representative
(the physical velocity slice) inherit the datum of the `L²` element, and lets
the initial clause `U 0 = a.toLp` be moved onto the physical field `a.field`. -/
theorem IsSobolevDatum.congr_field {s : ℝ} {z z' : Space → Space}
    {A : RealVectorSobolev s} (h : IsSobolevDatum s z A) (hzz' : z =ᵐ[volume] z') :
    IsSobolevDatum s z' A := by
  intro i ψ
  rw [h i ψ]
  refine integral_congr_ae ?_
  filter_upwards [hzz'] with x hx
  rw [hx]

/-- **C1b-0 — the order-0 carrier bridge.**  An Euler ordinary `L²` field
`U : EulerMeanSolenoidal.L2` has the D01 order-0 angular Sobolev datum
`orderZeroDatum (Lp.memLp U)` — its own componentwise `L²` Fourier transform,
projected into the real subspace and transported to the manuscript's angular
convention.  No smoothness, no compact support, no `L¹` hypothesis.

This is the C1b bridge at order 0: it identifies the ordinary `L²` coordinate of
`exists_local`'s path value with a D01 datum.  At order 0 the `ordinaryLift`
adjoint is not used (`ordinarySobolev`'s value coordinate is `ordinaryLift u`,
`Euler/MeanOrbitSobolev.lean:75`), so this is D01's order-0 seed applied to `U`. -/
theorem isSobolevDatum_zero_ordinaryL2 (U : EulerMeanSolenoidal.L2) :
    IsSobolevDatum 0 (⇑U) (orderZeroDatum (Lp.memLp U)) :=
  isSobolevDatum_orderZeroDatum (Lp.memLp U)

/-- Every Euler ordinary `L²` field has an order-0 angular real-vector Sobolev
datum.  The `∃` corollary of `isSobolevDatum_zero_ordinaryL2`. -/
theorem exists_isSobolevDatum_zero_ordinaryL2 (U : EulerMeanSolenoidal.L2) :
    ∃ A : RealVectorSobolev 0, IsSobolevDatum 0 (⇑U) A :=
  ⟨_, isSobolevDatum_zero_ordinaryL2 U⟩

/-- **C1b-0 slice of unit c5** (`research/A01/A01_SPLIT.md` §c row `c5`).  The
initial clause `U 0 = a.toLp` of `Source.OrdinaryForcedLocal.exists_local`
(`Source/OrdinaryForcedLocal.lean:41`), transported to a pointwise order-0 datum
statement for the physical initial field `a.field`.

`a.field` and the a.e. representative `⇑U` agree a.e. (`SmoothL2Field.toLp_ae`,
`Euler/LpSmoothField.lean:44`), and `IsSobolevDatum` is a.e.-invariant in the
field (`IsSobolevDatum.congr_field`), so the order-0 datum of `U` realizes
`a.field` as well. -/
theorem isSobolevDatum_zero_initial (a : EulerLpTranslation.SmoothL2Field Space)
    (U : EulerMeanSolenoidal.L2) (hU : U = a.toLp) :
    IsSobolevDatum 0 a.field (orderZeroDatum (Lp.memLp U)) :=
  IsSobolevDatum.congr_field (isSobolevDatum_zero_ordinaryL2 U)
    (by rw [hU]; exact a.toLp_ae)

end NSFormalization.Section4.A01
