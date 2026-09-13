import Formal.R3SchwartzMajorantYoungRepresentative

namespace MNS2

open MeasureTheory

noncomputable section

/--
The ordinary right scalar majorant belongs to real `L²(R³)` because it agrees almost everywhere
with the bundled Young candidate from `R3SchwartzNormFieldL2`.
-/
theorem memLp_r3H2RightScalarMajorant
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) :
    MemLp (r3H2RightScalarMajorant a b) 2 (volume : Measure R3) := by
  have hae := coeFn_r3H2RightMajorantYoungL2_eq_scalarMajorant a b
  have hmeas :
      AEStronglyMeasurable (r3H2RightScalarMajorant a b) (volume : Measure R3) :=
    (Lp.aestronglyMeasurable (r3H2RightMajorantYoungL2 a b)).congr hae
  exact (Lp.memLp (r3H2RightMajorantYoungL2 a b)).congr_norm hmeas
    (hae.mono fun ξ hξ => by rw [hξ])

/--
The ordinary left scalar majorant belongs to real `L²(R³)` because it agrees almost everywhere
with the bundled Young candidate from `R3SchwartzNormFieldL2`.
-/
theorem memLp_r3H2LeftScalarMajorant
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) :
    MemLp (r3H2LeftScalarMajorant a b) 2 (volume : Measure R3) := by
  have hae := coeFn_r3H2LeftMajorantYoungL2_eq_scalarMajorant a b
  have hmeas :
      AEStronglyMeasurable (r3H2LeftScalarMajorant a b) (volume : Measure R3) :=
    (Lp.aestronglyMeasurable (r3H2LeftMajorantYoungL2 a b)).congr hae
  exact (Lp.memLp (r3H2LeftMajorantYoungL2 a b)).congr_norm hmeas
    (hae.mono fun ξ hξ => by rw [hξ])

/-- The ordinary right scalar majorant bundled canonically as a real `L²(R³)` element. -/
def r3H2RightScalarMajorantL2
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) : R3L2RealScalar :=
  (memLp_r3H2RightScalarMajorant a b).toLp (r3H2RightScalarMajorant a b)

/-- The ordinary left scalar majorant bundled canonically as a real `L²(R³)` element. -/
def r3H2LeftScalarMajorantL2
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) : R3L2RealScalar :=
  (memLp_r3H2LeftScalarMajorant a b).toLp (r3H2LeftScalarMajorant a b)

/-- The canonical right-majorant bundle is exactly the previously constructed Young candidate. -/
theorem r3H2RightScalarMajorantL2_eq_Young
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) :
    r3H2RightScalarMajorantL2 a b = r3H2RightMajorantYoungL2 a b := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp (memLp_r3H2RightScalarMajorant a b)).trans
    (coeFn_r3H2RightMajorantYoungL2_eq_scalarMajorant a b).symm

/-- The canonical left-majorant bundle is exactly the previously constructed Young candidate. -/
theorem r3H2LeftScalarMajorantL2_eq_Young
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) :
    r3H2LeftScalarMajorantL2 a b = r3H2LeftMajorantYoungL2 a b := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp (memLp_r3H2LeftScalarMajorant a b)).trans
    (coeFn_r3H2LeftMajorantYoungL2_eq_scalarMajorant a b).symm

/-- Young `L¹ * L² → L²` bound transferred to the ordinary right scalar majorant. -/
theorem norm_r3H2RightScalarMajorantL2_le
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) :
    ‖r3H2RightScalarMajorantL2 a b‖ ≤
      (∫ ξ : R3, ‖a ξ‖) *
        ‖(r3H2WeightedVelocitySchwartz b).toLp 2 (volume : Measure R3)‖ := by
  rw [r3H2RightScalarMajorantL2_eq_Young]
  exact norm_r3H2RightMajorantYoungL2_le a b

/-- Young `L² * L¹ → L²` bound transferred to the ordinary left scalar majorant. -/
theorem norm_r3H2LeftScalarMajorantL2_le
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) :
    ‖r3H2LeftScalarMajorantL2 a b‖ ≤
      ‖(r3H2WeightedScalarSchwartz a).toLp 2 (volume : Measure R3)‖ *
        (∫ ξ : R3, ‖b ξ‖) := by
  rw [r3H2LeftScalarMajorantL2_eq_Young]
  exact norm_r3H2LeftMajorantYoungL2_le a b

end

end MNS2
