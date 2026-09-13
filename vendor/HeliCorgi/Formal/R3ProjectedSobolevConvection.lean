import Formal.R3H2LerayBridge
import Formal.R3SobolevConvectionExtension

namespace MNS2

open MeasureTheory

noncomputable section

/--
The completed order-three-to-order-two convection map followed by the Leray projector on the
stored order-two Bessel coordinate.  The sign is positive: the mild equation supplies its own
minus sign.
-/
def r3ProjectedConvectionH3ToH2 :
    R3HsVelocity 3 →L[ℂ] R3HsVelocity 3 →L[ℂ] R3HsVelocity 2 :=
  (ContinuousLinearMap.postcomp (R3HsVelocity 3) r3LerayH2Operator).comp
    r3ConvectionH3ToH2

@[simp]
theorem r3ProjectedConvectionH3ToH2_apply
    (u v : R3HsVelocity 3) :
    r3ProjectedConvectionH3ToH2 u v =
      r3LerayH2Operator (r3ConvectionH3ToH2 u v) := by
  rfl

/-- The projected completed bilinear operator inherits the same operator-norm bound. -/
theorem norm_r3ProjectedConvectionH3ToH2_le :
    ‖r3ProjectedConvectionH3ToH2‖ ≤
      r3SchwartzConvectionFullH3Constant := by
  let Ppost :
      (R3HsVelocity 3 →L[ℂ] R3HsVelocity 2) →L[ℂ]
        (R3HsVelocity 3 →L[ℂ] R3HsVelocity 2) :=
    ContinuousLinearMap.postcomp (R3HsVelocity 3) r3LerayH2Operator
  change ‖Ppost.comp r3ConvectionH3ToH2‖ ≤
    r3SchwartzConvectionFullH3Constant
  calc
    ‖Ppost.comp r3ConvectionH3ToH2‖ ≤
        ‖Ppost‖ * ‖r3ConvectionH3ToH2‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖r3LerayH2Operator‖ * ‖r3ConvectionH3ToH2‖ :=
      mul_le_mul_of_nonneg_right
        (by
          simpa [Ppost] using
            (ContinuousLinearMap.norm_postcomp_le
              (E := R3HsVelocity 3) r3LerayH2Operator))
        (norm_nonneg r3ConvectionH3ToH2)
    _ ≤ 1 * r3SchwartzConvectionFullH3Constant :=
      mul_le_mul norm_r3LerayH2Operator_le_one norm_r3ConvectionH3ToH2_le
        (norm_nonneg r3ConvectionH3ToH2) (by norm_num)
    _ = r3SchwartzConvectionFullH3Constant := one_mul _

/-- The projected completed map has the explicit inherited `H³ × H³ → H²` bound. -/
theorem norm_r3ProjectedConvectionH3ToH2_apply_le
    (u v : R3HsVelocity 3) :
    ‖r3ProjectedConvectionH3ToH2 u v‖ ≤
      r3SchwartzConvectionFullH3Constant * ‖u‖ * ‖v‖ := by
  rw [r3ProjectedConvectionH3ToH2_apply]
  exact (norm_r3LerayH2Operator_apply_le _).trans
    (norm_r3ConvectionH3ToH2_apply_le u v)

/-- Every output lies in the stored-coordinate `L²` solenoidal submodule. -/
theorem r3ProjectedConvectionH3ToH2_mem_solenoidal
    (u v : R3HsVelocity 3) :
    r3ProjectedConvectionH3ToH2 u v ∈ r3L2SolenoidalSubmodule := by
  rw [r3ProjectedConvectionH3ToH2_apply]
  exact r3LerayH2Operator_mem_solenoidal _

/-- The genuine physical `L²` reconstruction of every output is also solenoidal. -/
theorem r3H2ToL2Operator_r3ProjectedConvectionH3ToH2_mem_solenoidal
    (u v : R3HsVelocity 3) :
    r3H2ToL2Operator (r3ProjectedConvectionH3ToH2 u v) ∈
      r3L2SolenoidalSubmodule := by
  rw [r3ProjectedConvectionH3ToH2_apply,
    r3H2ToL2Operator_commutes_leray]
  exact r3LerayL2Operator_mem_solenoidal _

/--
The order-two decoder identifies the projected completed output with the physical `L²` Leray
projection of the genuine `J⁻²` reconstruction of the unprojected output coordinate.
-/
theorem r3HsToTempered_r3ProjectedConvectionH3ToH2
    (u v : R3HsVelocity 3) :
    r3HsToTemperedCLM 2 (r3ProjectedConvectionH3ToH2 u v) =
      r3L2ToTemperedCLM
        (r3LerayL2Operator
          (r3H2ToL2Operator (r3ConvectionH3ToH2 u v))) := by
  rw [r3ProjectedConvectionH3ToH2_apply,
    r3HsToTempered_r3LerayH2Operator]

/-- On canonical Schwartz inputs, the projected extension agrees in its stored coordinate. -/
@[simp]
theorem r3ProjectedConvectionH3ToH2_apply_schwartz
    (u v : R3SchwartzVelocity) :
    r3ProjectedConvectionH3ToH2
        (r3SchwartzToHsCLM 3 u) (r3SchwartzToHsCLM 3 v) =
      r3LerayH2Operator
        (r3SchwartzToHsCLM 2 (r3SchwartzConvection u v)) := by
  rw [r3ProjectedConvectionH3ToH2_apply,
    r3ConvectionH3ToH2_apply_schwartz]

/--
On Schwartz inputs, decoding the projected extension recovers the repository's existing literal
physical `L²` object `P((u · ∇)v)`.
-/
theorem r3HsToTempered_r3ProjectedConvectionH3ToH2_schwartz
    (u v : R3SchwartzVelocity) :
    r3HsToTemperedCLM 2
        (r3ProjectedConvectionH3ToH2
          (r3SchwartzToHsCLM 3 u) (r3SchwartzToHsCLM 3 v)) =
      r3L2ToTemperedCLM (r3ProjectedSchwartzConvectionL2 u v) := by
  rw [r3ProjectedConvectionH3ToH2_apply_schwartz]
  simpa [r3ProjectedSchwartzConvectionL2] using
    r3HsToTempered_r3LerayH2Operator_schwartz
      (r3SchwartzConvection u v)

end

end MNS2
