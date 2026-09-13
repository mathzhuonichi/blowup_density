import NSFormalization.Paper1.PeriodicFiniteOrderMild
import Euler.CylinderSobolevDerivatives
set_option maxHeartbeats 800000

/-!
# H3 point-evaluation bridge for periodic paths

This is the small, proved bridge currently available below the finite-order
mild theory.  It does not assert Navier--Stokes regularity or pressure
recovery; those remain separate analytic obligations.
-/

noncomputable section

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge

open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerSobolevJointEvaluation
open EulerSobolevPointEvaluation EulerCylinderSobolev EulerLiftedGradientSpace

variable {T : Type*} [TopologicalSpace T]

/-- A continuous cylinder H3 path has a jointly continuous pointwise
representative.  This is the exact API needed before adding PDE identities. -/
theorem continuous_pointwise_representative
    (period : ℝ) [Fact (0 < period)]
    (u : C(T, SobolevSpace period 3)) :
    Continuous (fun p : T × LiftDomain period =>
      EulerSobolevPointEvaluation.pointEvaluation period p.2 (u p.1)) := by
  exact path_representative_joint_continuous period u

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge

open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
open EulerSobolevPointEvaluation EulerSobolevJointEvaluation

variable {period : ℝ} [Fact (0 < period)]

/-- A Sobolev coordinate derivative is compatible with the classical derivative
of the underlying translated representative.  This is the spatial part of the
mild-to-classical bridge; temporal smoothness is deliberately not asserted. -/
theorem derivative_translation_hasDerivAt {r : ℕ}
    (i : Fin 4) (u : SobolevSpace period (r + 1)) :
    HasDerivAt
      (fun s => translation period (translationPath period (standardDirection i) s)
        (value period u))
      (value period (derivativeOperator period r i u)) 0 := by
  exact derivativeOperator_hasDerivAt period i u

/-- The same derivative compatibility holds at every time slice of a continuous
path whose values have one additional Sobolev order. -/
theorem path_derivative_translation_hasDerivAt {T : Type*} [TopologicalSpace T]
    {r : ℕ} (u : C(T, SobolevSpace period (r + 1))) (t : T) (i : Fin 4) :
    HasDerivAt
      (fun s => translation period (translationPath period (standardDirection i) s)
        (value period (u t)))
      (value period (derivativeOperator period r i (u t))) 0 := by
  exact derivative_translation_hasDerivAt i (u t)

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge

open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
open EulerSobolevPointEvaluation EulerSobolevJointEvaluation

variable {period : ℝ} [Fact (0 < period)]

/-- Iterated spatial translation derivative for a field with two additional Sobolev
orders.  This is the second-order interface used by the mild-to-classical bridge. -/
theorem second_derivative_translation_hasDerivAt {r : ℕ}
    (i j : Fin 4) (u : SobolevSpace period (r + 2)) :
    HasDerivAt
      (fun s => translation period (translationPath period (standardDirection i) s)
        (value period (derivativeOperator period (r + 1) j u)))
      (value period (derivativeOperator period r i
        (derivativeOperator period (r + 1) j u))) 0 := by
  exact derivativeOperator_hasDerivAt period i (derivativeOperator period (r + 1) j u)

/-- Joint continuity of the pointwise representative after taking one spatial
Sobolev derivative along a continuous path. -/
theorem differentiated_path_pointwise_continuous {T : Type*} [TopologicalSpace T]
    (u : C(T, SobolevSpace period 4)) (i : Fin 4) :
    Continuous (fun p : T × LiftDomain period =>
      EulerSobolevPointEvaluation.pointEvaluation period p.2 (derivativeOperator period 3 i (u p.1))) := by
  exact path_representative_joint_continuous period
    ((derivativeOperator period 3 i).compLeftContinuous ℝ T u)

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge

open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerCylinderSobolev EulerLiftedGradientSpace

variable {period : ℝ} [Fact (0 < period)]

/-- A fixed spatial slice of the differentiated representative is continuous in time. -/
theorem differentiated_time_slice_continuous {T : Type*} [TopologicalSpace T]
    (u : C(T, SobolevSpace period 4)) (i : Fin 4) (x : LiftDomain period) :
    Continuous (fun t : T =>
      EulerSobolevPointEvaluation.pointEvaluation period x
        (derivativeOperator period 3 i (u t))) := by
  have hjoint := differentiated_path_pointwise_continuous u i
  have hmap : Continuous (fun t : T => (t, x)) := Continuous.prodMk continuous_id (continuous_const : Continuous (fun _ : T => x))
  exact hjoint.comp hmap

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge

open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerSobolevJointEvaluation
open EulerCylinderSobolev EulerLiftedGradientSpace

variable {period : ℝ} [Fact (0 < period)]

/-- Point evaluation of a continuous H3-valued path is continuous in time at
any fixed lifted spatial point. -/
theorem pointwise_time_slice_continuous {T : Type*} [TopologicalSpace T]
    (u : C(T, SobolevSpace period 3)) (x : LiftDomain period) :
    Continuous (fun t : T => pointEvaluation period x (u t)) := by
  have hjoint := continuous_pointwise_representative period u
  have hmap : Continuous (fun t : T => (t, x)) :=
    Continuous.prodMk continuous_id (continuous_const : Continuous (fun _ : T => x))
  exact hjoint.comp hmap

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge

open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerSobolevJointEvaluation
open EulerCylinderSobolev EulerLiftedGradientSpace

variable {period : ℝ} [Fact (0 < period)]

/-- Fixed-space continuity of a first spatial derivative along an H⁴ path. -/
theorem differentiated_pointwise_time_slice_continuous
    {T : Type*} [TopologicalSpace T]
    (u : C(T, SobolevSpace period 4)) (i : Fin 4) (x : LiftDomain period) :
    Continuous (fun t : T => pointEvaluation period x
      (derivativeOperator period 3 i (u t))) := by
  exact differentiated_time_slice_continuous u i x

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge

open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerSobolevJointEvaluation
open EulerCylinderSobolev EulerLiftedGradientSpace

variable {period : ℝ} [Fact (0 < period)]

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge

open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerSobolevJointEvaluation
open EulerCylinderSobolev EulerLiftedGradientSpace

variable {period : ℝ} [Fact (0 < period)]

/-- Stable alias for fixed-space continuity of an H3-valued path. -/
theorem h3_pointwise_time_continuous {T : Type*} [TopologicalSpace T]
    (u : C(T, SobolevSpace period 3)) (x : LiftDomain period) :
    Continuous (fun t : T => pointEvaluation period x (u t)) := by
  exact pointwise_time_slice_continuous u x

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge

open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerSobolevJointEvaluation
open EulerCylinderSobolev EulerLiftedGradientSpace

variable {period : ℝ} [Fact (0 < period)]

/-- Explicit H3 path-evaluation continuity wrapper. -/
theorem h3_path_evaluation_joint_continuous {T : Type*} [TopologicalSpace T]
    (u : C(T, SobolevSpace period 3)) :
    Continuous (fun p : T × LiftDomain period => pointEvaluation period p.2 (u p.1)) := by
  exact path_representative_joint_continuous period u

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge

open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerCylinderSobolev EulerLiftedGradientSpace
variable {period : ℝ} [Fact (0 < period)]

@[simp] theorem h3_point_evaluation_zero (x : LiftDomain period) :
    pointEvaluation period x (0 : SobolevSpace period 3) = 0 := by
  exact (pointEvaluation period x).map_zero

@[simp] theorem h3_point_evaluation_add (x : LiftDomain period)
    (u v : SobolevSpace period 3) :
    pointEvaluation period x (u + v) =
      pointEvaluation period x u + pointEvaluation period x v := by
  exact (pointEvaluation period x).map_add u v

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge
open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerCylinderSobolev EulerLiftedGradientSpace
variable {period : ℝ} [Fact (0 < period)]

/-- Point evaluation is continuous as a function of the H3 field at a fixed point. -/
theorem h3_point_evaluation_continuous (x : LiftDomain period) :
    Continuous (fun u : SobolevSpace period 3 => pointEvaluation period x u) := by
  exact (pointEvaluation period x).continuous

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge
open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerCylinderSobolev EulerLiftedGradientSpace
variable {period : ℝ} [Fact (0 < period)]

/-- The scalar norm of fixed-point H3 evaluation is continuous in the field. -/
theorem h3_point_evaluation_norm_continuous (x : LiftDomain period) :
    Continuous (fun u : SobolevSpace period 3 => ‖pointEvaluation period x u‖) := by
  exact (continuous_norm.comp (h3_point_evaluation_continuous x))

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge
open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerCylinderSobolev EulerLiftedGradientSpace
variable {period : ℝ} [Fact (0 < period)]

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge
open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerCylinderSobolev EulerLiftedGradientSpace
variable {period : ℝ} [Fact (0 < period)]

/-- The norm observable vanishes on the zero H3 field. -/
@[simp] theorem h3_point_evaluation_norm_zero (x : LiftDomain period) :
    ‖pointEvaluation period x (0 : SobolevSpace period 3)‖ = 0 := by
  simp

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge

namespace NSFormalization.Paper1.PeriodicH3RepresentativeBridge
open EulerCylinderSobolevSpace EulerSobolevPointEvaluation EulerCylinderSobolev EulerLiftedGradientSpace
variable {period : ℝ} [Fact (0 < period)]

/-- Point evaluation commutes with scalar multiplication of H3 fields. -/
theorem h3_point_evaluation_smul (c : ℝ) (x : LiftDomain period)
    (u : SobolevSpace period 3) :
    pointEvaluation period x (c • u) = c • pointEvaluation period x u := by
  exact (pointEvaluation period x).map_smul c u

end NSFormalization.Paper1.PeriodicH3RepresentativeBridge
