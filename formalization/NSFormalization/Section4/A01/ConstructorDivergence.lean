import NSFormalization.Section4.A01.ConstructorPieces
import Euler.CylinderGradientEmbedding
import Euler.MeanClassicalConstraints

/-!
# Descent of the cylinder divergence constraint

The ordinary carrier is unrestricted L². Its solenoidal constraint is proved by
pulling cylinder orthogonality back along the actual isometric ordinary lift.
The existing compact-test gradient embedding supplies the required gradient
subspace inclusion; no smoothness or angular invariance of the carrier is needed.
A genuinely smooth a.e. representative then inherits pointwise divergence zero.
-/

noncomputable section
namespace NSFormalization.Section4.A01

open Set MeasureTheory InnerProductSpace
open NavierStokes.ProblemStatement (Space spatialDivergence spatialDerivative coordinateVector)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
open scoped ContDiff RealInnerProductSpace

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The measure-preserving ordinary lift and the compact-test embedding give
exactly the same L² class on the unit cylinder. -/
theorem ordinaryLift_eq_embedding (U : EulerMeanSolenoidal.L2) :
    ordinaryLift U = EulerCylinderSpatialEmbedding.embedding 1 U := by
  apply Lp.ext
  exact (ordinaryLift_ae U).trans (EulerCylinderSpatialEmbedding.lift_ae 1 U).symm

/-- A genuine ordinary gradient remains a cylinder gradient. The existing
embedding theorem lifts compact smooth scalar tests and then their closed span. -/
theorem ordinaryLift_gradient_mem (g : EulerMeanSolenoidal.L2)
    (hg : g ∈ EulerMeanSolenoidal.gradientSpace) :
    ordinaryLift g ∈ gradientSpace 1 1 0 := by
  rw [ordinaryLift_eq_embedding]
  exact EulerCylinderSpatialEmbedding.embedding_gradient_mem 1 1 (by norm_num) 0 g hg

/-- Reverse divergence descent for an arbitrary ordinary L² carrier. The
solenoidal constraint is a conclusion, not part of the carrier type. -/
theorem solenoidal_of_ordinaryLift (U : EulerMeanSolenoidal.L2)
    (hU : ordinaryLift U ∈ divergenceFreeSpace 1 1 0) :
    U ∈ EulerMeanSolenoidal.solenoidalSpace := by
  intro g hg
  exact (ordinaryLift.inner_map_map g U).symm.trans
    (hU (ordinaryLift g) (ordinaryLift_gradient_mem g hg))

/-- An actual smooth representative of the descended carrier is pointwise
solenoidal. No representative or its smoothness is constructed here. -/
theorem divergence_eq_zero_of_ordinaryLift (U : EulerMeanSolenoidal.L2)
    (hU : ordinaryLift U ∈ divergenceFreeSpace 1 1 0)
    (f : Space → Space) (hf : ContDiff ℝ ∞ f) (hrep : (⇑U) =ᵐ[volume] f) :
    ∀ x, EulerSmoothLimit.divergence f x = 0 :=
  EulerMeanClassical.solenoidal_representative_divergence U
    (solenoidal_of_ordinaryLift U hU) f hf hrep

/-- The precise two local-theory carrier conclusions imply ordinary
solenoidality at every time, without any additional regularity hypothesis. -/
theorem solenoidal_path_of_cylinder {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) :
    ∀ t, U t ∈ EulerMeanSolenoidal.solenoidalSpace := by
  intro t
  apply solenoidal_of_ordinaryLift (U t)
  rw [hU t]
  exact hdiv t

/-- The c6 field on the supplied time slab, in the actual A02/ProblemStatement
spatial-divergence vocabulary. Smooth slices and the a.e. handoff remain B1 inputs. -/
theorem spatialDivergence_eq_zero_of_cylinder {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (velocity : A02.SpaceTimeField)
    (hsmooth : ∀ t : Icc (0 : ℝ) S, ContDiff ℝ ∞ (fun x : Space => velocity (↑t, x)))
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    ∀ (t : Icc (0 : ℝ) S) x, spatialDivergence velocity t x = 0 := by
  intro t x
  have h := EulerMeanClassical.solenoidal_representative_divergence (U t)
    (solenoidal_path_of_cylinder u U hU hdiv t)
    (fun x : Space => velocity (↑t, x)) (hsmooth t) (hslice t).symm x
  rw [EulerSmoothLimit.divergence_eq_coordinate_sum] at h
  simpa only [spatialDivergence, spatialDerivative, coordinateVector] using h

end NSFormalization.Section4.A01
