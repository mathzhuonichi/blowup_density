import NSFormalization.Section4.A01.ConstructorDivergence

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space coordinateVector)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerLpTranslation EulerMetricTransport
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

namespace NSFormalization.Section4.A01

/-- Review probe: the a.e. conclusion follows directly, without angle invariance or word descent. -/
theorem rev162_divergence_ae_direct_without_words {q : ℕ}
    (u : SobolevSpace 1 (q + 1))
    (U : EulerMeanSolenoidal.L2)
    (hU : ordinaryLift U = value 1 u)
    (hdiv : value 1 u ∈ divergenceFreeSpace 1 1 0)
    (Z : SmoothL2Field Space)
    (hZ : Z.field =ᵐ[volume] ⇑U) :
    ∀ᵐ x ∂(volume : Measure Space),
      ∑ i : Fin 3, (fderiv ℝ Z.field x (coordinateVector i)) i = 0 := by
  have hrep0 := ordinaryLift_ae U
  rw [hU] at hrep0
  have hZlift : (fun p : LiftDomain 1 => U p.1) =ᵐ[liftMeasure 1]
      fun p : LiftDomain 1 => Z.field p.1 :=
    ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae hZ.symm
  have hrep : ((value 1 u : LiftDomain 1 → Space)) =ᵐ[liftMeasure 1]
      fun p : LiftDomain 1 => Z.field p.1 := hrep0.trans hZlift
  have hlocal : ∀ p : LiftDomain 1,
      ContDiff ℝ ∞ (localFieldLift 1 (fun z : LiftDomain 1 => Z.field z.1) p) := by
    intro p
    exact Z.smooth.comp (contDiff_const.add contDiff_fst)
  have hlifted_zero :=
    EulerClassicalDivergence.divergenceFree_classical_divergence_zero
      1 1 (0 : Space) (value 1 u) hdiv (fun p : LiftDomain 1 => Z.field p.1) hrep hlocal
  filter_upwards [] with x
  have hx := hlifted_zero (x, 0)
  simpa [EulerMeanCylinderSolenoidal.fieldDerivative_spatial 1 Z.field Z.smooth,
    coordinateDirection, coordinateVector] using hx

end NSFormalization.Section4.A01
