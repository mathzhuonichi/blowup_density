import NSFormalization.Source.ForcedCylinderInvariant
import NSFormalization.Source.OrdinaryCylinderDescent
import Euler.SmoothFieldSobolevTime
import Euler.MeanCylinderSolenoidal

/-! Finite-order forced local existence for actual smooth ordinary data,
with a genuine continuous ordinary L2 output and its cylinder mild realization. -/
noncomputable section
namespace NSFormalization.Source.OrdinaryForcedLocal
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open scoped Topology ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The physical classical divergence assumption supplies the source cylinder constraint. -/
theorem initial_divergenceFree (q : ℕ) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) :
    value 1 (ordinarySobolev q a.toLp a.translation_contDiff) ∈ divergenceFreeSpace 1 1 0 := by
  erw [ordinarySobolev_value]
  apply EulerCylinderClassicalSolenoidal.mem_of_classical 1 1 0 (ordinaryLift a.toLp)
    (fun z : LiftDomain 1 => a.field z.1)
    ((ordinaryLift_ae a.toLp).trans
      (ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae a.toLp_ae))
  · intro z
    exact a.smooth.comp (contDiff_const.add contDiff_fst)
  · exact EulerMeanCylinderSolenoidal.lift_classical_divergence 1 1 0 a.field a.smooth ha

/-- Actual physical smooth data give a continuous ordinary L2 local path and
an invariant finite-order cylinder witness satisfying the genuine forced mild equation. -/
theorem exists_local {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous (fun t => (F t).jetLp n)) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
        (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2)),
        ‖u‖ ≤ ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ + 1 ∧
        u ⟨0, le_rfl, hT.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hT.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hT.le hTS
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  obtain ⟨T, hT, hTS, u, hu, hi, hd, hm, hinv⟩ :=
    exists_local_forced_mild_invariant 1 hq hν hS
      (ordinarySobolev (q + 1) a.toLp a.translation_contDiff)
      (initial_divergenceFree (q + 1) a ha) (sobolevPath F hF q)
      (ordinarySobolev_angle (q + 1) a.toLp a.translation_contDiff)
      (fun θ t => ordinarySobolev_angle q (F t).toLp (F t).translation_contDiff θ)
  let U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2) :=
    ⟨fun t => ordinaryValue (q + 1) (u t), (ordinaryValue (q + 1)).continuous.comp u.continuous⟩
  have hl (t : Icc (0 : ℝ) T) : ordinaryLift (U t) = value 1 (u t) :=
    ordinaryValue_lift (by omega) (u t) (fun θ => hinv θ t)
  refine ⟨T, hT, hTS, u, U, hu, hi, ?_, hl, hd, hm, hinv⟩
  apply ordinaryLift.injective
  rw [hl, hi]
  exact ordinarySobolev_value _ _ _

end NSFormalization.Source.OrdinaryForcedLocal
