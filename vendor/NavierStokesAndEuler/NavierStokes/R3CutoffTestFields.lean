import NavierStokes.R3SpaceTimeCalculus
import NavierStokes.R3CompactEnergy
import NavierStokes.R3CompactParametricIntegral

/-!
# Cutoff vector tests and continuity of the physical flux
-/

noncomputable section
namespace NavierStokes.R3CutoffTestFields

open Set Filter MeasureTheory ProblemStatement
open R3SpaceTime R3WeakPressure R3SpaceTimeCalculus R3CompactEnergy
open scoped ContDiff

def weightedVelocity (χ : Space → ℝ) (w : VelocityField) : VelocityField :=
  fun tx => χ tx.2 • w tx

theorem weightedVelocity_smooth {s : Set ℝ} {χ : Space → ℝ} {w : VelocityField}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiffOn ℝ ∞ w (s ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (weightedVelocity χ w) (s ×ˢ (univ : Set Space)) :=
  (hχ.comp contDiff_snd).contDiffOn.smul hw

theorem divergence_weighted {χ : Space → ℝ} {w : VelocityField} {t : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ (fun x : Space => w (t, x))) (x : Space) :
    spatialDivergence (weightedVelocity χ w) t x =
      fderiv ℝ χ x (w (t, x)) + χ x * spatialDivergence w t x := by
  have he : spatialDerivative (weightedVelocity χ w) t x =
      χ x • fderiv ℝ (fun y => w (t, y)) x + (fderiv ℝ χ x).smulRight (w (t, x)) :=
    ((hχ.differentiable (by simp) x).hasFDerivAt.smul (hw.differentiable (by simp) x).hasFDerivAt).fderiv
  unfold spatialDivergence
  rw [PeriodicUniqueness.fderiv_apply_eq_sum]
  simp only [he, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hh : (∑ i : Fin 3, fderiv ℝ χ x (coordinateVector i) * w (t, x) i) =
      ∑ i : Fin 3, w (t, x) i * fderiv ℝ χ x (coordinateVector i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hh]
  dsimp only [spatialDerivative]
  ring

theorem test_divergence {s : Set ℝ} (hs : IsOpen s) {χ : Space → ℝ} {w : VelocityField}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiffOn ℝ ∞ w (s ×ˢ (univ : Set Space)))
    (hd : ∀ t ∈ s, ∀ x, spatialDivergence w t x = 0) {t : ℝ} (ht : t ∈ s) (x : Space) :
    functionDivergence (liftVelocity (weightedVelocity χ w)) (pack t x) =
      (fderiv ℝ χ x (w (t, x)) : ℝ) := by
  rw [liftVelocity_divergence hs (weightedVelocity_smooth hχ hw) ht,
    divergence_weighted hχ (slice_smooth hw ht), hd t ht x, mul_zero, add_zero]

theorem test_support (χ : Space → ℝ) (w : VelocityField) (i : Fin 3) (z : Domain)
    (hx : spaceProj z ∉ tsupport χ) : liftVelocity (weightedVelocity χ w) i z = 0 := by
  simp [liftVelocity, liftScalar, weightedVelocity, image_eq_zero_of_notMem_tsupport hx]

theorem spatialDerivative_joint {w : VelocityField} {t : ℝ} {x : Space}
    (hw : DifferentiableAt ℝ w (t, x)) :
    spatialDerivative w t x = (fderiv ℝ w (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
  (hw.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv

theorem spatialPartial_continuousOn {s : Set ℝ} (hs : IsOpen s) {w : VelocityField}
    (hw : ContDiffOn ℝ ∞ w (s ×ˢ (univ : Set Space))) (i : Fin 3) :
    ContinuousOn (fun tx : SpaceTime => spatialDerivative w tx.1 tx.2 (coordinateVector i))
      (s ×ˢ (univ : Set Space)) := by
  have hc := (hw.continuousOn_fderiv_of_isOpen (hs.prod isOpen_univ) (by simp)).clm_apply
    (show ContinuousOn (fun _ : SpaceTime => ((0 : ℝ), coordinateVector i)) (s ×ˢ univ) from continuousOn_const)
  apply hc.congr
  intro tx htx
  have hd := (hw.contDiffAt ((hs.prod isOpen_univ).mem_nhds htx)).differentiableAt (by simp)
  dsimp only
  rw [spatialDerivative_joint hd]
  rfl

theorem dissipation_continuousOn {s : Set ℝ} (hs : IsOpen s) {χ : Space → ℝ} {w : VelocityField}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hw : ContDiffOn ℝ ∞ w (s ×ˢ (univ : Set Space))) :
    ContinuousOn (fun t => dissipation χ (fun x => w (t, x))) s := by
  apply continuousOn_finsetSum
  intro i _
  apply R3CompactParametricIntegral.integral_continuousOn_open hs hc
    ((hχ.comp continuous_snd).continuousOn.mul ((spatialPartial_continuousOn hs hw i).norm.pow 2))
  intro t ht x hx
  simp [image_eq_zero_of_notMem_tsupport hx]

theorem pressureFlux_continuousOn {s : Set ℝ} (hs : IsOpen s) {χ : Space → ℝ}
    {w : VelocityField} {p : PressureField} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hw : ContDiffOn ℝ ∞ w (s ×ˢ (univ : Set Space)))
    (hp : ContDiffOn ℝ ∞ p (s ×ˢ (univ : Set Space))) :
    ContinuousOn (fun t => pressureFlux χ (fun x => w (t, x)) (fun x => p (t, x))) s := by
  have hD : ContinuousOn (fun tx : SpaceTime => fderiv ℝ χ tx.2 (w tx)) (s ×ˢ univ) :=
    (((hχ.continuous_fderiv (by simp)).comp continuous_snd).continuousOn).clm_apply hw.continuousOn
  apply R3CompactParametricIntegral.integral_continuousOn_open hs hc (hD.mul hp.continuousOn)
  intro t ht x hx
  simp [fderiv_of_notMem_tsupport ℝ hx]

end NavierStokes.R3CutoffTestFields
