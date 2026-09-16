import NSFormalization.Section4.A01.TameAssembly
import NSFormalization.Section4.A01.CylinderWiring
import NSFormalization.Section4.A01.JointRepresentative
import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A01.PressureRegularity
import NSFormalization.Section4.A04.ZeroSolution

/-! Unconditional local constructor. The horizon is supplied by base-order local
existence; positivity alone does not supply a solution on an arbitrary prescribed horizon. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- All analytic inputs are discharged on the base solution's horizon. -/
theorem constructor_of_base {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (f : A02.SpaceTimeField) (hf : D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7))
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath (C01.forcePath (S := S) hf)
        (C01.forcePath_jetLp_continuous (S := S) hf) 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t) :
    ∃ (velocity : A02.SpaceTimeField)
      (w : A02.ClassicalSolutionR ν (fun x : Space => velocity (0, x)) f S),
      w.velocity = velocity := by
  let F := C01.forcePath (S := S) hf
  let hF := C01.forcePath_jetLp_continuous (S := S) hf
  let R := aprioriRadius a F hF ‖u₆‖ E (fun q => tameAssemblyA q^2/(4*ν))
  have hb := hb_of_base'' hν hS.le a ha F hF u₆ le_rfl h₆
  obtain ⟨U, _hU0, hpairs, hpaths⟩ := cylinderPair_of_bounds hf hν hS a ha R hb
  obtain ⟨velocity, hslice, hc3⟩ := exists_joint_smooth_representative hS U hpaths
  obtain ⟨G, hG_int, hG_smooth, hG_slices⟩ :=
    pressureSupply_of_pieces (le_refl 6) hν hS f hf a ha U hpairs hpaths velocity hslice hc3
  obtain ⟨u, hU, hdiv, _hinv, _hduh⟩ := hpairs 6 (le_refl 6)
  obtain ⟨w, hw, _hslice⟩ := carrierConstructor_of_localTheory hS u U hU hdiv f
    velocity hslice (hpaths 0) hc3 G hG_int ⟨hG_smooth, hG_slices⟩
  exact ⟨velocity, w, hw⟩

/-- A01 local-existence milestone from force regularity, solenoidal smooth data,
viscosity positivity and a positive upper bound on the local horizon only. -/
theorem a01_constructor_unconditional {ν Smax : ℝ} (hν : 0 < ν) (hSmax : 0 < Smax)
    (f : A02.SpaceTimeField) (hf : D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) :
    ∃ S : ℝ, 0 < S ∧ S ≤ Smax ∧
      ∃ (velocity : A02.SpaceTimeField)
        (w : A02.ClassicalSolutionR ν (fun x : Space => velocity (0, x)) f S),
        w.velocity = velocity := by
  obtain ⟨S, hS, hSSmax, u, _hR, _hu0, hu⟩ :=
    exists_local_quadratic_mild 1 6 ν hν Smax hSmax
      (ordinarySobolev 7 a.toLp a.translation_contDiff)
      (coefficients 1 (le_refl 6) (sobolevPath (C01.forcePath (S := Smax) hf)
        (C01.forcePath_jetLp_continuous (S := Smax) hf) 6))
  exact ⟨S, hS, hSSmax, constructor_of_base hν hS f hf a ha u hu⟩

#print axioms constructor_of_base
#print axioms a01_constructor_unconditional

example : ∃ S : ℝ, 0 < S ∧ S ≤ 1 ∧
    ∃ (velocity : A02.SpaceTimeField)
      (w : A02.ClassicalSolutionR 1 (fun x : Space => velocity (0, x)) 0 S),
      w.velocity = velocity :=
  a01_constructor_unconditional (by norm_num) (by norm_num) 0 A04.memForceR_zero
    SmoothL2Field.zeroField
    (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField])

end NSFormalization.Section4.A01
