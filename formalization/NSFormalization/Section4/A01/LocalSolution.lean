import NSFormalization.Section4.A01.TameAssembly
import NSFormalization.Section4.A01.CylinderWiring
import NSFormalization.Section4.A01.JointRepresentative
import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A01.PressureRegularity
import NSFormalization.Section4.D01.DatumToJets

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

/-- Change only the named initial datum; velocity and pressure are preserved. -/
def transport_initial {ν S : ℝ} {a b : A02.SpatialField} {f : A02.SpaceTimeField}
    (w : A02.ClassicalSolutionR ν a f S) (hab : a = b) :
    A02.ClassicalSolutionR ν b f S :=
  { w with initial := fun x => (w.initial x).trans (congrFun hab x) }

/-- The manuscript initial class supplies the actual smooth solenoidal carrier. -/
theorem smoothL2_of_initialClassR {a : A02.SpatialField} (ha : a ∈ A02.initialClassR) :
    ∃ A : SmoothL2Field Space, A.field = a ∧
      ∀ x, EulerSmoothLimit.divergence A.field x = 0 := by
  obtain ⟨A, hA⟩ := D01.exists_smoothL2Field_of_memHInfty ha.1.1 ha.1.2
  refine ⟨A, hA, ?_⟩
  intro x
  rw [hA]
  simpa only [EulerSmoothLimit.divergence_eq_coordinate_sum,
    NavierStokes.ProblemStatement.spatialDivergence,
    NavierStokes.ProblemStatement.spatialDerivative,
    NavierStokes.ProblemStatement.coordinateVector] using ha.2 x

/-- All analytic inputs are discharged on the base solution's horizon. -/
theorem solution_of_base {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (f : A02.SpaceTimeField) (hf : D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7))
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath (C01.forcePath (S := S) hf)
        (C01.forcePath_jetLp_continuous (S := S) hf) 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t) :
    Nonempty (A02.ClassicalSolutionR ν a.field f S) := by
  let F := C01.forcePath (S := S) hf
  let hF := C01.forcePath_jetLp_continuous (S := S) hf
  let R := aprioriRadius a F hF ‖u₆‖ E (fun q => tameAssemblyA q^2/(4*ν))
  have hb := hb_of_base'' hν hS.le a ha F hF u₆ le_rfl h₆
  obtain ⟨U, hU0, hpairs, hpaths⟩ := cylinderPair_of_bounds hf hν hS a ha R hb
  obtain ⟨velocity, hslice, hc3⟩ := exists_joint_smooth_representative hS U hpaths
  obtain ⟨G, hG_int, hG_smooth, hG_slices⟩ :=
    pressureSupply_of_pieces (le_refl 6) hν hS f hf a ha U hpairs hpaths velocity hslice hc3
  obtain ⟨u, hU, hdiv, _hinv, _hduh⟩ := hpairs 6 (le_refl 6)
  obtain ⟨w, hw, _hslice⟩ := carrierConstructor_of_localTheory hS u U hU hdiv f
    velocity hslice (hpaths 0) hc3 G hG_int ⟨hG_smooth, hG_slices⟩
  have heq : (fun x => velocity (0, x)) = a.field := by
    apply ((D01.contDiff_slice hc3 ⟨le_rfl, hS⟩).continuous.ae_eq_iff_eq
      volume a.smooth.continuous).mp
    have hs := hslice ⟨0, le_rfl, hS.le⟩
    rw [hU0] at hs
    exact hs.trans a.toLp_ae
  exact ⟨transport_initial w heq⟩

/-- A01 local-existence milestone from force regularity, solenoidal smooth data,
viscosity positivity and a positive upper bound on the local horizon only. -/
theorem exists_localSolution_smooth {ν Smax : ℝ} (hν : 0 < ν) (hSmax : 0 < Smax)
    (f : A02.SpaceTimeField) (hf : D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) :
    ∃ S : ℝ, 0 < S ∧ S ≤ Smax ∧
      Nonempty (A02.ClassicalSolutionR ν a.field f S) := by
  obtain ⟨S, hS, hSSmax, u, _hR, _hu0, hu⟩ :=
    exists_local_quadratic_mild 1 6 ν hν Smax hSmax
      (ordinarySobolev 7 a.toLp a.translation_contDiff)
      (coefficients 1 (le_refl 6) (sobolevPath (C01.forcePath (S := Smax) hf)
        (C01.forcePath_jetLp_continuous (S := Smax) hf) 6))
  exact ⟨S, hS, hSSmax, solution_of_base hν hS f hf a ha u hu⟩

/-- Local existence for precisely the manuscript initial class. -/
theorem exists_localSolution {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (hν : 0 < ν) (ha : a ∈ A02.initialClassR) (hf : D01.MemForceR f) :
    ∃ S : ℝ, 0 < S ∧ Nonempty (A02.ClassicalSolutionR ν a f S) := by
  obtain ⟨A, hA, hdiv⟩ := smoothL2_of_initialClassR ha
  obtain ⟨S, hS, _, hw⟩ := exists_localSolution_smooth hν (by norm_num : (0:ℝ) < 1)
    f hf A hdiv
  rw [hA] at hw
  exact ⟨S, hS, hw⟩

/-- Total common horizon; invalid inputs receive the harmless value one. -/
def localHorizon (ν : ℝ) (a : A02.SpatialField) (f : A02.SpaceTimeField) : ℝ := by
  classical
  exact if h : 0 < ν ∧ a ∈ A02.initialClassR ∧ D01.MemForceR f then
    Classical.choose (exists_localSolution h.1 h.2.1 h.2.2)
  else 1

/-- The selected horizon carries a solution for every admissible input. -/
theorem localHorizon_spec {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (hν : 0 < ν) (ha : a ∈ A02.initialClassR) (hf : D01.MemForceR f) :
    0 < localHorizon ν a f ∧
      Nonempty (A02.ClassicalSolutionR ν a f (localHorizon ν a f)) := by
  rw [localHorizon, dite_eq_left (show 0 < ν ∧ a ∈ A02.initialClassR ∧ D01.MemForceR f from ⟨hν, ha, hf⟩)]
  exact Classical.choose_spec (exists_localSolution hν ha hf)

/-- Positivity of the common chosen horizon. -/
theorem localHorizon_pos {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (hν : 0 < ν) (ha : a ∈ A02.initialClassR) (hf : D01.MemForceR f) :
    0 < localHorizon ν a f := (localHorizon_spec hν ha hf).1

/-- Shared solution data for subsequent regularity and horizon lanes. -/
def localSolution (ν : ℝ) (a : A02.SpatialField) (f : A02.SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ A02.initialClassR) (hf : D01.MemForceR f) :
    A02.ClassicalSolutionR ν a f (localHorizon ν a f) :=
  Classical.choice (localHorizon_spec hν ha hf).2

end NSFormalization.Section4.A01
