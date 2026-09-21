import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A04.ZeroSolution
import Euler.OrdinaryCauchyInterpolation
import Euler.SmoothL2Series

/-! The fully concrete zero cylinder pair satisfies the scoped lane-189
`PressureSupply` proposition. -/

noncomputable section

namespace Rev180PressureSupplyZero

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerOrdinarySobolev EulerSmoothL2Series
open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerSmoothFieldSobolevTime
open EulerQuadraticSource EulerVolterraConvolution
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

private theorem canonical_zero_initial (q : ℕ) :
    ordinarySobolev q
      (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
      (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm
  · refine (ordinarySobolev_norm_le_tensor
      (SmoothL2Field.zeroField : SmoothL2Field Space) q).trans ?_
    simp [tensorNorm, zeroField_jet]
  · exact norm_nonneg _

private theorem canonical_zero_force (q : ℕ) :
    sobolevPath
      (NSFormalization.Section4.C01.forcePath (S := (1 : ℝ))
        NSFormalization.Section4.A04.memForceR_zero)
      (NSFormalization.Section4.C01.forcePath_jetLp_continuous (S := (1 : ℝ))
        NSFormalization.Section4.A04.memForceR_zero) q = 0 := by
  apply ContinuousMap.ext
  intro t
  apply norm_eq_zero.mp
  apply le_antisymm
  · refine (ordinarySobolev_norm_le_tensor
      (NSFormalization.Section4.C01.forcePath (S := (1 : ℝ))
        NSFormalization.Section4.A04.memForceR_zero t) q).trans ?_
    have hpath : NSFormalization.Section4.C01.forcePath (S := (1 : ℝ))
        NSFormalization.Section4.A04.memForceR_zero t =
        (SmoothL2Field.zeroField : SmoothL2Field Space) := by
      unfold NSFormalization.Section4.C01.forcePath
        NSFormalization.Section4.C01.forceSliceField SmoothL2Field.zeroField
      rfl
    rw [hpath]
    simp [tensorNorm, zeroField_jet]
  · exact norm_nonneg _

example :
    let U : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2) := 0
    let velocity : SpaceTimeField := 0
    ∃ (hpairs : ∀ p (hp : 6 ≤ p),
        ∃ u : C(Icc (0 : ℝ) 1, SobolevSpace 1 (p + 1)),
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t,
            sobolevTranslation 1 (p + 1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 1 (by norm_num) (by norm_num) le_rfl
            (coefficients 1 hp
              (sobolevPath
                (NSFormalization.Section4.C01.forcePath (S := (1 : ℝ))
                  NSFormalization.Section4.A04.memForceR_zero)
                (NSFormalization.Section4.C01.forcePath_jetLp_continuous
                  (S := (1 : ℝ)) NSFormalization.Section4.A04.memForceR_zero) p))
            (ordinarySobolev (p + 1)
              (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
              (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff) u t)
      (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) 1) ∧
        ∀ t : Icc (0 : ℝ) 1, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
      (hslice : ∀ t : Icc (0 : ℝ) 1,
        (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
      (hc3 : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space))),
      PressureSupply (show 6 ≤ 6 by omega) (by norm_num) (by norm_num)
        (0 : SpaceTimeField) NSFormalization.Section4.A04.memForceR_zero
        (SmoothL2Field.zeroField : SmoothL2Field Space)
        (by
          intro x
          rw [show (SmoothL2Field.zeroField : SmoothL2Field Space).field =
            (0 : Space → Space) by rfl, EulerSmoothLimit.divergence, fderiv_zero]
          simp)
        U hpairs hpaths velocity hslice hc3 := by
  dsimp only
  let U : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2) := 0
  let velocity : SpaceTimeField := 0
  have hpairs : ∀ p (hp : 6 ≤ p),
      ∃ u : C(Icc (0 : ℝ) 1, SobolevSpace 1 (p + 1)),
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (p + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 1 (by norm_num) (by norm_num) le_rfl
          (coefficients 1 hp
            (sobolevPath
              (NSFormalization.Section4.C01.forcePath (S := (1 : ℝ))
                NSFormalization.Section4.A04.memForceR_zero)
              (NSFormalization.Section4.C01.forcePath_jetLp_continuous
                (S := (1 : ℝ)) NSFormalization.Section4.A04.memForceR_zero) p))
          (ordinarySobolev (p + 1)
            (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
            (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff) u t := by
    intro p hp
    let u : C(Icc (0 : ℝ) 1, SobolevSpace 1 (p + 1)) := 0
    refine ⟨u, ?_, ?_, ?_, ?_⟩
    · intro t
      change ordinaryLift (0 : EulerMeanSolenoidal.L2) =
        value 1 (0 : SobolevSpace 1 (p + 1))
      rw [map_zero]
      rfl
    · intro t
      change (0 : LiftL2 1) ∈ divergenceFreeSpace 1 1 0
      exact Submodule.zero_mem _
    · intro θ t
      change sobolevTranslation 1 (p + 1) (0, θ)
        (0 : SobolevSpace 1 (p + 1)) = 0
      exact map_zero _
    · intro t
      have hu0 := canonical_zero_initial (p + 1)
      have hf0 := canonical_zero_force p
      change (0 : SobolevSpace 1 (p + 1)) = quadraticDuhamel 1 1 (by norm_num)
        (by norm_num) le_rfl _ _ 0 t
      rw [hu0, hf0]
      simp [quadraticDuhamel, source_eq]
  have hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) 1) ∧
      ∀ t : Icc (0 : ℝ) 1, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
    intro j m
    refine ⟨fun _ => 0, contDiffOn_const, ?_⟩
    intro t
    apply IsSobolevDatum.congr_field (isSobolevDatum_zero (m : ℝ))
    exact (Lp.coeFn_zero Space 2 volume).symm
  have hslice : ∀ t : Icc (0 : ℝ) 1,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t) := by
    intro t
    change (0 : Space → Space) =ᵐ[volume] ⇑(0 : EulerMeanSolenoidal.L2)
    exact (Lp.coeFn_zero Space 2 volume).symm
  have hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) := contDiffOn_const
  refine ⟨hpairs, hpaths, hslice, hc3, ?_⟩
  dsimp only [PressureSupply]
  refine ⟨0, ?_, contDiffOn_const, ?_⟩
  · intro t ht x
    simp [pressureGradientOfVelocity, momentumResidualOfVelocity,
      NavierStokes.ProblemStatement.advection,
      NavierStokes.ProblemStatement.spatialLaplacian,
      NavierStokes.ProblemStatement.spatialDerivative,
      NavierStokes.ProblemStatement.temporalDerivative]
  · intro t ht
    refine ⟨MemLp.zero', ?_⟩
    change RadialPotential.HasSymmetricJacobian (fun _ : Space => (0 : Space))
    refine ⟨differentiable_const 0, ?_⟩
    intro x i j
    simp

end Rev180PressureSupplyZero
