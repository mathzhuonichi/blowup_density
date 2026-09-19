import Contracts.V1.CriticalRegularityT
import Bindings.TorusLocalTheory
import Bindings.MeanZeroCalculus
import NSFormalization.Section3.T20.Assembly

/-!
# Binding for the T20 critical-regularity contract

Every T20-specific restated definition is checked by `rfl`.  Fields involving
the separately restated `ClassicalSolutionT` are transported through
`Bindings.TorusLocalTheory.ofContract`; the maximal-lifespan conclusion uses
the existing propositional bridge `maximalLifespanT_eq`.
-/

noncomputable section

namespace BlowupDensity.Bindings.CriticalRegularityT

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.MeanZeroCalculus
open BlowupDensity.Contracts.V1.CriticalRegularityT
open scoped ContDiff ENNReal BigOperators

/-! ## Definitional drift guards -/

theorem meanPathT_eq (g : SpaceTimeField) (t : ℝ) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.meanPathT g t =
      NSFormalization.Section3.T20.meanPathT g t := rfl

theorem meanFreeVelocity_eq (g u : SpaceTimeField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.meanFreeVelocity g u =
      NSFormalization.Section3.T20.meanFreeVelocity g u := rfl

theorem meanFreeForce_eq (g : SpaceTimeField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.meanFreeForce g =
      NSFormalization.Section3.T20.meanFreeForce g := rfl

theorem constantTransportT_eq (m : ℝ → Space) (v : SpaceTimeField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.constantTransportT m v =
      NSFormalization.Section3.T20.constantTransportT m v := rfl

theorem constantTransportSpatialT_eq (m : Space) (v : SpatialField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.constantTransportSpatialT m v =
      NSFormalization.Section3.T20.constantTransportSpatialT m v := rfl

theorem meanForceIntegralT_eq (g : SpaceTimeField) (t : ℝ) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.meanForceIntegralT g t =
      NSFormalization.Section3.T20.meanForceIntegralT g t := rfl

theorem criticalY_eq (v : SpaceTimeField) (t : ℝ) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.criticalY v t =
      NSFormalization.Section3.T20.criticalY v t := rfl

theorem criticalZ_eq (v : SpaceTimeField) (t : ℝ) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.criticalZ v t =
      NSFormalization.Section3.T20.criticalZ v t := rfl

theorem criticalB_eq (h : SpaceTimeField) (t : ℝ) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.criticalB h t =
      NSFormalization.Section3.T20.criticalB h t := rfl

theorem criticalBIntegral_eq (h : SpaceTimeField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.criticalBIntegral h =
      NSFormalization.Section3.T20.criticalBIntegral h := rfl

theorem criticalRho_eq (g : SpaceTimeField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.criticalRho g =
      NSFormalization.Section3.T20.criticalRho g := rfl

theorem gradientSqT_eq (v : SpatialField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.gradientSqT v =
      NSFormalization.Section3.T20.gradientSqT v := rfl

theorem laplacianSqT_eq (v : SpatialField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.laplacianSqT v =
      NSFormalization.Section3.T20.laplacianSqT v := rfl

theorem lTwoSqT_eq (h : SpatialField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.lTwoSqT h =
      NSFormalization.Section3.T20.lTwoSqT h := rfl

theorem meanFreeForceLTwoSqIntegral_eq (h : SpaceTimeField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.meanFreeForceLTwoSqIntegral h =
      NSFormalization.Section3.T20.meanFreeForceLTwoSqIntegral h := rfl

theorem meanModeCriterionIntegral_eq (S : ℝ) (g u : SpaceTimeField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.meanModeCriterionIntegral S g u =
      NSFormalization.Section3.T20.meanModeCriterionIntegral S g u := rfl

theorem periodicPairing_eq (v w : SpatialField) :
    BlowupDensity.Contracts.V1.CriticalRegularityT.periodicPairing v w =
      NSFormalization.Section3.T20.periodicPairing v w := rfl

/-! ## Transport of the canonical record -/

/-- The canonical 23-field record, transported into registered vocabulary. -/
noncomputable def criticalRegularityT :
    BlowupDensity.Contracts.V1.CriticalRegularityT.CriticalRegularityTAPI where
  c := NSFormalization.Section3.T20.criticalRegularityT.c
  hc := NSFormalization.Section3.T20.criticalRegularityT.hc
  C₀ := NSFormalization.Section3.T20.criticalRegularityT.C₀
  C₀_pos := NSFormalization.Section3.T20.criticalRegularityT.C₀_pos
  C₁ := NSFormalization.Section3.T20.criticalRegularityT.C₁
  C₁_pos := NSFormalization.Section3.T20.criticalRegularityT.C₁_pos
  CH1 := NSFormalization.Section3.T20.criticalRegularityT.CH1
  CH1_pos := NSFormalization.Section3.T20.criticalRegularityT.CH1_pos
  Ccriterion := NSFormalization.Section3.T20.criticalRegularityT.Ccriterion
  hCcriterion := NSFormalization.Section3.T20.criticalRegularityT.hCcriterion
  c_lt_C₀ := NSFormalization.Section3.T20.criticalRegularityT.c_lt_C₀
  c_lt_C₁ := NSFormalization.Section3.T20.criticalRegularityT.c_lt_C₁
  reductionRegular := by
    intro ν hν g hg T w t ht
    exact NSFormalization.Section3.T20.criticalRegularityT.reductionRegular
      ν hν g hg T (TorusLocalTheory.ofContract w) t ht
  meanBound := NSFormalization.Section3.T20.criticalRegularityT.meanBound
  meanFreeEquation := by
    intro ν hν g hg T w t ht x
    exact NSFormalization.Section3.T20.criticalRegularityT.meanFreeEquation
      ν hν g hg T (TorusLocalTheory.ofContract w) t ht x
  constantTransportSkew :=
    NSFormalization.Section3.T20.criticalRegularityT.constantTransportSkew
  constantTransportCommutesLambda :=
    NSFormalization.Section3.T20.criticalRegularityT.constantTransportCommutesLambda
  criticalEnergy := by
    intro ν hν g hg T w t ht
    exact NSFormalization.Section3.T20.criticalRegularityT.criticalEnergy
      ν hν g hg T (TorusLocalTheory.ofContract w) t ht
  bIntegral := NSFormalization.Section3.T20.criticalRegularityT.bIntegral
  yBound := by
    intro ν hν g hg hsmall T w t ht
    exact NSFormalization.Section3.T20.criticalRegularityT.yBound
      ν hν g hg hsmall T (TorusLocalTheory.ofContract w) t ht
  hOneEnergy := by
    intro ν hν g hg hsmall T w t ht
    exact NSFormalization.Section3.T20.criticalRegularityT.hOneEnergy
      ν hν g hg hsmall T (TorusLocalTheory.ofContract w) t ht
  continuationBound := by
    intro ν hν g hg hsmall T w S hS hST
    exact NSFormalization.Section3.T20.criticalRegularityT.continuationBound
      ν hν g hg hsmall T (TorusLocalTheory.ofContract w) S hS hST
  globalRegularity := by
    intro ν hν g hg hsmall
    rw [TorusLocalTheory.maximalLifespanT_eq]
    exact NSFormalization.Section3.T20.criticalRegularityT.globalRegularity
      ν hν g hg hsmall

theorem criticalRegularityStatement_holds :
    BlowupDensity.Contracts.V1.CriticalRegularityT.criticalRegularityStatement :=
  ⟨criticalRegularityT⟩

/-- The canonical nonzero compact-force witness in registered vocabulary. -/
theorem criticalRegularity_nonvacuous :
    ∃ (ν : ℝ) (g : SpaceTimeField) (_hg : g ∈ forceClassT),
      0 < ν ∧ g (2, 0) ≠ 0 ∧
        BlowupDensity.Contracts.V1.CriticalRegularityT.criticalRho g <
          ENNReal.ofReal (criticalRegularityT.c * ν) ∧
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ := by
  obtain ⟨ν, g, hg, hν, hgne, hsmall, hglobal⟩ :=
    NSFormalization.Section3.T20.criticalRegularityT_nonvacuous
  refine ⟨ν, g, hg, hν, hgne, hsmall, ?_⟩
  rw [TorusLocalTheory.maximalLifespanT_eq]
  exact hglobal

end BlowupDensity.Bindings.CriticalRegularityT

namespace BlowupDensity.Bindings

/-- The registered critical periodic regularity package. -/
noncomputable def criticalRegularityT :
    BlowupDensity.Contracts.V1.CriticalRegularityT.CriticalRegularityTAPI :=
  CriticalRegularityT.criticalRegularityT

end BlowupDensity.Bindings
