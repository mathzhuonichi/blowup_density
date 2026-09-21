import Contracts.V3.LocalForceTheory
import Bindings.ContinuationV2
import Bindings.TorusLocalTheory
import NSFormalization.Section4.A01.LocalForceTheory
import NSFormalization.Section3.T11.LocalForceTheory

/-! Fieldwise transport of local theory for forces without global time bounds. -/
noncomputable section
namespace BlowupDensity.Bindings.LocalForceTheory
open Contracts.V3.LocalForceTheory

theorem smoothForceR_eq : SmoothForceR = NSFormalization.Section4.A01.SmoothForceR := rfl

theorem smoothForceT_eq : SmoothForceT = NSFormalization.Section3.T11.SmoothForceT := rfl

theorem localForceTheory : LocalForceTheoryAPI where
  localR := by
    intro ν hν a ha f hf
    obtain ⟨T, hT, w, hr⟩ := NSFormalization.Section4.A01.exists_local_regular_of_smoothForceR ν hν a ha f hf
    exact ⟨T, hT, maximalPartial_ofA02 w, hr.sobolev_smooth,
      hr.pressure_recovery, hr.projected, hr.pressure_potential⟩
  maximalR := by
    intro ν hν a ha f hf
    obtain ⟨u, p, hm⟩ := NSFormalization.Section4.A01.exists_maximal_of_smoothForceR ν hν a ha f hf
    exact ⟨u, p, (continuationV2_isMaximalSolution_iff ν a f u p).mp hm⟩
  uniqueR := by
    intro ν hν a f T₁ T₂ w₁ w₂ t ht x
    exact NSFormalization.Section4.A02.velocity_unique_core hν
      (uniqueness_toA02 w₁) (uniqueness_toA02 w₂) t ht x
  pressureGaugeR := by
    intro ν hν a f T₁ T₂ w₁ w₂
    exact NSFormalization.Section4.A02.pressure_gauge_core hν
      (uniqueness_toA02 w₁) (uniqueness_toA02 w₂)
  continuationR := by
    intro ν hν a ha f hf S hS u p hu hi
    obtain ⟨R, hR, w, hw⟩ := NSFormalization.Section4.A01.extends_of_smoothForceR
      ν hν a ha f hf S hS u p ((continuationV2_solvesBelow_iff ν a f S u p).mp hu) hi
    exact ⟨R, hR, maximalPartial_ofA02 w, hw⟩
  localT := by
    intro ν hν a ha f hf
    obtain ⟨T, hT, w, hr⟩ := NSFormalization.Section3.T11.exists_local_regular_smoothForceT ν hν a ha f hf
    exact ⟨T, hT, TorusLocalTheory.toContract w, hr.sobolev_smooth,
      hr.pressure_poisson, hr.projected⟩
  maximalT := by
    intro ν hν a ha f hf
    obtain ⟨u, p, hm⟩ := NSFormalization.Section3.T11.exists_maximal_smoothForceT ν hν a ha f hf
    exact ⟨u, p, (TorusLocalTheory.isMaximalPeriodicSolution_eq ν a f u p).symm ▸ hm⟩
  uniqueT := by
    intro ν hν a f T₁ T₂ w₁ w₂ t ht x
    exact ⟨NSFormalization.Section3.T11.velocity_unique_local hν
      (TorusLocalTheory.ofContract w₁) (TorusLocalTheory.ofContract w₂) t ht x,
      NSFormalization.Section3.T11.pressure_unique_local hν
        (TorusLocalTheory.ofContract w₁) (TorusLocalTheory.ofContract w₂) t ht x⟩
  continuationT := by
    intro ν hν a f hf S hS u p hu hi
    rw [TorusLocalTheory.extendsBeyondT_eq]
    exact NSFormalization.Section3.T11.extendsBeyond_locallySmoothForceT ν hν a f hf S hS u p
      (TorusLocalTheory.solvesBelowT_eq ν a f S u p ▸ hu) hi

end BlowupDensity.Bindings.LocalForceTheory
