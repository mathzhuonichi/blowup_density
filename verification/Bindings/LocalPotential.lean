import Contracts.V1.LocalPotential
import NSFormalization.Section3.T16.Assembly

noncomputable section
namespace BlowupDensity.Bindings
open Set MeasureTheory
open BlowupDensity.Contracts.V1

 theorem latticeVector_eq : @Contracts.V1.latticeVector = @NSFormalization.Section3.T16.latticeVector := rfl
 theorem periodicSet_eq : @Contracts.V1.periodicSet = @NSFormalization.Section3.T16.periodicSet := rfl
 theorem periodicScaledPacket_eq : @Contracts.V1.periodicScaledPacket = @NSFormalization.Section3.T16.periodicScaledPacket := rfl
 theorem correctedBackground_eq : @Contracts.V1.correctedBackground = @NSFormalization.Section3.T16.correctedBackground := rfl

def CutoffData.toContract (D : NSFormalization.Section3.T16.CutoffData) : Contracts.V1.CutoffData :=
  ⟨D.θ,D.η,D.plateau,D.θRadius,D.ε₀,D.potential,D.correction⟩
def CutoffData.ofContract (D : Contracts.V1.CutoffData) : NSFormalization.Section3.T16.CutoffData :=
  ⟨D.θ,D.η,D.plateau,D.θRadius,D.ε₀,D.potential,D.correction⟩
theorem CutoffData.of_to (D : NSFormalization.Section3.T16.CutoffData) : CutoffData.ofContract (CutoffData.toContract D) = D := rfl
theorem CutoffData.to_of (D : Contracts.V1.CutoffData) : CutoffData.toContract (CutoffData.ofContract D) = D := rfl

theorem api_toContract {v U : Contracts.V1.Data.SpaceTimeField}
    {K : Set Space} {x₀ : Space} {r T δ : ℝ}
    {D : NSFormalization.Section3.T16.CutoffData}
    (h : NSFormalization.Section3.T16.LocalPotentialAPI v U K x₀ r T δ D) :
    Contracts.V1.LocalPotentialAPI v U K x₀ r T δ (CutoffData.toContract D) :=
  { theta_smooth := h.theta_smooth, theta_compactSupport := h.theta_compactSupport, theta_range := h.theta_range, plateau_open := h.plateau_open, prescribed_subset_plateau := h.prescribed_subset_plateau, theta_one := h.theta_one, theta_radius_pos := h.theta_radius_pos, theta_support := h.theta_support, eta_smooth := h.eta_smooth, eta_compactSupport := h.eta_compactSupport, eta_range := h.eta_range, eta_one := h.eta_one, eta_support := h.eta_support, eps_pos := h.eps_pos, eps_time := h.eps_time, eps_space := h.eps_space, potential_smooth := h.potential_smooth, potential_formula := h.potential_formula, potential_curl := h.potential_curl, correction_formula := h.correction_formula, correction_smooth := h.correction_smooth, correction_periodic := h.correction_periodic, correction_divergence_free := h.correction_divergence_free, correction_support := h.correction_support, correction_support_ball := h.correction_support_ball, correction_cancels := h.correction_cancels }

theorem localPotential : Contracts.V1.localPotentialStatement := by
  intro v U K x₀ r T δ hr hr2 hT hδ hK hper hcont hdiv hUsupp
  obtain ⟨D, hD⟩ := NSFormalization.Section3.T16.localPotential v U K x₀ r T δ hr hr2 hT hδ hK hper hcont hdiv hUsupp
  exact ⟨CutoffData.toContract D, api_toContract hD⟩
end BlowupDensity.Bindings
