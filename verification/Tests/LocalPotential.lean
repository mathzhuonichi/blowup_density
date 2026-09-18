import Contracts.V1.LocalPotential
import Bindings.LocalPotential
import TestSupport.Axioms
noncomputable section
namespace BlowupDensity.Tests
open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Bindings
 theorem checkedLocalPotential : Contracts.V1.localPotentialStatement := Bindings.localPotential
run_cmd TestSupport.checkAxioms ``checkedLocalPotential
example : Contracts.V1.localPotentialStatement := checkedLocalPotential
example (x₀ : Space) {r T δ : ℝ} (hr : 0 < r) (hr2 : r < 1 / 2) (hT : 0 < T) (hδ : 0 < δ) :
    ∃ D : Contracts.V1.CutoffData, Contracts.V1.LocalPotentialAPI (fun _ => (0 : Space)) (fun _ => (0 : Space)) ({0} : Set Space) x₀ r T δ D := by
  have hU : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => (fun _ => (0 : Space)) (t,x)) ⊆ ({0} : Set Space) := by
    intro t ht; rw [NSFormalization.Section3.T16.tsupport_zero_slice]; exact empty_subset _
  obtain ⟨D,hD⟩ := NSFormalization.Section3.T16.localPotential_zero (fun _ => (0 : Space)) ({0} : Set Space) x₀ r T δ hr hr2 hT hδ isCompact_singleton hU
  exact ⟨CutoffData.toContract D, api_toContract hD⟩
end BlowupDensity.Tests
