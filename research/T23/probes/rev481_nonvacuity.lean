import NSFormalization.Section3.T23.CorrectionEstimates

noncomputable section
namespace Rev481

open Set
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T23

/-- A positive cutoff gives a concrete admissible scale at which the actual
correction energy estimate applies; the quantified scale interval is not empty. -/
example {ν : ℝ} {u v : VelocityField} {K : Set Space}
    (C : WholeSpaceCorrectionAPI ν u K)
    (heq : EqOn v C.v (Ioo (0 : ℝ) (C.T + C.δ) ×ˢ Metric.ball C.x₀ C.r))
    {e : ℝ} (hepos : 0 < e) (he : e ≤ C.ε₀) :
    let D := localCorrectionData v C.x₀ C.T C.θ C.η C.plateau C.θRadius e
    ∃ ε ∈ Ioc (0 : ℝ) e, ∃ B : ℝ, 0 ≤ B ∧
      NSFormalization.Section3.T24.energyENorm C.T (D.correction ε) ≤
        ENNReal.ofReal (B * ε ^ ((3 : ℝ) / 2)) := by
  obtain ⟨B, hB, hb⟩ := C.local_energy_bound heq he
  exact ⟨e, ⟨hepos, le_rfl⟩, B, hB, (hb e ⟨hepos, le_rfl⟩).1⟩

end Rev481
