import NSFormalization.Section4.R44.EnergyIdentity

/-! Lane 222: complete declaration audit and a closed zero-solution instance. -/
noncomputable section
open Set NavierStokes.ProblemStatement
open NSFormalization.Section4
open NSFormalization.Section4.R44

#print axioms NSFormalization.Section4.R44.energyDatum
#print axioms NSFormalization.Section4.R44.energyDatum_eq
#print axioms NSFormalization.Section4.R44.energyDatum_isDatum
#print axioms NSFormalization.Section4.R44.energyDatum_eq_lower
#print axioms NSFormalization.Section4.R44.energyVelocity
#print axioms NSFormalization.Section4.R44.energyVelocity_isDatum
#print axioms NSFormalization.Section4.R44.energyVelocity_smooth
#print axioms NSFormalization.Section4.R44.jWeightDatumPath
#print axioms NSFormalization.Section4.R44.jWeightDatumPath_force_eq_lower
#print axioms NSFormalization.Section4.R44.hasDerivAt_Y_sq
#print axioms NSFormalization.Section4.R44.energyVelocity_momentum
#print axioms NSFormalization.Section4.R44.inner_eq_jPairing
#print axioms NSFormalization.Section4.R44.half_laplacian_component
#print axioms NSFormalization.Section4.R44.laplacian_jPairing
#print axioms NSFormalization.Section4.R44.pressure_jPairing_zero
#print axioms NSFormalization.Section4.R44.energyAdvectionJPairing
#print axioms NSFormalization.Section4.R44.energy_identity_of_data
#print axioms NSFormalization.Section4.R44.energy_identity
#print axioms NSFormalization.Section4.R44.energyDatum_zero
#print axioms NSFormalization.Section4.R44.zero_energy_terms

example : HasDerivAt
    (fun r => Y (fun x => (A04.zeroSol 1 1 (by norm_num) (by norm_num)).velocity (r,x)) ^ 2)
    0 (1/2) := by
  have ht : (1/2 : ℝ) ∈ Ioo 0 1 := by constructor <;> norm_num
  have h := energy_identity (by norm_num : (0 : ℝ) < 1) A04.memForceR_zero
    (A04.zeroSol 1 1 (by norm_num) (by norm_num)) ht
  obtain ⟨_, hz, hn, hf⟩ := zero_energy_terms 1 1 (by norm_num) (by norm_num)
    (t := 1/2) ⟨ht.1.le, ht.2⟩
  rw [hz, hn, hf] at h
  simpa using h
