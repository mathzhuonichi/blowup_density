import NSFormalization.Section3.T20.CriticalEnergy

/-! Transitive axiom audit for T20 unit U8 (`Section3/T20/CriticalEnergy.lean`).
Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`. -/

open NSFormalization.Section3.T20

-- §1  torus Parseval for the real `L²` pairing
#print axioms NSFormalization.Section3.T20.hasSum_periodicPairing

-- §2  the constant-transport drop
#print axioms NSFormalization.Section3.T20.periodicFourierCoeff_fderiv_dir
#print axioms NSFormalization.Section3.T20.re_sum_conj_fderiv_dir_zero

-- §3  the critical frequency energy and its derivative
#print axioms NSFormalization.Section3.T20.hasDerivAt_critFreqEnergy
#print axioms NSFormalization.Section3.T20.homogeneousDatumWeight_half_sq
#print axioms NSFormalization.Section3.T20.homogeneousDatumWeight_three_halves_sq
#print axioms NSFormalization.Section3.T20.abs_critFreqEnergyDeriv_le_freq
#print axioms NSFormalization.Section3.T20.abs_critFreqEnergyDeriv_le
#print axioms NSFormalization.Section3.T20.summable_critFreqEnergy
#print axioms NSFormalization.Section3.T20.hasDerivAt_tsum_critFreqEnergy

-- §4  homogeneous norms and the mean-free slice
#print axioms NSFormalization.Section3.T20.homENorm_eq_enorm_of_datum
#print axioms NSFormalization.Section3.T20.homENorm_toReal_eq_norm
#print axioms NSFormalization.Section3.T20.homENorm_toReal_sq
#print axioms NSFormalization.Section3.T20.zero_mem_initialClassT
#print axioms NSFormalization.Section3.T20.meanFreeVelocity_slice_eq
#print axioms NSFormalization.Section3.T20.meanFreeForce_slice_eq
#print axioms NSFormalization.Section3.T20.criticalY_toReal_sq_eq_tsum
#print axioms NSFormalization.Section3.T20.criticalZ_toReal_sq_eq_tsum
#print axioms NSFormalization.Section3.T20.advection_mean_split

-- §5  the frequency split
#print axioms NSFormalization.Section3.T20.rawEnergyDeriv_split

-- §6  the U8 target
#print axioms NSFormalization.Section3.T20.criticalEnergy
