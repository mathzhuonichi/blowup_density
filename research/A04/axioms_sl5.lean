import NSFormalization.Section4.A04.NonlinearPairing

/- Transitive-axiom audit for the SL5 (S items) public declarations.
Each must print exactly `[propext, Classical.choice, Quot.sound]`. -/

open NSFormalization.Section4.A04
open NSFormalization.Paper3

-- SL5(e): discrete Cauchy–Schwarz
#print axioms sum_inner_le_sqrt_mul_sqrt
#print axioms abs_sum_inner_le_sqrt_mul_sqrt

-- SL5(d): summed real skew-adjointness
#print axioms sum_real_inner_angularDirectionalDerivative
#print axioms sum_real_inner_angularDirectionalDerivativeReal

-- SL5(i): two-vector, two-source-order lowering transfer (mid / complex / real)
#print axioms inner_loweringMid_transfer
#print axioms inner_lowering_transfer_complex
#print axioms real_inner_lowering_transfer
