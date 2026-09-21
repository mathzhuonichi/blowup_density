import NSFormalization.Section4.A04.EnstrophyInequality

/- Each analytic step is independently exposed; the final statements retain only B0 norm bridges. -/
#check NSFormalization.Section4.A04.inhomogeneousEnergyIdentity
#check NSFormalization.Section4.A04.lintegral_convection_holder_632
#check NSFormalization.Section4.A04.eLpNorm_three_interpolation
#check NSFormalization.Section4.A04.velocity_six_le_gradient_two
#check NSFormalization.Section4.A04.convection_interpolation
#check NSFormalization.Section4.A04.young_quartic
#check NSFormalization.Section4.A04.convection_bound_of_norm_bridges
#check NSFormalization.Section4.A04.young_three_quarters
#check NSFormalization.Section4.A04.young_two_factors
#check NSFormalization.Section4.A04.weightedEnergyIdentity
#check NSFormalization.Section4.A04.abs_pairing_carrier_le
#check NSFormalization.Section4.A04.weighted_cubic_assembly
#check NSFormalization.Section4.A04.enstrophy_differential_of_norm_bridges
#check NSFormalization.Section4.A04.enstrophy_differential
#check NSFormalization.Section4.A04.convection_sobolev
#check NSFormalization.Section4.A04.enstrophy_differential_on_Icc

example {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    a * b ^ 3 ≤ ε * b ^ 4 + a ^ 4 / ε ^ 3 :=
  NSFormalization.Section4.A04.young_quartic ha hb hε

example {C Y Z ε : ℝ} (hC : 0 ≤ C) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hε : 0 < ε) :
    C * Y ^ (3 / 4 : ℝ) * Z ^ (3 / 4 : ℝ) ≤ ε * Z + C ^ 4 / ε ^ 3 * Y ^ 3 :=
  NSFormalization.Section4.A04.young_three_quarters hC hY hZ hε
