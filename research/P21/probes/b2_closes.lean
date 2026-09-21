import NSFormalization.Section3.T11.EnstrophyInequality
#check NSFormalization.Section3.T11.inhomogeneousEnergyIdentityT
#check NSFormalization.Section3.T11.lintegral_convection_holder_632T
#check NSFormalization.Section3.T11.eLpNorm_three_interpolationT
#check NSFormalization.Section3.T11.young_quarticT
#check NSFormalization.Section3.T11.young_three_quartersT
#check NSFormalization.Section3.T11.young_two_factorsT
#check NSFormalization.Section3.T11.weighted_cubic_assemblyT
#check NSFormalization.Section3.T11.gradient_six_le_laplacian_twoT
#check NSFormalization.Section3.T11.convection_interpolationT
#check NSFormalization.Section3.T11.velocity_six_le_localized_gradientT

open NSFormalization.Section3.T11
example {C Y Z ε : ℝ} (hC : 0 ≤ C) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hε : 0 < ε) :
    C * Y ^ (3 / 4 : ℝ) * Z ^ (3 / 4 : ℝ) ≤ ε * Z + C ^ 4 / ε ^ 3 * Y ^ 3 :=
  young_three_quartersT hC hY hZ hε

-- Ordinary energy can be positive when all spatial derivatives vanish.
example {ν U F P d : ℝ} (hν : 0 < ν) (hU : 0 ≤ U) (hF : 0 ≤ F)
    (hd : d = 2 * P) (hP : P ≤ Real.sqrt U * Real.sqrt F) :
    d + ν * U ≤ (1 + ν) * (1 + U) ^ 3 + (1 + 2 / ν) * F := by
  have h := weighted_cubic_assemblyT (Y := U) (Z := U) (C := 0) (G := 0) (L := 0) (N := 0) (Q := 0)
    hν le_rfl hU le_rfl le_rfl hF (by ring) (by simp) (by simpa using hd)
    (by simp) hP (by simp)
  simpa using h
