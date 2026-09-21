import Bindings.EnergyHighPartialV2
-- NEGATIVE PROBE: claim Cgron = (Chigh m)^2/(2 ν) instead of /(4 ν).
-- Expected: rfl fails (the Young constant is 4ν, and it is sharp, 135-review).
noncomputable section
namespace BlowupDensity.Bindings
theorem bad_cgron_value (m : ℕ) (ν : ℝ) :
    energyHighPartialV2.Cgron m ν = NSFormalization.Section4.A04.Chigh m ^ 2 / (2 * ν) :=
  rfl
end BlowupDensity.Bindings
