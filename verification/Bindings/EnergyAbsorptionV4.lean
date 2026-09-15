import Contracts.V4.EnergyAbsorption
import Bindings.EnergyAbsorptionPartialV3
import NSFormalization.Section4.C01.H2TimeIntegral

/-! Bind all six remaining C01 fields. No new vocabulary is mirrored: solution
transport and the Frobenius gradient bridge are reused from earlier versions. -/
noncomputable section
namespace BlowupDensity.Bindings

/-- Frozen V3, extended by the complete enstrophy and H² estimates. -/
def energyAbsorptionV4 : Contracts.V4.EnergyAbsorption.EnergyAbsorptionAPI :=
  { energyAbsorptionPartialV3 with
    CRH1 := 2
    CRH1_pos := by norm_num
    CH2 := 16
    CH2_pos := by norm_num
    Cassembly := 32
    Cassembly_pos := by norm_num
    enstrophyIdentity := fun _ _ _ _ _ hf _ w _ ht => by
      simp only [energyAbsorptionPartialV2_gradientSq_eq]
      exact NSFormalization.Section4.C01.enstrophyIdentity (uniqueness_toA02 w) hf ht
    enstrophyDifferentialBound := fun _ hν _ _ _ hf _ w _ ht hsmall _ hd => by
      simp only [energyAbsorptionPartialV2_gradientSq_eq] at hd
      exact NSFormalization.Section4.C01.enstrophyDifferentialBound hν
        (uniqueness_toA02 w) hf ht hsmall hd
    enstrophyIntegralBound := fun _ hν _ _ _ hf _ w _ ht hsmall => by
      simp only [energyAbsorptionPartialV2_gradientSq_eq]
      exact NSFormalization.Section4.C01.enstrophyIntegralBound hν
        (uniqueness_toA02 w) hf ht hsmall
    sobolevTwoFourier := NSFormalization.Section4.C01.sobolevTwoFourier
    h2TimeIntegral := fun _ hν _ _ _ hf _ w _ hS hST hsmall => by
      simp only [energyAbsorptionPartialV2_gradientSq_eq]
      exact NSFormalization.Section4.C01.h2TimeIntegral hν
        (uniqueness_toA02 w) hf hS hST hsmall
    h2TimeIntegralZeroDatum := fun _ hν _ hf _ w _ hS hST hsmall =>
      NSFormalization.Section4.C01.h2TimeIntegralZeroDatum hν
        (uniqueness_toA02 w) hf hS hST hsmall }

/-- The parent is definitionally the unchanged frozen V3 witness. -/
theorem energyAbsorptionPartialV3_of_v4 :
    energyAbsorptionV4.toEnergyAbsorptionPartialV3API = energyAbsorptionPartialV3 := rfl

end BlowupDensity.Bindings
