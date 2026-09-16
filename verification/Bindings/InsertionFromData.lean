import Contracts.V1.Packet
import NSFormalization.Section4.I01.Energy
import NSFormalization.Section4.I01.Extension
import NSFormalization.Section4.I01.Quiet
import NSFormalization.Source.ViscosityPacket
import Bindings.Thresholds
import Bindings.InsertionFamily
import Bindings.InsertionLifespanV2

/-!
# R42 insertion from raw R41D data

A02 selects a reference horizon strictly inside the lifespan. I02 accepts its
open-slab restriction, with the arbitrary ball centred at zero of radius one.
I03 and R42 preserve the reference data definitionally. No supplier hypothesis
is needed, and the resulting object is the registered contract V2 record.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set Filter
open Contracts.V1 Contracts.V1.Data
open scoped ENNReal Topology

/-! `Bindings.Packet` and `Bindings.Scaling` both declare
`BlowupDensity.Bindings.navierStokesResidual_eq`, so Lean cannot import them
together. The following field assembly reproduces `Bindings.packet` under a
fresh name, using the very same upstream witnesses. Existing bindings stay
unchanged; this is an import collision workaround, not a supplier assumption. -/

open MeasureTheory in
open NSFormalization.Section4.I01 in
/-- Bind the selected compact packet, its Lemma 2.2 constants and its
negative-time zero extensions to the stable version-one contract. -/
def insertionFromData_packet (ν : ℝ) (hν : 0 < ν) : Contracts.V1.PacketAPI ν := by
  choose u p f K hprop hdiss hearly using
    NSFormalization.Source.selected_packet_every_viscosity hν
  choose τ hquietPos hquietLt hforceQuiet hvelocityQuiet hpressureQuiet using
    exists_packet_quiet hprop hearly
  choose M hM using exists_l2_isLUB hprop.energy_bounded
  exact
    { velocity := u
      pressure := p
      force := f
      carrier := K
      energyBound := M
      dissipationBound :=
        Real.sqrt (∫ s in Ioo (0 : ℝ) 1, Contracts.V1.dissipation u s)
      quietTime := τ
      viscosity_pos := hν
      velocity_smooth := hprop.velocity_smooth
      pressure_smooth := hprop.pressure_smooth
      force_smooth := hprop.force_smooth
      force_support := hprop.force_support
      carrier_compact := hprop.support_compact
      velocity_support := hprop.velocity_support
      pressure_support := hprop.pressure_support
      zero_initial_velocity := hprop.zero_initial_velocity
      divergence_free := hprop.divergence_free
      navier_stokes := hprop.navier_stokes
      speed_unbounded := hprop.speed_unbounded
      square_integrable := by
        obtain ⟨E, _, hbound⟩ := hprop.energy_bounded
        exact fun s hs => (hbound s hs).1
      energy_isLUB := hM
      dissipation_integrable := hdiss
      dissipation_eq := rfl
      quiet_pos := hquietPos
      quiet_lt_one := hquietLt
      force_quiet := hforceQuiet
      velocity_quiet := hvelocityQuiet
      pressure_quiet := hpressureQuiet
      force_zero_nonpos := fun _ ht y => hprop.force_support.eq_zero_of_nonpos ht y
      velocity_extension_smooth :=
        extension_smoothOn hquietPos hprop.velocity_smooth hvelocityQuiet
      pressure_extension_smooth :=
        extension_smoothOn hquietPos hprop.pressure_smooth hpressureQuiet
      extension_navier_stokes := fun _ ht y =>
        extension_navierStokes hquietPos hvelocityQuiet hpressureQuiet
          hprop.navier_stokes ht y
      extension_divergence_free := fun _ ht y =>
        extension_divergence_free hprop.divergence_free ht y }

/-- Gap G1: construct the registered insertion record from admissible data. -/
theorem insertionLifespanV2_of_data :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ (a : SpatialField), a ∈ initialClassR →
        ∀ (g : SpaceTimeField), MemForceR g →
          ENNReal.ofReal T < maximalLifespanR ν a g →
            ∃ (P : PacketAPI ν)
              (L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P),
              L.family.a = a ∧ L.family.g = g ∧ L.family.T = T := by
  intro ν hν T hT a _ha g hg hLife
  have hreg := (maximalPartial.regularThrough_iff ν a g T hT).mpr hLife
  obtain ⟨δ, hδ, ⟨R⟩, _, hlong⟩ := maximalPartial.referenceLifespan ν a g T hT hreg
  have hsub : Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space) ⊆
      Ico (0 : ℝ) (T + δ) ×ˢ (univ : Set Space) :=
    prod_mono Ioo_subset_Ico_self Subset.rfl
  let P := insertionFromData_packet ν hν
  let C : CorrectionAPI ν P := correction P (T := T) (δ := δ) (r := 1)
    (v := R.velocity) (π := R.pressure) (g := g) 0 hT hδ zero_lt_one
    (R.velocity_smooth.mono hsub) (R.pressure_smooth.mono hsub)
    (fun t ht => R.divergence t ⟨ht.1.le, ht.2⟩) R.momentum
  let S := scaling C thresholds
  let F := insertionFamily S R rfl rfl
  have hregLong : RegularThrough ν F.a F.g (F.T + F.margin) :=
    (maximalPartial.regularThrough_iff ν a g (T + δ) (add_pos hT hδ)).mpr hlong
  exact ⟨P, InsertionLifespan.insertionLifespanV2API F hg hregLong, rfl, rfl, rfl⟩

/-- Rewrite the record's exact lifespan to the original datum and time. -/
theorem insertionFromData_lifespan {ν T : ℝ} {a : SpatialField} {P : PacketAPI ν}
    (L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P)
    (ha : L.family.a = a) (hT : L.family.T = T)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) L.family.ε₀) :
    maximalLifespanR ν a (L.family.force ε) = ENNReal.ofReal T := by
  simpa only [ha, hT] using L.lifespan ε hε

/-- The same record supplies convergence relative to the original force. -/
theorem insertionFromData_forceConvergence {ν : ℝ} {g : SpaceTimeField}
    {P : PacketAPI ν}
    (L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P)
    (hg : L.family.g = g) (q : ℝ≥0∞) (hq : q = 1 ∨ q = 2) (s : ℝ)
    (hs : s < L.family.scaling.thresholds.exponent q.toReal 0) :
    Tendsto (fun ε : ℝ => forceSobolevENorm q s (fun z => L.family.force ε z - g z))
      (𝓝[>] 0) (𝓝 0) := by
  have h := L.family.forceConvergence q hq s hs
  change Tendsto (fun ε : ℝ => forceSobolevENorm q s
    (fun z => L.family.force ε z - L.family.g z)) (𝓝[>] 0) (𝓝 0) at h
  simpa only [hg] using h

end BlowupDensity.Bindings
