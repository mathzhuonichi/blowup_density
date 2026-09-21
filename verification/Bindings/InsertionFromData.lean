import Contracts.V1.Packet
import NSFormalization.Section4.I01.Energy
import NSFormalization.Section4.I01.Extension
import NSFormalization.Section4.I01.Quiet
import NSFormalization.Source.ViscosityPacket
import Bindings.Thresholds
import Bindings.InsertionFamily
import Bindings.InsertionLifespanV2

/-! Whole-space gluing from a prescribed reference solution and spatial ball.
The correction, scaling, lifespan and convergence results share one family.
The raw-data density entry point specializes the same construction. -/

noncomputable section

namespace BlowupDensity.Bindings

open Set Filter
open Contracts.V1 Contracts.V1.Data
open scoped ENNReal Topology

/-! Construct the concrete packet used by whole-space gluing from the selected source witness. -/

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

/-- Construct one inserted family in any prescribed positive-radius ball,
using exactly the given reference velocity and pressure. The internal time
margin is halved so the original reference supplies strict continuation past
that margin without any additional hypothesis. -/
theorem insertionLifespanV2_of_reference
    {ν T δ : ℝ} {a : SpatialField} {g : SpaceTimeField}
    (P : PacketAPI ν) (hT : 0 < T) (hδ : 0 < δ) (hg : MemForceR g)
    (R : ClassicalSolutionR ν a g (T + δ)) (x₀ : Space) (r : ℝ) (hr : 0 < r) :
    ∃ L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P,
      L.family.a = a ∧ L.family.g = g ∧ L.family.T = T ∧
      L.family.v = R.velocity ∧ L.family.π = R.pressure ∧
      L.family.ball = Metric.ball x₀ r := by
  let R' : ClassicalSolutionR ν a g (T + δ / 2) :=
    maximalPartial_ofA02 ((uniqueness_toA02 R).restrict (by linarith) (by linarith))
  have hsub : Ioo (0 : ℝ) (T + δ / 2) ×ˢ (univ : Set Space) ⊆
      Ico (0 : ℝ) (T + δ / 2) ×ˢ (univ : Set Space) :=
    prod_mono Ioo_subset_Ico_self Subset.rfl
  let C : CorrectionAPI ν P := correction P (T := T) (δ := δ / 2) (r := r)
    (v := R'.velocity) (π := R'.pressure) (g := g) x₀ hT (by linarith) hr
    (R'.velocity_smooth.mono hsub) (R'.pressure_smooth.mono hsub)
    (fun t ht => R'.divergence t ⟨ht.1.le, ht.2⟩) R'.momentum
  let S := scaling C thresholds
  let F := insertionFamily S R' rfl rfl
  have hregLong : RegularThrough ν F.a F.g (F.T + F.margin) := by
    refine ⟨δ / 2, by linarith, ?_⟩
    change Nonempty (ClassicalSolutionR ν a g ((T + δ / 2) + δ / 2))
    have he : (T + δ / 2) + δ / 2 = T + δ := by ring
    rw [he]
    exact ⟨R⟩
  exact ⟨InsertionLifespan.insertionLifespanV2API F hg hregLong,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Construct the inserted family from admissible data and a regular lifespan.
The density argument uses the unit-ball specialization of the general
reference-solution construction. -/
theorem insertionLifespanV2_of_data :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ (a : SpatialField), a ∈ initialClassR →
        ∀ (g : SpaceTimeField), MemForceR g →
          ENNReal.ofReal T < maximalLifespanR ν a g →
            ∃ (P : PacketAPI ν)
              (L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P),
              L.family.a = a ∧ L.family.g = g ∧ L.family.T = T := by
  intro ν hν T hT a _ha g hg hLife
  obtain ⟨δ, hδ, ⟨R⟩⟩ := (maximalPartial.regularThrough_iff ν a g T hT).mpr hLife
  let P := insertionFromData_packet ν hν
  obtain ⟨L, ha, hforce, htime, _⟩ :=
    insertionLifespanV2_of_reference P hT hδ hg R 0 1 zero_lt_one
  exact ⟨P, L, ha, hforce, htime⟩

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

/-- The full prescribed-region gluing theorem, with no analytic supplier
arguments. The open-set formulation includes every prescribed nonempty ball. -/
theorem wholeSpaceInsertion_holds :
    Contracts.V2.InsertionLifespan.wholeSpaceInsertionStatement := by
  intro ν hν
  let P := insertionFromData_packet ν hν
  refine ⟨P, ?_⟩
  intro T δ hT hδ a _ha g hg R B hB hBne
  obtain ⟨x₀, hx₀⟩ := hBne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hB x₀ hx₀
  obtain ⟨L, ha, hforce, htime, hv, hp, hregion⟩ :=
    insertionLifespanV2_of_reference P hT hδ hg R x₀ r hr
  have hinside : L.family.ball ⊆ B := by rw [hregion]; exact hball
  refine ⟨L, ha, hforce, htime, hv, hp, hinside, ?_, ?_⟩
  · intro ε hε
    refine ⟨InsertionLifespan.memForceR_force L.family L.memForce hε, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [ha, htime] using L.lifespan ε hε
    · simpa only [htime] using L.blowup_limsup ε hε
    · subst a
      subst T
      exact L.solution ε hε
    · have h : ∀ t : ℝ, 0 ≤ t → t ≤ L.family.T - 2 * ε ^ 2 → ∀ x : Space,
          L.family.velocity ε (t, x) = L.family.v (t, x) := L.family.history ε hε
      simpa only [htime, hv] using h
    · intro t ht
      have ht' : t ∈ Ico (0 : ℝ) L.family.T := by rw [htime]; exact ht
      have h := L.family.velocityDifference_support ε hε t ht'
      change tsupport (fun x : Space => L.family.velocity ε (t, x) - L.family.v (t, x)) ⊆
        L.family.ball at h
      rw [hv] at h
      exact h.trans hinside
    · have h : MemForceCompact (fun z => L.family.force ε z - L.family.g z) :=
        L.family.forceDifference_compact ε hε
      simpa only [hforce] using h
    · have h : ∀ z ∈ tsupport (fun z => L.family.force ε z - L.family.g z),
          z.2 ∈ L.family.ball := L.family.forceDifference_ball ε hε
      rw [hforce] at h
      exact fun z hz => hinside (h z hz)
    · have h : energyENorm L.family.T (fun z => L.family.velocity ε z - L.family.v z) ≤
          ENNReal.ofReal ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
            L.family.scaling.correctionEnergyConst * ε ^ ((3 : ℝ) / 2)) :=
        L.family.energyRate ε hε
      simpa only [htime, hv] using h
  · intro q hq s hs
    apply insertionFromData_forceConvergence L hforce q hq s
    simpa only [L.family.scaling.thresholds.formula, sub_zero] using hs

end BlowupDensity.Bindings
