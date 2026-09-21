import Bindings.Scaling3

noncomputable section
namespace NSFormalization.Section3.T15.AssemblyProbe
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Source.PacketScaling
open scoped ContDiff

/-- The registered, nonzero I01 packet supplies each raw clause consumed by
U15; the energy subrecord lists all eight clauses individually. -/
def registeredRawScaling (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) :
    let P := BlowupDensity.Bindings.packet ν hν
    ScalingAPI (ν := ν) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound
      (placementData P.carrier_compact P.force_support.1 T hT) := by
  let P := BlowupDensity.Bindings.packet ν hν
  have hK : IsCompact P.carrier := P.carrier_compact
  have hu : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => P.velocity (t, x)) ⊆ P.carrier := P.velocity_support
  have hp : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => P.pressure (t, x)) ⊆ P.carrier := P.pressure_support
  have hus : ContDiffOn ℝ ∞ (zeroPastField P.velocity)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)) := P.velocity_extension_smooth
  have hps : ContDiffOn ℝ ∞ (zeroPastField P.pressure)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)) := P.pressure_extension_smooth
  have hf : ContDiff ℝ ∞ P.force := P.force_smooth
  have hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport P.force := P.force_support
  have hz : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, P.force (t, x) = 0 := P.force_zero_nonpos
  have heq : ∀ t : ℝ, t < 1 → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (zeroPastField P.velocity) (zeroPastField P.pressure) t x =
          zeroPastField P.force (t, x) := P.extension_navier_stokes
  have hdiv : ∀ t : ℝ, t < 1 → ∀ x : Space,
      spatialDivergence (zeroPastField P.velocity) t x = 0 := P.extension_divergence_free
  have hb : SpeedUnboundedAtOne P.velocity := P.speed_unbounded
  have hE : NSFormalization.Section4.I03.PacketData P.velocity P.carrier
      P.energyBound P.dissipationBound :=
    { extension_smooth := hus
      carrier_compact := hK
      support := hu
      square_int := P.square_integrable
      zero_initial := P.zero_initial_velocity
      energy_isLUB := P.energy_isLUB
      dissipation_int := P.dissipation_integrable
      dissipation_eq := P.dissipation_eq }
  exact scalingAPI hE hp hps hf hc hz heq hdiv hb _

example (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) :
    let P := BlowupDensity.Bindings.packet ν hν
    (placementData (u := P.velocity) (p := P.pressure)
      P.carrier_compact P.force_support.1 T hT).T = T := rfl

#print axioms registeredRawScaling
end NSFormalization.Section3.T15.AssemblyProbe
