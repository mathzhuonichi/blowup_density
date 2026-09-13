import Contracts.V1.Packet
import NSFormalization.Section4.I01.Energy
import NSFormalization.Section4.I01.Extension
import NSFormalization.Section4.I01.Quiet
import NSFormalization.Source.ViscosityPacket

/-! The only layer that knows the current implementation's names and paths.

`Contracts.V1.Packet` is self-contained, so this adapter has two jobs: record
that each locally written specification notion really is the pinned upstream
Navier-Stokes notion, and assemble the selected packet into the contract.
-/

noncomputable section
namespace BlowupDensity.Bindings

open Set MeasureTheory
open scoped ContDiff

section Correspondence

variable (ν : ℝ) (u f : Contracts.V1.VelocityField) (p : Contracts.V1.PressureField)
  (t : ℝ) (x : Contracts.V1.Space) (i : Fin 3)

/-- The contract's space is the upstream space. -/
theorem space_eq : Contracts.V1.Space = NavierStokes.ProblemStatement.Space := rfl

/-- The contract's unit coordinate vectors are the upstream ones. -/
theorem coordinateVector_eq :
    Contracts.V1.coordinateVector i = NavierStokes.ProblemStatement.coordinateVector i := rfl

/-- The contract's presingular half-domain is the upstream one. -/
theorem preSingularDomain_eq :
    Contracts.V1.preSingularDomain = NavierStokes.ProblemStatement.preSingularDomain := rfl

/-- The contract's positive-time domain is the upstream one. -/
theorem positiveTimeDomain_eq :
    Contracts.V1.positiveTimeDomain = NavierStokesR3.ProblemStatement.positiveTimeDomain := rfl

/-- The contract's time derivative is the upstream one. -/
theorem temporalDerivative_eq : Contracts.V1.temporalDerivative u t x =
    NavierStokes.ProblemStatement.temporalDerivative u t x := rfl

/-- The contract's spatial Frechet derivative is the upstream one. -/
theorem spatialDerivative_eq : Contracts.V1.spatialDerivative u t x =
    NavierStokes.ProblemStatement.spatialDerivative u t x := rfl

/-- The contract's advection term is the upstream one. -/
theorem advection_eq : Contracts.V1.advection u t x =
    NavierStokes.ProblemStatement.advection u t x := rfl

/-- The contract's pressure gradient is the upstream one. -/
theorem pressureGradient_eq : Contracts.V1.pressureGradient p t x =
    NavierStokes.ProblemStatement.pressureGradient p t x := rfl

/-- The contract's Laplacian is the upstream componentwise Laplacian. -/
theorem spatialLaplacian_eq : Contracts.V1.spatialLaplacian u t x =
    NavierStokes.ProblemStatement.spatialLaplacian u t x := rfl

/-- The contract's divergence is the upstream Euclidean divergence. -/
theorem spatialDivergence_eq : Contracts.V1.spatialDivergence u t x =
    NavierStokes.ProblemStatement.spatialDivergence u t x := rfl

/-- The contract's residual is the upstream residual at the same viscosity. -/
theorem navierStokesResidual_eq : Contracts.V1.navierStokesResidual ν u p t x =
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x := rfl

/-- It is also the residual used by the local insertion calculus. -/
theorem navierStokesResidual_eq_source : Contracts.V1.navierStokesResidual ν u p t x =
    NSFormalization.Source.residual ν u p t x := rfl

/-- The contract's force class is the upstream compact positive-time support. -/
theorem compactPositiveTimeSupport_eq : Contracts.V1.CompactPositiveTimeSupport f =
    NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f := rfl

/-- The contract's slicewise square integrability is the upstream one. -/
theorem squareIntegrableAtTime_eq : Contracts.V1.SquareIntegrableAtTime u t =
    NavierStokesR3.ProblemStatement.SquareIntegrableAtTime u t := rfl

/-- The contract's blow-up condition is the upstream one. -/
theorem speedUnboundedAtOne_eq : Contracts.V1.SpeedUnboundedAtOne u =
    NavierStokes.ProblemStatement.SpeedUnboundedAtOne u := rfl

/-- The contract's squared spatial `L²` norm is the upstream one. -/
theorem l2Sq_eq : Contracts.V1.l2Sq u t = NavierStokesR3.CompactEnergy.l2Sq u t := rfl

/-- The contract's dissipation rate is the upstream one. -/
theorem dissipation_eq :
    Contracts.V1.dissipation u t = NavierStokesR3.CompactEnergy.dissipation u t := rfl

/-- The contract's past-zero extension is the one the scaling lemmas use. -/
theorem zeroPastField_eq :
    Contracts.V1.zeroPastField u = NSFormalization.Source.PacketScaling.zeroPastField u := rfl

/-- The same extension for a scalar pressure field. -/
theorem zeroPastPressure_eq :
    Contracts.V1.zeroPastField p = NSFormalization.Source.PacketScaling.zeroPastField p := rfl

end Correspondence

open NSFormalization.Section4.I01 in
/-- Bind the selected compact packet, its Lemma 2.2 constants and its
negative-time zero extensions to the stable version-one contract. -/
def packet (ν : ℝ) (hν : 0 < ν) : Contracts.V1.PacketAPI ν := by
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

/-- The manuscript fixes one packet per viscosity and rescales that one. -/
def packetFamily : Contracts.V1.PacketFamily where
  select := packet

end BlowupDensity.Bindings
