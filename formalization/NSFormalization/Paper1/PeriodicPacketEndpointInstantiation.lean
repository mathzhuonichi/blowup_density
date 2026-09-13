import NSFormalization.Paper1.PeriodicEndpointInstantiation
import NSFormalization.Paper1.PeriodicPacketEndpointRates
import NSFormalization.Paper1.PeriodicConcentratedSupport

/-!
# Packet-specific periodized endpoint product

The already proved order-zero Parseval endpoint and order-one periodization
comparison are combined with the actual packet scaling rates.  The result is
an eventual bound for every `0 ≤ s ≤ 1`; all profile constants remain
explicit.  This is an endpoint product estimate, not a critical embedding.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicPacketEndpointInstantiation

open Set Filter MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source NSFormalization.Paper3
open NSFormalization.Paper1.PeriodicBridge
open NSFormalization.Paper1.PeriodicForceEndpointScaling
open NSFormalization.Paper1.PeriodicPacketEndpointRates
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal FourierTransform Topology

/-- Eventual packet bound for one scalar component after periodization. -/
theorem eventually_packet_coordinate_periodized_endpoint_product
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (i : Fin 3) (center : ℝ → ℝ) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Filter.Eventually (fun ε : ℝ =>
      eLpNorm (fun t => periodicSobolevNorm s
        (fun x => periodize
          (coordinateForce (parabolicForce ε⁻¹ (center ε) 0 F) i) (t, x))) 1 volume ≤
      (ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) *
        eLpNorm (fun t => fourierSobolevNorm 0
          (fun x => coordinateForce F i (t, x))) 1 volume) ^ (1 - s) *
      (ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) *
          eLpNorm (fun t => fourierSobolevNorm 1
            (fun x => coordinateForce F i (t, x))) 1 volume)) ^ s)
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by
  have hsupp : Filter.Eventually (fun ε : ℝ =>
      SupportedInCube (1 / 4)
        (coordinateForce (parabolicForce ε⁻¹ (center ε) 0 F) i))
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    filter_upwards [eventually_supportedInQuarterCube_parabolicForce_inv hc center]
      with ε hε
    exact supported_comp hε (fun v : Space => (v i : ℂ)) (by simp)
  have heps : Filter.Eventually (fun ε : ℝ => ε ≤ 1)
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    exact (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hsupp, heps, self_mem_nhdsWithin] with ε hS hε1 hε
  have hFε : ContDiff ℝ ∞
      (coordinateForce (parabolicForce ε⁻¹ (center ε) 0 F) i) :=
    coordinateForce_smooth (parabolicForce_smooth _ _ _ hF) i
  have hcε : HasCompactSupport
      (coordinateForce (parabolicForce ε⁻¹ (center ε) 0 F) i) :=
    coordinateForce_compact (parabolicForce_compact _ _ _ hc) i
  have hbase := periodized_scalar_L1Hs_le_endpoint_product hS (by norm_num)
    hFε hcε hs0 hs1
  have hzero := packet_scalar_H0_L1_endpoint_bound hF hc i hε hε1 (center ε)
  have hone := packet_scalar_H1_L1_endpoint_bound hF hc i hε hε1 (center ε)
  have hzero' : eLpNorm (fun t => fourierSobolevNorm 0
      (fun x => coordinateForce (parabolicForce ε⁻¹ (center ε) 0 F) i (t, x))) 1 volume ≤
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) *
        eLpNorm (fun t => fourierSobolevNorm 0
          (fun x => coordinateForce F i (t, x))) 1 volume := hzero
  have hone' : eLpNorm (fun t => fourierSobolevNorm 1
      (fun x => coordinateForce (parabolicForce ε⁻¹ (center ε) 0 F) i (t, x))) 1 volume ≤
      ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) *
        eLpNorm (fun t => fourierSobolevNorm 1
          (fun x => coordinateForce F i (t, x))) 1 volume := hone
  apply hbase.trans
  gcongr

end NSFormalization.Paper1.PeriodicPacketEndpointInstantiation
