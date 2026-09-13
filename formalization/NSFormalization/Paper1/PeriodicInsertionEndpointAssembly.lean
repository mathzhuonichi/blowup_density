import NSFormalization.Paper1.PeriodicForceMeasurability
import NSFormalization.Paper1.PeriodicEndpointInstantiation
import NSFormalization.Paper1.PeriodicForceConvergence
import NSFormalization.Paper1.PeriodicInsertionSupport
import NSFormalization.Source.InsertionForceConvergence

/-!
# Vector endpoint assembly for the insertion force

This file assembles the already proved scalar periodization endpoint estimate
for the three components of the *complete* insertion force.  The result is a
finite-dimensional `L¹_t` bound; it does not assert the missing fractional
localization theorem or critical embedding.  Measurability of the fractional
periodic profiles follows from their actual Fourier-series definition.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicInsertionEndpointAssembly

open Set Filter MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicBridge
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicForceEndpointScaling
open NSFormalization.Source.InsertionFamily
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal FourierTransform Topology

/-- The complete insertion force has a vector periodized endpoint-product
bound; its scalar periodic profiles are measurably defined.  The right-hand
side is the sum of the three scalar whole-space endpoint products, so every
constant and endpoint norm remains explicit. -/
theorem eventually_insertion_vector_periodized_endpoint_product
    {F : ℝ → VelocityField}
    (hF : ∀ ε, ContDiff ℝ ∞ (F ε))
    (hcompact : ∀ ε, 0 < ε → HasCompactSupport (F ε))
    (hsupp : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SupportedInCube (1 / 4) (F ε))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      eLpNorm (fun t => periodicVectorSobolevNorm s
        (periodize (F ε)) t) 1 volume ≤
      ∑ i : Fin 3,
        (eLpNorm (fun t => fourierSobolevNorm 0
          (fun x => coordinateForce (F ε) i (t, x))) 1 volume) ^ (1 - s) *
          (ENNReal.ofReal (2 * Real.pi) *
            eLpNorm (fun t => fourierSobolevNorm 1
              (fun x => coordinateForce (F ε) i (t, x))) 1 volume) ^ s := by
  filter_upwards [hsupp, self_mem_nhdsWithin] with ε hS hε
  have hmeasε (i : Fin 3) :=
    (stronglyMeasurable_periodicSobolevNorm_time s
      (coordinateForce_smooth (contDiff_periodize hS (hF ε)) i).continuous).aestronglyMeasurable (μ := (volume : Measure ℝ))
  have hεpos : 0 < ε := hε
  apply (eLpNorm_periodicVectorSobolevNorm_le_sum (s := s)
    (F := periodize (F ε)) hmeasε).trans
  apply Finset.sum_le_sum
  intro i hi
  have hSi : SupportedInCube (1 / 4)
      (coordinateForce (F ε) i) :=
    supported_comp hS (fun v : Space => (v i : ℂ)) (by simp)
  have hFi : ContDiff ℝ ∞ (coordinateForce (F ε) i) :=
    coordinateForce_smooth (hF ε) i
  have hci : HasCompactSupport (coordinateForce (F ε) i) :=
    coordinateForce_compact (hcompact ε hεpos) i
  have hscalar := periodized_scalar_L1Hs_le_endpoint_product
    hSi (by norm_num) hFi hci hs0 hs1
  have hcoord : (fun z => coordinateForce (periodize (F ε)) i z) =
      periodize (coordinateForce (F ε) i) := by
    have hp := periodize_comp hS (by norm_num : (1 / 4 : ℝ) < 1 / 2)
      (fun v : Space => (v i : ℂ)) (by simp)
    exact hp
  have hslice : (fun t => periodicSobolevNorm s
      (fun x => coordinateForce (periodize (F ε)) i (t, x))) =
      (fun t => periodicSobolevNorm s
        (fun x => periodize (coordinateForce (F ε) i) (t, x))) := by
    funext t
    congr 1
    funext x
    exact congrFun hcoord (t, x)
  rw [hslice]
  exact hscalar

/-- Insertion-family specialization of the vector endpoint assembly.  All
smoothness, compactness, and fixed-cube support facts are discharged from the
existing insertion-force lemmas; fractional-profile measurability follows
from the Fourier-series time measurability theorem. -/
theorem eventually_actual_insertion_vector_periodized_endpoint_product
    (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hv : ContDiff ℝ ∞ v) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      eLpNorm (fun t => periodicVectorSobolevNorm s
        (periodize (InsertionFamily.force ν f v 0 T θ η ε)) t) 1 volume ≤
      ∑ i : Fin 3,
        (eLpNorm (fun t => fourierSobolevNorm 0
          (fun x => coordinateForce
            (InsertionFamily.force ν f v 0 T θ η ε) i (t, x))) 1 volume) ^ (1 - s) *
          (ENNReal.ofReal (2 * Real.pi) *
            eLpNorm (fun t => fourierSobolevNorm 1
              (fun x => coordinateForce
                (InsertionFamily.force ν f v 0 T θ η ε) i (t, x))) 1 volume) ^ s := by
  apply eventually_insertion_vector_periodized_endpoint_product
    (F := fun ε => InsertionFamily.force ν f v 0 T θ η ε)
    (fun ε => force_smooth_all ν hf hv 0 T ε hθ hη)
    (fun ε hε => force_compact_nonzero ν v hfc 0 T ε hε.ne' hθc hηc)
    (eventually_supportedInQuarterCube_insertionForce ν v T hfc η hθc)
    hs0 hs1

end NSFormalization.Paper1.PeriodicInsertionEndpointAssembly
