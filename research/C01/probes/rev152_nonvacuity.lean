import Bindings.EnergyAbsorptionPartialV2
import Bindings.MaximalPartial
import NSFormalization.Section4.A04.ZeroSolution

/-!
Lane 152 review — the contract field `energyIdentity` is not vacuously satisfiable.

1. `nonvac_interior`: for any `w : ClassicalSolutionR ν a f T` the quantified time set
   `Ioo 0 T` is **nonempty** (`w.horizon_pos : 0 < T`), so the `∀ t ∈ Ioo 0 T` is not an
   empty quantification.
2. `nonvac_witness`: the whole hypothesis block (`0 < ν`, `a ∈ initialClassR`,
   `MemForceR f`, a `ClassicalSolutionR`) is **satisfiable**: `A04.zeroSol` moved to the
   contract's structure by `Bindings.maximalPartial_ofA02`.
3. `nonvac_instance`: the contract's own witness, applied to that instance at an actual
   interior time, so the field really produces a `HasDerivAt`.
-/

noncomputable section
open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial (slice l2Sq)
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial (gradientSq pairing)
open BlowupDensity.Bindings

theorem nonvac_interior {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) : (Ioo (0 : ℝ) T).Nonempty :=
  nonempty_Ioo.2 w.horizon_pos

def nonvac_witness (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) :
    ClassicalSolutionR ν 0 0 T :=
  maximalPartial_ofA02 (NSFormalization.Section4.A04.zeroSol ν T hν hT)

theorem nonvac_instance (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) :
    HasDerivAt (fun s => l2Sq (slice (nonvac_witness ν T hν hT).velocity s))
      (-2 * ν * gradientSq (slice (nonvac_witness ν T hν hT).velocity (T / 2)) +
        2 * pairing (slice (nonvac_witness ν T hν hT).velocity (T / 2))
          (slice (0 : SpaceTimeField) (T / 2))) (T / 2) :=
  energyAbsorptionPartialV2.energyIdentity ν hν 0
    NSFormalization.Section4.A04.zero_mem_initialClassR 0
    NSFormalization.Section4.A04.memForceR_zero T (nonvac_witness ν T hν hT) (T / 2)
    ⟨by linarith, by linarith⟩

#print axioms nonvac_instance
