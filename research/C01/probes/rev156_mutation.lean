import Bindings.EnergyAbsorptionPartialV3

/-! REVIEW PROBE (lane 156), negative check: three scratch copies of the **V3 contract
statement**, each with one mutation, each fed the verbatim binding proof term of
`Bindings.energyAbsorptionPartialV3`.  All three must fail to typecheck.

* A — `l2Bound`: `Ico 0 T` widened to `Icc 0 T` (the endpoint `t = T`).
* B — `l2Bound`: the forcing term `∫₀ᵗ‖f‖₂` dropped from the right-hand side of eq:RL2.
* C — `energyDifferentialBound`: the factor `2` dropped from `2‖f‖₂‖u‖₂`.
-/

noncomputable section
open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial (slice l2Sq l2Norm)
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial (gradientSq)
open BlowupDensity.Contracts.V3.EnergyAbsorptionPartial (forcePrimitive energyBudget)
open BlowupDensity.Bindings

/-! ### A. `Ico 0 T` → `Icc 0 T` -/

structure MutA extends
    BlowupDensity.Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API where
  l2Bound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Icc (0 : ℝ) T,
          l2Norm (slice w.velocity t) ≤ energyBudget a f t

def bindA : MutA :=
  { energyAbsorptionPartialV2 with
    l2Bound := fun _ hν _ _ _ hf _ w _ ht =>
      NSFormalization.Section4.C01.l2Bound (uniqueness_toA02 w) hf hν ht }

/-! ### B. the forcing primitive dropped from `K(t)` -/

def energyBudgetB (a : SpatialField) (_f : SpaceTimeField) (_t : ℝ) : ℝ := l2Norm a

structure MutB extends
    BlowupDensity.Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API where
  l2Bound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          l2Norm (slice w.velocity t) ≤ energyBudgetB a f t

def bindB : MutB :=
  { energyAbsorptionPartialV2 with
    l2Bound := fun _ hν _ _ _ hf _ w _ ht =>
      NSFormalization.Section4.C01.l2Bound (uniqueness_toA02 w) hf hν ht }

/-! ### C. the factor `2` dropped from the Cauchy–Schwarz right-hand side -/

structure MutC extends
    BlowupDensity.Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API where
  energyDifferentialBound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          ∀ E' : ℝ, HasDerivAt (fun s => l2Sq (slice w.velocity s)) E' t →
            E' + 2 * ν * gradientSq (slice w.velocity t) ≤
              l2Norm (slice f t) * l2Norm (slice w.velocity t)

def bindC : MutC :=
  { energyAbsorptionPartialV2 with
    energyDifferentialBound := fun _ _ _ _ _ hf _ w _ ht E' hderiv => by
      rw [energyAbsorptionPartialV2_gradientSq_eq]
      exact NSFormalization.Section4.C01.energyDifferentialBound (uniqueness_toA02 w) hf ht E'
        hderiv }
