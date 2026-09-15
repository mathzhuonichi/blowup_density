import Contracts.V1.EnergyAbsorptionPartial

/-! Version 2 of the **proved part of C01's ordinary-energy interface**: the version-one
record `EnergyAbsorptionPartialAPI` (`Contracts/V1/EnergyAbsorptionPartial.lean`),
extended by the single field `energyIdentity` — the ordinary energy identity as a genuine
`HasDerivAt` at every interior time — that was proved in the tree *after* version one was
frozen (lane 150, `Section4/C01/EnergyDerivative.lean`;
`energyIdentity_classical_unconditional`).

Task `collaboration/tasks/C01.md`, graph node `C01`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:277`: `C01 ← A02, A05`; consumers
`C01 → R43, R44` at `:285`, `:292`).  `research/C01/Spec.lean` bundles the whole obligation as
`EnergyAbsorptionAPI`; version one registered the five fields discharged in the tree at the
time and listed `energyIdentity`, `energyDifferentialBound`, `l2Bound` in its "Out of scope"
section, "not proved in the tree on this branch".  For `energyIdentity` that is no longer
true: lane 143 assembled `energyIdentity_classical` and lane 150 discharged its last
hypothesis (row **E4**), giving `energyIdentity_classical_unconditional` — the identity,
unconditionally, at every interior time.  Version two records it.

## Why a new version

`Contracts.V1.EnergyAbsorptionPartial`'s "Out of scope" list names `energyIdentity`
(`Spec.lean:344-350`) among the excluded fields "because not proved in the tree on this
branch".  It is now proved (lanes 143, 150); `Contracts/V1/*` is frozen by CI, so a version
two is the only way to register it without editing the frozen file.

## What changed, exactly

`EnergyAbsorptionPartialV2API` extends
`Contracts.V1.EnergyAbsorptionPartial.EnergyAbsorptionPartialAPI` unchanged and adds **one**
field `energyIdentity`, stated **token-for-token** as `research/C01/Spec.lean:344-350`.  No
version-one field is removed, weakened, renamed or restated; `extends` makes that structural.
`Bindings.energyAbsorptionPartial_of_v2` records the version-one projection is the frozen
version-one witness by `rfl`, and `Tests.checkedEnergyAbsorptionPartial` keeps running
against the untouched `Bindings.energyAbsorptionPartial`.

The field uses the two spec-local `def`s version one did not restate — `gradientSq`
(`Spec.lean:185`, `∫|∇z|²` through the registered `Contracts.V1.GradientL6` object
`gradientTensor`) and `pairing` (`Spec.lean:196`, the real `L²` pairing `∫⟪w,z⟫`) — plus the
version-one spec-local `slice`/`l2Sq` inherited by importing
`Contracts.V1.EnergyAbsorptionPartial` (drift-guarded there by `rfl` bridges).  `pairing` is
`rfl`-equal to its implementation counterpart `NSFormalization.Section4.C01.pairing`
(`Section4/C01/EnergySpec.lean`); `gradientSq` is the single non-`rfl` bridge of this
contract, `= ∫∑ᵢ‖∂ᵢz‖²` by `PiLp.norm_sq_eq_of_L2`, discharged in the binding.

## Scope disclosures

1. **The pressure and transport cancellations are folded in as proof obligations, not
   hypotheses.**  The identity's derivative value has only the viscous and forcing terms; the
   transport work `⟨(u·∇)u, u⟩` and the pressure work `⟨∇p, u⟩` are both `0`, proved in the
   tree from `ClassicalSolutionR.{divergence,pressure_gradient}`, not assumed.
2. **`0 < ν` and `a ∈ initialClassR` are slack.**  The lane's theorem
   `energyIdentity_classical_unconditional` needs neither; they are stated so the field reads
   as the manuscript's, matching the other version-one fields.
3. **The gradient term is the Frobenius `∫∑ᵢⱼ|∂ᵢuⱼ|²`, not the operator norm** — the same
   reading as `gradientTensor` (`Data.lean` documents this deliberately), so `gradientSq` is
   the second summand of `E_T` and not a weaker quantity.
4. **`energyDifferentialBound` (`Spec.lean:364`) and `l2Bound` (`Spec.lean:383`) remain
   excluded** — the differential (Cauchy–Schwarz) and integrated (eq:RL2) consequences of the
   identity; they are now unblocked but are not proved on this branch and are left to a future
   version.  Only `energyIdentity` is added here.
5. **Out of scope, asserted nowhere below.**  The enstrophy fields, the Fourier inequality,
   the assembly `h2TimeIntegral`, the `ν`-free assembly constants, `eq:Rcritical1/2`, the
   Grönwall and first-crossing arguments — exactly as version one's "Out of scope" records.

No new field is a hypothesis about an unspecified proposition, and none is `True`,
`∃ x, True` or any similar placeholder. -/

noncomputable section

namespace BlowupDensity.Contracts.V2.EnergyAbsorptionPartial

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1 (gradientTensor)
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial (slice l2Sq)

/-! ## 1. The two spec-local `def`s version one did not restate -/

/-- `research/C01/Spec.lean:185`, `‖∇z‖₂²`: the squared `L²` norm of the gradient **tensor**,
`∫|∇z|²`, the Frobenius `∫∑ᵢⱼ|∂ᵢzⱼ|²`.  `gradientTensor` is the **registered**
`Contracts/V1/GradientL6.lean:89` object (`Data.spatialGradient` on the time-independent
lift), so this is the second summand of `Data.energyGradient`, carried unchanged. -/
def gradientSq (z : SpatialField) : ℝ := ∫ x : Space, ‖gradientTensor z x‖ ^ 2

/-- `research/C01/Spec.lean:196`, `⟨w, z⟩`: the real `L²(R³;R³)` pairing `∫⟪w x, z x⟫`.  Used
for the forcing work `⟨f,u⟩` of the energy identity.  `rfl`-equal to its implementation
counterpart `NSFormalization.Section4.C01.pairing` (`Bindings` records it). -/
def pairing (w z : SpatialField) : ℝ := ∫ x : Space, (inner ℝ (w x) (z x) : ℝ)

/-! ## 2. The contract -/

/-- **The proved part of C01's ordinary-energy interface, version 2.**  Version one's
`EnergyAbsorptionPartialAPI` (the constant `C₁`/`C₁_pos`, `velocityJets`,
`forceTimeRegularity`, `trilinearHolder`, `trilinearAbsorbed`, `laplacianSqENorm`) together
with the ordinary energy identity `energyIdentity` proved by lanes 143 and 150.

Every field of `Contracts.V1.EnergyAbsorptionPartial.EnergyAbsorptionPartialAPI` is inherited
verbatim through `toEnergyAbsorptionPartialAPI`; see
`Contracts/V1/EnergyAbsorptionPartial.lean` for their docstrings and manuscript citations.

`EnergyAbsorptionPartialV2API` carries the data field `C₁` (inherited), so it is a `Type` and
the binding is a `def`, as in version one.

No new field is a hypothesis about an unspecified proposition, and none is `True`,
`∃ x, True` or any similar placeholder. -/
structure EnergyAbsorptionPartialV2API extends
    BlowupDensity.Contracts.V1.EnergyAbsorptionPartial.EnergyAbsorptionPartialAPI where
  /-- **The ordinary energy identity** (`research/C01/Spec.lean:344-350`;
  `04-whole-space.tex:117`, "The separate ordinary energy identity"; the display at
  `02-preliminaries.tex:136-139`), the exact form before any inequality:

    `(‖u(t)‖₂²)' = −2ν‖∇u(t)‖₂² + 2⟨u(t), f(t)⟩`.

  Equivalently `½(‖u‖₂²)' + ν‖∇u‖₂² = ⟨f,u⟩`.  The transport term `⟨(u·∇)u, u⟩` and the
  pressure term `⟨∇p, u⟩` are folded in as **proof obligations** (both vanish by
  solenoidality, `ClassicalSolutionR.{divergence,pressure_gradient}`), not hypotheses.
  Asserting `HasDerivAt` also asserts the squared energy is differentiable at every interior
  time.  Discharged by `NSFormalization.Section4.C01.energyIdentity_l2Sq`
  (`Section4/C01/EnergySpec.lean`, the clamp-free form of lane 150's
  `energyIdentity_classical_unconditional`).  The hypotheses `0 < ν` and `a ∈ initialClassR`
  are slack (the lane's theorem needs neither). -/
  energyIdentity :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s => l2Sq (slice w.velocity s))
            (-2 * ν * gradientSq (slice w.velocity t) +
              2 * pairing (slice w.velocity t) (slice f t)) t

end BlowupDensity.Contracts.V2.EnergyAbsorptionPartial
