import Contracts.V2.EnergyAbsorptionPartial

/-! Version 3 of the **proved part of C01's ordinary-energy interface**: the version-two
record `EnergyAbsorptionPartialV2API` (`Contracts/V2/EnergyAbsorptionPartial.lean`), extended
by the **two remaining ordinary-energy consequences** of the identity — the Cauchy–Schwarz
differential bound `energyDifferentialBound` and eq:RL2 `l2Bound` — proved in the tree after
version two was frozen (lane 154, `Section4/C01/EnergyBounds.lean`;
`energyDifferentialBound`, `l2Bound`).

Task `collaboration/tasks/C01.md`, graph node `C01`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:277`: `C01 ← A02, A05`; consumers
`C01 → R43, R44` at `:285`, `:292`).  `research/C01/Spec.lean` bundles the whole obligation as
`EnergyAbsorptionAPI`; version two's "Scope disclosures" (`Contracts/V2/EnergyAbsorptionPartial.lean:58-61`)
recorded `energyDifferentialBound` (`Spec.lean:364`) and `l2Bound` (`Spec.lean:383`) as
"now unblocked but not proved on this branch and left to a future version".  Lane 154 proved
both.  Version three records them.

## Why a new version

`Contracts.V2.EnergyAbsorptionPartial`'s "Scope disclosures" (item 4) names
`energyDifferentialBound` and `l2Bound` among the excluded fields "not proved on this branch".
They are now proved (lane 154); `Contracts/V1/*` and `Contracts/V2/*` are frozen by CI, so a
version three is the only way to register them without editing the frozen files.

## What changed, exactly

`EnergyAbsorptionPartialV3API` extends
`Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API` unchanged and adds **two**
fields, `energyDifferentialBound` and `l2Bound`, each stated **token-for-token** as
`research/C01/Spec.lean:364-370` and `:383-387`.  No version-one or version-two field is
removed, weakened, renamed or restated; `extends` makes that structural.
`Bindings.energyAbsorptionPartialV2_of_v3` records the version-two projection is the frozen
version-two witness by `rfl`, and `Tests.checkedEnergyAbsorptionPartialV2` keeps running
against the untouched `Bindings.energyAbsorptionPartialV2`.

The two fields use the version-one/version-two spec-local `def`s inherited by importing
`Contracts.V2.EnergyAbsorptionPartial` — `slice`/`l2Sq`/`l2Norm` (`Contracts/V1`, drift-guarded
there by `rfl` bridges) and `gradientSq` (`Contracts/V2`, the `gradientTensor` Frobenius form,
guarded by the single non-`rfl` bridge `energyAbsorptionPartialV2_gradientSq_eq`) — plus **two**
spec-local `def`s versions one and two did not restate: `forcePrimitive` (`Spec.lean:218-219`,
the forcing primitive `∫₀ᵗ‖f(s)‖₂ ds`) and `energyBudget` (`Spec.lean:224-225`, the whole
right-hand side `K(t) = ‖a‖₂ + ∫₀ᵗ‖f(s)‖₂ ds` of eq:RL2).  Both are `rfl`-equal to their
implementation counterparts `NSFormalization.Section4.C01.forcePrimitive`/`energyBudget`
(`Bindings` records each with its own `rfl` bridge).

## Scope disclosures

1. **The differential bound has no §4 display.**  `energyDifferentialBound`,
   `(‖u‖₂²)' + 2ν‖∇u‖₂² ≤ 2‖f‖₂‖u‖₂`, is the doubled Cauchy–Schwarz form of the §2 energy
   identity `½(‖U(t)‖₂²)' + ν‖∇U(t)‖₂² = ⟨F(t), U(t)⟩` (`02-preliminaries.tex:136-142`), the
   step the manuscript writes as `½(‖U‖₂²)' ≤ ‖F‖₂‖U‖₂` when dissipation is dropped; §4 uses it
   only as the "regularized norm division" input to eq:RL2 (`04-whole-space.tex:117`).  It is
   quantified over any real `E'` that is the derivative at `t`, not over `deriv`, so a consumer
   may feed the derivative from `energyIdentity` or from its own differentiability proof;
   derivatives are unique, so this is the same statement.
2. **`0 < ν` and `a ∈ initialClassR` are slack.**  For `energyDifferentialBound` the lane's
   theorem uses **neither**.  For `l2Bound` the lane's theorem uses `0 < ν` **only through
   `0 ≤ ν`** (the dissipation term `2ν‖∇u‖₂²` is discarded by nonnegativity); `a ∈ initialClassR`
   is unused.  Both hypotheses are stated so the fields read as the manuscript's, matching the
   version-one/version-two fields.
3. **The gradient term is the Frobenius `∫∑ᵢⱼ|∂ᵢuⱼ|²`, not the operator norm** — inherited from
   `gradientSq`'s `gradientTensor` reading (`Data.lean` documents this deliberately), so it is
   the second summand of `E_T`, not a weaker quantity.
4. **eq:RL2 (`l2Bound`) carries no smallness hypothesis and no absorption.**  This is the
   *ordinary* `L²` energy estimate, deliberately kept separate from eq:RH1
   (`04-whole-space.tex:117` "It does not control low frequencies by itself", `:132` "The low
   frequencies have been controlled directly by the ordinary energy estimate"); on `R³` there
   is no spectral gap to obtain it from the dissipation term instead.  The window `Ico 0 T`
   (`t = 0` included) is load-bearing, not a convenience — `research/C01/probes/rev154_icc_false.lean`
   proves the `Icc` widening false.
5. **Out of scope, asserted nowhere below.**  The enstrophy fields, the Fourier inequality
   `sobolevTwoFourier`, the assembly `h2TimeIntegral`/`h2TimeIntegralZeroDatum`, the constants
   `CRH1`/`CH2`/`Cassembly`, `eq:Rcritical1`/`eq:Rcritical2`, the Grönwall and first-crossing
   arguments — exactly as versions one and two record.

No new field is a hypothesis about an unspecified proposition, and none is `True`,
`∃ x, True` or any similar placeholder. -/

noncomputable section

namespace BlowupDensity.Contracts.V3.EnergyAbsorptionPartial

open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial (slice l2Sq l2Norm)
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial (gradientSq)

/-! ## 1. The two spec-local `def`s versions one and two did not restate -/

/-- `research/C01/Spec.lean:218-219` (`04-whole-space.tex:119` eq:RL2, `∫₀ᵗ‖f(s)‖₂ ds`): the
forcing primitive.  The time integral is the ordinary interval integral, so `t ≥ 0` is intended
throughout; the version-one field `forceTimeRegularity` supplies the interval integrability that
keeps it from being Mathlib's junk `0`. -/
def forcePrimitive (f : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, l2Norm (slice f s)

/-- `research/C01/Spec.lean:224-225` (`04-whole-space.tex:119` eq:RL2,
`K(t) = ‖a‖₂ + ∫₀ᵗ‖f(s)‖₂ ds`): the entire right-hand side of eq:RL2, named as the manuscript
names it, so that R43's and R44's assembly can quote `K(S)` directly
(`04-whole-space.tex:127-128`). -/
def energyBudget (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : ℝ :=
  l2Norm a + forcePrimitive f t

/-! ## 2. The contract -/

/-- **The proved part of C01's ordinary-energy interface, version 3.**  Version two's
`EnergyAbsorptionPartialV2API` (version one's fields plus the ordinary energy identity
`energyIdentity`) together with its two ordinary-energy consequences, the Cauchy–Schwarz
differential bound and eq:RL2, proved by lane 154.

Every field of `Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API` is inherited
verbatim through `toEnergyAbsorptionPartialV2API`; see
`Contracts/V2/EnergyAbsorptionPartial.lean` and `Contracts/V1/EnergyAbsorptionPartial.lean` for
their docstrings and manuscript citations.

`EnergyAbsorptionPartialV3API` carries the data field `C₁` (inherited), so it is a `Type` and
the binding is a `def`, as in versions one and two.

No new field is a hypothesis about an unspecified proposition, and none is `True`,
`∃ x, True` or any similar placeholder. -/
structure EnergyAbsorptionPartialV3API extends
    BlowupDensity.Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API where
  /-- **The ordinary energy inequality** (`research/C01/Spec.lean:364-370`;
  `04-whole-space.tex:118-121`, the "regularized norm division" input to eq:RL2; the doubled
  Cauchy–Schwarz form of the display at `02-preliminaries.tex:136-142`), the Cauchy–Schwarz form
  of the identity:

    `(‖u(t)‖₂²)' + 2ν‖∇u(t)‖₂² ≤ 2‖f(t)‖₂‖u(t)‖₂`.

  Quantified over any real `E'` that is the derivative at `t`, rather than over `deriv`, so that
  a consumer may feed in the derivative from `energyIdentity` or from its own differentiability
  proof; derivatives are unique, so this is the same statement.  It is the inequality whose
  regularized division by `(‖u‖₂² + ζ²)^{1/2}`, `ζ ↓ 0` (`04-whole-space.tex:100`) yields the
  next clause, including at times where `‖u(t)‖₂ = 0` (`:104`).  The hypotheses `0 < ν` and
  `a ∈ initialClassR` are slack (the lane's theorem `energyDifferentialBound` needs neither). -/
  energyDifferentialBound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          ∀ E' : ℝ, HasDerivAt (fun s => l2Sq (slice w.velocity s)) E' t →
            E' + 2 * ν * gradientSq (slice w.velocity t) ≤
              2 * l2Norm (slice f t) * l2Norm (slice w.velocity t)
  /-- **eq:RL2** (`research/C01/Spec.lean:383-387`; `04-whole-space.tex:118-121`, the display at
  `:119`), the display verbatim:

    `‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀^t‖f(s)‖₂ ds =: K(t)`,

  for every presingular time, with `K` spelled `energyBudget a f t`.  No smallness hypothesis
  and no absorption: this is the *ordinary* energy estimate, which is the whole point of keeping
  it separate from eq:RH1 — `04-whole-space.tex:117` "It does not control low frequencies by
  itself", and `:132` "The low frequencies have been controlled directly by the ordinary energy
  estimate".  On `R³` there is no spectral gap to obtain this from the dissipation term instead
  (`04-whole-space.tex:4-5`).  The window `Ico 0 T` (`t = 0` included) is load-bearing
  (`research/C01/probes/rev154_icc_false.lean` proves the `Icc` widening false).  `0 < ν` is
  consumed only as `0 ≤ ν`; `a ∈ initialClassR` is slack. -/
  l2Bound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          l2Norm (slice w.velocity t) ≤ energyBudget a f t

end BlowupDensity.Contracts.V3.EnergyAbsorptionPartial
