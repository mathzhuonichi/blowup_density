import Contracts.V2.DatumLemmas
import Contracts.V1.Packet

/-! Version 3 of the **datum lemmas** specification: the version-two record of
D01, extended by the pressure half of obligation **P2** (`eq:Rpressure`,
`paper/sections/02-preliminaries.tex:89-94`), proved by lane 117
(`Section4/D01/PressureJets.lean`).

Task `collaboration/tasks/D01.md`, graph node `D01`.  Every version-one and
version-two field is inherited verbatim through `extends`; version three adds the
three public deliverables of `research/D01/P2_SPLIT.md` obligation P2.

## Why a new version

`Contracts.V1.DatumLemmas`'s scope deliberately stopped short of the pressure:
its docstring (`Contracts/V1/DatumLemmas.lean:67-71`) records that
`solution_slice_pressureGradient_contDiff` is *all* the class gives for the
pressure — order-zero `MemLp` plus spatial smoothness — and that neither
`SmoothSquareIntegrableJets (∇p(t,·))` nor any Sobolev datum for `∇p` follows or
is claimed.  The V1 registry scope states this as "**Not asserted anywhere: …
any Sobolev datum or jet class for the pressure or its gradient**".

Lane 117 (`research/D01/REVIEW_SL8_ASSEMBLY.md`) proves exactly that missing
regularity.  `paper/sections/02-preliminaries.tex:89-94` requires
`∇p = (I−P)(f − ∇·(u⊗u)) =: G`, smooth on `H^∞` data.  For a classical solution
`u ∈ ClassicalSolutionR ν a f T` with a real admissible force `f ∈ 𝓕_ℝ`
(`Data.MemForceR`), the pressure-gradient slice `∇p(t,·)` at every interior time
lies in the jet form of `H^∞`, hence carries an angular Sobolev datum at every
integer order.  The V1 *registry-scope* sentence "no Sobolev datum or jet class
for the pressure or its gradient is asserted" is thereby superseded **for the
gradient**; because V1 and V2 are frozen, the strengthening lives here.  This does
**not** contradict V1's *docstring* claim (`Contracts/V1/DatumLemmas.lean:67-71`)
that `SmoothSquareIntegrableJets (∇p(t,·))` does not follow **from the class as
specified**: lane 117's theorem adds `hf : MemForceR f`, which is not a field of
`ClassicalSolutionR`, and without it the conclusion is false (`Pressure.lean:62-66`).

## What changed, exactly

`DatumLemmasV3API` extends `Contracts.V2.DatumLemmas.DatumLemmasV2API` unchanged
and adds **three** fields, all discharged by `Section4/D01/PressureJets.lean`
(lane 117):

* `solution_slice_pressureGradient_smoothJets` — P2's regularity conclusion:
  `∇p(t,·) ∈ Contracts.V1.SmoothSquareIntegrableJets` for `t ∈ Ioo 0 T`.  This is
  `PressureJets.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`.
* `solution_slice_temporalDerivative_smoothJets` — the corollary `∂ₜu(t,·) ∈ H^∞`
  (jet form) run backwards through the `∂ₜu ↔ ∇p` equivalence.
* `solution_slice_pressureGradient_exists_datum` — the existence form of the
  order-`m` datum of `∇p(t,·)` that `A04.momentum_datum`'s `hP` slot consumes.

No version-one or version-two field is removed, weakened, renamed or restated;
`extends` makes that structural.  `Bindings.datumLemmasV3` inhabits this record
over the frozen `Bindings.datumLemmasV2` witness.

## Out of scope, and asserted nowhere below

Only the `Ioo 0 T` interior slices are asserted.  Explicitly **not** a field
here:

* the identity `∇p = (I−P)(f − ∇·(u⊗u))` in the manuscript's spelling.  What lane
  117 proves is the order-0 datum identity with the momentum residual
  `f − (u·∇)u + νΔu` in place of `f − ∇·(u⊗u)`; the order-`m` datum identity
  `datumᵐ ∇p = (I−P)ₘ (datumᵐ h)` is proved and exported upstream
  (`PressureJets.isSobolevDatum_pressureGradient_lerayComplement`) but is **not**
  registered as a field.  The momentum residual is **not** the obstacle: `f (t,·)`,
  `advection` and `spatialLaplacian` are all `Contracts.V1.Packet` vocabulary, so
  `h = f − (u·∇)u + νΔu` writes out in contract terms directly.  The obstacle is
  the **operator** `(I−P)ₘ` (`D01.Leray.lerayComplement`), which has no
  `Contracts/V1` counterpart, so the identity in its operator form cannot be
  stated here.  Its *operator-free* form — the Helmholtz split
  `datumᵐ h = datumᵐ ∂ₜu + datumᵐ ∇p` — **is** statable and provable in pure
  contract vocabulary (reviewer's appendix E,
  `research/D01/probes/v4_split_identity.lean`, standard axioms); with V1's already
  registered datum uniqueness it pins `datumᵐ ∇p`, the consumable half of
  eq:Rpressure at order `m`.  That is the **V4 candidate**, deliberately not
  registered in V3.  Here only the consumer-facing consequence, the existence of
  *some* order-`m` datum, is registered (`solution_slice_pressureGradient_exists_datum`).
* anything at `t = 0`.  The interior route consumes
  `ClassicalSolutionR.momentum`, which is imposed only on `Ioo 0 T`; `t = 0` is
  not reachable and not asked for by `research/D01/P2_SPLIT.md`.
* any statement about the scalar pressure `p` itself, as opposed to its gradient
  (the manuscript fixes `p` by the radial potential, an A01 field).
* the pointwise `IsLerayComplement` characterization that A01's `pressure_recovery`
  needs (`research/A01/Spec.lean:197`): that is a family of order-zero pointwise
  `MemLp` statements one level below the datum carrier, neither sufficient nor
  required by the datum fields here (review §2b).

## Self-containedness

The imports are `Contracts.V2.DatumLemmas` (which itself imports only contracts)
and `Contracts.V1.Packet` for `pressureGradient` and `temporalDerivative`.  Every
notion the three new fields are stated with — `ClassicalSolutionR`, `MemForceR`,
`SpatialField`, `SpaceTimeField`, `Space`, `IsSobolevDatum` (`Contracts.V1.Data`),
`SmoothSquareIntegrableJets` (`Contracts.V1.GradientL6`), `pressureGradient`,
`temporalDerivative` (`Contracts.V1.Packet`) and `RealVectorSobolev`
(`NSFormalization.Paper3`) — is reused, not copied; no implementation module is
imported here.  The `rfl` bridges guarding the implementation restatements
against upstream drift live in `verification/Bindings/DatumLemmasV3.lean`, on top
of those already in `Bindings.DatumLemmas` and `Bindings.DatumLemmasV2`.

This module introduces one structure and proves nothing. -/

noncomputable section

namespace BlowupDensity.Contracts.V3.DatumLemmas

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)

/-- Version 2's `DatumLemmasV2API`, together with the pressure half of obligation
P2 (`eq:Rpressure`, `02-preliminaries.tex:89-94`) proved in
`Section4/D01/PressureJets.lean` (lane 117).

Every field of `Contracts.V2.DatumLemmas.DatumLemmasV2API` — hence every field of
`Contracts.V1.DatumLemmas.DatumLemmasAPI` — is inherited verbatim through
`toDatumLemmasV2API`; see `verification/Contracts/V2/DatumLemmas.lean` and
`verification/Contracts/V1/DatumLemmas.lean` for their docstrings and manuscript
citations.  The three new fields register the pressure-gradient regularity the V1
scope explicitly disclaimed.

No new field is a hypothesis about an unspecified proposition, and none is
`True`, `∃ x, True` or any similar placeholder. -/
structure DatumLemmasV3API extends
    BlowupDensity.Contracts.V2.DatumLemmas.DatumLemmasV2API where
  /-- **`Section4/D01/PressureJets.lean:128`, obligation P2 (`eq:Rpressure`,
  `paper/sections/02-preliminaries.tex:89-94`; `research/D01/P2_SPLIT.md`).**  For
  a classical solution `u ∈ ClassicalSolutionR ν a f T` with a real admissible
  force `f ∈ 𝓕_ℝ` (`Data.MemForceR`, `Data.lean:544`), the pressure-gradient slice
  `∇p(t,·)` at every interior time `t ∈ Ioo 0 T` lies in the jet form of `H^∞`,
  `Contracts.V1.SmoothSquareIntegrableJets` (`GradientL6.lean:106`).

  On interior times this strengthens the V1 field
  `solution_slice_pressureGradient_contDiff` (spatial `C^∞` only) to full `H^∞`
  regularity — a stronger conclusion on the narrower domain (V1 on `Ico 0 T`, V3
  on `Ioo 0 T`).  It supersedes the *gradient* half of the V1 scope's "no Sobolev
  datum or jet class for the pressure or its gradient" sentence; the scalar `p`
  half is untouched (see "Out of scope").  The interior restriction `Ioo` (not
  `Ico`) is the one `P2_SPLIT.md` and the C01 consumer ask for; `t = 0` is not
  reachable through `ClassicalSolutionR.momentum` and is not asserted. -/
  solution_slice_pressureGradient_smoothJets :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
      SmoothSquareIntegrableJets fun x : Space => pressureGradient u.pressure t x
  /-- **`Section4/D01/PressureJets.lean:150`, the `∂ₜu(t,·) ∈ H^∞` corollary
  (`02-preliminaries.tex:89-94`; `research/D01/P2_SPLIT.md`).**  Under the same
  hypotheses, the time-derivative slice `∂ₜu(t,·)` at every interior time lies in
  the jet form of `H^∞`.  Obtained from the pressure field above by running the
  pointwise identity `∂ₜu = h − ∇p` (`h` the `H^∞` momentum residual) backwards. -/
  solution_slice_temporalDerivative_smoothJets :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
      SmoothSquareIntegrableJets fun x : Space => temporalDerivative u.velocity t x
  /-- **`Section4/D01/PressureJets.lean:141`, the `hP` slot of `A04.momentum_datum`
  (`02-preliminaries.tex:89-94`; `research/D01/P2_SPLIT.md`).**  Consequently
  `∇p(t,·)` has an angular Sobolev datum `P : RealVectorSobolev m`
  (`Data.IsSobolevDatum`, `Data.lean:160`) at every integer order `m` and every
  interior time.  This is the existence form `A04.momentum_datum`'s `hP` argument
  consumes; it follows from the jet field above by unit `L2`
  (`memHInfty_iff_smoothSquareIntegrableJets`).  Registered separately because it
  is the exact shape A04 wants, making that hypothesis demonstrably dischargeable
  from the contract alone.  The specific datum `(I−P)ₘ (datumᵐ h)` is *not* named
  here — that identity is in operator form (`(I−P)ₘ` has no `Contracts/V1`
  counterpart); its operator-free Helmholtz split is a V4 candidate (see the
  module docstring). -/
  solution_slice_pressureGradient_exists_datum :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
      ∀ m : ℕ, ∃ P : RealVectorSobolev (m : ℝ),
        IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P

end BlowupDensity.Contracts.V3.DatumLemmas
