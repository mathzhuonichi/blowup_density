import Contracts.V1.Correction

/-! Version 2 of the correction specification: the caller pins the cutoff
radius above a prescribed compact set.

Task `collaboration/tasks/I02.md`, graph node `I02`.  The mathematics is the
same as version 1 -- the Euclidean halves of Lemma 3.4 (`lem:potential`,
`paper/sections/03-torus.tex:176-216`) and Lemma 3.5 (`lem:correction`,
`03-torus.tex:218-285`), as Theorem 4.2 (`thm:Rinsert`) reuses them.  What
changes is *who chooses the set the cutoff plateau has to cover*.

## Why a new version

`paper/sections/03-torus.tex:101-105` begins the insertion with

> Choose a compact set `K_*` containing `K` and the spatial projection of
> `supp F`. Fix `x_0 in B` ... For sufficiently small `eps > 0`, require
> `2 eps^2 < T`, `x_0 + eps K_* subset B`, `t_eps = T - eps^2`.

so the set that the cutoff, the radius `R_*` and the smallness threshold
`eps_0` are built around is the **enlarged** `K_*`, not the packet carrier `K`
of `01-introduction.tex:17-18`.  Version 1 records only
`carrier_subset_plateau : P.carrier subset plateau`; its docstring flags the
narrowing and defers the enlargement to `I03` and `R42`.

That deferral does not work through the registered interface, and two reviews
filed the same repair:

* `research/I03/REVIEW_CONTRACT.md` 5.1 item 4 and `research/I03/ATTEMPTS.md` 2.
  `V1.correctionStatement` binds `θRadius` *existentially*, and its registered
  witness fixes `θRadius` from `P.carrier` alone
  (`verification/Bindings/Correction.lean:174-178`), while
  `PacketAPI.force_support` says nothing about `carrier`.  So a consumer that
  reaches a `CorrectionAPI` through `Tests.checkedCorrection` gets a `θRadius`
  with no relation to `supp F`, and the field `force_carrier_subset` that
  `I03` had drafted was **dropped from `ScalingAPI`** as undischargeable
  (`Contracts/V1/Scaling.lean:180-190` records the deletion).
* `research/R42/ATTEMPTS.md` 3 and 5b.  Lacking the enlargement, `R42` has to
  rebuild it: it extracts a radius `R_F` from `HasCompactSupport P.force`,
  shrinks its own threshold to `min S.ε₀ (r / (R_F + 1))`, and carries the
  shrink as an extra field `eps_le_scaling`.  Every further consumer that
  touches `supp F_eps` must repeat this.

Version 2 removes the cause instead of the symptom: the caller names the
compact set, and the record guarantees the cutoff plateau -- hence `R_*`, hence
`eps_space` -- covers it.  With it, `eps * θRadius < r` alone places all five
rescaled fields `w_eps, H_eps, U_eps, P_eps, F_eps` inside `B`, and `R42` may
take `eps_0 = S.ε₀` rather than a `min`.

## What changed, exactly

`CorrectionAPI` gains a third parameter `K : Set Space`, extends the version-one
record unchanged, and adds **one** field,

  `prescribed_subset_plateau : K subset plateau`,

the `K_*` half of "`theta = 1` on a neighbourhood of `K_*`"
(`03-torus.tex:101-102, 181`).  `correctionStatement` quantifies over `K` and
assumes `IsCompact K`, the manuscript's "choose a compact set `K_*`"
(`03-torus.tex:101`).  Nothing else moves: no version-one field is removed,
weakened, renamed or restated, and `extends` makes that structural rather than
a claim about copied text -- `A.toCorrectionAPI` is a version-one record, which
is what `Bindings.correctionV1_of_V2` exports.

Two consequences worth stating.

* The added field is a **conclusion**, not a hypothesis: an inhabitant must
  build the cutoff around `P.carrier union K`, so version 2 is strictly
  stronger than version 1 and `V1.correctionStatement` follows from
  `V2.correctionStatement` (`Bindings.correctionStatement_of_v2`).
* `prescribed_subset_plateau` is stated against `plateau`, not against
  `Metric.ball 0 θRadius`, because the plateau form is what the manuscript
  says and it is the stronger of the two: `theta_one` and `theta_support` give
  `plateau subset ball 0 θRadius` in three lines, recorded once as
  `Bindings.prescribed_subset_ball` for consumers.  The version-one field
  `carrier_subset_plateau` is *kept* even though `K` may already contain
  `P.carrier`: deleting it would weaken the record for a caller that passes an
  unrelated `K`, and a specification field is never removed by a new version.

## Self-containedness

The contract-import rule of `experiments/check_contracts.py` allows a
specification to import another contract.  This module imports exactly
`Contracts.V1.Correction` and reuses its ten re-defined notions (`curl`,
`cross`, `scaledSpatialCutoff`, `scaledTemporalCutoff`, `dilateField`,
`parabolicVelocity`, `scaledPacket`, `alpha`, ...) and its structure, rather
than copying them.  That is deliberate: the `rfl` bridges of
`verification/Bindings/Correction.lean` already guard every one of those
notions against upstream drift, and a copy in this file would be a second,
unguarded spelling.  No implementation module is imported here.

This module introduces one structure and one `Prop`-valued definition.  It
proves nothing and asserts nothing.
-/

noncomputable section

namespace BlowupDensity.Contracts.V2

open Set MeasureTheory
open BlowupDensity.Contracts.V1 (Space VelocityField PressureField PacketAPI
  spatialDivergence navierStokesResidual)
open scoped ContDiff ENNReal Topology

/-- Version 1's `CorrectionAPI`, together with the manuscript's enlargement
`K_*` of the packet carrier (`paper/sections/03-torus.tex:101-102`) supplied by
the caller as the parameter `K`.

Every field of `V1.CorrectionAPI ν P` is inherited verbatim through
`toCorrectionAPI`; see `verification/Contracts/V1/Correction.lean:197-533` for
the 73 field docstrings and their manuscript citations.  The single new field is
`prescribed_subset_plateau`.

`K` is *not* required to contain `P.carrier`: `carrier_subset_plateau` covers
the packet carrier independently, so a caller may pass the enlargement
`P.carrier union Prod.snd '' tsupport P.force` of `03-torus.tex:101-102`, the
bare `Prod.snd '' tsupport P.force`, any larger compact set, or `emptyset` to
recover version 1 exactly.

No field is a hypothesis about an unspecified proposition, and no field is
`True`, `exists x, True` or any similar placeholder. -/
structure CorrectionAPI (ν : ℝ) (P : PacketAPI ν) (K : Set Space) extends
    V1.CorrectionAPI ν P where
  /-- `K_* subset` the open plateau of `theta`, so `theta = 1` on a
  neighbourhood of the prescribed compact set: the second half of "choose a
  compact set `K_*` containing `K` and the spatial projection of `supp F`"
  (`paper/sections/03-torus.tex:101-102`) read against the Urysohn cutoff of
  `03-torus.tex:167-174, 181`.

  This is the whole content of version 2.  Combined with the inherited
  `theta_one` and `theta_support` it gives `K subset ball 0 θRadius`, and then
  the inherited `eps_space : eps * θRadius < r` gives
  `x_0 + eps K subset B = ball x_0 r` for every `eps` in `(0, eps_0]`
  (`03-torus.tex:104-105`) -- the clause that version 1 could state only for the
  packet carrier. -/
  prescribed_subset_plateau : K ⊆ plateau

/-- What `I03` and `R42` receive from `I02` at version 2: the version-one
statement with a prescribed compact set threaded through.

Given a packet, **a compact set `K`**, and the ambient data of Theorem 4.2 -- a
singular time, a regularity margin, a smooth divergence-free reference solving
the momentum equation on `(0,T+delta) x R^3`, and a nonempty ball -- the
potential, the cutoffs, the correction and the correction force exist with all
the version-one properties *and* with a cutoff plateau covering `K`, for the
given reference itself and not merely for some extension of it.  The seven data
identities are those of `V1.correctionStatement`; `K` needs none, being a
parameter of the record's type.

`IsCompact K` is the manuscript's "choose a compact set `K_*`"
(`paper/sections/03-torus.tex:101`).  It cannot be dropped: `plateau` is
contained in `ball 0 θRadius`, so an unbounded `K` makes the conclusion false.

Introducing this definition asserts nothing. -/
def correctionStatement : Prop :=
  ∀ (ν : ℝ) (P : PacketAPI ν) (K : Set Space) (T δ r : ℝ) (v : VelocityField)
    (π : PressureField) (g : VelocityField) (x₀ : Space),
    IsCompact K → 0 < T → 0 < δ → 0 < r →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space)) →
    ContDiffOn ℝ ∞ π (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space)) →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space, spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space,
      navierStokesResidual ν v π t x = g (t, x)) →
    ∃ A : CorrectionAPI ν P K,
      A.T = T ∧ A.δ = δ ∧ A.v = v ∧ A.π = π ∧ A.g = g ∧ A.x₀ = x₀ ∧ A.r = r

end BlowupDensity.Contracts.V2
