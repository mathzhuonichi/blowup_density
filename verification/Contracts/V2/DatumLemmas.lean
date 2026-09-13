import Contracts.V1.DatumLemmas

/-! Version 2 of the **datum lemmas** specification: the version-one record of
D01, extended by the half-order time-norm finiteness of lane 042.

Task `collaboration/tasks/D01.md`, graph node `D01`.  The mathematics of every
version-one field is unchanged; version two adds the finiteness statements that
certify the smallness hypotheses of Propositions 4.3 and 4.4 are *not vacuous*.

## Why a new version

`Contracts.V1.DatumLemmas` deliberately stops short of the half-order time
norms.  Its field docstring (`Contracts/V1/DatumLemmas.lean:163`) records that
`smoothJets_sobolevENorm_ne_top` is the **spatial** slice finiteness only, and lists no clause bounding the
*time-integrated* Sobolev norm `Data.forceSobolevENorm q s`
(`Contracts/V1/Data.lean:225`) of a force in `𝓕_ℝ`.

That norm is the one Section 4's critical propositions weigh against a threshold:

* **Proposition 4.3** (`prop:Rcritical1`, `paper/sections/04-whole-space.tex:82-89`)
  asks `‖a‖_{Ḣ^{1/2}} + ‖f‖_{L¹_t Ḣ^{1/2}_x} < c ν`, and in particular
  (`04-whole-space.tex:88`) the ball `‖f‖_{L¹_t H^{1/2}_x} < c ν` of *inhomogeneous*
  data — `Data.forceSobolevENormL1 (1/2) f` (`Data.lean:231`).
* **Proposition 4.4** (`prop:Rcritical2`, `04-whole-space.tex:136-144`) asks
  `‖f‖_{L²(0,∞;H^{-1/2})} < r_{ν,S}` — `Data.forceSobolevENormL2 (-1/2) f`
  (`Data.lean:235`), the inhomogeneous critical `L²_t` norm.

`Data.MemForceR` (`Data.lean:544`) supplies datum paths only at **integer**
orders `m`, while `forceSobolevENorm q s` is an infimum over datum paths at the
real order `s`.  On the bare definitions the infimum can be the empty one, so
`forceSobolevENorm q s f = ⊤` for a genuine `f ∈ 𝓕_ℝ` and the hypothesis
`‖f‖ ≤ c` is then met vacuously by `‖f‖ = ⊤` — the one way a wrong implementation
satisfies the R43/R44 contracts (`research/R43/COMPARISON.md` §4 G3;
`research/R44/COMPARISON.md` §4 S1 and G6).  Version two removes that escape.

## What changed, exactly

`DatumLemmasV2API` extends `Contracts.V1.DatumLemmas.DatumLemmasAPI` unchanged and
adds **three** fields, all discharged by `Section4/D01/HalfOrder.lean` (lane 042,
reviewed in `research/D01/REVIEW_HALFORDER.md`):

* `forceSobolevENorm_ne_top` — the general statement: for every `f ∈ 𝓕_ℝ`, every
  real order `s` bounded by an integer `m`, and both time exponents `q ∈ {1, 2}`,
  the time norm `forceSobolevENorm q s f` is finite.  The order-`m` datum path
  that `MemForceR` supplies with finite `L¹_t`/`L²_t` norms lowers to an order-`s`
  datum path of no larger norm (real order lowering `A03.lowerDatum`, carried
  across `MemLp` because it is a `ContinuousLinearMap`); the order-`s` infimum is
  then bounded by that finite value.
* `forceSobolevENormL1_half_ne_top`, `forceSobolevENormL2_half_ne_top` — the two
  `s = 1/2 ≤ 1` instances R43 names directly (`q = 1` is `04-whole-space.tex:88`;
  the `q = 2` companion).  R44's `s = -1/2`, `q = 2` case is the general field at
  `m = 0`, `s = -1/2 ≤ 0`.

No version-one field is removed, weakened, renamed or restated; `extends` makes
that structural.  `Bindings.datumLemmas_of_v2` exports the version-one record,
and `Tests.checkedDatumLemmas` keeps running against the untouched
`Bindings.datumLemmas`.

## Out of scope, and asserted nowhere below

* **No homogeneous half of G3.**  `Data.forceHomogeneousENorm 1 (1/2) f ≠ ⊤` and
  the path-level monotonicity `forceHomogeneousENorm 1 (1/2) f ≤
  forceSobolevENormL1 (1/2) f` (G2, `04-whole-space.tex:132`) need a *homogeneous*
  datum for a general `H^∞` slice — an `L²`-multiplier construction beyond order
  monotonicity — and are proved nowhere in the tree.  `HalfOrder.lean`'s docstring
  and `research/D01/ATTEMPTS_HALFORDER.md` record the gap; neither is claimed here.
* **No order shift** `‖∇v‖_{H^s} ≤ ‖v‖_{H^{s+1}}` and no norm equivalence: version
  two adds only the finiteness of the inhomogeneous time norms, inheriting the
  version-one out-of-scope list verbatim.

## Self-containedness

The only import is `Contracts.V1.DatumLemmas`, which itself imports only three
other contracts.  Every notion the three new fields are stated with —
`SpaceTimeField`, `MemForceR`, `forceSobolevENorm`, `forceSobolevENormL1`,
`forceSobolevENormL2` — is `Contracts.V1.Data`'s, reused rather than copied; the
`rfl` bridges guarding `Section4/D01/HalfOrder.lean`'s local restatements against
upstream drift live in `verification/Bindings/DatumLemmasV2.lean`, following
`research/D01/axioms_halforder.lean`.  No implementation module is imported here.

This module introduces one structure and proves nothing. -/

noncomputable section

namespace BlowupDensity.Contracts.V2.DatumLemmas

open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- Version 1's `DatumLemmasAPI`, together with the half-order time-norm
finiteness of lane 042 (`Section4/D01/HalfOrder.lean`).

Every field of `Contracts.V1.DatumLemmas.DatumLemmasAPI` is inherited verbatim
through `toDatumLemmasAPI`; see `verification/Contracts/V1/DatumLemmas.lean` for
their docstrings and manuscript citations.  The three new fields make the
smallness hypotheses of Propositions 4.3 and 4.4 non-vacuous.

No new field is a hypothesis about an unspecified proposition, and none is
`True`, `∃ x, True` or any similar placeholder. -/
structure DatumLemmasV2API extends
    BlowupDensity.Contracts.V1.DatumLemmas.DatumLemmasAPI where
  /-- **`Section4/D01/HalfOrder.lean:156`, the general finiteness.**  On a force
  `f ∈ 𝓕_ℝ` (`Data.MemForceR`, `Data.lean:544`) the time-integrated Sobolev norm
  `Data.forceSobolevENorm q s f` (`Data.lean:225`) is finite for **every** real
  order `s` bounded by an integer `m` and for **both** time exponents
  `q ∈ {1, 2}`.

  `MemForceR` supplies a datum path only at integer orders, with finite `L¹_t`
  and `L²_t` Bochner norms (`Data.lean:546`); the real order-lowering operator
  `A03.lowerDatum` (`01-introduction.tex:94-95`, the inhomogeneous weight
  monotonicity `(1+|ξ|²)^{s/2} ≤ (1+|ξ|²)^{m/2}` for `s ≤ m`) turns it into an
  order-`s` datum path of the same slices with no larger norm, so the order-`s`
  infimum defining `forceSobolevENorm q s` is bounded by a finite value.

  This is the field `research/R44/COMPARISON.md` §4 S1/G6 asks for: with it the
  smallness ball of Proposition 4.4 (`04-whole-space.tex:136-144`,
  `‖f‖_{L²(0,∞;H^{-1/2})} < r_{ν,S}` = `forceSobolevENormL2 (-1/2) f`) is a genuine
  neighbourhood, taking `m = 0`, `s = -1/2 ≤ 0`, `q = 2`. -/
  forceSobolevENorm_ne_top :
    ∀ (f : SpaceTimeField), MemForceR f → ∀ (s : ℝ) (m : ℕ), s ≤ (m : ℝ) →
      ∀ q : ℝ≥0∞, q = 1 ∨ q = 2 → forceSobolevENorm q s f ≠ ⊤
  /-- **`Section4/D01/HalfOrder.lean:178`, the R43 instance.**  Proposition 4.3's
  smallness hypothesis `‖f‖_{L¹_t H^{1/2}_x} < c ν` (`04-whole-space.tex:88`,
  `prop:Rcritical1`) is not vacuous: the *inhomogeneous* half-order `L¹_t` norm
  `Data.forceSobolevENormL1 (1/2) f` (`Data.lean:231`) is finite on `𝓕_ℝ`.

  This is exactly `research/R43/COMPARISON.md` §4 G3's first clause,
  `∀ f, MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤` — the `s = 1/2 ≤ 1 = m`,
  `q = 1` case of `forceSobolevENorm_ne_top`.  (Its homogeneous twin
  `forceHomogeneousENorm 1 (1/2) f ≠ ⊤` is the open half of G3 and is not a field
  here; see the module docstring.) -/
  forceSobolevENormL1_half_ne_top :
    ∀ f : SpaceTimeField, MemForceR f → forceSobolevENormL1 (1 / 2) f ≠ ⊤
  /-- **`Section4/D01/HalfOrder.lean:183`, the `L²_t` companion.**  The
  *inhomogeneous* `L²_t H^{1/2}_x` norm `Data.forceSobolevENormL2 (1/2) f`
  (`Data.lean:235`) is finite on `𝓕_ℝ` too — the `s = 1/2 ≤ 1 = m`, `q = 2` case
  of `forceSobolevENorm_ne_top`, recorded so both time exponents of the
  half-order norm have a named instance. -/
  forceSobolevENormL2_half_ne_top :
    ∀ f : SpaceTimeField, MemForceR f → forceSobolevENormL2 (1 / 2) f ≠ ⊤

end BlowupDensity.Contracts.V2.DatumLemmas
