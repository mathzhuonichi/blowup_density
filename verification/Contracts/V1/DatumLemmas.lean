import Contracts.V1.Data
import Contracts.V1.GradientL6
import Contracts.V1.BoundedRepresentative

/-! Stable specification for the **datum lemmas** of D01.

Task `collaboration/tasks/D01.md`, graph node `D01`
(`formalization/blueprint/DEPENDENCY_GRAPH.md`).  `Contracts/V1/Data.lean` is
definitions only: it fixes *what* the Section 4 statements mean and asserts
nothing.  Four proof modules under
`formalization/NSFormalization/Section4/D01/` discharge the lemmas that
`Data.lean`'s own docstrings book as owed — the datum/jet equivalence it calls
unit **L2** (`Data.lean:487-491`), the datum uniqueness it promises at
`Data.lean:145`, the homogeneous inhabitant and uniqueness it calls unit **L7**
(`Data.lean:318-321`), and the force-class closure
`F_R + C_c^∞(R³×(0,∞)) ⊆ F_R` of `paper/sections/04-whole-space.tex:51`.  This
version-one record bundles their **public deliverables**, stated in the
vocabulary of `Contracts/V1/Data.lean`, `Contracts/V1/GradientL6.lean` and
`Contracts/V1/BoundedRepresentative.lean`, so that A02, R43/R44 and B01 consume
them through a contract instead of through raw module imports.

| clause group | proof module | reviewed in |
|---|---|---|
| jets ⟹ datum, every real order | `Section4/D01/SmoothDatum.lean` (lane 020) | `research/D01/REVIEW_L2.md` |
| datum ⟹ jets, quantitatively; slices of a solution | `Section4/D01/DatumToJets.lean` (lane 025) | `research/D01/REVIEW_DATUM_TO_JETS.md` |
| homogeneous witness, uniqueness, path lift | `Section4/D01/HomogeneousWitness.lean` (lane 024) | `research/D01/REVIEW_HOMOGENEOUS.md` |
| `F_c ⊆ F_R`, additivity, the inserted force | `Section4/D01/ForceClass.lean` (lane 028) | `research/D01/REVIEW_FORCECLASS.md` |

## Consumers

* **A02** (local theory, uniqueness and continuation): `memHInfty_iff_smoothJets`
  converts `Data.ClassicalSolutionR.sobolev`'s datum path into the jet class the
  embedding contracts run on, `solution_slice_smoothJets` does it one time slice
  at a time from the solution record itself, `memLp_of_isSobolevDatum` is unit
  U1a's order-zero step (`Data.energyEssSup`, `Data.lean:444`, needs a genuinely
  square-integrable slice), and `isSobolevDatum_unique` is the uniqueness the
  `IsSobolevDatum` docstring promises (`Data.lean:145`).
* **R43/R44** (`prop:Rcritical1`, `prop:Rcritical2`): `solution_slice_smoothJets`
  puts every velocity slice in `Contracts.V1.SmoothSquareIntegrableJets`, the
  class `A05.gradient_l6` is stated on, and
  `jetSobolevENorm_le_sobolevENorm` converts the jet-form right-hand side of
  `A03.bounded_representative` into the manuscript's own `C_tH²` datum norm.
* **B01/R42** (`thm:Rinsert`): `memForceR_of_force_formula` and
  `memForceR_of_compact_difference` are the two shapes in which
  `Contracts.V1.InsertionFamily` hands the inserted force `g_ε = g + H_ε + F_ε`
  (`04-whole-space.tex:49`) to a consumer, and `memForceCompact_of_smooth_support`
  is what turns `Contracts.V1.Correction`'s three support fields into `F_c`
  membership.
* **R46/B02** (`prop:Renergy`): the homogeneous clauses make `Data.lean:338`
  `homogeneousENorm` and `Data.lean:367` `IsHomogeneousSliceDatum` inhabited, so
  the `L²(0,∞;Ḣ^{-1})` statements of `04-whole-space.tex:219-226` stop being
  vacuous.

## Out of scope, and asserted nowhere below

* **No norm equivalence.**  Only `jetSobolevENorm_le_sobolevENorm` is registered;
  the reverse inequality `sobolevENorm ≤ C · jetSobolevENorm`, i.e. the two-sided
  comparison of the manuscript's Fourier-side norm with the jet norm, is **not**
  proved anywhere in the tree and is not asserted here.  Likewise the
  manuscript's `∑_{|α|≤m}‖∂^αz‖₂` form never appears.
* **No time regularity of a datum path**, beyond what `MemForceR` itself carries:
  `Data.ClassicalSolutionR.sobolev`'s `ContinuousOn G (Ico 0 T)` conjunct is
  discarded by every slice clause below, and no clause produces a continuous or
  smooth datum path for a velocity.  This is the open half of R42's lifespan
  clause (`research/D01/REVIEW_FORCECLASS.md` §9).
* **No pressure datum.**  `Data.ClassicalSolutionR.pressure_gradient`
  (`Data.lean:647`) is order-zero `MemLp` only and the structure supplies no
  Sobolev datum for `p` or `∇p`, so only spatial smoothness of the slice is
  registered (`solution_slice_pressureGradient_contDiff`); neither
  `SmoothSquareIntegrableJets (∇p(t,·))` nor `BoundedRep.SmoothJetsUpTo 1` of it
  follows from the class as specified, and neither is claimed.
* **`forceHomogeneousENorm` is still not known to be `< ⊤`.**  `Data.lean:390`
  takes the infimum over paths that are additionally
  `AEStronglyMeasurable`; `compact_exists_homogeneousPath` inhabits
  `Data.IsHomogeneousPath` only.  What is registered about that infimum is the
  unconditional lower bound `eLpNorm_slice_le_forceHomogeneousENorm` and the
  identification `bochnerDatumENorm_eq_eLpNorm_slice` of the Bochner norm of
  *any* such path; the conditional equality is the two of them together and is
  deliberately not a field — the upstream theorem's hypothesis names the
  implementation's own path, and the contract-vocabulary form would need a proof
  in the binding, which the binding rule forbids.  See
  `research/D01/ATTEMPTS_CONTRACT.md` §2.3.
* **The `L¹ ∩ L²` homogeneous class** of `research/B02/Spec.lean:454` is not
  reached: every homogeneous existence clause below hypothesises Schwartz
  components, or smoothness with compact support.
* **`F_rd`** (`Data.forceClassRapid`, `Data.lean:578`) is untouched: no clause
  below mentions it, so `F_c ⊆ F_rd ⊆ F_R` is registered only in its outer form.
* Every **estimate** of Lemma A.1 and Lemma B.1.  Those are
  `A03.tame_products`, `A03.bounded_representative` and `A05.gradient_l6`; this
  record only supplies the *class membership* on which they are stated.

## Conventions

* **Fourier.**  The manuscript's unitary angular transform
  `ẑ(ξ) = (2π)^{-3/2}∫exp(-i x·ξ)z(x)dx` (`01-introduction.tex:91`), carried by
  `Data.IsSobolevDatum` and `Data.IsHomogeneousDatum`.  Mathlib's
  cycles-convention `𝓕` never appears in a statement of this file; the
  implementation's `(2π)` bookkeeping is invisible here because `Cjet` is an
  opaque structure field.
* **Constants.**  `Cjet` is a structure field, hence quantified *outside* every
  field: `appendix-a-local-theory.tex:10` fixes the constants to the integer
  order and the fixed domain `R³`, never to the field or its support.
* **Totalization.**  Every norm is `ℝ≥0∞`-valued and none is routed through
  `.toReal`.  `Data.sobolevENorm` is an infimum over data, so a field with no
  order-`m` datum gets `⊤` and `jetSobolevENorm_le_sobolevENorm` is then true and
  vacuous; the constant is positive, so `⊤` is never silently collapsed to `0`.
* **The homogeneous range.**  Existence needs only `-3/2 < s`, written `-3 / 2 < s`
  as `02-preliminaries.tex:70` and `04-whole-space.tex:70-72` write it;
  uniqueness needs no constraint on `s` at all.  The upper bound `s < 3/2` of the
  `Data.IsHomogeneousDatum` docstring (`Data.lean:307-317`) is a *sufficient*
  Cauchy-Schwarz route for a general `L²` datum and is **not** a hypothesis of
  any clause below — `research/D01/REVIEW_HOMOGENEOUS.md` ruling (a) records why
  the stronger statement is sound.

Self-containedness: the only imports are three other contracts.  Every notion a
clause is stated with is `Contracts.V1.Data`'s, `Contracts.V1.GradientL6`'s or
`Contracts.V1.BoundedRepresentative`'s; nothing here names an implementation
module, and `verification/Bindings/DatumLemmas.lean` supplies the `rfl` bridges.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.DatumLemmas

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff ENNReal SchwartzMap

/-- The lemmas of D01: the datum/jet dictionary for `H^∞` and `H^m`, uniqueness
of both kinds of datum, the first inhabitants of the homogeneous realization, and
closure of the force classes.  Each field is a theorem of one of the four
`Section4/D01/` modules, restated in the vocabulary of `Contracts/V1/Data.lean`. -/
structure DatumLemmasAPI where
  /-- The constant of `jetSobolevENorm_le_sobolevENorm` at integer order `m`.
  Depends only on `m` and the dimension three and carries exactly one `(2π)^m`
  (`research/D01/REVIEW_DATUM_TO_JETS.md` ruling (a)); the manuscript allows
  exactly this — `appendix-a-local-theory.tex:10` fixes constants to the order
  and the fixed domain.  Total in `m`. -/
  Cjet : ℕ → ℝ
  /-- Positivity of `Cjet`, which is what keeps the `⊤` branch of
  `jetSobolevENorm_le_sobolevENorm` from collapsing to `0`. -/
  Cjet_pos : ∀ m : ℕ, 0 < Cjet m

  -- ### 1. `Section4/D01/SmoothDatum.lean` — jets ⟹ datum

  /-- **`Section4/D01/SmoothDatum.lean:290`, the headline of lane 020.**  A smooth
  real three-vector field all of whose spatial Fréchet jets are square integrable
  has an angular real-vector Sobolev datum at **every real order** `s`: negative
  orders and half-integers included, with **no** compact-support, decay or `L¹`
  hypothesis.  `02-preliminaries.tex:12` eq:Rinitial only ever asks for integer
  orders, so this is strictly more than `MemHInfty` needs; `01-introduction.tex:94`
  defines `H^s` at every real `s` and `04-whole-space.tex:8` thm:Rmain uses the
  non-integer threshold `s_q = 2/q - 3/2`, which is why the real-order form is the
  one registered.

  Before lane 020 the only in-tree producer of real angular vector data required
  `HasCompactSupport`; that gap is `research/D01/RECONCILIATION.md:153`. -/
  smoothJets_exists_datum :
    ∀ (s : ℝ) (z : SpatialField), SmoothSquareIntegrableJets z →
      ∃ A : RealVectorSobolev s, IsSobolevDatum s z A
  /-- **`Section4/D01/SmoothDatum.lean:315`.**  Consequently the manuscript's norm
  `‖z‖_{H^s(R³)}` of `01-introduction.tex:94` — `Data.sobolevENorm`, an infimum
  over data, hence `⊤` on a field with none — is finite at every real order on the
  jet class.  This is the clause that makes every `Data.lean` quantity indexed by
  `sobolevENorm` a genuine number on Section 4's fields rather than the empty
  infimum. -/
  smoothJets_sobolevENorm_ne_top :
    ∀ (s : ℝ) (z : SpatialField), SmoothSquareIntegrableJets z →
      sobolevENorm s z ≠ ⊤
  /-- **`Section4/D01/SmoothDatum.lean:400`.**  Derivative closure on the jet
  carrier, at the level of data: every directional derivative `∂_v z` of a jet-class
  field again has a datum at every real order.  Stated with Mathlib's `fderiv`
  rather than with a coordinate derivative because the direction `v` is arbitrary;
  the coordinate case is `memHInfty_partialDeriv` below. -/
  smoothJets_exists_datum_fderiv :
    ∀ (s : ℝ) (z : SpatialField) (v : Space), SmoothSquareIntegrableJets z →
      ∃ A : RealVectorSobolev s, IsSobolevDatum s (fun x => fderiv ℝ z x v) A

  -- ### 2. `Section4/D01/DatumToJets.lean` — datum ⟹ jets

  /-- **Unit L2 (`Data.lean:487-491`), both directions.**  The *datum* form of
  `H^∞(R³;R³)` that `02-preliminaries.tex:12` eq:Rinitial is transcribed into —
  `Data.MemHInfty`, smooth with an angular datum at every integer order — and the
  *jet* form on which the registered embedding contracts
  `Contracts.V1.GradientL6` and `Contracts.V1.BoundedRepresentative` are stated
  are the **same class**.

  `Data.lean:487-491`, `GradientL6.lean`'s and `BoundedRepresentative.lean`'s
  module docstrings all book this equivalence as owed and assert it nowhere; it is
  `Section4/D01/DatumToJets.lean:298`, whose `←` half is lane 020's
  `memHInfty_of_contDiff_memLp` at integer orders and whose `→` half is lane 025's
  `memHInfty_jets`.  Every "a consumer holding `MemHInfty` still needs unit L2"
  sentence in those two contracts is discharged by this one field. -/
  memHInfty_iff_smoothJets :
    ∀ z : SpatialField, MemHInfty z ↔ SmoothSquareIntegrableJets z
  /-- **`Section4/D01/DatumToJets.lean:267`, A02 unit U1a's order-zero step.**  A
  smooth field with a datum at *any* single integer order is itself square
  integrable.  Registered separately from `memHInfty_iff_smoothJets` because it
  needs only one order, which is all that `Data.energyEssSup` (`Data.lean:444`),
  the upstream `SquareIntegrableAtTime` and the kinetic energy of
  `01-introduction.tex:143` eq:Enorm require; the `m = 0` clause of `MemForceR`
  (`Data.lean:546`) supplies exactly one order too. -/
  memLp_of_isSobolevDatum :
    ∀ (m : ℕ) (z : SpatialField) (A : RealVectorSobolev (m : ℝ)), ContDiff ℝ ∞ z →
      IsSobolevDatum (m : ℝ) z A → MemLp z 2 volume
  /-- **`Section4/D01/DatumToJets.lean:343`, the quantitative half of unit L2.**
  The jet-form norm `BoundedRep.jetSobolevENorm m` on which
  `A03.bounded_representative` states `supNorm_le` and `eLpNormTop_le` is bounded
  by the manuscript's own Fourier-side norm `Data.sobolevENorm (m : ℝ)`
  (`01-introduction.tex:85-86,94`).

  `Data.sobolevENorm` is an **infimum over data**, so the bound holds against every
  datum at once and not merely against a chosen one.  At `m = 2` this is what makes
  `04-whole-space.tex:53` composable: an extension through `T` bounded in `C_tH²`
  is bounded in `L^∞_x`, with the manuscript's `H²` norm on the right.
  `BoundedRepresentative.lean`'s module docstring says explicitly that it states no
  clause with `Data.sobolevENorm 2 z` on the right "because that would require
  bounding the jet norm by the datum norm, which is the open direction"; this is
  that direction.

  Only smoothness is hypothesised, not membership: with no order-`m` datum the
  right-hand side is `⊤` and the bound is true and vacuous.  The reverse
  inequality is **not** registered anywhere — see the module docstring. -/
  jetSobolevENorm_le_sobolevENorm :
    ∀ (m : ℕ) (z : SpatialField), ContDiff ℝ ∞ z →
      BoundedRep.jetSobolevENorm m z ≤ ENNReal.ofReal (Cjet m) * sobolevENorm (m : ℝ) z
  /-- **`Section4/D01/DatumToJets.lean:488`,** `research/A03/Spec.lean:339`'s
  `memHInfty_partialDeriv`: the datum form of `H^∞` is closed under the coordinate
  derivative `∂_j`.  `partialDeriv` is `Contracts.V1.GradientL6`'s
  (`GradientL6.lean:83`), i.e. `spatialDerivative` on the time-independent lift.

  `BoundedRepresentative.lean`'s module docstring names *derivative-closure of the
  field class* as one of two ingredients its `supNorm_le` consumer — the
  uniqueness coefficient `‖∇u₂‖_∞` of `appendix-a-local-theory.tex:120-123` —
  still needs and which it does not supply.  This field supplies it.  The other
  ingredient, the order shift `‖∇v‖_{H^s} ≤ ‖v‖_{H^{s+1}}`, is **not** registered
  here and is not proved in the tree. -/
  memHInfty_partialDeriv :
    ∀ (z : SpatialField) (j : Fin 3), MemHInfty z → MemHInfty (partialDeriv j z)
  /-- **`Section4/D01/DatumToJets.lean:458`.**  The reference initial velocity of
  `02-preliminaries.tex:12` eq:Rinitial, `X_R = H^∞(R³;R³) ∩ L²_σ(R³)`, is in the
  jet class, so `A03.bounded_representative` and `A05.gradient_l6` apply to it. -/
  initialClass_smoothJets :
    ∀ a : SpatialField, a ∈ initialClassR → SmoothSquareIntegrableJets a
  /-- **`Section4/D01/DatumToJets.lean:396`, the time-slice extraction.**  Every
  velocity slice `u(t,·)`, `0 ≤ t < T`, of a classical whole-space solution is in
  the jet class, hence in the hypothesis of `A05.gradient_l6`,
  `A05.hessianLaplacianIdentity` and (through
  `BoundedRep.smoothJetsUpTo_of_allOrders`) of `A03.bounded_representative`.

  This is the step `research/A05/REVIEW_CONTRACT.md:93-113` lists as missing
  between `Data.ClassicalSolutionR` and the registered jet-form contracts.  It uses
  only `velocity_smooth` (`Data.lean:632`) and the datum half of `sobolev`
  (`Data.lean:643`); the `ContinuousOn G (Ico 0 T)` conjunct of `sobolev` is
  **discarded**, so nothing below asserts time regularity of the datum path.
  Valid at `t = 0` as well, where the slab is one-sided in time: the slab still
  contains a full *spatial* neighbourhood of every `(t,x)`. -/
  solution_slice_smoothJets :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T) (t : ℝ), t ∈ Ico (0 : ℝ) T →
      SmoothSquareIntegrableJets fun x : Space => u.velocity (t, x)
  /-- **`Section4/D01/DatumToJets.lean:504`.**  The pressure gradient of a classical
  solution is smooth in space on every slice.  This is *all* the class as specified
  gives for the pressure: `pressure_gradient` (`Data.lean:647`) is order-zero
  `MemLp` only, no field supplies a Sobolev datum for `p` or `∇p`, and neither jet
  class follows — see the module docstring. -/
  solution_slice_pressureGradient_contDiff :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T) (t : ℝ), t ∈ Ico (0 : ℝ) T →
      ContDiff ℝ ∞ fun x : Space => pressureGradient u.pressure t x

  -- ### 3. `Section4/D01/ForceClass.lean` — datum uniqueness and the force classes

  /-- **`Section4/D01/ForceClass.lean:286`, unit L1.**  The order-`s` angular datum
  of a physical field is unique when it exists — the lemma the `IsSobolevDatum`
  docstring promises at `Data.lean:145`, "the datum is unique when it exists,
  because `angularRealization` is injective; that uniqueness is a lemma (unit L1),
  not built into this definition".  It is what turns `Data.sobolevENorm`
  (`Data.lean:189`) from an infimum into the norm of *the* datum, and what makes
  the additivity below an identity of data rather than an existence statement.
  No hypothesis on `s` or on `z`. -/
  isSobolevDatum_unique :
    ∀ (s : ℝ) (z : SpatialField) (A B : RealVectorSobolev s),
      IsSobolevDatum s z A → IsSobolevDatum s z B → A = B
  /-- **`Section4/D01/ForceClass.lean:261`.**  The datum of a sum is the sum of the
  data.  `angularRealization` is a continuous linear map, so the distributional
  side is additive outright; the *physical* side of `Data.IsSobolevDatum` is a
  Bochner integral, which Mathlib totalizes to `0` on a non-integrable integrand,
  so it splits only when both pairings are integrable.  That side condition is the
  `Data.lean:148-155` totalization caveat made a hypothesis; it is **not**
  removable, and it is discharged on `F_R` by `memForceR_slice_integrable` below.
  Together with `isSobolevDatum_unique` this says `A + B` is *the* datum of
  `z + w`, not merely one of them. -/
  isSobolevDatum_add :
    ∀ (s : ℝ) (z w : SpatialField) (A B : RealVectorSobolev s),
      (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
          Integrable (fun x : Space => ψ x * ((z x i : ℝ) : ℂ)) volume) →
      (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
          Integrable (fun x : Space => ψ x * ((w x i : ℝ) : ℂ)) volume) →
      IsSobolevDatum s z A → IsSobolevDatum s w B →
        IsSobolevDatum s (z + w) (A + B)
  /-- **`Section4/D01/ForceClass.lean:320`**, the time-path form: additivity of
  `Data.IsSobolevPath` (`Data.lean:174`).  `research/R42/COMPARISON.md` §4.3 lists
  exactly this as missing — "not the additivity
  `IsSobolevPath m g G₁ → IsSobolevPath m φ G₂ → IsSobolevPath m (g+φ) (G₁+G₂)`
  needed to add it to the reference force". -/
  isSobolevPath_add :
    ∀ (s : ℝ) (f g : SpaceTimeField) (G H : ℝ → RealVectorSobolev s),
      (∀ t : ℝ, 0 ≤ t → ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
          Integrable (fun x : Space => ψ x * ((f (t, x) i : ℝ) : ℂ)) volume) →
      (∀ t : ℝ, 0 ≤ t → ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
          Integrable (fun x : Space => ψ x * ((g (t, x) i : ℝ) : ℂ)) volume) →
      IsSobolevPath s f G → IsSobolevPath s g H →
        IsSobolevPath s (f + g) (G + H)
  /-- **`Section4/D01/ForceClass.lean:309`**, the discharger of the previous two
  side conditions on `F_R`: every slice of a force in `F_R` pairs integrably with
  every Schwartz test.  This is the argument the `Data.lean:153` caveat sketches
  — the `m = 0` clause of `MemForceR` puts the slice in `L²`, where Schwartz times
  `L²` is `L¹` — made explicit. -/
  memForceR_slice_integrable :
    ∀ f : SpaceTimeField, MemForceR f → ∀ t : ℝ, 0 ≤ t →
      ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
        Integrable (fun x : Space => ψ x * ((f (t, x) i : ℝ) : ℂ)) volume
  /-- **`Section4/D01/ForceClass.lean:189`, `F_c ⊆ F_R`.**  `04-whole-space.tex:185`
  `F_c = C_c^∞(R³×(0,∞);R³)` lies in `02-preliminaries.tex:17` eq:Rclasses'
  `F_R`: the order-`m` angular datum path of a compactly supported smooth force is
  smooth in time into `H^m` and Bochner `L¹ ∩ L²` on `(0,∞)`.  The `C^∞` in time
  clause is new in lane 028 — nothing in the project produced a datum path smooth
  in time before it.  This is the inclusion `cor:Rclasses`
  (`04-whole-space.tex:194`) needs. -/
  memForceCompact_memForceR : ∀ f : SpaceTimeField, MemForceCompact f → MemForceR f
  /-- **`Section4/D01/ForceClass.lean:330`.**  `F_R` is closed under addition, with
  **no** side hypothesis.  The physical side of `Data.IsSobolevDatum` is a Bochner
  integral, which Mathlib totalizes to `0` on a non-integrable integrand, so
  splitting it over a sum is not formal; the integrability comes from the `m = 0`
  clause of `MemForceR` itself, exactly as the totalization caveat of
  `Data.lean:148-155` anticipates ("`MemHInfty` and the `m = 0` clause of
  `MemForceR` put the slice in `L²`, where Schwartz times `L²` is `L¹`"). -/
  memForceR_add :
    ∀ f g : SpaceTimeField, MemForceR f → MemForceR g → MemForceR (f + g)
  /-- **`Section4/D01/ForceClass.lean:344`**, the D01 obligation
  `⟪D01:Cc_infty⟫` of `research/section4/STATEMENTS.md:270` and the sentence
  `04-whole-space.tex:51`: "Both force corrections are globally smooth and
  spacetime compact, including across `T`, so their sum preserves membership in
  `F_R`." -/
  memForceR_add_compact :
    ∀ g h : SpaceTimeField, MemForceR g → MemForceCompact h → MemForceR (g + h)
  /-- **`Section4/D01/ForceClass.lean:358`.**  `F_c` is closed under addition
  (`04-whole-space.tex:185`): the two corrections `H_ε` and `F_ε` of
  `04-whole-space.tex:49` may be added before being added to the reference. -/
  memForceCompact_add :
    ∀ f g : SpaceTimeField, MemForceCompact f → MemForceCompact g →
      MemForceCompact (f + g)
  /-- **`Section4/D01/ForceClass.lean:352`.**  `F_c` membership from the three facts
  `Contracts.V1.Correction` actually states about the correction force
  (`Correction.lean:426,429,440`: `force_smooth`, `force_compactSupport`,
  `force_positive_time`), character for character.  This is the adapter by which
  the I02 contract's output enters the force class. -/
  memForceCompact_of_smooth_support :
    ∀ f : SpaceTimeField, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∀ z ∈ tsupport f, 0 < z.1) → MemForceCompact f
  /-- **`Section4/D01/ForceClass.lean:380`.**  `F_R` is extensional for
  `Data.AgreesOnFuture` (`Data.lean:128`), as that docstring intends: the
  manuscript's forces live on `R³ × [0,∞)` (`02-preliminaries.tex:24`) while a
  `SpaceTimeField` is total in time, and both clauses of `MemForceR` read `f` only
  at `t ≥ 0`. -/
  memForceR_of_agreesOnFuture :
    ∀ f g : SpaceTimeField, AgreesOnFuture f g → (MemForceR f ↔ MemForceR g)
  /-- **`Section4/D01/ForceClass.lean:401`, `g_ε ∈ F_R` route 1.**  This is the
  shape `Contracts.V1.InsertionFamily.forceDifference_compact`
  (`InsertionFamily.lean:265`) delivers — `Data.MemForceCompact (fun z => g_ε z - g z)`
  — and it needs nothing else beyond the reference force's own membership
  `g ∈ F_R` (`04-whole-space.tex:32`).  Together they give
  `04-whole-space.tex:32`'s "there are `g_ε ∈ F_R`".

  Note that `g ∈ F_R` is **not** a consequence of `Data.ClassicalSolutionR`, which
  has no force-class field; R42 must carry it as a hypothesis
  (`research/D01/REVIEW_FORCECLASS.md` issue 1). -/
  memForceR_of_compact_difference :
    ∀ g gε : SpaceTimeField, MemForceR g →
      MemForceCompact (fun z => gε z - g z) → MemForceR gε
  /-- **`Section4/D01/ForceClass.lean:428`, `g_ε ∈ F_R` route 2.**  The third display
  of `04-whole-space.tex:49`, `g_ε = g + H_ε + F_ε`, with `H_ε` the correction force
  of I02 and `F_ε` the rescaled packet force of I03, each in `F_c` by
  `04-whole-space.tex:51`.  `Contracts.V1.InsertionFamily.force_formula`
  (`InsertionFamily.lean:187`) has the same left-associated grouping.

  *Availability.*  `MemForceCompact H_ε` is immediate from
  `memForceCompact_of_smooth_support` and `Contracts.V1.Correction`'s three fields;
  `MemForceCompact F_ε` is **not** currently available, because
  `ScalingAPI.F ε` is `PacketAPI`'s force pushed through `dilateField`
  (`Scaling.lean:115,448`) and nothing in the tree transports
  `Packet.force_smooth`/`force_support` (`Packet.lean:209,214`) through it.  Route 1
  above is therefore the one R42 can discharge today. -/
  memForceR_of_force_formula :
    ∀ g H F gε : SpaceTimeField, MemForceR g → MemForceCompact H → MemForceCompact F →
      (∀ z : SpaceTime, gε z = g z + H z + F z) → MemForceR gε

  -- ### 4. `Section4/D01/HomogeneousWitness.lean` — the homogeneous realization

  /-- **`Section4/D01/HomogeneousWitness.lean:473`.**  A real three-vector field
  whose complex components are Schwartz functions has an order-`s` **homogeneous**
  slice datum (`Data.lean:367`, `02-preliminaries.tex:58-69`
  eq:homogeneous-realization) for every `s > -3/2`, and its `L²` norm is the
  manuscript's own homogeneous Fourier quantity `Data.homogeneousFourierENorm`
  (`Data.lean:410`, `01-introduction.tex:105`).  Both clauses of
  `research/B02/Spec.lean:454` `lebesgueHomogeneousDatum`, under a Schwartz
  hypothesis in place of that draft's `L¹ ∩ L²`.

  `-3/2 < s` is the whole hypothesis; `04-whole-space.tex:70-72` is where the
  manuscript uses it, and it is exactly what makes `∫_{|ξ|<1}|ξ|^{2s}dξ` finite.
  No upper bound on `s` is needed — see the module docstring. -/
  schwartz_exists_homogeneousDatum :
    ∀ (s : ℝ), -3 / 2 < s → ∀ (z : SpatialField) (ψ : Fin 3 → SchwartzMap Space ℂ),
      (∀ (i : Fin 3) (x : Space), ψ i x = ((z x i : ℝ) : ℂ)) →
      ∃ A : RealVectorSobolev s,
        IsHomogeneousSliceDatum s z A ∧ ‖A‖ₑ = homogeneousFourierENorm s z
  /-- **`Section4/D01/HomogeneousWitness.lean:519`**, the same for a real
  `C_c^∞(R³;R³)` field — `04-whole-space.tex:249`'s "compact-smooth density in this
  realization", and the first inhabitant of `Data.lean:367`.  Both clauses again:
  existence, and that *every* datum of the slice has the Fourier norm. -/
  compact_exists_homogeneousDatum :
    ∀ (s : ℝ), -3 / 2 < s → ∀ z : SpatialField, ContDiff ℝ ∞ z → HasCompactSupport z →
      (∃ A : RealVectorSobolev s, IsHomogeneousSliceDatum s z A) ∧
        ∀ A : RealVectorSobolev s, IsHomogeneousSliceDatum s z A →
          ‖A‖ₑ = homogeneousFourierENorm s z
  /-- **`Section4/D01/HomogeneousWitness.lean:445`, unit L7.**  The homogeneous
  datum of a physical slice is unique, at **every real order** `s` — the "no
  polynomial ambiguity" of `02-preliminaries.tex:70`.  This is what turns the
  `Data.lean:338` and `Data.lean:390` infima into the norm of the datum.

  The `Data.IsHomogeneousDatum` docstring predicts `-3/2 < s` as a hypothesis of
  unit L7 (`Data.lean:318-321`); none is needed, because the `Integrable`
  temperedness clause built into `Data.IsHomogeneousDatum` already closes the
  escape that polynomial ambiguity uses.  `research/D01/REVIEW_HOMOGENEOUS.md`
  ruling (b) records the argument; `Data.lean` is frozen, so its docstring now
  understates what is proved. -/
  isHomogeneousSliceDatum_unique :
    ∀ (s : ℝ) (z : SpatialField) (A B : RealVectorSobolev s),
      IsHomogeneousSliceDatum s z A → IsHomogeneousSliceDatum s z B → A = B
  /-- **`Section4/D01/HomogeneousWitness.lean:463`.**  `Data.lean:338`
  `homogeneousENorm` is not the empty infimum: a Schwartz tempered distribution has
  finite `Ḣ^s` norm for every `s > -3/2`.  Before lane 024 every homogeneous name
  of `Data.lean` had zero users, so every statement about them was vacuously `⊤`. -/
  homogeneousENorm_schwartz_ne_top :
    ∀ (s : ℝ), -3 / 2 < s → ∀ φ : SchwartzMap Space ℂ,
      homogeneousENorm s (φ : 𝓢'(Space, ℂ)) ≠ ⊤
  /-- **`Section4/D01/HomogeneousWitness.lean:585`**, `research/B02/Spec.lean:470`'s
  `homogeneousDatumSub`, with the integrability side condition made explicit.
  Without it the statement is **false**: `Data.IsSliceDistribution` (`Data.lean:298`)
  totalizes a non-integrable pairing to `0`, so two fields differing by a genuine
  `C_c^∞` field can carry the same slice distribution
  (`research/D01/REVIEW_HOMOGENEOUS.md` ruling (c) exhibits the witness).  The
  side condition is discharged for fields with Schwartz components by
  `schwartz_integrable_component` below. -/
  isHomogeneousSliceDatum_sub :
    ∀ (s : ℝ) (z w : SpatialField) (Z W : RealVectorSobolev s),
      IsHomogeneousSliceDatum s z Z → IsHomogeneousSliceDatum s w W →
      (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
          Integrable (fun x : Space => ψ x * ((z x i : ℝ) : ℂ))) →
      (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
          Integrable (fun x : Space => ψ x * ((w x i : ℝ) : ℂ))) →
      IsHomogeneousSliceDatum s (z - w) (Z - W)
  /-- **`Section4/D01/HomogeneousWitness.lean:597`**, the discharger of the previous
  clause's side condition for a field with Schwartz components. -/
  schwartz_integrable_component :
    ∀ (z : SpatialField) (ψ : Fin 3 → SchwartzMap Space ℂ),
      (∀ (i : Fin 3) (x : Space), ψ i x = ((z x i : ℝ) : ℂ)) →
      ∀ (i : Fin 3) (χ : SchwartzMap Space ℂ),
        Integrable (fun x : Space => χ x * ((z x i : ℝ) : ℂ))
  /-- **`Section4/D01/HomogeneousWitness.lean:658`**, the path lift: a smooth
  compactly supported spacetime force has an order-`s` homogeneous **datum path**
  (`Data.lean:375`) at every `s > -3/2`, so `04-whole-space.tex:226` prop:Renergy's
  homogeneous clause is not vacuous.

  Stated existentially because the implementation's path
  (`compactHomogeneousPath`) is an implementation definition that a specification
  may not name.  This inhabits `Data.IsHomogeneousPath` **only**: the infimum
  `Data.forceHomogeneousENorm` (`Data.lean:390`) additionally demands
  `AEStronglyMeasurable`, which is not produced here and is I03's U7c blocker. -/
  compact_exists_homogeneousPath :
    ∀ (s : ℝ), -3 / 2 < s → ∀ f : SpaceTimeField, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∃ G : ℝ → RealVectorSobolev s, IsHomogeneousPath s f G
  /-- **`Section4/D01/HomogeneousWitness.lean:667`**, the `L^q_t` identification:
  *every* order-`s` homogeneous datum path of a smooth compactly supported force has
  the same Bochner norm (`Data.lean:205`), namely the `L^q(0,∞)` norm of the slice
  quantity `Data.homogeneousFourierENorm`.  With `q = 2`, `s = -1` this is the norm
  of `04-whole-space.tex:219,226`'s completed space `L²(0,∞;Ḣ^{-1}(R³))`. -/
  bochnerDatumENorm_eq_eLpNorm_slice :
    ∀ (q : ℝ≥0∞) (s : ℝ), -3 / 2 < s → ∀ f : SpaceTimeField, ContDiff ℝ ∞ f →
      HasCompactSupport f → ∀ G : ℝ → RealVectorSobolev s, IsHomogeneousPath s f G →
        bochnerDatumENorm q s G =
          eLpNorm (fun t => homogeneousFourierENorm s fun x => f (t, x)) q forceTimeMeasure
  /-- **`Section4/D01/HomogeneousWitness.lean:683`.**  Consequently the
  `Data.lean:390` infimum is bounded **below** by that `L^q_t` quantity, with no
  measurability hypothesis.  The matching upper bound needs one admissible
  (strongly measurable) path and is deliberately not a field here; see the module
  docstring and `research/D01/ATTEMPTS_CONTRACT.md`. -/
  eLpNorm_slice_le_forceHomogeneousENorm :
    ∀ (q : ℝ≥0∞) (s : ℝ), -3 / 2 < s → ∀ f : SpaceTimeField, ContDiff ℝ ∞ f →
      HasCompactSupport f →
        eLpNorm (fun t => homogeneousFourierENorm s fun x => f (t, x)) q forceTimeMeasure ≤
          forceHomogeneousENorm q s f

end BlowupDensity.Contracts.V1.DatumLemmas
