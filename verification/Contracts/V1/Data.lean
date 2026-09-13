import NSFormalization.Paper3.AngularFourierDilation
import NSFormalization.Paper3.RealVectorPositiveDensity
import NSFormalization.Paper3.PositiveTemporalDensity
import NSFormalization.Paper3.GridGeometry
import NSFormalization.Source.FourierConvention
import NSFormalization.Source.RealSobolev
import NavierStokes.R3.ProblemStatement
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# V1 stable specification: Section 4 data, forces, norms, solutions and grids

Reconciliation of `research/D01/DraftA.lean` and `research/D01/DraftB.lean`
under `research/D01/REVIEW_A.md` (REJECT) and `research/D01/REVIEW_B.md`
(ACCEPT-WITH-NOTES), against `research/section4/STATEMENTS.md` §8 and
`research/section4/REVIEW.md` item 1.  The object-by-object record of every
choice is `research/D01/RECONCILIATION.md`.

This module contains **definitions only**: `abbrev`, `def` and `structure`.
There is no theorem with mathematical content, no `sorry`, no `axiom`, and no
placeholder `Prop` field.  It fixes *what the Section 4 statements mean*; it
asserts nothing about them.

## Conventions fixed once

* **Fourier.**  `01-introduction.tex:91` fixes the unitary angular-frequency
  transform `ẑ(ξ) = (2π)^{-3/2} ∫ exp(-i x·ξ) z(x) dx` and
  `‖z‖²_{H^s} = ∫ (1+|ξ|²)^s |ẑ(ξ)|² dξ`.  Every Sobolev object below is
  expressed through `angularRealization`, never through Mathlib's
  cycles-convention `𝓕`.
* **Real.**  `02-preliminaries.tex:72` — reality of a frequency datum is the
  conjugate-reflection symmetry `F(-ξ) = conj (F ξ)`, i.e. membership in
  `realSubspace`, which is built into `RealSobolevHilbert`.
* **Vector.**  `01-introduction.tex:103` "For vectors and tensors we sum the
  squared component norms": the Euclidean `PiLp 2` product
  `RealVectorSobolev`, *not* the supremum-normed `Fin 3 → SobolevHilbert`.
* **Time.**  `01-introduction.tex:140` — force norms use `(0,∞)`
  (`positiveTimeMeasure`), velocity norms before blowup use `(0,T)`.  Time is
  the **first** spacetime coordinate, following the pinned upstream package.
* **Totalization.**  Every norm here is `ℝ≥0∞`-valued and takes the value `⊤`
  off its space.  No `.toReal`, and no lower Lebesgue integral of a function
  whose measurability is unavailable: time norms are `eLpNorm` of a genuine
  Banach-valued path, and the measurability of that path is part of the
  quantified data (`REVIEW_B` issues 2 and 3).

## Canonical local dependencies

Imports of local `NSFormalization.*` modules are restricted to definition-level
conventions that the whole project treats as canonical.  The complete list,
with the declarations actually used:

| module | declarations used | why unavoidable |
|---|---|---|
| `NSFormalization.Source.FourierConvention` | `angularFourier` | the manuscript's `(2π)^{-3/2}∫e^{-ix·ξ}` transform; `angularFourier_eq_integral` is the proof that it is literally the displayed formula |
| `NSFormalization.Paper3.AngularFourierDilation` | `angularRealization`, `angularFourierDistribution` | the distributional realization of an `L²` datum in that same normalization; the only in-tree map `L² → 𝓢'` carrying the manuscript weights |
| `NSFormalization.Source.RealSobolev` | `FourierData`, `RealSobolevHilbert` | the reality constraint `F(-ξ) = conj (F ξ)` as a closed real subspace |
| `NSFormalization.Paper3.RealVectorPositiveDensity` | `RealVectorSobolev` | the Euclidean (`PiLp 2`) three-vector carrier and its normed instances |
| `NSFormalization.Paper3.PositiveTemporalDensity` | `positiveTimeMeasure` | the `(0,∞)` force-time measure `volume.restrict (Ioi 0)` |
| `NSFormalization.Paper3.GridGeometry` | `CartesianGrid`, `CartesianGrid.cell` | grid geometry: per-axis widths, arbitrary offset, half-open cells |

No module whose role is a proof is imported.  Everything else comes from
Mathlib and from the pinned upstream `NavierStokes.*` / `NavierStokesR3.*`
packages, which the import policy allows freely.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.Data

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source (angularFourier)
open NSFormalization.Source.RealSobolev (FourierData)
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. Field types and time domains -/

/-- `01-introduction.tex` eq:NS.  A time-independent real Euclidean three-vector
field on `R³`: initial velocities and spatial slices.  Reuses the pinned
upstream `NavierStokes.ProblemStatement.Space = EuclideanSpace ℝ (Fin 3)`, whose
norm is already the manuscript's Euclidean norm.  A and B agree. -/
abbrev SpatialField := Space → Space

/-- `01-introduction.tex` eq:NS.  A real Euclidean three-vector field on
spacetime, **time first**.  Velocities, forces and their differences all have
this type.  A and B agree. -/
abbrev SpaceTimeField := VelocityField

/-- `01-introduction.tex` eq:NS and `02-preliminaries.tex` §2.3.  The scalar
pressure.  A and B agree. -/
abbrev SpaceTimeScalar := PressureField

/-- `02-preliminaries.tex:22` "with one-sided time derivatives at zero": the
closed half line `[0,∞)` on which force smoothness is imposed.  Lifted to
spacetime this is the upstream `futureDomain = Ici 0 ×ˢ univ`. -/
abbrev futureTimes : Set ℝ := Ici (0 : ℝ)

/-- `01-introduction.tex:140` "Unless an interval is displayed, force norms use
`(0,∞)`."  This is `volume.restrict (Ioi 0)`; it differs from `futureTimes`
by a null set, so a force may be nonzero at `t = 0`. -/
abbrev forceTimeMeasure : Measure ℝ := positiveTimeMeasure

/-- `02-preliminaries.tex:24`, "whole-space forces may be nonzero at zero":
the manuscript's forces are functions on `R³ × [0,∞)`, while a `SpaceTimeField`
is total in time.  Two fields are the *same* manuscript force exactly when they
agree at nonnegative times.  `REVIEW_B` issue 5: draft B claimed a
zero-extension in a docstring but imposed nothing.  Rather than strengthening
`MemForceR` — which would weaken the universally quantified reference force of
Theorem 4.1(i) — the convention is recorded here as the equivalence by which the
force classes are extensional, and by which a separated metric must be taken. -/
def AgreesOnFuture (f g : SpaceTimeField) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Space, f (t, x) = g (t, x)

/-! ## 2. Sobolev data in the manuscript's angular normalization

`01-introduction.tex:94` defines `H^s(R³) = {z ∈ 𝓢' : (1+|ξ|²)^{s/2} ẑ ∈ L²}`.
The *datum* of `z` at order `s` is the `L²` function `(1+|ξ|²)^{s/2} ẑ`, and
`angularRealization s` sends a datum back to the tempered distribution it
represents.  A real Euclidean three-vector datum is an element of
`RealVectorSobolev s`. -/

/-- `01-introduction.tex:91,94,103` together with `02-preliminaries.tex:72`:
`A` is *the* order-`s` angular real-vector Sobolev datum of the physical field
`z`, in the sense that the distribution it realizes pairs with every Schwartz
test exactly as `z` does.  This is the pairing shape of
`angularRealVectorSlice_pairing`.

The datum is unique when it exists, because `angularRealization` is injective;
that uniqueness is a lemma (unit L1), not built into this definition.

A used a distributional pairing (`IsAngularDatum`), B used the same pairing
(`RepresentsSlice`).  Chosen: the shared pairing, because it is the only form
that makes negative orders meaningful for a classical field. -/
def IsSobolevDatum (s : ℝ) (z : SpatialField) (A : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((A i : FourierData)) ψ = ∫ x : Space, ψ x * ((z x i : ℝ) : ℂ)

/-- `02-preliminaries.tex:18` eq:Rclasses.  `G` is the order-`s` angular datum
trajectory of the spacetime field `f` on the closed half line `[0,∞)`.  Nothing
is required at negative times. -/
def IsSobolevPath (s : ℝ) (f : SpaceTimeField) (G : ℝ → RealVectorSobolev s) : Prop :=
  ∀ t : ℝ, 0 ≤ t → IsSobolevDatum s (fun x => f (t, x)) (G t)

/-- `01-introduction.tex:94`, `‖z‖_{H^s(R³)}` for a real vector field, as an
`ℝ≥0∞` quantity: the norm of the (unique) order-`s` datum, and `⊤` when `z` has
no order-`s` datum.  The empty infimum in `ℝ≥0∞` is `⊤`, so this is total and
fail-safe.

A gave a literal Fourier integral (`angularVectorSobolevNorm`), which
`REVIEW_A` issue 2 showed to be junk `0` for slices outside `L¹`; B gave the
datum infimum on tempered distributions.  Chosen: the datum infimum, on the
physical field, so that the quantity is correct on every `H^∞` slice. -/
def sobolevENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : RealVectorSobolev s // IsSobolevDatum s z A}, ‖A.1‖ₑ

/-! ## 3. Bochner time norms, the thresholds, and the scaling exponent -/

/-- `01-introduction.tex:118-129` eq:time-norms with `I = (0,∞)` and the Bochner
framework of Hunter, Definitions 6.14 and 6.27: the `L^q(0,∞;H^s(R³))` norm of a
**strongly measurable** Sobolev-valued time path.  Mathlib's `eLpNorm` on
`positiveTimeMeasure` is exactly that norm, and `q = ⊤` is the essential
supremum of eq:time-norms.  The intended range is `q ∈ {1,2}`.

`02-preliminaries.tex:63` makes `h ↦ |ξ|^{-s} ĥ` an isometry of `Ḣ^s` onto the
same `L²` datum space, so this one expression is also the
`L^q(0,∞;Ḣ^s(R³))` norm of `04-whole-space.tex:219` prop:Renergy when the path
is read through `IsHomogeneousDatum` instead of `IsSobolevDatum`.  Only the
realization differs, never the norm. -/
def bochnerDatumENorm (q : ℝ≥0∞) (s : ℝ) (G : ℝ → RealVectorSobolev s) : ℝ≥0∞ :=
  eLpNorm G q forceTimeMeasure

/-- `01-introduction.tex:118` "the space of strongly measurable maps with finite
norm": membership of a datum path in the Bochner space `L^q(0,∞;H^s(R³))`.
This is the honest completion element, carrying both strong measurability and
finiteness. -/
def MemBochnerDatum (q : ℝ≥0∞) (s : ℝ) (G : ℝ → RealVectorSobolev s) : Prop :=
  MemLp G q forceTimeMeasure

/-- `01-introduction.tex:125` eq:time-norms, evaluated on a *physical* field:
`‖f‖_{L^q(0,∞;H^s(R³))}`.  The value is the Bochner norm of the field's
order-`s` datum path when that path exists and is strongly measurable, and `⊤`
otherwise.

Draft A measured this by an explicit existential over the path; draft B used
`∫⁻` of a pointwise infimum, which `REVIEW_B` issue 3 flagged as a *lower*
integral that can under-report the norm.  Chosen: the infimum over measurable
paths, which is the measurable-path form with no lower-integral gap — the
fail-safe direction is `⊤`, never an under-report. -/
def forceSobolevENorm (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → RealVectorSobolev s //
      IsSobolevPath s f G ∧ AEStronglyMeasurable G forceTimeMeasure},
    bochnerDatumENorm q s G.1

/-- `01-introduction.tex:132`, `L¹_tH^s_x`; the `q = 1` case of thm:Rmain. -/
abbrev forceSobolevENormL1 (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  forceSobolevENorm 1 s f

/-- `01-introduction.tex:132`, `L²_tH^s_x`; the `q = 2` case of thm:Rmain. -/
abbrev forceSobolevENormL2 (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  forceSobolevENorm 2 s f

/-- `01-introduction.tex:134`, `L^q_tL^p_x = L^q(0,∞;L^p(R³))`: `G` is the
`L^p`-slice path of the physical field `f` on `[0,∞)`.  Slices are identified
almost everywhere, as `02-preliminaries.tex:62` and the Bochner footnote of
`01-introduction.tex:124` require. -/
def IsLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : SpaceTimeField)
    (G : ℝ → Lp Space p (volume : Measure Space)) : Prop :=
  ∀ t : ℝ, 0 ≤ t → (G t : Space → Space) =ᵐ[volume] fun x => f (t, x)

/-- `01-introduction.tex:134` eq:time-norms with `X = L^p(R³)`:
`‖f‖_{L^q(0,∞;L^p(R³))}`, in the same measurable-path form as
`forceSobolevENorm` and `⊤` when no such path exists.  `q = 1, p = 2` is the
`L¹_tL²_x` convergence of `04-whole-space.tex:224` prop:Renergy; `q = ⊤` is the
essential supremum.  Neither draft defined it. -/
def mixedLebesgueENorm (q p : ℝ≥0∞) [Fact (1 ≤ p)] (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p (volume : Measure Space) //
      IsLebesgueSlicePath p f G ∧ AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- `04-whole-space.tex:8` thm:Rmain, `s_q = 2/q - 3/2`: the Sobolev threshold
for the time exponent `q`.  A and B agree.  `s_1 = 1/2` and `s_2 = -1/2` are the
two thresholds of thm:Rmain. -/
def criticalOrder (q : ℝ) : ℝ := 2 / q - 3 / 2

/-- `04-whole-space.tex:57`, proof of thm:Rinsert: `β(q,s) = 2/q - 3/2 - s`, the
exponent of `ε` in eq:RpositiveScale and eq:RnegativeScale.  This is the same
arithmetic as the already registered `ThresholdAPI.exponent`; a binding should
identify the two.  A did not define it; B did. -/
def scalingExponent (q s : ℝ) : ℝ := 2 / q - 3 / 2 - s

/-! ## 4. Homogeneous realizations

`research/section4/REVIEW.md` item 1: the three homogeneous usages of Section 4
(Appendix B's `Λ^a` completion for `0 < a < 3/2`, the bare Fourier integral for
`-3/2 < s < 0`, and eq:homogeneous-realization at `s = -1`) are one formula.
A single definition on `-3/2 < s < 3/2`, plus the `Ḣ^{3/2}` *quantity*, serves
prop:Rcritical1, thm:Rinsert and prop:Renergy, with the App-B completion
identity and the smooth-compact-profile finiteness left as lemmas.

Draft A defined only the scalar `Ḣ^{-1}` case; draft B defined the general `s`
case without an integrability clause (`REVIEW_B` issue 4).  Chosen: B's general
`s`, with the manuscript's own temperedness estimate added as an explicit
integrability clause, plus the separate physical quantity below. -/

/-- Three tempered distributions, the componentwise home of a real vector
distribution.  Defined locally rather than imported: it is one line, and the
in-tree spelling lives in a module whose remaining content is proof. -/
abbrev VectorDistribution := Fin 3 → 𝓢'(Space, ℂ)

/-- `02-preliminaries.tex:58-69` eq:homogeneous-realization, and its
`appendix-b-embeddings.tex:56-70` counterpart at positive orders:
`Ḣ^s(R³) = {h ∈ 𝓢' : ĥ measurable and |ξ|^s ĥ ∈ L²}`, realized by
`ĥ = |ξ|^{-s} G` with `G ∈ L²`.  `G` is the datum, and `‖h‖_{Ḣ^s} = ‖G‖₂`.

The `Integrable` clause is the manuscript's own displayed temperedness estimate
(`02-preliminaries.tex:67`, `appendix-b-embeddings.tex:59-64`), which holds
exactly on `-3/2 < s < 3/2`; without it the Bochner integral would silently
totalize to `0`.  Outside that range this definition is not claimed faithful:
`appendix-b-embeddings.tex:44` restricts the completion to `0 < a < 3/2` and
`:101` refuses `Ḣ^{3/2}` as a space. -/
def IsHomogeneousDatum (s : ℝ) (G : FourierData) (u : 𝓢'(Space, ℂ)) : Prop :=
  ∀ φ : SchwartzMap Space ℂ,
    Integrable (fun ξ : Space => φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ)) ∧
      angularFourierDistribution u φ =
        ∫ ξ : Space, φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ)

/-- `02-preliminaries.tex:59` eq:homogeneous-realization: membership in the
fixed realization of `Ḣ^s(R³)`, `-3/2 < s < 3/2`. -/
def MemHomogeneous (s : ℝ) (u : 𝓢'(Space, ℂ)) : Prop :=
  ∃ G : FourierData, IsHomogeneousDatum s G u

/-- `02-preliminaries.tex:63` "The map `h ↦ |ξ|^{-1} ĥ` is an isometric
bijection onto `L²`": `‖h‖_{Ḣ^s}` is the `L²` norm of its datum, and `⊤` off the
space.  That the infimum is attained at a unique datum is a lemma (unit L7). -/
def homogeneousENorm (s : ℝ) (u : 𝓢'(Space, ℂ)) : ℝ≥0∞ :=
  ⨅ G : {G : FourierData // IsHomogeneousDatum s G u}, ‖G.1‖ₑ

/-- `02-preliminaries.tex:59` at `s = -1`: the completed energy-force space
`Ḣ^{-1}(R³)` of prop:Renergy. -/
abbrev MemDotHNegOne (u : 𝓢'(Space, ℂ)) : Prop := MemHomogeneous (-1) u

/-- `02-preliminaries.tex:72` with `01-introduction.tex:103`: the vector form of
`Ḣ^s`, summing squared component norms. -/
def MemHomogeneousVector (s : ℝ) (U : VectorDistribution) : Prop :=
  ∀ i : Fin 3, MemHomogeneous s (U i)

/-- `01-introduction.tex:103` "sum the squared component norms": the vector
`Ḣ^s` norm.  `⊤` propagates correctly through the `ℝ≥0∞` arithmetic. -/
def homogeneousVectorENorm (s : ℝ) (U : VectorDistribution) : ℝ≥0∞ :=
  (∑ i : Fin 3, homogeneousENorm s (U i) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `01-introduction.tex:105` "The homogeneous norm `Ḣ^s` replaces the weights
above by `|ξ|^{2s}`", written as the literal Fourier integral on a physical
field and summed over components:
`‖z‖²_{Ḣ^s} = ∑_i ∫ |ξ|^{2s} |ẑ_i(ξ)|² dξ`.

This is the *quantity* form, the only one Section 4 and the appendices use at
`s = 3/2` (`04-whole-space.tex:91` `z = ‖Λ^{3/2}u‖₂`;
`appendix-b-embeddings.tex:31,107`; `appendix-a-local-theory.tex:24`), where
`appendix-b-embeddings.tex:101` explicitly refuses a space.  It is also
ledger item `⟪D01:dotHsFinite s⟫`, the `-3/2 < s < 0` finiteness used for the
rescaled compact profiles of eq:RnegativeScale.  `angularFourier` is a pointwise
Bochner transform, so this quantity is faithful on the `L¹ ∩ L²` fields it is
applied to (Schwartz, smooth compactly supported, and the profiles of
lem:correction) and must not be used on a general `H^∞` slice — `sobolevENorm`
is the general-purpose spatial norm. -/
def homogeneousFourierENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  (∑ i : Fin 3, ∫⁻ ξ : Space,
      ENNReal.ofReal (‖ξ‖ ^ (2 * s) *
        ‖angularFourier (fun x => ((z x i : ℝ) : ℂ)) ξ‖ ^ 2)) ^ ((2 : ℝ)⁻¹)

/-- `04-whole-space.tex:91` and `appendix-b-embeddings.tex:31`:
`‖z‖_{Ḣ^{3/2}} = ‖Λ^{3/2}z‖₂`, required to exist as a quantity even though
`Ḣ^{3/2}` is never completed to a space. -/
abbrev dotHThreeHalvesENorm (z : SpatialField) : ℝ≥0∞ :=
  homogeneousFourierENorm (3 / 2) z

/-- `04-whole-space.tex:85` prop:Rcritical1: `‖a‖_{Ḣ^{1/2}}`, the critical
homogeneous quantity of the small-data hypothesis. -/
abbrev dotHHalfENorm (z : SpatialField) : ℝ≥0∞ :=
  homogeneousFourierENorm (1 / 2) z

/-! ## 5. The energy norm `E_T` -/

/-- `01-introduction.tex:143` eq:Enorm, first summand:
`‖z‖_{L^∞(0,T;L²(R³))}`, on the *open* interval `(0,T)`, so no endpoint value
at `T` is imposed (`01-introduction.tex:150`). -/
def energyEssSup (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  essSup (fun t => eLpNorm (fun x => z (t, x)) 2 volume)
    (volume.restrict (Ioo (0 : ℝ) T))

/-- `01-introduction.tex:145` eq:Enorm: the spatial gradient at a fixed time,
assembled as the Euclidean vector of the three coordinate derivatives, so that
its norm is the Frobenius quantity `(∑_{i,j} |∂_i z_j|²)^{1/2}` demanded by
"sum the squared component norms" — deliberately *not* the operator norm of
`spatialDerivative`, which is a different (equivalent but unequal) number. -/
def spatialGradient (z : SpaceTimeField) (t : ℝ) (x : Space) : WithLp 2 (Fin 3 → Space) :=
  WithLp.toLp 2 (fun i => spatialDerivative z t x (coordinateVector i))

/-- `01-introduction.tex:145` eq:Enorm, second summand:
`‖∇z‖_{L²(0,T;L²(R³))}`. -/
def energyGradient (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (eLpNorm (fun x => spatialGradient z t x) 2 volume) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `01-introduction.tex:143` eq:Enorm:
`‖z‖_{E_T} = ‖z‖_{L^∞(0,T;L²)} + ‖∇z‖_{L²(0,T;L²)}`, on `(0,T)` with no
endpoint value at `T`.

A returned `ℝ≥0∞`; B returned `ℝ` through `.toReal`, which `REVIEW_B` issue 2
showed makes the *bound* eq:REclose satisfiable by a field of infinite energy.
Chosen: A's `ℝ≥0∞`, so the bound is never vacuous. -/
def energyENorm (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  energyEssSup T z + energyGradient T z

/-! ## 6. Initial-velocity classes -/

/-- `02-preliminaries.tex:12` eq:Rinitial, the factor
`H^∞(R³;R³) = ⋂_{m≥0} H^m`.  Membership in every integer-order `H^m` is stated
through the same order-`m` datum as everywhere else in this file, so that
"`H^m`" means one thing throughout.  `ContDiff` is redundant for a field in
every `H^m` (Sobolev embedding) but pins the smooth representative, which the
pointwise divergence condition and the classical equation both need.

A used the datum form; B used the physical jet form
(`∀ n, MemLp (iteratedFDeriv ℝ n a) 2 volume`, field-for-field
`EulerLpTranslation.SmoothL2Field`).  Chosen: the datum form, for uniformity
with `F_R` and with the solution class; the equivalence with B's jet form is
unit L2, which is what binds to the upstream structure.

No Fréchet topology is attached: eq:Rinitial fixes only the set, and thm:Rmain
topologizes only the force side. -/
def MemHInfty (a : SpatialField) : Prop :=
  ContDiff ℝ ∞ a ∧ ∀ m : ℕ, ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) a A

/-- `02-preliminaries.tex:6,12`, the factor `L²_σ(R³)`: the classical Euclidean
divergence vanishes identically.  Reuses the upstream `spatialDivergence` on the
time-independent lift of `a`, so that one divergence operator serves the datum
class and the solution class.  Equality with the closed divergence-free subspace
of `L²` for `H^∞` fields is a lemma (unit L3).  A and B agree up to spelling;
B's reuse of `spatialDivergence` is chosen. -/
def IsSolenoidal (a : SpatialField) : Prop :=
  ∀ x : Space, spatialDivergence (fun z : SpaceTime => a z.2) 0 x = 0

/-- `02-preliminaries.tex:12` eq:Rinitial:
`X_R = H^∞(R³;R³) ∩ L²_σ(R³)`. -/
def initialClassR : Set SpatialField := {a | MemHInfty a ∧ IsSolenoidal a}

/-- `04-whole-space.tex:192`: `S_σ = 𝓢(R³;R³) ∩ L²_σ`, the initial class of the
rapid-decay formulation used by cor:Rclasses.  Only B defined it. -/
def initialClassSchwartz : Set SpatialField :=
  {a | (∃ φ : SchwartzMap Space Space, ⇑φ = a) ∧ IsSolenoidal a}

/-! ## 7. Force classes -/

/-- `02-preliminaries.tex:17` eq:Rclasses:
`F_R = {f ∈ C^∞([0,∞);H^∞) : ‖f‖_{L¹_tH^m_x} + ‖f‖_{L²_tH^m_x} < ∞`
for every integer `m ≥ 0}`.

* `ContDiffOn ℝ ∞ f futureDomain` is smoothness of the **physical field
  itself** on `R³ × [0,∞)`, one-sided in time at zero.  Draft A omitted it;
  `REVIEW_A` issue 1 showed that without it `MemForceR` is stable under
  modification of `f` on a null set, which makes `B^R_{ν,a,T}` leak, Theorem
  4.1(i) vacuous and the "only if" of 4.1(ii) false.  Draft B carried it.
  Chosen: B.
* `ContDiffOn ℝ ∞ G (Ici 0)` is the manuscript's "smoothness into each `H^m`,
  with one-sided time derivatives at zero" (`02-preliminaries.tex:22`);
  `Ici 0` is `UniqueDiffOn`, so the one-sided derivative is determined.
* `MemLp _ 1` and `MemLp _ 2` over `positiveTimeMeasure` are the two finiteness
  requirements on `(0,∞)`, in the strongly measurable Bochner sense of
  `01-introduction.tex:118`.
* Reality is automatic: `RealVectorSobolev` is the conjugate-reflection
  subspace.
* No compact support and no vanishing near `t = 0` is imposed
  (`02-preliminaries.tex:24`), and nothing constrains `t < 0`
  (see `AgreesOnFuture`).

Stated as a predicate on `SpaceTimeField` rather than as a bundled structure
(draft B's `ForceR`), so that `F_c ⊆ F_rd ⊆ F_R` are set inclusions in one
type and `maximalLifespanR ν a ·` is literally the same function on all three —
`research/section4/STATEMENTS.md` §9 items 11 and 12. -/
def MemForceR (f : SpaceTimeField) : Prop :=
  ContDiffOn ℝ ∞ f futureDomain ∧
    ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      IsSobolevPath (m : ℝ) f G ∧
      ContDiffOn ℝ ∞ G futureTimes ∧
      MemLp G 1 forceTimeMeasure ∧
      MemLp G 2 forceTimeMeasure

/-- `02-preliminaries.tex:17` eq:Rclasses: the set `F_R`. -/
def forceClassR : Set SpaceTimeField := {f | MemForceR f}

/-- `04-whole-space.tex:185`: `F_c = C_c^∞(R³ × (0,∞);R³)`.  The support
condition is the pinned upstream `CompactPositiveTimeSupport`, i.e. compact
`tsupport` contained in `t > 0`; global `ContDiff` is then the zero extension.
A and B agree. -/
def MemForceCompact (f : SpaceTimeField) : Prop :=
  ContDiff ℝ ∞ f ∧ NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f

/-- `04-whole-space.tex:185`: the set `F_c`. -/
def forceClassCompact : Set SpaceTimeField := {f | MemForceCompact f}

/-- `04-whole-space.tex:186-191`: `F_rd`, the rapidly decaying class
`{f ∈ C^∞(R³×[0,∞)) : sup (1+|x|+t)^N |∂_x^α ∂_t^j f| < ∞ for all N, α, j}`.
The manuscript's mixed `∂_x^α ∂_t^j` seminorm family is collected in the joint
order-`k` `iteratedFDerivWithin` on `futureDomain`, which is equivalent up to
dimensional constants absorbed by the per-`(N,k)` existential `C`.  No common
numerical bound on the seminorms is imposed (`04-whole-space.tex:192`).
Only B defined it. -/
def MemForceRapid (f : SpaceTimeField) : Prop :=
  ContDiffOn ℝ ∞ f futureDomain ∧
    ∀ N k : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      (1 + ‖x‖ + t) ^ N * ‖iteratedFDerivWithin ℝ k f futureDomain (t, x)‖ ≤ C

/-- `04-whole-space.tex:186`: the set `F_rd`. -/
def forceClassRapid : Set SpaceTimeField := {f | MemForceRapid f}

/-! ## 8. Pressure conventions -/

/-- `02-preliminaries.tex:31` "the scalar pressure is determined up to a
function of time", stated on an arbitrary time set so that the same relation
serves a solution on `[0,T)` and the *spatially constant* gauge of
`04-whole-space.tex:320` (the case of a constant `c`).

A indexed the relation by a horizon `T`, B stated it globally; the set-indexed
form chosen here subsumes both. -/
def PressureGaugeEquivOn (I : Set ℝ) (p q : SpaceTimeScalar) : Prop :=
  ∃ c : ℝ → ℝ, ∀ t ∈ I, ∀ x : Space, q (t, x) = p (t, x) + c t

/-- `02-preliminaries.tex:97`: the explicit potential
`p(x,t) = ∫₀¹ G(rx,t)·x dr` of the curl-free field `G` of eq:Rpressure, the
manuscript's chosen representative inside a `PressureGaugeEquivOn` class.
A and B transcribe it identically. -/
def pressurePotential (G : SpaceTimeField) : SpaceTimeScalar :=
  fun z => ∫ r in (0 : ℝ)..1, (inner ℝ (G (z.1, r • z.2)) z.2 : ℝ)

/-! ## 9. Classical solutions, lifespan and breakdown -/

/-- `02-preliminaries.tex` §2.1 and §2.3, prop:local, and
`appendix-a-local-theory.tex`: a classical whole-space solution of eq:NS on
`[0,T)` at viscosity `ν`, with initial velocity `a` and force `f`.

* `velocity_smooth`, `pressure_smooth`: smoothness on the closed-at-zero slab
  `[0,T) × R³`, so every time derivative at `t = 0` is one-sided and no
  extension to negative time is differentiated.
* `momentum` is imposed at interior times only.  `navierStokesResidual` takes
  an unrestricted two-sided `temporalDerivative`, which need not exist at
  `t = 0` for a field smooth only on `Ico 0 T ×ˢ univ`; this matches the pinned
  upstream convention.  A and B made the same choice; it is ratified here.
* `sobolev` encodes `02-preliminaries.tex:29`, "a classical velocity belongs to
  `C([0,S];H^m)` for every integer `m ≥ 0` on each compact interval of its
  lifespan", as a continuous order-`m` datum path on `Ico 0 T`.  A used this
  datum form; B used `L²` jet paths plus an a.e. identification.  Chosen: A's
  datum form, for uniformity with `MemForceR` and `MemHInfty`.
* `pressure_gradient`: `02-preliminaries.tex:101` "There is no requirement that
  `p ∈ L²(R³)`.  Its gradient belongs to `L²`, so a nonzero constant pressure
  gradient is excluded."  Only the gradient is constrained, so the scalar
  pressure is determined exactly up to `PressureGaugeEquivOn (Ico 0 T)`.
* eq:Rpressure in its `(I-P)` form is deliberately not a field: for a smooth
  solenoidal solution it follows from `momentum` and `divergence` together with
  `∇p ∈ L²`.  Deriving it is a lemma (unit L9). -/
structure ClassicalSolutionR (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) where
  /-- The velocity field. -/
  velocity : SpaceTimeField
  /-- The pressure field, fixed only up to a function of time. -/
  pressure : SpaceTimeScalar
  /-- The horizon is a genuine interval. -/
  horizon_pos : 0 < T
  /-- Smoothness on `[0,T) × R³`, one-sided at `t = 0`. -/
  velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- Smoothness of the pressure on `[0,T) × R³`. -/
  pressure_smooth : ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- `u(·,0) = a`. -/
  initial : ∀ x : Space, velocity (0, x) = a x
  /-- `∇·u = 0` on `[0,T)`. -/
  divergence : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 0
  /-- eq:NS at viscosity `ν`, at interior times. -/
  momentum : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)
  /-- `u ∈ C([0,S];H^m)` for every integer `m ≥ 0` on each compact subinterval. -/
  sobolev : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    ContinuousOn G (Ico (0 : ℝ) T) ∧
      ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => velocity (t, x)) (G t)
  /-- `∇p ∈ L²`; excludes a nonzero constant pressure gradient. -/
  pressure_gradient : ∀ t ∈ Ico (0 : ℝ) T,
    MemLp (fun x : Space => pressureGradient pressure t x) 2 volume

/-- `02-preliminaries.tex:32` "local uniqueness defines a maximal classical
lifespan, denoted by `T^ν_{max,R}(a,f)`": the supremum of the horizons carrying
a classical solution, valued in `[0,∞]` so that global regularity is `⊤`, as
prop:Rcritical1 writes it.  The empty supremum is `0`, so a datum with no
solution at all has lifespan `0`; every downstream statement must therefore
carry the membership hypotheses.  A and B agree; the argument order
`ν a f T` of B is used. -/
def maximalLifespanR (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨆ S : ℝ, ⨆ _ : Nonempty (ClassicalSolutionR ν a f S), ENNReal.ofReal S

/-- `02-preliminaries.tex:34`: a reference solution is *regular through `T`* if
it extends smoothly to `[0,T+δ]` for some `δ > 0`; the half-open form on
`T + δ` is equivalent after shrinking `δ`.  Hypothesis of thm:Rinsert and of
the second case in the proof of thm:Rmain.  A and B agree. -/
def RegularThrough (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionR ν a f (T + δ))

/-- `02-preliminaries.tex:42` eq:Rsingularforces, stated relative to an
arbitrary ambient force class `Y`: `{f ∈ Y : T^ν_{max,R}(a,f) ≤ T}`.  Section 4
uses `Y = F_R` (thm:Rmain), `Y = F_c` and `Y = F_rd` (cor:Rclasses,
prop:Renergy), always with the *same* lifespan function
(`research/section4/STATEMENTS.md` §9 item 12). -/
def breakdownSetIn (Y : Set SpaceTimeField) (ν : ℝ) (a : SpatialField) (T : ℝ) :
    Set SpaceTimeField :=
  {f | f ∈ Y ∧ maximalLifespanR ν a f ≤ ENNReal.ofReal T}

/-- `02-preliminaries.tex:42` eq:Rsingularforces:
`B^R_{ν,a,T} = {f ∈ F_R : T^ν_{max,R}(a,f) ≤ T}`. -/
def breakdownSetR (ν : ℝ) (a : SpatialField) (T : ℝ) : Set SpaceTimeField :=
  breakdownSetIn forceClassR ν a T

/-- `02-preliminaries.tex:41` eq:Rsingularforces:
`B^{R,0}_{ν,T} = B^R_{ν,0,T}`, the zero-datum case for which
`04-whole-space.tex:11` thm:Rmain (ii) is an if-and-only-if. -/
def breakdownSetRZero (ν T : ℝ) : Set SpaceTimeField :=
  breakdownSetR ν (fun _ => 0) T

/-! ## 10. Relative and completed density -/

/-- `01-introduction.tex:137` "We give each smooth force class the relative
topology induced by the stated norm" and `04-whole-space.tex:8` thm:Rmain:
density of `S` in the ambient smooth class `Y` for the relative
`L^q(0,∞;H^s(R³))` topology, in the `ε`-approximation form with which the proof
of thm:Rmain opens (`04-whole-space.tex:177`).  For a topology induced by a
pseudometric this is density.

Parametric in the ambient class `Y` so that thm:Rmain (`Y = F_R`) and
cor:Rclasses (`Y ∈ {F_c, F_rd}`) are one predicate — the fix recommended by
`research/section4/REVIEW.md` item 17.  A and B both used the `ε` form; A fixed
`Y = F_R`, B fixed `Y` to the whole bundled force type. -/
def RelativelyDense (q : ℝ≥0∞) (s : ℝ) (Y S : Set SpaceTimeField) : Prop :=
  ∀ g ∈ Y, ∀ r : ℝ≥0∞, 0 < r → ∃ f ∈ S, forceSobolevENorm q s (f - g) < r

/-- `04-whole-space.tex:10` thm:Rmain (i)/(ii), instantiated at the breakdown
set: the exact predicate asserted for `a ∈ X_R` when `s < s_q`. -/
def BreakdownDenseR (ν : ℝ) (a : SpatialField) (T : ℝ) (q : ℝ≥0∞) (s : ℝ) : Prop :=
  RelativelyDense q s forceClassR (breakdownSetR ν a T)

/-- `04-whole-space.tex:219` prop:Renergy: density of `S` in the **full** Bochner
space `L^q(0,∞;H^s(R³))`, i.e. against an arbitrary element of the completion
rather than against a smooth force.

Draft B quantified the target over *all* `ℝ → ForceDistribution`;
`REVIEW_B` issue 1 showed that this makes the predicate false for every `S`
(a target off `H^s` sits at distance `⊤` from everything), so prop:Renergy
stated with it is unprovable.  Fixed here by quantifying the target over the
completion itself: a datum path with finite Bochner norm and strong
measurability, i.e. `MemBochnerDatum`.  This is a genuinely different predicate
from `RelativelyDense` — `research/section4/STATEMENTS.md` §9 item 11 requires
the two roles to be distinguishable. -/
def CompletedDense (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) : Prop :=
  ∀ b : ℝ → RealVectorSobolev s, MemBochnerDatum q s b →
    ∀ r : ℝ≥0∞, 0 < r →
      ∃ f ∈ S, ∃ D : ℝ → RealVectorSobolev s,
        IsSobolevPath s f D ∧ bochnerDatumENorm q s (D - b) < r

/-! ## 11. Cell averages on prescribed grids (thm:Rgrid) -/

/-- `04-whole-space.tex:288` "a complete uniform Cartesian grid of `R³` with
positive mesh widths".  Reuses `NSFormalization.Paper3.CartesianGrid`, which is
the shape recommended by `research/section4/STATEMENTS.md` §8.9: **per-axis
mesh widths**, an **arbitrary offset**, and **half-open cells**
(`CartesianGrid.cell k = {x | ∀ j, offset j + width j * k j ≤ x j <
offset j + width j * (k j + 1)}`).  Half-open cells fix the convention on grid
faces and partition all of `R³`, the grid has infinitely many cells indexed by
`Fin 3 → ℤ`, and every cell has positive finite volume.  Only B reached this
object. -/
abbrev Grid := CartesianGrid

/-- `04-whole-space.tex:291`: `(A_h z)_C = |C|^{-1} ∫_C z dx`, the cell average
of a locally integrable vector field, in the manuscript's vector form.  The
componentwise spelling
`NSFormalization.Paper3.componentCellAverage` (`Paper3/CompactObservations.lean:62`)
already exists and carries the grid observation theorems; agreement of the two
is unit L11. -/
def cellAverage (C : Set Space) (z : SpatialField) : Space :=
  ((volume C).toReal)⁻¹ • ∫ x in C, z x

/-- `04-whole-space.tex:290`: the cell-observation map
`A_h : L¹_loc(R³;R³) → (R³)^{T_h}`, with the full index family `Fin 3 → ℤ` as
the sequence codomain and coordinatewise equality
(`04-whole-space.tex:293`, "Only coordinatewise equality in this codomain is
needed").  The volume-weighted sequence norm of `04-whole-space.tex:294` is not
defined here; thm:Rgrid does not use it. -/
def gridObservation (grid : Grid) (z : SpatialField) : (Fin 3 → ℤ) → Space :=
  fun k => cellAverage (grid.cell k) z

end BlowupDensity.Contracts.V1.Data
