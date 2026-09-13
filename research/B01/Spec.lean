import Contracts.V1.Data

/-!
# B01 draft specification: real positive-time Bochner approximation

Task `collaboration/tasks/B01.md`, graph node `B01` in
`formalization/blueprint/DEPENDENCY_GRAPH.md:313-320`, consumed by `R46`
(`research/section4/STATEMENTS.md:823-838`).

This file is a *specification draft only*.  It contains `def`s and one
obligation record.  It proves nothing with mathematical content, assumes
nothing, and introduces no `axiom`, no `sorry` and no abstract `Prop`
placeholder field: every propositional field is a fully spelled-out statement
about explicitly named objects of `Contracts.V1.Data`.

## What is specified

The **approximation half** of Proposition 4.6 (`prop:Renergy`,
`paper/sections/04-whole-space.tex:218-229`), in its inhomogeneous realization:
the four stages of the proof at `04-whole-space.tex:232-260`, packaged as the
single statement that `F_c` is dense in the completed Bochner space
`L^q(0,∞;H^s(R³;R³))`.

The stages, in the manuscript's order:

1. `04-whole-space.tex:233-237` — Fourier truncation and mollification of
   `G = ⟨ξ⟩^s ĥ ∈ L²` give Schwartz `h_n → h` in `H^s`, "by the isometry
   defining `H^s`".  Field `schwartzApprox`.
2. `04-whole-space.tex:238-243` — the spatial cutoff `χ_R(x) = χ(x/R)`:
   `‖(1−χ_R)h_n‖_{H^m} → 0` for every integer `m ≥ 0`, and
   `‖z‖_{H^s} ≤ ‖z‖_{H^m}` for `m ≥ max(s,0)`.  Fields `χ`…`chi_range` and
   `cutoffApprox`.
3. `04-whole-space.tex:250-252` — "take real parts of each component of the
   approximants"; conjugation is an isometry for these real even weights.  This
   stage is invisible in Lean, because `RealVectorSobolev s` *is* the
   conjugate-reflection subspace (`02-preliminaries.tex:74`,
   `Data.lean` §2), so 1–3 are packaged as the single field `spatialApprox`.
4. `04-whole-space.tex:253-260` — the Bochner stage: restrict to `[1/N,N]`,
   approximate by finite simple functions, approximate each `E_j` by a finite
   union of intervals, smooth the indicators.  Field `temporalApprox`.

Stage 4 is written for "any of the preceding separable Hilbert spaces `X`"
(`04-whole-space.tex:253`) and is therefore stated here on the *datum* carrier
`RealVectorSobolev s`, which `Data.lean` §4 records as the common carrier of the
`H^s` and `Ḣ^s` realizations.  `B02` reuses `temporalApprox` verbatim; only its
spatial stage differs.  See the interface note in `research/B01/COMPARISON.md`.

## The `s` and `q` ranges

Explicitly, and contrary to what the surrounding statement of `prop:Renergy`
might suggest:

* **`s` is arbitrary real.**  `04-whole-space.tex:233` "Fix any real `s`" and
  `04-whole-space.tex:243` "proves spatial compact-smooth density in `H^s` for
  every real `s`".  No stage of the approximation uses `s < s_q`.
* **`q` is any exponent in `[1,∞)`.**  `04-whole-space.tex:253` "Write `X` for
  any of the preceding separable Hilbert spaces and `1 ≤ q < ∞`."

The threshold `s < s_q = 2/q − 3/2` (`04-whole-space.tex:8`,
`Data.lean.criticalOrder`) belongs to the *singular*-force half of `prop:Renergy`
— the appeal to `cor:Rclasses` at `04-whole-space.tex:262-264`, i.e. node
`R41D`/`R45` — and never to `B01`.  `manuscriptApproximation` below records the
instance `R46` actually consumes, with the threshold hypothesis present but
unused, so that no reader mistakes `B01` for a thresholded statement.

## The completion object

`R46` quantifies over "each full Bochner space `L^q(0,∞;H^s(R³))`"
(`04-whole-space.tex:219`).  The shape proposed here, and the one already fixed
by `Data.lean.CompletedDenseVia`, is the **datum-path** form: a target is a
function `b : ℝ → RealVectorSobolev s` with `MemBochnerDatum q s b`, i.e.
`MemLp b q (volume.restrict (Ioi 0))`, and the distance to it is
`bochnerDatumENorm q s (D − b) = eLpNorm (D − b) q (volume.restrict (Ioi 0))`.

The ledger asks in addition for a Bochner *space object*
(`⟪D01:BochnerLq q X⟫`, `research/section4/STATEMENTS.md:812-814`).  That object
is `bochnerSpace q s = Lp (RealVectorSobolev s) q forceTimeMeasure`, which is
also the object the existing source theorem
`NSFormalization.Paper3.exists_angular_real_vector_positive_physical_approx`
quantifies over.  The two are identified by the three fields
`completionRepresentative`, `completionSurjective`, `completionNorm`, together
with `completionCongr`; the path form is kept as the *primary* one because

* it is what `Data.lean.CompletedDenseVia` already quantifies over, and
  `REVIEW_B` issue 1 (`Data.lean:713-722`) fixed that choice deliberately;
* `IsSobolevPath` and `IsHomogeneousPath` are predicates on paths, not on `Lp`
  classes, so the two realizations of `prop:Renergy` share one predicate only in
  the path form;
* it avoids asserting anything about a quotient in the contract, while
  `completionSurjective` guarantees no element of the completion is missed.

## Conventions

* Time is the first spacetime coordinate
  (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:33`);
  `Space = EuclideanSpace ℝ (Fin 3)` (`ibid.:30`).
* Force norms use `(0,∞)`: `forceTimeMeasure = volume.restrict (Ioi 0)`
  (`01-introduction.tex:140`, `Data.lean:113-116`).
* `F_c = C_c^∞(R³ × (0,∞);R³)` is `Data.lean.MemForceCompact`
  (`04-whole-space.tex:185`): global smoothness plus compact `tsupport`
  contained in `Ioi 0 ×ˢ univ`.
* `supp` of the manuscript is `tsupport`.
* Every norm is the `ℝ≥0∞`-valued one of `Data.lean`, so nothing has to be
  assumed finite in order to be written.
-/

noncomputable section

namespace BlowupDensity.B01.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. Named objects of the approximation -/

/-- `04-whole-space.tex:239`, `χ_R(x) = χ(x/R)`: the dilated spatial cutoff of
stage 2.  Written with `R⁻¹ • x` so that no positivity of `R` is needed to form
the expression; `cutoffApprox` takes `R → ∞`. -/
def scaledCutoff (χ : Space → ℝ) (R : ℝ) : Space → ℝ := fun x => χ (R⁻¹ • x)

/-- `04-whole-space.tex:260`, "the finite sum `Σ_j φ_j(t) h_j(x)`": the physical
spacetime field assembled from smooth compactly supported time factors `φ` and
smooth compactly supported spatial profiles `h`.  This is the shape in which
`B01` hands an element of `F_c` to `R46`
(`research/section4/STATEMENTS.md:826-830`). -/
def separatedField {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField) :
    SpaceTimeField :=
  fun z => ∑ j, φ j z.1 • h j z.2

/-- The order-`s` datum path of `separatedField φ h`, when `A j` is the datum of
`h j`: the same finite sum taken in `RealVectorSobolev s`.  `separatedAssembly`
asserts that this is indeed the datum path. -/
def separatedPath {J : ℕ} {s : ℝ} (φ : Fin J → ℝ → ℝ)
    (A : Fin J → RealVectorSobolev s) : ℝ → RealVectorSobolev s :=
  fun t => ∑ j, φ j t • A j

/-- `04-whole-space.tex:219` and `research/section4/STATEMENTS.md:812-814`
`⟪D01:BochnerLq q X⟫`: the full Bochner space `L^q(0,∞;H^s(R³;R³))` as a bundled
Banach space, i.e. the completion object of `prop:Renergy` read through the
`H^s` isometry `h ↦ ⟨ξ⟩^s ĥ` of `02-preliminaries.tex:70-74`.  Its underlying
carrier is `Data.lean`'s datum type, so the *same* type is the `Ḣ^s` completion
of `B02`; only the realization predicate distinguishes them
(`Data.lean:200-210, 380-390`). -/
abbrev bochnerSpace (q : ℝ≥0∞) (s : ℝ) := Lp (RealVectorSobolev s) q forceTimeMeasure

/-! ## 2. The contract -/

/-- Every obligation that the approximation half of Proposition 4.6
(`prop:Renergy`, `paper/sections/04-whole-space.tex:218-229`, proof at
`:232-260`) places on the inhomogeneous completed force space, in exactly the
form `R46` consumes (`research/section4/STATEMENTS.md:823-830`).

Layout of the fields.

* `χ … chi_range`: the fixed cutoff of `04-whole-space.tex:238-239`.
* `schwartzApprox`, `cutoffApprox`, `spatialApprox`: stages 1–3, the spatial
  half.  `spatialApprox` is the only one `approxCompact` needs; the other two
  are the manuscript's own intermediate displays, kept separately because
  `04-whole-space.tex:243` states stage 2 as a limit in `R` rather than as an
  `ε`-approximation, and because `B02`'s spatial stage
  (`04-whole-space.tex:245-250`) is stated by contrast with them.
* `temporalApprox`: stage 4, the Bochner step.  Shared verbatim with `B02`.
* `separatedAssembly`: the packaging of a finite separated sum as an element of
  `F_c` together with its datum path, `04-whole-space.tex:259-260`.
* `approxCompact`: the conclusion, in `Data.lean`'s `CompletedDense`.
* `completionRepresentative … completionCongr`: the identification of the
  datum-path completion with the bundled Bochner space `bochnerSpace q s`.
* `compactSubsetForceR`: `F_c ⊆ F_R`, the clause that makes "smooth compact
  forces" usable where `T^ν_{max,R}` and `cor:Rclasses` live.

Nothing about `Ḣ^{-1}` appears here; that is `B02`
(`04-whole-space.tex:244-252`), which consumes `temporalApprox` and
`separatedAssembly` unchanged.

No field is a hypothesis about an unspecified proposition, and no field is
`True`, `∃ x, True` or any similar placeholder. -/
structure BochnerApproxAPI where
  -- ### The fixed spatial cutoff, `04-whole-space.tex:238-239`
  /-- `χ ∈ C_c^∞`, "equal to one on the unit ball and zero outside the ball of
  radius two, with `0 ≤ χ ≤ 1`", `paper/sections/04-whole-space.tex:238`. -/
  χ : Space → ℝ
  /-- `χ` is smooth, `04-whole-space.tex:238`. -/
  chi_smooth : ContDiff ℝ ∞ χ
  /-- `χ = 1` on the closed unit ball, `04-whole-space.tex:238`. -/
  chi_one : ∀ x : Space, ‖x‖ ≤ 1 → χ x = 1
  /-- `χ = 0` outside the ball of radius two, `04-whole-space.tex:238`.  With
  `chi_smooth` this gives `HasCompactSupport χ`. -/
  chi_vanishes : ∀ x : Space, 2 ≤ ‖x‖ → χ x = 0
  /-- `0 ≤ χ ≤ 1`, `04-whole-space.tex:238`. -/
  chi_range : ∀ x : Space, χ x ∈ Icc (0 : ℝ) 1

  -- ### Stage 1: Schwartz approximation through the `H^s` isometry
  /-- `04-whole-space.tex:233-237`.  "Fix any real `s`, and let `h ∈ H^s`.
  Approximate `G = ⟨ξ⟩^s ĥ ∈ L²` by `G_n ∈ C_c^∞` in `L²` … By the isometry
  defining `H^s`, `h_n → h` in `H^s`."  Stated directly on the datum, since
  `RealVectorSobolev s` *is* the `L²` datum space that the isometry lands in:
  every datum is approximated by the datum of a real vector Schwartz field.

  Every real `s` is covered; no threshold enters. -/
  schwartzApprox : ∀ (s : ℝ) (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
    ∃ (ψ : SchwartzMap Space Space) (Z : RealVectorSobolev s),
      IsSobolevDatum s (⇑ψ) Z ∧ ‖Z - A‖ₑ < η

  -- ### Stage 2: the spatial cutoff
  /-- `04-whole-space.tex:238-243`.  "For fixed `n` and any nonnegative integer
  `m`, Leibniz' rule shows `‖(1−χ_R)h_n‖_{H^m} → 0` … Choosing `m ≥ max(s,0)`
  and using `‖z‖_{H^s} ≤ ‖z‖_{H^m}` proves spatial compact-smooth density in
  `H^s` for every real `s`."

  The `H^m`-to-`H^s` comparison is already absorbed: the limit is asserted at
  the order `s` that the conclusion needs, which is what the manuscript's two
  sentences jointly give.  `sobolevENorm` is `⊤` on a slice with no order-`s`
  datum, so the statement is not weakened by the totalization. -/
  cutoffApprox : ∀ (s : ℝ) (ψ : SchwartzMap Space Space),
    Filter.Tendsto
      (fun R : ℝ => sobolevENorm s (fun x => (1 - scaledCutoff χ R x) • ψ x))
      Filter.atTop (nhds 0)

  -- ### Stages 1–3 combined: real compact smooth spatial density
  /-- `04-whole-space.tex:243` together with `:250-252`.  "These constructions
  also prove the real vector-valued versions: take real parts of each component
  of the approximants."

  Physical `C_c^∞(R³;R³)` real vector fields are dense in `H^s(R³;R³)` for every
  real `s`.  This is the only spatial input `approxCompact` uses; it is the
  conjunction of `schwartzApprox` and `cutoffApprox`, with the real-part step
  discharged by the fact that `RealVectorSobolev s` is the conjugate-reflection
  subspace (`02-preliminaries.tex:74`). -/
  spatialApprox : ∀ (s : ℝ) (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
    ∃ (h : SpatialField) (H : RealVectorSobolev s),
      ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ IsSobolevDatum s h H ∧ ‖H - A‖ₑ < η

  -- ### Stage 4: the Bochner step, shared with `B02`
  /-- `04-whole-space.tex:253-260`.  "Write `X` for any of the preceding
  separable Hilbert spaces and `1 ≤ q < ∞`.  Given `b ∈ L^q((0,∞);X)`, first
  restrict it to `[1/N,N]` … strongly measurable functions can be approximated
  in `L^q` by finite simple functions `Σ_j 1_{E_j} b_j` … Each measurable
  `E_j ⊂ [1/N,N]` can be approximated in measure by a finite union of intervals
  lying in a fixed compact subset of `(0,∞)` … Smoothing their indicators by
  convolution gives `φ_j ∈ C_c^∞((0,∞))`."

  Stated on the datum carrier and *not* on a realization, so that `B02` uses
  this field verbatim at `X = Ḣ^{-1}(R³;R³)`: `Data.lean:200-210` records that
  `bochnerDatumENorm` is literally the same expression for both realizations,
  and `Data.lean:380-390` that both realizations read paths into the same
  `RealVectorSobolev s`.

  The coefficients `A j` are arbitrary elements of the completion's fibre; the
  spatial compactness of the profiles is supplied separately by
  `spatialApprox`, exactly as `04-whole-space.tex:256` ("Approximate each `b_j`
  by a physical `h_j ∈ C_c^∞(R³)` in `X`") separates the two errors. -/
  temporalApprox : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ (s : ℝ)
      (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b →
      ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      bochnerDatumENorm q s (separatedPath φ A - b) < η

  -- ### Packaging a separated sum as an element of `F_c`
  /-- `04-whole-space.tex:259-260`.  "Thus the finite sum `Σ_j φ_j(t)h_j(x)`
  approximates `b` and is jointly smooth with compact support strictly inside
  `R³ × (0,∞)`.  This proves the claimed Bochner density with both kinds of
  compactness, rather than merely compactness of a Sobolev-valued time path."

  This is the field that makes time and space compactness *simultaneous*: it
  turns the pair (smooth compact time factors, smooth compact spatial profiles)
  into a single member of `F_c` whose `Data.lean` datum path is the
  corresponding finite sum, with the strong measurability that
  `CompletedDenseVia` requires. -/
  separatedAssembly : ∀ (s : ℝ) (J : ℕ) (φ : Fin J → ℝ → ℝ)
      (h : Fin J → SpatialField) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, HasCompactSupport (φ j)) →
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) →
      (∀ j, ContDiff ℝ ∞ (h j)) → (∀ j, HasCompactSupport (h j)) →
      (∀ j, IsSobolevDatum s (h j) (A j)) →
    MemForceCompact (separatedField φ h) ∧
      IsSobolevPath s (separatedField φ h) (separatedPath φ A) ∧
      AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure

  -- ### The conclusion
  /-- `04-whole-space.tex:219` prop:Renergy, approximation half:
  "Smooth compact forces … are dense in each full Bochner space
  `L^q(0,∞;H^s(R³))`", stripped of the breakdown condition
  `T^ν_{max,R}(a,f) ≤ T` (which `R46` supplies from `R41D` by the two-radius
  argument of `04-whole-space.tex:262-264`).

  `q` ranges over all of `[1,∞)` and `s` over all of `ℝ`, per
  `04-whole-space.tex:233` and `:253`.  `R46` uses `q ∈ {1,2}`; see
  `manuscriptApproximation`. -/
  approxCompact : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ,
    CompletedDense q s forceClassCompact

  -- ### Identification of the completion object
  /-- Every element of the bundled Bochner space `L^q(0,∞;H^s(R³;R³))` is a
  datum path in the sense of `Data.lean.MemBochnerDatum`
  (`01-introduction.tex:118`, "the space of strongly measurable maps with finite
  norm"). -/
  completionRepresentative : ∀ (q : ℝ≥0∞) (s : ℝ) (u : bochnerSpace q s),
    MemBochnerDatum q s (u : ℝ → RealVectorSobolev s)
  /-- Conversely every datum path is represented by an element of the bundled
  space, so quantifying `approxCompact` over paths misses no element of the
  completion. -/
  completionSurjective : ∀ (q : ℝ≥0∞) (s : ℝ) (b : ℝ → RealVectorSobolev s),
    MemBochnerDatum q s b →
      ∃ u : bochnerSpace q s, (u : ℝ → RealVectorSobolev s) =ᵐ[forceTimeMeasure] b
  /-- The two norms agree: `Data.lean`'s `bochnerDatumENorm` on a representative
  is the Banach norm of the class.  This is what lets `R46` state its
  conclusion with either object. -/
  completionNorm : ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (s : ℝ) (u : bochnerSpace q s),
    bochnerDatumENorm q s (u : ℝ → RealVectorSobolev s) = ‖u‖ₑ
  /-- `bochnerDatumENorm` only sees the a.e. class, which is the "identified
  almost everywhere" convention of `01-introduction.tex:124` and
  `02-preliminaries.tex:62`.  Together with the two previous fields this is the
  full identification of the path model with `bochnerSpace q s`. -/
  completionCongr : ∀ (q : ℝ≥0∞) (s : ℝ) (b c : ℝ → RealVectorSobolev s),
    b =ᵐ[forceTimeMeasure] c → bochnerDatumENorm q s b = bochnerDatumENorm q s c

  -- ### `F_c ⊆ F_R`
  /-- `04-whole-space.tex:185-193` cor:Rclasses, "Theorem~\ref{thm:Rmain}
  remains valid with `F_R` replaced by `F_c`": the compact class is a
  *subclass*, so every `f ∈ F_c` satisfies `eq:Rclasses`
  (`02-preliminaries.tex:17`).

  Concretely this discharges, for a spacetime compact smooth `f`, the two
  clauses of `Data.lean.MemForceR` that `MemForceCompact` does not mention:
  smoothness of the order-`m` datum path into `H^m` with one-sided derivatives
  at zero (`ContDiffOn ℝ ∞ G futureTimes`), and the finiteness
  `‖f‖_{L¹_tH^m_x} + ‖f‖_{L²_tH^m_x} < ∞` (`MemLp G 1` and `MemLp G 2` on
  `(0,∞)`), for every integer `m ≥ 0`.

  `B01` carries it because it is proved by exactly the slice-path machinery that
  `separatedAssembly` uses, and because without it the phrase "smooth compact
  forces with `T^ν_{max,R}(a,f) ≤ T`" of `04-whole-space.tex:219` does not
  connect to `breakdownSetR`. -/
  compactSubsetForceR : forceClassCompact ⊆ forceClassR

/-! ## 3. Derived statements -/

/-- The exact instance of `approxCompact` that `R46` consumes
(`research/section4/STATEMENTS.md:770-774, 826-830`): the two manuscript time
exponents, and the Sobolev range in which `prop:Renergy` states its density.

The hypothesis `s < s_q` is *present and unused*.  It is written here only so
that the shape matches `REnergyAPI.densityInhomogeneous`
(`research/section4/STATEMENTS.md:849-853`); `04-whole-space.tex:233,243`
establish the approximation for every real `s`, and the threshold is consumed
solely by the singular-force half at `04-whole-space.tex:262-264`. -/
def manuscriptApproximation : Prop :=
  ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ, s < criticalOrder q.toReal →
    CompletedDense q s forceClassCompact

/-- The stage-4 predicate in isolation, so that `B02` can require the *same*
proposition rather than a paraphrase of it: separated finite sums with
`C_c^∞((0,∞))` time factors are dense in the datum-path Bochner space.
`04-whole-space.tex:253-260`.

It mentions no realization, hence applies unchanged to the `Ḣ^{-1}` completion
of `04-whole-space.tex:244-252`. -/
def SeparatedTemporalDense (q : ℝ≥0∞) (s : ℝ) : Prop :=
  ∀ (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b → ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      bochnerDatumENorm q s (separatedPath φ A - b) < η

/-- The existential form of the contract, the object a later
`verification/Contracts/V1/BochnerApprox.lean` would register. -/
def bochnerApproxStatement : Prop := Nonempty BochnerApproxAPI

end BlowupDensity.B01.Draft
