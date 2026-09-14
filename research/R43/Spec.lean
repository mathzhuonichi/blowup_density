import Contracts.V1.Data

/-!
# R43 reconciled specification: Proposition 4.3, `prop:Rcritical1`

**Global regularity for small critical data and `L¹` force.**
Statement `paper/sections/04-whole-space.tex:82-89`; proof `:90-133`.
Graph node `R43 ← A04, A05, C01` (`formalization/blueprint/DEPENDENCY_GRAPH.md:62-64`),
transitively `← A02` through A04's continuation clause; consumer `R43 → R41`
(`:69`).  Ledger: `research/section4/STATEMENTS.md` §3 (`:428-563`); R41's
consumption `:128-135`.

Reconciliation of `DraftA.lean` (`CriticalRegularityL1API`, 13 fields) and
`DraftB.lean` (`RCritical1API`, 4 fields) against the paper and against the
sibling specs as they actually stand on this branch.  Decisions and their
reasons: `research/R43/RECONCILIATION.md`; field-by-field and gap tables:
`research/R43/COMPARISON.md`.

This file is a **specification**.  It contains one `def` and one `structure`;
it proves nothing with mathematical content, assumes nothing, and introduces no
`axiom`, no `sorry`, no `native_decide` and no abstract `Prop` placeholder
field.  Both propositional fields are fully spelled-out statements about named
`Contracts.V1.Data` objects.

## The statement (`04-whole-space.tex:82-89`)

> There is a universal `c > 0` such that, for `a ∈ 𝒳_ℝ` and `f ∈ 𝓕_ℝ`,
> `‖a‖_{Ḣ^{1/2}} + ‖f‖_{L¹_t Ḣ^{1/2}_x} < cν  ⟹  T^ν_{max,ℝ}(a,f) = ∞`.
> In particular, for `a = 0`, the ball `‖f‖_{L¹_t H^{1/2}_x} < cν` consists of
> globally regular inputs.

Quantifier order, transcribed exactly (`research/section4/STATEMENTS.md:441`):

    ∃ c > 0, ∀ ν > 0, ∀ a ∈ 𝒳_ℝ, ∀ f ∈ 𝓕_ℝ, (smallness ⟹ T_max = ∞).

`c` is a **single** real, chosen before every `ν`, `a`, `f`; it is a field of
the structure, so both conclusion clauses are bound by the same `c`
(`STATEMENTS.md:522`, clarification 8 at `:1288-1291`).  A `c` allowed to depend
on `ν` would still be true but would destroy the `cν`-ball scaling Theorem 4.1's
converse and Corollary 4.5 need.  `a` is **quantified** over `𝒳_ℝ`, not fixed
and not zero (contrast Proposition 4.4, where `a = 0` is essential).  The force
time norm runs over `(0,∞)`.  The conclusion is **global** regularity, not
regularity up to a horizon.

## Why exactly these four fields

`research/section4/STATEMENTS.md:504-520` proposes precisely this skeleton, and
`R41` consumes precisely one of the two conclusion clauses —
`inhomogeneousAtZero`, through `RMainAPI.nonDensityZero` at `q = 1`
(`STATEMENTS.md:128-135`, `:160-164`).  No task in
`formalization/blueprint/DEPENDENCY_GRAPH.md` consumes an intermediate quantity
of Proposition 4.3's proof: `R44` has the *same three children* `A04, A05, C01`
(`STATEMENTS.md:598`) and reaches them directly, and `R45` reaches R43 only
through `R41` (`:702-706`).  The clauses R43's proof passes through are
therefore **not** restated as fields here; they live in their owners' contracts
and are tabulated in `COMPARISON.md` §2 with the sibling `file:line` each must
stay identical to:

| consumed | owner, as it actually stands |
|---|---|
| `‖u‖₃ ≤ C‖u‖_{Ḣ^{1/2}}`, `‖∇u‖₃+‖Λu‖₃ ≤ C‖u‖_{Ḣ^{3/2}}`, `‖∇u‖₆ ≤ C‖Δu‖₂` | `research/A05/Spec.lean:366,384,396` |
| `‖z‖_{Ḣ^a} ≤ ‖z‖_{H^a}` on `H^∞` fields | `research/A05/Spec.lean:268` |
| eq:RL2, eq:RH1, the `∫₀ˢ‖u‖²_{H²}` assembly | `research/C01/Spec.lean:383,532,576` |
| the continuation criterion at a finite lifespan | `research/A04/Spec.lean:657` |
| the maximal solution family | `research/A02/Spec.lean:421`, predicate `:210` |

Draft A restated five of these as structure fields.  Now that A04 and C01
exist, four of those restatements are **not** the siblings' actual types
(`COMPARISON.md` §3), so carrying them would create a second, divergent copy of
each sibling statement — the drift `CLAUDE.md` §"合同 import 规则" forbids.  They
are dropped; Draft B's shape is adopted.

## Conventions and the one non-`Data.lean` object

Every quantified object is `verification/Contracts/V1/Data.lean`'s:
`initialClassR` is `𝒳_ℝ` (`Data.lean:509`, eq:Rinitial `02-preliminaries.tex:12`),
`MemForceR` is `𝓕_ℝ` (`Data.lean:544`, eq:Rclasses `:17`),
`maximalLifespanR ν a f` is `T^ν_{max,ℝ}(a,f)` valued in `[0,∞]` with `⊤` for
global regularity (`Data.lean:657`, `02-preliminaries.tex:32`),
`forceHomogeneousENorm 1 (1/2) f` is `‖f‖_{L¹(0,∞;Ḣ^{1/2})}` (`Data.lean:390`),
`forceSobolevENormL1 (1/2) f` is `‖f‖_{L¹(0,∞;H^{1/2})}` (`Data.lean:231`).
Time is the first spacetime coordinate.

**Every norm is `ℝ≥0∞`-valued and none is routed through `.toReal`**, so a
missing datum fails safe to `⊤`, the smallness hypothesis then fails, and the
statement is never satisfied by accident.  The one direction that is *not*
fail-safe is a junk `0`, and avoiding it is the single load-bearing definitional
decision of this file:

**`Data.dotHHalfENorm` must not be used here.**  `Data.lean:427-430` defines it
as `homogeneousFourierENorm (1/2)`, and `Data.lean:410-414` defines that as the
literal pointwise Fourier integral
`(∑ᵢ ∫⁻ ξ, ofReal (‖ξ‖^(2s) * ‖angularFourier (zᵢ) ξ‖²))^(1/2)`.
`angularFourier g ξ = frequencyUnit^(-3/2) • 𝓕 g (frequencyUnit⁻¹ • ξ)`
(`formalization/NSFormalization/Source/FourierConvention.lean:23`) is a
**pointwise Bochner integral**, which Mathlib totalizes to `0` on a
non-integrable `g`; so for a field that is not `L¹` the whole expression is a
junk `0`, and `Data.lean:404-409` says so in as many words ("must not be used on
a general `H^∞` slice").  `𝒳_ℝ = H^∞ ∩ L²_σ` contains fields that are not `L¹`,
so `dotHHalfENorm a` would read `0` for a large datum, the smallness hypothesis
would hold **vacuously**, and `universal` would be a *false* statement.  Both
drafts rejected it independently and both are right.  The honest quantity is the
datum-infimum form below, `⊤` when no datum exists.
-/

noncomputable section

namespace BlowupDensity.R43.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal

/-! ## 0. The spatial homogeneous norm, in its honest realization -/

/-- ⟪A05:dotHomogeneousENorm⟫ — **must stay identical to
`research/A05/Spec.lean:131`.**

`appendix-b-embeddings.tex:26-27` and `04-whole-space.tex:85`, `‖z‖_{Ḣ^s}` **for
a physical field**: the `L²` norm of the order-`s` homogeneous datum of the
tempered vector distribution the field represents, and `⊤` when the field has no
such datum.  The empty infimum in `ℝ≥0∞` is `⊤`, so the quantity is total and
fail-safe.

Reproduced verbatim, with the general order `s` rather than specialized to
`s = 1/2`, because `research/` drafts are not Lean library modules and cannot be
`import`ed; keeping A05's name and arity means that when A05 registers under
`verification/Contracts/`, this `def` is deleted and the two occurrences below
become `A05.dotHomogeneousENorm`, with no change of spelling.  `Data.lean`
supplies the ingredients — `IsHomogeneousSliceDatum` (`Data.lean:364`),
`homogeneousVectorENorm` (`:349`) — but not this physical-field quantity, which
is gap **G1** of `COMPARISON.md` §4.

For `a ∈ 𝒳_ℝ` this is finite and equals the manuscript's `‖a‖_{Ḣ^{1/2}}`:
`research/A05/Spec.lean:268` `homogeneousLeSobolev` gives
`dotHomogeneousENorm (1/2) a ≤ sobolevENorm (1/2) a`, and the right side is
finite on `H^∞` fields (`Contracts/V1/DatumLemmas.lean:169`
`smoothJets_sobolevENorm_ne_top`).  So the hypothesis of `universal` is a genuine
smallness on the datum side, not a vacuous one. -/
def dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ

/-! ## 1. The contract -/

/-- **Proposition 4.3** (`prop:Rcritical1`, "Global regularity for small critical
data and `L¹` force"), `paper/sections/04-whole-space.tex:82-89`, in the shape
`research/section4/STATEMENTS.md:504-520` fixes and `R41` consumes.

The universal constant `c` is a **field**, hence quantified before every `ν`,
`a` and `f`, as `04-whole-space.tex:83` requires ("There is a universal `c > 0`
such that …") and as `STATEMENTS.md:536-538` and clarification 8 (`:1288-1291`)
insist for the `cν`-ball scaling of Theorem 4.1(ii) and Corollary 4.5.  The
proof's two internal constants `C₀` (`:98`) and `C₁` (`:110`) are **not**
exposed: they belong to the shrinkings `c < 1/(4C₀)` (`:104`) and `C₁y ≤ ν/4`
(`:112`), both of which are `ν`-free because `y ≤ cν`, so one `c` suffices and
the contract offers only `c`.  `C₁` is owned by `research/C01/Spec.lean:260` and
the embedding constant by `research/A05/Spec.lean:201`.

Every field is either data or a fully spelled-out manuscript statement; no field
is an abstract proposition variable, and no clause of A02/A04/A05/C01 is carried
as a field, so `universal` states exactly the manuscript's theorem with no added
rider. -/
structure RCritical1API where
  /-- `04-whole-space.tex:83`, "There is a universal `c > 0`": the smallness
  radius, in units of `ν`.  A single real, `ν`-free, shared by both conclusion
  clauses below. -/
  c : ℝ
  /-- `04-whole-space.tex:83`, "`c > 0`".  Load-bearing: without it `c ≤ 0` makes
  `ENNReal.ofReal (c * ν) = 0`, both smallness hypotheses become unsatisfiable,
  and the structure is inhabited by a statement with no content. -/
  hc : 0 < c
  /-- **The theorem** (`04-whole-space.tex:84-87`):

    `‖a‖_{Ḣ^{1/2}} + ‖f‖_{L¹(0,∞;Ḣ^{1/2})} < cν  ⟹  T^ν_{max,ℝ}(a,f) = ∞`,

  for every `ν > 0`, every `a ∈ 𝒳_ℝ` and every `f ∈ 𝓕_ℝ`.

  * `a` ranges over `initialClassR` (`Data.lean:509`), the manuscript's `𝒳_ℝ`; it
    is neither fixed nor zero (`STATEMENTS.md:441-443`, risk note `:545-547`).
  * `dotHomogeneousENorm (1/2) a` is `‖a‖_{Ḣ^{1/2}}` in the datum realization —
    **not** `Data.dotHHalfENorm`, which is a junk `0` off `L¹ ∩ L²` and would
    make this statement false; see the module docstring.
  * `forceHomogeneousENorm 1 (1/2) f` (`Data.lean:390`) is
    `‖f‖_{L¹(0,∞;Ḣ^{1/2})}`, the measurable-datum-path Bochner norm at `q = 1`
    over `forceTimeMeasure`, i.e. over `(0,∞)` as `:85` requires.
  * The sum and the threshold live in `ℝ≥0∞`; `ENNReal.ofReal (c * ν)` is
    positive and finite because `0 < c` and `0 < ν`, so a datum or force whose
    critical norm is `⊤` fails the hypothesis rather than meeting it.
  * `maximalLifespanR ν a f = ⊤` (`Data.lean:657`) is `T^ν_{max,ℝ}(a,f) = ∞`.
    `⊤` is unreachable by any finite horizon, so no implementation can satisfy
    this conclusion with a solution that breaks down.

  *The proof route, for the record, owned elsewhere* (`:90-133`).  Testing the
  projected equation against `Λu` gives eq:Rcritical1
  `½(y²)' + (ν − C₀y)z² ≤ by`, with `y = ‖u‖_{Ḣ^{1/2}}`, `z = ‖u‖_{Ḣ^{3/2}}`,
  `b = ‖f‖_{Ḣ^{1/2}}` — R43's own step, which
  `research/C01/Spec.lean` explicitly declares out of its scope.  Regularised
  division by `(y²+ζ²)^{1/2}` with `ζ↓0` and the continuity bootstrap under
  `c < 1/(4C₀)` propagate `y(t) ≤ y(0) + ∫₀ᵗ b < cν` through the lifespan.
  `research/A05/Spec.lean:366` then gives `‖u‖₃ ≤ C(1/2)·y`, which after a
  second shrinking of `c` discharges the absorption gate
  `ofReal C₁ * criticalL3 (u t) ≤ ofReal (ν/4)` of
  `research/C01/Spec.lean:532,576`; those yield `∫₀ˢ‖u‖²_{H²} < ∞` at every
  finite `S ≤ T_max`, and `research/A04/Spec.lean:657`
  `lifespanInfiniteOfLocallyFinite`, fed the maximal-solution family of
  `research/A02/Spec.lean:421`, turns that into `T_max = ⊤` ("Proposition 2.1
  excludes every finite maximal lifespan", `:132`).  None of these quantities is
  a hypothesis of this field: the manuscript's theorem carries none. -/
  universal :
    ∀ ν : ℝ, 0 < ν →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ f : SpaceTimeField, MemForceR f →
          dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
              < ENNReal.ofReal (c * ν) →
            maximalLifespanR ν a f = ⊤
  /-- **The "in particular" clause** (`04-whole-space.tex:88`, justified at
  `:132`), with `a = 0`, the **inhomogeneous** force norm, and the **same** `c`:

    `‖f‖_{L¹(0,∞;H^{1/2})} < cν  ⟹  T^ν_{max,ℝ}(0,f) = ∞`,

  for every `ν > 0` and every `f ∈ 𝓕_ℝ`.  `forceSobolevENormL1 (1/2) f`
  (`Data.lean:231`) is `‖f‖_{L¹(0,∞;H^{1/2})}`; the initial velocity is
  `fun _ => 0`, spelled as in `Data.breakdownSetRZero` (`Data.lean:686-687`) so
  that `R41` needs no conversion to reach `B^ℝ_{ν,0,T}`.

  **This is the single consequence `R41` consumes** (`STATEMENTS.md:128-135`):
  "there is a universal `c > 0` such that `{f ∈ 𝓕_ℝ : ‖f‖_{L¹_tH^{1/2}} < cν}`
  contains no element of `B^ℝ_{ν,0,T}` (because each such `f` has
  `T^ν_{max,ℝ}(0,f) = ∞ > T`)", which `RMainAPI.nonDensityZero`
  (`STATEMENTS.md:160-164`) turns into non-density in the `L¹_tH^s` metric for
  every `s ≥ 1/2` via `‖·‖_{H^{1/2}} ≤ ‖·‖_{H^s}`.  The same ball is the `q = 1`
  half of Corollary 4.5 (`:702-706`).

  Kept as its own field rather than derived, on `STATEMENTS.md:522`'s
  instruction, so that no consumer redoes the reduction — which is `a = 0`
  (`0 ∈ 𝒳_ℝ`, `‖0‖_{Ḣ^{1/2}} = 0`) together with the time-integrated
  monotonicity `‖f‖_{L¹_tḢ^{1/2}} ≤ ‖f‖_{L¹_tH^{1/2}}` of `:132`.  That
  monotonicity is gap **G2** of `COMPARISON.md` §4: A05 owns only its *spatial*
  form (`research/A05/Spec.lean:268`), and no lane yet owns the datum-path form
  that `Data.forceHomogeneousENorm`/`Data.forceSobolevENorm` need. -/
  inhomogeneousAtZero :
    ∀ ν : ℝ, 0 < ν →
      ∀ f : SpaceTimeField, MemForceR f →
        forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (c * ν) →
          maximalLifespanR ν (fun _ => 0) f = ⊤

end BlowupDensity.R43.Draft
