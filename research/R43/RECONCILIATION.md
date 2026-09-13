# R43 — reconciliation decisions (Proposition 4.3, `prop:Rcritical1`)

Plain language. What was decided, why, what a wrong implementation could get
away with, and what upstream still owes us.

Deliverable: `research/R43/Spec.lean`,
`BlowupDensity.R43.Draft.RCritical1API` — one local `def`, four fields.
Field-by-field table and the gap table: `research/R43/COMPARISON.md`.

---

## 1. The one decision that decides everything else: how big is the contract?

Draft A wrote a 13-field "proof interface": the two conclusion clauses, plus
restatements of the A02/A04/A05/C01 clauses its proof passes through, plus three
intermediate quantities of its own (`criticalNormBound`, `velocityL3Small`,
`h2SquaredIntegralFinite`). Draft B wrote the manuscript's theorem and nothing
else. **Draft B's shape is adopted.** Three reasons, in order of weight.

**(a) The restatements are now known to be wrong.** Draft A was written without
sight of the A04 and C01 specs and honestly said so — its clauses were "the first
written shape of what those specs must export". Those specs now exist, and seven
of A's eleven restated clauses are not the sibling's actual type
(`COMPARISON.md` §3). Two of the mismatches are not cosmetic:

* A's `continuation` demands a classical solution *at* horizon `S`. At a
  hypothetical finite maximal lifespan `T_max` no such solution exists at
  `S = T_max`, so A's field can only ever be applied at `S < T_max`, where its
  conclusion `ofReal S < T_max` is already known. **A's field set does not derive
  `T_max = ⊤`.** A04 saw this independently (its `REVIEW.md` finding 1, quoted at
  `research/A04/Spec.lean:628-641`) and ships `lifespanInfiniteOfLocallyFinite`
  (`:657`), which is literally R43's closing line.
* A's `h2SquaredIntegralFinite` is gated by R43's critical smallness. C01
  deliberately gates its clause by `‖u‖₃` instead
  (`research/C01/Spec.lean:253-265`), so that one clause serves both R43 and R44.
  A's shape would have pushed R43's constant threading into C01.

Carrying a second, divergent copy of a sibling statement inside R43's contract is
exactly the drift `CLAUDE.md` §"合同 import 规则" forbids: the binding layer would
have nothing to bridge it to.

**(b) No consumer wants them.** Checked against the DAG and the ledger
(`COMPARISON.md` §2): R43's only outgoing edge is `R43 → R41`, and R41 consumes
exactly one consequence — the `a = 0` inhomogeneous ball, at `q = 1`
(`STATEMENTS.md:128-135`). R44 shares R43's three children and goes to them
directly; R45 reaches R43 only through R41; R46 must not depend on R43 at all
(`STATEMENTS.md:1348`). The task's own rule — expose an intermediate only if some
consumer needs it — therefore drops all of them.

**(c) A statement contract should not fix a proof strategy.** `criticalNormBound`
and `velocityL3Small` are steps, not claims of the manuscript. If the Lean proof
later routes the absorption differently (say, straight from `y ≤ cν` to C01's
gate without naming `‖u‖₃`), a contract that named them would have to be
re-versioned for a reason with no mathematical content.

*What is not a reason:* Draft B's own argument that "adding the consumed clauses
as hypotheses would make `universal` weaker" is inaccurate as written — they were
separate fields of A's structure, not hypotheses of A's `universal`, and extra
fields make a structure harder to inhabit, not weaker. The correct objections are
(a), (b), (c).

Two things from Draft A are kept. The structure keeps A's **general-`s`** local
`def dotHomogeneousENorm`, with A05's name and arity, so that when A05 registers
the local copy is deleted and the two call sites do not change spelling (B's
`dotHalfSpatialENorm` would have had to be renamed). And A's §2 analysis of the
`Ḣ^{1/2}` norm is the sharper of the two write-ups and is folded into the module
docstring.

---

## 2. The `Ḣ^{1/2}` norm: both drafts were right to refuse `Data.dotHHalfENorm`

Verified rather than taken on trust.

`Data.dotHHalfENorm` (`Contracts/V1/Data.lean:427-430`) is an abbreviation for
`homogeneousFourierENorm (1/2)` (`:410-414`), which is

    (∑ᵢ ∫⁻ ξ, ENNReal.ofReal (‖ξ‖^(2s) * ‖angularFourier (zᵢ) ξ‖²)) ^ (1/2)

and `angularFourier g ξ = frequencyUnit^(-3/2) • 𝓕 g (frequencyUnit⁻¹ • ξ)`
(`formalization/NSFormalization/Source/FourierConvention.lean:23`, with
`angularFourier_eq_integral` at `:27` proving it is the displayed
`∫ exp(-i⟨x,ξ⟩) g(x) dx`). That is a **pointwise Bochner integral**, and Mathlib
returns `0` from a Bochner integral of a non-integrable function. So for a field
that is not `L¹`, `angularFourier` is identically `0`, the whole expression is
`0`, and `Data.lean:404-409` says so itself: "`angularFourier` is a pointwise
Bochner transform, so this quantity is faithful on the `L¹ ∩ L²` fields it is
applied to … and must not be used on a general `H^∞` slice."

`𝒳_ℝ = H^∞ ∩ L²_σ` (`Data.lean:509`) contains fields that are not `L¹` — smooth
solenoidal fields with `|x|^{-2}` decay, say. With `dotHHalfENorm`, such a field
would read `‖a‖_{Ḣ^{1/2}} = 0 < cν` however large it is, the smallness hypothesis
would be satisfied vacuously, and `universal` would assert global regularity for
arbitrarily large critical data. **The statement would be false**, not merely
loose. Both drafts caught this independently; that agreement is the strongest
signal in the pair.

The replacement is the datum infimum. It is total (the empty infimum in `ℝ≥0∞` is
`⊤`), so the failure direction is `⊤` — hypothesis fails — never a junk `0`. On
`𝒳_ℝ` it is the manuscript's number and is finite, by A05's
`homogeneousLeSobolev` (`research/A05/Spec.lean:268`) together with
`DatumLemmas.lean:169` `smoothJets_sobolevENorm_ne_top`.

---

## 3. Smaller decisions

| decision | taken | reason |
|---|---|---|
| structure name `RCritical1API` | B | `STATEMENTS.md:505` is the naming authority. |
| `c` as a structure field, not `∃ c` inside each clause | both | Binds `c` before `ν, a, f`; keeps the two clauses on the *same* `c`, which clarification 8 (`STATEMENTS.md:1288-1291`) requires because that same number is the radius of Theorem 4.1(ii)'s and Corollary 4.5's `q=1` non-density ball. |
| `C₀`, `C₁`, `C_emb` **not** exposed | B | `C₀` is internal to R43's own ODE step; `C₁` belongs to `research/C01/Spec.lean:266` and `C (1/2)` to `research/A05/Spec.lean:201`. A's `Cemb : ℝ` was also the wrong type for A05, which exposes `C : ℝ → ℝ`. |
| `inhomogeneousAtZero` kept as its own field | both | `STATEMENTS.md:522`: it is what `RMainAPI.nonDensityZero` consumes at `q = 1`. Derivable from `universal`, but only modulo gap **G2**, and a consumer should not carry that. |
| zero field spelled `fun _ => 0` | B | Matches `Data.breakdownSetRZero` (`Data.lean:686-687`), which is how R41 reaches this clause. A's `fun _ : Space => (0 : Space)` is defeq but needs a conversion. |
| everything in `ℝ≥0∞`, no `.toReal` | both | A missing datum fails safe to `⊤`. |
| strict `<`, threshold `ENNReal.ofReal (c * ν)` | both | The paper's `< cν`. Positive and finite because `0 < c`, `0 < ν`. |
| `a` quantified over `initialClassR`, not fixed, not zero | both | `:83`; `STATEMENTS.md:545-547` insists the contract carry the general statement even though R41 uses only `a = 0`. |

---

## 4. "Could a wrong implementation satisfy this?" — per field

| field | can it be satisfied by something that is not Prop 4.3? |
|---|---|
| `c : ℝ` | Data, nothing to satisfy. |
| `hc : 0 < c` | No. It is what stops `c ≤ 0` from making `ENNReal.ofReal (c*ν) = 0` and both clauses unsatisfiable-hence-vacuous. |
| `universal` | **Conclusion side: no.** `maximalLifespanR ν a f = ⊤` is the top of `ℝ≥0∞`; no finite horizon reaches it, and `maximalLifespanR` is `Data.lean:657`'s supremum over horizons that actually carry a `ClassicalSolutionR`, so it cannot be inflated by a field that is not a solution. **Hypothesis side: two ways, both closed or flagged.** (i) A junk-`0` critical norm would make the hypothesis vacuously true for large data and the field *false* — closed by using the datum infimum instead of `Data.dotHHalfENorm` (§2). (ii) If the order-`1/2` datum paths do not exist for `f ∈ 𝓕_ℝ`, `forceHomogeneousENorm 1 (1/2) f = ⊤`, the hypothesis is unsatisfiable, and the field is **vacuously true** — this is gap **G3**, the one remaining way a wrong implementation satisfies this contract. It is a non-vacuity obligation on D01, not a defect of the statement. |
| `inhomogeneousAtZero` | Same as `universal`. Additionally: `fun _ => 0` is a *specific* field, not a variable, so the clause cannot be dodged by choosing a convenient datum; and `forceSobolevENormL1 (1/2)` is `Data.lean`'s honest measurable-path infimum (`Data.lean:225-231`), not a lower integral that could under-report (the `REVIEW_B` issue 3 that `Data.lean` already decided). Gap **G3** applies here too. |
| the local `def dotHomogeneousENorm` | It is a definition, so the question is faithfulness, not satisfiability. It is A05's, verbatim; if A05's is wrong, R43 is wrong in the same way, which is the intended coupling. The one thing it could do silently is be `⊤` everywhere — it is not, by `homogeneousLeSobolev` (`research/A05/Spec.lean:268`). |

The honest summary: after §2's fix, the only remaining route by which this
contract could be satisfied by something that is not Proposition 4.3 is
**vacuity** — both hypotheses being unsatisfiable because the order-`1/2` datum
paths are missing. That is gap **G3**, and it is new in this reconciliation;
neither draft recorded it.

---

## 5. What upstream must add, ranked

Full shapes in `COMPARISON.md` §4. Ranked by what they block.

**Blocks stating Prop 4.3 faithfully — must land before registration**

1. **G1 — D01 or A05: the datum-form spatial `Ḣ^s` norm.** Promote
   `research/A05/Spec.lean:131` `dotHomogeneousENorm` into a registered contract
   and mark `Data.dotHHalfENorm` / `dotHThreeHalvesENorm` as quantity forms for
   `L¹ ∩ L²` slices only. Until this lands, `Spec.lean` carries a local copy and
   R43 cannot bind. Found by both drafts.

**Blocks the statement having content (non-vacuity) — should land before registration**

2. **G3 — D01 (`DatumLemmas`): order-`1/2` force datum paths exist.**
   `∀ f, MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤` and the homogeneous
   twin. `MemForceR` gives paths at integer orders only;
   `DatumLemmas.lean:160` gives slicewise data at every real order but not the
   measurable path. Without this both fields are vacuously true. **New here.**

**Blocks R43's proof**

3. **G2 — A05 (or D01): the time-integrated `‖f‖_{L¹_tḢ^{1/2}} ≤ ‖f‖_{L¹_tH^{1/2}}`.**
   `04-whole-space.tex:132`. A05 owns only the spatial slice form
   (`research/A05/Spec.lean:268`); the force norms are infima over datum
   *paths*, so the path-level bridge is missing. This is the whole content of
   deriving `inhomogeneousAtZero` from `universal`. **New here as a distinct
   item**; both drafts assumed it under the name of the spatial lemma.
4. **G7 — R43's own lane: eq:Rcritical1 and a differentiable critical path.**
   The `Λu` test and differentiability of `y²`. No sibling owns it — C01 says so
   explicitly. Needs a `HasSmoothCriticalPath` analogue of A04's
   `HasSmoothSobolevPath` (`research/A04/Spec.lean:247`). This is the substance
   R43 owes itself, and it is the largest single unit of the eventual proof lane.
   Found by B (GAP-3).
5. **G4 — C01: slicewise `Ḣ^{1/2}` force integrability.** `b(t) = ‖f(t)‖_{Ḣ^{1/2}}`
   as an interval-integrable real function with `∫₀ᵗ b = ‖f‖_{L¹(0,t;Ḣ^{1/2})}`.
   C01's `forceTimeRegularity` (`:326`) does the `L²` slice only. Found by B
   (GAP-2).
6. **G5 — C01 endpoint, or R43 gluing.** C01's `h2TimeIntegral` is stated on a
   fixed-horizon `ClassicalSolutionR` with `S ≤ T`; A04's closing clause needs
   `S = T_max`, where no such solution exists. R43 can glue by monotone
   convergence (C01's right-hand side is monotone in `S` and finite at `T_max`
   because `f ∈ 𝓕_ℝ`), so this is friction, not a blocker; a C01 endpoint
   corollary would remove it. Found by A (§4 items 2-3) and B (GAP-4).
7. **G6 — pin one power spelling.** `research/A04/Spec.lean:202` uses `^ (2:ℕ)`,
   `research/C01/Spec.lean:576,599` use `^ (2:ℝ)`. One `ℝ≥0∞` identity bridges
   them; pin A04's, since A04 exports the `def`. Found by B (GAP-5).

**Nothing owed**

8. **G8 — constant threading A05 ↔ C01.** Draft A asked that C01's gate be in the
   `‖u‖₃` shape R43 supplies; C01 already does exactly that
   (`research/C01/Spec.lean:532,576`), and both `C₁` and `C (1/2)` are exposed and
   `ν`-free. Checked and satisfied.

---

## 6. Commands run

    cd <WT> && bash scripts/lean-install.sh            # exit 0
    . scripts/lean-env.sh; export LEAN_NUM_THREADS=6
    cd verification && lake env lean ../research/R43/DraftA.lean   # exit 0
    cd verification && lake env lean ../research/R43/DraftB.lean   # exit 0
    cd verification && lake env lean ../research/R43/Spec.lean     # exit 0

No `sorry`, `admit`, `axiom`, `native_decide`, or placeholder `Prop` field in
`Spec.lean`; no warnings. `DraftA.lean` and `DraftB.lean` are unmodified and
still typecheck against the current tree.
