# R43 — Proposition 4.3 (`prop:Rcritical1`) — reconciled comparison

Statement `paper/sections/04-whole-space.tex:82-89`; proof `:90-133`.
Ledger `research/section4/STATEMENTS.md` §3 (`:428-563`); R41's consumption `:128-135`.

Inputs compared: `DraftA.lean` (`CriticalRegularityL1API`, 3 local `def`s + 13
fields, written **without** sight of the A04/C01 specs) and `DraftB.lean`
(`RCritical1API`, 1 local `def` + 4 fields, written **with** them), against the
paper and against the sibling specs as they actually stand on `erenup/integration`.

Output: `Spec.lean`, `BlowupDensity.R43.Draft.RCritical1API` — 1 local `def` +
4 fields.

---

## 1. Field-by-field decisions

Legend for "which is the paper's statement": ✅ = adopted verbatim, ≈ = adopted
after a spelling change, ✗ = dropped.

| # | field / object | paper line | Draft A | Draft B | decision | why |
|---|---|---|---|---|---|---|
| 1 | structure name | — | `CriticalRegularityL1API` | `RCritical1API` | **B** ✅ | `STATEMENTS.md:505` names the contract `RCritical1API`; the ledger is the naming authority for Section 4 contracts. |
| 2 | `c : ℝ` | `:83` "There is a universal `c>0`" | field of the structure | field of the structure | **both agree** ✅ | A field binds `c` outside every `∀ ν, a, f`, which is the paper's quantifier order and what clarification 8 (`STATEMENTS.md:1288-1291`) requires for the `cν`-ball scaling in Thm 4.1(ii) / Cor 4.5. |
| 3 | `hc : 0 < c` | `:83` | present | present | **both agree** ✅ | Without it `ENNReal.ofReal (c*ν) = 0` and both clauses are vacuous. |
| 4 | `Cemb : ℝ`, `hCemb` | `appendix-b-embeddings.tex:14-15` | present | absent | **B** ✗ | It is A05's constant, and A05's actual shape is `C : ℝ → ℝ` with `C_pos : ∀ a, 0 < C a` (`research/A05/Spec.lean:201,203`), used as `ENNReal.ofReal (C (1/2))` in `velocityCriticalL3` (`:366`). A's scalar `Cemb` is a *different type* from the sibling it claims to restate. R43 owns no embedding constant. |
| 5 | `universal` — quantifier order | `:83-87` | `∃c>0 ∀ν>0 ∀a∈𝒳_ℝ ∀f∈𝓕_ℝ` | same | **both agree** ✅ | Matches `STATEMENTS.md:441`. `a` is quantified, not fixed and not zero. |
| 6 | `universal` — datum norm `‖a‖_{Ḣ^{1/2}}` | `:85` | `dotHomogeneousENorm (1/2) a`, local copy of A05:131 with general `s` | `dotHalfSpatialENorm a`, local copy of A05 specialized to `s = 1/2` | **A's form, B's reasoning** ≈ | Both correctly reject `Data.dotHHalfENorm` (§4, G1). A's general-`s` copy keeps A05's *name and arity*, so when A05 registers the local `def` is deleted and the call sites are unchanged; B's specialized name would have to be renamed. |
| 7 | `universal` — force norm `‖f‖_{L¹_tḢ^{1/2}}` | `:85` | `forceHomogeneousENorm 1 (1/2) f` | same | **both agree** ✅ | `Data.lean:390`, the measurable-datum-path Bochner norm at `q=1` over `forceTimeMeasure = (0,∞)`, `⊤` when no path exists. |
| 8 | `universal` — threshold | `:85` | `< ENNReal.ofReal (c*ν)` in `ℝ≥0∞` | same | **both agree** ✅ | Strict, as the paper. `ℝ≥0∞` with no `.toReal`: an infinite norm fails the hypothesis instead of meeting it. |
| 9 | `universal` — conclusion | `:86` | `maximalLifespanR ν a f = ⊤` | same | **both agree** ✅ | `Data.lean:657`. `⊤` is unreachable by a finite horizon. |
| 10 | `inhomogeneousAtZero` — kept as its own field? | `:88` | yes, same `c` | yes, same `c` | **both agree** ✅ | `STATEMENTS.md:522` — it is the field `RMainAPI.nonDensityZero` consumes at `q=1`; a consumer should not redo the reduction. |
| 11 | `inhomogeneousAtZero` — force norm | `:88` | `forceSobolevENormL1 (1/2) f` | same | **both agree** ✅ | `Data.lean:231`, the **inhomogeneous** `H^{1/2}` norm. |
| 12 | `inhomogeneousAtZero` — the zero field | `:88` | `(fun _ : Space => (0 : Space))` | `(fun _ => 0)` | **B** ≈ | `Data.breakdownSetRZero` (`Data.lean:686-687`) is `breakdownSetR ν (fun _ => 0) T`; R41 reaches this field through that set, so the spelling must be Data.lean's. Defeq either way, but syntactic identity saves a conversion. |
| 13 | `existsMaximal` | `02-preliminaries.tex:105` | restated ⟪A02:exists_maximal⟫ | absent | **B** ✗ | A's restatement *does* match `research/A02/Spec.lean:421` (§3 row 1). It is nonetheless dropped: no consumer of R43 needs it (§2), and a second copy of a sibling statement inside R43's contract is exactly the drift `CLAUDE.md` §"合同 import 规则" forbids. |
| 14 | `lifespanLeIffNoExtension` | `02-preliminaries.tex:32,105` | restated ⟪A02:…⟫ | absent | **B** ✗ | Matches `research/A02/Spec.lean:451` exactly (§3 row 2), and is still dropped for the same reason. It is also not on R43's actual proof route any more: A04's `lifespanInfiniteOfLocallyFinite` supersedes it. |
| 15 | `continuation` | `02-preliminaries.tex:105-110` | restated ⟪A04:continuation⟫ | absent | **B** ✗ | A's shape does **not** match A04 (§3 rows 3-4) and, worse, could not close R43's proof: it demands a `ClassicalSolutionR ν a f S` at the endpoint `S`, which does not exist at `S = T_max`. A04 ships two better fields, `extendsBeyond` (`:613`) on `SolvesBelow`, and `lifespanInfiniteOfLocallyFinite` (`:657`) which is literally R43's closing step. |
| 16 | `velocityCriticalL3` | `appendix-b-embeddings.tex:29`, `04:93` | restated ⟪A05:velocityCriticalL3⟫ with `Cemb` | absent | **B** ✗ | A's right-hand constant is `ENNReal.ofReal Cemb`; A05's is `ENNReal.ofReal (C (1/2))` (`research/A05/Spec.lean:366`). Not identical, and unneeded by any consumer. |
| 17 | `criticalNormBound` (`y ≤ cν` on the lifespan) | `:97-104`, eq:Rcritical1 | present | absent | **B** ✗ | R43-owned proof intermediate. No consumer (§2). Exposing it also fixes a proof strategy in a *statement* contract, and it is stated on `IsMaximalSolution`/`presingularTimes`, whereas C01's absorption gate wants `∀ t ∈ Ico 0 S` on a `ClassicalSolutionR` slice — so as a field it would not even plug into C01 without a bridge. |
| 18 | `velocityL3Small` (`‖u‖₃ ≤ Cemb·cν`) | `:93,97-104` | present | absent | **B** ✗ | Same: derived intermediate, no consumer, and its constant is A's non-existent `Cemb`. |
| 19 | `h2SquaredIntegralFinite` (`∫₀ˢ‖u‖²_{H²} < ∞`) | `:118-131` | restated ⟪C01:h2TimeIntegral⟫ | absent | **B** ✗ | A's shape does **not** match C01's (§3 rows 5-7): different hypothesis (R43's critical smallness vs C01's `‖u‖₃` absorption gate), different solution object (maximal solution vs fixed-horizon `ClassicalSolutionR`), different power spelling. |
| 20 | local `def IsMaximalSolution`, `presingularTimes` | `02-preliminaries.tex:32,105` | both, verbatim A02:210,168 | neither | **B** ✗ | Verbatim-correct copies (§3 rows 8-9), but only needed by the dropped fields 17-19. |
| 21 | local `def dotHomogeneousENorm` | `appendix-b-embeddings.tex:26-27` | present (general `s`) | present (`s=1/2`) | **A** ✅ | Kept — it is the one object `Data.lean` lacks, and both drafts need it. See G1. |

**Net**: the reconciled contract is Draft B's four fields, with Draft A's
general-`s` local `def`, under the ledger's name.

---

## 2. Is any intermediate field wanted by a consumer? — No

Checked in `formalization/blueprint/DEPENDENCY_GRAPH.md:62-69` and
`research/section4/STATEMENTS.md`:

* `R43 → R41` is the only outgoing edge. `R41` consumes **exactly one**
  consequence (`STATEMENTS.md:128-135`): the `a=0` inhomogeneous ball, fed to
  `RMainAPI.nonDensityZero` at `q = 1` (`:160-164`).
* `R44` is *not* a consumer. It shares R43's three children (`A04, A05, C01`,
  `STATEMENTS.md:598`) and reaches the "closing calculation of Prop. 4.3"
  (`:581`) through those children directly, not through R43.
* `R45` (Cor. 4.5) reaches R43 only through R41 (`STATEMENTS.md:702-706`): the
  critical ball intersected with `F_c`/`F_rd`, still only the `a=0` clause.
* `R46` (Prop. 4.6) does not depend on R43; `STATEMENTS.md:1348` explicitly
  warns against "dragging R43/R44 into R46's closure".

So no field beyond `c`, `hc`, `universal`, `inhomogeneousAtZero` has a consumer.
`universal` itself has no consumer either, but it is the manuscript's theorem and
`STATEMENTS.md:545-547` requires the contract to carry it ("Theorem 4.1 only
uses `a = 0`, but the general statement is what the contract must carry").

---

## 3. Draft A's ⟪A04⟫/⟪C01⟫/⟪A02⟫/⟪A05⟫ restatements vs the real specs

Draft A was written blind to A04 and C01 and wrote what it *expected* them to
export. Every mismatch:

| # | A's field | the real sibling clause | verdict |
|---|---|---|---|
| 1 | `existsMaximal` | `research/A02/Spec.lean:421` `exists_maximal` | **match** (binders interleaved differently, same proposition) |
| 2 | `lifespanLeIffNoExtension` | `research/A02/Spec.lean:451` `lifespan_le_iff_no_extension` | **match**, verbatim |
| 3 | `continuation` hypothesis object | A04 `extendsBeyond` (`:613`) takes `SolvesBelow ν a f S u p` (a solution on **every** horizon strictly below `S`, plus a pressure); A takes one `w : ClassicalSolutionR ν a f S` | **mismatch.** A's is the stronger hypothesis (a solution *at* horizon `S`), hence the weaker clause. A04's is the shape R43 can actually supply from A02's maximal-solution family. |
| 4 | `continuation` extra hypothesis | A04 also requires `MemL1Hm f` (`research/A04/Spec.lean:268`); A omits it | **mismatch** (harmless — `MemL1Hm` is free from `MemForceR`, A04's unit F1 — but the types differ) |
| 5 | `continuation` closes nothing at the endpoint | A04 ships `lifespanInfiniteOfLocallyFinite` (`:657`), which A never asked for | **gap in A's design.** A's `continuation` yields `ofReal S < maximalLifespanR` from a solution at horizon `S`, which at a hypothetical finite `T_max` is only ever instantiable at `S < T_max` and is then trivially true. A's field set (`continuation` + `existsMaximal` + `lifespanLeIffNoExtension` + `h2SquaredIntegralFinite`) therefore does **not** derive `T_max = ⊤`. A04's REVIEW finding 1, quoted at `research/A04/Spec.lean:631-641`, is exactly this point. |
| 6 | `h2SquaredIntegralFinite` hypothesis | C01 `h2TimeIntegral` (`:576`) is gated by `∀ t ∈ Ico 0 S, ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤ ENNReal.ofReal (ν/4)`; A gates it by R43's own critical smallness `‖a‖_{Ḣ^{1/2}} + ‖f‖_{L¹_tḢ^{1/2}} < cν` | **mismatch.** C01 deliberately takes the `‖u‖₃` form so that one clause serves R43 and R44 (`research/C01/Spec.lean:253-265`). A's restatement pushes the whole constant-threading into C01. |
| 7 | `h2SquaredIntegralFinite` solution object and range | C01 quantifies over `w : ClassicalSolutionR ν a f T` with `0 < S ≤ T`; A quantifies over `IsMaximalSolution ν a f u p` with `ofReal S ≤ maximalLifespanR ν a f` | **mismatch**, and this is the substance of gap **G5**: no `ClassicalSolutionR` has horizon `T ≥ T_max`, so C01's clause is never instantiable at `S = T_max`, which is precisely the `S` A04's closing clause needs. |
| 8 | `h2SquaredIntegralFinite` power spelling | C01 writes `sobolevENorm 2 _ ^ (2 : ℝ)` (rpow); A (and A04's `squaredHTwoIntegral`, `research/A04/Spec.lean:202`) writes `^ 2` (npow) | **mismatch** = gap **G6** |
| 9 | `h2SquaredIntegralFinite` conclusion | C01 gives an explicit bound `≤ ENNReal.ofReal (Cassembly*S*K(S)² + …)`; A gives bare `< ⊤` | **weaker, compatible** — A04's hypothesis is `≠ ⊤`, so only finiteness is consumed |
| 10 | `velocityCriticalL3` constant | A05 `:366` uses `ENNReal.ofReal (C (1/2))` with `C : ℝ → ℝ`; A uses a scalar `Cemb` | **mismatch** (row 4 of §1) |
| 11 | local `IsMaximalSolution`, `presingularTimes` | `research/A02/Spec.lean:210,168` | **match**, verbatim |

Seven of eleven restatements diverge from the real sibling. Draft A's honest
"first written shape of what those specs must export" was a reasonable blind
guess, but the guesses are now superseded — and two of them (rows 5 and 7) would
have left R43's proof unclosable.

---

## 4. What upstream must add — one consolidated table

Merging Draft A's four A04/C01 asks (`COMPARISON_A.md` §4) and Draft B's
GAP-1…GAP-5. "Blocks" = whether the item blocks *stating* Prop 4.3, or only
*proving* it.

| id | owner | exact Lean shape needed | blocks | found by |
|---|---|---|---|---|
| **G1** | **D01** (`Data.lean`) or **A05** | the datum-form spatial homogeneous norm on a physical field: `def dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ := ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ`, promoted out of `research/A05/Spec.lean:131` into a registered contract. `Data.dotHHalfENorm` (`Data.lean:427`) cannot serve: it is `homogeneousFourierENorm (1/2)` (`:410`), a pointwise Bochner Fourier integral (`angularFourier`, `Source/FourierConvention.lean:23`) that Mathlib totalizes to a junk `0` on a non-`L¹` field — its own docstring (`Data.lean:404-409`) forbids the general `H^∞` use. Recommend also annotating `dotHHalfENorm` / `dotHThreeHalvesENorm` as "quantity forms, `L¹∩L²` slices only". | **the statement** | A ( §2) and B (GAP-1) independently |
| **G2** | **A05** (it already owns the spatial form) or **D01** | the **time-integrated** monotonicity `∀ f, MemForceR f → forceHomogeneousENorm 1 (1/2) f ≤ forceSobolevENormL1 (1/2) f` — `04-whole-space.tex:132`'s "Finally `‖f‖_{Ḣ^{1/2}} ≤ ‖f‖_{H^{1/2}}` proves the stated inhomogeneous consequence". A05's `homogeneousLeSobolev` (`research/A05/Spec.lean:268`) is the **spatial** slice form only; both `Data` force norms are infima over *datum paths*, so the bridge must carry an `IsSobolevPath (1/2) f G` to an `IsHomogeneousPath (1/2) f G'` with `‖G' t‖ ≤ ‖G t‖` and `AEStronglyMeasurable G'`. Also needed: `dotHomogeneousENorm (1/2) (fun _ => 0) = 0` and `(fun _ => 0) ∈ initialClassR`. | deriving `inhomogeneousAtZero` from `universal` | **neither draft, as a distinct item** (A's unit U1 and B's unit U8 both assume it; both call it "D01 `H^s` monotonicity", which is the spatial lemma that does not suffice) |
| **G3** | **D01** (`DatumLemmas`) | **non-vacuity of both hypotheses**: `∀ f, MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤` and `forceHomogeneousENorm 1 (1/2) f ≠ ⊤`. `MemForceR` (`Data.lean:544`) supplies datum paths only at *integer* orders; both force norms are infima over paths at order `1/2`, so on the current definitions they may both be `⊤` for a genuine `f ∈ 𝓕_ℝ`, making both conclusion fields **vacuously true** — the one way a wrong implementation satisfies this contract. `DatumLemmas.lean:160` `smoothJets_exists_datum` gives the slicewise half at every real order; the missing half is the measurable *path* at order `1/2`, and its homogeneous counterpart (`DatumLemmas.lean:483` `compact_exists_homogeneousPath` covers only compactly supported `f`). | **the statement's content** (not its well-formedness) | **neither draft** |
| **G4** | **C01**, or a new bridge | slicewise homogeneous force integrability: `b(t) = ‖f(t)‖_{Ḣ^{1/2}}` as a real function, interval-integrable on `[0,t]`, with `∫₀ᵗ b = ‖f‖_{L¹(0,t;Ḣ^{1/2})}` — the right-hand side of `04-whole-space.tex:102`. C01's `forceTimeRegularity` (`research/C01/Spec.lean:326`) supplies this only for the **`L²`** slice norm. Natural home: C01, mirroring `forceTimeRegularity` at the homogeneous critical order. | the proof (units U2/U3) | B (GAP-2) |
| **G5** | **C01** endpoint corollary (optional), else R43-owned gluing | A04's `lifespanInfiniteOfLocallyFinite` (`research/A04/Spec.lean:657`) instantiates its hypothesis at `S = T_max`; C01's `h2TimeIntegral` (`research/C01/Spec.lean:576`) is stated per `w : ClassicalSolutionR ν a f T` with `0 < S ≤ T`, and no solution has horizon `T ≥ T_max`. Either C01 adds `∀ S, 0 < S → ofReal S ≤ maximalLifespanR ν a f → (family) → ∫⁻ … ≤ …` (taking the sup), or R43 glues the interior bounds by monotone convergence, using that C01's RHS is monotone in `S` and finite at `S = T_max` because `f ∈ 𝓕_ℝ` (`04-whole-space.tex:121,171`). Doable in R43; a C01 corollary would remove the friction. | the proof (unit U6) | A (§4 items 2-3) and B (GAP-4) independently |
| **G6** | **A04 ↔ C01** spelling pin | `research/A04/Spec.lean:202` `squaredHTwoIntegral` uses `sobolevENorm 2 _ ^ 2` (`ℕ` pow); `research/C01/Spec.lean:576,599` bound `sobolevENorm 2 _ ^ (2 : ℝ)` (rpow). One `ℝ≥0∞` identity `x ^ (2:ℕ) = x ^ (2:ℝ)` bridges them. Pin **one** spelling at registration; A04's npow is the one A04's own `def` exports, so C01 should move. | the proof (one line) | B (GAP-5) |
| **G7** | **R43's own lane** (no sibling) | eq:Rcritical1 (`04-whole-space.tex:97-99`) — the critical `Ḣ^{1/2}` energy inequality from testing the projected equation against `Λu` — together with differentiability of `s ↦ y(s)²`. C01's docstring declares eq:Rcritical1 out of its scope. Needs a `HasSmoothCriticalPath`-style input, the critical analogue of A04's `HasSmoothSobolevPath` (`research/A04/Spec.lean:247`), which gives smooth *Sobolev* datum paths only; no lane exports a differentiable `Ḣ^{1/2}`/`Ḣ^{3/2}` path. | the proof (units U2-U4) — this is the substance R43 owns | B (GAP-3) |
| **G8** | **A05 / C01** constant threading (no new clause) | R43 must shrink `c` twice: `c < 1/(4C₀)` (`:104`, `C₀` is R43's own) and `C₁·C(1/2)·c·ν ≤ ν/4` (`:112`), the latter discharging C01's gate `ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤ ENNReal.ofReal (ν/4)` through A05's `‖u‖₃ ≤ C(1/2)·‖u‖_{Ḣ^{1/2}}`. Both `C₁` (`research/C01/Spec.lean:260`) and `C (1/2)` (`research/A05/Spec.lean:201`) are already exposed and `ν`-free, so **nothing is missing**; recorded so the reconciliation shows it was checked. | nothing | A (§4 item 4), confirmed satisfied |

Draft A's four asks resolve as: item 1 → **satisfied and improved** (A04 ships a
better shape, G5 notwithstanding); item 2 → **partly satisfied**, becomes G5;
item 3 → **not satisfied**, becomes G5; item 4 → **satisfied**, becomes G8.
Draft B's GAP-1…GAP-5 map to G1, G4, G7, G5, G6. G2 and G3 are new here.
