# R44 — Proposition 4.4 (`prop:Rcritical2`) — reconciled comparison

**Regularity on a prescribed finite interval.**
Statement `paper/sections/04-whole-space.tex:136-144`; proof `:145-174`
(`:171` "`f ∈ 𝓕_ℝ` … not required to be small"; `:173` "the inhomogeneous norm is
essential"); use in Theorem 4.1 at `S = T`, `:179`.
Ledger `research/section4/STATEMENTS.md` §4 (`:556-651`), skeleton `:611-624`;
R41's consumption `:133-136`.

Inputs: `DraftA.lean` + `COMPARISON_A.md` (9 fields, `radius` named and pinned),
`DraftB.lean` + `COMPARISON_B.md` (4 fields, radius inlined).
Output: `Spec.lean`, `BlowupDensity.R44.Draft.RCritical2API` — **9 fields, no
local `def`**. Decisions and reasons: `RECONCILIATION.md`.

The two drafts agree on every mathematical choice. They differ on packaging
(§1), on two Lean spellings (§2), and — the only substantive divergence — on
**what the siblings already provide** (§4): draft B reported two gaps at A04 and
C01 that do not exist, draft A reported as open a D01 finiteness that lane 042
has already proved.

---

## Current implementation update — lane 227 (2026-09-16)

`Section4/R44/Endpoint.lean` now assembles S2–S6 conditional **only** on
`RCritical2Differential`: the exact S1 inequality with one derivative locally
interval integrable on every closed presingular window. The fixed constants
are `C₂ = 2`, `C₃ = 4`,
`theta = min R43.criticalConst (1/(100*(A05.criticalL3Const+1)^3))`,
`c = theta/20`, and `C = 3`. The radius is exactly
`c * ν^(3/2 : ℝ) * exp (-(C*ν*S))`, and the conclusion is the strict finite
lifespan inequality, with zero datum and the original inhomogeneous norm.

G3's continuity, exact path-infimum norm identification, and squared prefix
bound are proved in the new module. G4's maximal endpoint gluing and G5's
power pin are reused from R43; A05 V2, C01 V4, A02 unconditional maximal
existence, and A04 unconditional fixed-force continuation are present and
consumed without additional named assumptions. The Data-vocabulary main and
non-density conformance theorems are in `axioms_endpoint.lean`, together with
zero-force and zero-solution non-vacuity checks. Every authored declaration
reports precisely the standard three logical axioms.

Only S1c/S1d and its derivative-integrability provider remain for the
unconditional theorem. `rcritical2_endpoint` explicitly retains that provider;
there is no fabricated unconditional theorem or complete API instance.
The tables below preserve the original statement-comparison audit; their
claims that sibling implementations are absent describe that older baseline.
Current statuses supersede them in `R44_SPLIT.md` rows S2–S6 and its gap table.

## 1. Field-by-field

`✓` = adopted as written; `→` = adopted with the change shown.

| # | field (reconciled) | A | B | decision |
|---|---|---|---|---|
| 1 | `c : ℝ` | ✓ | ✓ | both; `04-whole-space.tex:143`, bound before `ν,S,f` |
| 2 | `C : ℝ` | ✓ | ✓ | both; kept **exposed**, not existentially hidden (§3) |
| 3 | `hc : 0 < c` | ✓ | ✓ | both; the anti-vacuity guard |
| 4 | `hC : 0 < C` | ✓ | ✓ | both; faithfulness marker, not a guard (§3) |
| 5 | `radius : ℝ → ℝ → ℝ` | ✓ | absent | **A**, = ledger skeleton `:611-624` |
| 6 | `radiusFormula : ∀ ν S, radius ν S = c * ν ^ (3 / 2 : ℝ) * Real.exp (-(C * ν * S))` | → | (inlined) | **A**, exponent spelled `(3 / 2 : ℝ)` per ledger `:617` (A wrote `((3:ℝ)/2)`; `rfl`-equal, checked) |
| 7 | `radiusPos : ∀ ν S, 0 < ν → 0 < S → 0 < radius ν S` | ✓ | absent | **A** = ledger `:618`; derivable, kept so `R41` performs no reduction |
| 8 | `main` | → | → | both, with A's threshold `ENNReal.ofReal (radius ν S)` and the `-1 / 2` order spelling (§2) |
| 9 | `nonDensityBallZero` | → (`nonDensityBallZero`) | → (`nonDensityAtHorizon`) | both; **A's name**, B's verified `Iff.rfl` justification |
| — | local `def` | none | none | both: `a = 0`, so no spatial homogeneous norm is needed (contrast `research/R43/Spec.lean` §0) |

Agreed by both drafts and kept verbatim in `main` / `nonDensityBallZero`:

| ingredient | spelling | source |
|---|---|---|
| `𝓕_ℝ` | `MemForceR f` | `Data.lean:544` |
| `‖f‖_{L²(0,∞;H^{-1/2})}` | `forceSobolevENormL2 (-1 / 2) f` | `Data.lean:235` (= `forceSobolevENorm 2 (-1/2)`, `:225`) — **inhomogeneous**, never `forceHomogeneousENorm 2 (-1/2)` (`:390`) |
| `r_{ν,S}` as an `ℝ≥0∞` threshold | `ENNReal.ofReal (radius ν S)` | strict `<`, fail-safe: `⊤` never meets it |
| initial velocity `0` | `fun _ => 0` | `Data.lean:686-687`'s own spelling |
| `T^ν_{max,ℝ}(0,f) > S` | `ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f` | `Data.lean:657`; not `RegularThrough` (`:664`) |
| `B^ℝ_{ν,0,T}` | `breakdownSetRZero ν T` | `Data.lean:686` |

**Existing Lean for Proposition 4.4: none.** Both drafts grepped
`formalization/NSFormalization/{Source,Paper1,Paper3}` and
`vendor/NavierStokesAndEuler/NavierStokes` for `Rcritical2`, `critical2`,
`prescribed`, `Hminus`, `H^{-1/2}`, `negative Sobolev`, `finite interval`, and
agree: zero hits for a whole-space Prop 4.4. The nearest statement is B's find,
`Paper1/PeriodicCriticalRegularity.lean` (`CriticalRegularityCertificate`,
`critical_regular_ball`) — the **torus** `prop:critical`, proof *admitted*, and
it does not transfer: `04-whole-space.tex:4-5` names "the behavior of negative
Sobolev norms near frequency zero and the absence of a spectral gap" as the new
whole-space issues, which are exactly what force the `S`-dependent radius and
the inhomogeneous norm. A's find `Section4/I02/Prescribed.lean` matches only the
word "prescribed" (torus insertion cutoff). All reuse is at the
`Contracts.V1.Data` layer.

---

## 2. The two spellings, decided by experiment

Both were flagged by the brief; both were settled by running Lean, not by taste.

| item | A | B | decision | evidence |
|---|---|---|---|---|
| exponent | `ν ^ ((3 : ℝ) / 2)` | `ν ^ (3 / 2 : ℝ)` | **`ν ^ (3 / 2 : ℝ)`** (B's, = the ledger's `:617`) | `example (ν : ℝ) : ν ^ (3/2 : ℝ) = ν ^ ((3:ℝ)/2) := rfl` and `= Real.rpow ν (3/2) := rfl` both succeed — the two are interchangeable, so the ledger's spelling wins. The ascription is load-bearing: `(3 / 2 : ℕ)` would be `1`. |
| critical order | `-1/2` | `-(1/2)` | **`-1 / 2`** (A's parse) | `example : (-1/2 : ℝ) = -(1/2) := rfl` **fails** — `-1/2` parses as `(-1)/2` and is *not* defeq to `-(1/2)`. They are therefore different spellings of the same real, and since the order indexes a type (`RealVectorSobolev s` inside `forceSobolevENorm`), mixing them costs a transport. `-1 / 2` is what the frozen V1 contract `Contracts/V1/Thresholds.lean:15,16,17` uses three times, and what the ledger skeleton writes (`:622`). |

Checked in the same scratch run (all `rfl` / `Iff.rfl`, EXIT=0):

* `forceSobolevENormL2 (-1 / 2) f = forceSobolevENorm 2 (-1 / 2) f` — `rfl`;
* `f ∈ breakdownSetRZero ν T ↔ MemForceR f ∧ maximalLifespanR ν (fun _ => 0) f ≤ ENNReal.ofReal T`
  — `Iff.rfl` (**B's claim, verified**);
* `0 < c * ν ^ (3/2 : ℝ) * Real.exp (-(C*ν*S))` from `0 < c`, `0 < ν` alone —
  `mul_pos (mul_pos hc (Real.rpow_pos_of_pos hν _)) (Real.exp_pos _)`.

Note for downstream lanes: `Data.criticalOrder 2` is `2 / 2 - 3 / 2` and
`ThresholdAPI.exponent 2 0` is `-1 / 2 - 0`, so **no** literal spelling is
`rfl`-reachable from R41's threshold expression; R41 needs `norm_num` there
whatever R44 writes. The spelling choice matters for lemma *reuse* across lanes,
not for R41's own instantiation.

---

## 3. What each draft got right that the other missed

**A got right, B missed:**

* A04 **does** provide the bounded-horizon continuation R44 needs.
  `research/A04/Spec.lean:613` `extendsBeyond` concludes
  `ENNReal.ofReal S < maximalLifespanR ν a f` and its docstring at `:592-594`
  says, in as many words, "**This is the field `prop:Rcritical2` uses**", citing
  `04-whole-space.tex:171`. B's reported gap — "A04 does **not** provide a
  'lifespan `> S`' wrapper … the one place A04's current shape does not
  literally match" — is **false**; B was looking at A04's *other* field
  `lifespanInfiniteOfLocallyFinite` (`:657`), which is R43's.
* C01 **does** specialise to `a = 0`. `research/C01/Spec.lean:599`
  `h2TimeIntegralZeroDatum` exists and its docstring says it is "the shape
  Proposition 4.4 consumes", citing `STATEMENTS.md:604-605`. B's reported gap —
  "C01 does **not** specialise to `a=0`" — is **false**.
* The A04↔C01 power-spelling mismatch (A's G6) is real and still open:
  `A04/Spec.lean:202` `squaredHTwoIntegral` is
  `∫⁻ …, sobolevENorm 2 … ^ 2` (a `ℕ` power), while `C01/Spec.lean:576,599`
  bound `∫⁻ …, sobolevENorm 2 … ^ (2 : ℝ)`. B did not list it.

**B got right, A missed:**

* The D01 finiteness that makes the smallness ball a genuine neighbourhood is
  **already proved**: lane 042,
  `formalization/NSFormalization/Section4/D01/HalfOrder.lean:156`
  `forceSobolevENorm_ne_top {s : ℝ} {m : ℕ} (hsm : s ≤ (m : ℝ)) {q : ℝ≥0∞}
  (hq : q = 1 ∨ q = 2)`. Confirmed to cover R44's case: `m := 0`, `s := -1 / 2`
  (`-1/2 ≤ 0`, `norm_num`, spelling-independent), `q := 2`. A listed this as an
  open D01 obligation ("Neither piece is currently a registered lemma") and
  proposed the same `m = 0` route — the route is right, the work is done.
  What remains is **registration**: `Contracts/V1/DatumLemmas.lean:169` carries
  only the *spatial* `smoothJets_sobolevENorm_ne_top`.
* The `Iff.rfl` identification of `breakdownSetRZero` membership, which is what
  makes the `∉` form of field 9 consumable with no unfolding.

**Both got right (worth recording):** refusing `forceHomogeneousENorm 2 (-1/2)`;
`a = 0` not generalised; `ℝ≥0∞` throughout with no `.toReal`; lifespan
inequality rather than `RegularThrough`; no restatement of any sibling clause as
a field; no local `def`.

---

## 4. Gap table — one ranked list, merged

Ranked by what each blocks. "found by" credits the draft that identified it.
Nothing below blocks *stating* R44: `Spec.lean` typechecks against
`Contracts/V1/Data.lean` alone.

### Already satisfied — checked, not assumed

| id | what | where | found by |
|---|---|---|---|
| **S1** | `∀ f, MemForceR f → forceSobolevENormL2 (-1/2) f ≠ ⊤` (non-vacuity of the ball) | **proved**, lane 042 `Section4/D01/HalfOrder.lean:156`, at `m=0, s=-1/2, q=2` | B (A had it as open gap G3′) |
| **S2** | continuation at a *prescribed finite* `S`: `SolvesBelow … S u p → squaredHTwoIntegral S u ≠ ⊤ → ofReal S < maximalLifespanR ν a f` | `research/A04/Spec.lean:613` `extendsBeyond`, documented at `:592-594` as Prop 4.4's field | A (B called it a gap) |
| **S3** | the `∫₀^S‖u‖²_{H²}` assembly **at `a = 0`** (`K(S)=∫₀^S‖f‖₂`, `‖∇a‖₂=0`) | `research/C01/Spec.lean:599` `h2TimeIntegralZeroDatum` | A (B called it a gap) |
| **S4** | eq:RL2, eq:RH1 | `research/C01/Spec.lean:383,510,532` | both |
| **S5** | all critical embeddings R44 tests with, **including** the homogeneous→inhomogeneous comparison that `Y,Z` need | `research/A05/Spec.lean:268,280,366,384,396,406` (+`Cbessel` `:216`) | both |
| **S6** | the maximal-solution family behind `maximalLifespanR` | `research/A02/Spec.lean:210,421` | both |

### Blocks R44's own a-priori estimate — the substance the R44 proof lane owes itself

| id | owner | exact Lean shape needed | found by |
|---|---|---|---|
| **G1** | **D01** (weight algebra) | `J = (I−Δ)^{1/2}` (symbol `(1+|ξ|²)^{1/2}`, `02-preliminaries.tex:51`) and the **exact** identity `‖u‖²_{H^{3/2}} = ‖u‖²_{H^{1/2}} + ‖∇u‖²_{H^{1/2}}` — i.e. `(1+|ξ|²)^{3/2} = (1+|ξ|²)^{1/2} + |ξ|²(1+|ξ|²)^{1/2}`, exact, **not** up to constants (`STATEMENTS.md:588-590`); plus the duality `|⟨f, Ju⟩| ≤ ‖f‖_{H^{-1/2}}‖u‖_{H^{3/2}}` (`:591`). A05 supplies only the *inequality* `dotThreeHalvesLeGradientSobolev` (`A05/Spec.lean:280`) and `‖Jv‖₃ ≤ Cbessel‖v‖_{H^{3/2}}` (`:406`). No lane owns `J`. | both (A's GJ, B's U1) |
| **G2** | **R44's own lane** | eq:Rcritical2 `(Y²)' + νZ² ≤ C₂νY² + C₃ν^{-1}B²` while `Y ≤ θν` (`04-whole-space.tex:161-164`) on a **differentiable inhomogeneous critical path** — the analogue of `research/A04/Spec.lean:247` `HasSmoothSobolevPath` at order `1/2`, which no lane exports; then Grönwall from `Y(0)=0`, the choice `r_{ν,S} < θ²ν²/4`, and the **first-exit-time** closure on `[0, min(S,T_max))` (`:169`, `STATEMENTS.md:649-650`), with a single final `θ` serving both shrinkings (`:645-648`). | both (A's GC2, B's U3–U5) |

### Blocks R44's continuation half

| id | owner | exact Lean shape needed | found by |
|---|---|---|---|
| **G3** | **C01** (mirror of `forceTimeRegularity`, `C01/Spec.lean:326`) | the slice `B(t) = ‖f(t)‖_{H^{-1/2}}` as an interval-integrable real function with `∫₀ᵗ B(s)² ds = ‖f‖²_{L²(0,t;H^{-1/2})}`. `forceTimeRegularity` covers the **order-0** (`L²`) slice only, so the Grönwall right-hand side cannot yet be identified with the hypothesis norm. | A (G4′) |
| **G4** | **R44's lane** (a C01/A02 endpoint corollary would ease it) | assemble `SolvesBelow ν (fun _ => 0) f S u p` (`A04/Spec.lean:223`) from A02's maximal family; discharge C01's absorption gate `∀ t ∈ Ico 0 S, ENNReal.ofReal C₁ * criticalL3 (slice u t) ≤ ENNReal.ofReal (ν/4)` from `‖u‖₃ ≤ C(1/2)·Y ≤ C(1/2)·θν` by shrinking `θ`; supply `MemL1Hm f` (`A04/Spec.lean:268`, free from `MemForceR`, A04 unit F1). | A (GG) |
| **G5** | **A04 ↔ C01** spelling pin | one `ℝ≥0∞` identity `x ^ (2 : ℕ) = x ^ (2 : ℝ)` bridging `A04/Spec.lean:202` (`^ 2`, `ℕ`) to `C01/Spec.lean:576,599` (`^ (2 : ℝ)`). Identical to R43's gap **G6** (`research/R43/RECONCILIATION.md` §5 item 7); still open. | A (G6) |

### Packaging / registration — blocks nothing mathematically

| id | owner | what | found by |
|---|---|---|---|
| **G6** | **D01** | register lane-042 `forceSobolevENorm_ne_top` into `DatumLemmas` **V2** (+ a `Bindings` import of `HalfOrder`), so that S1 is a contract fact and not a theorem outside the build closure. | B |
| **G7** | tree-wide | pin `-1 / 2` (not `-(1 / 2)`) as the spelling of the `q = 2` critical order, matching `Contracts/V1/Thresholds.lean:15-17`. The two are **not** defeq (§2) and the order indexes a type. | this reconciliation |
| **G8** | A02/A04/A05/C01 | all four are research-stage specs; R44 cannot bind until they are registered contracts. | both |

---

## 5. Commands and results

```
cd WT && bash scripts/lean-install.sh                                # == OK
. scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
cd WT/verification
lake env lean ../research/R44/DraftA.lean    # EXIT=0, no output (unmodified)
lake env lean ../research/R44/DraftB.lean    # EXIT=0, no output (unmodified)
lake env lean ../research/R44/Spec.lean      # EXIT=0, no output
lake env lean /tmp/r44scratch/probe.lean     # EXIT=1 — the intended failure:
                                             #   (-1/2 : ℝ) = -(1/2) is NOT rfl
lake env lean /tmp/r44scratch/probe2.lean    # EXIT=0 — all §2 rfl/Iff.rfl checks
lake env lean /tmp/r44scratch/probe3.lean    # EXIT=0 — A-shape ↔ B-shape, and
                                             #   the two R41 derivations
```

`Spec.lean` contains one `structure`, no `def`, no proof term, no `sorry` /
`admit` / `axiom` / `native_decide` (those words appear only in the module
docstring), and no abstract `Prop` placeholder field.
