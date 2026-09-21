# R44 draft B — comparison, provenance and gaps

**Proposition 4.4** (`prop:Rcritical2`, "Regularity on a prescribed finite
interval"), `paper/sections/04-whole-space.tex:136-144` (proof `:145-174`).
Draft B specification: `research/R44/DraftB.lean`, structure
`BlowupDensity.R44.DraftB.RCritical2API`.  Typechecks (see §6).

## 0. The statement, transcribed

    ∃ c, C > 0, ∀ ν, S > 0, ∀ f ∈ 𝓕_ℝ,
      ( ‖f‖_{L²(0,∞;H^{-1/2})} < c ν^{3/2} e^{−CνS}  ⟹  T^ν_{max,ℝ}(0,f) > S ).

Four things a careless formalisation gets wrong, and where the paper pins each:

| # | fact | paper | how draft B encodes it |
|---|---|---|---|
| 1 | `c, C` universal, **both `ν`- and `S`-free**; radius depends on **both** `ν` and `S` (`e^{−CνS}`, so it shrinks as `S` grows) | `:143`, `STATEMENTS.md:594,641` | `c C : ℝ` are fields (bound before `∀ ν ∀ S`); radius inlined as `ENNReal.ofReal (c * ν^(3/2) * Real.exp (-(C*ν*S)))` |
| 2 | initial velocity **exactly `0`** (Grönwall from `Y(0)=0`) | `:137,141`, risk `:631` | datum `fun _ => 0`, spelling of `Data.breakdownSetRZero` (`Data.lean:686-687`) |
| 3 | force norm **INHOMOGENEOUS `H^{-1/2}`**, not `Ḣ^{-1/2}` | `:140,173`, risk `:570-571,639-640` | `forceSobolevENormL2 (-1/2)` = `forceSobolevENorm 2 (-1/2)` (`Data.lean:225,235`), never `forceHomogeneousENorm` |
| 4 | conclusion strict lifespan `T^ν_max(0,f) > S` | `:141` | `ENNReal.ofReal S < maximalLifespanR ν 0 f` (`Data.lean:657`) |

**Chosen conclusion form: the lifespan inequality, not `RegularThrough`.**
`Data.RegularThrough ν 0 f S` (`Data.lean:664`) = `∃ δ>0, Nonempty
(ClassicalSolutionR ν 0 f (S+δ))` is provably *equivalent* to
`ofReal S < maximalLifespanR ν 0 f` under `Data.maximalLifespanR`'s `⨆`
definition, but the lifespan form is (a) the literal transcription of "`T^ν_max
> S`" and (b) the *definitional negation* of `f ∈ Data.breakdownSetRZero ν S`,
so `R41` consumes it with no massaging (verified by `Iff.rfl`, §6).

## 1. Field-by-field provenance

| field | paper line | consumed from (statement / proof) | existing Lean | gap |
|---|---|---|---|---|
| `c`, `C`, `hc`, `hC` | `:143` | — (R44 owns the two universal constants) | none | R44's own; proved when the R44 proof lane closes |
| `main` (the theorem) | `:136-144` | statement: `Data` only. proof route: A05 embeddings + A04 continuation + C01 energy + A02 maximal family + D01 identities (§3) | **none** for R³; nearest is the torus analogue `Paper1/PeriodicCriticalRegularity.lean` (`prop:critical`, proof *admitted*), which does **not** transfer — R³ has no spectral gap (`:4-5`) | whole proof open; owned by future R44 proof lane |
| `nonDensityAtHorizon` (`S=T` consequence for R41) | `:141`, consumed at `STATEMENTS.md:133-136` | this is exactly `RMainAPI.nonDensityZero`'s `q=2`, `s=-1/2` base case (`STATEMENTS.md:160-164`) | none | one-line specialisation of `main` at `S:=T`; proved once `main` is |

### Objects reused from `Contracts/V1/Data.lean` (all frozen V1, no restatement)

| object | `Data.lean` | manuscript |
|---|---|---|
| `MemForceR` = `𝓕_ℝ` | `:544` | eq:Rclasses `02-preliminaries.tex:17` |
| `forceSobolevENormL2 s` = `forceSobolevENorm 2 s` = `‖·‖_{L²(0,∞;H^s)}` | `:235`, `:225` | `01-introduction.tex:132`; `04-whole-space.tex:140` at `s=-1/2` |
| `maximalLifespanR ν a f` = `T^ν_{max,ℝ}(a,f)` | `:657` | `02-preliminaries.tex:32` |
| `breakdownSetRZero ν T` = `B^ℝ_{ν,0,T}` | `:686` | eq:Rsingularforces `02-preliminaries.tex:42` |

Draft B adds **no** local `def`: with `a=0` the manuscript's hypothesis mentions
only the force norm, so (unlike `research/R43/Spec.lean`, which needs a spatial
`dotHomogeneousENorm` for `‖a‖_{Ḣ^{1/2}}`) no spatial homogeneous-norm object is
required here.

## 2. Existing Lean — grep results

Searched `formalization/NSFormalization/{Source,Paper1,Paper3}` and
`vendor/NavierStokesAndEuler/NavierStokes` for `Rcritical2`, `prescribed`,
`Hminus`, `negative Sobolev`, `finite interval`, `H^{-1/2}`, `critical2`.

* **`Rcritical2`, `critical2`, `H^{-1/2}`: zero hits.** No whole-space
  Proposition 4.4 exists anywhere in the tree.
* **`Paper1/PeriodicCriticalRegularity.lean`** — the closest existing statement:
  the **torus** `prop:critical` (`CriticalRegularityCertificate`,
  `critical_regular_ball`), analytic **proof admitted**.  Wrong domain (𝕋³) and
  does not transfer: `04-whole-space.tex:4-5` names "the behavior of negative
  Sobolev norms near frequency zero and the absence of a spectral gap" as the
  new whole-space issues — exactly what forces the `S`-dependent radius and the
  inhomogeneous norm here.
* **`Source/*Insertion*`, `Source/SmoothLifespan.lean`,
  `Source/WholeSpaceDensity.lean`** — insertion / lifespan machinery for the
  *density* half (R42/R41D), not the critical regularity converse.
* **`vendor/.../TangentODE.lean:196`** — Grönwall/uniqueness on a finite interval
  (generic ODE tool); potentially reusable inside the eventual proof, not the
  statement.
* `negative Sobolev` hits (`Paper3/Thresholds.lean`, vendor pressure files) are
  index arithmetic and pressure realizations, unrelated to this proposition.

**Conclusion: the statement itself is a total gap in R³ Lean.**  The spec pins
it against `Data.lean` objects that *do* exist; the theorem behind `main` does
not.

## 3. Clauses R44 consumes, and what the sibling specs do NOT yet provide

`R44 ← A04, A05, C01` (`STATEMENTS.md:598`), transitively `← A02, ← D01`.  None
of these is a hypothesis of `RCritical2API` (the manuscript's Prop 4.4 carries
none — the constants are absorbed and the data objects are `Data.lean`'s); they
are consumed **inside the future proof**.  Status of each, as the specs actually
stand on this branch:

### From A05 (`research/A05/Spec.lean`, `CriticalEmbeddingAPI`) — mostly ready
A05 was written with Prop 4.4 in mind and **provides**:
* `:214-216` `Cbessel` + the inhomogeneous multiplier bound `‖Jv‖₃ ≤ C‖v‖_{H^{3/2}}`
  ("the inhomogeneous multiplier form Proposition 4.4 tests against").
* `:268` `homogeneousLeSobolev`: `‖z‖_{Ḣ^a} ≤ ‖z‖_{H^a}` for `0 ≤ a < 3/2` — the
  homogeneous→inhomogeneous comparison at `a ∈ {1/2,1}` that turns Lemma B.1's
  homogeneous embeddings into bounds on the inhomogeneous `Y, Z`.
* `:280` `dotThreeHalvesLeGradientSobolev`: `‖v‖_{Ḣ^{3/2}} ≤ ‖∇v‖_{H^{1/2}} = Z`.
* `:204-213` the `‖u‖₃`, `‖∇u‖₃+‖Λu‖₃`, `‖∇u‖₆ ≤ C‖Δu‖₂` constants/estimates.

**A05 does NOT provide:** a *bundled* estimate `‖Ju‖₃ ≤ C(Y²+Z²)^{1/2}` already
composed with the `H^{3/2}` identity — A05 gives `‖Jv‖₃ ≤ C‖v‖_{H^{3/2}}`, and
the identity `‖v‖²_{H^{3/2}} = Y²+Z²` is R44's (see D01 below).  This is a
composition R44's proof does, not a missing A05 field.  A05 is a **draft spec**,
not yet a registered contract; it must land first.

### From C01 (`research/C01/Spec.lean`) — ready, but stated for general `a`
Provides, each `∀ a ∈ initialClassR`:
* `enstrophyIntegralBound` (eq:RH1, `H¹` absorption once `ENNReal.ofReal C₁ *
  criticalL3 (u s) ≤ ν/4` on `[0,t]`);
* `l2Bound` (eq:RL2, `‖u(t)‖₂ ≤ energyBudget a f t`);
* `h2TimeIntegral` (the `∫₀ˢ‖u‖²_{H²} < ∞` assembly, the `< ∞` A04 consumes).

**C01 does NOT specialise to `a=0`:** the `a=0` reductions `K(S)=∫₀ˢ‖f‖₂` and
`‖∇a‖₂=0` (`STATEMENTS.md:605`) are R44's own instantiation of C01's general
`energyBudget`.  Not a missing C01 field — R44 supplies `a := (fun _ => 0)` and
discharges `0 ∈ initialClassR`.  The absorption gate hypothesis
`‖u‖₃ ≤ ν/(4C₁)` is delivered by R44 from A05's `‖u‖₃ ≤ CY ≤ Cθν`.

### From A04 (`research/A04/Spec.lean`, `ContinuationAPI`) — ready
Provides the squared-`H²` continuation adapter
(`lifespanInfiniteOfLocallyFinite` region, `:296` onward) turning
`∫₀ˢ‖u‖²_{H²} < ∞` at every finite `S` into exclusion of a finite maximal
lifespan.  **A04 does NOT provide a "lifespan `> S`" wrapper:** its adapter is
oriented at *global* exclusion (`T_max = ⊤`); R44 needs the *bounded-horizon*
form "exclude a maximal lifespan **at or before `S`**" (`STATEMENTS.md:606-607`).
This is a re-use of the same energy computation on `[0,S]` rather than
`[0,∞)` — a wrapper R44's proof builds around A04's clause, not a new A04 field,
but it is the one place A04's current shape does not literally match.

### From A02 (`research/A02/Spec.lean`, `MaximalSolutionAPI`) — ready
`IsMaximalSolution` (`:210`) and the maximal-solution family (`:421`,
`exists ... IsMaximalSolution`) that the continuation argument runs on.
**Nothing missing** for R44 beyond A02 landing as a contract.

### From D01 — the finiteness lemma and the weight identity
* **Inhomogeneous non-vacuity (the vacuity trap, §4):**
  `∀ f, MemForceR f → forceSobolevENorm 2 (-1/2) f ≠ ⊤`.  **Proved** (lane 042,
  `HalfOrder.lean` `forceSobolevENorm_ne_top`, general `s ≤ m`, `q ∈ {1,2}`,
  standard axioms; here `s=-1/2 ≤ 0 = m`, `q=2`).  **Not yet registered** — the
  reviewer note routes it to `D01.datum_lemmas` **V2** (add the field + a
  `Bindings` import of `HalfOrder`); it is not in this worktree's build closure.
  This is the single "pending registration" dependency; it exists in Lean.
* **The exact Fourier weight identity** `‖u‖²_{H^{3/2}} = ‖u‖²_{H^{1/2}} +
  ‖∇u‖²_{H^{1/2}}` (i.e. `(1+|ξ|²)^{3/2} = (1+|ξ|²)^{1/2} + |ξ|²(1+|ξ|²)^{1/2}`,
  exact, not up to constants — `STATEMENTS.md:589-590`).  **Open**; owned by R44
  (D01's weight algebra).  A05 gives only the *inequality*
  `dotThreeHalvesLeGradientSobolev`.
* **The `J=(I−Δ)^{1/2}` duality** `|⟨f,Ju⟩| ≤ ‖f‖_{H^{-1/2}}‖u‖_{H^{3/2}}`
  (`STATEMENTS.md:591`).  **Open**; owned by R44.
* `⟪D01:normLp 3⟫`, the `L¹_t`/`L²_t` norms of `f` on `(0,∞)` (finite by
  `MemForceR`, "not required to be small", `:171`), `⟪D01:normHs 2⟫`,
  `⟪D01:Leray⟫`, `⟪D01:pairing⟫` (`STATEMENTS.md:586-593`) — proof-internal.

### R44's own lane (not owned by any sibling — like R43's G7)
`eq:Rcritical2` `(Y²)' + νZ² ≤ C₂νY² + C₃ν^{-1}B²` while `Y ≤ θν`; the
differentiable inhomogeneous critical path `Y`; the Grönwall step producing the
`e^{C₂νS}` factor from `Y(0)=0`; the first-crossing / first-exit-time argument
on `[0, min(S,T_max))` (`STATEMENTS.md:649`); the single `θ` serving both the
`eq:Rcritical2` gate and the `H¹` absorption (`STATEMENTS.md:647-648`).  This is
the substance the R44 proof lane owes itself.

## 4. The vacuity trap — resolved by the norm choice

*Can `forceHomogeneousENorm 2 (-1/2) f` be `⊤` for every `f ∈ 𝓕_ℝ`?*  Not for
*every* `f` (`0 ∈ 𝓕_ℝ` has homogeneous norm `0`), but it can be `⊤` for `f` that
are perfectly finite in the inhomogeneous norm — the low-frequency failure the
paper flags at `:173`.  Two independent reasons make the **homogeneous** norm the
wrong choice, and the **inhomogeneous** norm the right one:

1. **Mathematics.**  `:173`: "smallness in `H^{-1/2}` does not control the
   homogeneous negative norm at low frequencies"; the inhomogeneous norm is
   *essential*.  A homogeneous hypothesis would state a proposition **false as
   proved**.
2. **Non-vacuity in Lean.**  Draft B's `forceSobolevENorm 2 (-1/2)` fails safe to
   `⊤` (no measurable datum path ⟹ hypothesis fails), *and* is `≠ ⊤` on all of
   `𝓕_ℝ` by the **proved** lane-042 lemma — so the ball `{f ∈ 𝓕_ℝ : ‖f‖ <
   r_{ν,S}}` is a genuine neighbourhood of `0`.  The homogeneous twin's
   finiteness is **open** (lane 042 GAP: a homogeneous datum for general `H^∞`
   slices, multiplier `|ξ|^{1/2}(1+|ξ|²)^{-1/4}`), so a homogeneous formalisation
   would risk being vacuously true until that lands.

The inhomogeneous norm removes both problems at once; draft B uses it.

## 5. Unit split (for the eventual R44 proof lane, ≤ 8 units)

| unit | content | size |
|---|---|---|
| U1 | D01 weight identity `‖u‖²_{H^{3/2}} = ‖u‖²_{H^{1/2}} + ‖∇u‖²_{H^{1/2}}` (exact) and the `J=(I−Δ)^{1/2}` duality `|⟨f,Ju⟩| ≤ B(Y²+Z²)^{1/2}` | **S** (algebra of Fourier weights) |
| U2 | register lane-042 `forceSobolevENorm_ne_top` into D01.datum_lemmas V2 (+ `Bindings` import of `HalfOrder`); non-vacuity of the ball | **S** (proof exists, packaging only) |
| U3 | the inhomogeneous critical energy identity: testing against `Ju`, dissipation `νZ²`, differentiability of `Y²` on a critical path (a `HasSmoothCriticalPath`-analogue) | **M** (new; parallels R43 G7) |
| U4 | Young/absorption bookkeeping → `eq:Rcritical2` `(Y²)'+νZ² ≤ C₂νY²+C₃ν^{-1}B²` while `Y≤θν`, fixing `θ,C₂,C₃` | **M** (the paper's `:160-163` outline is not a derivation) |
| U5 | Grönwall from `Y(0)=0` → `Y(t)² ≤ C₃ν^{-1}e^{C₂νS}‖f‖²_{L²_tH^{-1/2}}`; radius `r_{ν,S}=cν^{3/2}e^{−CνS}` and the first-crossing/first-exit closure | **M** (variable-coeff Grönwall + continuity bootstrap) |
| U6 | continuation half on `[0,S]`: assemble C01 `enstrophyIntegralBound`/`l2Bound`/`h2TimeIntegral` at `a=0` with A05 `‖u‖₃≤CY≤Cθν`, feed A04's adapter to exclude `T_max ≤ S` | **M** (integration of sibling clauses; needs the A04 bounded-horizon wrapper) |
| U7 | assemble `main`; derive `nonDensityAtHorizon` at `S=T` (`f ∉ breakdownSetRZero ν T`) | **S** |

Blocking order: U1,U2 (data) → U3→U4→U5 (the a-priori bound) → U6 (continuation)
→ U7 (assembly).  U3–U5 are the genuine new mathematics; U6 is sibling
integration; U1,U2,U7 are small.  Prerequisites outside the lane: A05, C01, A04,
A02 must be **registered contracts** (currently research-stage specs) and the
A04 bounded-horizon continuation wrapper must exist.

## 6. Commands and results

* Install: `bash scripts/lean-install.sh` → `== OK` (Mathlib cache replayed,
  `lake test` green).
* Typecheck: `cd verification && lake env lean ../research/R44/DraftB.lean` →
  **EXIT=0**, no output (clean).  No `sorry`/`admit`/`axiom`/`native_decide` in
  the file (only the words appear inside the module docstring).  No axiom audit
  applies: the file declares one `structure` and no proof term.
* Semantic checks (scratch, all `rfl`/`Iff.rfl`/`norm_num`, EXIT=0):
  - `forceSobolevENormL2 (-(1/2)) f = forceSobolevENorm 2 (-(1/2)) f`  (q=2, s=−1/2, inhomogeneous);
  - `ν ^ (3/2 : ℝ) = Real.rpow ν (3/2)`  (the exponent is real `rpow`, not `npow`);
  - `(-(1/2) : ℝ) = -0.5`  (the `H^{-1/2}` order);
  - `f ∈ breakdownSetRZero ν T ↔ MemForceR f ∧ maximalLifespanR ν (fun _=>0) f ≤ ENNReal.ofReal T`  (`Iff.rfl`) — confirms `nonDensityAtHorizon`'s `∉` is the exact negation `R41` consumes, with the zero datum spelled to match.
