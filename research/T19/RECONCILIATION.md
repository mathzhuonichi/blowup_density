# T19 (the density package on `T³`: `prop:density` `03-torus.tex:349-382`, `cor:mixed` `:528-539`, `cor:closure` `:540-563`, `prop:projection` `:564-590`) — reconciliation of drafts A (lane 367) and B (lane 372)

Drafts: `.claude/worktrees/367-SPEC-t19-draft-a/research/T19/DraftA.lean` (553 lines; Opus; `PeriodicDensityAPI` 3 / `MixedRegionAPI` 4 / `StrongClosureAPI` 3 / `ProjectionAPI` 3, image-equality projection, defines `RegularTrajectoryT`/`SingularTrajectoryT`/`extendedBreakdownSetT`/`spaceTimeL2L2ENormT`, copies 4 carriers into the T19 namespace, uses registered `alpha`); `.claude/worktrees/372-SPEC-t19-draft-b/research/T19/DraftB.lean` (465 lines; Opus; 3 / 3 / 2 / 3, operational projection, defines `RelativelyDenseMixedT`, copies 3 carriers into `BlowupDensity.T15.Draft` with an `alphaT := alpha` drift `example`). Both blind, both statement-only, both elaborate clean (`lake env lean`, 0 errors, no `sorry`/`admit`/`axiom`/`native_decide`).

Upstream read: paper `:349-382,528-590`; registered `Contracts/V1/{TorusData,TorusLocalTheory,MainThresholds,CompletedDensity,Data,MaximalPartial,Correction}.lean`; the reconciled but unregistered `research/T18/Spec.lean` (`PeriodicInsertionAPI`, `periodicInsertionStatement`, the `:395-433` carrier block) and `research/T18/RECONCILIATION.md`; the house-style reconciliations `research/T18/RECONCILIATION.md`, `research/T24/RECONCILIATION.md`.

Key registration facts established while reconciling (they drive §2–§3):
- **`RelativelyDenseT`, `breakdownSetT`, `RegularThroughT`, `forceSobolevENormT`, `energyENormT`/`energyEssSupT`/`energyGradientT`, `ClassicalSolutionT`, `maximalLifespanT`, `forceClassT`, `initialClassT`, `criticalOrder`, `alpha`, `MaximalPartial.{limsupLeft,speedENorm}` are all registered** (`TorusLocalTheory.lean:89,221,205,89,233-246,144,200,109,97`; `Data.lean:259`; `Correction.lean:160`; `MaximalPartial.lean:101,106`). Both drafts write the four results almost entirely in this vocabulary. `RelativelyDenseT q s Y S := ∀ g∈Y, ∀ r>0, ∃ f∈S, forceSobolevENormT q s (f-g) < r` — the registered ε-approximation predicate the paper's "dense" unfolds to.
- **The torus mixed-Lebesgue norm is NOT registered.** Only the whole-space `Data.mixedLebesgueENorm` (`Data.lean:251`, `volume : Measure Space`) exists; `cor:mixed`'s `L^q(0,∞;L^p(T³))` needs the torus `mixedLebesgueENormT` (`periodicTorusMeasure`), which lives only in `research/T15|T18/Spec.lean`. So it (and its dependency `IsPeriodicLebesgueSlicePath`) must be copied. `alpha` is registered, so `alphaT` need not be.
- **T18 (`PeriodicInsertionAPI`) is reconciled but UNREGISTERED** — the same status T15 had for T18. Contracts may import only `Contracts.*`, so a registered T19 contract **cannot** produce/thread the T18 record; it must restate `thm:insertion`'s conclusions in registered torus vocabulary. This is exactly what R41 (`MainThresholdsAPI.regularReferenceApproximation`) and R46 (`CompletedDensityAPI.strongTrajectoryClosure`) do — except R46 can `∃ (A : InsertionFamilyAPI …)` because whole-space `InsertionFamilyAPI` **is** registered (`Contracts/V1/InsertionFamily.lean`), whereas T18's torus analogue is not.
- **R41/R46 carry NO honesty guards.** Their closeness is `Tendsto (fun ε => forceSobolevENorm q s (f ε - g)) (𝓝[>] 0) (𝓝 0)` and their density is strict `< r` — both self-guarding in `ℝ≥0∞` (an `⨅` that is `⊤` cannot satisfy `< r`, and `Tendsto (eventually ⊤) (𝓝 0)` is false). No `MemForceSobolev`/`MemMixed` field appears.
- `criticalOrder 1 = 2/1 − 3/2 = 1/2` (`Data.lean:259`); `alpha p q = −3 + 3/p.toReal + 2/q.toReal`, so `3/p+2/q>3 ⟺ 0 < alpha p q` and then `0 < alpha p q + 1` is immediate. `speedENorm = eLpNorm z ⊤ volume` (L∞); `limsupLeft T φ = limsup φ (𝓝[<] T)`.

## 0. Lead review

### Lead review (2026-09-18 12:30Z)
Drafted by an Opus subagent from the two blind drafts (367 / 372, both Opus, mutually invisible); reviewed and **approved** by the lead. Binding: per-structure bases (B, B, A, A); all four `Prop`; T18's insertion record **not threaded** — its conclusions restated in registered torus vocabulary (T19 consumes `thm:insertion` as a black box; same reason the T15 chain is threaded into T18 but not here); density/closure as ε-approximation (`RelativelyDenseT`, `RelativelyDenseMixedT`); registered `Contracts.V1.alpha`; no honesty guards (all closeness `< r` or `Tendsto … (𝓝 0)`, self-guarding in `ℝ≥0∞`); `𝓧` topology discharged by fixing `a`; citation hygiene (`:579/:586/:590/:591`) mandatory in the finalization. Owner questions (1)–(5) of §4 stand; (1) "register T18 before T19 assembly" is the standing T15→T18→T19 registration order.

(left for the lead)

## 1. Agreement

Both drafts are honest, non-vacuous, `sorry`/axiom-free statement APIs. Neither introduces a constant or datum; all four structures are `Prop`-valued (the inserted families are bound existentially inside fields). They agree, faithfully to the paper, on:

- **The headline density field** — byte-identical in both: `∀ a ∈ initialClassT, ∀ ν>0, ∀ T>0, ∀ s<1/2, RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)` (A `density`, B `fixedInitialDensity`), and an identical `def periodicDensityStatement`. This is `prop:density` (`:349-357`), and it unfolds to the paper's `∀g∀ρ∃f: ‖f−g‖_{L¹_tH^s}<ρ ∧ T_max^ν(a,f)≤T`.
- **The threshold** `s<1/2` written literally (numerically `= criticalOrder 1`, `:355`); the torus fixes `q=1` (no `q∈{1,2}`, unlike R41 — the other norms are `cor:mixed`).
- **The `:590` distinction**: both record that the regular-reference case yields lifespan **exactly** `T` (`maximalLifespanT ν a f = ofReal T`), sharper than the `≤ ofReal T` of the density set (A `regularReferenceApprox`, B `regularReferenceSingular`).
- **`cor:mixed`**: the region `1≤p,q≤∞, 3/p+2/q>3` with `[Fact (1≤p)]` + explicit `1≤q` (endpoints `p,q=∞` formally included, `toReal ⊤ = 0`); density via the copied torus `mixedLebesgueENormT`; and the arithmetic driver `α(p,q)>0 ⟹ α(p,q)+1>0` (A `mixedRegionArithmetic`, B `regionPositive`).
- **`cor:closure`**: the simultaneous family `(u_ε,g_ε)→(v,g)` in `E_T × L¹_tH^s` (`s<1/2`) around a reference `ClassicalSolutionT ν a g (T+δ)`, `δ>0`, with per-`ε` exact lifespan and a full classical solution whose velocity is the approximant, both limits along `𝓝[>] 0`, sharing one existential family (A `simultaneousPairConvergence`, B `strongClosure`) — mirroring R46.
- **`prop:projection`**: `𝔅_{ν,T}={(a,f)∈𝓧×𝓕: T_max^ν(a,f)≤T}` dense in the product topology, with the initial datum **kept fixed at `a`** to discharge "any topology on `𝓧`" (its own point lies in every `𝓧`-neighborhood, `:573-574`); the `∀a∃f` order (`:579`) respected in every field; the `a=0` fibre projecting to `{0}` (`:571`).
- **No T20.** Both correctly exclude `prop:critical` / `CriticalRegularityTAPI` (T20): the density package is constructive (proofs consume `thm:insertion` = T18); T20 feeds `cor:nondensity` = node T21.
- **Junk-value discipline**: all distances/norms are `ℝ≥0∞` (`forceSobolevENormT`, `mixedLebesgueENormT`, `energyENormT`); no real `sSup`, no `.toReal` collapse; `ν,T,δ,r>0` on every field.

Substance is the same four results. The disagreements are all about **granularity and rendering**, not about which theorem is stated; and — unlike T18 and T24 — **neither draft contains a false clause**.

## 2. Rulings

`𝔅 := extendedBreakdownSetT`; `R/S := RegularTrajectoryT / SingularTrajectoryT`.

### `prop:density` → `PeriodicDensityAPI`

| clause | A | B | ruling (reason) |
|---|---|---|---|
| headline density `:351-357` | `density` = `RelativelyDenseT 1 s …` | `fixedInitialDensity` = same | **both, identical.** Keep verbatim. |
| threshold `:355` `s<1/2` | in docstring only | `thresholdValue : criticalOrder 1 = 1/2` (field) | **B.** A field mirrors R41's `thresholdValues`; pins the torus threshold to the same arithmetic. Cheap, honest real equality. |
| already-singular case `:360-363` (`T_max≤T`, `f=g`) | `alreadySingularApprox` (separate field) | folded into the proof (no field) | **B (drop A's field).** R41 has no separate already-singular field; `f=g` with `‖0‖=0<r` is a trivial proof case, not a statement clause. |
| regular-reference exactly-`T` `:364-380`,`:590` | `regularReferenceApprox` (one `ε₀`, one family `f:ℝ→𝓕`, per-`ε` `f ε∈𝓕 ∧ f ε−g∈𝓕 ∧ lifespan=ofReal T ∧ solution`, split `0≤s<1/2` / `s<0` `Tendsto` **+ `MemForceSobolevT` guards**) | `regularReferenceSingular` (per-`(s,r)` `∃f∈𝓕, ‖f−g‖<r ∧ lifespan=ofReal T`, hypothesis `RegularThroughT ν a g T`) | **B.** `prop:density`'s *statement* is the density line; the `:590` distinction needs only "near every reference regular through `T`, ∃ a nearby force with lifespan **exactly** `T`". B's per-`(s,r)` strict-`<r` form says exactly that, is self-guarding (no honesty guard), uses the registered `RegularThroughT`, and does **not** split `s`-ranges (the `0≤s<1/2` vs `s<0` split is proof-internal — R41 states one uniform `∀s`). A's full family+energy content is `cor:closure`'s job (it would duplicate `simultaneousPairConvergence`); drop it here. |

### `cor:mixed` → `MixedRegionAPI`

| clause | A | B | ruling (reason) |
|---|---|---|---|
| density on the region `:530-535` | `mixedDensity` (inlined `∃f∈𝓑, mixedLebesgueENormT q p (f−g)<r`) | `mixedDensity` via `RelativelyDenseMixedT q p forceClassT (breakdownSetT …)` | **B.** `RelativelyDenseMixedT` is the exact mixed-norm analogue of registered `RelativelyDenseT`; one place to bind later, parallel to the Sobolev statement. Both are strict-`<r` (self-guarding). |
| arithmetic driver `:536-537` | `mixedRegionArithmetic` (**registered** `alpha p q`) | `regionPositive` (copied `alphaT p q`) | **A's spelling on B's field.** Use the **registered** `Contracts.V1.alpha` directly (T18 §3 decision); drop the `alphaT` copy + drift `example`. Content identical (`0<alpha ∧ 0<alpha+1`). |
| named spaces `:538` (`L¹_tL²_x`, `L²_tL^{4/3}_x`) | absent | `regionExamples` (`3/2+2/1>3 ∧ 3/(4/3)+2/2>3`, real literals) | **B, retimed to the registered exponent.** Keep the `:538` illustration, but state it as `0 < alpha 2 1 ∧ 0 < alpha (4/3) 2` at `ℝ≥0∞` points so it instantiates the region predicate rather than floating as disconnected reals (`α(2,1)=1/2>0`, `α(4/3,2)=1/4>0`). |
| already-singular / regular-reference **mixed** cases | `alreadySingularMixedApprox`, `regularReferenceMixedApprox` (family+`Tendsto`+`MemMixedLebesgueT`) | absent | **drop both (A).** The paper's proof says "use the **same two cases** as in `prop:density`" (`:535`); re-articulating them in the mixed norm is redundant. Dropping them also removes the only need for `MemMixedLebesgueT` — no honesty-guard copy is required. |

### `cor:closure` → `StrongClosureAPI`

| clause | A | B | ruling (reason) |
|---|---|---|---|
| `eq:closure` set inclusion `:543-547` `R_{a,T}⊆S̄_{a,T}^{E_T}` | `closureInEnergy` (ε-approx via defined `R`/`S` trajectory sets) | operational only (no set inclusion) | **A.** The task's `eq:closure` check is literal; A's `RegularTrajectoryT`/`SingularTrajectoryT` render the paper's `R`/`S` (`:544-547`) over registered `ClassicalSolutionT`, and `closureInEnergy` renders `⊆ closure^{E_T}` as ε-approximation (the `RelativelyDenseT` convention, no `TopologicalSpace` on force space). Both `R` and `S` differences have finite `E_T`, so `<r` is meaningful. |
| simultaneous pair convergence `:548-552` | `simultaneousPairConvergence` (family + `E_T` limit + `∀s<1/2` `L¹_tH^s` limit; per-`ε` `SingularTrajectoryT (u ε)`) | `strongClosure` (family + `energyENormT<⊤` + a `ClassicalSolutionT` with pinned velocity **+ history on `[0,T−2ε²]`** + both limits) | **A, minus history.** A mirrors R46's `strongTrajectoryClosure` shape (family, exact lifespan, solution, two `Tendsto` along `𝓝[>] 0`). R46 carries **no** `history` clause; drop B's `history` (it is a `thm:insertion` detail, not a `cor:closure` statement clause). Keep A's `SingularTrajectoryT (u ε)` (finite `E_T` + blow-up) — it ties the approximants to `S_{a,T}`. |
| reference finite `E_T` `:550-551` | implied by `SingularTrajectoryT`/`RegularTrajectoryT` | `referenceFiniteEnergy : energyENormT T reference.velocity < ⊤` (field) | **B (add as a 4th field).** Anchors the `E_T` limit in a finite-distance ambient space; the reference's finiteness (smooth through `T` ⟹ bounded on compact `[0,T]×T³`) is otherwise only implicit. Cheap, honest. |
| norm-equivalence `:555-560` (`‖z‖_{L²_tL²} ≤ T^{1/2}‖z‖_{L^∞_tL²}`) | `energyTimeEmbedding` (`spaceTimeL2L2ENormT T z ≤ ofReal(√T)·energyEssSupT T z`) | deferred to a proof-side lemma | **A.** A displayed inequality (`:559`), TRUE in `ℝ≥0∞` (`∫_{Ioo 0 T} h² ≤ (essSup h)²·ofReal T`, then `rpow ½`), self-contained and reusable; it documents the `E_T ↔ L²_tH¹` reading `eq:closure` relies on. Keep the local `spaceTimeL2L2ENormT`. |

### `prop:projection` → `ProjectionAPI`

| clause | A | B | ruling (reason) |
|---|---|---|---|
| product density `:568-577` (keep `a` fixed) | `extendedProductDensity` (`∃f, (a,f)∈𝔅 ∧ forceSobolevENormT 1 s (f−g)<r`) | `productDensity` (`∃f∈𝓕, ‖f−g‖<r ∧ maximalLifespanT ν a f ≤ ofReal T`) | **A.** Uses the defined pair set `𝔅 = extendedBreakdownSetT` (the paper's `:566-567` object), making the "density of the *pair* set" explicit; B's component form is equivalent but does not name `𝔅`. |
| projection onto `𝓧` is all of `𝓧` `:570`,`:579` | `projectionOntoInitialData : Prod.fst '' 𝔅 = initialClassT` | `projectionOntoInitial : ∀a∈𝓧, ∃f∈𝓕, T_max≤T` | **A.** The literal `Prod.fst '' 𝔅 = 𝓧` (the task's check). `⊆` is by construction (`𝔅 ⊆ 𝓧×𝓕`); `⊇` is the genuine `∀a∃f` content (from `prop:density`). B states only the `⊇` half operationally. |
| `a=0` fibre `:571` projects to `{0}` | `zeroInitialProjection : Prod.fst '' {p∈𝔅 ∣ p.1=0} = {0}` | `zeroInitialFiber : 0∈𝓧 ∧ ∃f∈𝓕, T_max^ν(0,f)≤T` | **A.** The literal `= {0}`; `⊇` forces the `a=0` fibre nonempty (a real singular force over `0`, `0∈initialClassT`), so the singleton is inhabited, not `∅`. B's inhabitation form is the `⊇` content without the image equality. |
| `:586` "`{0}` not dense in nontrivial normed `𝓧`" | omitted | omitted | **omit from both (justified).** Needs an abstract normed topology on `𝓧`, which the paper deliberately leaves generic ("any topology on `𝓧`"); no registered `𝓧` topology exists. Captured operationally by the `∀a∃f` order + `zeroInitialProjection`. Owner question §4. |

## False clauses / traps

**No clause of the four results is false in either draft, and none is missing from both** (up to the justified `:586` omission). This is the material difference from T18 (A's periodic single-ball support) and T24 (B's global `velocity=0`, the `tsupport ⊆ ball` and junk `sSup` traps): T19 consumes `thm:insertion` as a black box and therefore carries **no localization/support clause**, so the "periodized field is never inside one ball" trap cannot arise here. Checks performed:

1. **`energyTimeEmbedding` (A)** — TRUE. `spaceTimeL2L2ENormT T z = (∫_{Ioo 0 T}(eLpNorm(z(t))₂)²)^{½}`, `energyEssSupT T z = essSup_{Ioo 0 T}(eLpNorm(z(t))₂)`; `∫_{Ioo}h² ≤ (essSup h)²·volume(Ioo 0 T) = (essSup h)²·ofReal T`, and `((·)²·ofReal T)^{½} = essSup h · ofReal(√T)`. The `ℝ≥0∞` product is commutative, so A's `ofReal(√T)·energyEssSupT` is the paper's `T^{1/2}‖z‖_{L^∞_tL²}` (`:559`).
2. **`mixedRegionArithmetic` / `regionPositive`** — TRUE. `alpha p q = −3+3/p.toReal+2/q.toReal`, so `3/p+2/q>3 ⟺ 0<alpha p q`, and `0<alpha ⟹ 0<alpha+1`.
3. **`regionExamples`** — TRUE: `α(2,1)=−3+1.5+2=0.5>0`, `α(4/3,2)=−3+2.25+1=0.25>0`.
4. **`thresholdValue`** — TRUE: `criticalOrder 1 = 2−3/2 = 1/2`.
5. **`projectionOntoInitialData` (A)** — TRUE. `Prod.fst '' 𝔅 = {a∈𝓧 ∣ ∃f∈𝓕, T_max^ν(a,f)≤T}`; `⊇ = 𝓧` is `prop:density` applied at each `a` (any `g`, any radius). Genuine set equality, non-vacuous (`⊇` is the content).
6. **`zeroInitialProjection` (A)** — TRUE. `0∈initialClassT` (`ContDiff∞`, periodic, `div 0 = 0`), and `∃f∈𝓕, T_max^ν(0,f)≤T` (`prop:density` at `a=0`), so the fibre is nonempty and its image is `{0}`, not `∅`.
7. **`closureInEnergy` / `simultaneousPairConvergence` / `strongClosure`** — honest ∀∃ over registered `ClassicalSolutionT`; `SingularTrajectoryT` = `∃g∈𝓕, (∃ solution on horizon `T`), energyENormT T u ≠ ⊤, limsupLeft T (speedENorm∘u) = ⊤` faithfully renders `S_{a,T}` (smooth on `[0,T)`, finite `E_T`, unbounded speed at `T`).

**Provability notes (not falsities):** every regular-reference / closure field will be *provable* only once T18 (`PeriodicInsertionAPI`) is a registered contract the T19 proof can consume (see §4) — the same registration dependency T18 had on T15.

## 3. Decisions (binding for the finalization lane)

**Base per structure.** `PeriodicDensityAPI` → **B**; `MixedRegionAPI` → **B**; `StrongClosureAPI` → **A**; `ProjectionAPI` → **A**. One file `research/T19/Spec.lean`, namespace `BlowupDensity.T19`, four future contract ids (`T19.periodic_density`, `T19.mixed_region`, `T19.strong_closure`, `T19.projection`), four headline `def …Statement : Prop` in the paper's quantifier order.

**Sort.** All four `: Prop` (both drafts agree; none carries a distinguished constant/datum — every family is existential inside a field). This follows T24's data-free ruling (`AffineVariationAPI`/`ConservativeForcingAPI` are `Prop`). It diverges from the R41/R46 registry convention (those are `Type` though data-free) — owner question §4.

**The T18 insertion record: restate conclusions, do NOT thread.** T19 consumes `thm:insertion` as a black box (`:364-368`: "that theorem supplies `g_ε∈B` with lifespan exactly `T`; `eq:Hsclose→0`"); it never reasons about the packet/correction interior. So — exactly as R41/R46 restate insertion conclusions rather than reasoning inside them — the regular-reference and closure fields name the *conclusions* (`force ε∈forceClassT`, `maximalLifespanT = ofReal T`, the `ClassicalSolutionT`, the closeness limits) in registered torus vocabulary. Threading `PeriodicInsertionAPI` as a parameter is **rejected**: (i) it is not the T15↔T18 situation (there T18 manipulated T15's scaling identities; here T19 only consumes T18's outputs), and (ii) a registered `Contracts/V1` file may import only `Contracts.*`, so it cannot mention the unregistered `research/T18` record at all. R46 can `∃ (A : InsertionFamilyAPI …)` only because *whole-space* `InsertionFamilyAPI` is registered; the torus analogue is not — hence restatement, not record-production. Registration dependency flagged in §4.

**Density / closure spelling: ε-approximation, not topological closure.** `RelativelyDenseT` (density), `RelativelyDenseMixedT` (mixed density), `closureInEnergy` (ε-approx of `R⊆S̄^{E_T}`), `extendedProductDensity`, `regularReferenceSingular` — all "∀ r>0, ∃ witness with distance `< r`", and the simultaneous fields as `Tendsto … (𝓝[>]0) (𝓝 0)`. No `TopologicalSpace`/pseudometric instance on force or trajectory space (none registered); this is the repository convention (`RelativelyDenseT`/`RelativelyDense`).

**No honesty guards; no guard copies.** Every closeness is strict `< r` or `Tendsto … (𝓝 0)`, both self-guarding in `ℝ≥0∞` (R41/R46 carry none). **Drop** A's `MemForceSobolevT` guards (density/regular-reference) and A's `MemMixedLebesgueT` (mixed) — and therefore do **not** copy `MemMixedLebesgueT`/`MemForceSobolevT`. (This is *not* the T18 situation: T18 states per-`ε` two-sided rate **bounds** and chose to record the carrier for the proof; T19 states only density/limits.)

**`α(p,q)` spelling.** Registered `BlowupDensity.Contracts.V1.alpha` used directly (A). Drop B's `alphaT` copy and its drift `example`.

**`𝓧` topology in `prop:projection`.** Keep the initial datum fixed at `a` (topology-agnostic; `a` lies in every `𝓧`-neighborhood). No abstract `TopologicalSpace 𝓧` carrier; the `:586` non-density remark is not formalized (owner question §4).

**Copy policy (T18/T24 header convention).** One `research/T19/Spec.lean`, `import Contracts.V1.{TorusData,TorusLocalTheory,MainThresholds,CompletedDensity,Data,MaximalPartial,Correction}`. Everything registered (`ClassicalSolutionT`, `maximalLifespanT`, `RegularThroughT`, `breakdownSetT`, `RelativelyDenseT`, `forceClassT`, `initialClassT`, `forceSobolevENormT`, `energyENormT`, `energyEssSupT`, `criticalOrder`, `alpha`, `MaximalPartial.{limsupLeft,speedENorm}`) is imported, never copied. Copy **verbatim, in the historical namespace `BlowupDensity.T15.Draft` with the sync header** (B's approach) exactly two carriers: `IsPeriodicLebesgueSlicePath` and `mixedLebesgueENormT` (from `research/T18/Spec.lean:395-410`). No `alphaT`, no `MemMixed*`/`MemForceSobolev*`. The paper's own objects are restated over registered vocabulary as local defs (not copies of any record): `RegularTrajectoryT`, `SingularTrajectoryT`, `extendedBreakdownSetT`, `spaceTimeL2L2ENormT` (A), `RelativelyDenseMixedT` (B). No new constants.

**Field roster (binding).**
- `PeriodicDensityAPI : Prop` (3): `fixedInitialDensity` (both, verbatim); `thresholdValue : criticalOrder 1 = 1/2` (B); `regularReferenceSingular` (B — hypothesis `RegularThroughT ν a g T`, conclusion per-`(s,r)` `∃f∈𝓕, forceSobolevENormT 1 s (fun z=>f z−g z)<r ∧ maximalLifespanT ν a f = ofReal T`). Drop A's `alreadySingularApprox`, `regularReferenceApprox`.
- `MixedRegionAPI : Prop` (3): `mixedDensity` (B, `RelativelyDenseMixedT`); `mixedRegionArithmetic` (A's registered-`alpha` field); `regionExamples` (B, re-spelled `0<alpha 2 1 ∧ 0<alpha (4/3) 2`). Drop A's `alreadySingularMixedApprox`, `regularReferenceMixedApprox`.
- `StrongClosureAPI : Prop` (4): `energyTimeEmbedding` (A); `closureInEnergy` (A, with `RegularTrajectoryT`/`SingularTrajectoryT`); `simultaneousPairConvergence` (A, drop B's `history`); `referenceFiniteEnergy` (B).
- `ProjectionAPI : Prop` (3): `extendedProductDensity` (A, with `extendedBreakdownSetT`); `projectionOntoInitialData` (A, `Prod.fst '' 𝔅 = initialClassT`); `zeroInitialProjection` (A, `= {0}`). Drop B's operational `projectionOntoInitial`/`zeroInitialFiber` (their content is the `⊇` half of A's equalities).

**Citation hygiene.** Both drafts' docstrings cite the projection remarks at stale line numbers (`:582-585`, `:619-622`, `:625-631`); the current file has the `∀a∃f` order at `:579`, `{0}`-non-density at `:586`, the by-`T`/exactly-`T` distinction at `:590`, and `rem:peaks` at `:591`. The finalization lane must re-cite to the current `03-torus.tex`.

## 4. Next

**Proof dependencies the finalization proof will consume** (spec lane only writes the statement; recorded for the assembly lane):
- **`fixedInitialDensity` / `regularReferenceSingular`:** the dichotomy `le_or_lt (maximalLifespanT ν a g) (ofReal T)` (Mathlib); already-singular branch → `forceSobolevENormT 1 s 0 = 0 < r` (`eLpNorm` of the zero field); regular branch → T18 `PeriodicInsertionAPI.{lifespan (=ofReal T), force_mem, forceDifference_sobolev_bound (0≤s<1/2), forceDifference_negativeSobolev_tendsto (s<0)}`, with the reference solution from `RegularThroughT ν a g T` (T11 / registered `torusLocalTheoryAPI`).
- **`mixedDensity`:** T18 `PeriodicInsertionAPI.forceDifference_mixed_bound` (`≤ C(ε^{α}+ε^{α+1})`) + `mixedRegionArithmetic` (`α>0`, `α+1>0`) driving both terms to `0` along `𝓝[>]0`; already-singular branch as above with `mixedLebesgueENormT q p 0 = 0`.
- **`energyTimeEmbedding`:** pure Mathlib (`lintegral ≤ essSup · measure` on `Ioo 0 T`, then `rpow ½`); no Section 3 node.
- **`closureInEnergy` / `simultaneousPairConvergence`:** T18 `energyRate` (`E_T` limit), `lifespan`, `solution`, `blowup`/`blowup_limsup` (`SpeedUnboundedAt` / `limsupLeft … speedENorm = ⊤` ⟹ `SingularTrajectoryT`), `force_mem`, `forceDifference_sobolev_bound`/`_negativeSobolev_tendsto` (simultaneous `L¹_tH^s`); `energyENormT T (u ε) ≠ ⊤` from the reference's finite `E_T` + correction/packet finiteness (`:553`).
- **`referenceFiniteEnergy`:** continuity of `reference.velocity` on the compact `[0,T]×T³` ⟹ finite `energyEssSupT`/`energyGradientT`.
- **`prop:projection` (all three fields):** `PeriodicDensityAPI.fixedInitialDensity` applied at each `a` (the paper derives `prop:projection` from `prop:density`); `0 ∈ initialClassT` for `zeroInitialProjection`; the `⊆` half of both image equalities by definitional membership in `extendedBreakdownSetT`.
- **T20 not consumed** (feeds `cor:nondensity` = T21).

**Open questions for the owner:**
1. **Registration gap (both COMPARISONs flag it).** T18 (`PeriodicInsertionAPI`) + its T13/T15/T16/T17 chain are consumed by T19 but live only in `research/T18/Spec.lean`. T19 therefore restates `thm:insertion`'s conclusions in registered torus vocabulary (it cannot produce the T18 record the way R46 produces the registered `InsertionFamilyAPI`). Decide whether to **register the T18 torus insertion API before T19 assembly**; if registered, the T19 proof consumes it as a registered fact (mirroring R46). This is the direct analogue of T18's own open question about registering the T15 scaling chain.
2. **Sort.** `Prop` for all four (data-free, T24 precedent) vs the R41/R46 registry convention of `Type`. Confirm `Prop`, or align with the registered Section 4 twins as `Type`.
3. **`𝓧` topology.** `prop:projection`'s `:586` non-density remark (`{0}` not dense in a nontrivial normed `𝓧`) is not formalized — the paper keeps the `𝓧` topology generic and no registered `𝓧` topology exists. Confirm the omission, or add a normed-`𝓧` carrier (a new statement, owner's call).
4. **`rem:peaks` (`:591`).** The concentration/force-amplitude remark (`‖g_ε−g‖_{L^∞}→∞`) sits in the projection subsection but is not one of T19's four results. Confirm it is out of scope for the T19 contracts (or assign it as a separate remark-node).
5. **`regionExamples` spelling.** Confirm re-stating the `:538` illustration through the registered exponent at `ℝ≥0∞` points (`0 < alpha 2 1 ∧ 0 < alpha (4/3) 2`) rather than as disconnected real literals.
