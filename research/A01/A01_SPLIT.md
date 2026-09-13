# A01 — sub-lemma split table (lane 093, split-and-start)

Task **A01** ("Whole-space local solution adapter"), graph node
`formalization/blueprint/DEPENDENCY_GRAPH.md:172`, on the critical chain
`D01 → A01 → A02 → A04`.  This table decomposes the two `structure`s of the
draft contract `research/A01/Spec.lean` — `LocalTheoryAPI` (`:277-345`, four
fields) and `ManuscriptLocalRegularity` (`:167-240`, five fields, imposed on top
of `ClassicalSolutionR`) — into bounded, individually provable sub-lemmas.

It supersedes nothing in `research/A01/COMPARISON.md`; it reuses that memo's
unit names (E1, P1, …, X1) and adds the field-by-field `ClassicalSolutionR`
bridge (§c), the `exists_maximal` interface (§e) and the **U05 compile finding**
(below), which the earlier memo left as a blocker.

Size key (from COMPARISON.md §3): **S** ≤ ~100 lines, no new machinery; **M** a
self-contained lemma with a known proof; **L** a multi-file campaign.

Status column: **DONE** = proved and building this lane; **ready** = inputs
present, no blocker; **blocked** = named blocker.

---

## U05 re-verification — CLAUDE.md is stale (not a new result)

**U05 is already complete.**  It was done by lanes `004-U05-toolchain-probe`
(PR #8) and `010-U05-port` (PR #11, "88 模块全部编过"), recorded at
`PLAN.md:110,120,224` ("U05 已完成（HeliCorgi 已移植）"), and
`formalization/lakefile.toml:22` cites `research/U05/{REPORT,REVIEW,PORT}.md`.
It is **CLAUDE.md that is stale** (its line 80 still says "A01 还卡 U05"), not
the repo.  This lane's genuine contribution is (a) an independent reproduction,
(b) the enumeration of which roots are importable and which three are `unknown
target`, and (c) the mapping of that fact onto the A01 rows below.  With that
framing:

* `formalization/lakefile.toml:15-21` builds the HeliCorgi mild theory *in
  place* as the `Formal.*` library — the import closure (88 modules) of
  `R3EndpointSafeProjectedLocalExistence`, `R3NavierStokesEquation`,
  `R3HelmholtzPressure`, `R3MildContinuation` — **minus four modules that do not
  compile at 4.34.0-rc2**, which are maintained as byte-patched copies in the
  `FormalPatched` library (`lakefile.toml:116-121`):
  `R3RealLocalMildSolution`, `R3QuantitativeLifespan`,
  `EndpointSafeTwoSpaceUniqueness`, `R3MildContinuation`.
* **Verified this lane:** `lake build Formal.R3EndpointSafeProjectedLocalExistence`
  → `Build completed successfully (8830 jobs)`, exit 0, only style-linter
  warnings.  Oleans are present for `R3EndpointSafeProjectedLocalExistence`,
  `R3NavierStokesEquation`, `R3HelmholtzPressure`, `FlowMapLocalContDiff`,
  `R3LerayComplexFiberSymbol` (the last confirming lane 073).

**Consequence for A01:** the HeliCorgi existence / Duhamel / NS-equation /
Helmholtz-pressure edges (rows a1, E-pressure, B-semantics) are **importable
today** through `Formal.*`; the continuation + uniqueness edges (A2b) are
importable through `FormalPatched.*`.  No row below is blocked *by the toolchain*.
**This is not the same as "no row is blocked":** every HeliCorgi row lands on the
order-3 complex Bessel carrier, so consuming it inside A01 still needs the
carrier bridge **C1b/C1c** (both L, both gaps) — U05 removes the toolchain
blocker, not the carrier-bridge blocker.  See row A2b.

**Untested:** `Formal.MildSolutionSemantics`, `Formal.MildFlowMapBridge`,
`Formal.MildZeroUniqueness` are NOT in the four-seed closure and are not
registered roots (no olean); `lake build Formal.MildSolutionSemantics` →
`unknown target`.  Testing them needs a lakefile root addition (a config change,
out of this lane's scope).  They are not required by the existence/pressure
stack A01 uses.

---

## §a  What HeliCorgi/OpenAI supply, force-free / as-is

| # | sub-lemma (Lean-ready shape) | size | source (file:line) | status / blocker |
|---|---|---|---|---|
| a1 | HeliCorgi order-3 unforced mild existence: `∃ T, 0<T ∧ T≤1 ∧ ∃ u : ℝ → R3HsVelocity 3, IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u ∧ …` | — (imported) | `Formal/R3EndpointSafeProjectedLocalExistence.lean:35` `r3EndpointSafeProjected_exists_localMildSolution` | ready (olean present); complex Bessel coord, order pinned 3, **no forcing** |
| a2 | OpenAI/local forced mild existence, ordinary `R³` path: from `a : SmoothL2Field Space`, div-free, force path all-jets-cts, `∃ T∈(0,S]`, cylinder witness + ordinary `U : C(Icc 0 T, EulerMeanSolenoidal.L2)`, `U 0 = a.toLp`, forced mild eq | — (imported) | `Source/OrdinaryForcedLocal.lean:32` `exists_local` | ready; real, forced, **fixed order `q+1`, `q≥6`, `T` unquantified, no pointwise field, no pressure** |
| a3 | Strong `L²`-valued interior time derivative of that path `= adjoint(νΔu + P(f−(u·∇)u))` | — (imported) | `Source/OrdinaryForcedTime.lean:36,50` | ready; one interior derivative only |
| a4 | Helmholtz pressure for **arbitrary** `L²` source: `∂_j p = −((I−P)F)_j` in `𝓢'` | — (imported) | `Formal/R3HelmholtzPressure.lean:259` `r3HelmholtzPressure_gradient` | ready (olean present); complex `L²`, `𝓢'`-valued |
| a5 | HeliCorgi physical PDE capstone (unforced): momentum in `𝓢'` at `Ioo 0 T`, strong `L²` `∂ₜ` | — (imported) | `Formal/R3NavierStokesEquation.lean:142` `r3EndpointSafeProjectedMild_navierStokes` | ready (olean present); unforced, distributional |

**Gap common to §a:** none is a whole-space pointwise-classical forced field of
all Sobolev orders on one interval.  That is the content of §b–§c.

## §b  The force extension and the common all-order interval

| # | unit | Lean-ready statement | size | depends on | blocker |
|---|---|---|---|---|---|
| F1 | affine forcing in the Duhamel map | already `Coefficients.forcing` on OpenAI/local (`Euler/QuadraticCoefficients.lean:16`, instantiated `Source/ForcedCylinderLocal.lean:52` at `P(f−(u·∇)u)`) | S (OpenAI) / L (HeliCorgi: new field in `EndpointSafeTwoSpaceDuhamelContract`, `EndpointSafeTwoSpaceDuhamel.lean:407`) | — | none on OpenAI route |
| A1 | tame product `‖u⊗u‖_{Hᵏ} ≤ Cₖ‖u‖_{H²}‖u‖_{Hᵏ}` on the D01 carrier | `A03/OuterTameProduct.lean` `outerProductTame`, `advectionTame` | M | C1b | **A03's**, not A01; consumed here |
| A2 | high-order propagation `(‖u‖_{Hᵐ})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖_{Hᵐ}+‖f‖_{Hᵐ}`, `m≥3`, with `(‖·‖²+ζ²)^{1/2}` regularization | — | M | A1 | **gap; shared with A04** (`eq:Rhigh` `appendix-a:132-137`, `eq:highcontinuation` `:142-145`) — build once |
| A2b | order-`m` continuation (bounded trajectory extends) **+ cross-order agreement** | HeliCorgi has both at order 3: `FormalPatched/R3MildContinuation` `r3EndpointSafeProjected_exists_extension_of_bounded` (`:84`), `_blowup_dichotomy` (`:134`); unrestricted uniqueness `FormalPatched/EndpointSafeTwoSpaceUniqueness:222` | M (HeliCorgi spine) / **L** (recommended OpenAI spine) | A2, F1, A02.uniqueness | **toolchain ok** (all four `FormalPatched.*` build); but HeliCorgi's continuation lives on the order-3 complex Bessel carrier, so consuming it on the recommended OpenAI/local spine goes through **C1c** (L, gap) — the blocker moved from toolchain to carrier bridge. Euler/local layer has neither at any order |
| A3 | order-independent `T₀`: take budget `T` at lowest order (`H⁷` on OpenAI, `H³` on HeliCorgi), propagate all higher orders on that same `T₀` | — | **L** | A2, A2b, F1 | **gap**; does not touch `QuadraticHeatLocal.lean:32` |
| T1 | `C^j_tH^k_x` all `j,k`, one-sided at 0: `∂ₜu = νΔu + P(f−∇·(u⊗u)) ∈ C_tH^k`, induct | — | M | A3, E1 | **gap**; `appendix-a:71-76`; `Ico 0 T` is `UniqueDiffOn` ⇒ one-sided |

## §c  Semantic bridge: HeliCorgi/OpenAI solution → `A02.ClassicalSolutionR` (field by field)

Target structure `Section4/A02/SolutionClass.lean:114` `ClassicalSolutionR`
(9 fields).  `Source/SmoothLifespan.lean:23` `Flow` already shares the
velocity/pressure/`horizon_pos`/`velocity_smooth`/`pressure_smooth`/`initial`/
`divergence`/`equation`-core but **lacks `sobolev` and `pressure_gradient`** and
adds `energy`/`velocity_bound`/`derivative_bound`; and it is only ever built
*from an existing Flow*, never from data — so it does not shortcut assembly.

| # | `ClassicalSolutionR` field | Lean-ready obligation | size | inputs (file:line) | status / blocker |
|---|---|---|---|---|---|
| c1 | `velocity`, `pressure` | name the two fields of the produced solution | S | B1, P3 | via B1/P3 |
| c2 | `horizon_pos` | `0 < horizon ν a f` | S | A3 (`T₀>0`) | via A3 |
| c3 | `velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)` | joint space-time `C^∞` pointwise field from the `H^∞`-in-time path | **L** (=B1) | T1, A1, Sobolev embedding; **existing rungs**: `Paper1/PeriodicH3RepresentativeBridge.lean:24` `continuous_pointwise_representative` (joint (t,x) continuity of a cts `H³` path; `:83` one spatial derivative from `H⁴`), `Euler/SobolevPointEvaluation.lean:63` `pointEvaluation` (`H³→C⁰` bounded eval, cylinder), HeliCorgi `R3ClassicalIncompressibility.lean:58` `contDiff_one_r3PhysicalRepresentative` (`L²`-freq → pointwise `C¹`), `R3InversionConsistency.lean:139` `r3DecodedFrequency_incompressible_ae_decoder`; **torus precedent**: `Paper1/PeriodicLocalLifespan.lean:73` `ClassicalPeriodicLocalTheory` (same gap, left as a hypothesis, never proved) | **gap**; the hardest bridge. The rungs are C⁰/C¹, spatial-only or per-slice, order-pinned, some periodic/cylinder — no source produces joint all-order `C^∞`; but the next lane starts from them, not zero |
| c4 | `pressure_smooth` | as c3 for the pressure | M | P3, B1 | with P3/B1 |
| c5 | `initial : velocity (0,·) = a` | transport `U 0 = a.toLp` (`OrdinaryForcedLocal:32`) to pointwise `a` | S | C1b, B1 | via carrier bridge |
| c6 | `divergence : spatialDivergence velocity = 0` on `Ico 0 T` | transport the source's div-free clause (HeliCorgi route: `R3InversionConsistency.lean:139` `r3DecodedFrequency_incompressible_ae_decoder`) | S | B1, C1b | via carrier bridge |
| c7 | `momentum : navierStokesResidual ν velocity pressure = f` on `Ioo 0 T` | **from `projected` + `pressure_recovery` via E1** — see §d, `navierStokesResidual_eq_iff_projected` | S | **E1 (DONE)**, projected, pressure_recovery | E1 proved this lane; rest via §b/§d |
| c8 | `sobolev : ∀ m, ∃ G, ContinuousOn G ∧ IsSobolevDatum m (velocity t) (G t)` | the *continuous* order-`m` datum path (weaker than `sobolev_smooth`) | S | T1, C1b | weaker than `ManuscriptLocalRegularity.sobolev_smooth`; follows from it |
| c9 | `pressure_gradient : MemLp (∇p) 2 volume` on `Ico 0 T` | `∇p∈L²` clause | M | P3 | `appendix-a`/`02-prelim:101`; part of P3 |

D01 already bridges data/jets: `Section4/D01/Pressure.lean`, `D01/DatumToJets.lean`
(cited `research/A01/Spec.lean:58,66`) — `pressure_recovery`/`projected` on
`Ioo 0 T` is **D01 unit L9(c)** (`RECONCILIATION.md:160`); A01's genuine
increment is the `t=0` endpoint and the `Ico`-wide statement.

### `ManuscriptLocalRegularity` fields (the four clauses beyond `ClassicalSolutionR`)

| # | field (`Spec.lean`) | unit | size | status / blocker |
|---|---|---|---|---|
| m1 | `sobolev_smooth` (`:180`): all-order `ContDiffOn ℝ ∞ G (Ico 0 T)` datum path | T1+B1 | L | **gap** (the all-order time smoothness) |
| m2 | `pressure_recovery` (`:197`): `IsLerayComplement (f−∇·(u⊗u)) (∇p)` on `Ico 0 T` | P2, P3 | M | P2 needs Liouville for `L²`-harmonic (gap); P3 imports a4 |
| m3 | `projected` (`:214`): `∂ₜu − νΔu = (f − ∇·(u⊗u)) − ∇p` on `Ioo 0 T` | **DONE — a theorem** `projected_of_classicalSolution` (`Section4/A01/ProjectedEquation.lean`) | — | **no separate obligation**: reducible to c7/B2 (producing the `ClassicalSolutionR`). E1 + `velocity_smooth`/`divergence`/`momentum` discharge it outright |
| m4 | `pressure_potential` (`:227`): gauge-equiv to the radial potential `∫₀¹ G(rx)·x dr` | **P1 DONE (lane 101)** — pointwise `∇(radial potential)=G` (`Section4/A01/RadialPotential.lean`, `hasFDerivAt_radialPotential` + `pressureGradient_pressurePotential`); gauge wrapping ~90 lines left, **all S** | S | `02-prelim:98-100`; pointwise core done. Wrapping = "equal gradients on connected ℝ³ differ by a constant of time": lane-101 reviewer wrote+compiled **52 lines** (`is_const_of_fderiv_eq_zero` + 15-line "`pressureGradient` determines the slice `fderiv`" helper) with standard axioms, plus **14 lines** of slice smoothness straight from `pressure_smooth` (the `t=0` endpoint is *not* an obstacle), leaving **~25 lines** of Hessian symmetry via `ContDiffAt.isSymmSndFDerivAt`. **Recommended next A01 lane** (retires D01 L9(b)). |

Supporting characterization units (from `Spec.lean` §1 defs):
`E1` **DONE**; `P1` **DONE (lane 101)** — radial potential has gradient `G`; `P2`
(`IsLerayComplement` single-valued, needs `Differentiable`) M — Liouville gap;
`C1a` (=D01 L2) M; `C1b`/`C1c` (Fourier-convention bridges) **L**;
`P3` (physical eq:Rpressure) M.

## §d  `horizon_lower_bound`

| # | field | Lean-ready statement (`Spec.lean:338`) | size | inputs | blocker |
|---|---|---|---|---|---|
| H1 | `horizon_lower_bound` | `∀ ν>0, ∀ K≠⊤, ∃ δ>0, ∀ a f, a∈X_R → f∈F_R → ‖a‖_{H¹}≤K → ‖f‖_{L¹H¹}≤K → δ ≤ horizon ν a f` (norms = `sobolevENorm 1`, `forceSobolevENormL1 1`) | M (conditional on A3's size) | A3 | **gap**; `appendix-a:147-152`, quantitative source Tao 5.4(ii) eq.(46) rescaled by `:79-87`; **consumed by A02's own unproved `restart` field** (see §e) and, through it, A04's continuation |

`exists_positive_time_budget` (`Euler/VolterraUniqueness.lean:69`) gives **no
handle on `T`** (`REVIEW.md` H1), so H1 must come from the A3 propagation, not
be read off the source.  The quantifier order — `δ` chosen *before* `(a,f)` — is
exactly what A02's `restart` docstring (`research/A02/Spec.lean:551`) calls "the
whole point"; H1 is therefore an A02 dependency, not only an A04 one.

## §e  What A02's `exists_maximal` needs from A01 (exact interface)

A02 is **already discharged conditionally** on A01's `solution` clause.  The
partial contract `verification/Contracts/V1/MaximalPartial.lean` and
`Section4/A02/Maximal.lean` prove:

* `exists_maximal_of_localSolution`, `horizon_le_lifespan_of_localSolution`
  (`Maximal.lean:22-29`, `Order.lean`): take the A01 clause
  `∀ ν a f, 0<ν → a∈initialClassR → MemForceR f → ClassicalSolutionR ν a f (horizon ν a f)`
  as an **explicit hypothesis** and conclude `0 < maximalLifespanR`,
  `ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanR ν a f`
  (`MaximalPartial.lean:154-162`).

So for `exists_maximal` / `horizon_le_lifespan` the **only thing A02 needs from
A01** is inhabitation of that clause — i.e. the `LocalTheoryAPI.solution` field
itself (`Spec.lean:297-299`): build **one** `ClassicalSolutionR ν a f
(horizon ν a f)` from data for every manuscript datum.  That is unit **X1**
(package) sitting atop **B2** (assemble the structure) atop **B1/T1/A3/P3** — the
whole §b–§c spine.  (`A02` `patch`, `pressure_normalization`, `restrict`-shorten
are A02-internal and already proved.)

**But A02 has a second, still-unproved field that consumes A01:** `restart`
(`research/A02/Spec.lean:551`), whose docstring says the quantifier order is
"A01's `horizonLowerBound` quantifier order … the whole point".  So `restart`
needs unit **H1** (`horizon_lower_bound`), plus `A02.uniqueness` and `A02.patch`.
`NEXT_SESSION.md` independently records "A02 只剩 `restart*` / `insertion_lifespan_eq`".

| # | A01 unit → A02 field | Lean-ready obligation | size | depends on | blocker |
|---|---|---|---|---|---|
| B2 | `LocalTheoryAPI.solution` → `A02.exists_maximal`, `horizon_le_lifespan` | assemble `ClassicalSolutionR` from the bridged fields c1–c9 | S (likely M, per reviewer) | B1, E1, P3 | field-by-field; E1 done |
| X1 | `LocalTheoryAPI` → the above | package: choose `horizon`, `solution` as functions of `(ν,a,f)`; `regularity`, `horizon_lower_bound` | S | B2, P1, P3, T1, H1 | choice over A3's existential |
| H1 | `LocalTheoryAPI.horizon_lower_bound` → **`A02.restart`** and A04's continuation | see §d | M (conditional) | A3 | **gap**; quantifier order is `restart`'s "whole point" |

---

## Totals and critical path

Reusing COMPARISON.md §3, and counting only units **A01 owns** (A1 is A03's,
C1a is D01's — both shown below marked *(other task)* and excluded from the
total):

* **S** (3): E1 **DONE**, B2, X1
* **M** (6): P1, P2, A2, A2b, P3, T1, H1  — plus C1a *(other task, =D01 L2)*
* **L** (4): C1b, C1c, A3, B1
* **F1** (its own class): free on the OpenAI/local spine (already
  `Coefficients.forcing`), **L** on the HeliCorgi spine (new field in
  `EndpointSafeTwoSpaceDuhamelContract`)

**A01 owns 13 = 3 S + 6 M + 4 L**, with F1 a route-dependent extra (free or L)
and A1/C1a attributed to A03/D01.  (m3 is no longer a unit: it became the theorem
`projected_of_classicalSolution` this lane.)

**Single biggest blocker:** unit **B1/c3** — turning the family of `H^m`-valued
time paths into one jointly space-time `C^∞` pointwise field
(`ClassicalSolutionR.velocity_smooth`), which no source produces; it rests on
**A3** (order-independent `T₀`) and **A2/A2b** (the shared-with-A04 Grönwall
bootstrap + continuation).  These three L-units are essentially all of A01.

**Order of work (recommended, OpenAI/local spine + HeliCorgi pressure):**
F1 (free) → C1a+C1b → A1←A03, A2, A2b, A3, T1, B1, B2, with P1/P2/P3 and H1 in
parallel, X1 last.  **E1 (this lane) is the one S-unit with enough slack to run
first: it is an input to T1/c7 (and was the calculus behind m3), but never the
binding constraint — its successors are all gated by the L-units above.**

## First S item proved this lane

Unit **E1**, module
`formalization/NSFormalization/Section4/A01/ConvectionDivergence.lean`:

* `convectionDivergence` — the tensor divergence `∇·(u⊗u)`, verbatim from
  `Spec.lean:103-105` (A01 owns it; absent from `formalization/` before).
* `convectionDivergence_eq_advection_add_smul_div` — Leibniz:
  `∇·(u⊗u) = (u·∇)u + (∇·u) • u` for `u` differentiable in space at `(t,x)`.
* `convectionDivergence_eq_advection` — divergence-free specialization.
* `navierStokesResidual_eq_iff_projected` — the payoff: `momentum` form ⟺
  `projected` form at a differentiable div-free point.

Reviewer harvest, sibling module
`formalization/NSFormalization/Section4/A01/ProjectedEquation.lean`
(`research/A01/REVIEW_SPLIT.md` Finding 3):

* `projected_of_classicalSolution` — `ManuscriptLocalRegularity.projected` is a
  **theorem about every `ClassicalSolutionR`** (from `velocity_smooth`,
  `divergence`, `momentum` + `navierStokesResidual_eq_iff_projected`), so m3 is
  no longer a separate obligation.

All five declarations `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
