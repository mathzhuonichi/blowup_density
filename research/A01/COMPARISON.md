# A01 — source-to-target comparison, adapter edges, implementation split, strategy

Lane 013, task **A01** ("Whole-space local solution adapter"), 2026-09-13.
Target contract: [`Spec.lean`](Spec.lean), namespace `BlowupDensity.A01.Draft`.
Manuscript object: the **existence half** of `prop:local`
(`paper/sections/02-preliminaries.tex:105`), derived in
`paper/sections/appendix-a-local-theory.tex:60-107` from Tao 2013
Theorem 5.4(ii)–(iv) (`reference/Tao_2013_Localisation_Compactness_Published.pdf`,
published pp. 52–53).

Everything quantified over is the canonical D01 object of
`verification/Contracts/V1/Data.lean` (`research/D01/PAPER_TO_LEAN.md`).
Uniqueness is A02, the continuation criterion is A04; neither is stated here.

**Revision 2**, after [`REVIEW.md`](REVIEW.md) (verdict ACCEPT-WITH-NOTES).
Changed: the order-uniformity claim about the OpenAI horizon (H1), the sizes of
C1b/A3/B1 and hence the route comparison (H3), a new unit A2b (M1), the
`SmoothLifespan.Flow` row (M2), all `appendix-a-local-theory.tex` citations
(M3, the committed block `60-107` is ≈14 lines earlier than revision 1 said),
and the low-level items L1–L8.  P2's statement was under-specified (H2); the
fix landed in `Spec.lean` (`HasSymmetricJacobian` now carries
`Differentiable ℝ G`) and the unit is restated below.  Every source
`file:line` in this revision was re-opened.

---

## 0. What the target actually demands

Tao Theorem 5.4, as printed:

| clause | printed content |
|---|---|
| (ii) | `‖u₀‖_{H¹} + ‖f‖_{L¹_tH¹}` small compared with `T^{-1/4}` gives an `H¹` **mild** solution with `‖u‖_{X¹} ≲ ‖u₀‖_{H¹}+‖f‖_{L¹_tH¹}`, **and more generally** `‖u‖_{X^k} ≲_{k,‖u₀‖_{H^k},‖f‖_{L¹_tH^k},1}` for each `k ≥ 1` — i.e. every order on the **same** `T` |
| (iii) | at most one `H¹` mild solution |
| (iv) | for Schwartz data `u` and `p` are smooth, `∂ₜ^ju, ∂ₜ^jp ∈ L^∞_tH^k` for all `j,k`; the proof's closing parenthesis says `u₀ ∈ H^k` and `f ∈ C^j_tH^k` suffice, Schwartz is not needed |

The manuscript's own additions on top of that (`appendix-a-local-theory.tex`):
viscosity `ν` by parabolic rescaling (`:79-87`), the projected formulation with
force `P f` (`:76-77`), pressure by `eq:Rpressure` + the radial potential
(`02-preliminaries.tex:90-100`), and the mild equation `eq:mild` (`:109-114`)
used only to reach uniqueness and restart.  The load-bearing sentence for
component (A) below is `:66-67`, "The higher-order bounds in part (ii) hold on
the same local interval for every order"; the `C^j_tH^k_x` induction is
`:71-76`; the restart uniformity A04 consumes is `:147-150`.

So the A01 deliverable has five irreducible components: **(A)** one positive
`T₀` independent of the Sobolev order; **(B)** an ordinary real physical field
on `R³`, classically smooth on `[0,T₀) × R³`; **(C)** `C^j_tH^k_x` for all
`j,k` with one-sided `t = 0` derivatives; **(D)** the projected equation with
affine forcing; **(E)** the pressure gradient and its radial potential.

---

## 1. Three-source table

### 1.1 HeliCorgi (`vendor/HeliCorgi/Formal/`, namespace `MNS2`)

Importable at this pin as `Formal.*` — **84 explicitly listed roots** in
`formalization/lakefile.toml`, built in place from `vendor/HeliCorgi` — and
`FormalPatched.*` (4 patched copies: `R3RealLocalMildSolution`,
`R3QuantitativeLifespan`, `EndpointSafeTwoSpaceUniqueness`,
`R3MildContinuation`), per `research/U05/PORT.md`;
`formalization/NSFormalization/Section4/HeliCorgiPort.lean` is the smoke module.
The roots list is *not* a glob, so anything absent from it is **not importable
today**: in particular `Formal.R3SchwartzInitialData` and
`Formal.R3DecodedVelocityRealness` are absent (the former imports the
non-compiling `Formal.R3MildContinuation`, so porting it means a fifth patched
copy), and `EndpointSafeTwoSpaceUniqueness` is reachable only through
`FormalPatched`.  Rows below are marked accordingly.

| declaration | file:line | space / carrier | order | forced? | interval | field type | real/complex |
|---|---|---|---|---|---|---|---|
| `r3EndpointSafeProjected_exists_localMildSolution` | `R3EndpointSafeProjectedLocalExistence.lean:35` | `R3HsVelocity 3` `= R3L2Velocity = Lp R3C 2 volume` (`R3SobolevCarrier.lean:29`, `R3StokesL2Operator.lean:22`) | exactly **3** (fixed) | **no** | `∃ T, 0 < T ∧ T ≤ 1`, trajectory on `Icc 0 T`, closed-ball uniqueness at radius `‖u₀‖+1` | Bessel **coordinate** `J³u ∈ L²`; the physical field is `J⁻³` of it | **complex** (`R3C = EuclideanSpace ℂ (Fin 3)`) |
| `IsR3EndpointSafeProjectedMildSolutionOn` / `r3EndpointSafeProjectedMild_equation_at_time` | `R3EndpointSafeProjectedDuhamel.lean:156`, `:163` | same | 3 (→ 2 for the source) | **no** | `u t = S(t)u₀ − ∫₀^t K(t,s)P(u⊗u)(s)` | coordinate | complex |
| `r3EndpointSafeProjectedDuhamelContract` | `R3EndpointSafeProjectedDuhamel.lean:20` | instance of `EndpointSafeTwoSpaceDuhamelContract` (`EndpointSafeTwoSpaceDuhamel.lean:407`) | — | **no forcing field exists**: the contract's only source is `bilinear : X →L X →L Y` (`:427`) | — | — | — |
| `r3EndpointSafeProjectedMild_navierStokes` | `R3NavierStokesEquation.lean:142` | decoded `r3H3ToL2Operator (u t) : R3L2Velocity` (`R3StokesH2H3Smoothing.lean:294`) | 3 | **no** | interior times `Ioo 0 T` | strong `L²`-valued `∂ₜ`; momentum **componentwise in `𝓢'`**, divergence distributional | complex |
| `r3AdmissibleSchwartzDatum_navierStokes` **(not ported — module absent from the 84 roots)** | `R3SchwartzInitialData.lean:233` | same, entered from `φ : R3SchwartzVelocity`, real + divergence free (`:77`) | 3 | **no** | `Icc 0 T` for realness, **`∀ t`** for the energy clause, `Ioo 0 T` for the equation | decoded physical `L²`, `U 0 = φ.toLp` | decoded field **is** real here, via `r3EndpointSafeProjectedMild_isR3RealVelocity_decoded` (`R3DecodedVelocityRealness.lean:71`, also not ported); `R3SchwartzInitialData.lean:194` is realness of the **encoded** coordinate |
| `r3HelmholtzPressure` / `r3HelmholtzPressure_gradient` | `R3HelmholtzPressure.lean:223`, `:259` | arbitrary `F : R3L2Velocity` | — | source is **arbitrary**, so nonzero forcing is already allowed | — | `∂_j p = −((I−P)F)_j` in `𝓢'` | complex |
| `r3EndpointSafeProjected_exists_extension_of_bounded`, `r3EndpointSafeProjected_blowup_dichotomy` **(`FormalPatched` only)** | `R3MildContinuation.lean:84`, `:134` (patched copy `formalization/FormalPatched/R3MildContinuation.lean`) | coordinate | 3 | no | extension by an explicit `r3MildLifespan ν R`; **this is the only continuation layer in tree** (see unit A2b) | — | complex |
| `r3EndpointSafeProjectedMildSolution_unique` **(`FormalPatched` only)** | `EndpointSafeTwoSpaceUniqueness.lean:222` | coordinate | 3 | no | unrestricted — no ball, no realness, no smallness | — | complex |
| `r3LerayL2Operator` | `R3LerayL2Operator.lean:28` | `R3L2Velocity` | — | — | — | **`r3L2SolenoidalSubmodule.starProjection`**, *not* a bundled symbol: the file docstring (`:24-26`) says the identification is intentionally unbundled.  Symbol: `r3LeraySymbolComplex_apply` (`R3LerayComplexFiberSymbol.lean:114`); a.e. identification: `fourier_r3LerayL2Operator_ae` (`R3LerayPointwiseProjectionIdentification.lean:97`) | complex |

**Distance to `prop:local`:** four of the five components are missing. No
forcing anywhere in the Picard layer (D); order pinned at 3, so no common
all-order interval (A); the equation is `𝓢'`-valued in space with a strong
`L²` time derivative, never a pointwise classical field (B, C); realness of
the decoded field only via the Schwartz entry point, which is not ported.
What it *does* supply, and nothing else in tree does, is (i) the concrete `R³`
Leray/Stokes/Helmholtz operator stack with a pressure theorem already valid for
an arbitrary `L²` source (E) and (ii) a **continuation layer** (extension of a
norm-bounded trajectory, blow-up dichotomy) — see unit **A2b**, which the
persistence bootstrap needs and the Euler/local layer does not have.

One structural fact that matters for costing the pressure edge:
`R3HsVelocity` is **order-erasing** — `abbrev R3HsVelocity (_s : ℝ) :=
R3L2Velocity` (`R3SobolevCarrier.lean:29`) — so `r3LerayComplementL2` and
`r3HelmholtzPressure` act on plain complex `L²`, with no Bessel order in sight.
Importing the pressure therefore needs a real-`L²` ↪ complex-`L²` embedding and
a `𝓢'`→pointwise transport, **not** the angular↔Bessel Sobolev bridge (unit
C1c).  That bridge is needed only for the *velocity*.

### 1.2 OpenAI (`vendor/NavierStokesAndEuler/`, `Euler*` namespaces)

| declaration | file:line | space / carrier | order | forced? | interval | field type | real/complex |
|---|---|---|---|---|---|---|---|
| `EulerQuadraticSource.quadraticDuhamel` | `Euler/QuadraticHeatLocal.lean:23` | `SobolevSpace period (q+1)` `= sobolevSubspace period (q+1)` (`Euler/CylinderSobolevSpace.lean:49`), a closed submodule of derivative-word arrays in `LiftL2 period` over the **cylinder** `LiftDomain period = Vector3 × AddCircle period` (`Euler/EulerProof.lean:1085`) | `q+1`, `q` fixed | **yes** — `heatOperator …u₀ + ∫₀^t heatKernel … (C.apply …)` with `C.forcing` affine | `Icc 0 T` | Hilbert-space-valued path, physical-side coordinates (no Fourier coordinate) | **real** |
| `Coefficients` (with `forcing : C(T,Y)`) | `Euler/QuadraticCoefficients.lean:16` | — | — | **the affine forcing edge already exists here** | — | — | real |
| `EulerQuadraticSource.exists_local_quadratic_mild` | `Euler/QuadraticHeatLocal.lean:32` | as above | `q+1` | yes | `∃ T, 0 < T ∧ T ≤ S`, `‖u‖ ≤ ‖u₀‖+1` | continuous path | real |
| `EulerQuadraticSource.exists_local_quadratic_divergenceFree` | `Euler/QuadraticHeatConstraint.lean:19` | as above | `q+1` | yes | as above | adds `value (u t) ∈ divergenceFreeSpace period κ m`; parametrized by `(κ, m)` and requires **two** `gradientProjection … = 0` hypotheses (on `u₀` and on every source value) | real |
| `EulerSobolevHeat.exists_positive_time_budget` | `Euler/VolterraUniqueness.lean:69` (namespace opens at `:54`) | — | — | — | produces the `T` above from `C.ballBound R`, `C.ballLipschitz R`; **purely existential** — an `ε`-style witness from continuity at `0` of `T ↦ (T + 2·parabolicConstant ν·√T)·M`, with no formula and no monotonicity claim | — | — |
| `Coefficients.ballBound` | `Euler/QuadraticCoefficients.lean:47` | `‖P‖(‖forcing‖ + ‖linear‖R + ‖quadratic‖R²)`, `R = ‖u₀‖+1` | — | — | — | — | — |

**Distance to `prop:local`:** forcing (D) is free. But the carrier is a
**cylinder** `R³ × S¹`, and the order is fixed.

*On the horizon, stated precisely (revision 2, `REVIEW.md` H1).*  `T` is an
**existential witness** constrained by `ballBound R` and `ballLipschitz R` with
`R = ‖u₀‖_{H^{q+1}} + 1`; `exists_positive_time_budget`
(`Euler/VolterraUniqueness.lean:69`) gives no formula for it and proves no
monotonicity in `M`, `L`, `R` or `q`, and a cross-order comparison is not even
type-correct — `u₀`, `C.linear` and `C.quadratic` live in different spaces for
different `q`. Revision 1 said `T` "provably shrinks in `q`" and that
order-uniformity "is false of the quoted `T`"; **both were overclaims** — a
purely existential theorem cannot make uniformity false. The correct statement
is: **uniformity in `q` is not proved, and the theorem offers no handle on `T`
with which to prove it.** That is what unit A3 has to supply. No pressure, no
classical field, no `𝓢'`/Fourier identification with the D01 datum.

### 1.3 Local `Source` (`formalization/NSFormalization/Source/`)

| declaration | file:line | what it literally gives |
|---|---|---|
| `ForcedCylinderLocal.leray` | `ForcedCylinderLocal.lean:26` | `id − sobolevGradientProjection`, the cylinder Leray projection as a CLM on `SobolevSpace period q`; the gradient part is *discarded*, never reconstructed as a pressure |
| `ForcedCylinderLocal.coefficients` | `:52` | `Coefficients` with `forcing := −f`, `linear := 0`, `quadratic := advection`, `projection := leray` — i.e. the source `P(f − (u·∇)u)` |
| `ForcedCylinderLocal.exists_local_forced_mild` | `:72` | for `q ≥ 6`, `ν,S > 0`, `u₀ : SobolevSpace period (q+1)` with divergence-free value, `f : C(Icc 0 S, SobolevSpace period q)`: `∃ T ∈ (0,S]` and `u : C(Icc 0 T, SobolevSpace period (q+1))` with `‖u‖ ≤ ‖u₀‖+1`, `u 0 = u₀`, divergence free at every `t`, and the forced Duhamel identity. **Cylinder, fixed order, real, no pressure.** |
| `exists_local_forced_mild_invariant` — namespace `NSFormalization.Source.ForcedCylinderLocal`, **not** `…ForcedCylinderInvariant` (`ForcedCylinderInvariant.lean:6`) | `ForcedCylinderInvariant.lean:30` | the same, plus invariance under every angle translation — but it *requires* angle invariance of `u₀` and of every `f t` as hypotheses |
| `OrdinaryCylinderDescent.ordinaryValue`, `ordinaryValue_lift` | `OrdinaryCylinderDescent.lean:56`, `:60` | the adjoint that turns an angle-invariant cylinder element back into an ordinary `EulerMeanSolenoidal.L2` field (`Euler/MeanSolenoidalSpace.lean:22`, `Lp Space 2 volume`); `ordinaryValue_lift` needs `hq : 3 ≤ q` |
| **`OrdinaryForcedLocal.exists_local`** | `OrdinaryForcedLocal.lean:32` | **the closest thing in tree.** From `a : SmoothL2Field Space` (`Euler/LpSmoothField.lean:31`: a genuinely smooth field all of whose jets are `L²`) with classical `divergence a = 0`, and a force path `F : Icc 0 S → SmoothL2Field Space` with all jets continuous in time: `∃ T ∈ (0,S]`, a cylinder witness `u : C(Icc 0 T, SobolevSpace 1 (q+1))` and an **ordinary whole-space** path `U : C(Icc 0 T, EulerMeanSolenoidal.L2)` with `U 0 = a.toLp`, `ordinaryLift (U t) = value 1 (u t)`, divergence free, satisfying the forced mild equation, angle invariant. Real, physical `L²`, **fixed order `q+1` with `q ≥ 6`, `T` unquantified (see §1.2 on the horizon), no pointwise field, no pressure, no `H^m` for all `m`, no time smoothness.** |
| `OrdinaryForcedTime.ordinary_hasDerivAt`, `realization_hasDerivAt` | `OrdinaryForcedTime.lean:36`, `:50` | strong `L²`-valued time derivative of that ordinary path at interior times, equal to `adjoint(νΔu + P(f − (u·∇)u))` |
| `OrdinaryViscousUniqueness.velocity_unique` | `OrdinaryViscousUniqueness.lean:26` | uniqueness for two classical `SmoothL2Field`-valued solutions with the same force and datum — **A02's**, listed here because it fixes the physical shape A01's output must have |
| `SmoothLifespan.Flow` | `SmoothLifespan.lean:23` | the **same velocity/pressure/smoothness/equation core** as `ClassicalSolutionR` (`Data.lean:617`): `velocity`, `pressure`, `horizon_pos`, `ContDiffOn ℝ ∞ … (Ico 0 S ×ˢ univ)`, `initial`, `divergence`, `equation` on `Ioo 0 S`. It **lacks** `sobolev` and `pressure_gradient` — precisely components (C) and (E) that A01 must add — and instead carries `energy`, `velocity_bound`, `derivative_bound`, which `ClassicalSolutionR` does not. Two constructors exist, `Flow.restrict` (`:83`) and `insertionFlow` (`:218`, consumed at `Source/InsertionBreakdown.lean:75`), but **both consume an existing `Flow`**: nothing in tree builds one *from data*, which is exactly the A01 gap. `lifespan` (`:41`) is syntactically the same supremum as `maximalLifespanR` (`Data.lean:650`). |

**Distance to `prop:local`:** the descent to ordinary `R³` (half of B) and the
affine forcing (D) are done. (A), (C), (E) and the pointwise-classical half of
(B) are open.

### 1.4 One-line summary

| component | HeliCorgi | OpenAI | local `Source` |
|---|---|---|---|
| (A) order-independent `T₀` | order fixed at 3 | `T` existential, **uniformity in `q` unproved and unreachable from the statement** | inherits OpenAI's `T` |
| (B) ordinary real physical field | complex coordinate, `𝓢'` equation | real, but on the cylinder | real ordinary `L²` path; **not pointwise classical** |
| (C) `C^j_tH^k_x`, one-sided at 0 | one interior `L²` derivative | continuity only | one interior `L²` derivative |
| (D) affine forcing | **absent from the contract itself** | **present** (`Coefficients.forcing`) | **present and already projected** |
| (E) pressure gradient + potential | **present** for arbitrary `L²` source, in `𝓢'` | absent (gradient discarded) | absent (gradient discarded) |

---

## 2. The adapter edges the paper needs

| # | edge | manuscript locus | closest source | what is missing |
|---|---|---|---|---|
| **D** | affine forcing inside the Duhamel map | `appendix-a:76-77`, `eq:mild` `:109-114` | local `Source/ForcedCylinderLocal.coefficients:52` (`forcing := −f`), resting on `Euler/QuadraticCoefficients.lean:16` | nothing on the OpenAI/local side; on the HeliCorgi side the *structure* `EndpointSafeTwoSpaceDuhamelContract` (`:407`) has no forcing field, so adding it means a new field, a new integrand branch, a new majorant clause and re-running `exists_pos_time_isMildSolutionOn` (`EndpointSafeTwoSpacePicard.lean:887`) |
| **A** | one interval for all Sobolev orders | `02-prelim:117`, `appendix-a:66-67`, Tao 5.4(ii) "more generally" | **none.** OpenAI's `T` is the unquantified existential of `exists_positive_time_budget ν (ballBound R) (ballLipschitz R) 1 S` with `R = ‖u₀‖_{H^{q+1}}+1` (`QuadraticHeatConstraint.lean:19` → `QuadraticHeatLocal.lean:32` → `VolterraUniqueness.lean:69`): uniformity in the order is neither proved nor refutable from the statement | the persistence-of-regularity bootstrap: fix `T₀` at the lowest available order, then propagate every higher `H^m` bound on that same `T₀` by the tame product `eq:tame` `‖u⊗u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}` (`appendix-a:9-13` eq:Rproduct, `:15-19` eq:tame, **A03**) plus Grönwall. The Grönwall is *the same* `eq:Rhigh` (`appendix-a:132-137`) / `eq:highcontinuation` (`:142-145`) that **A04** needs — build once, share. The bootstrap additionally needs an order-`m` continuation criterion and cross-order agreement, unit **A2b** |
| **C** | `C^j_tH^k_x` for all `j,k`, one-sided at `t = 0` | `appendix-a:71-76`, Tao 5.4(iv) | continuity only (`C(Icc 0 T, …)` everywhere); one interior strong `L²` derivative from `OrdinaryForcedTime.lean:36` or `R3NavierStokesEquation.lean:142` | the appendix's own induction: the equation has a continuous right-hand side in every `H^k`, so `∂ₜu ∈ C_tH^k`; differentiate repeatedly. Needs (A) first, and `Ico 0 T`-relative (one-sided) derivatives, which no source states |
| **B** | identification of the decoded field with a `ClassicalSolutionR` | `02-prelim:28-36`, `Data.lean:617` | `SmoothLifespan.Flow` (`:23`) has the same velocity/pressure/equation core but lacks `sobolev` and `pressure_gradient`, and is never built from data; `OrdinaryForcedLocal.exists_local:32` produces the ordinary `L²` path | three sub-gaps: (i) `L²`-valued path → pointwise `ContDiffOn ℝ ∞` field on `Ico 0 T ×ˢ univ` (all-order Sobolev embedding, needs (A)); (ii) carrier translation between D01's angular datum `IsSobolevDatum` (`Data.lean:160`, unitary `(2π)^{-3/2}` convention) and the source coordinates — Euler `ordinarySobolev` (`Euler/MeanOrbitSobolev.lean:71`) / HeliCorgi's Bessel `R3HsVelocity` under its own `𝓕`; (iii) complex→real if the HeliCorgi route is used |
| **E** | pressure gradient `eq:Rpressure` and the radial potential | `02-prelim:90`, `:96-100` | HeliCorgi `r3HelmholtzPressure_gradient` (`R3HelmholtzPressure.lean:259`) — already for an **arbitrary** `L²` source, so instantiating at `F = ∇·(u⊗u) − f` needs no new analysis, and since `R3HsVelocity` erases its order the operators involved are plain complex `L²` | transport from `𝓢'`-componentwise to the physical `pressureGradient` of `Data.lean`; a real-`L²` ↪ complex-`L²` embedding; the `∇p ∈ L²` clause; the sign/normalization; and the radial-potential identity (self-contained, `02-prelim:98-100`). **Overlap:** on `Ioo 0 T` this is D01 unit **L9(c)** (`RECONCILIATION.md:160`), which already cites the same two HeliCorgi declarations; A01's genuine increment is the `t = 0` endpoint and the `Ico`-wide statement |
| **L** | the Leray projection itself | `02-prelim:76-79` | HeliCorgi `r3LerayL2Operator` (`R3LerayL2Operator.lean:28`) is `r3L2SolenoidalSubmodule.starProjection`, **not** a bundled symbol — its docstring (`:24-26`) says the identification is intentionally unbundled; the symbol is `r3LeraySymbolComplex_apply` (`R3LerayComplexFiberSymbol.lean:114`) and the a.e. identification is `fourier_r3LerayL2Operator_ae` (`R3LerayPointwiseProjectionIdentification.lean:97`). Local `ForcedCylinderLocal.leray:26` is the cylinder gradient complement | `Spec.lean` states `P` by the Helmholtz characterization `IsLerayComplement`, so the contract needs no operator. Identifying that characterization with either in-tree operator is a *consumer-side* obligation (unit **P3**), not a hypothesis; on the HeliCorgi side P3 must chain through the two extra modules just named, since the projection itself carries no symbol |
| **N** | `∇·(u⊗u)` vs `(u·∇)u` | `eq:projected` `02-prelim:81` vs `Data.lean` `momentum` (upstream `advection`) | — | one-line calculus for divergence-free smooth `u` (unit **E1**) |
| **M** | the mild equation `eq:mild` | `appendix-a:109-114` | HeliCorgi `IsR3EndpointSafeProjectedMildSolutionOn` (unforced), OpenAI `quadraticDuhamel` (forced, cylinder) | **owner: A02/A04, not A01.** Deliberately absent from `Spec.lean`; recorded here so it is not lost. Reaching it needs a whole-space heat semigroup on the D01 carrier, which neither `heatOperator` (cylinder) nor `r3StokesH3Evolution` (complex Bessel) is |

---

## 3. Bounded implementation split

Size key: **S** ≤ ~100 lines of Lean, no new analytic machinery; **M** a
self-contained lemma with real content but a known proof; **L** a multi-file
campaign. Units are named so the strategy memo can reference them.

Re-sized in revision 2 (`REVIEW.md` H3, and the reviewer's unit-sanity pass):
**C1b**, **A3** and **B1** are **L**, not M — C1b is the same kind of
Fourier-convention bridge as C1c, and A3/B1 are bootstrap campaigns booked as
lemmas; **P1** is **M**, not S (differentiation under `intervalIntegral` with
its side conditions).  **A2b** is new (`REVIEW.md` M1).  No unit is an open
mathematical problem — A3 is Tao 5.4(ii) by a standard Grönwall bootstrap — but
A3, C1b and B1 together are essentially all of A01.

| # | unit | size | depends on | binds to / gap |
|---|---|---|---|---|
| **E1** | `∇·(u⊗u) = (u·∇)u` for smooth divergence-free `u`; hence `ClassicalSolutionR.momentum` ⟺ `projected` + `pressure_recovery` | S | — | pure calculus on `NavierStokes.ProblemStatement.advection` / `spatialDerivative` |
| **P1** | `pressurePotential G` has gradient `G` under `HasSymmetricJacobian G`; hence `pressure_potential` is satisfiable | **M** | — | the manuscript's own two lines (`02-prelim:98-100`); = D01 unit L9(b). M rather than S: differentiating `∫₀¹ ⟨G(rx,t),x⟩ dr` under the integral needs the `intervalIntegral` side conditions |
| **P2** | `IsLerayComplement w ·` is single-valued **for differentiable `w`**: two witnesses differ by an `L²` field that is curl free and divergence free, hence harmonic and `0` | M | — | **gap**; Liouville for `L²`-harmonic fields. Mathlib has the pieces; no in-tree statement. *Restated in revision 2*: revision 1 omitted the hypothesis on `w`, and `HasSymmetricJacobian` did not require `Differentiable ℝ G`, so bare-`fderiv` junk values made the unit **false as written** (`REVIEW.md` H2). `Spec.lean` now carries `Differentiable ℝ G`; `IsSolenoidal` still reads a bare `fderiv`, hence the hypothesis on `w`, which holds wherever the contract uses it (`w = f − ∇·(u⊗u)` is smooth) |
| **C1a** | `MemHInfty a ↔ ContDiff ∧ ∀n, MemLp (iteratedFDeriv n a) 2`, and either gives `a : SmoothL2Field Space` | M | — | = D01 unit **L2**, already scoped there. Binds `Euler/LpSmoothField.lean:31`, `Source/FourierPhysicalJets.lean:169`; gap in `⟸` for non-compact data |
| **C1b** | D01 angular datum `IsSobolevDatum m` ⟷ Euler `ordinarySobolev`/`EulerMeanSolenoidal.L2` coordinates, order by order, **through the cylinder `ordinaryLift` adjoint** | **L** | C1a | binds `Paper3.angularRealization`, `Source.AngularForceNorms`, `Euler/MeanOrbitSobolev.lean:71`, `OrdinaryCylinderDescent.lean:56-71`. Re-sized: this is the *same kind* of Fourier-convention bridge as C1c, plus the angle-invariance bookkeeping, and it sits on the critical path of the **recommended** route |
| **C1c** | D01 angular datum ⟷ HeliCorgi Bessel coordinate `R3HsVelocity m` + reality subspace + `(2π)` normalization | L | C1a | **gap**; three Fourier conventions meet here. *Velocity only.* The **pressure** slice does not need it: `R3HsVelocity` is order-erasing (`R3SobolevCarrier.lean:29`), so `r3LerayComplementL2`/`r3HelmholtzPressure` act on plain complex `L²` and P3 needs only real↪complex plus `𝓢'`→pointwise |
| **F1** | affine forcing in the Duhamel map | S on the OpenAI route (already `Coefficients.forcing`, `QuadraticCoefficients.lean:16`) / **L** on the HeliCorgi route (new field in `EndpointSafeTwoSpaceDuhamelContract:407`, new integrand branch, new majorant, re-prove `EndpointSafeTwoSpacePicard.lean:887`) | — | see the size column |
| **A1** | tame product `‖u⊗u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}` and `‖v‖_∞ ≤ C‖v‖_{H²}` on the D01 carrier | M | C1b | **A03's**, `appendix-a:9-13`/`:15-19` (`eq:Rproduct`, `eq:tame`). A01 consumes, does not prove |
| **A2** | high-order propagation: `(‖u‖_{H^m})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m}` for `m ≥ 3` on an interval of low-order existence, with the `(‖u‖²+ζ²)^{1/2}` regularization | M | A1 | **gap**, but *shared with A04*: it is literally `eq:Rhigh` (`appendix-a:132-137`, hypothesis `m ≥ 3` at `:129`) and `eq:highcontinuation` (`:142-145`, regularization at `:140-141`). Build in one place |
| **A2b** | order-`m` **continuation criterion** (a bounded order-`m` trajectory extends by a positive step) **plus cross-order agreement** (the order-`(q+1)` and order-`(q'+1)` solutions for the same datum coincide where both exist) | M | A2, F1, A02's uniqueness | **new in revision 2** (`REVIEW.md` M1). Without (a) the Grönwall bound of A2 cannot be cashed into a longer interval; without (b) "the" all-order solution is not well defined. HeliCorgi **has (a)** at order 3 — `r3EndpointSafeProjected_exists_extension_of_bounded` (`R3MildContinuation.lean:84`) and `_blowup_dichotomy` (`:134`), ported as `FormalPatched` — and its unrestricted uniqueness (`EndpointSafeTwoSpaceUniqueness.lean:222`) gives (b) at that order. The Euler/local Picard layer has **neither**. This unit is the strongest single argument for the HeliCorgi route |
| **A3** | order-independent `T₀`: take `T₀` = the budget's `T` at the **lowest available order** and propagate every higher order on that same `T₀`. On the recommended (OpenAI/local) spine the lowest order is `q + 1 = 7` (`hq : 6 ≤ q`, `ForcedCylinderLocal.lean:72`), i.e. `T₀` from `‖a‖_{H⁷} + ‖f‖_{L¹_tH⁷}`; on the HeliCorgi route it is `H³` | **L** | A2, A2b, F1 | **gap**. Note it need **not** touch `QuadraticHeatLocal.lean:32`: the budget's `T` is used as given at one order, and everything above it is propagation |
| **T1** | `C^j_tH^k_x` for all `j,k` on `[0,T₀)`, one-sided at `0`: `∂ₜu = νΔu + P(f − ∇·(u⊗u)) ∈ C_tH^k`, then induct | M | A3, E1 | **gap**; `appendix-a:71-76`. `Ico 0 T` is `UniqueDiffOn`, so `ContDiffOn` gives the one-sided derivative |
| **B1** | `H^∞`-in-time path → pointwise field: `ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)` from T1 by all-order Sobolev embedding | **L** | T1, A1 | **gap**; the joint space-time smoothness is what `ClassicalSolutionR.velocity_smooth` demands and no source produces. Re-sized: turning a family of `H^m`-valued time paths into one jointly smooth pointwise field is a campaign, not a lemma |
| **B2** | assemble `ClassicalSolutionR`: `initial`, `divergence`, `momentum`, `sobolev`, `pressure_gradient` from B1 + E1 + P3 | S | B1, E1, P3 | field-by-field. `SmoothLifespan.Flow` (`:23`) shares the velocity/pressure/equation core and can be produced in the same pass for A02, but it needs `energy`/`velocity_bound`/`derivative_bound` in addition and does not need `sobolev`/`pressure_gradient` |
| **P3** | physical `eq:Rpressure`: `IsLerayComplement (f − ∇·(u⊗u)) (∇p)` with `∇p ∈ L²`, plus `pressure_smooth` | M | P2; real↪complex `L²` + `𝓢'`→pointwise *(HeliCorgi route — **no** Bessel bridge, see C1c)* or a directly constructed Helmholtz split *(OpenAI route)* | binds `r3HelmholtzPressure_gradient` (`R3HelmholtzPressure.lean:259`), `r3LerayComplementL2` (`:228`), and for the symbol `R3LerayComplexFiberSymbol.lean:114` / `R3LerayPointwiseProjectionIdentification.lean:97`. **Overlaps D01 unit L9(c)** (`RECONCILIATION.md:160`), which is the same statement on `Ioo 0 T`; A01's increment is the `t = 0` endpoint. Book it once, in whichever lane runs first |
| **H1** | `horizon_lower_bound`: one `δ > 0` below every horizon in an `H¹` ball, for fixed `ν` | M | A3 | **gap**; `appendix-a:147-150`, quantitative source Tao 5.4(ii) eq. (46) at viscosity one, rescaled by `appendix-a:79-87`. Consumed by **A04**'s restart at `t₀ ↑ S`; new field in `Spec.lean` in revision 2 (`REVIEW.md` M5) |
| **X1** | package `LocalTheoryAPI`: choose `horizon` and `solution` as functions of `(ν,a,f)` | S | B2, P1, P3, T1, H1 | choice over the existential of A3; no analysis |

Totals: **3 S / 7 M / 5 L** — S: E1, B2, X1; M: P1, P2, C1a, A1, A2, A2b, P3, T1, H1 *(minus the two attributed away)*; L: C1b, C1c, A3, B1, and F1 **on the HeliCorgi route only** (S on the OpenAI route).
**A1** is A03's and **C1a** is D01's, so A01 owns 14 units. Three of the five L
units — C1b, A3, B1 — are on the critical path of *every* route; the fifth
(F1 or C1c) is what the route choice selects.

---

## 4. Strategy memo

### Recommendation (unchanged after review, on a revised balance)

**I keep the revision-1 recommendation: spine = the OpenAI/local forced Duhamel
(`OrdinaryForcedLocal.exists_local`), HeliCorgi = the pressure edge.**  The
margin, however, is thinner than revision 1 claimed, and the reviewer is right
about why (`REVIEW.md` §Strategy).  Order of work: F1 (free), C1a + C1b, then
A1 ← A03, A2, A2b, A3, T1, B1, B2, with P1/P2/P3 and H1 in parallel, X1 last.

What survives review unchanged:

* **Forcing is structural, not incidental.** HeliCorgi's Picard layer is built
  on `EndpointSafeTwoSpaceDuhamelContract` (`EndpointSafeTwoSpaceDuhamel.lean:407`),
  whose *only* source is `bilinear` (`:427`) — 11 fields, no forcing. Adding a
  forcing term is a change to the abstract contract plus its endpoint-safe
  integrand, its majorant estimate and its fixed-point theorem
  (`EndpointSafeTwoSpacePicard.lean:887`) — an **L**. On the OpenAI side
  `Coefficients.forcing` (`QuadraticCoefficients.lean:16`) exists and
  `ForcedCylinderLocal.coefficients:52` already instantiates it at
  `P(f − (u·∇)u)` — free.
* **Reality and physicality are only on the OpenAI/local side.**
  `OrdinaryForcedLocal.exists_local:32` starts from a real physical
  `SmoothL2Field Space` and lands in real ordinary `L²`; HeliCorgi's carrier is
  complex and its equation lives in `𝓢'`, and its one real, physical entry
  point (`R3SchwartzInitialData`) is **not ported**. `OrdinaryViscousUniqueness.velocity_unique`
  (`OrdinaryViscousUniqueness.lean:26`) already fixes the output shape A02
  needs, in the same physical carrier. This, not F1, is now the decisive
  argument.
* **A2 is shared with A04.** `eq:Rhigh` (`appendix-a:132-137`) and
  `eq:highcontinuation` (`:142-145`) are exactly the inequality A04's
  continuation criterion needs; building it once is the difference between two
  M-units and four.
* **A Tao-style direct proof** on the D01 carrier is the "replacement
  Fourier/Leray/Picard library" the task card forbids scheduling, and it
  duplicates two working Picard layers.

Three corrections the review forced, all of which narrow the margin:

1. **The pressure edge is *stronger* than revision 1 said, for a reason
   revision 1 missed.** `R3HsVelocity` erases its order
   (`abbrev R3HsVelocity (_s : ℝ) := R3L2Velocity`, `R3SobolevCarrier.lean:29`),
   so `r3LerayComplementL2` and `r3HelmholtzPressure` act on **plain complex
   `L²`**. Importing the pressure needs a real-`L²` ↪ complex-`L²` embedding and
   a `𝓢'`→pointwise transport — **no Bessel/angular Sobolev bridge at all**.
   C1c is needed only for the *velocity*. This makes "HeliCorgi for the pressure
   only" cheap and clean; it also removes the revision-1 sentence that P3 needs
   "a narrow slice of C1c", which was wrong.
2. **Revision 1's claim that the OpenAI route "avoids an L" was false.** It
   trades C1c (L) for **C1b (also L)** — the same kind of Fourier-convention
   bridge, plus the angle-invariance bookkeeping of the cylinder descent — and
   C1b sits on the *critical path of the recommended route*. Worse, revision 1
   did not count the **continuation layer**: HeliCorgi has
   `exists_extension_of_bounded` / `blowup_dichotomy` (`R3MildContinuation.lean:84`,
   `:134`) and unrestricted uniqueness (`EndpointSafeTwoSpaceUniqueness.lean:222`)
   already ported as `FormalPatched`; the Euler/local Picard layer has no
   analogue, which is unit **A2b**. So the honest scoreboard is: F1 and
   reality/physicality favour OpenAI; E, A2b and the absence of C1b favour
   HeliCorgi. I still land on OpenAI because reality + physical `L²` +
   `velocity_unique` are *structural* and cannot be bought, while A2b is a
   lemma the OpenAI route can prove — but the margin is thin enough that
   **trigger 3 below should be tested first, not last**.
3. **The "biggest risk" was misdiagnosed** — see below.

### Biggest risk

**Not** "A3 must replace the Euler time budget". Revision 1 said that, and it
overstated the problem: A3 need not touch `QuadraticHeatLocal.lean:32` at all.
Take `T₀` to be the budget's `T` at the **lowest available order** — on this
spine `q = 6`, i.e. `H⁷` (`hq : 6 ≤ q`, `ForcedCylinderLocal.lean:72`;
`H³` is the HeliCorgi order, not this one) — and propagate every higher order
on that same `T₀`. The budget theorem is used as given, once.

The real risk is what that bootstrap *actually* needs and neither the revision-1
unit list nor its risk section contained: **an order-`m` continuation criterion
plus cross-order agreement** (unit **A2b**). A Grönwall bound on `‖u‖_{H^m}`
over `[0,T₀)` is worthless without a theorem that turns a bounded order-`m`
trajectory into a longer one, and "the" all-order solution is not even well
defined without agreement between the order-`(q+1)` and order-`(q'+1)`
witnesses. HeliCorgi has both at order 3, ported; the Euler/local layer has
neither at any order. If A2b turns out to require re-opening the Euler Picard
layer, the recommendation flips (trigger 1).

Second risk, unchanged: three Fourier conventions (D01 angular unitary, Euler
translation-orbit coordinates, HeliCorgi Bessel/`𝓕`) meet in C1b/C1c, and the
`(2π)` bookkeeping is exactly where `REVIEW_A` found D01's first junk-value bug.

Third, recorded rather than ranked: `exists_positive_time_budget` gives no
handle on `T` whatsoever (`REVIEW.md` H1). That is not itself a risk to A3 —
A3 quantifies over the `T` it is handed — but it does mean **H1**
(`horizon_lower_bound`) cannot be read off the source and must come from the
propagation argument together with Tao 5.4(ii)'s explicit smallness condition.

### What would change the route

Ordered by when to test, not by likelihood.

1. **Test first — if C1c turns out to be short.** Revision 1 ranked this last on
   the belief that the pressure edge needed "a slice of C1c"; correction 1 above
   shows it needs *none*, so the C1c estimate is now untested by anything on the
   recommended path. If the full angular↔Bessel bridge is days rather than a
   campaign, the HeliCorgi route pays only F1 and gets E, A2b and `R³`-native
   operators for free, which makes it the better base for A02/A04 as well.
   **Trigger:** a scoping spike on C1c that revises its `L` to `M`.
   **Cost of testing:** small, and it is needed for the pressure edge's
   `𝓢'`→pointwise step anyway.
2. **If A2b requires re-opening the Euler Picard layer.** Then the cylinder
   carrier is paid for (C1b + angle-invariance bookkeeping) and the continuation
   layer must still be built from scratch, while HeliCorgi's is already ported.
   **Trigger:** a failed attempt at A2b that has to touch
   `Euler/QuadraticHeatLocal.lean:32` or `Euler/VolterraUniqueness.lean:69`.
3. **If A03 lands `eq:Rproduct`/`eq:tame` on the D01 carrier early.** A03 is
   already a dependency of R43/R44, so A1 may arrive independently. Once it is
   in hand on the *D01* carrier, A2/A3 can be run there directly and the value
   of *any* vendor Picard layer drops to the initial short interval only — at
   which point the shortest path may be HeliCorgi's `H³` existence + A2/A2b/A3,
   with no cylinder at all. **Trigger:** A03 completed and stated on
   `IsSobolevDatum`.
4. **If a reviewer rejects `IsLerayComplement` as a characterization.** Then the
   Fourier-symbol `P` must be constructed on the D01 carrier — and note that
   HeliCorgi's `r3LerayL2Operator` is a `starProjection`, so even there the
   symbol comes from two further modules (`R3LerayComplexFiberSymbol.lean:114`,
   `R3LerayPointwiseProjectionIdentification.lean:97`). This pulls a multiplier
   construction into the critical path regardless of route, and the HeliCorgi
   route becomes strictly better.
