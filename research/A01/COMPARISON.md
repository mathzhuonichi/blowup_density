# A01 — source-to-target comparison, adapter edges, implementation split, strategy

Lane 013, task **A01** ("Whole-space local solution adapter"), 2026-09-13.
Target contract: [`Spec.lean`](Spec.lean), namespace `BlowupDensity.A01.Draft`.
Manuscript object: the **existence half** of `prop:local`
(`paper/sections/02-preliminaries.tex:105`), derived in
`paper/sections/appendix-a-local-theory.tex:74-107` from Tao 2013
Theorem 5.4(ii)–(iv) (`reference/Tao_2013_Localisation_Compactness_Published.pdf`,
published pp. 52–53).

Everything quantified over is the canonical D01 object of
`verification/Contracts/V1/Data.lean` (`research/D01/PAPER_TO_LEAN.md`).
Uniqueness is A02, the continuation criterion is A04; neither is stated here.

---

## 0. What the target actually demands

Tao Theorem 5.4, as printed:

| clause | printed content |
|---|---|
| (ii) | `‖u₀‖_{H¹} + ‖f‖_{L¹_tH¹}` small compared with `T^{-1/4}` gives an `H¹` **mild** solution with `‖u‖_{X¹} ≲ ‖u₀‖_{H¹}+‖f‖_{L¹_tH¹}`, **and more generally** `‖u‖_{X^k} ≲_{k,‖u₀‖_{H^k},‖f‖_{L¹_tH^k},1}` for each `k ≥ 1` — i.e. every order on the **same** `T` |
| (iii) | at most one `H¹` mild solution |
| (iv) | for Schwartz data `u` and `p` are smooth, `∂ₜ^ju, ∂ₜ^jp ∈ L^∞_tH^k` for all `j,k`; the proof's closing parenthesis says `u₀ ∈ H^k` and `f ∈ C^j_tH^k` suffice, Schwartz is not needed |

The manuscript's own additions on top of that (`appendix-a-local-theory.tex`):
viscosity `ν` by parabolic rescaling (`:93-99`), the projected formulation with
force `P f` (`:88-90`), pressure by `eq:Rpressure` + the radial potential
(`02-preliminaries.tex:90-100`), and the mild equation `eq:mild` (`:109-113`)
used only to reach uniqueness and restart.

So the A01 deliverable has five irreducible components: **(A)** one positive
`T₀` independent of the Sobolev order; **(B)** an ordinary real physical field
on `R³`, classically smooth on `[0,T₀) × R³`; **(C)** `C^j_tH^k_x` for all
`j,k` with one-sided `t = 0` derivatives; **(D)** the projected equation with
affine forcing; **(E)** the pressure gradient and its radial potential.

---

## 1. Three-source table

### 1.1 HeliCorgi (`vendor/HeliCorgi/Formal/`, namespace `MNS2`)

Importable at this pin as `Formal.*` (84 modules built in place from
`vendor/HeliCorgi`) and `FormalPatched.*` (4 modules), per
`research/U05/PORT.md`; `formalization/NSFormalization/Section4/HeliCorgiPort.lean`
is the smoke module.

| declaration | file:line | space / carrier | order | forced? | interval | field type | real/complex |
|---|---|---|---|---|---|---|---|
| `r3EndpointSafeProjected_exists_localMildSolution` | `R3EndpointSafeProjectedLocalExistence.lean:35` | `R3HsVelocity 3` `= R3L2Velocity = Lp R3C 2 volume` (`R3SobolevCarrier.lean:29`, `R3StokesL2Operator.lean:22`) | exactly **3** (fixed) | **no** | `∃ T, 0 < T ∧ T ≤ 1`, trajectory on `Icc 0 T`, closed-ball uniqueness at radius `‖u₀‖+1` | Bessel **coordinate** `J³u ∈ L²`; the physical field is `J⁻³` of it | **complex** (`R3C = EuclideanSpace ℂ (Fin 3)`) |
| `IsR3EndpointSafeProjectedMildSolutionOn` / `r3EndpointSafeProjectedMild_equation_at_time` | `R3EndpointSafeProjectedDuhamel.lean:156`, `:163` | same | 3 (→ 2 for the source) | **no** | `u t = S(t)u₀ − ∫₀^t K(t,s)P(u⊗u)(s)` | coordinate | complex |
| `r3EndpointSafeProjectedDuhamelContract` | `R3EndpointSafeProjectedDuhamel.lean:20` | instance of `EndpointSafeTwoSpaceDuhamelContract` (`EndpointSafeTwoSpaceDuhamel.lean:407`) | — | **no forcing field exists**: the contract's only source is `bilinear : X →L X →L Y` (`:427`) | — | — | — |
| `r3EndpointSafeProjectedMild_navierStokes` | `R3NavierStokesEquation.lean:142` | decoded `r3H3ToL2Operator (u t) : R3L2Velocity` (`R3StokesH2H3Smoothing.lean:294`) | 3 | **no** | interior times `Ioo 0 T` | strong `L²`-valued `∂ₜ`; momentum **componentwise in `𝓢'`**, divergence distributional | complex |
| `r3AdmissibleSchwartzDatum_navierStokes` | `R3SchwartzInitialData.lean:233` | same, entered from `φ : R3SchwartzVelocity`, real + divergence free (`:77`) | 3 | **no** | `Icc 0 T` for realness/energy, `Ioo 0 T` for the equation | decoded physical `L²`, `U 0 = φ.toLp` | decoded field **is** real here (`:194`, `R3DecodedVelocityRealness`) |
| `r3HelmholtzPressure` / `r3HelmholtzPressure_gradient` | `R3HelmholtzPressure.lean:223`, `:259` | arbitrary `F : R3L2Velocity` | — | source is **arbitrary**, so nonzero forcing is already allowed | — | `∂_j p = −((I−P)F)_j` in `𝓢'` | complex |
| `r3EndpointSafeProjected_exists_extension_of_bounded`, `r3EndpointSafeProjected_blowup_dichotomy` | `R3MildContinuation.lean:84`, `:134` (patched copy `formalization/FormalPatched/R3MildContinuation.lean`) | coordinate | 3 | no | extension by an explicit `r3MildLifespan ν R` | — | complex |
| `r3EndpointSafeProjectedMildSolution_unique` | `EndpointSafeTwoSpaceUniqueness.lean:222` | coordinate | 3 | no | unrestricted (no ball) | — | complex |

**Distance to `prop:local`:** four of the five components are missing. No
forcing anywhere in the Picard layer (D); order pinned at 3, so no common
all-order interval (A); the equation is `𝓢'`-valued in space with a strong
`L²` time derivative, never a pointwise classical field (B, C); realness of
the decoded field only via the Schwartz entry point. What it *does* supply,
and nothing else in tree does, is the concrete `R³` Leray/Stokes/Helmholtz
operator stack and a pressure theorem already valid for an arbitrary `L²`
source (E).

### 1.2 OpenAI (`vendor/NavierStokesAndEuler/`, `Euler*` namespaces)

| declaration | file:line | space / carrier | order | forced? | interval | field type | real/complex |
|---|---|---|---|---|---|---|---|
| `EulerQuadraticSource.quadraticDuhamel` | `Euler/QuadraticHeatLocal.lean:23` | `SobolevSpace period (q+1)` `= sobolevSubspace period (q+1)` (`Euler/CylinderSobolevSpace.lean:49`), a closed submodule of derivative-word arrays in `LiftL2 period` over the **cylinder** `LiftDomain period = Vector3 × AddCircle period` (`Euler/EulerProof.lean:1085`) | `q+1`, `q` fixed | **yes** — `heatOperator …u₀ + ∫₀^t heatKernel … (C.apply …)` with `C.forcing` affine | `Icc 0 T` | Hilbert-space-valued path, physical-side coordinates (no Fourier coordinate) | **real** |
| `Coefficients` (with `forcing : C(T,Y)`) | `Euler/QuadraticCoefficients.lean:16` | — | — | **the affine forcing edge already exists here** | — | — | real |
| `EulerQuadraticSource.exists_local_quadratic_mild` | `Euler/QuadraticHeatLocal.lean:32` | as above | `q+1` | yes | `∃ T, 0 < T ∧ T ≤ S`, `‖u‖ ≤ ‖u₀‖+1` | continuous path | real |
| `EulerQuadraticSource.exists_local_quadratic_divergenceFree` | `Euler/QuadraticHeatConstraint.lean:19` | as above | `q+1` | yes | as above | adds `value (u t) ∈ divergenceFreeSpace` | real |
| `EulerVolterraUniqueness.exists_positive_time_budget` | `Euler/VolterraUniqueness.lean:69` | — | — | — | produces the `T` above from `C.ballBound R`, `C.ballLipschitz R` | — | — |
| `Coefficients.ballBound` | `Euler/QuadraticCoefficients.lean:47` | `‖P‖(‖forcing‖ + ‖linear‖R + ‖quadratic‖R²)`, `R = ‖u₀‖+1` | — | — | — | — | — |

**Distance to `prop:local`:** forcing (D) is free. But the carrier is a
**cylinder** `R³ × S¹`, the order is fixed, and — decisively — `T` is produced
from `ballBound R` with `R = ‖u₀‖_{H^{q+1}} + 1`, so `T` *shrinks as `q`
grows*. The order-independent interval (A) is not merely unproved here, it is
false of the quoted `T`. No pressure, no classical field, no `𝓢'`/Fourier
identification with the D01 datum.

### 1.3 Local `Source` (`formalization/NSFormalization/Source/`)

| declaration | file:line | what it literally gives |
|---|---|---|
| `ForcedCylinderLocal.leray` | `ForcedCylinderLocal.lean:26` | `id − sobolevGradientProjection`, the cylinder Leray projection as a CLM on `SobolevSpace period q`; the gradient part is *discarded*, never reconstructed as a pressure |
| `ForcedCylinderLocal.coefficients` | `:52` | `Coefficients` with `forcing := −f`, `quadratic := advection`, `projection := leray` — i.e. the source `P(f − (u·∇)u)` |
| `ForcedCylinderLocal.exists_local_forced_mild` | `:72` | for `q ≥ 6`, `ν,S > 0`, `u₀ : SobolevSpace period (q+1)` with divergence-free value, `f : C(Icc 0 S, SobolevSpace period q)`: `∃ T ∈ (0,S]` and `u : C(Icc 0 T, SobolevSpace period (q+1))` with `‖u‖ ≤ ‖u₀‖+1`, `u 0 = u₀`, divergence free at every `t`, and the forced Duhamel identity. **Cylinder, fixed order, real, no pressure.** |
| `ForcedCylinderInvariant.exists_local_forced_mild_invariant` | `ForcedCylinderInvariant.lean:30` | the same, plus invariance under every angle translation |
| `OrdinaryCylinderDescent.ordinaryValue`, `ordinaryValue_lift` | `OrdinaryCylinderDescent.lean:56`, `:60` | the adjoint that turns an angle-invariant cylinder element back into an ordinary `EulerMeanSolenoidal.L2` field (`Euler/MeanSolenoidalSpace.lean:22`, `Lp Space 2 volume`) |
| **`OrdinaryForcedLocal.exists_local`** | `OrdinaryForcedLocal.lean:32` | **the closest thing in tree.** From `a : SmoothL2Field Space` (`Euler/LpSmoothField.lean:31`: a genuinely smooth field all of whose jets are `L²`) with classical `divergence a = 0`, and a force path `F : Icc 0 S → SmoothL2Field Space` with all jets continuous in time: `∃ T ∈ (0,S]`, a cylinder witness `u : C(Icc 0 T, SobolevSpace 1 (q+1))` and an **ordinary whole-space** path `U : C(Icc 0 T, EulerMeanSolenoidal.L2)` with `U 0 = a.toLp`, `ordinaryLift (U t) = value 1 (u t)`, divergence free, satisfying the forced mild equation, angle invariant. Real, physical `L²`, **fixed order `q+1` with `q ≥ 6`, `T` depending on `q`, no pointwise field, no pressure, no `H^m` for all `m`, no time smoothness.** |
| `OrdinaryForcedTime.ordinary_hasDerivAt`, `realization_hasDerivAt` | `OrdinaryForcedTime.lean:36`, `:50` | strong `L²`-valued time derivative of that ordinary path at interior times, equal to `adjoint(νΔu + P(f − (u·∇)u))` |
| `OrdinaryViscousUniqueness.velocity_unique` | `OrdinaryViscousUniqueness.lean:26` | uniqueness for two classical `SmoothL2Field`-valued solutions with the same force and datum — **A02's**, listed here because it fixes the physical shape A01's output must have |
| `SmoothLifespan.Flow` | `SmoothLifespan.lean:23` | field-for-field the shape of `ClassicalSolutionR` (`Data.lean:617`): `velocity`, `pressure`, `ContDiffOn ℝ ∞ … (Ico 0 S ×ˢ univ)`, `initial`, `divergence`, `equation` on `Ioo 0 S`, plus energy/velocity/derivative bounds. **Nowhere inhabited.** `lifespan` (`:41`) is the same supremum as `maximalLifespanR` (`Data.lean:650`). |

**Distance to `prop:local`:** the descent to ordinary `R³` (half of B) and the
affine forcing (D) are done. (A), (C), (E) and the pointwise-classical half of
(B) are open.

### 1.4 One-line summary

| component | HeliCorgi | OpenAI | local `Source` |
|---|---|---|---|
| (A) order-independent `T₀` | order fixed at 3 | **`T` provably shrinks in `q`** | inherits OpenAI's `T` |
| (B) ordinary real physical field | complex coordinate, `𝓢'` equation | real, but on the cylinder | real ordinary `L²` path; **not pointwise classical** |
| (C) `C^j_tH^k_x`, one-sided at 0 | one interior `L²` derivative | continuity only | one interior `L²` derivative |
| (D) affine forcing | **absent from the contract itself** | **present** (`Coefficients.forcing`) | **present and already projected** |
| (E) pressure gradient + potential | **present** for arbitrary `L²` source, in `𝓢'` | absent (gradient discarded) | absent (gradient discarded) |

---

## 2. The adapter edges the paper needs

| # | edge | manuscript locus | closest source | what is missing |
|---|---|---|---|---|
| **D** | affine forcing inside the Duhamel map | `appendix-a:88-90`, `eq:mild` `:109-113` | local `Source/ForcedCylinderLocal.coefficients:52` (`forcing := −f`), resting on `Euler/QuadraticCoefficients.lean:16` | nothing on the OpenAI/local side; on the HeliCorgi side the *structure* `EndpointSafeTwoSpaceDuhamelContract` (`:407`) has no forcing field, so adding it means a new field, a new integrand branch, a new majorant clause and re-running `exists_pos_time_isMildSolutionOn` (`EndpointSafeTwoSpacePicard.lean:887`) |
| **A** | one interval for all Sobolev orders | `02-prelim:117`, `appendix-a:81`, Tao 5.4(ii) "more generally" | **none.** OpenAI's `T` comes from `exists_positive_time_budget ν (ballBound R) (ballLipschitz R) 1 S` with `R = ‖u₀‖_{H^{q+1}}+1` (`QuadraticHeatConstraint.lean:19` → `QuadraticHeatLocal.lean:32` → `VolterraUniqueness.lean:69`), so it degrades with the order | the persistence-of-regularity bootstrap: fix `T₀` from the low-order norm, then propagate every `H^m` bound on that same `T₀` by the tame product `eq:tame` `‖u⊗u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}` (`appendix-a:15-21`, **A03**) plus Grönwall. This is *the same* Grönwall as `eq:Rhigh`/`eq:highcontinuation` (`appendix-a:132-140`) that **A04** needs — build once, share |
| **C** | `C^j_tH^k_x` for all `j,k`, one-sided at `t = 0` | `appendix-a:85-88`, Tao 5.4(iv) | continuity only (`C(Icc 0 T, …)` everywhere); one interior strong `L²` derivative from `OrdinaryForcedTime.lean:36` or `R3NavierStokesEquation.lean:142` | the appendix's own induction: the equation has a continuous right-hand side in every `H^k`, so `∂ₜu ∈ C_tH^k`; differentiate repeatedly. Needs (A) first, and `Ico 0 T`-relative (one-sided) derivatives, which no source states |
| **B** | identification of the decoded field with a `ClassicalSolutionR` | `02-prelim:28-36`, `Data.lean:617` | `SmoothLifespan.Flow` (`:23`) is the target shape; `OrdinaryForcedLocal.exists_local:32` produces the ordinary `L²` path | three sub-gaps: (i) `L²`-valued path → pointwise `ContDiffOn ℝ ∞` field on `Ico 0 T ×ˢ univ` (all-order Sobolev embedding, needs (A)); (ii) carrier translation between D01's angular datum `IsSobolevDatum` (`Data.lean:160`, unitary `(2π)^{-3/2}` convention) and the source coordinates — Euler `ordinarySobolev` (`Euler/MeanOrbitSobolev.lean:71`) / HeliCorgi's Bessel `R3HsVelocity` under its own `𝓕`; (iii) complex→real if the HeliCorgi route is used |
| **E** | pressure gradient `eq:Rpressure` and the radial potential | `02-prelim:90`, `:96-100` | HeliCorgi `r3HelmholtzPressure_gradient` (`R3HelmholtzPressure.lean:259`) — already for an **arbitrary** `L²` source, so instantiating at `F = ∇·(u⊗u) − f` needs no new analysis | transport from `𝓢'`-componentwise to the physical `pressureGradient` of `Data.lean`; the `∇p ∈ L²` clause; the sign/normalization; and the radial-potential identity (self-contained, `02-prelim:98-100`, = D01 unit L9(b)) |
| **L** | the Leray projection itself | `02-prelim:76-79` | HeliCorgi `r3LerayL2Operator` (`R3LerayL2Operator.lean:28`, symbol `I−ξ⊗ξ/|ξ|²` on complex `L²`); local `ForcedCylinderLocal.leray:26` (cylinder gradient complement) | `Spec.lean` states `P` by the Helmholtz characterization `IsLerayComplement`, so the contract needs no operator. Identifying that characterization with either in-tree operator is a *consumer-side* obligation (unit **P3**), not a hypothesis |
| **N** | `∇·(u⊗u)` vs `(u·∇)u` | `eq:projected` `02-prelim:81` vs `Data.lean` `momentum` (upstream `advection`) | — | one-line calculus for divergence-free smooth `u` (unit **E1**) |
| **M** | the mild equation `eq:mild` | `appendix-a:109-113` | HeliCorgi `IsR3EndpointSafeProjectedMildSolutionOn` (unforced), OpenAI `quadraticDuhamel` (forced, cylinder) | **owner: A02/A04, not A01.** Deliberately absent from `Spec.lean`; recorded here so it is not lost. Reaching it needs a whole-space heat semigroup on the D01 carrier, which neither `heatOperator` (cylinder) nor `r3StokesH3Evolution` (complex Bessel) is |

---

## 3. Bounded implementation split

Size key: **S** ≤ ~100 lines of Lean, no new analytic machinery; **M** a
self-contained lemma with real content but a known proof; **L** a multi-file
campaign. Units are named so the strategy memo can reference them.

| # | unit | size | depends on | binds to / gap |
|---|---|---|---|---|
| **E1** | `∇·(u⊗u) = (u·∇)u` for smooth divergence-free `u`; hence `ClassicalSolutionR.momentum` ⟺ `projected` + `pressure_recovery` | S | — | pure calculus on `NavierStokes.ProblemStatement.advection` / `spatialDerivative` |
| **P1** | `pressurePotential G` has gradient `G` under `HasSymmetricJacobian G`; hence `pressure_potential` is satisfiable | S | — | the manuscript's own two lines (`02-prelim:98-100`); = D01 unit L9(b) |
| **P2** | `IsLerayComplement w ·` is single-valued on `R³`: a curl-free, divergence-free `L²` field is `0` | M | — | **gap**; Liouville for `L²`-harmonic fields. Mathlib has the pieces; no in-tree statement |
| **C1a** | `MemHInfty a ↔ ContDiff ∧ ∀n, MemLp (iteratedFDeriv n a) 2`, and either gives `a : SmoothL2Field Space` | M | — | = D01 unit **L2**, already scoped there. Binds `Euler/LpSmoothField.lean:31`, `Source/FourierPhysicalJets.lean:169`; gap in `⟸` for non-compact data |
| **C1b** | D01 angular datum `IsSobolevDatum m` ⟷ Euler `ordinarySobolev`/`EulerMeanSolenoidal.L2` coordinates, order by order | M | C1a | binds `Paper3.angularRealization`, `Source.AngularForceNorms`, `Euler/MeanOrbitSobolev.lean:71` |
| **C1c** | D01 angular datum ⟷ HeliCorgi Bessel coordinate `R3HsVelocity m` + reality subspace + `(2π)` normalization | L | C1a | **gap**; three Fourier conventions meet here. *Only needed on the HeliCorgi route* |
| **F1** | affine forcing in the Duhamel map | S on the OpenAI route (already `Coefficients.forcing`, `QuadraticCoefficients.lean:16`) / **L** on the HeliCorgi route (new field in `EndpointSafeTwoSpaceDuhamelContract:407`, new integrand branch, new majorant, re-prove `EndpointSafeTwoSpacePicard.lean:887`) | — | see the size column |
| **A1** | tame product `‖u⊗u‖_{H^k} ≤ C_k‖u‖_{H²}‖u‖_{H^k}` and `‖v‖_∞ ≤ C‖v‖_{H²}` on the D01 carrier | M | C1b | **A03's**, `appendix-a:15-21` `eq:Rproduct`/`eq:tame`. A01 consumes, does not prove |
| **A2** | high-order propagation: `(‖u‖_{H^m})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m}` on an interval of low-order existence, with the `(‖u‖²+ζ²)^{1/2}` regularization | M | A1 | **gap**, but *shared with A04*: it is literally `eq:Rhigh`/`eq:highcontinuation` (`appendix-a:132-140`). Build in one place |
| **A3** | order-independent `T₀`: choose `T₀` from `‖a‖_{H³} + ‖f‖_{L¹_tH³}` and propagate every order on `[0,T₀)` | M | A2, F1 | **gap**. Replaces `exists_positive_time_budget`'s order-dependent `T` for `m > 3` |
| **T1** | `C^j_tH^k_x` for all `j,k` on `[0,T₀)`, one-sided at `0`: `∂ₜu = νΔu + P(f − ∇·(u⊗u)) ∈ C_tH^k`, then induct | M | A3, E1 | **gap**; `appendix-a:85-88`. `Ico 0 T` is `UniqueDiffOn`, so `ContDiffOn` gives the one-sided derivative |
| **B1** | `H^∞`-in-time path → pointwise field: `ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)` from T1 by all-order Sobolev embedding | M | T1, A1 | **gap**; the joint space-time smoothness is what `ClassicalSolutionR.velocity_smooth` demands and no source produces |
| **B2** | assemble `ClassicalSolutionR`: `initial`, `divergence`, `momentum`, `sobolev`, `pressure_gradient` from B1 + E1 + P3 | S | B1, E1, P3 | field-by-field; `SmoothLifespan.Flow` (`:23`) is the same shape and can be produced in the same pass for A02 |
| **P3** | physical `eq:Rpressure`: `IsLerayComplement (f − ∇·(u⊗u)) (∇p)` with `∇p ∈ L²`, plus `pressure_smooth` | M | P2, C1c *(HeliCorgi route)* or a direct Helmholtz split of a smooth `H^∞` field *(OpenAI route)* | binds `r3HelmholtzPressure_gradient` (`R3HelmholtzPressure.lean:259`) and `r3LerayComplementL2` (`:228`); the direct route needs the split constructed instead |
| **X1** | package `LocalTheoryAPI`: choose `horizon` and `solution` as functions of `(ν,a,f)` | S | B2, P1, P3, T1 | choice over the existential of A3; no analysis |

Total: 4 S, 9 M, 2 L (one of which, **C1c**, is route-dependent and avoidable).
**A1** is A03's and **C1a** is D01's, so A01 owns 12 units.

---

## 4. Strategy memo

### Recommendation

**Spine: the OpenAI/local forced Duhamel (`OrdinaryForcedLocal.exists_local`).
HeliCorgi: for the pressure edge only.** Concretely: F1 (free), C1a+C1b, then
A1←A03, A2, A3, T1, B1, B2, with P1/P2/P3 in parallel, and X1 last.

Why this and not the alternatives:

* **Forcing is structural, not incidental.** HeliCorgi's Picard layer is built
  on `EndpointSafeTwoSpaceDuhamelContract` (`:407`), whose *only* source is
  `bilinear`. Adding a forcing term is not a lemma, it is a change to the
  abstract contract plus its endpoint-safe integrand, its majorant estimate and
  its fixed-point theorem (`EndpointSafeTwoSpacePicard.lean:887`) — an **L**.
  On the OpenAI side, `Coefficients.forcing` (`QuadraticCoefficients.lean:16`)
  already exists and `ForcedCylinderLocal.coefficients:52` already instantiates
  it at `P(f − (u·∇)u)`. Taking the source whose forcing is free removes the
  single largest avoidable unit.
* **The real work is the same on either route.** (A), (C) and the classical
  identification are equally missing from both — HeliCorgi's order is pinned at
  3, OpenAI's `T` shrinks in `q`. Neither vendor shortens A2/A3/T1/B1. So the
  route should be chosen on the *avoidable* differences, which are F1 (favours
  OpenAI) and E (favours HeliCorgi).
* **Reality and physicality are already half-done on the OpenAI route.**
  `OrdinaryForcedLocal.exists_local:32` starts from a real physical
  `SmoothL2Field Space` and lands in real ordinary `L²`; HeliCorgi's carrier is
  complex and its equation lives in `𝓢'`, so the HeliCorgi route additionally
  owes C1c (**L**) and a complex→real transport.
* **The pressure is cheap to import and expensive to rebuild.**
  `r3HelmholtzPressure_gradient` is stated for an arbitrary `L²` source, so it
  already covers nonzero forcing; and U05 has made it importable
  (`Formal.R3HelmholtzPressure` builds in place). Using it for P3 only — one
  operator, at one time slice, on a field we already know is `H^∞` — needs a
  narrow slice of C1c rather than the full carrier bridge.
* **A2 is shared with A04.** The Grönwall that gives the all-order interval is
  literally the appendix's continuation inequality. Building it once in a shared
  module is the difference between two **M** units and four.
* The third alternative, a **Tao-style direct proof** on the D01 datum carrier
  (heat semigroup, Leray multiplier, Picard, all in the angular normalization),
  is exactly the "replacement Fourier/Leray/Picard library" the task card
  forbids scheduling, and it duplicates two working Picard layers.

### Biggest risk

**The cylinder detour may not survive the order-independent interval.**
`OrdinaryForcedLocal.exists_local` reaches `R³` through
`SobolevSpace 1 (q+1)` on `R³ × S¹` and an angle-invariance descent
(`OrdinaryCylinderDescent.lean:56-71`), and its `T` is produced by
`exists_positive_time_budget` from `ballBound R` with `R = ‖u₀‖_{H^{q+1}}+1`.
Unit A3 has to *replace* that `T`, not refine it. If the replacement cannot be
done at the level of `Coefficients`/`quadraticDuhamel` — i.e. if fixing `T` and
re-running the propagation forces re-opening `exists_local_quadratic_mild`
itself — then the cylinder carrier is being paid for with nothing bought, and
the whole descent (C1b + the angle-invariance bookkeeping) becomes dead weight.
Second risk, smaller: three Fourier conventions (D01 angular unitary, Euler
translation-orbit coordinates, HeliCorgi Bessel/`𝓕`) meet in C1b/C1c, and the
`(2π)` bookkeeping is exactly where `REVIEW_A` found D01's first junk-value bug.

### What would change the route

1. **If A3 forces re-opening the Euler Picard budget anyway.** Then the cylinder
   detour buys nothing, and it is cheaper to pay F1 on HeliCorgi (one new
   contract field + one new majorant clause) and work directly on `R³`, where
   Leray, Stokes, Helmholtz and the pressure already exist and where the
   continuation layer (`FormalPatched.R3MildContinuation`) is already ported.
   **Trigger:** a failed attempt at A3 that has to touch
   `Euler/QuadraticHeatLocal.lean:32`.
2. **If A03 lands `eq:Rproduct`/`eq:tame` on the D01 carrier early.** A03 is
   already a dependency of R43/R44, so A1 may arrive independently. Once it is
   in hand on the *D01* carrier, A2/A3 can be run there directly and the value
   of *any* vendor Picard layer drops to the initial short interval only — at
   which point the shortest path may be HeliCorgi's `H³` existence + A2/A3,
   with no cylinder at all. **Trigger:** A03 completed and stated on
   `IsSobolevDatum`.
3. **If C1c turns out to be short.** The pressure edge already needs a slice of
   it; if the full angular↔Bessel bridge is a day's work rather than a campaign,
   the HeliCorgi route's only remaining cost is F1, and its `R³`-native
   operators and continuation layer make it the better base for A02/A04 too.
   **Trigger:** C1c's `L` estimate revised to `M` after the P3 slice is done.
4. **If a reviewer rejects `IsLerayComplement` as a characterization.** Then the
   Fourier-symbol `P` must be constructed on the D01 carrier, which pulls C1c
   (or an equivalent multiplier construction) into the critical path regardless
   of route, and the HeliCorgi route becomes strictly better.
