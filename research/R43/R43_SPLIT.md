# R43 — Proposition 4.3 proof-route split (`prop:Rcritical1`)

## Lane 223 update: zero-datum endpoint proved unconditionally

`Endpoint.lean` closes S4/S5/S6 at zero datum. Its explicit positive
`criticalConst` gives the exact inhomogeneous force-smallness statement of
`Spec.lean:243–247`, with no named analytic hypothesis. G5 reuses lane 167's
existing maximal-family bound; its absorption premise is now discharged from
force smallness. The lane 217 continuation dependencies are included unchanged.
See `REPORT_223.md` for provenance, exact scope and all validation results.
The older registration audit below is historical, not a claim that the
zero-datum endpoint remains unproved. General initial data remain separate.


## Lane 167 update: G5 endpoint passage proved locally

`Section4/R43/MaximalEndpoint.lean` now transfers the C01 absorption/H2 estimate
through the actual `A02.IsMaximalSolution` family to every real `0<S` with
`ofReal S ≤ maximalLifespanR`, including the finite maximal endpoint. It supplies
both the full constant-32 estimate and A04's canonical `squaredHTwoIntegral ≠ ⊤`.
Only strictly shorter classical horizons are used. The actual frozen V2 family
and V4 absorption constant are consumed in `research/R43/axioms_endpoint167.lean`.

The module, four standard-axiom audits, 27 registered contracts, mutations and
administrative checks passed; see `logs/VALIDATION_167_20260915.md`. This closes
G5 conditional on the genuine absorption bound. It does not derive that bound
from initial/forcing smallness or close critical energy G7, A05's remaining
critical embeddings, or unconditional A04 continuation. The historical rows
below describing G5 as missing are superseded only in this stated scope.

## Lane 165 update (2026-09-15; supersedes the historical C01 registration status below)

This branch now registers `C01.energy_absorption_v4` in
`Contracts/V4/EnergyAbsorption.lean`, with the actual binding and
`Tests/EnergyAbsorptionV4.lean`. It extends frozen V3 and supplies the six original
remaining C01 fields, including enstrophy absorption, the genuine angular H²
comparison, and the H² time integral for **0<S≤T, including S=T**. The test module
and its exact parent projection and terminal-finiteness consumer compile with
standard logical axioms only. Independent paper-first statement drafts and the
comparison/review are in `research/C01/BLIND165_{A,B}.*`, `COMPARISON_165.md`, and
`REVIEW_SPEC_165.md`.

Consequently, the historical rows below saying C01 V4 / `h2TimeIntegral` /
`enstrophyIntegralBound` / `sobolevTwoFourier` are unproved or unregistered no
longer apply on this branch. C01's fixed-horizon endpoint is proved. Passing
from a compatible maximal family to S=T_max (G5), critical energy (G7), and
the other A05/A04 or force-path obligations are not closed by this registration.
This is a local stacked-PR result; it does not assert merged or successful cloud CI.

Statement `paper/sections/04-whole-space.tex:82-89`; proof `:90-133`.
Contract `research/R43/Spec.lean` (`BlowupDensity.R43.Draft.RCritical1API`, 4 fields);
gap ledger `research/R43/COMPARISON.md` §4 (G1–G8); reconciliation `research/R43/RECONCILIATION.md`.

This is the proof route of Prop 4.3 as a row table. For each row: the exact Lean
shape, which **registered** contract field / tree lemma supplies it (or the precise
gap with owner, size, dependency), and whether it blocks **stating** vs **proving**.

**Lean delivered this lane** (`formalization/NSFormalization/Section4/R43/Pieces.lean`,
namespace `NSFormalization.Section4.R43`): G6, all of G8's arithmetic, and the S2
`a = 0` bootstrap by reuse. Conformance `research/R43/axioms_r43_pieces.lean`
(all five `#print axioms` = `[propext, Classical.choice, Quot.sound]`).

---

## 0. Registration audit (what the consumed contracts actually contain, on this branch)

The single most important finding of this split: **three of the four sibling
clauses R43's proof route quotes are draft-only, not registered.** `research/*/Spec.lean`
are drafts (namespaces `…Draft`); only `verification/Contracts/**` + `contracts.json`
are registered. Checked `verification/contracts.json` and every `Contracts/V*` file:

| sibling clause R43 needs | draft location | **registered?** | registered contract that *is* present |
|---|---|---|---|
| A05 `velocityCriticalL3` (`‖u‖₃ ≤ C(1/2)·y`) | `research/A05/Spec.lean:366` | **NO** | `A05.gradient_l6` (V1 `GradientL6`) registers only `gradientLSix` = `‖∇v‖₆ ≤ C‖Δv‖₂` (unit U9) |
| C01 `h2TimeIntegral` (`∫₀ˢ‖u‖²_{H²} ≤ …`) | `research/C01/Spec.lean:576` | **NO** | `C01.energy_absorption_partial_v3` registers up to eq:RL2 (`l2Bound`) + `energyIdentity` + `energyDifferentialBound`; `h2TimeIntegral`/`enstrophyIntegralBound`/`sobolevTwoFourier` are out of scope (V3 disclosure 5) |
| C01 `enstrophyIntegralBound` (eq:RH1), `sobolevTwoFourier` | `research/C01/Spec.lean:532,555` | **NO** | same — draft only |
| A04 `lifespanInfiniteOfLocallyFinite` (`T_max = ⊤`) | `research/A04/Spec.lean:657` | **NO** | `A04.energy_high_partial_v2` registers `energyIdentityHigh`, `regularizedNormDerivative`, `highContinuationIntegral`, `Cgron`, `MemL1Hm` — the continuation *interface*, not the closing lifespan clause |
| A02 maximal family (`exists_maximal`, `IsMaximalSolution`, `presingularTimes`) | `research/A02/Spec.lean:421` | **YES** | `A02.maximal_partial_v2` (V2 `MaximalPartial`) |
| A05 `gradientLSix` (`‖∇v‖₆ ≤ C‖Δv‖₂`, eq:RH1 ingredient) | — | **YES** | `A05.gradient_l6` |
| C01 `l2Bound` = eq:RL2, `energyIdentity`, `energyDifferentialBound`, `C₁`, `trilinearAbsorbed`, `forceTimeRegularity`, `criticalL3` | — | **YES** | `C01.energy_absorption_partial_v3` (+ V1/V2) |

Consequence: R43 cannot be *proved* against the registry as it stands. Three
upstream registrations are prerequisites — **A05 V2** (`velocityCriticalL3`), **C01 V4**
(the `∫‖u‖²_{H²}` assembly `h2TimeIntegral`, with eq:RH1 + `sobolevTwoFourier`), and
**A04 V3** (`lifespanInfiniteOfLocallyFinite`) — none of which this lane owns.

`Data.dotHomogeneousENorm` (G1) is **absent** from `Contracts/V1/Data.lean`: the file
has `dotHHalfENorm` (= `homogeneousFourierENorm (1/2)`, the junk-`0` Fourier form),
`homogeneousVectorENorm`, `IsHomogeneousSliceDatum` — but no datum-infimum spatial
homogeneous norm on a physical field. So the local `def dotHomogeneousENorm` in
`Spec.lean:142` is load-bearing and G1 blocks **stating** the contract cleanly.

---

## 1. Proof-route rows S1–S6

`y = ‖Λ^{1/2}u‖₂ = ‖u‖_{Ḣ^{1/2}}`, `z = ‖Λ^{3/2}u‖₂ = ‖u‖_{Ḣ^{3/2}}`,
`b = ‖f‖_{Ḣ^{1/2}}`, `C₀` R43-own, `C₁` C01's, `Cemb = C(1/2)` A05's.

### S1 — eq:Rcritical1: the critical energy inequality (G7, CLOSED by lane 219)

`04-whole-space.tex:97-99`. Testing the projected equation against `Λu` gives
`½(y²)' + (ν − C₀y)z² ≤ by`.

**CLOSED for every classical solution with positive viscosity and `MemForceR f`.**
Lane 219's `Section4/R43/CriticalMomentum.lean` proves
`criticalDatumInputs_of_classical`, `exists_criticalDatumPath'`, and
`rcritical1_of_classical'`, with no `CriticalDatumInputs`, `hcrit`, or momentum
hypothesis. The last theorem includes the genuine `HasDerivAt` statement for
the squared critical norm and lane 214's exact inequality.

| S1 sub | result | supplier |
|---|---|---|
| S1a pairing identities | DONE: Laplacian symbol, pressure orthogonality, derivative pairing | lanes 175, 216; unconditional carrier from 219 |
| S1b trilinear estimate | DONE: physical fractional Parseval and the exact shifted-field bridge | lanes 182, 191, 214 |
| S1c force term | DONE: half-order Hilbert Cauchy–Schwarz | lane 175; slice data from 216 |
| S1d differentiability | DONE: chosen half-order trajectory is smooth; its derivative is the momentum datum | lane 219 |

The time bridge uses lane 215's local-carrier covering/uniqueness argument,
reproduced in a separate namespace because its module is absent from this
baseline. At order two, `A04.momentum_datum` identifies the derivative with
the physical residual. The bounded Bessel-to-homogeneous map composed with
order lowering transports both smoothness and momentum to the chosen
half-order trajectory, using D01 homogeneous uniqueness.

This closes S1/G7, not the time-integrated force obligations of G2/G3/G4.
Lane 216's G3 slicewise note below remains unchanged. See
`ATTEMPTS_CRITICAL_MOMENTUM.md` and `REPORT_219.md`.

### S2 — regularized division + continuity bootstrap (M; **a=0 closed by reuse**)

`04-whole-space.tex:100-104`: on `y ≤ ν/(2C₀)`, regularize by `(y²+ζ²)^{1/2}`, `ζ↓0`,
gives `y(t) ≤ y(0) + ∫₀ᵗ b`; with `c < 1/(4C₀)` the gate holds throughout by continuity.

**Already in the tree, domain-agnostic — reuse, do not reprove:**

| supplier | file:line | covers |
|---|---|---|
| `NSFormalization.Paper1.sqrt_energy_le_primitive` | `Paper1/ScalarEnergy.lean:22` | `E' ≤ 2b√E ⟹ √E ≤ N`, `E(0)=N(0)=0` |
| `NSFormalization.Paper1.continuous_bootstrap` | `:85` | first level-crossing / continuity bootstrap |
| `NSFormalization.Paper1.critical_norm_bound` | `:123` | **full** `a=0` bootstrap; its `henergy` **is** eq:Rcritical1 verbatim |
| `NSFormalization.Section4.C01.sqrt_energy_le_primitive'` | `Section4/C01/EnergyBounds.lean:179` | the `E(0)/N(0)`-arbitrary generalization for **general `a`** |

Delivered here: `NSFormalization.Section4.R43.criticalNormBound_radius` (`Pieces.lean`)
packages `critical_norm_bound` with the `ν`-free arithmetic `K = ν/(2C₀)`, `ρ = c·ν`,
discharging `C₀·K ≤ ν/2` and `ρ < K` from `0 < c < 1/(2C₀)`. Conclusion `y(t) ≤ c·ν`
on `[0,T]`. **G4 CLOSED (221)**: `ForcePath.lean` proves continuity of
`criticalForceAt`, interval integrability, and continuity/FTC/monotonicity of
`criticalForcePrimitive`. `critical_bootstrap_zero_datum` wires these facts to
lane 219's unconditional energy inequality and `criticalNormBound_radius`,
proving `criticalNormAt w.velocity t ≤ c * ν` on every `[0,S]` with `S < T`.
No extra analytic hypothesis remains for the zero-datum bootstrap. The strict
lifespan restriction reflects that a classical solution is defined on `[0,T)`.
General-`a` bootstrap (`y(0)≠0`) still needs `sqrt_energy_le_primitive'` and
`continuous_bootstrap` with `ρ = y(0)+∫b` (not wrapped here).

### S3 — `‖u‖₃ ≤ C(1/2)·y` and the second-shrinking gate discharge (G8 done; A05 field draft-only)

`04-whole-space.tex:93,112`. Two parts:

* **The embedding** `‖u‖₃ ≤ C(1/2)·y`: A05 `velocityCriticalL3`
  (`research/A05/Spec.lean:366`), `eLpNorm u 3 ≤ ENNReal.ofReal (C (1/2)) · dotHomogeneousENorm (1/2) u`.
  **Draft-only, unregistered** (registered A05 = `gradientLSix` only). Gap: A05 V2
  registration + its Fourier proof (A05 units U1–U8). **Blocks proving.** Size: external (A05 lane).
* **The gate discharge** (G8, "nothing owed"): from `y ≤ cν`, `‖u‖₃ ≤ Cemb·y`, and the
  `ν`-free `C₁·Cemb·c ≤ 1/4`, derive C01's gate
  `ENNReal.ofReal C₁ · criticalL3 (u t) ≤ ENNReal.ofReal (ν/4)`
  (`research/C01/Spec.lean:532,576`). **CLOSED this lane**:
  `criticalL3_gate_enorm` (ℝ≥0∞, exact C01 shape), `criticalL3_gate_real` (ℝ), and
  `exists_critical_radius` (one `c` below both `1/(4C₀)` and the gate threshold).

### S4 — finite H² integral through the maximal endpoint: **CLOSED (223)**

`maximal_h2TimeIntegral_zero_of_small_force` (namespace R43, module
`Endpoint`) supplies the explicit zero-datum bound for every `0 < S` with
`ofReal S ≤ maximalLifespanR ν 0 f`:

`ofReal (32 * S * C01.forcePrimitive f S ^ 2 +
32 * (ν⁻¹)^2 * ∫ t in 0..S, C01.l2Sq (C01.slice f t))`.

It uses the already present `MaximalEndpoint.maximal_h2TimeIntegral` theorem,
which applies `C01.h2TimeIntegral_Ioc` with the **same terminal S budget** to
all strictly shorter intervals and takes their directed union. The endpoint
value of the velocity is never evaluated. C01 V4 is registered; the previous
“draft-only” description was obsolete. G6 converts the real square to A04's
natural square. `maximal_squaredHTwoIntegral_of_small_force` is unconditional
under positive viscosity, force membership, maximality and homogeneous force
smallness.

### S5 — continuation: **CLOSED (223, using 217)**

`A02.exists_maximal'` supplies a maximal family. The exact lane 217 theorem
`A04.lifespanInfiniteOfLocallyFinite_of_memForceR'` consumes that family and
`∀ S, 0 < S → ofReal S ≤ maximalLifespanR ν a f → squaredHTwoIntegral S u ≠ ⊤`.
S4 supplies its last premise, including finite maximal S. No additional
analytic hypothesis remains. This checkout lacked lanes 215/217's two A04
files; they are included unchanged from local lane 217 commit
`d6f9cfd605041cb015a2119d351b6d77578c6b18`, without a merge or rebase.

### S6 — `inhomogeneousAtZero`: **CLOSED (223)**

`inhomogeneousAtZero_of_memForceR` proves the exact `Spec.lean:243–247` shape
with the explicit positive radius
`criticalConst = min (1/(8*trilinearConst))
(1/(4*(A05.gradientL6Const*A05.criticalL3Const)))`.
The smallness norm is the registered datum-path **inhomogeneous**
`forceSobolevENormL1 (1/2)`. The stronger
`homogeneousAtZero_of_memForceR` is proved first; lane 221's exact G2 inequality
then derives the spec theorem. General nonzero initial data (`universal`) and
registration of a complete `RCritical1API` remain outside this lane.

---

## 2. Gap ledger (G1–G8), with size, owner, blocks

| id | owner | blocks | status this lane | size |
|---|---|---|---|---|
| **G1** | D01 / A05 | **stating** | open — `Data.dotHomogeneousENorm` absent; `Spec.lean` carries a local `def` | S (promote a `def` to a registered contract) |
| **G2** | A05 / D01 | proving S6 | **CLOSED (221)** — contractive map and comparison of measurable path infima | DONE |
| **G3** | D01 | **content** (non-vacuity) | **CLOSED (221)** — canonical measurable `L¹_t Ḣ^{1/2}` path and finite homogeneous force norm | DONE |
| **G4** | C01 | proving S2 | **CLOSED (221)** — critical force continuity, interval integrability, primitive continuity and FTC | DONE |
| **G5** | C01 / R43 | proving S4→S5 | **CLOSED (223 wiring)** — existing `MaximalEndpoint` directed-union bound, now with absorption discharged | DONE |
| **G6** | A04↔C01 | proving S4 | **CLOSED** — `enorm_npow_two_eq_rpow_two` | S (done) |
| **G7** | R43 | proving S1 | **CLOSED (219)** — unconditional eq:Rcritical1 and smooth critical path for positive-viscosity classical solutions | DONE |
| **G8** | A05↔C01 | nothing | **CLOSED** — `exists_critical_radius`, `criticalL3_gate_real`, `criticalL3_gate_enorm` | S (done) |

Historical registration prerequisites above no longer block the zero-datum proof.
Lane 223 consumes proved implementation theorems and the registered C01 V4
implementation; it does not register the complete R43 API.

---

## 3. What closed in Lean this lane

`formalization/NSFormalization/Section4/R43/Pieces.lean` (built silent, standard 3 axioms):

| decl | row / gap | statement |
|---|---|---|
| `enorm_npow_two_eq_rpow_two` | G6 (S4) | `∀ x : ℝ≥0∞, x ^ (2:ℕ) = x ^ (2:ℝ)` |
| `exists_critical_radius` | G8 (S3) | `∃ c>0, c < 1/(4C₀) ∧ C₁·Cemb·c ≤ 1/4` |
| `criticalL3_gate_real` | G8 (S3) | real absorption-gate discharge `C₁·‖u‖₃ ≤ ν/4` |
| `criticalL3_gate_enorm` | G8 (S3) | ℝ≥0∞ gate `ofReal C₁ · L3 ≤ ofReal (ν/4)`, exact C01 shape |
| `criticalNormBound_radius` | S2 (a=0) | eq:Rcritical1 ⟹ `y(t) ≤ cν` on `[0,T]`, via `Paper1.critical_norm_bound` |

Historical blocked rows, with S1/G7 now closed by lane 219: S2 general-a
(G4), S3 embedding (A05 V2), S4 (C01 V4 + G5), S5 (A04 V3), S6 (G2 + G3).
