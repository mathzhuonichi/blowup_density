# R43 — Proposition 4.3 proof-route split (`prop:Rcritical1`)

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

### S1 — eq:Rcritical1: the critical energy inequality (G7, R43-owned, L)

`04-whole-space.tex:97-99`. Testing the projected equation against `Λu`:
`½(y²)' + (ν − C₀y)z² ≤ by`. **Blocks proving.** No sibling owns it (C01 declares
it out of scope). Needs a differentiable critical path — a `HasSmoothCriticalPath`
analogue of A04's `HasSmoothSobolevPath` (`research/A04/Spec.lean:247`) at orders
`1/2`, `3/2`; no lane exports one. Sub-split (all R43-owned):

| S1 sub | Lean shape (informal) | supplier | size |
|---|---|---|---|
| S1a pairing identities | **DONE, conditional on `hcrit` carrier data** in `Section4/R43/CriticalPairing.lean`: `⟪Δ_{1/2},A_{1/2}⟫ = -‖A_{3/2}‖²`, `⟪P_{1/2},A_{1/2}⟫ = 0`, and `(y²)' = 2⟪A_{1/2},A'_{1/2}⟫`; the first is proved componentwise from the Fourier symbols and the second through `A04.inner_lerayComplement_eq_zero_of_eq_zero` | R43-own; carrier bridge remains in named `CriticalDatumPath` hypothesis | M |
| S1b trilinear estimate | `|⟨(u·∇)u, Λu⟩| ≤ C₀·y·z²` | R43-own, via A05 `velocityCriticalL3` + `derivativeCriticalL3` (both **draft-only**) | L |
| S1c force term | **DONE** in `Section4/R43/CriticalPairing.lean`: `|⟪F_{1/2},A_{1/2}⟫| ≤ ‖F_{1/2}‖‖A_{1/2}‖ = b y`, by real Hilbert-space Cauchy--Schwarz and homogeneous-datum uniqueness | R43-own | S |
| S1d differentiability of `y²` | **IDENTITY SHAPE DONE, carrier still a gap**: `criticalEnergyPath` defines `t ↦ ‖A_{1/2}(t)‖²`; `criticalEnergyPath_eq` identifies it with `y(t)²`, and `criticalEnergyDerivative_hasDerivAt` derives `HasDerivAt (fun r => criticalNormAt u r ^ 2) (2⟪A,A'⟫) t` from `hcrit.velocityHalf_smooth`; constructing that smooth homogeneous path from `ClassicalSolutionR` remains a later lane | R43-own smooth critical path (named field of `CriticalDatumPath`) | M |

Lane 175 also closes the S1 scalar assembly:
`rcritical1_of_trilinear` produces
`E'/2 + (ν - C₀*y)*z^2 ≤ b*y` on `Ioo 0 T`, in the literal `henergy`
shape consumed by `criticalNormBound_radius`, conditional only on the named
carrier hypothesis `hcrit : CriticalDatumPath w hf` and the separate S1b
hypothesis `htri : CriticalTrilinearEstimate (C₀ := C₀) hcrit` (besides the
ambient force-membership witness `hf`).
| S1a pairing identities | `⟨∂_t u, Λu⟩ = ½(y²)'`, `ν⟨−Δu,Λu⟩ = νz²`, `⟨∇p,Λu⟩ = 0` (Leray) | R43-own; pressure orthogonality via `A02`/`D01` Leray | M |
| S1b trilinear estimate | `|⟨(u·∇)u, Λu⟩| ≤ C₀·y·z²` | **Lane 182 conditional estimate + lane 191 shifted carrier complete:** `R43.criticalAdvectionLpBridge_shifted hcrit` now supplies the physical `Λu`, its `MemHInfty` closure, and the three exact half-order derivative data at every interior time. The sole remaining field of `CriticalAdvectionLpBridge hcrit` is `pairing_identity`, the fractional Parseval/duality identity equating the datum pairing with the physical integral. | L → one Parseval lemma |
| S1c force term | `|⟨f, Λu⟩| ≤ b·y` (Cauchy–Schwarz in `Ḣ^{1/2}`) | R43-own | S |
| S1d differentiability of `y²` | `HasDerivAt (fun s => (y s)^2) (E' s) s` | R43-own smooth critical path (gap) | M |

The **scalar consequence** of S1 (`E'/2 + (ν−C₀y)z² ≤ by`) is exactly the `henergy`
hypothesis of the tree's scalar bootstrap (see S2), so once S1 is proved, S2 is free.

Lane 182's `criticalTrilinearEstimate_of_hcrit` and `rcritical1_of_hcrit` are
conditional on `CriticalAdvectionLpBridge hcrit`. Lane 191 constructs its
entire `shifted` field in `Section4/R43/ShiftedData.lean`; the only remaining
field is the separate fractional Parseval statement `pairing_identity`.
That hypothesis contains no `L³` or trilinear bound. See `ATTEMPTS_S1B.md` and
`../A05/ATTEMPTS_U4_U8.md` for the exact boundary.

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
on `[0,T]`. **Remaining gap G4** (owner C01, M): the forcing primitive `N t = ∫₀ᵗ b`
must be continuous with FTC derivative `b(t) = ‖f(t)‖_{Ḣ^{1/2}}` — C01's
`forceTimeRegularity` (`research/C01/Spec.lean:326`) supplies this for the **L²** slice
only, not the homogeneous critical slice. General-`a` bootstrap (`y(0)≠0`) needs
`sqrt_energy_le_primitive'` + a re-run of `continuous_bootstrap` with `ρ = y(0)+∫b`
(not yet wrapped; R43-own, S). **Blocks proving** general-a; a=0 closable modulo G4+S1.

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

### S4 — `∫₀ˢ‖u‖²_{H²} < ∞` for every finite `S ≤ T_max` (C01 assembly, **draft-only → C01 V4**)

`04-whole-space.tex:118-131`. C01's `h2TimeIntegral` (`research/C01/Spec.lean:576`)
gives `∫⁻ Ioo 0 S, sobolevENorm 2 (u t) ^ (2:ℝ) ≤ ENNReal.ofReal (…)` under the gate
of S3, per `w : ClassicalSolutionR ν a f T`, `0 < S ≤ T`. **NOT registered** (C01 V3
scope disclosure 5 lists it out of scope). It is a **C01 V4 item**, together with its
inputs `enstrophyIntegralBound` (eq:RH1) and `sobolevTwoFourier`, all draft-only.

Two further gaps:
* **G5** (owner C01 endpoint, or R43 gluing, M): `h2TimeIntegral` is per fixed-horizon
  `ClassicalSolutionR` with `S ≤ T`; A04's closing clause instantiates at `S = T_max`,
  where no such solution exists. R43 can glue by monotone convergence (RHS monotone in
  `S`, finite at `T_max` since `f ∈ 𝓕_ℝ`), or C01 adds an endpoint corollary.
* **G6** (power spelling, one line): `squaredHTwoIntegral` (A04, `^(2:ℕ)`) vs
  `h2TimeIntegral` (C01, `^(2:ℝ)`). **CLOSED this lane**: `enorm_npow_two_eq_rpow_two`
  (`x ^ (2:ℕ) = x ^ (2:ℝ)` in `ℝ≥0∞`).

**Blocks proving.**

### S5 — `lifespanInfiniteOfLocallyFinite` fed the maximal family ⟹ `T_max = ⊤` (A04, **draft-only → A04 V3**)

`04-whole-space.tex:132`, "Proposition 2.1 excludes every finite maximal lifespan."
A04 `lifespanInfiniteOfLocallyFinite` (`research/A04/Spec.lean:657`): from `0 < T_max`,
the presingular solution family, and `∀ S, 0<S → ofReal S ≤ T_max → squaredHTwoIntegral S u ≠ ⊤`
(supplied by S4), concludes `maximalLifespanR ν a f = ⊤`. **NOT registered** (registered
A04 V2 stops at `highContinuationIntegral`). An **A04 V3 item**.

* The maximal family (`exists_maximal`, `IsMaximalSolution`, `presingularTimes`):
  **REGISTERED** in `A02.maximal_partial_v2` (V2 `MaximalPartial`). This is the one
  fully-registered input on the closing path.
* The `≠ ⊤` hypothesis comes from S4; the power spelling from G6 (done).

**Blocks proving** (needs A04 V3 registration + wiring S4→S5).

### S6 — `inhomogeneousAtZero`: the `a = 0` clause R41 consumes (G2 + G3 + reduction)

`04-whole-space.tex:88,132`. `‖f‖_{L¹(0,∞;H^{1/2})} < cν ⟹ T^ν_{max,ℝ}(0,f) = ∞`.
Reduction from `universal` at `a = 0`:

* `dotHomogeneousENorm (1/2) (fun _ => 0) = 0` and `(fun _ => 0) ∈ initialClassR`
  (R43-own, S; needs the local `def` of G1).
* **G2** (owner A05 or D01, M, **new gap**): time-integrated monotonicity
  `∀ f, MemForceR f → forceHomogeneousENorm 1 (1/2) f ≤ forceSobolevENormL1 (1/2) f`
  (`:132` "`‖f‖_{Ḣ^{1/2}} ≤ ‖f‖_{H^{1/2}}`"). A05 owns only the *spatial slice* form
  (`research/A05/Spec.lean:268`); both `Data` force norms are infima over datum **paths**,
  so the bridge must carry an `IsHomogeneousPath` from an `IsSobolevPath` with
  `‖G' t‖ ≤ ‖G t‖`. Unregistered, unowned. **Blocks proving** the reduction.
* **G3** (owner D01, non-vacuity, blocks **content**): `forceSobolevENormL1 (1/2) f ≠ ⊤`
  and `forceHomogeneousENorm 1 (1/2) f ≠ ⊤` for `f ∈ 𝓕_ℝ`. `MemForceR` gives datum
  paths at **integer** orders only; both norms are infima over order-`1/2` paths, so
  both may be `⊤` and both conclusion fields **vacuously true**. `DatumLemmas.lean:160`
  gives slicewise data at every real order but not the measurable **path**;
  `compact_exists_homogeneousPath` (`DatumLemmas.lean:483`) covers only compactly
  supported `f`. Not closable for general `f` on current defs; needs a D01 order-`1/2`
  path constructor. **Blocks the statement's content** (not its well-formedness).

**Blocks proving + content.**

---

## 2. Gap ledger (G1–G8), with size, owner, blocks

| id | owner | blocks | status this lane | size |
|---|---|---|---|---|
| **G1** | D01 / A05 | **stating** | open — `Data.dotHomogeneousENorm` absent; `Spec.lean` carries a local `def` | S (promote a `def` to a registered contract) |
| **G2** | A05 / D01 | proving S6 | open — new; path-level force-norm monotonicity | M |
| **G3** | D01 | **content** (non-vacuity) | open — order-`1/2` force datum *paths* for general `f` | M–L |
| **G4** | C01 | proving S2 | open — homogeneous critical-slice force integrability | M |
| **G5** | C01 / R43 | proving S4→S5 | open — `S = T_max` endpoint gluing (monotone convergence) | M |
| **G6** | A04↔C01 | proving S4 | **CLOSED** — `enorm_npow_two_eq_rpow_two` | S (done) |
| **G7** | R43 | proving S1 | open — eq:Rcritical1 + differentiable critical path; largest R43 unit | L |
| **G8** | A05↔C01 | nothing | **CLOSED** — `exists_critical_radius`, `criticalL3_gate_real`, `criticalL3_gate_enorm` | S (done) |

Plus the **three registration prerequisites** (not "gaps" in COMPARISON's sense but
hard blockers to proving): A05 V2 (`velocityCriticalL3`), C01 V4 (`h2TimeIntegral` +
eq:RH1 + `sobolevTwoFourier`), A04 V3 (`lifespanInfiniteOfLocallyFinite`).

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

Blocked rows (need external registration or an R43-owned L unit): S1 (G7), S2 general-a
(G4), S3 embedding (A05 V2), S4 (C01 V4 + G5), S5 (A04 V3), S6 (G2 + G3).
