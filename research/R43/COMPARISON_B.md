# R43 — Proposition 4.3 (`prop:Rcritical1`) — comparison / provenance (draft B)

Statement: `paper/sections/04-whole-space.tex:82-89`; proof `:90-132`.
Ledger: `research/section4/STATEMENTS.md` §3 (`:428-563`); R41 consumption `:128-133`.
Structure delivered: `BlowupDensity.R43.DraftB.RCritical1API` in `DraftB.lean`
(typechecks; `lake env lean ../research/R43/DraftB.lean` → exit 0).

The R43 deliverable is the **statement** of Prop 4.3, not its proof. The
structure carries only what Prop 4.3 asserts (a universal `c`, the two
conclusion clauses), because a spec that added the consumed sibling clauses as
hypotheses would state something weaker than the manuscript's theorem. The
consumed clauses are analysed here (deliverable 2), not inlined as fields.

---

## 1. Field-by-field provenance

| field | paper line | consumed from | existing Lean (`formalization` / `vendor`) | gap |
|---|---|---|---|---|
| `c`, `hc` (`c : ℝ`, `0 < c`) | `04-whole-space.tex:82-83` "universal `c > 0`" | — (R43 owns; universal-const discipline `STATEMENTS.md:483-485`) | torus precedent `Paper1/PeriodicCriticalRegularity.lean:64-65` `CriticalRegularityCertificate.radius`,`.radius_pos`; unpacked by `exists_critical_regularity_constant:72` to `∃ c, 0<c ∧ …` | none for the field itself; the *value* `c ≤ min(1/(4C₀), 1/(4·C01.C₁·A05.C(1/2)))` is fixed in the proof (unit U5), not the statement |
| `universal` conclusion `maximalLifespanR ν a f = ⊤` | `:86` `T^ν_{max,ℝ}(a,f)=∞` | `Data.maximalLifespanR` (`Data.lean:657`), `= ⊤` | torus analog `Paper1/PeriodicLifespan.lean:27` `lifespan … = ⊤`; whole-space `maximalLifespanR` is canonical (D01) | none — `⊤` is unreachable by a finite horizon, so not vacuously satisfiable |
| `universal` datum norm `‖a‖_{Ḣ^{1/2}}` | `:85` | `DraftB.dotHalfSpatialENorm` = `⟪A05:dotHomogeneousENorm⟫ (1/2)` (`research/A05/Spec.lean`), built on `Data.IsHomogeneousSliceDatum` (`Data.lean:364`) | `Data.dotHHalfENorm`/`homogeneousFourierENorm` (`Data.lean:410,427`) exist but are Fourier-integral form, **junk `0` off `L¹∩L²`** (`Data.lean:406-409`); building blocks `IsHomogeneousSliceDatum`, `homogeneousVectorENorm` (`Data.lean:349,364`) exist | **GAP-1** (see §3): the honest datum-form spatial `Ḣ^s` norm is not in `Data.lean`; only A05 (`research/`, not importable) has it, so DraftB inlines it |
| `universal` force norm `‖f‖_{L¹(0,∞;Ḣ^{1/2})}` | `:85` | `Data.forceHomogeneousENorm 1 (1/2) f` (`Data.lean:390`) | canonical (D01); torus force metric `Paper1/…forceDistance` is the analog | none |
| smallness `… < cν` (strict, in `ℝ≥0∞`) | `:85-86` | `ENNReal.ofReal (c*ν)` | `Paper1/PeriodicCriticalRegularity.lean:66-68` uses the identical `< ENNReal.ofReal (radius*ν)` spelling | none |
| `inhomogeneousAtZero` (a=0, inhom. `H^{1/2}`) | `:87-88`, consumed at `:179` | `Data.forceSobolevENormL1 (1/2) f` (`Data.lean:231`), `maximalLifespanR ν (fun _=>0) f = ⊤`, zero datum `Data.breakdownSetRZero:687` | torus twin: `CriticalRegularityCertificate.global_lifespan` (`Paper1/PeriodicCriticalRegularity.lean:66-68`) — **same shape**, torus domain | none; must reuse the **same** `c` as `universal` (enforced by being one field) |

Whole-space Prop 4.3 itself has **no existing formalization**; the closest
artifact in tree is the torus (Paper 1) `CriticalRegularityCertificate`, which
is structurally identical for the `a=0` clause but built on periodic objects
(`PeriodicFrequency`, `TestForce`, periodic `lifespan`) and lacks the general-`a`
`universal` clause that is the whole-space novelty here.

---

## 2. Bounded unit split for the eventual R43 proof lane (8 units)

Units are proof steps (this deliverable is the statement only). Sizes S/M/L.

| unit | content | size | reuse / blocked on |
|---|---|---|---|
| **U1** norm plumbing | identify `dotHalfSpatialENorm = A05.dotHomogeneousENorm (1/2)`; define real slice quantities `y(t)=‖u(t)‖_{Ḣ^{1/2}}`, `z(t)=‖u(t)‖_{Ḣ^{3/2}}`, `b(t)=‖f(t)‖_{Ḣ^{1/2}}` as `.toReal` of datum norms; `∫₀ᵗ b` vs `forceHomogeneousENorm 1 (1/2)` interval identity | S | blocked on **GAP-2** (slicewise-`Ḣ^{1/2}` force integrability) |
| **U2** eq:Rcritical1 (`:97`) | test projected eq against `Λu`, using `⟪A05:velocityCriticalL3⟫` and `⟪A05:derivativeCriticalL3⟫`, to get `½(y²)′+(ν−C₀y)z² ≤ by`; needs differentiability of `y²` (R43-owned smooth-critical-path input, **GAP-3**) | L | R43-owned; C01 explicitly excludes eq:Rcritical1 |
| **U3** regularized propagation (`:100`) | `(y²+ζ²)^{1/2}`, `ζ↓0` on `{y ≤ ν/(2C₀)}` gives `y(t) ≤ y(0)+∫₀ᵗ b` | M | reuse `Paper1/ScalarEnergyContinuation.lean:21` `continuation_packet_bound` (scalar `E′+2νd ≤ 2b√E, E 0=0 ⟹ E+2ν∫d ≤ (∫b)²`) |
| **U4** continuity bootstrap (`:102-104`) | `c<1/(4C₀)`, `y(0)+∫b < cν < ν/(4C₀)` propagate `y ≤ ν/(2C₀)` through the lifespan (first-exit) | M | reuse `Paper1/ScalarEnergyContinuation.lean:13` `continuation_certificate` (continuous bootstrap) |
| **U5** absorption threshold (`:112`) | from `y ≤ cν` and `⟪A05:velocityCriticalL3⟫` (`‖u‖₃ ≤ A05.C(1/2)·y`), shrink `c` so `C01.C₁·‖u‖₃ ≤ ν/4` on the lifespan (constant threading A05↔C01, both `ν`-free) | S | needs `A05.C`, `C01.C₁` exposed (they are) |
| **U6** local `∫₀ˢ‖u‖²_{H²}<∞` (`:113-130`) | feed `⟪C01:l2Bound⟫`/`⟪C01:enstrophyIntegralBound⟫`/`⟪C01:h2TimeIntegral⟫` (with U5 absorption) at interior `S`, then glue to endpoint `S=T_max` by monotone convergence (finite `K(T_max)`, `∫₀^{T_max}‖f‖₂²` from `f∈𝓕_ℝ`, `:171`); bridge `sobolevENorm 2 _ ^(2:ℕ)` (A04) ↔ `^(2:ℝ)` (C01) | M | **GAP-4** (endpoint) + **GAP-5** (pow spelling) |
| **U7** global regularity ⇒ `universal` | assemble `⟪A02:exists_maximal⟫` (`0<T_max` + family) with `⟪A04:lifespanInfiniteOfLocallyFinite⟫` fed U6 ⟹ `maximalLifespanR ν a f = ⊤` | S | A02, A04 both provide the exact shapes |
| **U8** `inhomogeneousAtZero` | specialize U7 to `a=0`: `‖0‖_{Ḣ^{1/2}}=0`, `0∈𝒳_ℝ`, `‖f‖_{L¹ₜḢ^{1/2}} ≤ ‖f‖_{L¹ₜH^{1/2}}` (`:132`) | S | reuse `Paper1/PeriodicCriticalRegularity.lean:47` `forceDistance_order_mono` pattern |

---

## 3. Clauses R43 needs from A04 / C01 / A02 / A05 that the specs do **not** provide

Direct DAG children `R43 ← A04, A05, C01`; A02 enters transitively (A04's
continuation clause takes the maximal-solution family as a hypothesis).

### Provided, exact-shape match (no gap)
* **A02** `MaximalSolutionAPI.exists_maximal` (`research/A02/Spec.lean:423`) →
  `IsMaximalSolution` (`:210`) gives `0 < maximalLifespanR` **and** the family
  `∀ S, 0<S → ofReal S < T_max → ∃ w, w.velocity=u ∧ w.pressure=p`, which is
  *literally* the family hypothesis of A04's `lifespanInfiniteOfLocallyFinite`.
* **A04** `ContinuationAPI.lifespanInfiniteOfLocallyFinite`
  (`research/A04/Spec.lean:658-665`): hypotheses `0<ν, a∈𝒳_ℝ, MemForceR f,
  MemL1Hm f, 0<T_max`, family, and `∀ S, 0<S → ofReal S ≤ T_max →
  squaredHTwoIntegral S u ≠ ⊤`; conclusion `T_max = ⊤`. Exactly R43's closing
  step (`04-whole-space.tex:121,132`). `MemL1Hm` is free from `MemForceR`.
* **C01** `EnergyAbsorptionAPI.{l2Bound, enstrophyIntegralBound, h2TimeIntegral}`
  (`research/C01/Spec.lean:389,538,582`): eq:RL2, eq:RH1, and the assembly, each
  gated by the absorption hypothesis `ENNReal.ofReal C₁ · criticalL3(u(t)) ≤
  ENNReal.ofReal (ν/4)` — exactly the smallness U5 supplies. `C01.criticalL3 =
  eLpNorm _ 3` equals A05's `velocityCriticalL3` left side, and its right side
  `dotHomogeneousENorm (1/2)` equals DraftB's `dotHalfSpatialENorm`, so the chain
  is type-consistent end to end.
* **A05** `CriticalEmbeddingAPI.{velocityCriticalL3, derivativeCriticalL3,
  gradientLSix}` (`research/A05/Spec.lean`): `‖u‖₃ ≤ Cy`, `‖∇u‖₃+‖Λu‖₃ ≤ Cz`,
  `‖∇u‖₆ ≤ C‖Δu‖₂` — all three R43 needs, with `ν`-free constants.

### Gaps — clauses R43 needs that are **absent** from the current specs

* **GAP-1 (D01 / A05).** The honest **datum-form spatial `Ḣ^s` norm** for `H^∞`
  fields is not in `Data.lean`: its `dotHHalfENorm` is the Fourier-integral form,
  junk `0` off `L¹∩L²` (`Data.lean:406-409`), so it cannot be used for
  `‖a‖_{Ḣ^{1/2}}` with a general `a ∈ 𝒳_ℝ`. Only A05's `dotHomogeneousENorm`
  (a `research/` draft, not importable) is honest. DraftB inlines the definition;
  the reconciliation should promote it into `Data.lean` or A05's registered
  contract. Without it Prop 4.3's `universal` cannot be *stated* faithfully.
* **GAP-2 (C01, or a new bridge).** eq:Rcritical1 and its propagation need
  `b(t)=‖f(t)‖_{Ḣ^{1/2}}` as a real function, interval-integrable on `[0,t]`,
  with `∫₀ᵗ b = ‖f‖_{L¹(0,t;Ḣ^{1/2})}`. C01's `forceTimeRegularity`
  (`C01/Spec.lean:332`) supplies this only for the **`L²`** slice norm, not for
  the homogeneous `Ḣ^{1/2}` slice norm. No sibling provides slicewise `Ḣ^{1/2}`
  force integrability. Needs a new bridge (natural home: C01, mirroring
  `forceTimeRegularity`, or A05).
* **GAP-3 (R43-owned, no sibling).** eq:Rcritical1 (`:97`) — the critical
  `Ḣ^{1/2}` energy inequality from testing against `Λu` — and the
  differentiability of `s ↦ y(s)²` are **R43's own** and provided by no sibling
  (C01's docstring explicitly declares eq:Rcritical1 out of scope). R43 will need
  a `HasSmoothCriticalPath`-style differentiability input, the critical analog of
  A04's `HasSmoothSobolevPath` (`A04/Spec.lean:248`); A01 gives smooth Sobolev
  datum paths, but no lane currently exports a differentiable `Ḣ^{1/2}`/`Ḣ^{3/2}`
  path. This is the substance R43 owns; it belongs in R43's proof lane.
* **GAP-4 (C01 endpoint).** A04's `lifespanInfiniteOfLocallyFinite` needs
  `squaredHTwoIntegral S u ≠ ⊤` at `S = T_max` (the finite supremum being
  excluded), but C01's `h2TimeIntegral` is stated per solution `w` on a **fixed**
  horizon `T` with `S ≤ T`, and no solution reaches `T = T_max`. R43 must glue
  the interior bounds (`S < T_max`) to the endpoint by monotone convergence,
  using that C01's RHS `Cassembly·S·K(S)² + … + Cassembly·ν⁻²∫₀ˢ‖f‖₂²` is finite
  at `S = T_max` (`K` and `∫‖f‖²` finite because `f ∈ 𝓕_ℝ`, `04-whole-space.tex:171`).
  This is R43-owned gluing, **not** a false C01 statement; a C01 endpoint
  corollary (`S ≤ T`, taking the sup) would remove the friction but is not
  required.
* **GAP-5 (A04 ↔ C01 power spelling).** A04's `squaredHTwoIntegral`
  (`A04/Spec.lean`) uses `sobolevENorm 2 _ ^ 2` (nat pow); C01's `h2TimeIntegral`
  bounds `sobolevENorm 2 _ ^ (2:ℝ)` (rpow). Composing C01's finiteness into A04's
  hypothesis needs the elementary `ℝ≥0∞` identity `x^(2:ℕ) = x^(2:ℝ)`. A
  one-line bridge; flagged so the reconciliation pins one spelling.

---

## 4. Notes for reconciliation with draft A

* Norm choice for `‖a‖_{Ḣ^{1/2}}` is the single most consequential decision: the
  Fourier-form `Data.dotHHalfENorm` makes `universal` **false**; the datum-form
  (`dotHalfSpatialENorm` here) makes it true. Whichever draft used the datum form
  is correct; GAP-1 must be resolved in `Data.lean`/A05 before registration.
* Whether to keep `inhomogeneousAtZero` as a separate field (draft B does, per
  the ledger skeleton `STATEMENTS.md:509-521` and R41's direct consumption) or
  derive it — draft B keeps it, same `c`.
* Draft B does **not** carry C₀/C₁ or the consumed clauses as structure fields
  (the contract exposes only `c`); if draft A carries a richer "proof interface"
  structure, that is a superset and the two are reconcilable by projection.
