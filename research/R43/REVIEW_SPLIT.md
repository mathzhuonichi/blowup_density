# REVIEW — lane 159-R43-split (opus reviewer, 2026-09-14)

Worktree `.claude/worktrees/159-R43-split`, branch `erenup/159-R43-split`, HEAD `e58b056`.
Read-only review; no edits to lane files, no git state changes.  Probes written to
`research/R43/probes/rev159_*.lean` (new files only).

**Verdict: ACCEPT-WITH-NOTES.**  One exact one-line fix (N1, a wrong `file:line` for `C₁`);
everything else is a forward-looking note, not a defect.  The Lean is genuine, hygienic,
standard-3-axioms, non-vacuous, and survives five falsity probes.

---

## 1. What the lane claims

* A proof-route split of Proposition 4.3 (`prop:Rcritical1`, statement
  `paper/sections/04-whole-space.tex:82-89`, proof `:90-133`) into rows S1–S6 with
  suppliers, owners, sizes and blocks-stating/blocks-proving, plus the G1–G8 gap ledger
  carried over from `research/R43/COMPARISON.md` §4 — `research/R43/R43_SPLIT.md`.
* A **registration audit**: three sibling clauses R43's route quotes (A05
  `velocityCriticalL3`, C01 `h2TimeIntegral` + `enstrophyIntegralBound` + `sobolevTwoFourier`,
  A04 `lifespanInfiniteOfLocallyFinite`) are draft-only, unregistered; A02's maximal family
  and C01's eq:RL2 layer are registered.
* Three closed rows in Lean, `formalization/NSFormalization/Section4/R43/Pieces.lean`
  (165 lines, 5 theorems): **G6** power-spelling pin, **G8** radius shrinkings + absorption-gate
  discharge (real and `ℝ≥0∞`), **S2** `a = 0` bootstrap by reuse of
  `NSFormalization.Paper1.critical_norm_bound`.
* Conformance `research/R43/axioms_r43_pieces.lean` (5 `#print axioms` + 5 non-vacuity witnesses).

### 1a. Split-table fidelity — VERIFIED, no gaps, no invented steps

Paper line map re-derived from source (not copied from a previous review):
`:91-95` setup + Lemma B.1 embeddings → S1's inputs and S3; `:96-99` eq:Rcritical1 → **S1**;
`:100-104` regularized division + continuity bootstrap → **S2**; `:106-112` trilinear Hölder,
`‖∇u‖₆ ≤ C‖Δu‖₂`, "Decrease `c` so that `C₁y ≤ ν/4`" → **S3** (the gate half);
`:113-116` eq:RH1 and `:118-131` eq:RL2 → `K(S)` → Fourier inequality → `∫₀^S‖u‖²_{H²}` → **S4**;
`:132` first sentence (Prop 2.1 excludes a finite maximal lifespan) → **S5**; `:132` last sentence
(`‖f‖_{Ḣ^{1/2}} ≤ ‖f‖_{H^{1/2}}`) + `:88` → **S6**.  Every sentence of `:90-133` lands in exactly
one row; no row asserts a step the paper does not take.  Sizes/owners are plausible and consistent
with the gap ledger (S1 = G7 = L and R43-owned; S6 = G2+G3; S3/S4/S5 external).

Citations spot-checked and correct: `research/A04/Spec.lean:202` (`squaredHTwoIntegral`, `^ 2` = npow),
`:247` (`HasSmoothSobolevPath`), `:657` (`lifespanInfiniteOfLocallyFinite`);
`research/C01/Spec.lean:326` (`forceTimeRegularity`), `:532` (`enstrophyIntegralBound`),
`:555` (`sobolevTwoFourier`), `:576` (`h2TimeIntegral`), V3 "disclosure 5"
(`verification/Contracts/V3/EnergyAbsorptionPartial.lean:72-75`, verbatim "Out of scope");
`research/A05/Spec.lean:201` (`C : ℝ → ℝ`), `:268` (`homogeneousLeSobolev`), `:366` (`velocityCriticalL3`);
`research/A02/Spec.lean:421` (`exists_maximal`);
`formalization/NSFormalization/Paper1/ScalarEnergy.lean:22,85,123`;
`formalization/NSFormalization/Section4/C01/EnergyBounds.lean:179` (`sqrt_energy_le_primitive'`,
`hEN0 : √(E 0) ≤ N 0` — genuinely the general-`a` generalization);
`verification/Contracts/V1/DatumLemmas.lean:160` (`smoothJets_exists_datum`), `:483`
(`compact_exists_homogeneousPath`, compact support only).  G1–G8 in the split match
`research/R43/COMPARISON.md:107-114` one for one.

### 1b. Registration audit — INDEPENDENTLY CONFIRMED

`grep -rn` over `verification/` for the five names returns **only docstring/"NOT INCLUDED"
prose**, never a field:

| clause | registered? | evidence |
|---|---|---|
| A05 `velocityCriticalL3` | **NO** | `Contracts/V1/GradientL6.lean` fields = `Csix` (`:121`), `Csix_pos` (`:124`), `hessianLaplacianIdentity` (`:130`), `gradientLSix` (`:138`).  The only occurrence of the name in `verification/` is the docstring `Contracts/V1/EnergyAbsorptionPartial.lean:46` |
| C01 `h2TimeIntegral`, `enstrophyIntegralBound`, `sobolevTwoFourier` | **NO** | listed as out of scope in all three C01 scopes (`contracts.json:188,199,287`) and in `Contracts/V{1,2,3}/EnergyAbsorptionPartial.lean:{59-62, 63, 72}` |
| A04 `lifespanInfiniteOfLocallyFinite` | **NO** | zero hits in `verification/`.  Registered A04 = `Chigh`/`Chigh_pos`/`energyIdentityHigh` (V1 `:162,165,182`) + `Cgron`/`Cgron_pos`/`regularizedNormDerivative`/`highContinuationIntegral` (V2 `:199,204,221,250`) |
| A02 maximal family | **YES** | `A02.maximal_partial_v2`, `Contracts/V2/MaximalPartial.lean:139` `exists_maximal`, `:154` `maximal_unique` |
| `Data.dotHomogeneousENorm` (G1) | **ABSENT** | zero hits in `verification/`.  `Contracts/V1/Data.lean` has `homogeneousENorm` (`:338`, on `𝓢'`), `homogeneousVectorENorm` (`:352`), `IsHomogeneousSliceDatum` (`:367`), `homogeneousFourierENorm`/`dotHHalfENorm` (`:410,427`) — but no datum-infimum spatial homogeneous norm on a physical field |

26 contracts are registered on this branch; none of them carries any of the three clauses.

---

## 2. What is in Lean

`NSFormalization.Section4.R43` (`Section4/R43/Pieces.lean`), 5 theorems, all with the standard
three axioms and all instantiated by a non-vacuous witness in `axioms_r43_pieces.lean`:

* `enorm_npow_two_eq_rpow_two (x : ℝ≥0∞) : x ^ (2:ℕ) = x ^ (2:ℝ)` (`:62`).  **Genuine**: the proof is
  `rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]`, and `ENNReal.rpow_natCast`
  really is at `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:686` (the ATTEMPTS note that
  `…Pow.NNRpow` does not exist at this pin is also correct — that file is absent from the
  `Pow/` directory).  Instantiating `x := sobolevENorm 2 _` is exactly the A04 (`^ 2`, npow,
  `research/A04/Spec.lean:203`) ↔ C01 (`^ (2:ℝ)`, rpow, `research/C01/Spec.lean:582`) bridge.
* `exists_critical_radius` (`:75`): `0 < C₀ → 0 < C₁ → 0 < Cemb → ∃ c, 0 < c ∧ c < 1/(4*C₀) ∧ C₁*Cemb*c ≤ 1/4`,
  witness `c = min (1/(8C₀)) (1/(4·C₁·Cemb))`.  **`c` is `ν`-free: YES** — `ν` does not occur in the
  statement at all, so the `∃ c` is outside every `ν`, exactly as `04-whole-space.tex:83`
  ("There is a universal `c > 0`") demands.  This is the right spelling *because* the `ν` cancels:
  `C₁·Cemb·c·ν ≤ ν/4 ⟺ C₁·Cemb·c ≤ 1/4` for `ν > 0`.  Probe B2 proves that the alternative
  `ν`-carrying spelling `∀ ν > 0, C₁·Cemb·c·ν ≤ 1/4` is **unsatisfiable** by any `c > 0`.
* `criticalL3_gate_real` (`:98`) and `criticalL3_gate_enorm` (`:112`).  The `ℝ≥0∞` conclusion is
  `ENNReal.ofReal C₁ * L3 ≤ ENNReal.ofReal (ν / 4)`, which is **token-for-token** C01's gate
  hypothesis `ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤ ENNReal.ofReal (ν / 4)`
  (`research/C01/Spec.lean:536-537` inside `enstrophyIntegralBound`, `:580-581` inside
  `h2TimeIntegral`, `:514-515` inside `enstrophyDifferentialBound`) with
  `L3 := criticalL3 (slice w.velocity t)`.  No `.toReal` anywhere.
* `criticalNormBound_radius` (`:145`).  It **is** a reuse, not a reproof: the body is
  `exact NSFormalization.Paper1.critical_norm_bound hν.le hC₀.le (mul_nonneg hc0 hν.le) hρK hK hy hy0
  hynonneg hN hN0 hNbound hb hdE hdN henergy` (`:162-163`), i.e. every hypothesis is passed
  through and the only R43 content is `hK : C₀*(ν/(2C₀)) ≤ ν/2` and `hρK : c*ν < ν/(2C₀)`.
  - `henergy : ∀ t ∈ Ioo 0 T, E' t / 2 + (ν - C₀ * y t) * (z t)^2 ≤ b t * y t`, with
    `hdE : ∀ t ∈ Ioo 0 T, HasDerivAt (fun x => (y x)^2) (E' t) t` — this is eq:Rcritical1
    `½(y²)' + (ν − C₀y)z² ≤ by` (`04-whole-space.tex:98`) **verbatim**, and it is literally the
    `henergy` field of `Paper1/ScalarEnergy.lean:132-133`.
  - Interval: hypotheses on `Ioo 0 T`, continuity/bounds/conclusion on `Icc 0 T`.
  - Continuity hypotheses: `hy : Continuous y` (global — see note N2), `hN : ContinuousOn N (Icc 0 T)`.
  - Conclusion: `∀ t ∈ Icc 0 T, y t ≤ c * ν`.  **This is the `a = 0` clause, correctly.**  The paper's
    displayed conclusion at `:102` is the general `y(t) ≤ y(0) + ∫₀ᵗ b`; the lemma assumes
    `hy0 : y 0 = 0` and `hN0 : N 0 = 0`, so `y(t) ≤ N(t) ≤ cν` is the `a = 0` specialization the
    contract's `inhomogeneousAtZero` consumes.  Probe **B5** proves the `hy0`-free version **false**
    (`y ≡ 1/2`, `c = 1/4`, `ν = C₀ = T = 1`, `E' = z = b = N ≡ 0`), so `hy0` is load-bearing and the
    lemma is not silently claiming the general clause.  The general-`a` row is honestly left open in
    `R43_SPLIT.md` §S2 with `Section4/C01/EnergyBounds.lean:179` named as its input.

### 2a. G1 — what a `Contracts/V2/Data`-style addition needs

`Spec.lean:142-143` `def dotHomogeneousENorm (s) (z) := ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ`
is **exactly** `Data.sobolevENorm`'s homogeneous analogue: `Contracts/V1/Data.lean:189`
`def sobolevENorm (s) (z) := ⨅ A : {A : RealVectorSobolev s // IsSobolevDatum s z A}, ‖A.1‖ₑ`,
with `IsSobolevDatum` replaced by the already-registered `IsHomogeneousSliceDatum`
(`Data.lean:367`).  D01's tree objects stop one level short: `homogeneousENorm` lives on `𝓢'`
(`:338`) and `homogeneousVectorENorm` on `VectorDistribution` (`:352`); neither is a norm on a
`SpatialField`.  So the addition is a **one-line `def` over registered vocabulary, zero new
mathematics** — it needs a new file (V1 is frozen), a scope entry naming the owning lane, and no
`rfl` bridge until some `formalization/` module restates it.

On rule 2 (blind comparison): the object is a *definition*, not a theorem, and the two-independent-
drafts evidence already exists — `research/R43/COMPARISON.md:28` (item 6) and `:43` (item 21) record
that drafts A and B each wrote this infimum independently, differing only in general `s` vs `s = 1/2`,
and both independently rejected `Data.dotHHalfENorm` as the junk-`0` Fourier form.  A fresh blind
pass would add nothing; the comparison record should simply be cited in the registration scope.

---

## 3. Gaps — the proved-vs-unproved audit of the three sibling clauses

The lane established that the three clauses are **unregistered**.  The deeper question it could not
settle is whether they are *proved but unregistered* or *unproved*.  Answer: **one is partially
proved, two are unproved.**  R43 is therefore blocked on **proof lanes (L)**, not on registration
lanes (S).

### A05 `velocityCriticalL3` (`‖u‖₃ ≤ C(1/2)·‖u‖_{Ḣ^{1/2}}`) — **PARTIALLY PROVED**

The genuine homogeneous critical estimate at order `a = 1/2` **is in the tree**:

* `NSFormalization.Paper1.SchwartzCriticalEmbedding.criticalPotential_eLpNorm_le`
  (`formalization/NSFormalization/Paper1/SchwartzCriticalEmbedding.lean:57`) —
  `eLpNorm (criticalPotential φ) 3 volume ≤ ENNReal.ofReal (κ · ‖criticalDatum φ‖)`, the right-hand
  side being the **homogeneous** datum `|ξ|^{1/2}𝓕φ` (not the inhomogeneous weight).
* `…criticalFieldLp_norm_le_datum` (`:171`) — the same bound on the `L^{p_a}` element that
  `normalizedCriticalPotential_toLp` (`:151`) identifies with the original distribution.
* All orders `0 < a < 3/2`, not just `1/2`:
  `NSFormalization.Source.FractionalRealization.realization_norm_le_datum`
  (`formalization/NSFormalization/Source/FractionalRealization.lean:96`) with
  `realization_toDistribution` (`:78`).
* `targetExponent a = 6/(3−2a)` is literally the paper's `p_a`.

What is missing is **not** the analysis but the carrier: `research/A05/COMPARISON.md:205-214` books
`velocityCriticalL3` under unit **U7** ("Real-3-vector + angular + `ℝ≥0∞` packaging of U6: closes
`embeddingPair`, `velocityCriticalL3`, `criticalRepresentative`, and
`ENNReal.ofReal (targetExponent (1/2)) = 3`", size M), which needs **U1** (datum uniqueness incl. the
`3/2` endpoint, M), **U2** (the angular↔cycles `(2π)^{-a}` normalization, M), **U3** (`homogeneousLeSobolev`
+ endpoint existence, S), **U4** (`IsRieszPower`, M) and **U6** (the scalar completion form, M).
`COMPARISON.md:216`: "Critical path for R43: U1 → U2 → U3 → U4 → U6 → U7 → U8."  Of A05's ten units
only **U9** (`gradientLSix`, "Fourier-free; independent of U1–U8") is done and registered.  The four
recorded mismatches are `research/A05/COMPARISON.md:52`: scalar `ℂ` not real `Fin 3`-vector; cycles
convention not angular; the headline `criticalFieldLp_norm_le_weighted` (`:195`) carries the
*inhomogeneous* weight so the homogeneous form is `:171`; and the LHS is `‖·.toLp p‖ : ℝ` not
`eLpNorm · 3 volume : ℝ≥0∞`.
**Owning table:** there is **no** `research/A05/*SPLIT*.md` — A05's unit ledger is
`research/A05/COMPARISON.md:205-216` (see note N5).
**Verdict: partially proved — ≈5 units (U1,U2,U3,U4,U6) + U7, an M-heavy Fourier campaign.**
R43's S1b additionally needs `derivativeCriticalL3` = **U8**.

### C01 `enstrophyIntegralBound` (eq:RH1), `sobolevTwoFourier`, `h2TimeIntegral` — **UNPROVED**

`grep -rni enstrophy formalization/NSFormalization/` returns **two docstring mentions only**
(`Section4/C01/Trilinear.lean:212`, `Section4/C01/Evolution.lean:11`) and no theorem; `eq:RH1`'s shape
`(‖∇u‖₂²)' + ν‖Δu‖₂² ≤ Cν^{-1}‖f‖₂²` occurs nowhere; `sobolevTwoFourier` and `h2TimeIntegral` have zero
non-docstring hits anywhere in the tree.

Owning table `research/C01/ENERGY_SPLIT.md`: the enstrophy rows are **E5** (enstrophy time derivative
`d/dt ∑ᵢ‖∂ᵢu‖² = −2⟪Δu,∂ₜu⟫`, **M**), **E6** (enstrophy pressure drop `⟨Δu,∇p⟩ = 0`, **M**,
"COMPARISON.md item 2(b)2 *new*"), **E7** (enstrophy arithmetic core, **S**) — all three still open,
explicitly "**not** done this lane (scope)".  The *prerequisite* machinery, however, **is** done:
E1 (velocity path), E2 (Lp↔spec vocabulary, lane 136), E3 (momentum in `Lp`, lane 143),
E4a (the three time-continuous residual jet paths, lane 146), E4b (`∇p` jet continuity, lane 148),
E4 (`energyDerivative_hasDerivAt`, lane 150) — so E5 runs the same carrier at `s = 1` minus `s = 0`.
Beyond E5–E7 there is still the Young absorption → integrated eq:RH1 (`enstrophyIntegralBound`), the
new Fourier inequality `sobolevTwoFourier` (no in-tree statement at all), and the `h2TimeIntegral`
assembly, plus **G5** (`S = T_max` endpoint gluing).
**Verdict: unproved — C01 V4 is E5(M) + E6(M) + E7(S) + three unstated fields.  The longest of the three.**

### A04 `lifespanInfiniteOfLocallyFinite` — **UNPROVED**

`grep -rn "= ⊤" formalization/NSFormalization/Section4/A04/` returns **nothing**; the only occurrence
of the name in `formalization/` is the docstring `Section4/A04/Forcing.lean:11`.
`research/A04/COMPARISON.md:76` marks it **Gap** in the lane's own words, with the nearest in-tree
analogue `MNS2.r3EndpointSafeProjected_horizons_unbounded_of_uniform_bound`
(`formalization/FormalPatched/R3MildContinuation.lean:122`) rejected for carrier (Bessel `R3HsVelocity 3`),
forcing (unforced), solution notion (mild, not classical) and criterion (a sup bound, not
`∫₀^S‖u‖²_{H²} < ∞`).

Route, from `research/A04/COMPARISON.md:217` row **C1**: "`extendsBeyond` and
`lifespanInfiniteOfLocallyFinite` from G3 and R1, on `maximalLifespanR` | **S** | order-theoretic",
binding `Source.SmoothLifespan.lifespan_ge_of_forall_shorter`
(`formalization/NSFormalization/Source/SmoothLifespan.lean:101`), `lifespan_le_iff_no_extension` (`:58`)
and `lifespan_eq_of_forall_shorter_of_upper_bound` (`:124`) — all three verified present and proved,
on the vendor `Flow`/`lifespan` carrier — transcribed to `ClassicalSolutionR`/`maximalLifespanR` by
A02 (`Section4/A02/Order.lean:50,72,102,126,137` already has that transcription layer).  C1 depends
on row **R1** (`restartBeyond` from A02's `restart`, **M**, `COMPARISON.md:216`), which is itself unproved.
**Verdict: unproved, but cheapest — R1 (M) then C1 (S), on machinery that already exists.**

### Recommended next lanes, in order

1. **A04 V3: R1 (`restartBeyond`, M) → C1 (`lifespanInfiniteOfLocallyFinite` + `extendsBeyond`, S).**
   Cheapest, order-theoretic on an existing skeleton, and it is R43's S5 *and* R44's.
2. **G1 registration (S, can run in parallel with anything).**  A one-line `def` over registered
   vocabulary; it unblocks *stating* R43's contract and A05's `embeddingPair`/`homogeneousLeSobolev`.
3. **C01 V4: E5 → E6 → E7 (M/M/S) → `enstrophyDifferentialBound`/`enstrophyIntegralBound` →
   `sobolevTwoFourier` → `h2TimeIntegral`**, plus **G5** (endpoint gluing, M).  Needed by both R43 S4
   and R44; longest, so start early.
4. **A05 V2: U1 → U2 → U3 → U4 → U6 → U7 (+U8 for `derivativeCriticalL3`).**  The Fourier campaign;
   the analysis exists (`SchwartzCriticalEmbedding`, `FractionalRealization`) and the work is carrier
   translation.
5. **R43-own G7/S1 (L)**: eq:Rcritical1 plus a `HasSmoothCriticalPath` — the critical analogue of
   `research/A04/Spec.lean:247` `HasSmoothSobolevPath`.  Depends on nobody's registration, so the
   `HasSmoothCriticalPath` definition and the S1c/S1d sub-rows can start now; S1b needs A05 U7/U8.
6. **G4** (homogeneous critical-slice force integrability, C01, M) and **G2/G3** (S6's reduction and
   non-vacuity, A05/D01, M–L) close last.

### Findings

* **N1 (minor, one-line fix, the only actionable item).**
  `formalization/NSFormalization/Section4/R43/Pieces.lean:74` says
  "``C₁``, ``C₁`` … of R43, C01 (`research/C01/Spec.lean:266`)".  `research/C01/Spec.lean:266` is
  **`CRH1`** (eq:RH1's right-hand constant, `:262-266`), a different constant; `C₁` is at
  `research/C01/Spec.lean:260` with `C₁_pos` at `:262`, as `verification/contracts.json:188` itself
  records ("carried verbatim from Spec.lean:260,262").  Fix: `:266` → `:260`.  The error is inherited
  from `research/R43/COMPARISON.md:114` (G8) and `research/R43/Spec.lean:158`, both pre-existing files
  outside this diff — exactly the "论文/文件行号引用代代相传" failure mode of `logs/LESSONS.md`.  Worth
  correcting in COMPARISON/Spec too, in whichever lane touches them next.
* **N2 (note, no action this lane).**  `criticalNormBound_radius` requires `hy : Continuous y`
  **globally**, inherited from `Paper1.continuous_bootstrap` (`Paper1/ScalarEnergy.lean:86`, which
  uses `hy.continuousOn` for `intermediate_value_Icc`).  At instantiation `y = ‖Λ^{1/2}u(t,·)‖₂` will
  only be continuous on `[0,T)`.  Either relax `continuous_bootstrap` to
  `ContinuousOn y (Icc 0 T)` (S, upstream edit in `Paper1/`) or extend `y` past `T`.  Recommend adding
  this as a sub-row of S2 in `R43_SPLIT.md` so the S1→S2 hand-off does not discover it late.
* **N3 (note, no action).**  In `exists_critical_radius`, `hC₀ : 0 < C₀` **is** load-bearing (with
  `C₀ < 0` the conjunction `0 < c ∧ c < 1/(4C₀)` is unsatisfiable), but `hC₁`/`hCemb` are load-bearing
  only for the *proof route* (the `min` witness): if `C₁·Cemb ≤ 0` then `C₁·Cemb·c ≤ 0 ≤ 1/4` for any
  `c > 0`, so the statement stays true without them.  Harmless — both constants are positive in every
  intended instantiation — but record it so a later "we dropped a hypothesis and it still compiled"
  is not mistaken for a defect.
* **N4 (note).**  `R43_SPLIT.md` §S3 cites the C01 gate as `research/C01/Spec.lean:532,576`; those are
  the two *field-declaration* lines.  The gate hypothesis itself sits at `:536-537` and `:580-581`
  (third copy `:514-515`).  Token match confirmed against all three.
* **N5 (note, for the lead's next brief).**  `research/A05/*SPLIT*.md` and a
  `research/A04/*SPLIT*.md` for the lifespan clause **do not exist**.  A05's unit ledger is
  `research/A05/COMPARISON.md:205-216`; A04's lifespan route is `research/A04/COMPARISON.md:76,216-217`
  (`research/A04/{G1,SL5}_SPLIT.md` cover other units).  `research/C01/ENERGY_SPLIT.md` rows E5–E7 is
  correct as cited.

### Honesty of ATTEMPTS_R43.md — VERIFIED

Both negative claims check out against the environment, not just against the narrative:
`Mathlib/Analysis/SpecialFunctions/Pow/` at this pin contains no `NNRpow.lean` (files: Asymptotics,
Complex, Continuity, Deriv, Integral, NNReal, NthRootLemmas, Real), and `ENNReal.rpow_natCast` is at
`NNReal.lean:686`.  The "reuse, not reprove" claim for S2 is confirmed by reading
`Paper1/ScalarEnergy.lean:123-151` and the one-`exact` body of `criticalNormBound_radius`.

---

## 4. Commands and results

All from the worktree, `. scripts/lean-env.sh` first, `LEAN_NUM_THREADS=6`, `lake` only from
`verification/`, one `lake` at a time.

```
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.Pieces
Build completed successfully (2667 jobs).            # exit 0, no warnings

$ cd verification && lake env lean ../formalization/NSFormalization/Section4/R43/Pieces.lean
                                                     # exit 0, 0 bytes of output

$ cd verification && lake env lean ../research/R43/axioms_r43_pieces.lean
'NSFormalization.Section4.R43.enorm_npow_two_eq_rpow_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.exists_critical_radius'     depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalL3_gate_real'       depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalL3_gate_enorm'      depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalNormBound_radius'   depends on axioms: [propext, Classical.choice, Quot.sound]
                                                     # exit 0; the 5 non-vacuity `example`s all typecheck

$ grep -n 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option' \
      formalization/NSFormalization/Section4/R43/Pieces.lean research/R43/axioms_r43_pieces.lean
# only docstring prose ("It contains no `sorry`, no `axiom`, …") and the five `#print axioms`
# lines of the conformance file.  No declaration, no option.

$ make check                                          # exit 0
  check_formalization_plan --check OK; check_contracts OK;
  test_contract_policy: Ran 13 tests ... OK;
  check_work_queue: 30 work items: ownership, contract registration and task cards consistent.

$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration   # exit 0
  "base_compatibility_checked": true

$ python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run
  Changed Lean modules: NSFormalization.Section4.R43.Pieces      # in CI's compiled closure

$ make test                                           # exit 0
  ... [10524/10524] Replayed Tests.EnergyAbsorptionPartialV3
  every registered contract: "checked; standard logical axioms only"
```

### Negative checks (probes kept, per `logs/LESSONS.md`)

`research/R43/probes/rev159_mutations_fail.lean` — **expected to fail, and does.**  G6 mutated to
`x ^ (2:ℕ) = x ^ (3:ℝ)`, original proof script kept verbatim (not an argument drop):

```
../research/R43/probes/rev159_mutations_fail.lean:14:6: error: unsolved goals
x : ℝ≥0∞
⊢ False
```

`research/R43/probes/rev159_negatives.lean` — **compiles silently (exit 0)**; every lemma in it
*proves* a falsity, so each is a genuine negative check rather than a failed `apply`:

| probe | what it proves |
|---|---|
| **B1** `g6_rpow_three_false` | `(2:ℝ≥0∞)^(2:ℕ) ≠ (2:ℝ≥0∞)^(3:ℝ)` — the G6 mutation is false, not merely unprovable |
| **B2** `no_nu_carrying_radius` | `¬ ∃ c > 0, ∀ ν > 0, C₁·Cemb·c·ν ≤ 1/4` — a `ν`-free `c` can never satisfy a `ν`-carrying threshold, so `exists_critical_radius`'s `C₁·Cemb·c ≤ 1/4` is the only spelling compatible with "one universal `c`" |
| **B3** `weaker_radius` | the brief's suggested mutation (`c < 1/(2C₀)`, `C₁·Cemb·c ≤ 1/2`) is derivable *from* `exists_critical_radius`, i.e. it is a strict **weakening** and therefore **not** a valid negative check.  Recorded so it is not reused as one |
| **B4** `gate_needs_nu_pos` | `criticalL3_gate_real` without `hν : 0 < ν` is false (`C₁=Cemb=1, c=0, ν=−1, y=L3=0`) |
| **B5** `bootstrap_needs_zero_datum` | `criticalNormBound_radius` without `hy0 : y 0 = 0` is false (`y ≡ 1/2, c = 1/4, ν = C₀ = T = 1`) — so the lemma really is the paper's `a = 0` clause and does not silently claim the general `y(t) ≤ y(0)+∫b` |
