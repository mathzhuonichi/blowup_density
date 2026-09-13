# A01 review — "Whole-space local solution adapter" (lane 013)

Reviewer pass over `research/A01/Spec.lean` and `research/A01/COMPARISON.md`, tree state
`4ba9f2b`. Nothing was modified. All paper line numbers below are the committed file.

## Verdict: **ACCEPT-WITH-NOTES**

`Spec.lean` is a faithful, hygienic, compiling specification of the *existence* half of
`prop:local`. The two questions that decide statement fidelity both come out right:

* **Quantifier order is correct.** `LocalTheoryAPI.horizon : ℝ → SpatialField → SpaceTimeField → ℝ`
  depends only on `(ν, a, f)`; the Sobolev order `m` is quantified *inside* the fixed `T`
  (`sobolev_smooth : ∀ m : ℕ, ∃ G, … ContDiffOn ℝ ∞ G (Ico 0 T)`). This is exactly
  `02-preliminaries.tex:117` ("one common existence interval for all Sobolev orders") and
  `appendix-a-local-theory.tex:66-67`. A fixed-order witness cannot discharge it.
* **Exclusions are right.** Uniqueness / maximal identification (A02, `appendix-a:115-125`),
  `eq:criterion` (A04, `appendix-a:127-157`) and `eq:mild` (`appendix-a:109-114`) are absent and
  correctly attributed. `Ico 0 T` matches `[0,T₀)`; `ContDiffOn` on the `UniqueDiffOn` set
  `Ico 0 T` really is the one-sided derivative at `t = 0`.

What holds the verdict back from ACCEPT is **not** the Lean file: it is two overclaims in the
source survey (H1, M2), one plan unit that is false as stated (H2), a route comparison that
rests on a mis-sized unit (H3), and a block of wrong appendix citations (M3).

## Ranked issues

| # | Sev | Field / claim | Location | What differs | One-line fix |
|---|---|---|---|---|---|
| H1 | high | "`T` **provably shrinks** in `q`"; "(A) is not merely unproved, **it is false** of the quoted `T`" | `COMPARISON.md:83-85,110,211-216` vs `Euler/VolterraUniqueness.lean:69` | `exists_positive_time_budget` gives **no formula** for `T` (an `ε/2` from `Metric.mem_nhds_iff`); no monotonicity in `M,L,R,q` is stated or proved anywhere, and cross-`q` comparison is not even type-correct (`u₀`, `C.linear`, `C.quadratic` live in different spaces). A purely existential theorem cannot make order-uniformity *false*. | Reword to "`T` is an existential witness constrained by `ballBound R`/`ballLipschitz R` with `R = ‖u₀‖_{H^{q+1}}+1`; **not proved uniform in `q`**". |
| H2 | high | unit **P2**, "`IsLerayComplement w ·` is single-valued on `R³`" | `COMPARISON.md:143`; `Spec.lean:74-76` | `HasSymmetricJacobian` (`Spec.lean:110`) uses bare `fderiv`, which is junk `0` for a non-differentiable `G`; `IsSolenoidal` likewise. Any nowhere-differentiable `L²` field satisfies `IsLerayComplement 0 G`, alongside `G = 0`. **P2 as written is unprovable.** Harmless *in the contract*, where `G = ∇p` and `pressure_smooth` is `ContDiffOn ℝ ∞`. | Add `Differentiable ℝ G` to `HasSymmetricJacobian`, or state P2 under a `ContDiff` hypothesis. |
| H3 | high | split sizes; "the OpenAI route avoids an **L**" | `COMPARISON.md:145-146,150,152,157,181-190` | **C1b** (D01 angular datum ⟷ Euler `ordinarySobolev` through the `ordinaryLift` adjoint) is the *same kind* of Fourier-convention bridge the memo sizes **L** for C1c, and it is on the critical path of the **recommended** route. **A3** and **B1** are also campaigns, not lemmas. So the route swaps C1c for C1b rather than avoiding an L. | Re-size C1b, A3, B1 to **L** (totals become ≈3 S / 7 M / 5 L) and re-run the F1-vs-C1b comparison. |
| M1 | med | missing unit | — | Order-uniformity by persistence needs (a) an **extension/continuation theorem at each order** and (b) **cross-order agreement** of the order-`(q+1)` and order-`(q'+1)` solutions. HeliCorgi has (a) at order 3 (`R3MildContinuation.lean:84`, `:134`, ported as `FormalPatched`); the Euler/local Picard layer has none. Neither appears among the 15 units. | Add unit "A2b: order-`m` continuation + cross-order agreement"; note it favours HeliCorgi. |
| M2 | med | `SmoothLifespan.Flow`: "field-for-field the shape of `ClassicalSolutionR`" and "**Nowhere inhabited**" | `COMPARISON.md:100` vs `Source/SmoothLifespan.lean:23` | Both false. `Flow` **lacks** `sobolev` and `pressure_gradient` — precisely components (C) and (E) A01 needs — and adds `energy`, `velocity_bound`, `derivative_bound`. And two constructors exist: `Flow.restrict` (`:83`) and `insertionFlow` (`:218`, a full `refine {…}` at `:226`), consumed at `Source/InsertionBreakdown.lean:75`. | "Same velocity/pressure/smoothness/equation core, missing `sobolev` and `pressure_gradient`; never constructed **from data** — both constructors consume an existing `Flow`." |
| M3 | med | appendix line citations, block 66-87 shifted ≈ +14 | `Spec.lean:25,30,33,51,257`; `COMPARISON.md:7,28,124` | `:81` cited for "the higher-order bounds … hold on the same local interval for every order" → actually **66-67** (`:81` is `\tau=\nu t`). `:85-88` for `C^j_tH^k_x` one-sided → **71-76**. `:88-90` for force `Pf` → **76-77**. `:93-107` for "viscosity rescaling and mean reduction" → rescaling is **79-87**, entirely outside. `:74-107` for the derivation excludes the common-interval sentence. `eq:highcontinuation` is **142-145**, outside the cited `:132-140`. The *load-bearing* quote for order-independence is the one mis-cited. (`02-prelim:117` **is** cited correctly at `Spec.lean:148,246`; all `02-preliminaries` and `04-whole-space` citations checked resolve.) | Renumber the appendix citations against `4ba9f2b`. |
| M4 | med | "R42, whose reference field `v` and pressure `π` **are** `LocalTheoryAPI.velocity`/`pressure`" | `Spec.lean:226-228` vs `STATEMENTS.md:330-333` | R42's `reference : IsClassicalSolution ν a g v π (Icc 0 (T+δ))` with `referenceLifespan : T+δ < Tmax ν a g`. `LocalTheoryAPI` gives a solution only on `[0, horizon ν a g)` with **no** relation to `T+δ`. R42's fields come from its `RegularThrough` hypothesis plus A02, not from A01's accessors. | "…are the *local piece* of R42's reference field; the identification on `[0,T+δ]` is A02's." |
| M5 | med | no lower bound on `horizon` | `Spec.lean:249` | `appendix-a:147-152` restarts at `t₀↑S` using "a common positive existence duration" from the `H¹` local bounds. `horizon` is exported as an arbitrary total function, so **A04 cannot state its restart from `LocalTheoryAPI`**. | Either add `horizon_lower : h ν ‖a‖_{H¹} ‖f‖_{L¹H¹} ≤ horizon ν a f` (`h` decreasing), or record explicitly that A04 re-derives it. |
| L1 | low | "Importable at this pin as `Formal.*` (84 modules)" | `COMPARISON.md:45` | `R3SchwartzInitialData` (row `:56`) and `R3DecodedVelocityRealness` are **not** among the 84 lakefile roots, and the former imports the non-compiling `Formal.R3MildContinuation`. `EndpointSafeTwoSpaceUniqueness` (row `:59`) is reachable only via `FormalPatched`; the table notes that only for `R3MildContinuation`. No `Formal/` olean tree exists in this worktree. | Mark the three rows "`FormalPatched` only / not ported". |
| L2 | low | `r3LerayL2Operator` "symbol `I−ξ⊗ξ/\|ξ\|²`" | `COMPARISON.md:127` vs `R3LerayL2Operator.lean:28` | It is `r3L2SolenoidalSubmodule.starProjection`; the file docstring (`:24-26`) says the symbol identification is *intentionally not bundled*. Symbol: `R3LerayComplexFiberSymbol.lean:114`; a.e. identification: `R3LerayPointwiseProjectionIdentification.lean:97`. | Cite the two extra modules in unit P3. |
| L3 | low | decoded realness at `:194` | `COMPARISON.md:56` | `:194` is realness of the **encoded** coordinate; decoded realness is `R3DecodedVelocityRealness.lean:71` (capstone `:238`). Energy clause is `∀ t`, not `Icc 0 T`. | Repoint. |
| L4 | low | namespaces | `COMPARISON.md:78,95` | `exists_positive_time_budget` is in `EulerSobolevHeat` (`EulerVolterraUniqueness` does not exist); `exists_local_forced_mild_invariant` is in `ForcedCylinderLocal`. | Rename. |
| L5 | low | dropped hypotheses | `COMPARISON.md:77,93,95,96` | `exists_local_quadratic_divergenceFree` is parametrized by `(κ, m)` and needs two `gradientProjection = 0` hypotheses; `ordinaryValue_lift` needs `hq : 3 ≤ q`; `exists_local_forced_mild_invariant` needs `u₀`/`f` invariant; `coefficients` also sets `linear := 0`. | Add to the cells. |
| L6 | low | "choose `T₀` from `‖a‖_{H³} + ‖f‖_{L¹_tH³}`" | `COMPARISON.md:150` | The recommended spine needs `hq : 6 ≤ q`, so its lowest available order is `q+1 = 7`. `H³` is the **HeliCorgi** order. | Say `H^7` on the OpenAI route. |
| L7 | low | double counting P3 against D01 L9 | `COMPARISON.md:154` | `RECONCILIATION.md:160` already scopes eq:Rpressure as D01 unit **L9(c)** ("`∇p = (I−P)(f−∇·(u⊗u))` ⟺ `momentum` given `divergence` and `∇p ∈ L²`"), citing the same two HeliCorgi declarations. Relatedly: three of the four `ManuscriptLocalRegularity` fields are consequences of `ClassicalSolutionR` — `projected` = `momentum` + E1 (verified: `navierStokesResidual = ∂ₜu + (u·∇)u − νΔu + ∇p`, `Packet.lean:127`), `pressure_recovery` = L9(c) **except at `t = 0`**, `pressure_potential` = P1 + connectedness. Only `sobolev_smooth` and the `t=0` endpoint add logical content. The redundancy is deliberate and documented; the *duplication with L9* is not. | Cross-reference L9(c) and note the `t=0` delta as the genuine increment. |
| L8 | low | C1c sizing for the pressure slice | `COMPARISON.md:146,191-196` | `R3HsVelocity` is order-**erasing** (`abbrev R3HsVelocity (_s : ℝ) := R3L2Velocity`, `R3SobolevCarrier.lean:29`), so `r3LerayComplementL2 : R3L2Velocity → R3L2Velocity` is plain complex `L²`: the pressure edge needs only real-`L²` ↪ complex-`L²` plus `𝓢'`→pointwise transport, **no Bessel bridge**. This *strengthens* the recommendation. | Say so; keep the Bessel bridge only for the velocity. |
| L9 | low | force class narrowing | `Spec.lean:255` | `prop:local` asks for "each force smooth into every `H^m` on compact time intervals"; `MemForceR` (eq:Rclasses) additionally demands `L¹_t`/`L²_t` finiteness. Strictly narrower than the paper's hypothesis. Fine for Section 4 (`F_c ⊆ F_rd ⊆ F_R`). | Record the narrowing. |

Not defects, checked and confirmed: `convectionDivergence` (`Spec.lean:102`) is literally `∑_j ∂_j(u_j u)`, and equals upstream `advection` (`Packet.lean:107`) for divergence-free `u` — E1 is genuinely a one-line calculus unit and the distinction is harmless. `IsLerayComplement` **is** equivalent to `(I−P)` on the class actually used (smooth `H^∞` `w`): `(I−P)w` is `H^∞`, `ξ`-parallel hence curl-free, and `Pw` is solenoidal; conversely the difference of two witnesses is `L²`, curl-free, divergence-free, smooth, hence harmonic and `0`. Single-valuedness therefore holds **in the contract** — the defect is only in the standalone unit P2 (H2). `maximalLifespanR ν a f > 0` does follow from the contract alone (`Data.lean:650-651`).

## Source spot-check table (16 claims opened at the cited `file:line`)

| # | Declaration | Cited | Verdict |
|---|---|---|---|
| 1 | `r3EndpointSafeProjected_exists_localMildSolution` | `R3EndpointSafeProjectedLocalExistence.lean:35` | **ACCURATE** — unforced, order 3 fixed, `∃ T, 0 < T ∧ T ≤ 1`, `Icc 0 T`, ball radius `‖u₀‖+1`, complex (`R3C = EuclideanSpace ℂ (Fin 3)`) |
| 2 | `EndpointSafeTwoSpaceDuhamelContract` | `EndpointSafeTwoSpaceDuhamel.lean:407`, `bilinear` `:427` | **ACCURATE** — 11 fields, **no forcing field**; `exists_pos_time_isMildSolutionOn` is at `Picard.lean:887` as cited. F1's "**L** on HeliCorgi" is justified. |
| 3 | `r3HelmholtzPressure` / `_gradient` / `r3LerayComplementL2` | `R3HelmholtzPressure.lean:223` / `:259` / `:228` | **ACCURATE** — source `F : R3L2Velocity` genuinely **arbitrary**, `∂_j p = −((I−P)F)_j` in `𝓢'`, complex. The pressure edge is real. |
| 4 | `IsR3…MildSolutionOn` / `_equation_at_time` / contract | `R3EndpointSafeProjectedDuhamel.lean:156` / `:163` / `:20` | ACCURATE (minor underclaim: `:163` also gives an `IntervalIntegrable` conjunct) |
| 5 | `r3EndpointSafeProjectedMild_navierStokes` | `R3NavierStokesEquation.lean:142` | **ACCURATE** — `Ioo 0 T`, strong `L²` `HasDerivAt`, momentum componentwise in `𝓢'`, divergence tempered |
| 6 | `r3AdmissibleSchwartzDatum_navierStokes` | `R3SchwartzInitialData.lean:233` (`:77`, `:194`) | Math ACCURATE; **`:194` wrong** (encoded, not decoded — L3) and **module not ported** (L1) |
| 7 | continuation + uniqueness | `R3MildContinuation.lean:84`,`:134`; `EndpointSafeTwoSpaceUniqueness.lean:222` | **ACCURATE** — uniqueness genuinely unrestricted (no ball, no realness, no smallness) |
| 8 | `r3LerayL2Operator` | `R3LerayL2Operator.lean:28` | **OVERCLAIM** — `starProjection`, not the symbol (L2) |
| 9 | `quadraticDuhamel` (+ carrier, cylinder) | `QuadraticHeatLocal.lean:23`; `CylinderSobolevSpace.lean:49`; `EulerProof.lean:1085` | **ACCURATE** — real, forced, `Icc 0 T`, cylinder `Vector3 × AddCircle period`, `q` fixed |
| 10 | `Coefficients` (`forcing`) / `ballBound` | `QuadraticCoefficients.lean:16` / `:47` | **ACCURATE** — 4 fields incl. `forcing : C(T,Y)`; `ballBound` formula character-for-character. F1's "**S** on OpenAI" is justified. |
| 11 | `exists_local_quadratic_mild` | `QuadraticHeatLocal.lean:32` | ACCURATE |
| 12 | `exists_local_quadratic_divergenceFree` | `QuadraticHeatConstraint.lean:19` | ACCURATE with dropped `(κ,m)` + 2 hypotheses (L5) |
| 13 | `exists_positive_time_budget` | `VolterraUniqueness.lean:69` | **Structure ACCURATE, monotonicity OVERCLAIM** (H1); wrong namespace (L4) |
| 14 | `ForcedCylinderLocal.leray` / `.coefficients` / `exists_local_forced_mild` | `ForcedCylinderLocal.lean:26` / `:52` / `:72` | ACCURATE — `q ≥ 6`, cylinder, real, no pressure anywhere in the file |
| 15 | **`OrdinaryForcedLocal.exists_local`** | `OrdinaryForcedLocal.lean:32` | **ACCURATE in full** — real, forced, `q ≥ 6` fixed, ordinary `L²` path (not pointwise), no pressure, `T` unquantified. `SmoothL2Field` (`LpSmoothField.lean:31`) is genuinely smooth with all jets `L²`. |
| 16 | `SmoothLifespan.Flow` / `.lifespan` | `SmoothLifespan.lean:23` / `:41` | **OVERCLAIM ×2** (M2); `lifespan` is syntactically the same supremum as `maximalLifespanR` ✔ |

`sorry` / `axiom` / `admit` / `native_decide`: **zero** across all 128 `vendor/HeliCorgi/Formal/*.lean`, all
4 `FormalPatched`, `vendor/NavierStokesAndEuler/Euler/`, `Source/` and `Data.lean`. Every cited
theorem is fully proved. All other cited `file:line` pairs in the source tables resolve exactly.

## Strategy

**I would take the same route, for a partly different reason, with one unit added.**

The two load-bearing facts are verified and decisive: `EndpointSafeTwoSpaceDuhamelContract` really
has no forcing field (11 fields, only `bilinear` as a source), so F1 on HeliCorgi is an **L**; and
`Coefficients.forcing` really exists and `ForcedCylinderLocal.coefficients:52` really instantiates
it at `P(f − (u·∇)u)`, so F1 on OpenAI is free. `r3HelmholtzPressure_gradient` really takes an
arbitrary `L²` source, so the pressure edge is a genuine import. The memo's core reasoning stands.

Three corrections to the memo's own case:

1. **The strongest argument for HeliCorgi-for-pressure is stronger than the memo makes it**, and the
   memo does not notice why: `R3HsVelocity` erases its order, so `r3LerayComplementL2` acts on plain
   complex `L²`. The pressure slice needs no Bessel bridge at all (L8).
2. **The strongest argument against the OpenAI spine is missing**: the memo trades C1c (L) for C1b
   (sized M, actually L) and for the angle-invariance bookkeeping, and it does not count the
   continuation layer. HeliCorgi has `exists_extension_of_bounded` / `blowup_dichotomy` already
   ported; the Euler/local Picard layer has no analogue (M1). Once C1b is priced at L, the two
   routes are much closer than "F1 favours OpenAI, E favours HeliCorgi" suggests. I still land on
   the memo's split, because reality + physical `L²` + `OrdinaryViscousUniqueness` (which fixes the
   output shape A02 needs) are genuinely only on the OpenAI/local side — but the margin is thin and
   trigger 3 ("if C1c turns out short") should be checked **first**, not last.
3. **The "biggest risk" is real but misdiagnosed.** `A2 = eq:Rhigh/eq:highcontinuation` is **correct**:
   `appendix-a:143-145` is literally `(‖u‖_{H^m})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m}` with the
   `(‖u‖²+ζ²)^{1/2}` regularization at `:140-141`, for `m ≥ 3` (`:129`), and A04 needs the same
   inequality — "build once, share" is right. But the stated risk ("A3 has to **replace** that `T`")
   overstates the problem *and* understates a different one. A3 need not touch
   `QuadraticHeatLocal.lean:32`: take `T₀` = the budget's `T` at the **lowest** available order
   (`q = 6`, i.e. `H^7`) and propagate every higher order on that same `T₀`. What that bootstrap
   actually requires is an order-`m` continuation criterion plus cross-order agreement (M1) — absent
   from both the unit list and the risk section. And since H1 shows `T` is only an unquantified
   existential, the honest statement is "no handle on `T`", not "`T` shrinks".

Unit sanity: E1, F1, B2, X1 as **S** are right. P1 is **M** not S (differentiation under
`intervalIntegral` with its side conditions). P2 is unprovable as stated (H2). C1a and A1 are
correctly attributed away (D01 L2, A03). C1b, A3, B1 are **L** (H3). **No unit is an open
mathematical problem** — A3 is Tao 5.4(ii) via a standard Grönwall bootstrap — but A3, C1b and B1
are each multi-week campaigns booked as lemmas, and together they are essentially all of A01.

## Check log

| Check | Command | Result |
|---|---|---|
| Typecheck | `. scripts/lean-env.sh; LEAN_NUM_THREADS=6; cd verification && lake env lean ../research/A01/Spec.lean` | **exit 0**, no diagnostics (1.90s user / 2.84s wall) |
| Hygiene | `grep -nE 'sorry\|axiom\|admit\|native_decide\|unsafe' research/A01/Spec.lean` | 2 hits, both in the module docstring (`:10`, `:11`) asserting their absence; **no code hits** |
| No proofs | `grep -nE '^\s*(theorem\|lemma\|example\|instance\|abbrev)\b' research/A01/Spec.lean` | **no matches**; declarations are 5 `def` + 2 `structure` only |
| Fidelity | `02-preliminaries.tex` 1-130, `appendix-a-local-theory.tex` 1-157, `04-whole-space.tex:25-60,125-140` read in full | see M3, M4, L9 |
| Consumers | `STATEMENTS.md` v2 `referenceLifespan` (`:333`), `IsMaximalSolution` (`:174,:346,:1198`), `prop:local` (`:42,:257,:549,:706,:1317`) | A02's uniqueness is statable from `LocalTheoryAPI` (it projects `u`,`p` for the 5-ary `IsMaximalSolution`); R42's `referenceLifespan` is **not** (M4); A04's restart is **not** (M5) |
| D01 carrier | `Data.lean:160,488-502,537,582-590,617-651`; `Packet.lean:95-131`; `RECONCILIATION.md:160,173-244` | `ClassicalSolutionR` fields as `Spec.lean:137-141` describes; `horizon_pos` present (`:623`); L9(c) overlap → L7 |
| Sources | 16 declarations opened at the cited `file:line` across `vendor/HeliCorgi/Formal/`, `vendor/NavierStokesAndEuler/Euler/`, `formalization/NSFormalization/Source/` | table above; 2 overclaims, 1 wrong citation, 4 naming/hypothesis slips |
