# A04 — source-to-target comparison and implementation split

Task `collaboration/tasks/A04.md`; graph node `A04` in
`formalization/blueprint/DEPENDENCY_GRAPH.md:205-209` (`A04 ← A02, A03`;
consumers `A04 → R43`, `A04 → R44`).  Target of this comparison:
`research/A04/Spec.lean`, `structure ContinuationAPI`.

**Target statement.**  `paper/sections/02-preliminaries.tex:105-114` `prop:local`
(= `lem:Rlocal`), continuation clause `eq:criterion` (`:111-113`), derived at
`paper/sections/appendix-a-local-theory.tex:127-157`: eq:Rhigh (`:132-137`), the
`ζ`-regularization (`:139-141`), eq:highcontinuation (`:142-145`), the Grönwall
consequence (`:146-147`) and the restart (`:147-152`).  The closing sentence
`:155-157` ("without requiring zero mean or a whole-space Poincaré inequality")
is a **negative** requirement on the contract and is honoured: no field below
mentions a spectral gap, a mean reduction or a Poincaré constant.

**Revision 2**, after [`REVIEW.md`](REVIEW.md) (verdict ACCEPT-WITH-NOTES) and
the merge of `erenup/integration` into the lane branch.  Changed: the
`outerProductTame` row is now a `tame` row against the merged contract
(finding 3); the `Chigh`-vs-`Ctame` decision is recorded (finding 3 sub-note);
the `HasSmoothSobolevPath` hypothesis and the `lifespanInfiniteOfLocallyFinite`
and `highContinuationIntegral` corrections are reflected in §2 and §4
(findings 1, 2, 4, 6); the two citation nits of finding 7 are fixed; and every
"PR #31 has not landed" sentence is gone.  `research/A04/ATTEMPTS.md` lists the
changes against `Spec.lean`.

Every `file:line` in this document was re-opened at the merge commit `f2937e8`
of the lane branch, which contains `erenup/integration` at `4ba9f2b`.

---

## 1. What the target actually demands

The appendix proves the criterion in five moves.  Naming them here, because the
split in §4 is indexed by them:

| move | manuscript | content |
|---|---|---|
| (1) | `:129-137` eq:Rhigh | pair eq:projected with `u` in `H^m`, `m ≥ 3`; pressure drops by solenoidality; the nonlinear term is bounded by eq:Rproduct/eq:tame and Cauchy–Schwarz against `‖∇u‖_{H^m}` |
| (2) | `:139-141` | Young absorbs `C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}` into `ν‖∇u‖²_{H^m}`; divide by `(‖u‖²_{H^m}+ζ²)^{1/2}`; let `ζ↓0` |
| (3) | `:142-145` eq:highcontinuation | `(‖u‖_{H^m})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m}` |
| (4) | `:146-147` | Grönwall with the **time-integrable** coefficient `‖u‖²_{H²}` and the `L¹_t` inhomogeneity `‖f‖_{H^m}`: every `H^m` norm is bounded uniformly on `[0,S)` |
| (5) | `:147-152` | restart at `t₀ ↑ S` with the uniform `H¹` step; one interval passes `S`; uniqueness identifies it with the original solution |

Two features of (4) are what make A04 hard and are the reason no source matches:
the Grönwall coefficient is **not bounded in time**, only `L¹` — that is the
entire content of eq:criterion — and the conclusion must hold **for every order
simultaneously** on the **same** interval `[0,S)`.

`C_m` in (1) depends on the order alone; `C_{m,ν}` in (3) acquires the viscosity
from the Young step.  Carrying out (2) explicitly gives `C_{m,ν} = (C_m)²/(4ν)`;
the manuscript displays no formula and `ContinuationAPI.Cgron` pins none.

---

## 2. Field-by-field comparison

Carrier abbreviations: **D01** = the datum carrier of
`verification/Contracts/V1/Data.lean` (`sobolevENorm`, `ClassicalSolutionR`,
`maximalLifespanR`); **jet** = `EulerLpTranslation.SmoothL2Field` with
`wordEnergy`/`WordBound`; **Bessel** = HeliCorgi's complex `R3HsVelocity 3`;
**scalar** = a bare `ℝ → ℝ` energy path.

| field | paper location | closest existing declaration (name, file:line, carrier, hypotheses) | mismatch |
|---|---|---|---|
| `Chigh`, `Chigh_pos` | `appendix-a:132-137` `C_m` | `EulerOrdinarySobolev.tameEnergyConstant` (`vendor/NavierStokesAndEuler/Euler/OrdinaryTameEnergy.lean:86`), a closed-form `ℕ → ℝ` on the jet carrier and Euler's; `Contracts.V1.TameProduct.TameProductAPI.Ctame` (`verification/Contracts/V1/TameProduct.lean:233`), the right one | none structurally. **Decision recorded** (`REVIEW.md` finding 3 sub-note): `Chigh` is kept as an **opaque field of its own**, and `energyIdentityHigh` is stated with it rather than with `tame.Ctame`. Carrying out eq:Rhigh's Cauchy–Schwarz step contributes a factor one, so an implementation *may* take `Chigh m = tame.Ctame m` — but `appendix-a:131` says only "using eq:Rproduct gives", so pinning them equal would oblige an implementer to prove a sharper identity than the manuscript states, for no gain: `R43`/`R44` use the criterion qualitatively and never see either constant. Revision 1's docstring claim that "`Chigh` may be taken to be `Ctame`" is now stated as a permission, not an identification |
| `Cgron`, `Cgron_pos` | `appendix-a:142-145` `C_{m,ν}` | **none.** No in-tree constant carries a viscosity index | gap, but trivial: it is `(Chigh m)²/(4ν)` once (2) is done |
| `tame` (⟪A03⟫) | `appendix-a:17-18` eq:tame | `Contracts.V1.TameProduct.TameProductAPI` (`verification/Contracts/V1/TameProduct.lean:215`), **registered on integration** as `A03.tame_products`; the clause consumed is `.outerProductTame` (`:345`), D01 carrier, `MemHmVector k`, `3 ≤ k`; accepted draft `research/A03/Spec.lean:512`; shape cross-check `EulerOrdinarySobolev.tame_outer_product` (`Euler/OrdinaryTameProduct.lean:83`), jet carrier | **no mismatch** — imported and carried whole, exactly as `boundedRepresentative` is. Revision 1 mirrored the clause and seven supporting definitions (`lift`, `partialDeriv`, `outerColumn`, `columnsSobolevENorm`, `outerSobolevENorm`, `gradientSobolevENorm`, `MemHmVector`) because the module was not yet on the lane branch; `REVIEW.md` finding 3 verified they were symbol-for-symbol identical, and all seven plus the `outerProductTame` field are deleted in revision 2 |
| `boundedRepresentative` (⟪A03⟫) | `appendix-a:12` eq:Rproduct, 2nd clause | `Contracts.V1.BoundedRep.BoundedRepresentativeAPI` (`verification/Contracts/V1/BoundedRepresentative.lean:173`), **registered on integration**, D01 carrier + `SmoothJetsUpTo 2` | **no mismatch** — imported, not restated |
| `energyIdentityHigh` (eq:Rhigh) | `appendix-a:132-137` | `EulerOrdinarySobolev.integerEnergyDerivative_bound` (`vendor/NavierStokesAndEuler/Euler/OrdinaryEulerHigherEnergy.lean:56`): `(wordEnergy m)'(t) ≤ C_m·M·wordEnergy m t` for `3 ≤ m`, jet carrier, hypothesis `∀ t, WordBound 3 M (U.velocity t)` | four mismatches: (a) **Euler** — `derivative_eq_eulerRhs` (`:42`), so no `ν‖∇u‖²_{H^m}` dissipation and no `+‖f‖_{H^m}‖u‖_{H^m}` forcing; (b) the coefficient is a **uniform-in-time** `M`, not `‖u(t)‖_{H²}`; (c) carrier is `wordEnergy` (jets), not `sobolevENorm` (datum) — D01 unit **L2**; (d) `Evolution T hT` is not `ClassicalSolutionR` |
| `regularizedNormDerivative` (`ζ`-step) | `appendix-a:139-141` | `NSFormalization.Paper1.sqrt_energy_le_primitive` (`formalization/NSFormalization/Paper1/ScalarEnergy.lean:22`), scalar: from `E' ≤ 2b√E` and `E 0 = N 0 = 0` it proves `√E ≤ N`, by regularizing with `√(E+δ²)` and dividing — **literally the manuscript's device**, already proved | the proved inequality has **no linear term**: the input is `E' ≤ 2b√E`, whereas (2) needs `E' ≤ 2(K(t)E + b√E)` so that the quotient carries `K(t)√(E+ζ²)`. Also `hE0 : E 0 = 0` is assumed, which the continuation cannot assume. It is the right lemma one term short |
| `highContinuationIntegral` (after `ζ↓0`) | `appendix-a:141-145` | `Paper1.continuation_packet_bound` (`Paper1/ScalarEnergyContinuation.lean:22`, the **A04 card's own evidence**) = `Paper1.packet_energy_integral_bound` (`ScalarEnergy.lean:197`): from `E' + 2νd ≤ 2b√E` it gives `E + 2ν∫d ≤ (∫b)²` | wrong inequality: that is `eq:packetenergy` (`02-preliminaries.tex:152`, Lemma 2.2), the `L²` packet energy with `E 0 = 0` and **no linear term**, not eq:highcontinuation. The other export of that file, `continuation_certificate` (`:14`) = `continuous_bootstrap` (`ScalarEnergy.lean:85`), is a subcritical continuity bootstrap used by `prop:Rcritical1`'s smallness argument (C01/R43), not by A04. **Revision 2** also settles the interval-integral totality (`REVIEW.md` finding 6): the field now *asserts* `IntervalIntegrable` of the integrand alongside the bound, rather than writing an inequality against Mathlib's junk `0` — a strengthening that is free on a classical solution (unit **N1**) and spares every consumer a side condition |
| `higherOrderBound` (Grönwall, move (4)) | `appendix-a:146-147` | `EulerOrdinarySobolev.integer_energy_bound` / `integer_energy_uniform` (`Euler/OrdinaryEulerHigherEnergy.lean:64,84`): `wordEnergy m (U t) ≤ wordEnergy m (U 0)·exp(C_m M t)` for every `3 ≤ m`, via `linear_stability_within` (`Euler/OrdinaryEulerL2Stability.lean:46`) | the all-order shape is right and is the **only** in-tree all-order propagation; but the coefficient is the constant `C_m·M` from a sup bound, and A04's is `C_{m,ν}‖u(t)‖²_{H²}` which is **only `L¹` in time**. Mathlib's continuous Grönwall (`Mathlib/Analysis/ODE/Gronwall.lean:112,134`, `le_gronwallBound_of_liminf_deriv_right_le`, `norm_le_gronwallBound_of_norm_deriv_right_le`) also takes **constant** `K` and `ε`; only `DiscreteGronwall.lean:50` `discrete_gronwall_prod_general` has variable `c n`, `b n`, and it is discrete. **This is the hardest single gap in A04** |
| `restartBeyond` (move (5)) | `appendix-a:147-152` | `MNS2.r3EndpointSafeProjected_exists_extension_of_bounded` (`formalization/FormalPatched/R3MildContinuation.lean:93`): a mild solution bounded by `R` on `Icc 0 T` extends to `T + r3MildLifespan ν R`, with `r3MildLifespan_antitone` (`:67`) giving the uniform step; `_horizons_unbounded_of_uniform_bound` (`:122`) and `_blowup_dichotomy` (`:143`) | the **step machinery is exactly right** and is the strongest reusable asset in the lane: an explicit `δ(ν,R)` antitone in the bound, a concatenation, and the "bounded ⇒ horizons unbounded" argument. Mismatches: Bessel complex `R3HsVelocity 3` carrier at the **fixed order 3**; **unforced** (`EndpointSafeTwoSpaceDuhamelContract` has no forcing field, `research/A01/COMPARISON.md` §2 edge D); mild, not classical; `r3MildHorizons` is not `maximalLifespanR`; and the input criterion is a **sup bound on the trajectory**, not `∫₀^S‖u‖²_{H²} < ∞` — the discrepancy `formalization/blueprint/EXTERNAL_REUSE.md:32` already records. The manuscript's own restart is A02's `restart` (`research/A02/Spec.lean:550`), which is the intended route |
| `extendsBeyond` (eq:criterion) | `02-preliminaries.tex:108-114`; used at `04-whole-space.tex:171` | `Source.SmoothLifespan.lifespan_ge_of_forall_shorter` (`formalization/NSFormalization/Source/SmoothLifespan.lean:101`) and `lifespan_le_iff_no_extension` (`:58`), on `Flow`/`lifespan` | order-theoretic scaffolding only: these say how a lifespan relates to its horizons, not that any criterion extends one. `Flow` (`:23`) is not `ClassicalSolutionR` — it has `velocity_bound`/`derivative_bound` fields and lacks `sobolev` and `pressure_gradient`. No in-tree statement has `∫₀^S‖u‖²_{H²}` on either side. **Gap** |
| `lifespanInfiniteOfLocallyFinite` (R43's packaging) | `04-whole-space.tex:121`, `:132-133` | `MNS2.r3EndpointSafeProjected_horizons_unbounded_of_uniform_bound` (`FormalPatched/R3MildContinuation.lean:122`) is the same *argument* (a certified horizon within one step of the supremum extends past it) | same carrier/forcing/criterion mismatches as `restartBeyond`; and the hypothesis there is a uniform norm bound, here a family of finite time integrals. **Gap.** Revision 2 fixed two statement defects here (`REVIEW.md` findings 1 and 2): the criterion hypothesis is now guarded by `ENNReal.ofReal S ≤ maximalLifespanR ν a f`, the manuscript's own range at `04-whole-space.tex:121` and the only range C01's assembly can supply; and `0 < maximalLifespanR ν a f` — `IsMaximalSolution`'s first clause (`research/A02/Spec.lean:212-215`, rationale at `:180-183`) — is now a hypothesis, without which `u = p = 0` at a datum with empty lifespan makes the field assert `0 = ⊤` |
| `squaredHTwoIntegral`, `SolvesBelow`, `MemL1Hm`, `BoundedIntoHOne`, `HasSmoothSobolevPath` | `02-preliminaries.tex:111-113`, `:108`, `:17`, `appendix-a:150-151`, `:71-76` | `Data.forceSobolevENormL1` (`Contracts/V1/Data.lean:231`) and the `MemLp G 1` clause of `MemForceR` (`:544`) exist; the `∫⁻` of the squared `H²` norm does not appear anywhere; `HasSmoothSobolevPath` is `ManuscriptLocalRegularity.sobolev_smooth` (`research/A01/Spec.lean:230`) verbatim | new definitions, all short, all on D01 vocabulary. `HasSmoothSobolevPath` is a **copy** of A01's clause, not a weakening: `research/` is not a Lean library, so A01's specification cannot be a field of a file checked with `lake env lean`, and the three fields that *assert* differentiability would otherwise not be dischargeable from `ContinuationAPI` plus `Data.lean` alone (`REVIEW.md` finding 4) |

### Declarations checked and found **not** to be the target

* `Paper1/ScalarEnergyContinuation.lean` (the A04 card's cited evidence, 36 lines
  total): both its theorems are thin re-exports — `continuation_certificate` of
  `continuous_bootstrap` (`ScalarEnergy.lean:85`) and `continuation_packet_bound`
  of `packet_energy_integral_bound` (`ScalarEnergy.lean:197`).  Neither has a
  linear term, neither has a viscosity-dependent constant, neither mentions an
  order `m`, a lifespan or a Sobolev norm.  **The file's name is the only thing
  in it that is about continuation.**  Its real value to this lane is indirect:
  it shows that `ScalarEnergy.lean`'s regularization lemma is already the
  project's chosen scalar layer, which is where unit **Z1** below should land.
* `Source/SmoothLifespan.lean:70` `bad_or_regular_reference` and `:124`
  `lifespan_eq_of_forall_shorter_of_upper_bound`: R42/A02 material.
* `Source/OrdinaryViscousUniqueness.lean:26` `velocity_unique` and
  `Source/OrdinaryViscousStability.lean:71` `difference_energy_bound`: the
  **uniqueness** Grönwall of `appendix-a:117-124`, with the coefficient
  `‖∇u₂‖_∞` bounded by hypothesis `hK`.  A02's, not A04's; it is nevertheless the
  best in-tree template for "differentiate a squared `L²` norm along a solution
  and close by Grönwall", because it does the `HasDerivWithinAt` bookkeeping on
  a physical jet path.
* Mathlib `Analysis/ODE/Gronwall.lean` and `Analysis/ODE/DiscreteGronwall.lean`:
  see the `higherOrderBound` row.  `Analysis/ODE/PicardLindelof.lean` and
  `ExistUnique.lean` are finite-dimensional ODE theory and do not apply.

---

## 3. Relation to A01's units A2/A2b and to A02's `restart` — share, do not duplicate

**A01 unit A2 *is* this Grönwall.**  `research/A01/COMPARISON.md` §3 books unit
**A2** as "high-order propagation: `(‖u‖_{H^m})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖_{H^m} +
‖f‖_{H^m}` for `m ≥ 3` on an interval of low-order existence, with the
`(‖u‖²+ζ²)^{1/2}` regularization", size **M**, and says in the same cell:
"**gap**, but *shared with A04*: it is literally eq:Rhigh (`appendix-a:132-137`)
and eq:highcontinuation (`:142-145`, regularization at `:140-141`).  Build in one
place."  Its §2 edge **A** repeats the instruction.  This comparison confirms it
from the other side and makes the sharing concrete:

* `ContinuationAPI.energyIdentityHigh`, `.regularizedNormDerivative` and
  `.highContinuationIntegral` **are** A01's unit A2, stated on the D01 carrier.
  A01 uses them to propagate every higher order onto the **low-order existence
  interval** `T₀` (A01 unit **A3**); A04 uses them to propagate every higher
  order up to the **endpoint** `S` under `∫₀^S‖u‖²_{H²} < ∞`.  Same three
  inequalities, two different intervals.
* Recommendation: implement units **G1**, **Z1**, **G2** of §4 once, in a module
  under `verification/Contracts/` or a shared `Section4/Gronwall/` namespace, and
  let both A01's `horizon`/`solution` construction and `ContinuationAPI` consume
  them.  Neither lane should carry a private copy.  Where the two differ is only
  in what is fed in: A01 feeds a *bounded* `‖u‖_{H²}` on a short interval, A04
  feeds an `L¹`-in-time `‖u‖²_{H²}`, and only the latter forces the
  variable-coefficient Grönwall of unit **G3**.
* **A01 unit A2b** (order-`m` continuation criterion plus cross-order agreement)
  is *not* A04's.  A2b asks that a bounded order-`m` trajectory extend by a
  positive step, at fixed `m`, inside the Picard layer; A04's `restartBeyond`
  asks that a solution with a uniform `H¹` bound on `[0,S)` reach past `S` on the
  classical carrier.  A2b is an input to A01's construction of `horizon`; A04
  reaches the same conclusion through A02 instead.  HeliCorgi's
  `r3EndpointSafeProjected_exists_extension_of_bounded` is the source for A2b and
  is *not* a source for A04 (see the `restartBeyond` row).

**A02's `restart` is used, not restated.**  `research/A02/Spec.lean:550`
`MaximalSolutionAPI.restart` already states: for each `ν > 0` and each finite `K`
there is one `δ > 0` with `ofReal (t₀ + δ) ≤ maximalLifespanR ν a f` at every
presingular `t₀` whose datum and shifted force obey `K`.  `DEPENDENCY_GRAPH.md`
gives A04 exactly this edge, and `research/A02/Spec.lean:302-305` names the four
fields A04 takes (`restart`, `restart_datum`, `restart_force`, `uniqueness`).

`ContinuationAPI` therefore **does not** restate any A02 field — unlike
`MaximalSolutionAPI`, which had to restate three `LocalTheoryAPI` fields because
it needed them in its own statements.  A04 needs A02 only in its *proofs*.  What
`restartBeyond` adds over `restart` is precisely the endpoint passage:

* `restart` is quantified over presingular times `t₀ < T^ν_{max,R}` one at a
  time; `restartBeyond` is quantified over the endpoint `S` and concludes
  `ofReal (S + δ) ≤ T^ν_{max,R}`;
* the bridge is the **uniformity** of the `H¹` bound over all of `[0,S)`, which
  is `higherOrderBound` at `m = 1`, and the fact that `δ` in `restart` does not
  depend on `t₀`.  Taking `t₀ > S − δ` gives a horizon past `S`.

Consequently the only A02-shaped object in `Spec.lean` is `SolvesBelow` (A02's
own hypothesis shape, `research/A02/Spec.lean:576`): `IsMaximalSolution`,
`presingularTimes` and `timeShift` are deliberately **not** copied, and
`lifespanInfiniteOfLocallyFinite` writes out the presingular family inline for
the same reason.  Revision 2 does copy `IsMaximalSolution`'s **first** clause,
`0 < maximalLifespanR ν a f`, into that inline family — `REVIEW.md` finding 2
showed the field is false without it — but not the predicate itself.

**A03 and `BoundedRepresentative`.**  Only one Lemma A.1 clause is consumed,
eq:tame.  Both A03 contracts are now merged and registered
(`verification/contracts.json`: `A03.tame_products`, `A03.bounded_representative`),
so both are imported and carried as fields, and nothing of A03 is restated or
re-proved.

**Why A01 and A02 are treated differently from A03.**  `REVIEW.md` finding 4
asks why `boundedRepresentative` is a field while the A01/A02 inputs are not.
The rule is **importability**, and `Spec.lean`'s header now says so.  A03's two
contracts are registered Lean modules, so they are fields.  A01's and A02's
specifications live under `research/`, which is not a Lean library and cannot be
imported by `cd verification && lake env lean ../research/A04/Spec.lean`, so
`maximal : MaximalSolutionAPI` is simply not available to this draft.  What those
lanes supply is therefore split by whether a field *asserts* it:

* the `C^∞`-in-time datum path **is** asserted, by the three differential fields
  ("`r ↦ ‖u(r)‖²_{H^m}` is differentiable"), so A01's clause is restated verbatim
  as `HasSmoothSobolevPath` and is an explicit hypothesis of those three.  They
  are now self-contained;
* A02's `restart` and `uniqueness` are **not** asserted by any field — they are
  proof inputs of `restartBeyond` — so they stay out, because restating `restart`
  would drag in `IsMaximalSolution`, `presingularTimes` and `timeShift`, the very
  duplication this section argues against.  Units **D1** and **R1** below are the
  pointers a standalone implementer follows.

The three fields that transcribe manuscript sentences (`higherOrderBound`,
`extendsBeyond`, `lifespanInfiniteOfLocallyFinite`) deliberately carry **no**
regularity rider: their hypotheses are `prop:local`'s, and adding one would make
them weaker than the proposition.

---

## 4. Bounded implementation split

Size key, the same as `research/A01/COMPARISON.md` §3 and `research/A03/COMPARISON.md`
§4: **S** ≤ ~100 lines of Lean, no new analytic machinery; **M** a self-contained
lemma with real content but a known proof; **L** a multi-file campaign.

Ten units.  `→` in the *depends on* column means "needs the named unit finished";
registered-contract dependencies are named by their field.

| # | unit | size | depends on | binds to / gap |
|---|---|---|---|---|
| **N1** | Norm bookkeeping on the datum carrier: `ClassicalSolutionR.sobolev` gives `sobolevENorm (m:ℝ) (u t ·) ≠ ⊤` on `Ico 0 T`, `sobolevNormAt` is then the datum norm `‖G t‖`, and `t ↦ sobolevNormAt s u t` is continuous there. Same for `MemForceR` and `f`. | S | D01 **L1** (datum uniqueness, `RECONCILIATION.md:152`) | `Paper3.angularRealization_injective` (`Paper3/AngularFourierDilation.lean:203`), `Paper3.MemAngularSobolev.exists_unique_datum` (`Paper3/AngularSobolevClass.lean:68`). Pure transport; unblocks every real-valued statement in `Spec.lean` |
| **F1** | `MemForceR f → MemL1Hm f`, and `MemForceR f → BoundedIntoHOne (Icc 0 b) K f` for some finite `K` at every `b` | S | N1, D01 **L1** | the `MemLp G 1` clause of `MemForceR` (`Contracts/V1/Data.lean:544`) is literally `MemL1Hm`; the sup bound is `ContDiffOn ℝ ∞ G futureTimes` (`:544`) restricted to a compact, i.e. `IsCompact.exists_bound_of_continuousOn`. Both are bookkeeping the contract states explicitly so the consumer never re-derives them |
| **M1** | Sobolev order monotonicity on the D01 carrier, `s ≤ r → sobolevENorm s z ≤ sobolevENorm r z`, so that `higherOrderBound` at `m ≤ 2` follows from `m = 3` | S | D01 **L5** (`RECONCILIATION.md:156`) | already scoped by D01: binds `Paper3.sobolevOrderLowering` (`Paper3/SobolevOrderLowering.lean:26`), `sobolevOrderLowering_norm_le` (`:39`). Not A04's to prove — consume |
| **D1** | From `HasSmoothSobolevPath T u`, the derivative of the squared norm: `HasDerivAt (fun r => ‖G r‖²) (2⟪G t, G' t⟫) t` on `Ioo 0 T`, and `sobolevNormAt (m:ℝ) u r = ‖G r‖` there | **M** | N1, A01's `ManuscriptLocalRegularity.sobolev_smooth` (`research/A01/Spec.lean:230`) | **narrowed in revision 2.** Supplying the `C^∞`-in-time datum path is no longer part of this unit: it is now the explicit hypothesis `HasSmoothSobolevPath` of the three differential fields (`REVIEW.md` finding 4), and is A01's obligation to produce. What remains is turning it into the inner-product derivative on the D01 carrier. Template: `EulerOrdinarySobolev.ordinaryWord_hasDerivWithinAt … .norm_sq` as used at `Source/OrdinaryViscousStability.lean:88` and `Euler/OrdinaryEulerL2Stability.lean:79`. `ClassicalSolutionR.sobolev` alone gives only `ContinuousOn`, which is why the hypothesis is needed |
| **G1** | **eq:Rhigh** on the D01 carrier: pairing eq:projected with `u` in `H^m`, the pressure drop by solenoidality, integration by parts of `∇·(u⊗u)`, Cauchy–Schwarz, then `⟪A03:outerProductTame⟫` | **L** | D1, M1, `TameProductAPI.outerProductTame`, `BoundedRepresentativeAPI` | **gap, and the mathematical core of the lane.** Nothing in tree pairs a *forced viscous* equation in `H^m` on the datum carrier. Closest: `EulerOrdinarySobolev.integer_energy_tame` (`Euler/OrdinaryTameEnergy.lean:123`) + `integerEnergyDerivative_bound` (`Euler/OrdinaryEulerHigherEnergy.lean:56`) — same all-order shape, Euler, jet carrier, no dissipation, no force. Carrying it across is D01 unit **L2** (`RECONCILIATION.md:153`, gap in the `⟸` direction at non-compact data), which is why this is **L** and not M. Shared with **A01 unit A2** |
| **Z1** | The `ζ`-regularized division **with a linear term**: from `E' ≤ 2(K(t)E + b(t)√E)` and `E ≥ 0`, for every `ζ > 0`, `(d/dt)√(E+ζ²) ≤ K(t)√(E+ζ²) + b(t)`; and the `ζ↓0` integral form `√(E t) ≤ √(E t₀) + ∫_{t₀}^t (K√E + b)` | **M** | — (pure scalar calculus) | **near-hit.** `Paper1.sqrt_energy_le_primitive` (`Paper1/ScalarEnergy.lean:22`) is this lemma **without** the `K(t)E` term and with `E 0 = 0` assumed; its proof (regularize, differentiate `√(E+δ²)`, `antitoneOn_of_hasDerivWithinAt_nonpos`, let `δ↓0` through `le_of_forall_pos_le_add`) generalizes directly. The same `ζ` device is needed at `02-preliminaries.tex:152`, `04-whole-space.tex:103` and `:121`, so **book it once** and let C01 and I01 reuse it. Shared with **A01 unit A2** |
| **G2** | **eq:highcontinuation**: Young's absorption of `C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}` into `ν‖∇u‖²_{H^m}`, fixing `Cgron m ν = (Chigh m)²/(4ν)`, then Z1 | S | G1, Z1 | arithmetic once G1 and Z1 exist. `Paper1.critical_energy_absorption` (`Paper1/ScalarEnergy.lean:68`) and `Paper1.absorbed_energy_inequality` (`Paper1/ScalarEnergyAuxiliary.lean:12`) are the same absorption step at the critical order and are the template. Shared with **A01 unit A2** |
| **G3** | **Variable-coefficient Grönwall**: from `y(t) ≤ y(t₀) + ∫_{t₀}^t (c(s)y(s) + b(s))` with `c ≥ 0` locally integrable and `b ∈ L¹`, `y(t) ≤ (y(t₀) + ∫b)·exp(∫c)`; hence `higherOrderBound` from G2 and `∫₀^S‖u‖²_{H²} < ∞` and `MemL1Hm` | **M** | G2, F1 | **gap, and the hardest unit that is not G1.** Mathlib's `le_gronwallBound_of_liminf_deriv_right_le` and `norm_le_gronwallBound_of_norm_deriv_right_le` (`Mathlib/Analysis/ODE/Gronwall.lean:112,134`) take a **constant** `K`; `discrete_gronwall_prod_general` (`DiscreteGronwall.lean:50`) has variable coefficients but is discrete; the in-tree `EulerOrdinarySobolev.linear_stability_within` (`Euler/OrdinaryEulerL2Stability.lean:46`) is a thin wrapper on the constant-`K` Mathlib lemma. The integrating-factor proof (`y·exp(−∫c)` is non-increasing) is standard and self-contained. **Prior art (lane 041):** a variable-coefficient Grönwall by the same integrating-factor route already exists in tree, `EulerOrdinarySobolev.variable_linear_stability` (`Euler/OrdinaryVariableGronwall.lean:14`), but it is **homogeneous** (`b = 0`), **differential-form** only, anchored at **`t₀ = 0`**, and bundles the coefficient as a `C(Icc 0 T, ℝ)`, so it cannot express `higherOrderBound`'s `+ ‖f‖_{H^m}` term and G3 is not derivable from it. Lane 041 supplies the inhomogeneous, integral-form, general-`t₀` version in `formalization/NSFormalization/Section4/A04/Gronwall.lean` (`gronwall_integral`, `gronwall_deriv`, `gronwall_integral_mul`), continuous `c, b ≥ 0` (which is what A04 provides on each compact `[t₀,t₁] ⊂ (0,S)`; the `L¹`-in-time character enters only at the sup over `t₁ ↑ S`) |
| **R1** | `restartBeyond` from A02's `restart`: uniformity of the `H¹` bound on `[0,S)` (G3 at `m = 1`, via M1), the force conditions (F1), then `t₀ > S − δ` | **M** | G3, M1, F1, `MaximalSolutionAPI.restart`/`.restart_datum`/`.restart_force`/`.uniqueness` | the step itself is A02's; A04's work is the limit `t₀ ↑ S` and checking that `restart`'s `δ` is independent of `t₀` and of `S`. Structural template for the "within one step of the supremum" argument: `MNS2.r3EndpointSafeProjected_horizons_unbounded_of_uniform_bound` (`FormalPatched/R3MildContinuation.lean:122`) |
| **C1** | `extendsBeyond` and `lifespanInfiniteOfLocallyFinite` from G3 and R1, on `maximalLifespanR` | S | R1, D01 **L10** (`RECONCILIATION.md:161`) | order-theoretic. Binds `Source.SmoothLifespan.lifespan_ge_of_forall_shorter` (`Source/SmoothLifespan.lean:101`), `lifespan_le_iff_no_extension` (`:58`), `lifespan_eq_of_forall_shorter_of_upper_bound` (`:124`) — all already proved on `Flow`/`lifespan`, transcribed to `ClassicalSolutionR`/`maximalLifespanR` by A02 |

**Critical path.** `D1 → G1 → G2 → G3 → R1 → C1`, with `Z1` off to the side of
`G2` and `N1/F1/M1` feeding everything.  The two **L**/hard units are `G1` (the
energy identity on the datum carrier, blocked behind D01 **L2**) and `G3` (the
variable-coefficient Grönwall, absent from Mathlib).  Everything else is bounded.

**Registered-contract dependencies.**  `TameProductAPI.outerProductTame`
(A03, merged and registered as `A03.tame_products`) for `G1`; `BoundedRepresentativeAPI.supNorm_le`/`.eLpNormTop_le`
(registered, `Contracts/V1/BoundedRepresentative.lean:200,213`) for `G1`'s product
step and for `R1`'s identification through A02's uniqueness.  No other registered
contract is touched; `Contracts/V1/GradientL6.lean`, `Scaling.lean`,
`Thresholds.lean`, `Packet.lean` and `Correction.lean` are not consumed by A04.

**D01 dependencies**, by unit number of `research/D01/RECONCILIATION.md` §3:
**L1** (datum uniqueness, `:152`) for N1; **L2** (`MemHInfty` ↔ jets, `:153`, with
its recorded `⟸` gap) for G1's carrier transport; **L5** (order monotonicity,
`:156`) for M1; **L10** (lifespan interface, `:161`) for C1.  **L12** (`:163`,
`MemForceR f → forceSobolevENorm q s f < ⊤` at every real `s`) is *not* needed —
A04 uses only integer orders, which `MemForceR` states directly.

---

## 5. What is genuinely new mathematics

Three things, in decreasing order of size.

1. **eq:Rhigh on the datum carrier with a force (unit G1).**  The all-order
   energy identity for the *forced viscous* equation, paired in `H^m` on
   `Contracts/V1/Data.lean`'s angular datum carrier, with the pressure term
   discharged by solenoidality and the nonlinearity closed by eq:tame.  The
   nearest in-tree statement, `EulerOrdinarySobolev.integerEnergyDerivative_bound`
   (`Euler/OrdinaryEulerHigherEnergy.lean:56`), is Euler, on the jet carrier,
   unforced and without dissipation; three of its four defects are on the
   critical path and the fourth (the carrier) is D01 unit **L2**, whose `⟸`
   direction is an open gap at non-compact data.  This is the single largest
   piece of new work in the lane and it is the piece `research/A01/COMPARISON.md`
   §3 already booked as unit **A2** for A01 — it must be written once.

2. **The variable-coefficient Grönwall (unit G3).**  The whole point of
   eq:criterion is that the Grönwall coefficient `C_{m,ν}‖u(t)‖²_{H²}` is only
   `L¹` in time; a bounded coefficient would make the statement trivial and would
   not be the manuscript's criterion.  Neither Mathlib
   (`Analysis/ODE/Gronwall.lean`, constant `K` and `ε`) nor the tree
   (`linear_stability_within`, a wrapper on it) has the integrable-coefficient
   version.  The proof is classical — multiply by `exp(−∫c)` and use monotonicity
   — but it is new here, and the `ℝ≥0∞`-to-`ℝ` bookkeeping around
   `squaredHTwoIntegral` (unit N1) is what makes it usable on the D01 carrier.

3. **The `ζ`-regularization *with a linear term* (unit Z1).**  The manuscript's
   own device at `appendix-a:139-141`.  The repository already contains the
   device in its pure form, `Paper1.sqrt_energy_le_primitive`
   (`Paper1/ScalarEnergy.lean:22`), for the packet energy — but only for
   `E' ≤ 2b√E` with `E 0 = 0`.  Adding the `K(t)E` term and dropping the initial
   vanishing is a genuine, if modest, generalization, and it is the one piece of
   A04 that four separate places in the manuscript need
   (`02-preliminaries.tex:152`, `04-whole-space.tex:103`, `:121`, and
   `appendix-a:141`).

Everything else in `ContinuationAPI` is transport (`N1`, `F1`, `M1`, `C1`),
arithmetic (`G2`), or the consumption of an already-specified contract (`R1`
consuming A02's `restart`, `outerProductTame` consuming A03).  **What A04 is
*not*:** it is not a new blow-up criterion, not a new local existence theorem,
and not a mild-solution continuation — the HeliCorgi continuation layer
(`FormalPatched/R3MildContinuation.lean`) answers a different question, as
`formalization/blueprint/EXTERNAL_REUSE.md:32` states, and is the source for
A01's unit **A2b** rather than for anything here.

## Lane 215 update — fixed-force restart and exact G3 (2026-09-16)

`Section4/A04/RestartFixedForce.lean` now proves, without analytic hypotheses,
`restartFixedForce_of_memForceR`: one positive lower bound for `localHorizon'`
uniform over **all** restart times in `[0,S]` and all admissible H⁷-bounded
data, for one fixed force. The common order-6 force bound is the continuous
path norm on `[0,S+1]`; the chosen horizon is antitone.

`higherOrderBound_of_gronwall : HigherOrderBound` is also unconditional and
uses the existing definition unchanged. A new overlap/uniqueness argument
proves `HasSmoothSobolevPath` for arbitrary classical solutions. The finite
H² integral then supplies the common Grönwall cap on all shorter intervals.
The separate `localCarrier_gronwall_bound` checks lane 179's literal closed
cylinder interface for the same selected solution; no carrier at a possibly
singular final endpoint is postulated.

The fixed-force consumers are proved **conditional on one remaining precise
fact**, `ShiftedLocalExtension`: an actual local classical solution starting
at an interior time extends the original problem's maximal lifespan. This
is the missing shifted union construction, not A02's existing same-origin
`patch`. The force-window, smooth-path and Grönwall inputs are discharged.
Thus unconditional lifespan continuation is **not yet delivered**.

V2 wording is still for the owner: the new R1 theorem fixes f and S before δ
and uses H⁷. It does not prove the old all-force/H¹ R1 statement. No original
`Restart`, `HigherOrderBound`, or contract was changed. Full statements,
satisfiability audit and proof route: [ATTEMPTS_RESTART_FIXED_FORCE.md](ATTEMPTS_RESTART_FIXED_FORCE.md).

## Lane 217 update — shifted extension closed (2026-09-16)

The remaining fact in the lane 215 update above is now proved:
`Section4/A04/ShiftedExtension.lean` supplies
`shiftedLocalExtension : ShiftedLocalExtension`, with no named input.
`exists_shifted_glue` constructs the original problem's classical solution
on `[0,b+L)` when the restarted interval reaches beyond T. A02 classical
uniqueness identifies velocities; basepoint pressure normalization makes
pressures literally agree on the overlap. Pasting at `(b+T)/2` avoids extending
any gauge function across T and proves every classical-solution field.

The new `restartBeyond_of_memForceR'`, `extendsBeyond_of_memForceR'`, and
`lifespanInfiniteOfLocallyFinite_of_memForceR'` have **no remaining analytic or
gluing input**. They retain the stated ν>0, datum, `MemForceR`, solution and
norm/integral hypotheses. Together with lane 215's unconditional fixed-force
windows and `HigherOrderBound`, this closes the fixed-force/H⁷ continuation
chain. Existing conditional declarations remain unchanged for compatibility.
This does not prove the old all-force/H¹ R1 statement or change a contract.

See [ATTEMPTS_SHIFTED_EXTENSION.md](ATTEMPTS_SHIFTED_EXTENSION.md) for the
construction, exact uniqueness API, and pressure-gauge treatment, and
[REPORT_217.md](REPORT_217.md) for validation.

## Paper vs V2

The owner-approved V2 registration deliberately exposes the continuation chain
that the tree proves without relabelling it as the paper's stronger restart.
The paper's H¹ sentence remains named by
`Contracts.V2.Continuation.ManuscriptHorizonLowerBoundH1`, but that definition
is not a field, theorem or axiom and remains open.

| paper sentence | V1 field (H¹) | V2 field (H⁷, fixed force) | why V2 suffices downstream | what the H¹ version would need |
|---|---|---|---|---|
| `appendix-a-local-theory.tex:147-152`: “The H¹ local existence bounds … give a common positive existence duration when restarting at t₀↑S”; the Spec/V1 quantifiers choose `δ` from viscosity and a common H¹ datum/force bound before choosing the force | `Restart`: `δ` is uniform over every admissible force and restart time, with an H¹ datum bound and an `L¹_tH¹_x` force bound. It remains open and is not included as a proved V2 field. | `ContinuationV2API.restart`: for each fixed `f ∈ F_R` and compact horizon `S`, both placed before `∃ δ`, one `δ > 0` works for every `t₀ ∈ [0,S]` and every `a' ∈ X_R` in a finite H⁷ ball. This is exactly the owner-approved `RestartFixedForce` recut. | `research/A04/REPORT_215.md` §3 identifies that all consumers keep the same force. `restartBeyond`, `extendsBeyond`, and `lifespanInfiniteOfLocallyFinite` (closed unconditionally in lane 217), and A02's `exists_maximal` construction (lane 213), restart that same force at data whose H⁷ norms are bounded by `higherOrderBound`. Cross-force uniformity is never used. | A forced quantitative H¹ local theory on the mild stack: a horizon lower bound depending only on the H¹ datum and force bounds, valid uniformly across the whole force class. The proved H⁷ ball cannot be enlarged to an H¹ ball, and compactness of one force's shifted path cannot supply cross-force uniformity. |

Thus V2 is sufficient for the formalized downstream continuation argument, but
it does **not** prove the manuscript's H¹ local-existence sentence. In
particular, neither stronger-to-weaker Sobolev embedding nor the fixed-force
compactness argument reverses the two missing implications: controlling an H⁷
ball does not control every H¹-bounded datum, and a duration for one fixed force
does not become uniform over all forces.

## Lead corrections (review 230, 2026-09-17)

1. "uninhabited" → "unproved" wherever the H¹ sentence is described (it is an open proposition, not a claim of falsity).
2. A02's `exists_maximal'` (lane 213) does **not** depend on lane 179's Grönwall bound; it uses lane 211's `localHorizon'`/`localCarrier` only. The Grönwall bound enters the A04 continuation consumers (215/217), not maximal existence.
3. The contract's restated `timeShift` is **definitionally equal** to lane 160's (bridged by `rfl`), not a token-for-token copy.
