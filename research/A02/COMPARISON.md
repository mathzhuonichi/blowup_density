# A02 — source-to-target comparison, implications, implementation split

Lane 016, task **A02** ("Uniqueness and maximal solution identification"),
2026-09-13, tree state `4ba9f2b`.
Target contract: [`Spec.lean`](Spec.lean), namespace `BlowupDensity.A02.Draft`.

Manuscript object: the **uniqueness / maximal-lifespan / restart** third of
`prop:local` (`paper/sections/02-preliminaries.tex:105`), derived at
`paper/sections/appendix-a-local-theory.tex:115-125` (uniqueness and patching)
and `:147-152` (the restart), plus the lifespan identification of
`paper/sections/04-whole-space.tex:53`.

Everything quantified over is the canonical D01 object of
`verification/Contracts/V1/Data.lean`.  Existence is A01, the continuation
criterion `eq:criterion` is A04, the embedding `eq:Rproduct` is A03; none is
stated here.  Every `file:line` below was opened in this worktree.

---

## 0. What the target demands, sentence by sentence

| # | manuscript sentence | locus |
|---|---|---|
| S1 | "equation (NS) has a **unique** maximal smooth velocity, with pressure determined as above" | `02-preliminaries.tex:105-107` |
| S2 | "if `z = u₁ − u₂` for two such solutions with the same data, `½(‖z‖₂²)' + ν‖∇z‖₂² ≤ ‖∇u₂‖_∞‖z‖₂²`.  The coefficient is bounded on compact common intervals, since `u₂ ∈ C_tH³`.  Grönwall gives uniqueness." | `appendix-a-local-theory.tex:119-124` |
| S3 | "**Patching** these local solutions defines the maximal lifespan" | `appendix-a-local-theory.tex:124-125` |
| S4 | "local uniqueness defines a maximal classical lifespan, denoted `T^ν_{max,R}(a,f)`" | `02-preliminaries.tex:32-33` |
| S5 | "a reference solution is *regular through `T`* if it extends smoothly to `[0,T+δ]`" | `02-preliminaries.tex:34-36` |
| S6 | "The `H¹` local existence bounds … give a **common positive existence duration** when restarting at `t₀ ↑ S` … One interval extends beyond `S`, and **uniqueness identifies it with the original solution on the overlap**." | `appendix-a-local-theory.tex:147-152` |
| S7 | "Proposition 2.1 identifies the solution with the unique maximal solution.  An extension through `T` would be bounded in `C_tH²` on a neighbourhood of `T`, hence bounded in `L^∞` by (eq:Rproduct), contradicting the blowup of `U_ε`.  Thus its maximal lifespan is exactly `T`." | `04-whole-space.tex:53` |
| S8 | "the solution for `a ∈ X_R` and `g ∈ F_R`, **regular through `T+δ`**" — the definite article | `04-whole-space.tex:32` |

S1–S3 are `UniquenessAPI` + `patch`; S4–S5 the lifespan order theory; S6
`restart`; S7 `lifespan_le_of_unbounded` + `insertion_lifespan_eq`; S8
`referenceLifespan` + `maximal_unique`.

---

## 1. Field-by-field comparison

Carrier column: **phys** = D01's pointwise real `VelocityField = ℝ × Space →
Space` (the carrier of `ClassicalSolutionR`); **SmoothL2** = OpenAI/local
`SmoothL2Field Space` paths; **Bessel-ℂ** = HeliCorgi `R3HsVelocity 3 =
Lp (EuclideanSpace ℂ (Fin 3)) 2`.  Solution notion: **classical** = pointwise
`ClassicalSolutionR`/`Flow`; **mild** = Duhamel identity in a Banach space.

### 1.1 The two `UniquenessAPI` fields

| field | paper | existing declaration / gap | mismatch |
|---|---|---|---|
| `velocity_unique` | S1, S2 (`appendix-a:119-124`) | **`NSFormalization.Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc`**, `formalization/NSFormalization/Source/BoundedViscosityUniqueness.lean:23`.  Hypotheses: `0 < T`, `0 < ν`; `ContDiffOn ℝ ∞` of `u,v,p,q` on `Comparison.slab 0 T = Icc 0 T ×ˢ univ`; `UniformFiniteEnergy (Icc 0 T)` for **both**; `0 ≤ B`, `‖u (t,x)‖ ≤ B` and `0 ≤ G`, `‖spatialDerivative u t x‖ ≤ G` on `Icc 0 T` for **one** of them; `spatialDivergence = 0` on `Ioo 0 T` for both; `residual ν u p = residual ν v q` on `Ioo 0 T`; `u(0,·) = v(0,·)`.  Conclusion `∀ t ∈ Icc 0 T, ∀ x, u (t,x) = v (t,x)`.  Carrier **phys**, notion **classical**, force implicit (equal residuals), arbitrary `ν > 0`. | **This is the right theorem on the right carrier** and it is *not* in the task card's starting evidence.  Three deltas: (a) closed `Icc 0 T` vs D01's half-open `Ico 0 T` — apply at each `T' < min T₁ T₂` and take the union; (b) `residual` (`Source/Insertion.lean:21`) and `NavierStokesR3.ProblemStatement.navierStokesResidual` (`vendor/…/NavierStokes/R3/ProblemStatement.lean:57`) are the *same expression*, so `ClassicalSolutionR.momentum` (both sides `= f (t,x)`) discharges `hNS` by `rfl`; (c) **the real gap** — `UniformFiniteEnergy`, `hB` and `hG` are not fields of `ClassicalSolutionR` (unit **U1**). |
| | | `NSFormalization.Source.OrdinaryViscousUniqueness.velocity_unique`, `Source/OrdinaryViscousUniqueness.lean:26` (the task card's evidence).  Same mathematics; hypotheses `0 ≤ T`, `0 ≤ ν`, two velocity paths `U₁ U₂ : Icc 0 T → SmoothL2Field Space` with **separate** derivative paths `D₁ D₂`, jet-continuity `∀ n, Continuous (fun t => (Uᵢ t).jetLp n)`, `HasDerivAt` at interior times, pressures `Icc 0 T → Space → ℝ` each `ContDiff ℝ ∞`, classical `divergence = 0`, the equation, equal data.  Carrier **SmoothL2**, notion **classical**, forced. | Strictly harder to feed than `classical_uniqueness_on_Icc`: the carrier is `SmoothL2Field`-valued paths, so it needs D01 unit **L2** (`MemHInfty` ⟷ the jet form `∀ n, MemLp (iteratedFDeriv ℝ n a) 2 volume`, `Data.lean:487-491`) *and* a time-derivative path `D` extracted from `velocity_smooth`.  It buys nothing `classical_uniqueness_on_Icc` does not.  **Not the recommended source.** |
| | | HeliCorgi `MNS2.r3EndpointSafeProjectedMildSolution_unique`, `formalization/FormalPatched/EndpointSafeTwoSpaceUniqueness.lean:231` (vendor `:222`), from the abstract `EndpointSafeTwoSpaceDuhamelContract.IsMildSolutionOn.unique` `:119` (vendor `:110`).  Genuinely **unrestricted** — no ball, no realness, no smallness.  Carrier **Bessel-ℂ** at order 3, notion **mild**, **unforced**. | Three blocking mismatches, each an A01-sized campaign: no forcing in `EndpointSafeTwoSpaceDuhamelContract` (A01 edge **F1**, sized **L**), the Bessel↔angular Sobolev bridge (A01 unit **C1c**), and `eq:mild` on the D01 carrier (A01 edge **M**, which needs a whole-space heat semigroup that does not exist in tree).  The manuscript's own proof is an energy estimate, not a Duhamel contraction, so none of this is on A02's critical path. |
| `pressure_gauge` | S1 "with pressure determined as above", `02-preliminaries.tex:31` | **gap.**  No in-tree declaration concludes anything about two pressures.  `Data.lean:589` `PressureGaugeEquivOn` is the target relation; `Source/OrdinaryViscousUniqueness.lean:53-64` (`gradient_mem … gradientSpace`) shows only that each residual is a gradient. | Unit **U3**.  Inputs: `ClassicalSolutionR.momentum` at both solutions and equal velocities give `pressureGradient p₁ = pressureGradient p₂` on `Ioo 0 (min T₁ T₂)`; connectedness of `R³` makes the difference spatially constant; `pressure_smooth` on `Ico 0 T ×ˢ univ` carries it to `t = 0` by continuity.  `momentum` is imposed on `Ioo` only (`Data.lean:640`), which is exactly why the `t = 0` endpoint is a separate step. |

### 1.2 Lifespan order theory

`Source/SmoothLifespan.lean` proves the whole of it — for `Flow`, not for
`ClassicalSolutionR`.  Every proof there is **structure-agnostic**: it uses only
`Nonempty (Flow ν a f S)`, `horizon_pos` and `iSup`, and `lifespan`
(`SmoothLifespan.lean:41`) is *syntactically* `maximalLifespanR`
(`Data.lean:657`) with `Flow` in place of `ClassicalSolutionR`.

| field | paper | existing declaration | mismatch |
|---|---|---|---|
| `horizon_le_lifespan` | S4; assigned to A02 by `research/A01/Spec.lean:371-372` | `SmoothLifespan.horizon_le_lifespan`, `Source/SmoothLifespan.lean:44` | rename `Flow → ClassicalSolutionR`; proof is `le_iSup_of_le` twice. |
| `lifespan_le_iff` | `02-preliminaries.tex:42` eq:Rsingularforces via `Data.lean:672` `breakdownSetIn` | `SmoothLifespan.lifespan_le_iff`, `:48` | same; needs `0 ≤ T`. |
| `lifespan_le_iff_no_extension` | S7 (the contrapositive Theorem 4.2 argues in) | `SmoothLifespan.lifespan_le_iff_no_extension`, `:58` | same. |
| `lifespan_ge_of_forall_shorter` | S7, the `≥` half of "`T^ν_{max,R}(a,g_ε) = T`" | `SmoothLifespan.lifespan_ge_of_forall_shorter`, `:101`; packaged as `lifespan_eq_of_forall_shorter_of_upper_bound`, `:124` | same. |
| `restrict` | S3 | `SmoothLifespan.Flow.restrict`, `:83` (`ContDiffOn.mono` field by field) | `ClassicalSolutionR` has two fields `Flow` lacks — `sobolev` (`Data.lean:643`) and `pressure_gradient` (`:647`) — both restricted by `Ico`-monotonicity, and lacks the three `Flow` has (`energy`, `velocity_bound`, `derivative_bound`).  Mechanical. |
| `patch` | S3 | **gap**, but a cheap one. | With `velocity_unique` no gluing is needed: WLOG `T₁ ≤ T₂`, take `w := u₂`; the agreement clauses are `velocity_unique`/`pressure_gauge`.  `max T₁ T₂` is then literally one of the two horizons. |
| `regularThrough_iff`, `referenceLifespan` | S5, S8 | **gap.**  `bad_or_regular_reference` (`Source/SmoothLifespan.lean:70`) is the two-case alternative `lifespan ≤ ofReal T ∨ ∃ S > T, Nonempty (Flow …)`, i.e. the *forward* half in disjunctive form. | The backward half needs `restrict` to shrink a horizon `S > T` to `T + (S−T)/2`.  `referenceLifespan` then halves once more to get R42's **strict** `T + δ < T_max` (`research/section4/STATEMENTS.md:333`) and settles risk note **O2** (`:388-392`). |

### 1.3 Maximal solution, restart, insertion

| field | paper | existing declaration / gap | mismatch |
|---|---|---|---|
| `IsMaximalSolution` (def) | S1, S4 | **gap.**  `research/section4/STATEMENTS.md:1198` fixes the arity `ν a f u p`; "DraftB has the lifespan but not yet the predicate".  Nothing in `Source/` or HeliCorgi names a chosen maximal trajectory: `R3MildContinuation.lean:30-33` says outright "the glued maximal trajectory `u* : [0,T*) → H³` … is not yet constructed". | A02 defines it.  The literal-equality clause (`w.velocity = u`) needs a `ClassicalSolutionR` **congruence** lemma — the structure's fields depend only on the germ on `Ico 0 S ×ˢ univ` (`ContDiffOn.congr`; `momentum` at `t ∈ Ioo 0 S` sees a full spacetime neighbourhood) — which is part of unit **U7**. |
| `exists_maximal`, `maximal_unique` | S1, S8 | **gap.** | Directed union over `S ↑ T_max` with coherence from `velocity_unique`; discharges the R42 risk note "the definite article presupposes uniqueness (A02)" (`STATEMENTS.md:393-395`). |
| `restart_datum` | S6, the restart initial velocity | **gap.** | `MemHInfty (u(t₀,·))` from `ClassicalSolutionR.sobolev` at every `m` plus `velocity_smooth`; `IsSolenoidal` from `divergence` at `t₀`.  Needed because A01's `localSolution` only accepts `a ∈ initialClassR`. |
| `restart_force` | S6, "`f` is bounded into `H¹` on `[0,S+1]`" | **gap.** | `MemForceR` (`Data.lean:544`) is smoothness on `futureDomain` plus `MemLp _ 1`/`MemLp _ 2` of each order-`m` datum path over `positiveTimeMeasure`; a forward shift by `t₀ ≥ 0` restricts both integrals and preserves one-sided smoothness at the new origin.  Pure measure theory, no PDE. |
| `restart` | S6 | **gap** on the manuscript class.  HeliCorgi has the *shape* — `MNS2.r3EndpointSafeProjected_exists_extension_of_bounded`, `formalization/FormalPatched/R3MildContinuation.lean:93` (vendor `:84`): a mild solution bounded by `R` on `[0,T]` extends to `T + r3MildLifespan ν R`, with `r3MildLifespan_antitone` `:67` supplying the *uniform* step, and `IsR3EndpointSafeProjectedMildSolutionOn.restart` / `.concat` (`vendor/HeliCorgi/Formal/EndpointSafeTwoSpaceRestart.lean:185`, `EndpointSafeTwoSpaceConcatenation.lean:232`) supplying the shift and the glue.  Carrier **Bessel-ℂ**, order 3, **mild**, **unforced**. | The HeliCorgi step is quantified by a norm ball `R` on the *trajectory*, A01's by an `H¹` ball on the *datum*; both are "one `δ` before the datum", so the shape transfers, but the carrier does not (F1 + C1c + M again).  On the manuscript class the glue is easier than HeliCorgi's `concat`: since `t₀ ∈ presingularTimes` there is `S > t₀` with a solution on `[0,S)`, so the original and the restarted piece **overlap on `[t₀,S)`**, uniqueness identifies them there, and smoothness of the glued field at every point of `[0,t₀+δ)` comes from one piece on a full neighbourhood.  No smooth-matching lemma at the single point `t₀` is needed. |
| `lifespan_le_of_unbounded` | S7 | **`NSFormalization.Source.LocalizedBlowup.no_continuous_continuation`**, `Source/LocalizedBlowup.lean:36`: from `IsCompact K` and `LocalSpeedUnboundedAt T K u`, **no** `δ > 0` and `W` with `ContinuousOn W (Icc (T−δ) (T+δ) ×ˢ K)` agreeing with `u` on `K` at late times `< T`.  Carrier **phys**, notion: none — it is a statement about continuous fields.  Used at `Source/InsertionBreakdown.lean:51`. | Two routes.  (i) *Manuscript route*: continuity of the `H²` datum path on the compact `Icc 0 T` (`ClassicalSolutionR.sobolev`, `Data.lean:643`) plus `‖z‖_∞ ≤ C‖z‖_{H²}` — **A03**.  (ii) *In-tree route*: `no_continuous_continuation`, which needs no embedding at all but needs the blow-up in the **local** form `LocalSpeedUnboundedAt T K u` on a compact `K`.  R42's difference is supported in the ball `B` (`04-whole-space.tex:38`), so the local form is available there, but it is a strictly stronger hypothesis than the contract's global `limsup ‖u(t)‖_∞ = ⊤`.  The contract states the manuscript's global form; §5 records the consequence. |
| `insertion_lifespan_eq` | S7, R42's `lifespan` + `isSol` (`STATEMENTS.md:345-347`) | `NSFormalization.Source.SmoothLifespan.insertion_lifespan_eq`, `Source/InsertionBreakdown.lean:68`: `lifespan ν a (g + G) = ENNReal.ofReal T`, from `insertion_lifespan_le` `:58` (via `insertion_has_no_extension` `:16`, which is `classical_uniqueness_on_Icc` + `no_continuous_continuation`) and `horizon_le_lifespan (insertionFlow …)` (`SmoothLifespan.lean:218`).  Hypotheses: `InsertionFamily.InsertionProperties ν U.velocity U.pressure g x₀ r T τ V Q G` (`Source/InsertionFamily.lean:15`) and a reference `Flow ν a g R` with `T < R`.  Carrier **phys**, notion **classical-`Flow`**. | The conclusion is about `SmoothLifespan.lifespan`, **not** `maximalLifespanR`.  Transporting it wholesale needs `Flow ⟺ ClassicalSolutionR`, which the task explicitly does not require and which is *false in one direction with the tools at hand* — `Flow` has no `sobolev` and no `pressure_gradient`.  See §2, implication **I5**: only `ClassicalSolutionR → Flow` is available, and it gives exactly the `≤` half. |

---

## 2. The exact source-to-manuscript implications needed

One direction each.  No equivalence with `Flow`, with `SmoothL2Field` paths or
with the HeliCorgi mild class is claimed anywhere.

* **I1** (`ClassicalSolutionR` ⟹ classical-uniqueness hypotheses).  For every
  `u : ClassicalSolutionR ν a f T` and every `T' ∈ (0,T)`:
  `ContDiffOn ℝ ∞ u.velocity (Comparison.slab 0 T')` and the same for
  `u.pressure`; `UniformFiniteEnergy (Icc 0 T') u.velocity`; and
  `∃ B ≥ 0, ∀ t ∈ Icc 0 T', ∀ x, ‖u.velocity (t,x)‖ ≤ B` together with the same
  for `spatialDerivative u.velocity`.
  Inputs: `velocity_smooth.mono`; `sobolev` at `m = 0` for the energy, at
  `m = 2, 3` for the two sup bounds, each bounded on the compact `Icc 0 T'`
  because the datum path is `ContinuousOn (Ico 0 T)`; **A03**'s `eq:Rproduct`
  second clause `‖z‖_∞ ≤ C‖z‖_{H²}`; and a D01-level realization lemma turning
  an order-0 datum into `SquareIntegrableAtTime` + a `kineticEnergy` bound
  (`vendor/…/NavierStokes/R3/ProblemStatement.lean:71,76,81`).
  **No converse is needed or available**: `Flow`'s `energy`/`velocity_bound`/
  `derivative_bound` do not produce `sobolev` or `pressure_gradient`.
* **I2** (uniqueness on closed slabs ⟹ uniqueness on the half-open common
  interval).  `classical_uniqueness_on_Icc` at every `T' < min T₁ T₂`, then
  `Ico 0 (min T₁ T₂) = ⋃_{T' < min T₁ T₂} Icc 0 T'`.
* **I3** (equal velocities ⟹ gauge-equivalent pressures).  `momentum` twice on
  `Ioo`, connectedness of `R³`, continuity of `pressure` at `t = 0`.
* **I4** (A01's local solution of the *shifted* problem ⟹ a longer
  `ClassicalSolutionR` of the original).  Restart at `t₀ ∈ presingularTimes`
  with `restart_datum`/`restart_force`, glue on the overlap `[t₀,S)` using
  **I2** at the shifted datum.  This is S6's "uniqueness identifies it with the
  original solution on the overlap", and is what makes `restart` quantitative:
  the step length is A01's `horizon_lower_bound` `δ`, chosen before the datum.
* **I5** (optional, only if R42 is routed through the source insertion).
  **I1** upgraded to `ClassicalSolutionR ν a f S → Flow ν a f S` gives
  `maximalLifespanR ν a f ≤ SmoothLifespan.lifespan ν a f`, hence every upper
  bound proved for `lifespan` — in particular `insertion_lifespan_le`
  (`Source/InsertionBreakdown.lean:58`) — is an upper bound for
  `maximalLifespanR`.  The reverse inequality is **not** available (it would
  need `Flow → ClassicalSolutionR`), and it is not needed: the `≥` half is
  proved directly on the manuscript class by `lifespan_ge_of_forall_shorter`.
  This is the precise sense in which A02 needs "only the source-to-manuscript
  implications for the inserted field, no equivalence with every legacy `Flow`"
  (`DEPENDENCY_GRAPH.md:188`).

---

## 3. Bounded implementation split

Size key as in `research/A01/COMPARISON.md` §3: **S** ≤ ~100 lines, no new
analytic machinery; **M** a self-contained lemma with real content and a known
proof; **L** a multi-file campaign.

| unit | content | size | depends on |
|---|---|---|---|
| **U1** | **I1**: from `ClassicalSolutionR` produce, on each `Icc 0 T'` with `T' < T`, `UniformFiniteEnergy` and the two uniform sup bounds on velocity and spatial derivative | **M** | **A03** (`eq:Rproduct` `‖z‖_∞ ≤ C‖z‖_{H²}`, orders 2 and 3), D01 unit **L1** (datum uniqueness), a D01 order-0-datum ⟹ `L²`-slice realization lemma.  *No A01 dependency.* |
| **U2** | `UniquenessAPI.velocity_unique` from `classical_uniqueness_on_Icc` (`BoundedViscosityUniqueness.lean:23`): `residual = navierStokesResidual` by `rfl`, `slab` mono, **I2** | **S** | U1 |
| **U3** | `UniquenessAPI.pressure_gauge` (**I3**) | **S** | U2 |
| **U4** | `restrict` — the `ClassicalSolutionR` analogue of `Flow.restrict` (`SmoothLifespan.lean:83`), plus the `ClassicalSolutionR` **congruence** lemma (fields depend only on the germ on `Ico 0 S ×ˢ univ`) that `IsMaximalSolution`'s literal equality needs | **S** | — |
| **U5** | `patch` (WLOG the longer horizon; no gluing) | **S** | U2, U3 |
| **U6** | the six order-theoretic fields: `horizon_le_lifespan`, `lifespan_le_iff`, `lifespan_le_iff_no_extension`, `lifespan_ge_of_forall_shorter`, `regularThrough_iff`, `referenceLifespan` — transcribe `SmoothLifespan.lean:44,48,58,101` with `Flow → ClassicalSolutionR` | **S** | U4 (backward half of `regularThrough_iff`) |
| **U7** | `exists_maximal` + `maximal_unique`: directed union over `S ↑ T_max`, coherence from U2/U3, transport along the congruence of U4 | **M** | U2, U3, U4, U6, **⟪A01:solution⟫** |
| **U8** | `restart_datum`, `restart_force`, and `restart` (**I4**) | **M** | U2, U4, U6, U7, **⟪A01:solution⟫**, **⟪A01:horizon_lower_bound⟫** |
| **U9** | `lifespan_le_of_unbounded` (S7): uniqueness, then the `C_tH²` bound on `Icc 0 T` and the embedding | **M** | U2, U6, **A03**; alternative route via `LocalizedBlowup.no_continuous_continuation` (`LocalizedBlowup.lean:36`) drops A03 but needs the local blow-up form (§5) |
| **U10** | `insertion_lifespan_eq`: assemble `lifespan_ge_of_forall_shorter` + U9 + U7 | **S** | U6, U7, U9 |

Totals: **6 S / 4 M / 0 L**.  Order: `U1 → U2 → U3 → {U4,U5} → U6 → U7 → U8`,
with `U9 → U10` after U6.  U4 and U6 can start immediately and in parallel with
U1; they touch nothing analytic.

### Dependencies on A01 units

* U7 and U8 consume A01's `LocalTheoryAPI.solution` and
  `horizon_lower_bound`, i.e. they wait on A01 units **A1, A2, A2b, A3, B1,
  B2** (`research/A01/COMPARISON.md` §3) actually inhabiting `LocalTheoryAPI`.
  Because `Spec.lean` restates those three fields as hypotheses, U7 and U8 can
  nevertheless be *proved as implications* before A01 lands.
* **The converse edge is real and must not be run backwards.**  A01 unit
  **A2b** ("order-`m` continuation + **cross-order agreement**") lists "A02's
  uniqueness" among its dependencies (`research/A01/COMPARISON.md:199`).  U1–U3
  depend only on D01 and A03 — **not on A01** — so the order
  `U1 → U2 → A2b → A1/A3 → U7/U8` is acyclic.  Anyone who tries to prove U2
  *from* A01's all-order local solution creates the cycle.
* A01 edge **M** (`eq:mild`) is attributed to "A02/A04"
  (`research/A01/COMPARISON.md:170`).  **A02's statement does not need it and
  its recommended implementation does not either**: the manuscript's uniqueness
  is the energy estimate S2, and `classical_uniqueness_on_Icc` is a pointwise
  classical theorem.  `eq:mild` stays with A04, or with whoever imports the
  HeliCorgi mild layer.

---

## 4. Route recommendation

**Take the local `Source/` classical route, not the HeliCorgi mild route.**

The decisive fact is one line: `classical_uniqueness_on_Icc`
(`Source/BoundedViscosityUniqueness.lean:23`) is already stated on
`VelocityField` — the *same* carrier as `ClassicalSolutionR` — for an arbitrary
`ν > 0`, with the force entering only as equality of residuals, and
`Source/Insertion.lean:21` `residual` is `rfl`-equal to the upstream
`navierStokesResidual` that `ClassicalSolutionR.momentum` uses.  The whole
distance from it to `UniquenessAPI` is unit U1, a hypothesis bundle.

The HeliCorgi uniqueness is stronger *as a theorem* (unrestricted, no ball, no
realness) but sits behind three A01-sized edges — F1 (no forcing field in
`EndpointSafeTwoSpaceDuhamelContract`), C1c (Bessel↔angular), M (`eq:mild` on
the D01 carrier).  Its continuation layer
(`FormalPatched/R3MildContinuation.lean:93,143`) is the only in-tree
continuation, which is why A01's unit A2b and A04 want it; **A02 does not**,
because S6's restart is a concatenation of two classical solutions across an
overlap, not an extension of a bounded mild trajectory.

`OrdinaryViscousUniqueness.velocity_unique` (`:26`), the task card's evidence,
is the same mathematics one carrier away; it is a fallback if U1 stalls on the
`UniformFiniteEnergy` clause, at the cost of D01 unit L2.

---

## 5. Risks and recommended DAG change

1. **`A03 → A02` is missing and is needed.**  S2's Grönwall coefficient
   `‖∇u₂‖_∞` is finite only through `eq:Rproduct`
   (`appendix-a-local-theory.tex:9-13`), so unit **U1** — and hence *every*
   other unit — depends on A03.  Today `DEPENDENCY_GRAPH.md:186` gives A02 the
   single dependency A01.  No cycle: `A03 ← D01, U04, A05`
   (`DEPENDENCY_GRAPH.md:216`), none of which descends from A02.
   `research/section4/STATEMENTS.md:405-411` already contemplates the edge for a
   different reason (R42's `L^∞` step) and rejects `A03 → A02` as "not existing
   today"; the correct conclusion is the opposite one — add it, and then R42
   needs no `H²` conversion of its own, because `lifespan_le_of_unbounded` and
   `insertion_lifespan_eq` take the blow-up in the manuscript's `L^∞` form
   verbatim (`04-whole-space.tex:35`, R42's `blowup` field at
   `STATEMENTS.md:348-351`).
2. **The A03-free fallback changes a hypothesis.**
   `LocalizedBlowup.no_continuous_continuation` (`LocalizedBlowup.lean:36`)
   proves the `≤` half with no embedding, but wants `LocalSpeedUnboundedAt T K u`
   on a **compact** `K`.  Global `limsup ‖u(t)‖_∞ = ⊤` does not imply it (the
   supremum could escape spatially).  R42 does have the local form — its
   velocity difference is supported in the ball `B` (`04-whole-space.tex:38`) —
   so if the A03 edge is refused, the contract's blow-up hypothesis must be
   restated locally and R42's `blowup` field must be strengthened to match.
   That is a **statement** change, not an implementation choice; it is recorded
   here rather than taken.
3. **`presingularTimes` uses a strict inequality.**  `IsMaximalSolution` asserts
   a solution on `[0,S)` for every `S` *strictly* below `T^ν_{max,R}`.  Nothing
   is asserted at the supremum, matching the manuscript, and matching the fact
   that `maximalLifespanR` is an `iSup` that need not be attained.  A reviewer
   should check that no consumer silently needs `≤`; R42 does not
   (`STATEMENTS.md:310`, "on every `[0,T']`, `T' < T`").
4. **`IsMaximalSolution` demands literal field equality.**  This is what makes
   the predicate usable downstream (R42 talks about `u_ε` outside `[0,S)`), but
   it forces the `ClassicalSolutionR` congruence lemma into U4.  The lemma is
   true — `momentum` at `t ∈ Ioo 0 S` sees a full spacetime neighbourhood and
   `pressure_gradient` is slicewise — but it must actually be proved, not
   assumed.
5. **The empty supremum.**  `maximalLifespanR` is `0` for a datum with no
   solution at all (`Data.lean:650-657`).  `IsMaximalSolution`'s first
   conjunct `0 < maximalLifespanR` blocks the resulting vacuity; without it the
   predicate would hold of every pair on a datum outside the class.
6. **`restart_force` is stated for `t₀ ≥ 0` only.**  D01's force fields are
   unconstrained at negative times (`Data.lean:120-128` `AgreesOnFuture`), so a
   backward shift would be meaningless.  Every use is at a presingular
   `t₀ ≥ 0`.
7. **Not claimed anywhere:** that `ClassicalSolutionR` and
   `SmoothLifespan.Flow` are equivalent; that `maximalLifespanR` and
   `SmoothLifespan.lifespan` are equal; that the maximal solution satisfies
   A01's `ManuscriptLocalRegularity` on every subinterval (true, and cheap once
   A01 lands, but no consumer in `research/section4/STATEMENTS.md` asks for it).
