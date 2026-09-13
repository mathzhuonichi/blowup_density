# R42 — reviewer verdict on `R42.insertion_family` v1 (lane 027)

Reviewed at `3862f4c` on `erenup/027-R42-assembly-contract`, base `erenup/integration`
(merge-base `ac6b1b2`; no rebase needed — the base-ref gate passed as given). Nothing in the tree
was modified; the scratch axiom file was deleted.
## Verdict — ACCEPT, with two documentation corrections before merge

The registered content is faithful to Theorem 4.2 and is a genuine composition: every field of
`InsertionFamilyAPI` is discharged in `Bindings.insertionFamily` from `PacketAPI`/`CorrectionAPI`/
`ScalingAPI`/`Data.ClassicalSolutionR` fields; none is `True`-shaped, a hypothesis about an
unspecified proposition, or inert (the binding is the inhabitant, built from the *given* `S` and
`R`, with `A.scaling = S ∧ A.a = a` pinned by the test). The two omitted clauses are isolated in an
unregistered structure with an honest docstring. All issues below are documentation-level.

## 1. Gates (worktree root, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`)

| command | result |
|---|---|
| `make check` | exit 0, 8.3 s — plan check, `check_contracts` (7), 13 policy tests, 30 work items consistent |
| `make test` | exit 0, 2.1 s (replay) — **all seven** contracts print `checked; standard logical axioms only`, incl. `Tests/InsertionFamily.lean:19` |
| `make test-mutations` | exit 0, 8.8 s — `implementation_refactor` accepted; `admitted_proof`, `extra_axiom`, `weakened_hypothesis` rejected as required |
| `check_contracts.py --base-ref erenup/integration` | exit 0, 9.0 s — `registered_contracts: 7`, `base_compatibility_checked: true` |
| `build_changed_lean.py --base-ref … --dry-run` | exactly four: `Bindings.InsertionFamily`, `Contracts.V1.InsertionFamily`, `NSFormalization.Section4.R42.Assembly`, `Tests.InsertionFamily` |
| same, without `--dry-run` | exit 0, **10.3 s**, `Build completed successfully (9388 jobs)` — full replay, closure prebuilt here |
| `tasks.py render` | cards regenerate **byte-identically** (`git status` empty afterwards) |

`check_formalization_plan.py` reports `source_hashes_match: false`; the sole drifting file is
`formalization/lakefile.toml`, pre-existing and untouched here. The `sorry` it lists is in
`Paper1/BoundaryCorollary.lean`, **not** in R42's 624-module closure.

## 2. Axioms and hygiene

Scratch `#print axioms` over **every** public constant of the three new modules (not only the 42
source-level declarations): Assembly 6, `Bindings.InsertionFamily` 28, `Contracts.V1.InsertionFamily`
65 — **99 constants, each exactly `[propext, Classical.choice, Quot.sound]`**, none forbidden, none
with an axiom set of size ≠ 3. `checkedInsertionFamily` and `Bindings.insertionFamily` printed the
three explicitly. The "42" in `ATTEMPTS.md` is the source-level count (6+25+11) and is correct.
Hygiene grep over the four files: one hit, the word `True` inside a docstring disclaiming
placeholders. No `set_option maxHeartbeats` — §6.3 of `ATTEMPTS.md` records the `whnf` blow-up in
`blowup` being fixed by a concretely-typed intermediate `have` instead, which is the right repair.

## 3. Clause table — Theorem 4.2 (`04-whole-space.tex:31-43`) and its proof (`:44-55`)

| paper clause (line) | field | supplied by | exactness |
|---|---|---|---|
| *the* solution for `a, g` regular through `T+δ` (`:32`) | `reference`, `reference_velocity/_pressure` | `Data.ClassicalSolutionR ν a g (T+δ)`, hypothesis | exact but for the definite article (excluded) |
| `T^ν_{max,R}(a,g_ε)=T` (`:34`) | — | — | **excluded** → `InsertionLifespanAPI.lifespan` |
| `limsup_{t↑T}‖u_ε(t)‖_∞=∞` (`:35`) | `blowup` | `scaledBlowup` + `correction_cancels_germ` via `Source.inserted_speed` | pointwise `SpeedUnboundedAt T`; adjudication 3 |
| `u_ε=v` on `0≤t≤T-2ε²` (`:36`) | `history` | `correction_vanishes_before` + `zeroPast_dilate_early` | exact (proved for all `t ≤ T-2ε²`) |
| same initial velocity (`:13`, `:53`) | `initial` | `ClassicalSolutionR.initial` + the two vanishings at `t=0` | exact |
| velocity difference ⊆ `B`, `t<T` (`:37-38`) | `velocityDifference_support` | `correction_support_ball`; `delayed_full_support` + `carrier_subset` + `eps_space` | exact, guard `t ∈ Ico 0 T` |
| `g_ε-g ∈ C_c^∞(B×(0,∞))` (`:38`) | `forceDifference_compact` + `forceDifference_ball` | I02 force fields; `parabolicForce_smooth/_positive_support` + new `parabolicForce_ball` | exact; **no** time guard (C3), correct |
| `‖u_ε-v‖_{E_T}≤(M+D)ε^{1/2}+Cε^{3/2}` (`:39-41`) | `energyRate` | `perturbationEnergyBound`, verbatim | exact: `M=P.energyBound`, `D=P.dissipationBound`, `C=correctionEnergyConst` (eq:wE); `ℝ≥0∞` norm, non-vacuous |
| `‖g_ε-g‖_{L^q_tH^s}→0`, `q∈{1,2}`, `s<2/q-3/2` (`:42`) | `forceConvergence` | `ScalingAPI.forceConvergence`, verbatim | exact: `thresholds.exponent q.toReal 0 = 2/q-3/2`, limit `𝓝[>] 0` |
| same family (`:43`) | structural | one `ε₀`, one `velocity/pressure/force`, carried `scaling`, `A.scaling = S` | exact |
| `g_ε ∈ F_R` and *a solution* `u_ε` (`:32`) | partial: `velocity_smooth`, `pressure_smooth`, `initial`, `incompressible`, `momentum` | `ClassicalSolutionR.*` + I02/I03 via `inserted_{equation,divergence}_slab` | `MemForceR g_ε`, `ClassicalSolutionR.{sobolev,pressure_gradient}` **absent**; adjudication 2 |
| displays `u_ε=v+w_ε+U_ε`, `p_ε=π+P_ε`, `g_ε=g+H_ε+F_ε` (`:47-49`) | three `*_formula` | definitions, `rfl` | exact |
| "the equation is exact" (`:51`) | `momentum` | `corrected_background` + `scaledEquation` + `correction_cancels_germ` | `Ioo 0 T`, matching `ClassicalSolutionR.momentum` (two-sided `temporalDerivative`) |
| incompressibility (eq:NS; `03-torus.tex:332`) | `incompressible` | `ClassicalSolutionR.divergence` + `perturbation_divergence_free` | `Ico 0 T`, **including `t=0`** |
| compact pressure representative (`:51`) | `pressureDifference_formula` + `_support` | `pressure_formula`; `delayed_pressure_support` + `pressure_support` + `carrier_subset` | exact, gauge pinned pointwise (not up to `c(t)`) |
| `u_ε-v` div-free (`03-torus.tex:295`; used `:306,:308`) | `velocityDifference_divFree` | `perturbation_divergence_free`, verbatim | exact, `Ico 0 T` |

Every velocity/pressure conclusion carries `0 ≤ t < T`; no force conclusion carries a time guard.
One `ε₀`, one family, `ε ∈ Ioc 0 ε₀` throughout (⊇ the paper's `0<ε<ε₀`; matches I02/I03).
**Exclusions.** `InsertionLifespanAPI` carries exactly `referenceLifespan` and `lifespan`, is absent
from `contracts.json` (`checkedInsertionFamily` mentions only `insertionFamilyStatement`), and its
docstring names the real blockers (A02 uniqueness/continuation; A03 registered only in jet form).
Precedent: I03's unregistered `HomogeneousScalingAPI` in the same file.

**Reference choice.** `Data.ClassicalSolutionR` is right and strictly necessary; all four
`CorrectionAPI` reference hypotheses follow from it and not conversely. The worker's three
conclusions all check out — `initial`; `incompressible` at `t=0`
(`reference_divergence_free` is on `Ioo 0 (T+δ)`, `ClassicalSolutionR.divergence` on `Ico`); naming
`a`. It is in fact **four**: `velocity_smooth`/`pressure_smooth` on `Ico 0 T` (one-sided at `t=0`)
are equally unavailable from `reference_smooth` (`ContDiffOn … (Ioo 0 (T+δ) ×ˢ univ)`), and the
binding uses `R.velocity_smooth`/`R.pressure_smooth` for exactly that.

## 4. Adjudications

**(1) `K → K_*` via `threshold S := min S.ε₀ (r/(R_F+1))` — SOUND; R42 is the right place, for now.**
`forceRadius P` is `Classical.choose` on a proved existential (`HasCompactSupport P.force` ⇒ compact
spatial projection ⇒ bounded), a deterministic definition, not a hypothesis; `force_space_bound`
gives `ε·R_F ≤ r·R_F/(R_F+1) < r`, and `scaledForce = parabolicForce ε⁻¹ …` definitionally, so
`parabolicForce_ball` applies. Nothing is weakened: `eps_le_scaling` keeps every I02/I03 bound on the
smaller range, and the enlargement is genuinely needed only for `F_ε` (`U_ε`, `P_ε` lie in
`P.carrier`, already placed in `B` by `carrier_subset` + `eps_space`). The two rejected routes in
`ATTEMPTS.md` §3 are rejected for the right reasons — route 2 would have produced exactly the
undischargeable-hypothesis defect the I03 review flagged. **But only until I02 V2:**
`correctionStatement` pins `T, δ, v, π, g, x₀, r` and existentially binds `θRadius`, so nobody
reaching `CorrectionAPI` through `checkedCorrection` can relate `θRadius` to `supp F`; every future
consumer touching `F_ε`'s support repeats this shrink and acquires its own threshold. The clean fix
is an I02 V2 letting the caller pin `θRadius` above a prescribed compact set
(`K ∪ Prod.snd '' tsupport P.force`), after which `eps_space` alone places all five rescaled fields
in `B` and R42 can take `ε₀ = S.ε₀`. File that as an I02 V2 item; do **not** hold R42 for it.

**(2) `g_ε ∈ F_R` — the gap is real, correctly diagnosed, correctly not attempted.** Confirmed:
`Data.MemForceR` (`Data.lean:544`) is defined and used **nowhere else** in the project, and
`IsSobolevPath` appears only in `Data.lean` plus one comment. For every `m : ℕ` it demands a datum
path `G` with `IsSobolevPath m f G`, **`ContDiffOn ℝ ∞ G futureTimes`**, `MemLp G 1/2
forceTimeMeasure`. `Section4/I03/Angular.lean` gives, for a smooth compactly supported field,
`angularPath` + `angularPath_pairing` (datum at *every* `t`) + `memLp_angularPath` (every `q`) — and
**not** the path's time regularity, which nothing in the project constructs, and **not** additivity
`IsSobolevPath m g G₁ → IsSobolevPath m φ G₂ → IsSobolevPath m (g+φ) (G₁+G₂)`. The D01 unit needed is
`F_R + C_c^∞(R³×(0,∞)) ⊆ F_R` (`STATEMENTS.md:270`), concretely: (a)
`ContDiffOn ℝ ∞ (angularPath m φ …) (Ici 0)` for smooth compactly supported `φ`; (b) `IsSobolevPath`
additivity, from linearity of `angularRealization` and of the pairing; (c) the physical side,
`ContDiffOn ℝ ∞ (f+φ) futureDomain` and `MemLp.add` for the two time norms. Two corrections to the
worker's account: `ofReal T ≤ maximalLifespanR ν a g_ε` **is** a well-formed statable `Prop` — what
fails is that it is undischargeable, since `maximalLifespanR` is a supremum over
`Nonempty (ClassicalSolutionR ν a g_ε S)` and nothing produces an inhabitant; and the D01 unit alone
will not close it at R42, because `InsertionFamilyAPI` deliberately carries no
`hg : Data.MemForceR scaling.correction.g`, which an R42 V2 asserting `memF` must add.

**(3) `SpeedUnboundedAt` — acceptable as registered; the docstring's justification is wrong.**
Acceptable because `Data.lean` has no spatial `L^∞` norm and no left `limsup` at all, it is the form
`PacketAPI.speed_unbounded`/`ScalingAPI.scaledBlowup` produce, and — decisively — it is *equivalent*
to the paper's clause for every inhabitant, since `velocity_smooth` is co-carried: for `t ∈ Ioo 0 T`
the slice is continuous, so `∃ x, M < ‖u(t,x)‖` opens a positive-measure set and forces
`esssup > M`. The docstring's "it is *stronger* than the essential-supremum reading, since it
exhibits points" is **backwards** — `esssup > M` ⇒ positive measure ⇒ `∃ x`, so in isolation the
pointwise form is the weaker one; only continuity closes the converse. The second reason (an ess-sup
reading "would be about `v + w_ε + U_ε`" and `v` is unbounded) does not discriminate: an unbounded
`v` trivializes both readings equally. Replace both sentences with the continuity argument. The
limsup form needs three D01 additions: a spatial `L^∞` e-norm (`eLpNorm · ⊤ volume`);
`limsup … (𝓝[<] T) = ⊤`; and the bridge "continuous slice ⇒ `esssup = ⨆ x ‖·‖ₑ`" — after which
`blowup` yields it immediately. This is a documented deviation from `STATEMENTS.md:255-258` and
belongs in the `contracts.json` scope, not only in a docstring.

## 5. `contracts.json`, work item, cards, research notes

Scope reads *"Theorem 4.2's inserted family and all its quantitative clauses except the
maximal-lifespan identification and the reference-lifespan clause"* — both required exclusions
verbatim. `work_items.json` R42: `in-progress`, `erenup`, `["R42.insertion_family"]`;
`tasks/R42.md` and `TASKS.md` agree; `check_work_queue.py` passes; cards regenerate byte-identically.
`COMPARISON.md`/`ATTEMPTS.md` are substantially accurate and unusually candid — the clause table,
the field-by-field provenance, the three `K → K_*` routes and the non-reuse rationales for
`Source/InsertionFamily.lean` and `InsertionBreakdown.lean` all check out. Errors are listed below.

## 6. Issues, ranked

1. **MEDIUM — `contracts.json` scope is narrower than the truth.** A reader sees "all its quantitative
   clauses except [the two lifespan clauses]" and assumes `g_ε ∈ F_R` — an explicit clause at `:32` —
   is covered. It is not, nor is `u_ε` being a `Data.ClassicalSolutionR`. Append: *"; the force-class
   membership `g_ε ∈ F_R` and the `ClassicalSolutionR` fields `sobolev`/`pressure_gradient` for `u_ε`
   are not asserted, and the blow-up clause is registered in the pointwise `SpeedUnboundedAt` form."*
2. **MEDIUM — `blowup` docstring reverses the logical direction** (adjudication 3): "stronger …
   since it exhibits points" is false in isolation; the truth is equivalence given the co-carried
   `velocity_smooth`. The second justification is inert and should go. A strength claim inside a
   registered specification, so worth fixing before merge.
3. **MEDIUM-LOW — `ATTEMPTS.md` §2 misstates `correctionStatement`**: it says the statement
   "existentially binds `x₀` and `r`", but `Correction.lean:542-552` takes both as arguments and
   concludes `… ∧ A.x₀ = x₀ ∧ A.r = r`. Only `θRadius` is existentially bound. The decision (take `S`
   as a hypothesis so `B` is a parameter of R42, per `STATEMENTS.md:1276`) stands; the recorded reason
   is wrong and would mislead whoever next reasons about where `B` can be pinned.
4. **LOW-MEDIUM — "cannot even be stated" overstates** (adjudication 2): statable, undischargeable.
   Add that an R42 V2 asserting `memF` also needs a new `hg : MemForceR g` hypothesis field, so the
   D01 unit alone does not close the `≥ T` half.
5. **LOW — "three conclusions … only available this way" is four**: `velocity_smooth` and
   `pressure_smooth` on `Ico 0 T` also require the `ClassicalSolutionR` reference. This strengthens
   the choice; correct it in the contract docstring and `ATTEMPTS.md` §2.
6. **LOW — `COMPARISON.md` §4.2 "`ε₀` is *strictly* below `S.ε₀`"**: it is `min S.ε₀ (r/(R_F+1))`,
   hence `≤`, with equality when `S.ε₀ ≤ r/(R_F+1)`. The contract field is correctly `≤`.
7. **LOW — six docstring line citations drift by one.** `:33` (×2: "for all sufficiently small ε" and
   "there are `g_ε ∈ F_R`") → `:32`; `p_ε` display `:47` → `:48`; `g_ε` display `:48` → `:49`; "the
   initial value and earlier history are unchanged" `:52` → `:53`; "the same initial velocity" `:14` →
   `:13`; "the equation is exact" `:50-51` → `:51`. Same drift on `:52`/`:14` in `COMPARISON.md` §1.
   All other cited lines verified correct.
8. **LOW/cosmetic — `ATTEMPTS.md` §7 gate table is stale**: `build_changed_lean.py --dry-run` now
   reports the four modules, not `none` ("nothing committed yet" was true pre-commit).
