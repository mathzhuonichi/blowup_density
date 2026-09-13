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

---

# R42 — reviewer verdict on `R42.insertion_lifespan` v1 (lane 096)

Reviewed at `e26b0b0` on `erenup/096-R42-lifespan-contract`, merge-base `cc0c06b`.
`origin/erenup/integration` has since advanced to `66292f7` (lanes 088/095/097), so the
lane needs a rebase at merge time; nothing it touches collides (its only registry edits are
appends). Nothing in the tree was modified by this review; the fidelity probe was compiled
from `/tmp`, outside the repo.

## Verdict — ACCEPT-WITH-NOTES

The Lean is right and the statement is faithful. The two clause fields are **byte-identical**
to the frozen 3-field `Contracts.V1.InsertionLifespanAPI` (checked mechanically, not by eye —
see the probe below), the two carried hypotheses are exactly the manuscript's, the two dropped
hypotheses are genuinely derived, the anti-substitution guard is in place, and all gates are
green with the standard three axioms. Every finding below is prose: wrong line citations and a
stale module docstring. None of them changes a single Lean statement, and none blocks the
mathematics — but a contract lane's provenance citations are part of the deliverable, and two
of these send a reader to unrelated text, so fix them before merge.

## 1. Statement fidelity — the core

### 1.1 Field-by-field

| new field | Lean type | manuscript source | frozen counterpart | verdict |
|---|---|---|---|---|
| `family : InsertionFamilyAPI ν P` | carries the registered `R42.insertion_family` | 04:43 "All of these conclusions hold for the same family of inserted solutions" | frozen `family`, identical | OK — no copy, no restatement |
| `memForce : Data.MemForceR family.g` | `g ∈ F_R` | 04:32 "`g\in\mathcal F_{\R}`" | **new** (not in frozen) | OK — see 1.3 |
| `regular : Data.RegularThrough ν family.a family.g (family.T + family.margin)` | reference regular through `T+δ` | 04:32 "regular through `T+\delta` for some `\delta>0`"; 02-preliminaries:34-36 | **new** (not in frozen) | OK — see 1.4 |
| `referenceLifespan : ENNReal.ofReal (family.T + family.margin) < Data.maximalLifespanR ν family.a family.g` | `T+δ < T^ν_{max,R}(a,g)` | 04:32 (the definite article); STATEMENTS.md:**333** | **byte-identical** | OK |
| `lifespan : ∀ ε ∈ Ioc (0:ℝ) family.ε₀, Data.maximalLifespanR ν family.a (family.force ε) = ENNReal.ofReal family.T` | `T^ν_{max,R}(a,g_ε)=T` | 04:34 first display; STATEMENTS.md:**347** | **byte-identical** | OK |

The accessors resolve as the paper intends: `family.T = scaling.correction.T` (the singular time
`T`), `family.margin = scaling.correction.δ` (the regularity margin `δ`), `family.g =
scaling.correction.g` (the reference force), all `InsertionFamily.lean:335-347`.

### 1.2 Token identity, checked mechanically

Normalising whitespace and comparing the raw slices of the two files, both clause fields are
identical **byte for byte**, not merely token for token. Stronger, a semantic probe compiled
clean (`lake env lean /tmp/096rev/fidelity.lean`, exit 0, no output): the new record's
`referenceLifespan` and `lifespan` fields are fed *directly* into the frozen 3-field structure's
slots and back again, which typechecks only if the two clause types are the same proposition for
the same family, and the round trip is `rfl`. Drift between the frozen and the registered clause
is therefore impossible, not just unlikely.

### 1.3 `memForce` is exactly `g ∈ F_R`

`Data.MemForceR` (`Data.lean:544`) is `F_R` of `02-preliminaries.tex:17` eq:Rclasses, the class
04:32 names. The justification for carrying it rather than deriving it is correct and checkable:
`Data.ClassicalSolutionR` has no force-class field, and `g_ε − g ∈ C_c^∞` runs the *other*
direction (`memForceR_of_compact_difference` gives `g_ε ∈ F_R` **from** `g ∈ F_R`), so `g ∈ F_R`
cannot be recovered from the family record. Carried as a field rather than only as a statement
hypothesis so R47 can reuse it — the shape `research/R42/REVIEW_BINDING.md:242-276` proposed,
followed exactly.

### 1.4 `regular` is the closed-interval notion, not the half-open `reference`

Confirmed, and this is the load-bearing point of the whole contract.
`Data.RegularThrough ν a f T = ∃ δ' > 0, Nonempty (ClassicalSolutionR ν a f (T + δ'))`
(`Data.lean:664`), i.e. a solution on `[0, T+δ')`, which covers the closed `[0,T]` —
02-preliminaries:34-36's "extends smoothly to `[0,T+\delta]` for some `\delta>0`". Applied at
`T + margin` it gives a solution strictly past `T+δ`, hence the **strict** `<` in
`referenceLifespan`. The family's own `reference` field is only a `ClassicalSolutionR ... (T +
margin)`, i.e. on the half-open `[0,T+δ)`, which yields `≤` and not `<` — exactly what the frozen
file's docstring says is missing and why A02 was needed. The probe above also confirms the
unfolding mechanically. So `regular` is not a restatement of `reference`; it is strictly stronger,
and it is the manuscript's hypothesis.

One inherited identification worth recording (not a defect of this lane): the paper's `δ` is
existentially quantified ("regular through `T+\delta` for some `\delta>0`"), while the contract
pins it to `family.margin = scaling.correction.δ`. That pinning is already baked into the frozen
`InsertionFamilyAPI.reference` and the frozen `referenceLifespan` clause, so this lane inherits it
rather than introducing it, and the correction record's `δ` is itself produced existentially
upstream. No action.

### 1.5 `insertionLifespanStatement` — can a wrong implementation satisfy it?

No. It mirrors `insertionFamilyStatement` (`InsertionFamily.lean:381`) precisely:

```lean
∀ (ν : ℝ) (P : PacketAPI ν) (F : InsertionFamilyAPI ν P),
  Data.MemForceR F.g → Data.RegularThrough ν F.a F.g (F.T + F.margin) →
    ∃ A : InsertionLifespanAPI ν P, A.family = F
```

Three escape routes, all closed. *Substituting a different family*: `A.family = F` is an
equation, and every clause field is dependent on `family`, so rewriting along it turns
`A.referenceLifespan`/`A.lifespan` into the clauses **for `F`**; the `rfl` in the test pins it at
the term level as well. *Vacuity of the hypotheses*: `RegularThrough` is a genuine existence
statement over `ClassicalSolutionR`, not `True` or `∃ x, True` — were it vacuous, the strict
inequality in `referenceLifespan` could not be derived from it, and the binding does derive it via
`regularThrough_iff`. *A placeholder clause*: neither clause is `Prop`-shaped over an unspecified
proposition; both are equations/inequalities in `Data.maximalLifespanR`, the canonical
`ℝ≥0∞`-valued lifespan, so they cannot be met vacuously.

The one honest caveat is **conditionality**, shared with every contract in the tree and with
`R42.insertion_family` itself: the statement says nothing until an `InsertionFamilyAPI ν P` is
produced, which `insertionFamilyStatement` supplies only given a `PacketAPI`, a `ScalingAPI` and a
reference `ClassicalSolutionR`. Not this lane's burden; recorded in §5.

### 1.6 Tests

All four required checks are present and are the right ones.

* `checkedInsertionLifespan` closes the statement through
  `Bindings.InsertionLifespan.insertionLifespanAPI F hg hreg` with a final `rfl` — the
  anti-substitution guard of lane-092 finding 5, additionally guarded in the binding by
  `insertionLifespanAPI_family`.
* `run_cmd TestSupport.checkAxioms` reports `checked; standard logical axioms only`.
* The two hand-written displays **do** re-state the manuscript rather than re-project the fields:
  each `example` writes its conclusion out in full in `Data` vocabulary against a bare record `A`
  and only then discharges it with `A.referenceLifespan` / `A.lifespan ε hε`. Because the type is
  spelled, not inferred (no `_`), any later weakening of the structure field breaks the example.
  This is strictly stronger than the precedent `Tests/InsertionFamily.lean`, which has no such
  displays. What they cannot catch — inherent, and the same for every contract here — is an error
  in the shared `Data` vocabulary itself; that is `D01`'s two-agent transcription, already done.
* The two derived-hypothesis examples are present and are the ones lane 092 asked for:
  `0 < ν := P.viscosity_pos` and `A.family.a ∈ Data.initialClassR :=
  Bindings.InsertionLifespan.initialClassR_a A.family`. They pin that neither was quietly promoted
  to a field.

## 2. Findings

**Finding 1 — MINOR (fix before merge). Wrong and mutually inconsistent `STATEMENTS.md` line
citations, in three places that disagree with each other.**
Location: `verification/Contracts/V1/InsertionLifespan.lean:19` and `:23` (header), `:110`
(structure docstring); `verification/contracts.json`, the `R42.insertion_lifespan` `scope`.
The three places assign the two line numbers three different ways — header says
`lifespan→:245, referenceLifespan→:332`; the structure docstring says `referenceLifespan→:245`;
`contracts.json` says `referenceLifespan→:245, lifespan→:332`. All six assignments are wrong.
Ground truth: `referenceLifespan` is `research/section4/STATEMENTS.md:`**333**, `lifespan` is
`:`**347**. Line 245 is prose about `u_ε = v + w_ε + U_ε`; line 332 is the *`reference`* field,
i.e. precisely the half-open notion §1.4 distinguishes `regular` from — the most misleading of the
three for a reader chasing the provenance of `referenceLifespan`.
Provenance: `:245` is inherited verbatim from the frozen `InsertionFamily.lean:431`, and it was
already wrong there — `STATEMENTS.md` has not changed since before `InsertionFamily.lean` was
created (`git log baa6236..HEAD -- research/section4/STATEMENTS.md` is empty and `baa6236` is an
ancestor of `34f5715`), so the number never pointed at `referenceLifespan`. The `:332`/`:245`
swap in the new header, and the self-contradiction with the file's own structure docstring, are
new to this lane.
Fix: cite `:333` and `:347` in the header and in the `contracts.json` scope. Correct `:245` to
`:333` in the structure docstring too — only the two clause *field types* must stay token-identical
to the frozen ones, not the docstrings, so this costs nothing. (`check_contracts.py` compares only
`version/specification/test_module/declaration/enabled`, so editing `scope` before merge is free.)
The frozen file's own `:245` cannot be corrected and stays as a known wart.

**Finding 2 — MINOR (fix before merge). The Bindings module docstring is now stale: it still says
the contract is unregistered and calls this lane "a later lane".**
Location: `verification/Bindings/InsertionLifespan.lean:12-16`. It reads "This is the still-
unregistered target `Contracts.V1.InsertionFamily.InsertionLifespanAPI` …; contract registration
is a later lane, so this file only inhabits the structure and records the exact extra hypothesis
list the V2 contract must carry." That later lane is this one: the file now also inhabits the
registered `Contracts.V1.InsertionLifespan.InsertionLifespanAPI` in its new §8, and the decision
was a new contract id at version 1, not "the V2 contract" (the same stale "V2" wording recurs at
`:59`). This is the first thing a consumer opening the binding reads, and it points them away from
the registered record.
Fix: two sentences — name `R42.insertion_lifespan` as registered, say §8's `insertionLifespanAPI`
is the registered inhabitant and §7's `insertionLifespan` the legacy one, and drop "V2".

**Finding 3 — NOTE (judgement call; a docstring sentence suffices, do not delete code). Two
structures now share the name `InsertionLifespanAPI`, and the bare name resolves to the wrong
one.**
`BlowupDensity.Contracts.V1.InsertionLifespanAPI` (frozen, 3 fields, unregistered) and
`BlowupDensity.Contracts.V1.InsertionLifespan.InsertionLifespanAPI` (registered, 5 fields). Under
the customary `open BlowupDensity.Contracts.V1` — which both the binding (`:100`) and any future
consumer will write — a bare `InsertionLifespanAPI` silently resolves to the **frozen,
unregistered** one. The sub-namespace choice itself is right and follows `MaximalPartial` and
`EnergyAbsorptionPartial`; the hazard is the collision, not the namespace.
Worse, the frozen file's docstring (`InsertionFamily.lean:406-420`) still asserts "This structure
is deliberately not registered …, because it is not proved. Both fields need task `A02` …, which
has no contract yet". All three clauses are now false: `A02.maximal_partial` and
`A02.maximal_partial_v2` are registered, and both fields are proved by
`Bindings.InsertionLifespan.{referenceLifespan, lifespan_eq}`. Being frozen V1, that file cannot
be corrected, so the correction has to live where a consumer will see it.
Judgement on the dead-weight question the brief asks: **keep** §7's `insertionLifespan` and
`insertionLifespan_family`. They are the only inhabitant of the frozen structure, they are lane
092's merged record, the new §8 reuses their two proofs verbatim (so there is no duplicated proof
burden), and deleting them would churn a reviewed module for no gain. They are not dead weight —
but they are unlabelled, which is the actual risk.
Fix: one sentence in `Contracts/V1/InsertionLifespan.lean`'s header and one clause in the
`contracts.json` scope saying the frozen `Contracts.V1.InsertionLifespanAPI` is superseded by this
record and new consumers must not use it; plus the §7/§8 labelling already folded into Finding 2.

**Finding 4 — OBSERVATION (no action). The contract is conditional, as intended.**
`insertionLifespanStatement` is quantified over a given `InsertionFamilyAPI`, whose existence is
itself conditional in `R42.insertion_family`. Nothing absolute about Theorem 4.2 follows from this
contract alone. Correctly reflected in the scope; recorded here only so the §5 gap paragraph is
not read as narrower than it is.

## 3. Scope honesty

Cross-checked clause by clause against the files; the `scope` string is accurate and unusually
complete. Spot checks that mattered:

* "*Derived, not assumed*: `ν > 0` (`P.viscosity_pos`), `a ∈ X_R` … `0 < T`, `0 < δ`, and the
  essential-supremum form of the blow-up" — all four confirmed; the first two are additionally
  pinned by Tests examples, and `referenceLifespan`'s positivity side condition really is
  `add_pos time_pos margin_pos` in the binding.
* "the blow-up is consumed in the registered **pointwise** `SpeedUnboundedAt` form and re-expressed
  in `speedENorm` inside the proof" — confirmed: `InsertionFamilyAPI.blowup` is
  `SpeedUnboundedAt scaling.correction.T (velocity ε)`, and `lifespan_upper` transfers it through
  `limsupLeft_speedENorm_eq_top`.
* "*Carried*: `R42.insertion_family` through the field `family` (no new copy of anything), hence
  transitively `I01.packet`, `I02.correction`, `I03.scaling`" — confirmed via
  `InsertionFamilyAPI.scaling : ScalingAPI ν P`. The file restates nothing: its only import is
  `Contracts.V1.InsertionFamily`, and every notion it uses (`Data.MemForceR`,
  `Data.RegularThrough`, `Data.maximalLifespanR`, `InsertionFamilyAPI`, `PacketAPI`) comes from
  that closure, so no `rfl` bridge is owed.
* "*the binding consumes* `A02.maximal_partial` (`lifespan_ge_of_forall_shorter`,
  `lifespan_le_of_unbounded`, `regularThrough_iff`, `uniqueness_toA02`, `maximalPartial_ofA02`),
  `D01.datum_lemmas` (`memForceR_of_compact_difference`, `contDiff_slice`), and the merged
  Section4/R42 modules" — every one of the nine named symbols occurs in
  `Bindings/InsertionLifespan.lean`. No over-claim.
* "*NOT asserted*: `sobolev` and `pressure_gradient` for `u_ε` (built inside `sol_on_shorter`, not
  exported)" — confirmed, they are discharged at `SolutionOnShorter.lean:139-159` and no contract
  field exposes them. "the displayed limsup of the spatial sup norm", "A02's continuation
  criterion eq:criterion (A04)", "any Theorem 4.1 or 4.3-4.7 statement" — all absent from the
  file, correctly disclaimed.

The only scope defect is the citation error of Finding 1.

**`work_items.json` and the registry diff.** `work_items.json` adds `"R42.insertion_lifespan"` to
R42's `contracts` list and `tasks.py render` regenerated `TASKS.md` and `tasks/R42.md` — the same
two-line-plus-render shape lane 091 used for `C01.energy_absorption_partial` (`13748a3`). The
`contracts.json` diff is **exactly** the new 11-line entry: the whole diff contains a single `-`
line and it is the `--- a/verification/contracts.json` header, so the `ensure_ascii` misstep the
worker records in `ATTEMPTS_CONTRACT.md` was indeed fully reverted and no pre-existing `scope`
string was churned. `ATTEMPTS_CONTRACT.md` is candid about that misstep and about what was not
exported; it is a good negative-example record.

## 4. Consistency

* No duplicate restatement: single import, `Data.*` and `InsertionFamilyAPI` reused, no local copy,
  no bridge owed. Contract import policy satisfied (`Contracts.V1.InsertionFamily` only).
* Frozen files untouched: `git diff origin/erenup/integration -- verification/Contracts/V1/
  InsertionFamily.lean` is empty, and the only files added under `Contracts/V1/` and `Tests/` are
  the two new `InsertionLifespan.lean`. No existing contract or test was modified.
* `warningAsError = true` respected: `Tests` carries it (`verification/lakefile.toml:25`) and
  `Tests.InsertionLifespan` compiles with no diagnostic of its own beyond the contract `info:`
  line. The worker's precaution of explicit binders in the `example`s (rather than a `variable`
  block) and the `_ε` underscore in the `lifespan` field is what keeps the unused-binder linter
  quiet; worth remembering.
* No `Formal.*` anywhere in the Tests closure; no `sorry`/`admit`/`axiom`/`native_decide` in any
  of the three files.
* Naming collision: Finding 3.

## 5. Commands and results

Worktree `.claude/worktrees/096-R42-lifespan-contract`; `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`; one `lake` at a time, always from `verification/`.

| command | result |
|---|---|
| `bash scripts/lean-install.sh` | exit 0 (idempotent, no reinstall) |
| `lake build Tests.InsertionLifespan` | `Build completed successfully (9971 jobs).`; `Tests/InsertionLifespan.lean:24:0: Contract BlowupDensity.Tests.checkedInsertionLifespan: checked; standard logical axioms only` |
| `make check` | exit 0; `test_contract_policy.py` 13/13 OK; `check_work_queue.py` "30 work items: ownership, contract registration and task cards consistent" |
| `make test` | exit 0; all 17 registered contracts "checked; standard logical axioms only", `Tests.InsertionLifespan` among them; no `error:` |
| `make test-mutations` | `implementation_refactor: accepted`; `admitted_proof`, `extra_axiom`, `weakened_hypothesis` each "rejected as required"; "Mutation suite passed." |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | exit 0; **17 contracts, all enabled**; `base_compatibility_checked: true`; `Tests.InsertionLifespan` present in the closure |
| `bash scripts/gates.sh Tests.InsertionLifespan` | ends `== gates OK` (exit 0) |
| `git diff origin/erenup/integration -- verification/Contracts/V1/InsertionFamily.lean` | empty (0 lines) — frozen file untouched |
| `git diff cc0c06b HEAD -- verification/contracts.json \| grep -c '^-'` | `1` (the diff header only) — purely additive, no scope churn |
| clause-field byte comparison (python, raw slices) | `referenceLifespan` and `lifespan` **byte-identical** to `InsertionFamily.lean:421-436` |
| `lake env lean /tmp/096rev/fidelity.lean` | exit 0, no output — new→frozen and frozen+2hyps→new both typecheck, round trip `rfl`, `RegularThrough` unfolds to the closed-interval notion |

## 6. What R42 still lacks after this contract

Theorem 4.2 is now registered in two records that between them cover every display of
`04-whole-space.tex:31-43` except one: `R42.insertion_family` has the construction, the support and
history clauses, `eq:REclose` and the force convergences, and `R42.insertion_lifespan` adds the two
lifespan clauses. The remaining gap for `R41D`/`R46`/`R47` is threefold. First, the **displayed
blow-up** `limsup_{t↑T}‖u_ε(t)‖_∞ = ∞` is still registered only in the pointwise `SpeedUnboundedAt`
form; the `essSup`/`limsup` display of 04:34 exists in the tree (`limsupLeft_speedENorm_eq_top`) but
no contract field exports it, so a consumer that wants the manuscript's second display must still
reach into the binding. Second, the inserted pair's **identification as *the* maximal solution** —
`IsMaximalSolution ν a g_ε u_ε p_ε`, the "Proposition~\ref{prop:local} identifies the solution with
the unique maximal solution" step of 04:53 — is not asserted anywhere; this contract gives only the
lifespan *number*, and R47 in particular will want the solution named. Third, `sobolev` and
`pressure_gradient` for `u_ε` are proved inside `sol_on_shorter` but not exported, so a consumer
cannot rebuild a `ClassicalSolutionR` for the inserted pair from contracts alone. Finally, and
underlying all of it, both R42 records are conditional on an `InsertionFamilyAPI` existing, which
needs `I01.packet`'s record to be inhabited — still the open end of the chain.

**What A02's remaining fields now need.** `A02.maximal_partial`'s out-of-scope list
(`MaximalPartial.lean:50-62`) names `insertion_lifespan_eq` and the restart triple. This lane
changes the picture for the first: `insertion_lifespan_eq` (`research/A02/Spec.lean:609-626`)
packages *two* conclusions, `maximalLifespanR ν a gPert = ofReal T` **and** `IsMaximalSolution ν a
gPert u p`. The equality half is now delivered for R42's actual configuration by this contract,
assembled from the already-registered `lifespan_ge_of_forall_shorter` / `lifespan_le_of_unbounded`
— so A02 no longer needs to register `insertion_lifespan_eq` as a packaged field on R42's account,
and what is genuinely still owed from it is only the `IsMaximalSolution` half (which in turn needs
`exists_maximal`, `maximal_unique` and the `IsMaximalSolution` predicate, all still unregistered).
The restart triple `restart`, `restart_datum`, `restart_force` is untouched by this lane: nothing
here consumes it, and it remains what **A04**'s continuation criterion `eq:criterion` will consume,
on the A02 → A04 edge. Registering them stays A02's job, now with a narrower R42-facing target.

