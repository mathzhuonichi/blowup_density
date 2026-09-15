# Review — lane 050, C01 units U1 (`velocityJets`) and U3 (velocity half of evolution packaging)

Reviewed: `formalization/NSFormalization/Section4/C01/VelocityJets.lean`,
`formalization/NSFormalization/Section4/C01/Evolution.lean`,
`research/C01/axioms_u1u3.lean`, `research/C01/ATTEMPTS_U1U3.md`.
Worktree `.claude/worktrees/050-C01-units-u1-u3`, commit `eb6b99a`.
Diff vs `erenup/integration`: 4 files, 457 insertions, 0 deletions.

## Verdict: **ACCEPT-WITH-NOTES**

Every mechanical check passes. The Lean is correct, minimal and axiom-clean; the U1
conformance is the spec field verbatim; the U3 clauses that are proved are exactly the
consumer's hypotheses and are proved from the stated data only. **No code change is
required.** All seven findings are in the prose gap analysis (module header + ATTEMPTS),
and three of them (1, 2, 3) matter, because they misdescribe *what is left to do* and
one of the two proposed fixes points the wrong way.

---

## 1. Commands and results

All from `WT/verification` unless noted, `LEAN_NUM_THREADS=6`, no `-j`, one lake at a time.

| # | command | result |
|---|---|---|
| 1 | `cd WT && bash scripts/lean-install.sh` | `== OK` |
| 2 | `lake build NSFormalization.Section4.C01.VelocityJets NSFormalization.Section4.C01.Evolution` | `Build completed successfully (9882 jobs).` **EXIT=0** |
| 3 | `grep -n "Section4/C01\|Section4.C01" <full build log>` | **no output** — zero warnings, hints or info from either lane file. (The build log's warnings are all pre-existing: `Paper3/RealPositiveDensity.lean`, `Paper3/RealVectorPositiveDensity.lean`, `Source/PhysicalBesselSobolev.lean`, `Source/PacketForceExtension.lean`, `Source/ViscosityPacket.lean`, `Paper3/SobolevDirectionalDerivative.lean`.) |
| 4 | `lake env lean ../research/C01/axioms_u1u3.lean` | **EXIT=0**, no errors → the conformance `example` typechecks. All **8** `#print axioms` print exactly `[propext, Classical.choice, Quot.sound]`: `velocity_slice_memHInfty_and_smoothL2`, `velocity_slice_memHInfty`, `velocity_slice_smoothL2`, `velocityField`, `velocityField_field`, `velocityField_solenoidal`, `jetOfDatum_continuous`, `velocityField_jetLp_continuous`. |
| 5 | `grep -n "sorry\|admit\|native_decide\|axiom\|maxHeartbeats"` over the three lane files | only the eight `#print axioms` lines and three docstring/comment occurrences of the word "axiom" in `axioms_u1u3.lean`. **Nothing in code.** No `set_option` anywhere. |
| 6 | `cd WT && make check` | **EXIT=0**; `check_formalization_plan --check`, `check_contracts`, `test_contract_policy` (`Ran 13 tests … OK`), `check_work_queue` (`30 work items: ownership, contract registration and task cards consistent.`) |
| 7 | snag reproduction: copy of `VelocityJets.lean` with `open NavierStokes.ProblemStatement` deleted, run through `lake env lean` | reproduces: `error: Application type mismatch: The argument x has type Space but is expected to have type NavierStokes.ProblemStatement.Space` at three sites (lines 67, 68, 69). |

## 2. Conformance (U1) — confirmed

* `research/C01/Spec.lean:295-300` (`EnergyAbsorptionAPI.velocityJets`) and the `example` in
  `axioms_u1u3.lean:63-71` agree **token for token**, including the `slice` of
  `Spec.lean:167`, restated verbatim in `axioms_u1u3.lean:37`.
* Discharged in term mode by `velocity_slice_memHInfty_and_smoothL2 (toA02 w) ht`.
  **No extra hypotheses**: the binders `0 < ν`, `a ∈ initialClassR`, `MemForceR f` are all
  ignored (`fun _ _ _ _ _ _ _ w _ ht => …`), so the theorem is strictly stronger than the field.
* `toA02` (`axioms_u1u3.lean:46-60`) is **bare projections**: ten fields, each assigned
  `w.<same field>`, no tactic block, no proof content. Verified against the two structure
  declarations: `Contracts/V1/Data.lean:624-648` and `Section4/A02/SolutionClass.lean:100-123`
  are identical in field names, order and types.
* Vocabulary bridges are definitional, as claimed: `A02.MemHInfty` (`SolutionClass.lean:74`)
  = `Data.MemHInfty` (`Data.lean:495`); `A05.SmoothL2` (`A05/SmoothJets.lean:44`)
  = `Contracts.V1.SmoothSquareIntegrableJets` (`GradientL6.lean:106-107`), both
  `ContDiff ℝ ∞ ∧ ∀ n, MemLp (iteratedFDeriv ℝ n ·) 2 volume`; `Bindings/DatumLemmas.lean:59-62`
  carries the `rfl` for the D01 spelling.
* **Route is the registered contract's lemmas.** The proof term in
  `VelocityJets.lean:68-70` is byte-identical to the registered binding
  `Bindings/DatumLemmas.lean:199-201` (`solution_slice_smoothJets`):
  `D01.smoothSquareIntegrableJets_slice u.velocity_smooth (fun m => (u.sobolev m).imp fun _ h => h.2) ht`,
  and the datum direction is `D01.memHInfty_iff_smoothSquareIntegrableJets`, bound at
  `DatumLemmas.lean:189` as `memHInfty_iff_smoothJets`. The `.imp` discards the `ContinuousOn`
  conjunct exactly as the contract's docstring (`Contracts/V1/DatumLemmas.lean:255-259`) says
  it must.

## 3. Math (U3 velocity clauses) — confirmed

`velocityField_jetLp_continuous` (`Evolution.lean:139-155`) uses **only** the `ContinuousOn G (Ico 0 T)`
conjunct of `sobolev` at order `n`, plus the datum conjunct to identify the `Lp` element.
The continuity is a pure composition of continuous maps, each checked:

| stage | declaration | kind |
|---|---|---|
| datum component | `PiLp.continuous_apply 2 _ i` on `RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)` | continuous |
| subspace coercion | `continuous_subtype_val` | continuous |
| `cyclesComponentOfAngular` | `Paper3.cyclesToAngular` (`AngularTameProduct.lean:11`) `≃L[ℂ]`, `.symm.continuous` | CLE |
| `loweredComponent` | `Paper3.sobolevOrderLowering` (`SobolevOrderLowering.lean:26`) `→L[ℂ]` | CLM |
| reassembly | `Source.FourierPhysicalJets.physicalJetLp j` (`FourierPhysicalJets.lean:154`) `→L[ℝ]` | CLM |

The `Lp` identification is `((velocityField t).integrable n).coeFn_toLp` against
`D01.jetOfDatum_ae` (`DatumToJets.lean:202`), closed with `Lp.ext`; `jetLp` is literally
`(A.integrable n).toLp (iteratedFDeriv ℝ n A.field)` (`Euler/LpSmoothField.lean:46`), so the
bridge is the right one. **No smoothness-in-time and no differentiability in time is used
anywhere** — only `ContinuousOn`, and `mem_Ico_of_mem_Icc` for the domain transport.

This is worth flagging as genuine new content: `Contracts/V1/DatumLemmas.lean:61-65` states
"**No time regularity of a datum path** … the `ContinuousOn G (Ico 0 T)` conjunct of `sobolev`
is discarded by every slice clause below, and no clause produces a continuous or smooth datum
path for a velocity." This lane is the first place in tree that uses it, and it does so soundly.

`velocityField_solenoidal` is likewise clean: `ClassicalSolutionR.divergence` →
`EulerSmoothLimit.divergence_eq_coordinate_sum` → `smooth_mem_solenoidal`
(`Euler/MeanSolenoidalSpace.lean:187`), with the two divergences being the same coordinate sum.

## 4. Snags spot-checked (2 of 4)

* **`Space` namespace collision** (ATTEMPTS §U1, "First build failed with `Space` resolving to
  the wrong namespace"): **reproduced** (command 7 above). Without `open NavierStokes.ProblemStatement`
  the `Space` that D01's import chain brings into scope is a different `abbrev Space` and the
  `(t, x)` applications fail with an application type mismatch. Accurate.
* **`jetOfDatum` is not bundled as a CLM** (ATTEMPTS §U3, rejected approach): confirmed.
  `D01.norm_jetOfDatum_le` exists at `DatumToJets.lean:224` (an inequality on the unbundled
  function), and `grep` over `formalization/` finds no `→L[…]`-bundled `jetOfDatum` anywhere.
  Choosing the direct composition-of-continuous-maps proof over a Lipschitz-from-the-norm-bound
  route was correct, and it also avoids the ℝ-vs-ℂ realification the note mentions.
* Also confirmed (from the Data.lean reading below): `ClassicalSolutionR.pressure_gradient`
  (`Data.lean:646-648`) is order-zero `MemLp` only, so the rejected "build the `∇p` `SmoothL2Field`
  from `pressure_gradient` alone" really is blocked.

## 5. `difference_energy_bound` — hypotheses as they actually are

`Source/OrdinaryViscousStability.lean:71-82`, full package:
`hT : 0 ≤ T`, `hν : 0 ≤ ν`, paths `U W P D : Icc 0 T → SmoothL2Field Space`,
`hWc : ∀ n, Continuous (t ↦ (W t).jetLp n)`, `hDc` (same for `D`),
`hTime : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (r ↦ (W (projIcc 0 T hT r)).field x) ((D ⟨t,…⟩).field x) t`,
`K` with `hK : ∀ t x, ‖fderiv ℝ (U t).field x‖ ≤ K`,
`hdiv : ∀ t x, divergence (addField (U t) (W t)).field x = 0`,
`hW : ∀ t, (W t).toLp ∈ solenoidalSpace`, `hP : ∀ t, (P t).toLp ∈ gradientSpace`,
`hD : ∀ t x, (D t).field x = (differenceRhs (U t) (W t) (P t)).field x + ν • (laplacianField (W t)).field x`.

The lane's reading of this list (ATTEMPTS §U3 "Read of `difference_energy_bound`") is **accurate**.
Of it, the lane closes `hWc` and `hW` for the velocity, and `hdiv` is immediate from
`velocityField_solenoidal`'s ingredient with `U := 0` (`hK` then holds with `K = 0`).

## 6. The U3 gap — assessment

**The pressure gap is real and load-bearing.** Confirmed against `Contracts/V1/Data.lean:624-648`:
the class carries `velocity`, `pressure`, `horizon_pos`, `velocity_smooth`, `pressure_smooth`,
`initial`, `divergence`, `momentum`, `sobolev`, `pressure_gradient` — and `pressure_gradient`
(`:646-648`) is `∀ t ∈ Ico 0 T, MemLp (fun x => pressureGradient pressure t x) 2 volume`, i.e.
**order zero only**; there is no Sobolev datum for `p` or `∇p` at any positive order, and no
time-derivative datum of any kind. `EulerOrdinarySobolev.gradient_mem`
(`Euler/OrdinaryPressureCancellation.lean:84`) does need `A : SmoothL2Field Space` with
`A.field = gradient p`, i.e. **all** Fréchet jets of `∇p(t,·)` in `L²`. So `hP` genuinely does not
follow from the class as it stands today, and D01's own contract says so in as many words
(`Contracts/V1/DatumLemmas.lean:66-72`, "No pressure datum … neither `SmoothSquareIntegrableJets (∇p(t,·))`
nor `BoundedRep.SmoothJetsUpTo 1` of it follows from the class as specified, and neither is claimed").
`Evolution.lean`'s wording — "**not known** to be an `SmoothL2Field`" — is the right hedge.

**But the gap is a missing *lemma*, not a missing *hypothesis*, and the lane's second proposed
fix points the wrong way.** See findings 1–3.

---

## 7. Findings

### Finding 1 — the time-derivative clause is not an independent gap; `momentum` supplies ∂ₜu
**Severity: medium (gap analysis is wrong in substance).**
**Where:** `Evolution.lean:60-64` (header, open clause 2) and `ATTEMPTS_U1U3.md`, U3 open
clause "Pointwise time-derivative (clause `hTime`) and the derivative path `D`".

**What is wrong.** Both say: "The solution class carries only *spatial* data (`velocity_smooth`,
`sobolev`); there is no time-derivative datum, so the derivative field is not available as an
`SmoothL2Field`." That overlooks `ClassicalSolutionR.momentum` (`Data.lean:640-642`).
`navierStokesResidual ν u p t x = temporalDerivative u t x + advection u t x − ν • spatialLaplacian u t x + pressureGradient p t x`
(`vendor/.../NavierStokes/R3/ProblemStatement.lean:57-62`), and `temporalDerivative u t x =
fderiv ℝ (fun s => u (s, x)) t 1` (`NavierStokes/ProblemStatement.lean:55`). So `momentum`
pins ∂ₜu **algebraically** on `Ioo 0 T`:
`∂ₜu = f − (u·∇)u + νΔu − ∇p`, which is exactly the interval on which `hTime` is demanded.
Every summand but `∇p` is already known to have all jets in `L²` for this class
(`u` by U1 + the tame-product machinery, `f` by `MemForceR`, `Data.lean:544-550`, which gives
`f(t,·) ∈ H^m` for every `m` and every `t ≥ 0`). Moreover `hD` *forces* `D` to be
`differenceRhs (U t) (W t) (P t) + ν • laplacianField (W t)`, so `D` is not free data at all:
with `U := 0` and `P := ∇p`, `differenceRhs U W P = −((∇W)W + ∇p)` (`Euler/OrdinaryH3Energy.lean:25-30`),
i.e. `D` is an algebraic expression in `W` and `P` whose `SmoothL2Field`-hood and jet continuity
reduce to those of `W` and `P`.

**Consequence.** There is **one** root gap (the pressure jets), not two independent ones.
Clause 2 = clause 3 + routine work: (a) extracting `HasDerivAt` in time at interior points from
`velocity_smooth`'s `ContDiffOn ℝ ∞ u (Ico 0 T ×ˢ univ)` together with the `projIcc` bookkeeping;
(b) jet-continuity in `t` of `f`, `(u·∇)u`, `Δu`, `∇p`, of which the first three are within
reach of `sobolev`'s `ContinuousOn` conjunct (now usable, thanks to this lane's
`velocityField_jetLp_continuous`) plus tame products.

**A second, smaller point in the same place.** With `U := 0`, `P := ∇p`, `hD` forces
`D = −(u·∇)u − ∇p + νΔu`, which by `momentum` equals `∂ₜu − f`, **not** `∂ₜu`. So
`difference_energy_bound` as stated is the *unforced* estimate; a forced solution does not
satisfy its `hD`/`hTime` package with `P := ∇p` unless `f = 0`. This should be recorded so that
U4 does not inherit a `D` that is off by the force.

**Fix.** Rewrite open clause 2 in both places: say that `momentum` determines ∂ₜu on `Ioo 0 T`,
that clause 2 therefore reduces to clause 3 plus (a) and (b) above, and note the force
discrepancy in `hD`.

### Finding 2 — the "D01 V2 pressure-datum clause" alternative is the dishonest branch; the paper's class *does* imply ∇p ∈ H^∞
**Severity: medium (direction of the proposed fix).**
**Where:** `ATTEMPTS_U1U3.md`, U3 open clause `hP`: "*Missing clause:* `∀ t, SmoothSquareIntegrableJets (∇p(t,·))`
(**or a Sobolev datum for `∇p` at every order**) … a new D01/pressure unit"; and the task's own
framing of "elliptic pressure regularity unit, **or** a D01 V2 pressure-datum clause".

**What is wrong.** Asked directly: **yes, the paper's class implies ∇p ∈ H^∞.**
`paper/sections/02-preliminaries.tex:30-31` says the whole-space pressure gradient "is specified
below", and `:89-91` specifies it: eq:Rpressure, `∇p = (I−P)(f − ∇·(u⊗u)) =: G`. At `:80-81` the
Leray projection is "bounded on every `H^s` and commutes with derivatives and the heat semigroup",
and at `:93` "For smooth `H^∞` data, `G` is smooth". Since `u(t) ∈ H^∞` (the class, `:29-30`) and
`f(t) ∈ H^∞` (`F_R`, eq:Rclasses), `u⊗u ∈ H^∞` by the `H^m` algebra, so `∇·(u⊗u) ∈ H^∞`, so
`G(t) ∈ H^∞`. Hence `∇p(t,·) ∈ H^∞`, which by `memHInfty_iff_smoothJets` is exactly
`SmoothSquareIntegrableJets (∇p(t,·))`, i.e. the `SmoothL2Field` `gradient_mem` wants.

So this is a **theorem of the class, not a hypothesis to be added**, and the project has already
ratified that reading: `Data.lean:621-623` — "eq:Rpressure in its `(I-P)` form is deliberately not
a field: for a smooth solenoidal solution it follows from `momentum` and `divergence` together with
`∇p ∈ L²`. Deriving it is a lemma (unit L9)"; and `research/D01/RECONCILIATION.md:81` — "both
reviews: correct to omit … **Omitted deliberately**; becomes unit L9."

Adding a pressure datum as a V2 class field would make the Lean `ClassicalSolutionR` **strictly
stronger than the paper's class**: downstream theorems would then apply to fewer solutions, and
the obligation would silently move onto whoever must *construct* a `ClassicalSolutionR` (the
local-existence side, prop:local), which is where it is hardest to discharge. That is exactly the
kind of hypothesis-strengthening this project's contract policy exists to prevent.

**Fix.** Drop the "or a Sobolev datum for `∇p` at every order" / "D01 V2 pressure-datum clause"
alternative from `ATTEMPTS_U1U3.md` and from the `Evolution.lean` header. The elliptic-regularity
route is the only honest one. (If a V2 datum clause is ever wanted as *temporary scaffolding*, it
must be recorded as a debt against prop:local, not as a specification choice.)

### Finding 3 — the gap already has a named owner in tree: unit **L9(c)**, blocked on **U05**
**Severity: medium (navigability / duplicated work).**
**Where:** `ATTEMPTS_U1U3.md` U3 open clause `hP`, "a new D01/pressure unit";
`Evolution.lean:64-70`.

**What is wrong.** The unit exists and is named:
* `research/D01/RECONCILIATION.md:160` — "**L9** … (c) eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))`
  ⟺ `momentum` given `divergence` and `∇p ∈ L²`. … (c) **gap**: needs the Leray complement on
  physical fields. Reusable at the distributional level as HeliCorgi
  `MNS2.r3HelmholtzPressure_gradient` (`vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean:259`)
  and `r3LerayComplementL2` (`:228`), **blocked on toolchain task U05** (HeliCorgi is Lean 4.32.1,
  this project 4.34.0-rc2)."
* `research/D01/COMPARISON_A.md:105` — same, "**Gap in-tree** … cannot be imported (blocked on U05)".
* `research/D01/REVIEW_DATUM_TO_JETS.md:148` — "pressure-gradient jets, blocked behind **L9(c)**".
* `research/D01/ATTEMPTS_DATUM_TO_JETS.md:280` — "needs either a stronger `ClassicalSolutionR` or
  unit **L9(c)**".

**Fix.** Name L9(c) and the U05 toolchain blocker in both places, and add the one thing L9(c)
does *not* give: L9(c) delivers eq:Rpressure at the `L²` (order-zero) level, so the all-order jet
statement additionally needs `(I−P)` bounded on every `H^m` and the `H^∞` algebra for `u⊗u`
(the tame-product machinery, `Contracts/V1/TameProduct.lean`). Stating that turns "a new
D01/pressure unit" into a scoped piece of work with a known blocker.

### Finding 4 — `Evolution.lean`'s header contradicts its own file (stale)
**Severity: minor (documentation, but it is the first thing a consumer reads).**
**Where:** `Evolution.lean:38-48` ("What is proved here") and `:50-58` ("The three clauses that
are *not* closed here").

**What is wrong.** The header lists `jetLp` continuity as open clause 1 and says "Closing it needs
`jetOfDatum` packaged as a `ContinuousLinearMap` … plus that `Lp`-equality — **neither exists in
tree today**". The same file then proves it: `jetOfDatum_continuous` (`:122-130`) and
`velocityField_jetLp_continuous` (`:139-155`), and the latter's own docstring says "the missing
clause flagged in this module's header is in fact closed for the *velocity*". The
"What is proved here" list also omits both theorems. `ATTEMPTS_U1U3.md` is correct and consistent;
only the module header is stale.

**Fix.** Rewrite the header: three bullets under "What is proved" become five (add
`jetOfDatum_continuous` and `velocityField_jetLp_continuous`), and "The three clauses that are not
closed" becomes two (pressure jets; the time-derivative package — as re-scoped by finding 1).

### Finding 5 — the elliptic relation is written without the force
**Severity: minor (mathematical typo in the gap statement).**
**Where:** `ATTEMPTS_U1U3.md`, U3 open clause `hP`: "which needs the elliptic pressure regularity
`-Δp = div((u·∇)u)`".

**What is wrong.** For a forced solution the relation is `Δp = div f − ∂ᵢ∂ⱼ(uᵢuⱼ)`, equivalently
the paper's eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` (`02-preliminaries.tex:90-91`; the torus form
at `:86` shows the `div f` term explicitly). The stated form is the unforced one. Since C01 is
precisely the *forced* whole-space theory, dropping `f` matters.

**Fix.** Write `Δp = div f − ∂ᵢ∂ⱼ(uᵢuⱼ)`, or just cite eq:Rpressure.

### Finding 6 — `difference_energy_bound` is a proxy, not C01's actual consumer
**Severity: minor (scoping; prevents the next lane over-collecting hypotheses).**
**Where:** `ATTEMPTS_U1U3.md` §U3 "Target (task)" and `Evolution.lean:20-24`.

**What is wrong.** `research/C01/COMPARISON.md:173` cites `difference_energy_bound:71` only as
evidence that "the shape is proven usable"; the consumers it actually names for U4 and U7 are
`wordEnergy_hasDerivWithinAt` (`Euler/OrdinaryWordTime.lean:86`) and `ordinaryWord_hasDerivWithinAt`
(`:78`). Their hypothesis package is **only** `hA` (jetLp continuity of the path),
`hB` (jetLp continuity of the derivative path) and `hd` (pointwise `HasDerivAt`) — no `hK`, no
`hdiv`, no `hW`, no `hP`. The pressure enters U4/U7 not as `hP` but through the pressure-cancellation
lemmas, where `gradient_mem` (`Euler/OrdinaryPressureCancellation.lean:84`) is the consumer of the
`SmoothL2Field` structure on `∇p`.

This does not weaken what the lane proved — `velocityField_jetLp_continuous` is exactly `hA` for the
velocity, which is the clause U4/U7 need — but the framing over-states which hypotheses U3 owes.

**Fix.** In `ATTEMPTS_U1U3.md` and the `Evolution.lean` header, name `wordEnergy_hasDerivWithinAt`
as the real consumer and `difference_energy_bound` as the shape witness.

### Finding 7 — `COMPARISON.md` still rates U1 `L`
**Severity: minor (bookkeeping at merge time).**
**Where:** `research/C01/COMPARISON.md:171` still reads `| U1 | … | **L** |`, while
`ATTEMPTS_U1U3.md` records "was rated L, now S" and the lane has in fact closed it in three lines.

**Fix.** Update the U1 row (and its "depends on" cell, which still says D01 unit L2's direction is
**open**) when this lane merges, or add a supersession note.

---

## 8. What I did not find

No `sorry`, `admit`, `native_decide`, `axiom`, `maxHeartbeats` or `set_option` in code; no
warnings from either lane file; no extra hypotheses in the conformance example; no unused or
disguised smoothness-in-time in `velocityField_jetLp_continuous`; no proof content smuggled into
`toA02`; no registry or contract-policy breakage (`make check` clean). Nothing in the lane
overclaims in Lean — every overclaim found is in prose, and findings 1–3 are the ones that should
be corrected before this becomes the reference description of what C01 still owes.
