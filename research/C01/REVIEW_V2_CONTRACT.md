# REVIEW — lane 152-C01-v2-contract (C01 V2: the ordinary energy identity)

Reviewer: opus, read-only, worktree `.claude/worktrees/152-C01-v2-contract`, HEAD `c3f7e70`.
Probes written: `research/C01/probes/rev152_{mutation,nonvacuity,defeq}.lean` (new files only;
no tracked file touched, no git state changed — `git status --short` shows exactly those three
`??` lines).

## Verdict: **ACCEPT-WITH-NOTES**

Both notes are cosmetic and non-blocking; they are listed only because `Contracts/V2/*` is
frozen by CI the moment it merges, so a one-line fix is cheaper now than never.

---

## 1. What the contract claims

`Contracts/V2/EnergyAbsorptionPartial.lean:109` registers
`EnergyAbsorptionPartialV2API extends Contracts.V1.EnergyAbsorptionPartial.EnergyAbsorptionPartialAPI`
with exactly **one** new field, `energyIdentity` (`:125-131`):

> for `0 < ν`, `a ∈ initialClassR`, `MemForceR f`, a classical whole-space solution
> `w : ClassicalSolutionR ν a f T` and **every interior** `t ∈ Ioo 0 T`,
> `HasDerivAt (fun s => l2Sq (slice w.velocity s))`
> `(-2 * ν * gradientSq (slice w.velocity t) + 2 * pairing (slice w.velocity t) (slice f t)) t`.

That is the manuscript's ordinary energy identity. `paper/sections/02-preliminaries.tex:137-140`
displays `½(‖U(t)‖₂²)' + ν‖∇U(t)‖₂² = ⟨F(t),U(t)⟩`; multiplying by 2 gives
`(‖u‖₂²)' = −2ν‖∇u‖₂² + 2⟨u,f⟩`, term for term the Lean value.  It is invoked at
`04-whole-space.tex:117` ("The separate ordinary energy identity, with regularized norm division,
supplies" eq:RL2, `:118-120`).  `⟨F,U⟩` vs `pairing u f` is the same real number (real inner
product is symmetric).

**Statement fidelity — mechanical checks, all PASS.**

| claim | check | result |
|---|---|---|
| field is token-for-token `Spec.lean:344-350` | `sed -n '344,350p' research/C01/Spec.lean` vs `sed -n '125,131p' Contracts/V2/EnergyAbsorptionPartial.lean`, `diff` | **byte-identical**, including indentation |
| `gradientSq` is token-for-token `Spec.lean:185` | `diff` of the two `def` lines | **byte-identical** |
| `pairing` is token-for-token `Spec.lean:196` | same `diff` | **byte-identical** |
| the `Tests` conformance `example` is the same statement | whitespace-normalised compare of `Tests/EnergyAbsorptionPartialV2.lean:37-42` with `Spec.lean:345-350` | **equal** (differs only by the `+2` structure-field indent and the trailing ` :=`) |
| `gradientSq` is the **Frobenius** squared gradient, not an operator norm | `probes/rev152_defeq.lean`: `‖gradientTensor z x‖² = ∑ᵢ ∑ⱼ \|fderiv ℝ z x (coordinateVector i) j\|²` proved | **holds**; `gradientTensor` (`Contracts/V1/GradientL6.lean:89`) is `Data.spatialGradient` on the lift (`Data.lean:453`, whose docstring says "deliberately *not* the operator norm"), so this is the second summand of `E_T` (`Data.energyGradient`) |
| `pairing` is the real `L²` inner product | `def pairing w z := ∫ x, (inner ℝ (w x) (z x) : ℝ)` on `Space = EuclideanSpace ℝ (Fin 3)` | **holds** |
| the derivative is a genuine two-sided `HasDerivAt` at **interior** times | `Ioo (0:ℝ) T` | **holds**; `Ioo` (not `Ico`) is the right choice — a two-sided derivative at `t = 0` is not available from a solution defined on `[0,T)`, and `Ioo` is what the blind-comparison `Spec.lean` fixed |
| hypothesis prefix matches the V1 house style | V1 `velocityJets` (`Contracts/V1/EnergyAbsorptionPartial.lean:167-172`) has the identical `∀ ν, 0 < ν → ∀ a, a ∈ initialClassR → ∀ f, MemForceR f → ∀ T w, ∀ t ∈ …` prefix | **matches** (only `Ico` → `Ioo`) |

**Slack hypotheses — declared, and in the acceptable direction.** `0 < ν` and
`a ∈ initialClassR` are *unused* by the binding (`Bindings/EnergyAbsorptionPartialV2.lean:96`,
`fun _ _ _ _ _ hf _ w _ ht => …`): the lane's theorem
`NSFormalization.Section4.C01.energyIdentity_l2Sq` needs neither.  Extra hypotheses make the
**contract weaker**, and a **stronger** theorem is binding it — the safe direction; the reverse
(a contract stronger than what is proved) does not occur here.  This is disclosed in three
places: the field docstring (`:124`), the module "Scope disclosures" §2 (`:56-58`), and the
`contracts.json` scope string ("DISCLOSURES: … (2) 0 < nu and a in initialClassR are SLACK").
Keeping them is also the right call for a contract: they make the field read as the manuscript's
and match every sibling V1 field, so a consumer (R43/R44, which always carry `ha`) is not
surprised.  **Accepted as stated.**

**No other slack, no vacuity.** The transport work `⟨(u·∇)u,u⟩` and the pressure work `⟨∇p,u⟩`
are *absent from the value* because they are proved to vanish, not because they were hypothesised
away — disclosure §1 says so and lane 143's `energyIdentity_of_carrierB` is where they die
(`ClassicalSolutionR.{divergence,pressure_gradient}`).  Non-vacuity checked in §5 below.

## 2. What is in Lean

* `formalization/NSFormalization/Section4/C01/EnergySpec.lean` (new, 74 lines).
  `def pairing (w z : A02.SpatialField)` (`:46`) and `theorem energyIdentity_l2Sq` (`:60-74`):
  the clamp-free `l2Sq`/`slice`/`pairing` restatement of lane 150's
  `energyIdentity_classical_unconditional` (`EnergyDerivative.lean:156-167`).  The proof is the
  8 lines `REVIEW_E4.md` §4 step 1 prescribed and `probes/rev150_gap.lean` pre-verified:
  `HasDerivAt.congr_of_eventuallyEq` on an `Ioo 0 ((t+T)/2)` neighbourhood, `projIcc_of_mem`,
  `Vocabulary.norm_toLp_sq_eq_l2Sq` (`Vocabulary.lean:107`, **not** `rfl`).  Because
  `congr_of_eventuallyEq` carries the derivative **value unchanged**, the fact that it elaborates
  at all *is* the proof of the docstring's defeq claims (`axis i ≡ coordinateVector i`,
  `⟪·,·⟫ ≡ inner ℝ`, `pairing` unfolds to the raw force integral); I re-confirmed
  `@EulerOrdinarySobolev.axis = @NavierStokes.ProblemStatement.coordinateVector := rfl`
  independently in `probes/rev152_defeq.lean`.
* `verification/Contracts/V2/EnergyAbsorptionPartial.lean`. **Import policy: PASS** — the only
  import is `Contracts.V1.EnergyAbsorptionPartial` (`:1`), inside
  `check_contracts.py`'s `CONTRACT_IMPORT_PREFIXES`.  The `open NavierStokes.ProblemStatement` at
  `:76` is a transitively-imported namespace, which the policy checker does not scan and which V1
  does verbatim (`Contracts/V1/EnergyAbsorptionPartial.lean:103`) — allowed (LESSONS 133).
* **V1 is frozen and untouched**: `git diff origin/erenup/integration -- verification/Contracts/V1
  verification/Tests/EnergyAbsorptionPartial.lean verification/Bindings/EnergyAbsorptionPartial.lean`
  is **empty**.  `extends` makes the inheritance structural, and
  `Bindings.energyAbsorptionPartial_of_v2 : energyAbsorptionPartialV2.toEnergyAbsorptionPartialAPI
  = energyAbsorptionPartial := rfl` (`Bindings/…V2.lean:102`) is the checked proof that V2 reuses
  the frozen V1 witness rather than re-proving (or quietly weakening) it.  `extends` is a
  deviation from `REVIEW_E4.md` §4 step 2 ("re-stating V1's six fields verbatim"), recorded and
  justified in `ATTEMPTS_V2_CONTRACT.md`; it is a **strict improvement** and matches all six
  sibling V2 contracts (`Correction`, `DatumLemmas`, `EnergyHighPartial`, `HomogeneousPartial`,
  `InsertionLifespan`, `MaximalPartial` all use `extends`).  Not a finding.
* `verification/Bindings/EnergyAbsorptionPartialV2.lean`.
  * **structure exception honoured**: `uniqueness_toA02` (`Bindings/Uniqueness.lean:63-76`, the
    field-by-field `Data.ClassicalSolutionR → A02.ClassicalSolutionR` conversion) is **reused**,
    not re-written; `(uniqueness_toA02 w).velocity = w.velocity` is `rfl`
    (`Bindings/Uniqueness.lean:79`) and `w.velocity` is the only projection the statement mentions.
  * **`pairing` bridge is `rfl`**: `energyAbsorptionPartialV2_pairing_eq :
    Contracts.V2.…pairing = NSFormalization.Section4.C01.pairing := rfl` (`:54-56`). Confirmed by
    `#check` in the probe.
  * **the single non-`rfl` bridge, `gradientSq`, is correct and points the right way**:
    `energyAbsorptionPartialV2_gradientSq_eq (z) : Contracts.V2.…gradientSq z = ∫ x, ∑ i,
    ‖fderiv ℝ z x (coordinateVector i)‖ ^ 2` (`:69-75`) — contract on the **left**, formalization
    integrand on the right, which is why the binding's `rw [energyAbsorptionPartialV2_gradientSq_eq]`
    turns the contract goal into the shape `energyIdentity_l2Sq` produces.  Its proof is
    `PiLp.norm_sq_eq_of_L2` (`‖x‖² = ∑ᵢ ‖x.ofLp i‖²` for `PiLp 2`) pointwise — `gradientTensor z x`
    is literally `WithLp.toLp 2 (fun i => fderiv ℝ z x (coordinateVector i))`, verified `rfl` in the
    probe — fed through `integral_congr_ae ∘ Eventually.of_forall`.  So "Frobenius = sum over the
    three columns", each column a `Space`-vector whose own squared norm is `∑ⱼ|∂ᵢzⱼ|²`; the probe
    proves the full `∑ᵢ∑ⱼ` expansion.  No a.e. subtlety is hidden: the pointwise identity holds
    **everywhere**, `Eventually.of_forall` is honest.
  * the field is `C01.energyIdentity_l2Sq` (`:98`), i.e. the `EnergySpec.lean` theorem — no
    analytic step is inlined into the adapter.
* `verification/Tests/EnergyAbsorptionPartialV2.lean` mirrors the V2 pattern:
  `def checkedEnergyAbsorptionPartialV2 : …V2API := Bindings.energyAbsorptionPartialV2` (`:29-31`),
  `run_cmd TestSupport.checkAxioms` (`:33`), plus one conformance `example` discharged by
  `.energyIdentity` **with no extra hypotheses** (`:36-43`).  **`warningAsError` respected**:
  its three imports are `Contracts.V2.…`, `Bindings.…V2`, `TestSupport.Axioms`; `grep -rn
  '^import Formal' verification/Tests/` returns nothing; the 28 `Formal.*` modules in the
  registered closure are reached only through `Bindings`, exactly as V1 does.  `make test`
  (which builds `Tests` under `warningAsError = true`) is green.
* Registry `contracts.json`: entry `C01.energy_absorption_partial_v2`, `version: 2`,
  `parent_task: "C01"`, `specification/binding_module/test_module/declaration` all correct and
  all resolving (`check_contracts.py` builds the closure for it: 1626 modules, +424 over V1).
  `git diff --numstat` = `11 0` — **additions only, zero deleted lines**; `grep '\\u[0-9a-fA-F]{4}'`
  over the whole file returns nothing, so `ensure_ascii=False` was used (LESSONS 141).  The scope
  string is long and **honest**: it names what is included (one field), what is inherited, all four
  disclosures, both bridges with their proof terms, and what is still excluded
  (`energyDifferentialBound`, `l2Bound`, the enstrophy fields, the Fourier inequality, the
  assembly, eq:Rcritical1/2, Grönwall / first-crossing) — I checked each exclusion against
  `Spec.lean` and V1's own out-of-scope list and found no overclaim.
  `work_items.json` / `TASKS.md` / `tasks/C01.md` all gained the same id and are consistent
  (`check_work_queue.py`: "30 work items: ownership, contract registration and task cards
  consistent").  `ENERGY_SPLIT.md`'s `energyIdentity` row is updated truthfully.
* `ATTEMPTS_V2_CONTRACT.md` is honest.  I opened the three declarations it cites — `rev150_gap.lean`,
  `rev150b_gradientsq.lean` (both present in `research/C01/probes/`), `Vocabulary.norm_toLp_sq_eq_l2Sq`
  (`Vocabulary.lean:107`) — and re-ran every command in its results table; all reproduce.  Its
  "negative examples" section records a real failure (the bare `SpatialField` name-resolution trap
  under the selective `open`) with the right diagnosis and the right fix (`A02.SpatialField`).

## 3. Gaps

Nothing blocking.  Two cosmetic notes, and two forward-looking observations.

**N1 (cosmetic, `Contracts/V2/EnergyAbsorptionPartial.lean:75,78`) — two unused `open`s in a
file that is about to be frozen.** `lift` in `open BlowupDensity.Contracts.V1 (lift gradientTensor)`
is never used (only `gradientTensor` is), and `open scoped ENNReal` is unused (the module has no
`ℝ≥0∞`).  Zero warnings either way.
*Fix (one line each):* `:75` → `open BlowupDensity.Contracts.V1 (gradientTensor)`; delete `:78`.

**N2 (cosmetic, citation, `Contracts/V2/EnergyAbsorptionPartial.lean:11-12`) — the DAG line range
covers only half of what the sentence asserts.** The docstring writes
"`DEPENDENCY_GRAPH.md:275-281`: `C01 ← A02, A05`; consumers `C01 → R43, R44`".  `:275-281` is the
C01 node and does contain `Dependencies: A02, A05` (`:277`), but the consumer arrows live at
`:285` and `:292` (R43 and R44 each list `C01` among their dependencies — both verified).  Both
mathematical facts are **correct**; only the range is short.
*Fix (one line):* `…DEPENDENCY_GRAPH.md:277`: `C01 ← A02, A05`; consumers `C01 → R43, R44`
(`:285,292`)`.

**N3 (forward-looking, not a defect).** The statement does not separately assert `Integrable` of
`x ↦ ‖∇u(t,x)‖²` or of `x ↦ ⟪u,f⟫` — Mathlib's `∫` is junk-`0` off the integrable set.  This is
**not exploitable**: the implementation must *prove* the equality with a real `HasDerivAt`, so
junk values would make the field false, not cheap.  But a *consumer* who needs "the dissipation is
finite" must get it elsewhere.  Inherited verbatim from the blind-comparison `Spec.lean` and
unchanged here, so it is not this lane's to fix; worth a sentence in the V3 contract, where
`energyDifferentialBound` will want `l2Norm`-finiteness anyway.

**N4 (planning).** `energyDifferentialBound` (`Spec.lean:364`) and `l2Bound` (`Spec.lean:383`) are
now unblocked (the first is `HasDerivAt.unique` + `real_inner_le_norm` + `norm_toLp_sq_eq_l2Sq`;
the second needs the `Paper1.sqrt_energy_le_primitive` generalisation) and are correctly declared
out of scope in both the module docstring §4 and the registry scope string, with "A future version
3 would add" written down.  No action this lane.

## 4. Commands and results

All from the worktree root, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` from
`verification/` only.

| command | result |
|---|---|
| `bash scripts/gates.sh NSFormalization.Section4.C01.EnergySpec` | **exit 0**, ends `== gates OK`. `make check` clean; `lake build …EnergySpec` `Build completed successfully (10305 jobs)`; `make test` lists **all 25** contracts "checked; standard logical axioms only", including `Tests/EnergyAbsorptionPartialV2.lean:32:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV2`; `make test-mutations` → `extra_axiom: rejected as required` / `weakened_hypothesis: rejected as required` / `Mutation suite passed.` |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | **exit 0**, `"registered_contracts": 25`, `"base_compatibility_checked": true` |
| `python3 experiments/check_work_queue.py` | `30 work items: ownership, contract registration and task cards consistent.` (exit 0) |
| `lake env lean ../research/C01/axioms_v2_contract.lean` | `'BlowupDensity.Tests.checkedEnergyAbsorptionPartialV2' depends on axioms: [propext, Classical.choice, Quot.sound]` — **exactly the three** |
| `lake env lean ../formalization/NSFormalization/Section4/C01/EnergySpec.lean` | exit 0, **0 bytes** (silent) |
| `lake env lean Contracts/V2/EnergyAbsorptionPartial.lean` | exit 0, **0 bytes** |
| `lake env lean Bindings/EnergyAbsorptionPartialV2.lean` | exit 0, **0 bytes** |
| `lake env lean Tests/EnergyAbsorptionPartialV2.lean` | exit 0, only the `checkAxioms` info line |
| `grep -rn 'sorry\|admit\|^axiom \|native_decide'` over the five new Lean files | no match |
| `git diff origin/erenup/integration -- verification/Contracts/V1 verification/Tests/EnergyAbsorptionPartial.lean verification/Bindings/EnergyAbsorptionPartial.lean` | **empty** (frozen V1 untouched) |
| `git diff --numstat origin/erenup/integration...HEAD -- verification/contracts.json` | `11 0` (additions only); no `\uXXXX` in the file |
| `diff <(sed -n '344,350p' research/C01/Spec.lean) <(sed -n '125,131p' verification/Contracts/V2/EnergyAbsorptionPartial.lean)` | **no output** — byte-identical |
| `diff` of the `gradientSq`/`pairing` `def` lines (`Spec.lean:185,196` vs contract `:86,91`) | **no output** — byte-identical |

### Negative checks

**(a) Contract-statement mutations — `probes/rev152_mutation.lean`, exit 1, both rejected.**
Two substantive mutations of the field, each given the binding's own proof script
(`rw [energyAbsorptionPartialV2_gradientSq_eq]; exact C01.energyIdentity_l2Sq (uniqueness_toA02 w) hf ht`):

* **A. `-2 * ν` → `-ν`** (`:32:4`): `error: Type mismatch … has type HasDerivAt … ((-2 * ν✝ * ∫ …) + 2 * pairing …) … but is expected to have type HasDerivAt … ((-ν✝ * ∫ …) + 2 * pairing …)`.
* **B. `2 * pairing …` → `pairing …`** (`:44:4`): same shape, mismatch localised to `2 * pairing … ` vs `pairing …`.

In each error the LHS and the *unmutated* summand print identically on both sides and only the
mutated summand differs — i.e. the viscous coefficient `2ν` and the forcing factor `2` are both
individually load-bearing, and the binding cannot absorb a change in either.

**(b) Non-vacuity — `probes/rev152_nonvacuity.lean`, exit 0, standard 3 axioms.**

* `nonvac_interior (w : ClassicalSolutionR ν a f T) : (Ioo (0:ℝ) T).Nonempty :=
  nonempty_Ioo.2 w.horizon_pos` — the `∀ t ∈ Ioo 0 T` is never an empty quantification, because
  the structure itself carries `horizon_pos : 0 < T` (`Data.lean:630`).
* `nonvac_witness (ν T) (hν : 0 < ν) (hT : 0 < T) : ClassicalSolutionR ν 0 0 T :=
  maximalPartial_ofA02 (A04.zeroSol ν T hν hT)` — the whole hypothesis block is satisfiable
  (`A04.zero_mem_initialClassR`, `A04.memForceR_zero`).
* `nonvac_instance` applies the **contract's own witness**
  `energyAbsorptionPartialV2.energyIdentity` to that instance at the interior time `T/2` and
  obtains a real `HasDerivAt`; `#print axioms nonvac_instance` →
  `[propext, Classical.choice, Quot.sound]`.

**(c) Vocabulary defeq — `probes/rev152_defeq.lean`, exit 0.** `gradientTensor z x = WithLp.toLp 2
(fun i => fderiv ℝ z x (coordinateVector i))` by `rfl`; the full Frobenius expansion
`‖gradientTensor z x‖² = ∑ᵢ∑ⱼ |∂ᵢzⱼ|²`; the inherited V1 `slice`/`l2Sq` are `rfl`-equal to
`C01.slice`/`C01.l2Sq`; `@EulerOrdinarySobolev.axis = @coordinateVector` by `rfl`; and `#check`
prints for the three binding bridges.
