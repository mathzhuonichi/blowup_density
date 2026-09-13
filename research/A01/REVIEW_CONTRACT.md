# A01 lane 112 — contract review of `A01.regularity_partial`

Reviewer run in worktree `.claude/worktrees/112-A01-regularity-partial`, commit
`92c9f7d` on `erenup/112-A01-regularity-partial` (single commit above
`origin/erenup/integration` at `36b4261`).  Contract lane: strict
statement-fidelity review, Lean and all gates run by the reviewer.

## Verdict: **ACCEPT-WITH-NOTES**

The two registered fields are **token-for-token the spec's**, the flattening adds
no hypothesis, all three `rfl` bridges elaborate, the Tests module reports
`checked; standard logical axioms only`, and every gate is green.  The notes are
about *documentation of a V1 that is about to be frozen*, not about the Lean.
Finding 1 is the one I would fix before merge, because the sentence it concerns
becomes immutable the moment this lands.

---

## 1. Gates — all PASS

| gate | result |
|---|---|
| `lake build Tests.RegularityPartial` | `Build completed successfully (9953 jobs).`  `info: Tests/RegularityPartial.lean:17:0: Contract BlowupDensity.Tests.checkedRegularityPartial: checked; standard logical axioms only` |
| `make check` | exit 0 — `check_formalization_plan` (unchanged: the single known `sorry` token is `Paper1/BoundaryCorollary.lean:90`, not in any closure), `check_contracts` **19 registered contracts**, `test_contract_policy` 13 tests OK, `check_work_queue` "30 work items: ownership, contract registration and task cards consistent" |
| `make test` | exit 0 — all 19 contracts replay, each `checked; standard logical axioms only`, `Tests.RegularityPartial` among them |
| `make test-mutations` | exit 0 — `implementation_refactor: accepted`, `admitted_proof / extra_axiom / weakened_hypothesis: rejected as required` |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | exit 0, `registered_contracts: 19`, `base_compatibility_checked: true` (so no `Contracts/*` file on the base was removed or byte-changed) |
| `bash scripts/gates.sh Tests.RegularityPartial` | `== gates OK` |
| import policy | `Contracts/V1/RegularityPartial.lean` has exactly one import, `Contracts.V1.Data` — inside the strict rule, no white-list relaxation used |
| `Formal.*` in the Tests closure | none.  The registered closure has 1189 modules; filtering for `Formal` gives `[]` (`Section4/A01/RadialPotential` reaches `Euler.CompactParameterIntegral`, i.e. the OpenAI package, never HeliCorgi) |
| frozen files untouched | `git diff --stat origin/erenup/integration...HEAD` = 8 files, of which the three Lean files are **new**; no existing `Contracts/V1/*` or `Tests/*` file is modified |
| hygiene | no `sorry` / `admit` / `axiom` / `native_decide` in any of the three new files; no untracked leftovers (`git status --porcelain` empty; the de-risk probe `research/A01/probe_contract.lean` really was deleted) |

---

## 2. Statement fidelity — the core

### (a) Field-by-field against `research/A01/Spec.lean`

The flattening is `∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) (u : ClassicalSolutionR ν a f T),`
prefixed to the spec field's body.  `ManuscriptLocalRegularity` (`Spec.lean:167`)
is a `Prop` structure with parameters `(ν a f T u)` and **no hypothesis fields**,
so the flattened form is logically the same statement; I confirmed by reading
`Spec.lean:167-169` that the structure header carries `0 < ν`, `a ∈ initialClassR`,
`MemForceR f` **nowhere**, and the contract adds none.  This is the one real
difference from the `EnergyAbsorptionPartial.velocityJets` precedent
(`Contracts/V1/EnergyAbsorptionPartial.lean:166-171`, which does carry all three),
and the difference is in the safe direction: the registered reading is strictly
stronger.  Both discharging theorems indeed take no such hypothesis
(`projected_of_classicalSolution (ν) (a) (f) (T) (u)`;
`pressure_potential_of_classicalSolution {ν} {a} {f} {T} (u)`).

| field | spec (`Spec.lean`) | contract (`Contracts/V1/RegularityPartial.lean`) | verdict |
|---|---|---|---|
| `projected` | `:214-218`: `∀ t ∈ Ioo (0:ℝ) T, ∀ x : Space, temporalDerivative u.velocity t x - ν • spatialLaplacian u.velocity t x = (f (t, x) - convectionDivergence u.velocity t x) - pressureGradient u.pressure t x` | `:141-152`, same body verbatim under the `∀ ν a f T u` prefix | **identical**.  `ν` and `f` under the prefix are the solution's own viscosity and force (they are the parameters of `ClassicalSolutionR ν a f T`), so no silent decoupling.  `u.velocity` / `u.pressure` / `Ioo 0 T` unchanged |
| `pressure_potential` | `:227-229`: `PressureGaugeEquivOn (Ico (0:ℝ) T) (pressurePotential (fun z : SpaceTime => pressureGradient u.pressure z.1 z.2)) u.pressure` | `:154-159`, same body verbatim under the same prefix | **identical**.  `Ico 0 T` (endpoint included) unchanged; `pressurePotential` and `PressureGaugeEquivOn` are `Data.lean:596,589`, not restated |
| `convectionDivergence` (restated) | `Spec.lean:103-105` | `:104-106` | **byte-identical** (`∑ j : Fin 3, fderiv ℝ (fun y : Space => (u (t, y) j) • u (t, y)) x (coordinateVector j)`) |
| `HasSymmetricJacobian` (restated) | `Spec.lean:119-122` | `:118-121` | **byte-identical** |
| `sobolev_smooth`, `pressure_recovery` | `Spec.lean:180`, `:197` | absent | correctly absent, and named as absent in module docstring, scope string and `ATTEMPTS_CONTRACT.md` |

### (b) The three `rfl` bridges

All three elaborate (the module builds; `Bindings/RegularityPartial.lean:50-68`):

* `regularityPartial_pressurePotential_eq : Contracts.V1.Data.pressurePotential = NSFormalization.Section4.A01.RadialPotential.pressurePotential := rfl`
  — **this is the `REVIEW_M4` finding 6 debt, and it is the one the field actually
  goes through.**  `pressure_potential_of_classicalSolution`
  (`PressureGauge.lean:210-213`) states its conclusion with
  `RadialPotential.pressurePotential` (`PressureGauge.lean` imports
  `Section4/A01/RadialPotential` and its own docstring `:36` lists
  `pressurePotential` as reused from there), while the contract field uses
  `Data.pressurePotential`.  The field assignment at `Bindings:85-87` typechecks
  **only** because those two are defeq; the bridge is the named guard on exactly
  that defeq.  Debt cleared, and load-bearing as advertised.
* `regularityPartial_convectionDivergence_eq` — guards `projected`; same
  situation (`ProjectedEquation.lean:40-46` produces the
  `Section4.A01.convectionDivergence` spelling).
* `regularityPartial_hasSymmetricJacobian_eq` — see (c).
* `PressureGaugeEquivOn` is **not** re-restated; the binding reuses the already
  registered `Bindings.uniqueness_pressureGaugeEquivOn_eq`
  (`Bindings/Uniqueness.lean:54-57`).  Correct, and the right precedent.

Structure transport: `uniqueness_toA02` (`Bindings/Uniqueness.lean:66-77`) is
reused rather than re-declared, exactly as `Bindings/EnergyAbsorptionPartial.lean`
does — the `structure` exception of CLAUDE.md is honoured and only one local
restatement of the solution class exists.

### (c) `HasSymmetricJacobian`: restated, consumed by nothing — judgement

**Keep it, but the stated justification is slightly inverted.**  The CLAUDE.md
rule ("每个重写的定义都要有桥") is about definitions a *contract* rewrites; here
the rewriting direction is the other way round — `RadialPotential.HasSymmetricJacobian`
mirrors a *draft spec* def (`Spec.lean:119`), and draft specs are not contracts,
so there was no policy debt to clear.  `REVIEW_M4` #6 named `pressurePotential`
as the load-bearing debt and merely observed that `HasSymmetricJacobian` "is not
yet a contract object".  Creating a contract-side home *in order to* have a
bridge left-hand side is scaffolding, and freezing a def with no consumer in V1
is a mild oddity.

That said, I would not remove it: the excluded `pressure_recovery` field runs
through `Spec.lean:135`'s `IsLerayComplement`, whose second clause **is**
`HasSymmetricJacobian`.  Whichever lane registers `pressure_recovery` will need
this predicate contract-side, and having it already frozen in
`Contracts.V1.RegularityPartial` means that lane imports it rather than restating
it a second time.  So: harmless scaffolding *today*, with a real consumer already
on the map.  Note only, not a blocker — but the docstring should say "reserved for
`IsLerayComplement`/`pressure_recovery`" rather than only "to home a bridge".

### (d) Could a wrong implementation satisfy either field?

The API is a `Prop` structure with **no data fields**, so there is nothing to
instantiate wrongly: a binder must prove both universally quantified statements.
The remaining question is whether the statements are weak or vacuous.

* **`projected` is not vacuous and not trivial**, but it is *equivalent to*
  `ClassicalSolutionR.momentum`.  E1's
  `navierStokesResidual_eq_iff_projected` (`ConvectionDivergence.lean:127-138`)
  is an **iff** at any point where the velocity is spatially differentiable and
  divergence free — and every `ClassicalSolutionR` supplies both at every
  interior time.  So the field carries exactly the NS momentum content of the
  solution class, re-spelled in the manuscript's `∇·(u⊗u)` vocabulary; it adds
  no Leray-projection content.  See Finding 1.
* **`pressure_potential` carries no Navier–Stokes content at all** (`REVIEW_M4`
  #7): its proof consumes only `u.pressure_smooth`.  This **is** disclosed, and
  well: module docstring "Fidelity note (`REVIEW_M4.md` #7)" (`:83-91`), the
  field docstring `:161-163`, the `contracts.json` scope string's closing
  sentence, and `ATTEMPTS_CONTRACT.md`.  Non-triviality of the underlying lemma
  was machine-checked by the lane-106 reviewer (`REVIEW_M4` §2(d): with
  `p(t,x) = x₀` the radial potential reconstructs `p`, and a "zero potential"
  implementation is refutable) — I did not re-run that probe.
* **Vacuity through an uninhabited `ClassicalSolutionR`**: nothing in tree
  constructs a `ClassicalSolutionR` from scratch (`Restrict.lean:208`,
  `Maximal.lean:101`, `Order.lean` all *consume* `Nonempty`), so both fields are
  formally conditional on solutions existing.  That is not this lane's problem —
  it is precisely `LocalTheoryAPI.solution`, A01's remaining deliverable, and the
  same caveat applies verbatim to the already-registered `A02.uniqueness`,
  `C01.energy_absorption_partial` and every other `ClassicalSolutionR` contract.
  Recorded, not a finding.

---

## 3. Scope honesty — PASS (with Finding 1)

`contracts.json` diff is **only** the new 11-line entry; no other scope string,
and no byte elsewhere in the registry, changed (`git diff origin/erenup/integration...HEAD -- verification/contracts.json`
shows a pure insertion).  The `ensure_ascii` misstep `ATTEMPTS_CONTRACT.md`
records really was reverted: the Unicode in the neighbouring B02 scope string is
intact.

The scope string names both fields with their `Spec.lean` and `.tex` lines, both
discharging theorems and modules, the `Prop`/`theorem` shape, the `uniqueness_toA02`
transport, all three bridges, the explicit statement that `HasSymmetricJacobian`
is referenced by no field, the four exclusions (`sobolev_smooth`,
`pressure_recovery`, all of `LocalTheoryAPI`, every A02 clause) and the
no-NS-content caveat for `pressure_potential`.  That is the same level of
disclosure as the 091/096/099 entries, and `check_work_queue` confirms
`work_items.json` + the two rendered files are consistent (contract id added to
A01's list; `TASKS.md` and `tasks/A01.md` regenerated, nothing hand-edited).

The one gap is the missing symmetric caveat for `projected` — Finding 1.

---

## 4. Consistency — PASS

* `Tests/RegularityPartial.lean` is shape-identical to
  `Tests/EnergyAbsorptionPartial.lean` (same three imports, same
  `noncomputable section` / `namespace BlowupDensity.Tests`, same
  `run_cmd TestSupport.checkAxioms`), with `theorem` instead of `def` because the
  API is propositional — which is exactly `Tests/Uniqueness.lean:13-16`.  Correct
  choice, and the docstring says why.
* `warningAsError = true` in `verification`: the build emitted no warning from
  any `Contracts`/`Bindings`/`Tests` module (the warnings in the log are all
  replayed `formalization/` modules, pre-existing).
* No duplicate restatement: a grep over `verification/Contracts/` shows
  `convectionDivergence` and `HasSymmetricJacobian` defined **once** (here), and
  `pressurePotential` / `PressureGaugeEquivOn` **only** in `Data.lean`.
* `Prop`-structure choice (un-annotated `structure … where`, Lean infers `Prop`)
  matches `UniquenessAPI`; data-carrying precedents like
  `HomogeneousApproxPartialAPI` (which is a `Type` because of its `chi` field)
  are correctly not imitated.  Fine; noted for the record.

---

## Findings

| # | severity | location | finding / suggested fix |
|---|---|---|---|
| 1 | **note, but fix before merge** | `Contracts/V1/RegularityPartial.lean:98-102`, `:133-143` (the `projected` docstrings); `contracts.json` scope, `projected` clause | The docstrings assert more than the contract proves. `:101` says the manuscript spelling makes `projected` "a statement about eq:projected, **not a restatement of `ClassicalSolutionR.momentum`**", and `:139-141` repeats the spec's "Written as `P(f − ∇·(u⊗u)) = (f − ∇·(u⊗u)) − ∇p`".  Both sentences are legitimate **in `Spec.lean`**, where `pressure_recovery` sits one field above and licenses the substitution `∇p = (I−P)(f − ∇·(u⊗u))`.  In this contract `pressure_recovery` is *excluded*, and E1 (`ConvectionDivergence.lean:127`) is an **iff**, so at every interior point the registered field is exactly equivalent to `momentum`; what the manuscript spelling buys is display, not content, and the identification with eq:projected's `−P∇·(u⊗u) + Pf` right-hand side is precisely the excluded field.  Since `pressure_potential` already gets its honest "carries no NS content" caveat, `projected` should get the parallel one.  **Fix:** one sentence in the field docstring and one clause in the scope string, e.g. "E1 is an `iff`, so given `divergence` and spatial differentiability this field is *equivalent* to `ClassicalSolutionR.momentum`; its reading as eq:projected's Leray-projected form requires the excluded `pressure_recovery`."  Costs nothing now; is frozen forever after merge. |
| 2 | note | `Contracts/V1/RegularityPartial.lean:112-116`, `Bindings/RegularityPartial.lean:54-59` | `HasSymmetricJacobian`'s stated rationale ("to give the implementation's restatement a canonical contract-side home and thereby clear the one-bridge-per-restatement debt") inverts the policy: the implementation restates a *draft spec* def, not a contract def, so no debt existed for it (`REVIEW_M4` #6 named only `pressurePotential`).  The real justification is forward-looking — `Spec.lean:135`'s `IsLerayComplement`, hence the excluded `pressure_recovery`, needs this predicate contract-side.  **Fix (optional, same edit window as 1):** reword to "reserved for `IsLerayComplement` / `pressure_recovery`; referenced by no field of this version."  Keeping the def is right; only the sentence is off. |
| 3 | note (bookkeeping) | `research/A01/ATTEMPTS_CONTRACT.md` "What worked / did not" | The de-risk probe is cited as `research/A01/probe_contract.lean`, "deleted after use".  This is the same class of volatile citation that `logs/LESSONS.md`'s 2026-09-14 top entry warns about (a `/tmp` probe that vanished).  Nothing is lost here — the probe's content is fully subsumed by the three bridges and two field assignments that now compile in the frozen files, so the evidence is permanent by other means.  Recorded only so the pattern is not repeated where the probe *is* the only evidence. |
| 4 | cosmetic | `formalization/.../PressureGauge.lean:210-211` | Pre-existing, already `REVIEW_M4` #8: binders are `{a : Space → Space} {f : VelocityField}` where the contract writes `SpatialField` / `SpaceTimeField`.  Reducible abbrevs, the binding typechecks, no action for this lane. |

No finding is a blocker.  Finding 1 is the only one I would want addressed
*before* the merge, because it concerns immutable V1 prose; a one-line amend
commit on this branch is enough, and it needs no re-proof (docstring and JSON
string only — though `make check` and `lake build Tests.RegularityPartial` should
be re-run after touching the `.lean` docstring).

---

## Commands run

```
bash scripts/lean-install.sh                                   # exit 0 (idempotent)
. scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
cd verification && lake build Tests.RegularityPartial
    -> Build completed successfully (9953 jobs).
    -> info: Tests/RegularityPartial.lean:17:0: Contract
       BlowupDensity.Tests.checkedRegularityPartial: checked; standard logical axioms only
make check          -> exit 0; registered_contracts 19; 13 policy tests OK;
                       "30 work items: ownership, contract registration and task cards consistent"
make test           -> exit 0; 19 contracts replayed, all "standard logical axioms only"
make test-mutations -> exit 0; implementation_refactor accepted;
                       admitted_proof / extra_axiom / weakened_hypothesis rejected as required
python3 experiments/check_contracts.py --base-ref origin/erenup/integration
                    -> exit 0; registered_contracts 19; base_compatibility_checked true
bash scripts/gates.sh Tests.RegularityPartial               -> "== gates OK"
git diff --stat origin/erenup/integration...HEAD            -> 8 files, 3 new .lean, no frozen file touched
git status --porcelain                                      -> clean
(closure inspection) A01.regularity_partial closure = 1189 modules, zero "Formal.*"
```

---

## What A01 still owes A02, and the next lane

This contract makes lanes 093/101/106 visible to consumers, but it moves A02's
blocker not at all.  What A02 needs from A01 is **`LocalTheoryAPI`**
(`Spec.lean:277`): the *data* `solution` — a `ClassicalSolutionR ν a f (horizon ν a f)`
for every `ν > 0`, `a ∈ X_R`, `f ∈ F_R`, which is what lets A02 say "*the* local
solution for `(a,g)`" instead of quantifying over hypothetical ones — the
`regularity` bundle (all four `ManuscriptLocalRegularity` fields on that
solution, so both fields still missing here are on the critical path), and
`horizon_lower_bound`, the uniform positive `T₀(ν,a,f)` valid for every Sobolev
order simultaneously (`appendix-a-local-theory.tex:66-67`).  Nothing in tree
inhabits `ClassicalSolutionR` from scratch today: A02's `Restrict`, `Maximal`,
`Order` and R42 all *consume* `Nonempty (ClassicalSolutionR …)`, so the whole
maximal-lifespan layer is currently conditional, and the two fields registered
here are conditional in the same way.  Closing that is the existence half of
`prop:local`, which needs unit **T1** (all-order time smoothness) behind **A3**
(order-independent `T₀`), and the `A01_SPLIT.md` c-rows — with **c3/B1** (one
jointly space-time `C^∞` field out of the `H^m`-valued time paths) the single
biggest blocker.

**Recommended next A01 lane — P3, then m2**, exactly as `REVIEW_M4` scheduled it
(its candidate 1, the bridge lane, is what lane 112 just did).  Split it: first
unit **P3**, the physical eq:Rpressure, whose HeliCorgi input
`Formal/R3HelmholtzPressure.lean:259 r3HelmholtzPressure_gradient` is importable
today (`A01_SPLIT.md:74`) and whose real work is the carrier bridge from the
complex `L²`/`𝓢'` statement to the pointwise `∇p`, with the **P2** Liouville gap
(`IsLerayComplement` single-valuedness for `L²`-harmonic fields) isolated as its
own row; only then row **m2** `pressure_recovery` on `Ico 0 T`, where the genuine
increment over D01's L9(c) is the `t = 0` endpoint.  That lane is also what turns
`pressure_potential` from a gauge normalization into the manuscript's full
pressure prescription (Finding 1's and `REVIEW_M4` #7's point), and it will want
`Contracts.V1.RegularityPartial.HasSymmetricJacobian` — the def Finding 2
discusses.  Do **not** open `sobolev_smooth` / B1 as an S- or M-sized lane; it is
the L-cluster and needs its own plan.

Note for whoever registers `pressure_recovery`: it will not extend this contract
in place (V1 is frozen), so it lands either as a second partial contract
(`A01.pressure_recovery`) or as `RegularityPartial` V2 bundling three fields.
Given that `LocalTheoryAPI` is still far off, a second partial contract reusing
V1's `convectionDivergence` and `HasSymmetricJacobian` is the cheaper shape.
