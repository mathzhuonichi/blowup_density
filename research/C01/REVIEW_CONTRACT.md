# Lane 091 contract review — `C01.energy_absorption_partial`

Reviewer: opus, lane 091. Worktree `.claude/worktrees/091-C01-partial-contract`,
commit `d638841`, branch base `0df09c1` (`origin/erenup/integration` is now at
`f2fdece`, 8 commits ahead — see finding 7).

## Verdict

**ACCEPT-WITH-NOTES.**

All five propositional fields plus `C₁`/`C₁_pos` are, after whitespace
normalization, **token-for-token identical** to `research/C01/Spec.lean` — I
diffed them mechanically, with zero deviations (table in §2). The six restated
spec-local `def`s are verbatim transcriptions and each `rfl` bridge in the
binding really targets the object the discharging theorem's statement uses (not a
second local copy). The binding contains no proof content: every field is a
direct assignment or an eta-wrapper, and `velocityJets` goes through the reused,
field-wise `Bindings.uniqueness_toA02` with no strengthening or weakening. The
`contracts.json` `scope` partitions the 23 fields of `EnergyAbsorptionAPI`
**exactly** (7 in, 16 out), and I confirmed none of the 16 excluded fields is
discharged anywhere in `Section4/`. All six gates pass; the axiom audit reports
standard logical axioms only.

The findings below are (1-3, 6) documentation defects, two of them inherited
verbatim from `Spec.lean` and now frozen into `Contracts/V1`, (4-5) two
non-blocking hardening suggestions, and (7) base drift that the merge must
handle. **No Lean statement, no binding, and no build is affected by any of
them.**

---

## 1. Findings

### 1. `04-whole-space.tex:115` should be `:114` — LOW (doc, in a frozen file)

`verification/Contracts/V1/EnergyAbsorptionPartial.lean:123`, the `laplacianSq`
docstring: "`research/C01/Spec.lean:191`: `04-whole-space.tex:109,115`, `‖Δz‖₂²`".

Line 115 of the manuscript is `\le C\nu^{-1}\norm{f}_2^2.` — the *force* term.
The occurrence of `‖Δu‖₂²` inside eq:RH1 is line **114**
(`(\norm{\nabla u}_2^2)'+\nu\norm{\Delta u}_2^2`). Inherited verbatim from
`research/C01/Spec.lean:189` (which, two defs earlier, cites `:114` correctly for
`gradientSq` — so the error is a slip, not a different convention).

Fix: `04-whole-space.tex:109,114`. Since `Contracts/V1` is frozen by
`check_contracts.py`, this cannot be patched in place; carry the correction into
a V2 docstring, or leave it and note it here. I do **not** consider it worth a V2
on its own.

### 2. Inexact quotation of `STATEMENTS.md:604` — LOW (doc, in a frozen file)

`Contracts/V1/EnergyAbsorptionPartial.lean`, module docstring: the one
`research/section4/STATEMENTS.md:604` quotes ("`H¹` absorption once
`C₁‖u‖₃ ≤ ν/4`").

`STATEMENTS.md:604` actually reads: "`eq:RH1` (`H¹` absorption once
`‖u‖₃ ≤ ν/(4C₁)`)". The two are equivalent for `C₁ > 0`, but the text is placed
inside quotation marks as if verbatim, and it is not. Also inherited from
`Spec.lean:255-259`. Fix: quote the source verbatim, or drop the quotes.

### 3. `04-whole-space.tex:96-131` is looser than the contract's content — INFO

The module docstring and the registry `scope` both give the paper range as
`:96-131`. Lines 96-104 are the eq:Rcritical1 block (`½(y²)'+(ν−C₀y)z² ≤ by` and
its regularized integration), which the contract explicitly lists as *out of
scope*. The range the contract actually formalizes is **106-131**. This matches
the lane brief's own citation, so it is not a deviation from instruction; I
record it so a future reader does not infer that eq:Rcritical1 is covered. The
docstring's "Also asserted nowhere" paragraph already says it is not, so there is
no contradiction — only an over-wide pointer.

### 4. `integrable_advection_inner_laplacian` proved but not exported — NOTE

`formalization/NSFormalization/Section4/C01/Trilinear.lean:214` proves that
`x ↦ ⟪(z·∇)z, Δz⟫` is integrable on the jet class. It is **not** a field of
`Spec.lean`'s `EnergyAbsorptionAPI`, so its absence is not a scope-honesty
violation at field granularity (check 3 passes). But it is the one thing that
keeps `advectionWork z` from being Mathlib's junk `0`, and without it a holder of
this contract alone cannot rule out that `trilinearHolder` / `trilinearAbsorbed`
are `0 ≤ …` and therefore vacuous from the consumer's side. The mathematics is
done; only the export is missing.

Recommendation (not blocking this lane): when the enstrophy fields are added —
they are the fields that actually consume the trilinear bound — carry
`integrable_advection_inner_laplacian` as a field alongside them.
`research/C01/ATTEMPTS_CONTRACT.md` already records the decision not to register
it now, which is the right call for a *partial* contract that mirrors `Spec.lean`
field-for-field.

### 5. No `rfl` drift-guard for `Data.MemHInfty = A02.MemHInfty` — NOTE (Bindings, not frozen)

`verification/Bindings/EnergyAbsorptionPartial.lean:28` asserts in prose that
"`MemHInfty`/`SmoothSquareIntegrableJets` match". `SmoothSquareIntegrableJets` is
guarded by `Bindings.GradientL6.smoothSquareIntegrableJets_eq := rfl`;
`MemHInfty` is guarded by nothing. `Bindings/Uniqueness.lean` §0 sets the
precedent by recording `rfl` bridges for exactly the three other A02-local
restatements (`initialClassR`, `MemForceR`, `PressureGaugeEquivOn`), and
`MemHInfty` is the fourth of that family.

I verified by hand that the two are token-identical
(`Contracts/V1/Data.lean:495-496` vs
`formalization/NSFormalization/Section4/A02/SolutionClass.lean:88-90`, the only
difference being a line break after `ContDiff ℝ ∞ a ∧`), and any real drift would
fail the build rather than change the meaning silently, so this is cosmetic
hardening. `Bindings/` is not frozen, so a one-line

```lean
theorem energyAbsorptionPartial_memHInfty_eq (a : Contracts.V1.Data.SpatialField) :
    Contracts.V1.Data.MemHInfty a = NSFormalization.Section4.A02.MemHInfty a := rfl
```

can be added at any time, including after merge.

### 6. Wrong line number in `ATTEMPTS_CONTRACT.md` — LOW (non-durable file)

`research/C01/ATTEMPTS_CONTRACT.md`, "Which vocabulary is canonical": "`lift`,
`gradientTensor` (GradientL6:94), `laplacian` (GradientL6:94, name at :94)".
`gradientTensor` is at `Contracts/V1/GradientL6.lean:89`; `lift` is at `:78`. The
**contract file itself has this right** (`GradientL6.lean:89,94,106`), so only the
attempts note is wrong.

### 7. Base drift: the lane is 8 commits behind `origin/erenup/integration` — MERGE ACTION

`origin/erenup/integration` has advanced past this branch's base (lane 085's
`Section4/D01/LerayLowering.lean` merge, plus lane 087/092 bookkeeping).
`verification/Contracts` is unaffected (the only Contracts diff is the new file,
0 deletions), which is why `check_contracts.py --base-ref` reports
`base_compatibility_checked: true`. I confirmed `LerayLowering` is **not** in
`C01.energy_absorption_partial`'s import closure, so the rebase is mechanical and
cannot change this contract's meaning. Standard `/lane-merge` three-way merge on
`contracts.json` / `work_items.json` / `TASKS.md`, then re-run `make test` on the
rebased tip before pushing.

---

## 2. Field-by-field fidelity

Diffed mechanically: each field's type was extracted from both files, whitespace
normalized, and compared as a string. **All seven are identical; there are no
deviations to list.** No namespace prefixes even had to be normalized — the
contract's `open` block (`Contracts.V1 (lift gradientTensor laplacian
SmoothSquareIntegrableJets)`, `Contracts.V1.Data`,
`NavierStokes.ProblemStatement`, `Set MeasureTheory`, `scoped ContDiff ENNReal`)
reproduces `Spec.lean`'s exactly, so the field texts are byte-comparable.

| field | `Spec.lean` | contract | diff | discharged by | could a wrong implementation satisfy it? |
|---|---|---|---|---|---|
| `C₁ : ℝ` | :260 | :156 | none | `Bindings.gradientL6.Csix` = `A05.gradientL6Const` | Data field with one degree of freedom. Universality is **structurally** enforced: `C₁` sits outside every `∀`, so it cannot depend on `ν`, `a`, `f`, `T` or `z` — exactly the manuscript's "universal `C₁`". A larger `C₁` weakens `trilinearAbsorbed`, so the only cheat is a *huge* constant, which is mathematically legitimate and is what "some universal constant" means. |
| `C₁_pos : 0 < C₁` | :262 | :158 | none | `A05.gradientL6Const_pos` | No. Rules out the `C₁ ≤ 0` reading; note that with `C₁ ≤ 0` `trilinearAbsorbed` would be *stronger* (unprovable), not vacuous, so this field is honesty rather than load-bearing. Registering it without a separate conformance `example` is **fine**: its statement is three tokens, it was diffed here, and `Tests` type-checks the assembled record, which is the real audit. |
| `velocityJets` | :295-300 | :166-171 | none | `C01.velocity_slice_memHInfty_and_smoothL2` | No. Conclusion is a genuine regularity claim (`MemHInfty` ∧ jets) for every slice. Not vacuous: `Data.ClassicalSolutionR` is inhabited via the separately registered `A02.maximal_partial_v2` / A01 `localSolution`. Quantifier order, the `Ico (0:ℝ) T` horizon guard and the `MemHInfty ∧ SmoothSquareIntegrableJets` conjunction are identical on both sides (see §3). |
| `forceTimeRegularity` | :326-329 | :179-182 | none | `C01.forceTimeRegularity` | No — and the *conjunction* is what prevents it. `ContinuousOn (fun s => l2Norm (slice f s)) (Ici 0)` alone would be satisfiable by junk (`l2Sq` of a non-integrable slice is Mathlib's `0`, a constant, hence continuous); the first conjunct `∀ t ≥ 0, MemLp (slice f t) 2 volume` forces every `l2Sq` in sight to be an honest integral. Good design, carried over intact. |
| `trilinearHolder` | :410-414 | :190-194 | none | `C01.trilinearHolder` | Zero implementation freedom — every object (`advectionWork`, `criticalL3`, `gradientTensor`, `laplacian`, `SmoothSquareIntegrableJets`) is pinned by the contract or by the registered `GradientL6`. Non-vacuous on the right: `‖z‖₃ < ∞` on the jet class (`L²∩L⁶ ⊂ L³` via `H¹ ↪ L⁶`), so the RHS is not identically `⊤`. See finding 4 for the LHS side. |
| `trilinearAbsorbed` | :435-439 | :202-206 | none | `C01.trilinearAbsorbed` | Same. **Not weakened relative to the manuscript**: the paper's chain at `:108-110` is `\|⟨(u·∇)u,Δu⟩\| ≤ ‖u‖₃‖∇u‖₆‖Δu‖₂ ≤ C₁y‖Δu‖₂²`; the contract stops at the *middle* form after applying only `‖∇u‖₆ ≤ C‖Δu‖₂`, i.e. `≤ C₁‖z‖₃‖Δz‖₂²`. Since A05 gives `‖u‖₃ ≤ Cy`, the `‖u‖₃` form **implies** the paper's `C₁y` form (with constant `C₁C`) and not conversely — so this is the stronger statement, and `C₁` here differs from the manuscript's `C₁` by the A05 constant. The docstring says so explicitly, and the excluded `enstrophyIntegralBound` (`Spec.lean:536-537`) states its smallness hypothesis in the same `ENNReal.ofReal C₁ * criticalL3 … ≤ ENNReal.ofReal (ν/4)` vocabulary, so the two readings will not be mixed in V2. |
| `laplacianSqENorm` | :471-473 | :214-216 | none | `C01.laplacianSqENorm` | No, and this is the strongest of the five. It is an **equality** with no `.toReal`: if `Δz ∉ L²` the LHS is `⊤` while the RHS is `ENNReal.ofReal (junk 0) = 0`, so the field genuinely asserts `Δz ∈ L²` on the jet class. A junk-value implementation is refuted, not accommodated. |

### The six restated `def`s

Each opened in `Spec.lean`, re-read in the contract, and traced to the object the
implementation's theorem statements actually mention. All six are verbatim.

| def | `Spec.lean` | contract | implementation the `rfl` bridge targets | bridge really points at the used object? |
|---|---|---|---|---|
| `slice` | :167 | :113 | `Section4/C01/ForceSlices.lean:80` | Yes — `ForceSlices.lean:160-161` states `forceTimeRegularity` with this `slice`. |
| `l2Sq` | :172 | :117 | `ForceSlices.lean:83` | Yes — reached through `l2Norm`, which the theorem statement uses. |
| `l2Norm` | :177 | :121 | `ForceSlices.lean:86` | Yes — `ForceSlices.lean:161`. |
| `laplacianSq` | :191 | :127 | `Trilinear.lean:72` (written with `lap`) | Yes — it is the RHS of `laplacianSqENorm` at `Trilinear.lean:274`. |
| `criticalL3` | :212 | :132 | `Trilinear.lean:75` | Yes — `Trilinear.lean:242, 257`. |
| `advectionWork` | :202 | :138 | `Trilinear.lean:79` (written with `lap`) | Yes — LHS of both trilinear theorems, `Trilinear.lean:241, 256`. |

The `lap`/`laplacian` and `gradTensor`/`gradientTensor` spelling difference is
absorbed by the already-registered `Bindings.GradientL6` `rfl` bridges
(`laplacian_eq`, `gradientTensor_eq`, `smoothSquareIntegrableJets_eq`), which is
why each bridge above elaborates as `rfl`. **No second local copy is involved:**
the contract does not restate `lift`, `gradientTensor`, `laplacian` or
`SmoothSquareIntegrableJets`; it opens them selectively from
`Contracts.V1.GradientL6` (`EnergyAbsorptionPartial.lean:104-105`). This is
precisely what check 4 asked for.

`Spec.lean`'s `gradientSq`, `pairing`, `forcePrimitive`, `energyBudget` are *not*
restated — correct, since each is mentioned only by an excluded field.

---

## 3. `velocityJets`: the structure conversion

The field quantifies over `Contracts.V1.Data.ClassicalSolutionR`; the theorem
needs `Section4/A02`'s restatement. A `rfl` bridge is impossible (two separately
declared `structure`s = two inductive types), so the binding uses the **reused**
`Bindings.uniqueness_toA02` from `Bindings/Uniqueness.lean:63-75` rather than
declaring a second converter — correct under `CLAUDE.md`'s one-restatement rule.

I checked the conversion for hidden strengthening/weakening:

* It is a plain structure literal assigning **all ten** fields by `w.<field>` with
  no coercion and no proof step: `velocity`, `pressure`, `horizon_pos`,
  `velocity_smooth`, `pressure_smooth`, `initial`, `divergence`, `momentum`,
  `sobolev`, `pressure_gradient`. Every field type is therefore defeq, and
  `(uniqueness_toA02 w).velocity` reduces to `w.velocity` (recorded as an
  `example := rfl` at `Bindings/Uniqueness.lean:78-79`).
* **Horizon guards.** Contract: `∀ t ∈ Ico (0 : ℝ) T`. Theorem
  (`VelocityJets.lean:67`): `(ht : t ∈ Ico (0 : ℝ) T)`. Identical — no
  `Ico`/`Ioo` substitution. (`Ioo` appears only inside
  `ClassicalSolutionR.momentum`, on both sides equally.)
* **Quantifier order.** The binding is
  `fun _ _ _ _ _ _ _ w _ ht => …`: ten binders matching `ν, hν, a, ha, f, hf, T,
  w, t, ht` in the contract's order, with `w` and `ht` used and the rest
  discarded. The implementation legitimately does not need `0 < ν`,
  `a ∈ initialClassR` or `MemForceR f` — those are *hypotheses*, so ignoring them
  means the contract claims less than is true, never more. That matches
  `Spec.lean` exactly and is not a defect.
* **`ℝ≥0∞` vs `ℝ`.** `velocityJets` contains no norm; nothing to confuse. Across
  the whole contract the split is the one the docstring promises: `l2Sq`,
  `l2Norm`, `laplacianSq`, `advectionWork` real; `criticalL3` and every `eLpNorm`
  in `ℝ≥0∞`; `.toReal` appears nowhere.
* **Conclusion match.** `MemHInfty (slice w.velocity t)` vs
  `A02.MemHInfty (fun x => u.velocity (t, x))`: `slice` unfolds to the lambda by
  definition and the two `MemHInfty`s are token-identical (finding 5).
  `SmoothSquareIntegrableJets` vs `A05.SmoothL2` is bridged.

`C₁` is bound to the **registered** `A05.gradient_l6` constant —
`C₁ := gradientL6.Csix` where `gradientL6` is `Bindings.gradientL6`
(`Bindings/GradientL6.lean:43`, `Csix := A05.gradientL6Const`), and
`C₁_pos := gradientL6.Csix_pos` (`A05.gradientL6Const_pos`). Confirmed: the
binding reuses the registered contract's constant rather than reaching past it
into the implementation.

---

## 4. Scope honesty

`EnergyAbsorptionAPI` has **23** fields. I enumerated them programmatically and
partitioned against the registry `scope`:

* **Included (7):** `C₁`, `C₁_pos`, `velocityJets`, `forceTimeRegularity`,
  `trilinearHolder`, `trilinearAbsorbed`, `laplacianSqENorm`.
* **Excluded (16):** `gradientL6`, `CRH1`, `CRH1_pos`, `CH2`, `CH2_pos`,
  `Cassembly`, `Cassembly_pos`, `energyIdentity`, `energyDifferentialBound`,
  `l2Bound`, `enstrophyIdentity`, `enstrophyDifferentialBound`,
  `enstrophyIntegralBound`, `sobolevTwoFourier`, `h2TimeIntegral`,
  `h2TimeIntegralZeroDatum`.

The `scope` string names every one of the 16, with a reason, and names the
discharging theorem for every one of the 7. **The partition is exact: nothing
proved is omitted, nothing unproved is included.**

Exclusion verified independently, not taken on trust: I grepped
`formalization/NSFormalization/Section4/` for all nine excluded *propositional*
field names. Every hit is a docstring in `Section4/C01/Evolution.lean:10-11` and
`Section4/A04/*` (a different task's `energyIdentityHigh`); there is **no
theorem** named or stating any of them. The full theorem inventory of
`Section4/C01/` is 18 declarations across `VelocityJets`, `ForceSlices`,
`Trilinear`, `Evolution` — none of which is an excluded field. The registry's
claim that they "live in `Evolution.lean` only as the draft's PDE displays" is
accurate.

Line-range citations in the `scope` and docstring all check out:
`Spec.lean:344-387` (`energyIdentity` :344, `energyDifferentialBound` :364,
`l2Bound` :383-387), `:487-541` (enstrophy :487/:510/:532-541), `:555-558`,
`:576-607` (`h2TimeIntegral` :576, `h2TimeIntegralZeroDatum` :599-607), and all
six `def` line numbers `167,172,177,191,212,202`. The only bad citation is
finding 1.

`collaboration/work_items.json` records the registration exactly as lane 071 did
for B01 — the `C01` item's `contracts` array goes from `[]` to
`["C01.energy_absorption_partial"]`, nothing else changed — and
`collaboration/TASKS.md` / `tasks/C01.md` are the corresponding `tasks.py render`
output. `check_work_queue.py` confirms consistency across all 30 items.

---

## 5. Consistency and policy

* **Contract imports.** `Contracts.V1.Data`, `Contracts.V1.GradientL6` — both
  under the `Contracts.` prefix of `CONTRACT_IMPORT_PREFIXES`. **No use of the
  `CONTRACT_CANONICAL_MODULES` whitelist**, so lane 009's temporary policy
  relaxation is not extended here. Clean.
* **No duplicate restatement.** `gradientTensor`, `laplacian`, `lift`,
  `SmoothSquareIntegrableJets` are opened from the registered
  `Contracts.V1.GradientL6`, not restated — check 4 satisfied. One observation
  for the future: `Contracts/V1/Packet.lean:150` defines
  `BlowupDensity.Contracts.V1.l2Sq (u : VelocityField) (t : ℝ)`, which is this
  contract's `l2Sq ∘ slice` unfolded. It is a different arity in a different
  namespace, `Packet` is not imported here, and `Spec.lean` defines the slice
  form — so restating is the fidelity-correct choice, not a violation. Worth
  knowing that the contract's **selective** `open BlowupDensity.Contracts.V1
  (lift gradientTensor laplacian SmoothSquareIntegrableJets)` is what keeps
  `l2Sq` unambiguous; a future V2 must not widen it to an unselective `open`.
* **Namespace.** `BlowupDensity.Contracts.V1.EnergyAbsorptionPartial`, matching
  the `BochnerPartial` / `TameProduct` convention (and deliberately *not* the flat
  `BlowupDensity.Contracts.V1` that `GradientL6`/`Packet` use).
* **Tests module.** Byte-for-byte the shape of `Tests/BochnerPartial.lean`: same
  three imports, same `noncomputable section` / `namespace BlowupDensity.Tests`,
  one `def checked… := Bindings.…`, one `run_cmd TestSupport.checkAxioms`. ✓
* **`warningAsError = true`** (`verification/lakefile.toml`, `Tests` lib) is
  respected — the build emitted **zero** diagnostics from any of the three new
  files; every warning in the log comes from `NSFormalization/{Source,Paper3}/*`
  and `NavierStokes/*` in the dependency package.
* **No `Formal.*` import.** The registered closure of
  `C01.energy_absorption_partial` is 1202 modules and contains no
  `Formal.*` module (HeliCorgi is not reachable).
* **No forbidden tokens.** `grep` over the three new files for
  `sorry|admit|axiom |native_decide|set_option|maxHeartbeats` → nothing.
* **Binding contains no proof content.** Five field assignments, two constant
  assignments, six `rfl` correspondence theorems. No tactic block anywhere.

---

## 6. Commands and results

From the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`, lake
from `verification/`, one lake process at a time.

### 6.1 `cd verification && lake build Tests.EnergyAbsorptionPartial`

```
ℹ [9966/9966] Replayed Tests.EnergyAbsorptionPartial
info: Tests/EnergyAbsorptionPartial.lean:15:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartial: checked; standard logical axioms only
Build completed successfully (9966 jobs).
```

### 6.2 `make check` → exit 0

```
python3 experiments/check_formalization_plan.py --check   -> task_count 30; the only
    sorry token in the copied umbrella closure is the pre-existing
    Paper1/BoundaryCorollary.lean:90
python3 experiments/check_contracts.py                    -> "registered_contracts": 16,
    "Tests.EnergyAbsorptionPartial" present in the checked module set
python3 experiments/test_contract_policy.py               -> Ran 13 tests ... OK
python3 experiments/check_work_queue.py                   -> 30 work items: ownership,
    contract registration and task cards consistent.
```

### 6.3 `make test` → exit 0

Full replay; **16** `checked; standard logical axioms only` lines, one per
registered contract, including

```
info: Tests/EnergyAbsorptionPartial.lean:15:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartial: checked; standard logical axioms only
```

### 6.4 `make test-mutations` → exit 0

```
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

### 6.5 `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` → exit 0

```
registered_contracts 16
base_compatibility_checked True
```

No stable specification removed or changed; `contracts.json` gains exactly one
entry. (Base drift exists in non-contract files — finding 7.)

### 6.6 `bash scripts/gates.sh Tests.EnergyAbsorptionPartial` → exit 0

```
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
== gates OK
```

### 6.7 Fidelity diff (mechanical)

Python extraction of the seven field types from both files, whitespace
normalized, compared as strings:

```
### C₁ IDENTICAL
### C₁_pos IDENTICAL
### velocityJets IDENTICAL
### forceTimeRegularity IDENTICAL
### trilinearHolder IDENTICAL
### trilinearAbsorbed IDENTICAL
### laplacianSqENorm IDENTICAL
```

Field-set partition of `EnergyAbsorptionAPI` (23 fields), computed from
`Spec.lean` and compared against the registry `scope`: 7 included / 16 excluded,
matching exactly.

Excluded-field grep over `formalization/NSFormalization/Section4/`: no theorem
states any excluded field; all hits are docstrings.

Import-closure check: `LerayLowering in closure: False`; no `Formal.*` module in
the 1202-module closure.
