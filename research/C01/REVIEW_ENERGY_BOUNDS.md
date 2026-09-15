# REVIEW — lane 154-C01-v3-bounds (rows `energyDifferentialBound` + `l2Bound` = eq:RL2)

Reviewer run 2026-09-14, worktree `.claude/worktrees/154-C01-v3-bounds`, branch
`erenup/154-C01-v3-bounds`, HEAD `ace32a3` (unchanged).  Read-only: no Lean edited, no git
state touched.  New probes: `research/C01/probes/rev154_{mut_A_constant,mut_B_budget,
mut_C_icc,icc_false,t0_nonvacuous,positivity_note,v3_binding_dryrun}.lean`.

## Verdict: **ACCEPT**

Both deliverables are token-equivalent to `research/C01/Spec.lean:364-370` and `:383-387`
modulo the expected binder style and two deliberately-omitted slack hypotheses; all eleven
declarations carry exactly `[propext, Classical.choice, Quot.sound]`; the module emits **zero**
warnings of its own; the generalized scalar lemma is a faithful weakening of
`Paper1.sqrt_energy_le_primitive` with a correct endpoint step; three mutations break at exactly
the expected place, and the `Ico → Icc` mutation is additionally proved **false** (not merely
unprovable) by a counterexample built with `A02.ClassicalSolutionR.congr`.  A dry run of the
planned V3 binding compiles, confirming the V3 lane needs exactly one bridge (V2's).
Four notes, none blocking.

---

## 1. What the lane claims

`research/C01/ENERGY_SPLIT.md` rows **`energyDifferentialBound`** (`:364`) and **`l2Bound`**
(`:383`), both marked DONE by this lane, delivered in one new module
`formalization/NSFormalization/Section4/C01/EnergyBounds.lean` (316 lines, 11 declarations,
namespace `NSFormalization.Section4.C01`):

* the Cauchy–Schwarz form of the ordinary energy identity,
  `(‖u(t)‖₂²)' + 2ν‖∇u(t)‖₂² ≤ 2‖f(t)‖₂‖u(t)‖₂`, at every interior time, for **any** real `E'`
  that is the derivative there;
* **eq:RL2**, `‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀ᵗ‖f(s)‖₂ ds = energyBudget a f t`, at every presingular
  time `t ∈ Ico 0 T`, obtained through a generalization `sqrt_energy_le_primitive'` of
  `Paper1.sqrt_energy_le_primitive` (`Paper1/ScalarEnergy.lean:22`) whose
  `E 0 = 0 ∧ N 0 = 0` is replaced by `√(E 0) ≤ N 0`;
* plus the analytic inputs: `velocityL2{Norm,Sq}_continuousOn` (energy continuity on `[0,T)`,
  endpoint `0` included) and the carrier-B Cauchy–Schwarz `pairing_le_l2Norm_mul`;
* and a V3-contract plan in `research/C01/ATTEMPTS_ENERGY_BOUNDS.md:56-74`.

## 2. What is in Lean

### 2.1 `energyDifferentialBound` — statement fidelity

`EnergyBounds.lean:133-137` vs `research/C01/Spec.lean:364-370`.  Conclusion is
**character-for-character** the spec's:
`E' + 2 * ν * gradientSq (slice w.velocity t) ≤ 2 * l2Norm (slice f t) * l2Norm (slice w.velocity t)`,
with the same `∀ E' : ℝ, HasDerivAt (fun s => l2Sq (slice w.velocity s)) E' t →` premise
(`:134-135` vs `:368`) and the same interior guard `t ∈ Ioo (0 : ℝ) T` (`:134` vs `:367`).

Binder diff (the only one): the spec's `∀ (ν : ℝ), 0 < ν → ∀ a, a ∈ initialClassR → ∀ f,
MemForceR f → ∀ (T) (w), …` chain becomes the section variables `{ν} {a} {f} {T}`
(`EnergyBounds.lean:57`, implicit) plus explicit `(w) (hf : MemForceR f)`, with **`0 < ν` and
`a ∈ initialClassR` dropped** (unused — the theorem is strictly stronger, exactly the slack
that `Contracts/V2/EnergyAbsorptionPartial.lean:52-54` already discloses for `energyIdentity`).

Proof (`:138-148`), verified step by step:
* `hid := energyIdentity_l2Sq w hf ht` (`Section4/C01/EnergySpec.lean:58-63`);
* `hE' := hderiv.unique hid` pins `E' = −2ν·gradientSq + 2·pairing`.  The ascription to the
  local `gradientSq` typechecks by defeq; the mutation-A error dump (§5) shows `hid`'s value
  verbatim as `(-2 * ν * ∫ (x : Space), ∑ i, ‖(fderiv ℝ (slice w.velocity t) x) (coordinateVector i)‖ ^ 2) + 2 * pairing …`,
  i.e. **the raw-integral form**, confirming the identification is not a coincidence of names;
* `hkey` cancels `±2ν·gradientSq` by `ring`;
* `hcs := pairing_le_l2Norm_mul …` (`:109-120`) is genuine `L²` Cauchy–Schwarz:
  `pairing_eq_inner` (`Vocabulary.lean:147`) rewrites `pairing` to `⟪·.toLp, ·.toLp⟫`,
  `real_inner_le_norm` bounds it, and `l2Norm_eq_norm_toLp_{velocity,force}` (`:92-105`) are
  `norm_toLp_sq_eq_l2Sq` (`Vocabulary.lean:107`) + `Real.sqrt_sq`.  The `Ioo → Ico` widening
  for `velocitySliceField` is `Ioo_subset_Ico_self` and `0 ≤ t` is `ht.1.le` — both honest.

**`gradientSq` here is the raw-integral form** (`EnergyBounds.lean:65-66`,
`∫ x, ∑ i, ‖fderiv ℝ z x (coordinateVector i)‖ ^ 2`), **not** the spec's tensor form
(`Spec.lean:185`, `∫ x, ‖gradientTensor z x‖ ^ 2`).  The module header (`:32-41`) and the def
docstring (`:61-64`) both say so explicitly and name the bridge.  It is the only `gradientSq`
in `formalization/` (grep: `EnergyBounds.lean:65` is the sole hit), so no shadowing.

### 2.2 `l2Bound` (eq:RL2) — statement fidelity

`EnergyBounds.lean:239-241` vs `Spec.lean:383-387`: conclusion
`l2Norm (slice w.velocity t) ≤ energyBudget a f t` and window `t ∈ Ico (0 : ℝ) T`, both
character-for-character.  Binder diff as above, plus `(hν : 0 < ν)` **kept** (used, see note 2);
`a ∈ initialClassR` dropped.

The two new spec-local `def`s are token-for-token the spec's, modulo the deliberate `A02.`
qualification of the type names (`logs/LESSONS.md`, the 152 entry):

| spec | lane |
|---|---|
| `Spec.lean:218-219` `def forcePrimitive (f : SpaceTimeField) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, l2Norm (slice f s)` | `EnergyBounds.lean:69-70`, identical body |
| `Spec.lean:224-225` `def energyBudget (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : ℝ := l2Norm a + forcePrimitive f t` | `EnergyBounds.lean:73-74`, identical body |

Both bind by `rfl` — **proved**, not asserted: `rev154_v3_binding_dryrun.lean:30-33`
(`forcePrimitiveC = …C01.forcePrimitive := rfl`, `energyBudgetC = …C01.energyBudget := rfl`).

### 2.3 `sqrt_energy_le_primitive'` (`:179-225`) — the generalization

Hypotheses are `Paper1.sqrt_energy_le_primitive`'s (`ScalarEnergy.lean:22-31`) with
`hE0 : E 0 = 0`, `hN0 : N 0 = 0` replaced by the single `hEN0 : Real.sqrt (E 0) ≤ N 0`.  Since
`E 0 = 0 ∧ N 0 = 0 ⟹ √(E 0) = 0 = N 0`, this is a genuine weakening: every consumer of the
frozen lemma is still served.  The body is the frozen proof verbatim (regularized
`G x = √(E x + δ²) − N x`, `antitoneOn_of_hasDerivWithinAt_nonpos`, `δ ↓ 0` through
`le_of_forall_pos_le_add`) with only the endpoint changed:

* `hN0nn : 0 ≤ N 0` from `Real.sqrt_nonneg` + `hEN0` (`:213`);
* `hsq : E 0 ≤ N 0 ^ 2` from `Real.sq_sqrt hE0nn` + `hEN0` (`:214-215`);
* `hG0 : G 0 ≤ δ` by comparing squares, `E 0 + δ² ≤ N 0² + 2·N 0·δ + δ² = (N 0 + δ)²`
  (`:216-221`).  Correct: the extra `2·N 0·δ ≥ 0` is exactly `mul_nonneg hN0nn hδ.le`.

The monotonicity direction, the integrability of `b` and the `HasDerivAt` on `Ioo` are
untouched, so the analytic content is the frozen one.

### 2.4 The four analytic inputs of `l2Bound`

* **Energy continuity on `[0,t]`, endpoint included.**  `velocityL2Norm_continuousOn`
  (`:155-164`) takes `w.sobolev 0` (`A02/SolutionClass.lean:133-135`), whose datum path is
  `ContinuousOn G (Ico (0 : ℝ) T)` — `Ico`, so **genuinely through `t = 0`** (within-set
  continuity at `0`, which is exactly what `ContinuousOn E (Icc 0 S)` and
  `antitoneOn_of_hasDerivWithinAt_nonpos` consume).  It is the exact velocity analogue of
  `ForceSlices.forceTimeRegularity`'s second conjunct (`ForceSlices.lean:158-181`): same
  `continuous_jetOfDatum_zero` (`ForceSlices.lean:94`) ∘ `l2Norm_eq_norm_jetOfDatum`
  (`:112`), with `D01.contDiff_slice` (`D01/DatumToJets.lean:366`) in place of
  `contDiff_slice_future`.  The `((0 : ℕ) : ℝ)` order is carried uniformly, so no
  `Nat.cast_zero` transport is needed (the `logs/LESSONS.md` 124 trap is avoided).
  `velocityL2Sq_continuousOn` (`:167-170`) squares it via `l2Sq_eq_sq_l2Norm`.
* **Integrability of `s ↦ ‖f(s)‖₂` on `[0,t]`.**  Not from `MemLp G 1 forceTimeMeasure`, but
  from the *continuity* conjunct of `forceTimeRegularity` (`ForceSlices.lean:158`, the
  registered V1 contract field): `EnergyBounds.lean:242-243, 251-252`
  (`(hg_cont.mono …).integrableOn_Icc` after `uIcc_of_le`).  Cleaner and stronger; correct.
* **FTC derivative of the budget on `(0,t)`.**  `:268-282`,
  `intervalIntegral.integral_hasDerivAt_right` fed `IntervalIntegrable`, a
  `StronglyMeasurableAtFilter` built on `Ioi 0 ∈ 𝓝 s` (uses `0 < s`, available on `Ioo 0 t`),
  and `ContinuousAt` from `hg_cont.continuousAt` — all from the same continuity fact.
  `.const_add (l2Norm a)` lands on `energyBudget a f`.
* **Endpoint `√(E 0) = ‖a‖₂ = energyBudget a f 0`** (`:258-266`): `slice w.velocity 0 = a` by
  `funext w.initial` (`A02/SolutionClass.lean:126`), `forcePrimitive f 0 = 0` by
  `intervalIntegral.integral_same`, then `le_of_eq rfl`.  **Equality**, as claimed.

**`t = 0` is handled** (and `Ico` includes it): the lemma is applied with `S = t`, so at `t = 0`
we get `Ioo 0 0 = ∅` (all three differential hypotheses vacuous) and
`key 0 ⟨le_rfl, le_rfl⟩ = hEN0`.  Verified by instantiation:
`rev154_t0_nonvacuous.lean` typechecks `l2Bound … (0 ∈ Ico 0 2)` on `A04.zeroSol 1 2`.

* **Dissipation discarded** (`:284-303`): `hdiss : 0 ≤ 2*ν*gradientSq` from
  `mul_nonneg (mul_nonneg (by norm_num) hν.le) (gradientSq_nonneg _)`, then
  `le_trans (le_add_of_nonneg_right hdiss) hbound`.  `hν` is used **honestly** (there is no
  other route to the sign of `ν`), though only through `hν.le` — see note 2.
  Line `:303` `2 * ‖f‖₂ * l2Norm u = 2 * ‖f‖₂ * √(l2Sq u) := rfl` is correct by `l2Norm`'s def.

## 3. Mathematics — is this the paper's statement?

* **eq:RL2** is `paper/sections/04-whole-space.tex:118-120`, display at `:119`:
  `‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀ᵗ‖f(s)‖₂ ds =: K(t)`.  `l2Bound` is exactly that: **no smallness
  hypothesis, no absorption, no `C₁`/`ν`-threshold**, and the right-hand side is `K(t)` spelled
  `energyBudget a f t`.  This is the *ordinary* estimate the manuscript deliberately keeps
  separate from eq:RH1 (`:117` "It does not control low frequencies by itself", `:132` "The low
  frequencies have been controlled directly by the ordinary energy estimate").  ✔
* **The differential bound.**  The manuscript's §4 does not display it; it is the doubled form
  of `paper/sections/02-preliminaries.tex:138-139`
  (`½(‖U(t)‖₂²)' + ν‖∇U(t)‖₂² = ⟨F(t), U(t)⟩`) after Cauchy–Schwarz — precisely what `:141-142`
  then writes as `½(‖U‖₂²)' ≤ ‖F‖₂‖U‖₂` when dissipation is dropped.  Doubling:
  `(‖u‖₂²)' + 2ν‖∇u‖₂² ≤ 2‖f‖₂‖u‖₂`.  ✔  The regularized-division route
  (`04-whole-space.tex:117` "with regularized norm division"; `:100-103` for the `ζ ↓ 0`
  template, including "times at which `y=0`") is the one implemented, and the `δ`-regularized
  `√(E + δ²)` argument does cover `‖u(t)‖₂ = 0`.  ✔
* Orientation of the pairing (`pairing u f`, budget `‖f‖·‖u‖`) matches the registered V2 field
  `energyIdentity` (`Contracts/V2/EnergyAbsorptionPartial.lean:128-130`).  ✔

## 4. Hygiene and consistency

* `grep -n 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option' EnergyBounds.lean`
  → **no match**.
* No `Formal.*` import; the module sits under `Section4/C01`, imports only
  `Section4.C01.EnergySpec` and `Paper1.ScalarEnergy`.  No `Paper1/` edit (`git diff --stat`
  shows 4 files, none under `Paper1/` or `Contracts/V1/`).
* No duplicated restatement: `grep -rn 'def gradientSq\|def energyBudget\|def forcePrimitive\|
  def pairing\|def l2Norm\|def l2Sq\|def slice'` over `formalization/`, `verification/Contracts/`
  and `Spec.lean` shows `forcePrimitive`/`energyBudget` are **new** on the tree side and
  `gradientSq` is the tree's only copy; `slice`/`l2Sq`/`l2Norm` are imported from
  `ForceSlices.lean:80-86`, `pairing` from `EnergySpec.lean:46`, not re-declared.
* Citations opened and checked at the cited lines: `Paper1/ScalarEnergy.lean:22` ✔,
  `Spec.lean:364-370` / `:383-387` ✔, `Spec.lean:185,218-225` ✔,
  `ForceSlices.lean:94,112,158` ✔, `Vocabulary.lean:107,147` ✔,
  `A02/SolutionClass.lean:126,133-135` ✔, `A04/ZeroSolution.lean:70,91` ✔,
  `04-whole-space.tex:117-121` ✔ (display `:119`), `02-preliminaries.tex:136-139` ✔.
* ATTEMPTS honesty: the "`positivity` fails without `hs`" bullet
  (`ATTEMPTS_ENERGY_BOUNDS.md:42-46`) is **true** — `rev154_positivity_note.lean` reproduces
  `failed to prove strict positivity` without the hypothesis and succeeds with it.

## 5. Negative checks

All three mutations keep the proof script and change only the statement (no
"drop-an-argument" pseudo-check; `formalization/` has `autoImplicit` on, so statement-level
mutations of *constants* and *windows* are the safe form here).

| probe | mutation | result |
|---|---|---|
| `rev154_mut_A_constant.lean` | Cauchy–Schwarz constant `2 → 1` on the RHS of `energyDifferentialBound` (and in the matching `hassoc`, so the failure lands on the arithmetic, not on `rw`) | **breaks**: `:37:2: error: linarith failed to find a contradiction`, residual goal `1 * (l2Norm (slice f t) * l2Norm (slice w.velocity t)) < 2 * pairing (slice w.velocity t) (slice f t) ⊢ False` |
| `rev154_mut_B_budget.lean` | drop `∫₀ᵗ‖f‖₂` from the budget (`energyBudgetM a f t = l2Norm a`), `l2Bound` proof verbatim | **breaks** at the FTC step: `:60:4: Type mismatch … has type HasDerivAt (fun x => l2Norm a + ∫ r in 0..x, l2Norm (slice f r)) (l2Norm (slice f s)) s but is expected to have type HasDerivAt (energyBudgetM a f) (l2Norm (slice f s)) s`.  A constant budget cannot have derivative `‖f(s)‖₂`, which is exactly `b` in `sqrt_energy_le_primitive'` |
| `rev154_mut_C_icc.lean` | `Ico 0 T → Icc 0 T` in `l2Bound` | **breaks** in all three places that need the strict guard: `:29:43`, `:67:57`, `:84:63` — `ht.right has type t ≤ T but is expected to have type t < T` |

**Hardened check.**  `rev154_icc_false.lean` proves the `Icc` mutation is not merely unprovable
but **false** (`theorem l2Bound_Icc_false`, compiles clean): `A02.ClassicalSolutionR.congr`
(`A02/Restrict.lean:175-198`) turns `A04.zeroSol 1 2` into a solution whose velocity is
`bumpField` (indicator of the unit ball, valued in a unit vector, `l2Sq > 0` via
`integral_indicator_const` + `Metric.measure_ball_pos`) at `t = T = 2` while agreeing with `0`
on the whole slab `[0,2) × R³`; the mutated statement would then force
`Real.sqrt (l2Sq bumpField) ≤ energyBudget 0 0 2 = 0`.  So the `Ico` window in `Spec.lean:386`
is load-bearing, not a convenience.

**Nonzero instance.**  There is none.  The only concrete `ClassicalSolutionR` constructor in
the tree is `A04.zeroSol` (`Section4/A04/ZeroSolution.lean:91`); every other `def` producing
one (`restrict`, `congr`, `normalizePressure` in `A02/Restrict.lean`) transforms an existing
solution.  The counterexample above is the nearest thing — nonzero, but only *off* the
lifespan.  So non-vacuity rests on `zeroSol` (`axioms_energy_bounds.lean:47-54`, both examples
typecheck) and the load-bearingness of the constants on mutations A and B.

## 6. V3 plan — confirmed, and dry-run compiled

`ATTEMPTS_ENERGY_BOUNDS.md:56-74` is correct and I verified it end-to-end rather than by
reading: `rev154_v3_binding_dryrun.lean` states the two prospective V3 fields **in the
contract's vocabulary**, token-for-token from `Spec.lean:364-370` and `:383-387`, and
discharges them.  Result: **compiles, zero output.**

* `l2Bound` binds with **no bridge at all**:
  `fun _ hν _ _ _ hf _ w _ ht => …C01.l2Bound (uniqueness_toA02 w) hf hν ht`.
* `energyDifferentialBound` binds with **exactly one** `rw`, the already-existing V2 bridge
  `Bindings.energyAbsorptionPartialV2_gradientSq_eq`
  (`verification/Bindings/EnergyAbsorptionPartialV2.lean:70-75`).  No other gap.
* `forcePrimitive`/`energyBudget` bridges are `rfl`.

Files the V3 lane must add (the lakefile globs `Contracts.+`/`Bindings.+`/`Tests.+`, so no
build-file edit):

1. `verification/Contracts/V3/EnergyAbsorptionPartial.lean` — `EnergyAbsorptionPartialV3API
   extends Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API` + the two fields
   token-for-token from `Spec.lean:364-370` and `:383-387`, + the two new spec-local `def`s
   `forcePrimitive` (`Spec.lean:218-219`) and `energyBudget` (`:224-225`).  `slice`/`l2Sq`/
   `l2Norm` come from `Contracts.V1.EnergyAbsorptionPartial`, `gradientSq`/`pairing` from
   `Contracts.V2.EnergyAbsorptionPartial` — **do not re-declare them**, and in particular the
   contract's `gradientSq` must stay the `gradientTensor` form, not a copy of the tree's
   raw-integral one.
2. `verification/Bindings/EnergyAbsorptionPartialV3.lean` — `energyAbsorptionPartialV3 :=
   { energyAbsorptionPartialV2 with energyDifferentialBound := …, l2Bound := … }` (bodies as in
   the dry run), the compatibility `theorem energyAbsorptionPartialV3.toEnergyAbsorptionPartialV2API
   = energyAbsorptionPartialV2 := rfl`, and the two new per-definition `rfl` bridges
   `…V3_forcePrimitive_eq` / `…V3_energyBudget_eq` (CLAUDE.md's "每个重写的定义都要有桥").
3. `verification/Tests/EnergyAbsorptionPartialV3.lean` — `checkedEnergyAbsorptionPartialV3`,
   `run_cmd TestSupport.checkAxioms`, plus one `example` per new field in the manuscript's
   shape (the V2 test's pattern).
4. `verification/contracts.json` — a `C01.energy_absorption_partial_v3` entry
   (`version: 3`, `binding_module`/`test_module`/`declaration`/`scope`); write with
   `ensure_ascii=False, indent=2` (`logs/LESSONS.md`, 141).
5. `collaboration/work_items.json` + `python3 experiments/tasks.py render` (regenerates
   `collaboration/tasks/C01.md` and `collaboration/TASKS.md`).

No new `formalization/` file is needed.

## 7. Notes (none blocking)

1. **(doc)** The V3 contract docstring for `energyDifferentialBound` should cite
   `02-preliminaries.tex:136-142` alongside `04-whole-space.tex:117-121`, as
   `Contracts/V2/EnergyAbsorptionPartial.lean:110-112` does for `energyIdentity`: the
   inequality `(‖u‖₂²)' + 2ν‖∇u‖₂² ≤ 2‖f‖₂‖u‖₂` has no §4 display, it is the doubled §2 one.
2. **(scope disclosure)** In `l2Bound`, `0 < ν` is consumed only as `hν.le`
   (`EnergyBounds.lean:295`); `0 ≤ ν` would suffice.  Worth one line in the V3 contract's
   "scope disclosures", next to the existing `a ∈ initialClassR` slack note.
3. **(simplifier lane)** `sqrt_energy_le_primitive'` (`:179-225`) duplicates ~45 lines of
   `Paper1.sqrt_energy_le_primitive` (`ScalarEnergy.lean:22-66`).  Since the new one is
   strictly more general, a later SIMP lane could make the `Paper1` statement a two-line
   corollary of it (moved down, or re-exported) instead of keeping two copies.  Not for this
   lane — it would touch a module outside C01.
4. **(naming)** `NSFormalization.Section4.C01.gradientSq` carries the spec's *name* but the
   raw-integral *body*.  Header and docstring say so, and there is no second `gradientSq` in
   `formalization/`, so nothing is ambiguous today; but any future consumer must not assume a
   `rfl` bridge to `Contracts.*.gradientSq`.

## 8. Commands and results

All from the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` from
`verification/`.

```
$ cd verification && lake build NSFormalization.Section4.C01.EnergyBounds
Build completed successfully (10306 jobs).            # EXIT=0
# warnings: only vendor HeliCorgi replays; grep for "EnergyBounds" in the build log → no hit

$ cd verification && lake env lean ../formalization/NSFormalization/Section4/C01/EnergyBounds.lean
# EXIT=0, 0 bytes of output

$ cd verification && lake env lean ../research/C01/axioms_energy_bounds.lean      # EXIT=0
'NSFormalization.Section4.C01.l2Sq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.gradientSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.l2Sq_eq_sq_l2Norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.l2Norm_eq_norm_toLp_velocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.l2Norm_eq_norm_toLp_force' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.pairing_le_l2Norm_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.energyDifferentialBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.velocityL2Norm_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.velocityL2Sq_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.sqrt_energy_le_primitive'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.l2Bound' depends on axioms: [propext, Classical.choice, Quot.sound]
# 11/11 standard; both `A04.zeroSol` non-vacuity examples typecheck (no error emitted)

$ make check                                                                      # EXIT=0
python3 experiments/check_formalization_plan.py --check   → ok
python3 experiments/check_contracts.py                    → ok
python3 experiments/test_contract_policy.py               → Ran 13 tests … OK
python3 experiments/check_work_queue.py                   → 30 work items: ownership, contract registration and task cards consistent.

$ cd verification && lake -d . test                                               # EXIT=0
… Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV2: checked; standard logical axioms only

$ cd verification && lake env lean ../research/C01/probes/rev154_mut_A_constant.lean     # EXIT=1 (expected)
../research/C01/probes/rev154_mut_A_constant.lean:37:2: error: linarith failed to find a contradiction
…
a✝ : 1 * (l2Norm (slice f t) * l2Norm (slice w.velocity t)) < 2 * pairing (slice w.velocity t) (slice f t)
⊢ False

$ cd verification && lake env lean ../research/C01/probes/rev154_mut_B_budget.lean       # EXIT=1 (expected)
../research/C01/probes/rev154_mut_B_budget.lean:60:4: error: Type mismatch
  HasDerivAt.const_add (l2Norm a) hprim
has type
  HasDerivAt (fun x => l2Norm a + ∫ (r : ℝ) in 0..x, l2Norm (slice f r)) (l2Norm (slice f s)) s
but is expected to have type
  HasDerivAt (energyBudgetM a f) (l2Norm (slice f s)) s

$ cd verification && lake env lean ../research/C01/probes/rev154_mut_C_icc.lean          # EXIT=1 (expected)
:29:43, :67:57, :84:63 — Application type mismatch: ht.right has type t ≤ T but is expected to have type t < T

$ cd verification && lake env lean ../research/C01/probes/rev154_icc_false.lean          # EXIT=0
# `l2Bound_Icc_false` compiles: the Icc mutation is FALSE (2 deprecation warnings for if_pos/if_neg)

$ cd verification && lake env lean ../research/C01/probes/rev154_t0_nonvacuous.lean      # EXIT=0
# `l2Bound … (0 ∈ Ico 0 2)` on A04.zeroSol typechecks: the t = 0 endpoint is covered

$ cd verification && lake env lean ../research/C01/probes/rev154_positivity_note.lean    # EXIT=1 (expected)
:5:70: error: failed to prove strict positivity, but it would be possible to prove nonnegativity if desired
# line 6 (same goal with `hs` in context) succeeds → the ATTEMPTS bullet is accurate

$ cd verification && lake env lean ../research/C01/probes/rev154_v3_binding_dryrun.lean  # EXIT=0
# both prospective V3 fields discharged; forcePrimitive/energyBudget `rfl`; one V2 bridge for the gradient term
```
