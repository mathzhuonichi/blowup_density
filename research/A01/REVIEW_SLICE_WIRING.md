# REVIEW — lane 157 (`157-A01-slice-wiring`): wiring `Z` / `hfin` / `hslice` to a real `ClassicalSolutionR`

Reviewer: opus, read-only, worktree `.claude/worktrees/157-A01-slice-wiring`, branch
`erenup/157-A01-slice-wiring`, HEAD `90029bb`. No edits to lane files, no git state changes. New
files written by the reviewer: this report and
`research/A01/probes/rev157_{fidelity,sigs,mut1_hslice,mut2_const,mut3_horizon,constructor_loop,supply_side}.lean`.

## Verdict: **ACCEPT-WITH-NOTES**

All six declarations are what they claim to be, the build and all ten `#print axioms` are clean,
three substantive mutations fail as expected, and the claimed reduction of row (i) to a single
constructor is real — I closed the loop in Lean (`rev157_constructor_loop.lean`): assuming the named
constructor as an ordinary hypothesis, `HasAprioriBound` yields a cylinder pair **and** a genuine
`ClassicalSolutionR` with both a-priori rows and `‖u‖ ≤ R`, 3-axiom. The notes are all record-level;
**none requires a change to `SliceWiring.lean`**, but N1 and N2 are honesty corrections that should be
applied to the module header / ATTEMPTS / `A3_SPLIT.md` before the next lane reads them.

---

## 1. What the lane claims

Residual rows #1–#3 of `research/A01/REVIEW_L2_DESCENT.md` §3: supply the smooth jet carrier `Z` and
its finiteness `hfin` from a genuine `ClassicalSolutionR` (#1, #2, both graded **S**), state the
row-(ii) converse on the real solution with only the a.e. carrier hand-off `hslice` left, and package
both a-priori rows so that row (i) becomes a single named existence statement (#3, graded **M–L**).

## 2. What is in Lean now

New file `formalization/NSFormalization/Section4/A01/SliceWiring.lean` (189 lines, 1 `def` +
5 theorems, no `sorry/admit/axiom/native_decide/maxHeartbeats/set_option`, all six `#print axioms`
standard three). Checked declaration by declaration.

### 2.1 `velocitySliceSmoothL2` / `_field` (`SliceWiring.lean:105-118`) — reuse, verified by `rfl` ✅

`velocitySliceSmoothL2 w t hST := C01.velocityField w hST t`. I did **not** take the "reuse, not
duplication" claim on inspection: `rev157_fidelity.carrier_is_velocityField` states
`velocitySliceSmoothL2 w t hST = C01.velocityField w hST t` and closes it by `rfl` (3-axiom). And
`C01.velocityField` (`Section4/C01/Evolution.lean:115-119`) is

```
def velocityField (u : A02.ClassicalSolutionR ν a f T) (hST : S < T) (t : Icc (0:ℝ) S) :
    SmoothL2Field Space where
  field := fun x => u.velocity (t.1, x)
  smooth := (velocity_slice_smoothL2 u (mem_Ico_of_mem_Icc hST t.2)).1
  integrable := (velocity_slice_smoothL2 u (mem_Ico_of_mem_Icc hST t.2)).2
```

so the `field` is literally `fun x => u.velocity (t.1, x)` = `fun x => w.velocity (↑t, x)` and
`velocitySliceSmoothL2_field` is an honest `rfl` (re-checked in the probe's own `open` environment).
`smooth`/`integrable` come from C01 unit U1 `velocity_slice_smoothL2` (`C01/VelocityJets.lean:85-88`),
not reproved here.

**Index type and horizon match the consumers.** `velocityField`'s index is `t : Icc (0:ℝ) S` with
`hST : S < T`, which is exactly the pair's index in `AprioriRows.sobolevSpace_norm_le_sobolevNormAt`
(`AprioriRows.lean:301-309`, its horizon variable instantiated at `T := S`) and exactly what
`L2Descent.hword_jet_full` (`L2Descent.lean:199-203`) consumes pointwise (it takes a bare
`Z : SmoothL2Field Space`). The `Icc 0 S` / `hST : S < T` combination is what feeds
`mem_Ico_of_mem_Icc` (`Evolution.lean:108-110`) inside `velocityField`. Printed signature
(`rev157_sigs.lean`) confirms `Space` resolves to `NavierStokes.ProblemStatement.Space`, not the
vendor homonym `EulerSmoothLimit.Space` (LESSONS 2026-09-14 0839Z/152).

### 2.2 `sobolevENorm_slice_ne_top` (`:127-132`) ✅

```
theorem sobolevENorm_slice_ne_top {q ν a f T} (w : ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Ico (0:ℝ) T) :
    sobolevENorm ((q + 1 : ℕ) : ℝ) (fun x : Space => w.velocity (t, x)) ≠ ⊤
```

Proof: `w.sobolev (q+1)` (`A02/SolutionClass.lean:132-134`) gives a datum `G t` of the slice at every
`t ∈ Ico 0 T`; `sobolevENorm_le_of_isSobolevDatum` (`D01/SmoothDatum.lean:309-311`) makes
`sobolevENorm ≤ ‖G t‖ₑ`; `ne_top_of_le_ne_top (by simp)`. Correct and **not** `⊤`-vacuous: this is the
*finiteness* direction, so the LESSONS 09-14 0707Z/149 hazard (`⊤.toReal = 0`) is exactly what it
rules out, and it is fed to `AprioriRows`' `hfin` whose whole purpose is that ruling-out.
`ht : t ∈ Ico 0 T` is the right slab (half-open — `ClassicalSolutionR` says nothing at `t = T`).

### 2.3 `sobolevSpace_norm_le_sobolevNormAt_of_solution` (`:145-160`) — all three hypotheses discharged ✅

Target (`AprioriRows.lean:301-309`) carries exactly three: `hz`, `hfin`, `hword_jet`. All three are
supplied from `w`:

* `hz t := contDiff_slice w.velocity_smooth ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩` — `contDiff_slice` is
  `D01/DatumToJets.lean:366-368`, hypothesis `ContDiffOn ℝ ∞ v (Ico 0 T ×ˢ univ)`, field-for-field
  `ClassicalSolutionR.velocity_smooth` (`SolutionClass.lean:118`);
* `hfin t := sobolevENorm_slice_ne_top w ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩` (§2.2);
* `hword_jet t n hn wrd := hword_jet_full (u t) (fun θ => hu θ t) (U t) (hU t)
  (velocitySliceSmoothL2 w t hST) (hslice t).symm n hn wrd` — for **all** `n ≤ q+1`.

The two `eLpNorm` terms unify because `(velocitySliceSmoothL2 …).field` is *definitionally*
`fun x => w.velocity (↑t,x)` (§2.1), so the `exact` is not hiding a `simp`-level coincidence.
**The only named hypothesis left besides the pair's own data `hu`/`hU` is `hslice`** — confirmed by
the printed signature.

Binders are exactly as the brief specifies: `(w) (u U hu hU hslice)` after `hST`, conclusion
`∀ t : Icc 0 S, ‖u t‖ ≤ jetSobolevConst (q+1) * sobolevNormAt ((q+1:ℕ):ℝ) w.velocity ↑t`.

**`hslice` orientation — checked, and the `.symm` is load-bearing.** The two consumers disagree, on
purpose:

* `OrderTwoCap.sobolevNormAt_two_le_of_cylinder` (`OrderTwoCap.lean:163-170`) wants
  `hslice : ∀ t, (fun x => v (↑t,x)) =ᵐ[volume] ⇑(U t)` — **same** orientation as the lane's
  `hslice`, so `apriori_rows_of_hslice` passes it through unchanged;
* `L2Descent.hword_jet_full` (`L2Descent.lean:202`) wants `hUz : (⇑U) =ᵐ[volume] Z.field` — the
  **opposite** orientation, hence `(hslice t).symm`.

Mutation 1 (§6) deletes the `.symm` and fails with the expected application-type mismatch.

### 2.4 `isSobolevDatum_ordinary_of_hslice` (`:168-176`) ✅

`w.sobolev m` supplies the physical slice's order-`m` datum `G ↑t` at `↑t ∈ Ico 0 T`;
`IsSobolevDatum.congr_field` (`Section4/A01/CarrierBridge.lean:79-81`) moves it onto `⇑(U t)` along
`hslice t`. General in `m` (no `q+1` restriction). The printed signature shows the conclusion is
`NSFormalization.Section4.D01.IsSobolevDatum` — the one `sobolevENorm` is built on
(`SmoothDatum.lean:306-307`), i.e. the right one for downstream; `w.sobolev`'s datum is
`A02.IsSobolevDatum` (`SolutionClass.lean:79-81`), token-identical body, unifies by delta. The
ATTEMPTS note about the two defs is accurate. (LESSONS 2026-09-14/111 — I read `#check`, not the
`open` list.)

### 2.5 `apriori_rows_of_hslice` (`:191-204`) ✅

Both conjuncts exactly as claimed; forward from `OrderTwoCap.sobolevNormAt_two_le_of_cylinder`,
converse from §2.3. `hq : 4 ≤ q` is **exactly minimal** for the forward row:
`hasWeakDerivsL2Bound_of_cylinder` (`OrderTwoCap.lean:113-117`) asks `hm : m + 3 ≤ q + 1`, at `m = 2`
that is `4 ≤ q`. It is **strictly weaker** than `HasAprioriBound`'s `hq : 6 ≤ q`
(`Horizon.lean:106`), so the consumer discharges it by `omega` — verified,
`rev157_fidelity.rows_under_six` takes `hq : 6 ≤ q` and fires the rows (3-axiom). **No mismatch.**

Constants are load-bearing: mutation 2 (§6) replaces `jetSobolevConst (q+1)` by `1` and `16` by `1`;
both fail with a type mismatch naming the real constant.

### 2.6 Fidelity as a whole

`rev157_fidelity.lean` restates all five statements **verbatim** in a deliberately *different* `open`
environment (the `A01` namespace not opened, every lane name fully qualified,
`A02.SpatialField`/`A02.SpaceTimeField`/`A02.ClassicalSolutionR` written with prefixes) and discharges
each by the lane theorem. All typecheck, 3-axiom. So no bare name in `SliceWiring.lean` resolved to
something other than what the docstrings say.

Non-vacuity: `research/A01/axioms_slice_wiring.lean` fires all four row theorems on `A04.zeroSol 1 2`
(`ZeroSolution.lean:91`, a real `ClassicalSolutionR` on `[0,2)`) with the zero cylinder pair on
`[0,1]`, and all ten `#print axioms` are the standard three. This is a genuine instance (`hslice0` is
proved, not assumed), though a *trivial* one — the conclusions are `0 ≤ …`.

---

## 3. The reduction claim (brief item 4) — audited

### (a) Is the horizon relation right? **Yes, and `T = S` provably does not suffice.**

The pair is indexed by `Icc 0 S` (closed, endpoint included — the sup-norm `‖u‖ ≤ R` needs `t = S`),
while `ClassicalSolutionR ν a' f' T` carries data only on the half-open `Ico 0 T`
(`SolutionClass.lean:118-134`: `velocity_smooth`, `divergence`, `sobolev`, `pressure_gradient` are all
on `Ico 0 T`). So every `t : Icc 0 S` must satisfy `↑t ∈ Ico 0 T`, which at `t = S` is `S < T`.
`rev157_mut3_horizon.endpoint_not_in_Ico` **proves** `∃ t : Icc 0 S, ↑t ∉ Ico 0 S` (3-axiom), i.e. the
`T = S` reading is *false*, not merely unprovable by this route; `control_lt` proves the `S < T`
version for every `t`. Mutation 3 (§6) confirms the module body breaks under `hST : S ≤ T`.

### (b) What `exists_local_shape_of_aprioriBound` actually outputs — and the right citation

`Horizon.lean:166-188` returns

```
∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S), ∃ u U,
  ‖u‖ ≤ R ∧ u ⟨0,…⟩ = ordinarySobolev … ∧ U ⟨0,…⟩ = a.toLp ∧
  (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧ (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
  (∀ t, u t = quadraticDuhamel …) ∧ (∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t)
```

— **no `SpaceTimeField`, no `ClassicalSolutionR`, no `hslice`**, exactly as the lane says. But the pair
lives on `Icc 0 T'` for an existentially bound `T' ≤ S`, **not** on `Icc 0 S`; the theorem's own
docstring (`Horizon.lean:160-164`) says so: "`T = S` is invisible in the bare `∃ T` type — consumers
that need the horizon *pinned* to `S` must use `localTheory_on_prescribed_horizon`". The theorem that
delivers the pair on `Icc 0 S` is `localTheory_on_prescribed_horizon` (`Horizon.lean:137-157`). See N1.

**Owner of the constructor.** `research/A01/A01_SPLIT.md`: unit **B1** (row `c3`
`velocity_smooth`, the joint all-order `C^∞` pointwise field from the `H^m`-in-time path, graded **L**,
`A01_SPLIT.md:104`, and named "**Single biggest blocker**" at `:207`), unit **B2** (assemble the
structure field-by-field, S, `:184`), with the Fourier-convention bridges **C1b/C1c** (both L, `:129`)
underneath, plus residual row **(v)** (produce `a' ∈ initialClassR` and `f'` with `MemForceR` from
`a : SmoothL2Field Space` / `F : Icc 0 S → SmoothL2Field Space`; `REVIEW_L2_DESCENT.md` §3 row 5,
M–L). **Estimate: L, multi-lane** — not a single small lemma. See N3.

**The exact statement the next lane must prove** (typechecked, `rev157_constructor_loop.lean:33-40`):

```lean
def CarrierConstructor (q : ℕ) (ν S : ℝ) : Prop :=
  ∀ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
      (∀ t, ordinaryLift (U t) = value 1 (u t)) →
      ∃ (a' : SpatialField) (f' : SpaceTimeField) (T : ℝ) (_hST : S < T)
        (w : ClassicalSolutionR ν a' f' T),
        ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)
```

and `rev157_constructor_loop.rows_from_constructor` closes the loop with it (3-axiom): from
`HasAprioriBound hq hν a F hF R` and `CarrierConstructor q ν S` it produces `u`, `a'`, `f'`, `T`,
`w : ClassicalSolutionR ν a' f' T` with `‖u‖ ≤ R` **and both rows**. So the lane's claim is verified
in Lean, not just asserted.

### (c) `ClassicalSolutionR` appears only as an input in A01 — and tree-wide there is no mild ⇒ classical constructor ✅

```
$ grep -rn "ClassicalSolutionR" formalization/NSFormalization/Section4/A01/
```
11 files; in every one but `SliceWiring.lean` the token occurs only in a docstring or as a binder type
`(w : ClassicalSolutionR ν a f T)` (`GronwallInstance`, `AprioriRows`, `PressureGauge`,
`ProjectedEquation`, `RadialPotential`, `ConvectionDivergence`, `DatumPathContinuity`, `CarrierWords`,
`OrderTwoCap`, `Horizon`). **No constructor.** I widened the check as the brief asked:

* `formalization/NSFormalization/Section4/HeliCorgiPort.lean` — **0** occurrences;
* `formalization/NSFormalization/Section4/I02/` — **0** occurrences;
* `formalization/NSFormalization/Section4/A02/` — `SolutionClass.lean:114` is the `structure`
  declaration itself; the only term-producing declarations are `Restrict.lean:60`
  `ClassicalSolutionR.restrict`, `:175` `.congr`, `:247` `.normalizePressure`, all taking an existing
  `w` as input;
* tree-wide the only *from-scratch* constructor is `A04/ZeroSolution.lean:91` `zeroSol` (the zero
  solution). The `∃ w : ClassicalSolutionR …` statements in `A02/{Maximal,Patch,Restrict}.lean`,
  `R42/{FullHorizon,SolutionOnShorter}.lean` all start from an existing solution.

So the lane's negative claim is correct, and it is correct in the strong (tree-wide) form, not only
for `Section4/A01`.

### (d) Is `hinv` (iv) carried by the pair? **Yes on the consumer side; no on the supply side.** (N2)

`localTheory_on_prescribed_horizon` / `exists_local_shape_of_aprioriBound` both output
`∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t` as their **last conjunct** (lane 134's
`forced_global_of_bound_unconditional`). Verified, not inspected:
`rev157_constructor_loop.rows_from_constructor` destructures `hu` out of that conclusion and feeds it
to `apriori_rows_of_hslice` — no extra hypothesis.

**But that is a different `u` from the one row 4 of `REVIEW_L2_DESCENT.md` §3 meant.**
`rev157_supply_side.hasAprioriBound_unfold` proves by `Iff.rfl` that

```
HasAprioriBound hq hν a F hF R ↔
  ∀ (T' : ℝ) (hT : 0 ≤ T') (hTS : T' ≤ S) (u : C(Icc 0 T', SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) → ‖u‖ ≤ R
```

— the quantified `u` is constrained **only** by the Duhamel equation: no angle invariance, no ordinary
carrier `U`, no `ClassicalSolutionR`, and its index is `Icc 0 T'` with `T' ≤ S`, not `Icc 0 S`. A3's
actual goal (row A3-M2) is to **supply** `HasAprioriBound`; on that side `hu`, `U` (with the descent)
and `hslice` are all still owed, for an arbitrary Duhamel path. `A3_SPLIT.md` still lists (iv) under
"Still needed after 157", so the ledger is not wrong — only the parenthetical "(carried by the pair)"
and the module header's "modulo unit (iv) `hinv`, which is already carried by the pair" need the
distinction spelled out.

---

## 4. Numbered findings

All **notes**; none blocks the merge; none touches `SliceWiring.lean`'s mathematics.

**N1 (record, accuracy, one-line fix).** The module header (`SliceWiring.lean:57-59, 66`), the
ATTEMPTS "single remaining obligation" section (`ATTEMPTS_SLICE_WIRING.md:85-86, 100`) and the
`A3_SPLIT.md` lane-157 paragraph all say the constructor is for "the `(u,U)` of
`exists_local_shape_of_aprioriBound`" with the pair "on `Icc 0 S` (with `S := horizonOf … = S`)". The
`∃ T`-shaped corollary (`Horizon.lean:166`) does **not** pin the horizon; its own docstring
(`Horizon.lean:160-164`) says consumers needing `Icc 0 S` must use
`localTheory_on_prescribed_horizon` (`Horizon.lean:137`). *Fix: replace the three citations of
`exists_local_shape_of_aprioriBound` (`:166`) by `localTheory_on_prescribed_horizon` (`:137`).* (No
Lean change: the lane theorems are generic in the pair's horizon and `rev157_constructor_loop.lean`
runs them off `localTheory_on_prescribed_horizon` unchanged.)

**N2 (record, honesty, one sentence).** "(iv) `hinv` … already carried by the pair"
(`SliceWiring.lean:62-63`, `ATTEMPTS_SLICE_WIRING.md`, `A3_SPLIT.md` lane-157 paragraph) silently
switches which `u` is meant: it is true for the pair `HasAprioriBound`'s **consumer** outputs, false
for the `u` `HasAprioriBound` **quantifies over** (§3(d), proved by `Iff.rfl`). *Fix: add "— for the
pair the consumer outputs; the `u` inside `HasAprioriBound`'s `∀` still owes `hu`, `U` and `hslice`
(row A3-M2)".*

**N3 (record, cost honesty, one clause).** "**The one remaining obligation**" / "row (i) is now the
single constructor" is accurate as a *count* but reads as small. Per `A01_SPLIT.md` the constructor is
**B1** (row c3, **L**, "the hardest bridge" `:104`, "Single biggest blocker" `:207`) + **B2** (S,
`:184`) over **C1b/C1c** (both L, `:129`), plus residual row (v). *Fix: say "single **L**-sized
obligation (units B1/B2 over C1b/C1c, plus row (v)), the largest item in the A01 DAG".*

**N4 (CI coverage; carried over from lane-153 N4).** `NSFormalization.Section4.A01.SliceWiring` is
inside **no** registered contract closure — `make test` (10524 jobs) does not compile it. It *is*
compiled on this PR (`build_changed_lean.py --base-ref origin/erenup/integration --dry-run` prints
exactly `NSFormalization.Section4.A01.SliceWiring`), but nothing keeps it compiling after the merge.
*Fix: add it, with `AprioriRows`, `L2Descent`, `CarrierWords`, `OrderTwoCap`, to the next A01 contract
bundle.* Tracked, not blocking.

**N5 (follow-up, next `NNN-SIMP-A01` lane).** `velocitySliceSmoothL2` is a pure alias with **one** use
site (the `hword_jet_full` argument at `:159`); `rev157_fidelity.carrier_is_velocityField` closes
`velocitySliceSmoothL2 w t hST = C01.velocityField w hST t` by `rfl`. The tree now has three names for
the velocity-slice `SmoothL2Field` (`C01.velocityField` `Evolution.lean:115`, `C01.velocitySliceField`
`MomentumCarrierB.lean:93`, this alias) and two `@[simp]` `_field` lemmas with the same LHS shape.
*Fix in the simplifier lane: inline `C01.velocityField` and drop the alias + its `@[simp]` twin.* Do
not do it here (never mix simplification with new mathematics).

**N6 (follow-up, generality, simplifier lane).** `sobolevENorm_slice_ne_top` is stated only at order
`((q+1 : ℕ) : ℝ)`; its proof (`w.sobolev (q+1)` + `sobolevENorm_le_of_isSobolevDatum`) works verbatim
at every `m : ℕ`. *Fix: generalize to `(m : ℕ)` and keep the `q+1` form as a one-line instance* —
`isSobolevDatum_ordinary_of_hslice` is already general in `m`, so the two would match.

**N7 (informational, no action).** `make check` reports `"source_hashes_match": false` and one `sorry`
token in the copied-umbrella closure (`Paper1/BoundaryCorollary.lean:90`). Both pre-existing and
unrelated to this lane (identical to lane-153 N6); `make check` exits 0.

**N8 (informational, good news).** Unlike lane 153 (its N5), there is **no stale-base noise** here:
the 12 commits integration has gained since this lane's base `38abd97` touch only `NEXT_SESSION.md`,
`PLAN.md`, `logs/AGENT_RUNS.csv`, `logs/LESSONS.md`, so
`check_contracts.py --base-ref origin/erenup/integration` passes with
`"base_compatibility_checked": true`. A rebase before merge is still advisable (LESSONS
2026-09-14/123) but is expected to be a no-op for Lean.

---

## 5. Commands and results

Environment: `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` run only from `verification/`.

### 5.1 Build and typecheck — silent

```
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.SliceWiring
Build completed successfully (9988 jobs).
EXIT=0
$ grep -c SliceWiring <build log>      # warnings attributable to the new module
0
```
(The build log's 37 warnings are all *replayed* upstream modules — `Paper3/*`, `Source/*`,
vendor — none from `SliceWiring.lean`.)

```
$ cd verification && lake env lean ../formalization/NSFormalization/Section4/A01/SliceWiring.lean
EXIT=0        (no output)
```

### 5.2 Hygiene

```
$ grep -rn "sorry\|admit\|native_decide\|maxHeartbeats\|set_option\|axiom" \
    formalization/NSFormalization/Section4/A01/SliceWiring.lean \
    research/A01/axioms_slice_wiring.lean
EXIT=1        (no match)
```

### 5.3 Axioms and non-vacuity — all ten standard three

```
$ cd verification && lake env lean ../research/A01/axioms_slice_wiring.lean
'NSFormalization.Section4.A01.velocitySliceSmoothL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.velocitySliceSmoothL2_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.sobolevENorm_slice_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.sobolevSpace_norm_le_sobolevNormAt_of_solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.isSobolevDatum_ordinary_of_hslice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.apriori_rows_of_hslice' depends on axioms: [propext, Classical.choice, Quot.sound]
'nonvacuous_slice_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'nonvacuous_converse' depends on axioms: [propext, Classical.choice, Quot.sound]
'nonvacuous_datum_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'nonvacuous_apriori_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

### 5.4 Gates

```
$ make check
… "tokens_in_copied_umbrella_closure": [ { "module": "NSFormalization.Paper1.BoundaryCorollary",
    "line": 90, "token": "sorry" } ], "source_hashes_match": false …
python3 experiments/test_contract_policy.py → Ran 13 tests … OK
python3 experiments/check_work_queue.py → 30 work items: ownership, contract registration and task cards consistent.
EXIT=0

$ make test
ℹ [10524/10524] Replayed Tests.EnergyAbsorptionPartialV3
info: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3: checked; standard logical axioms only
EXIT=0        (SliceWiring appears 0 times — N4)

$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
… "base_compatibility_checked": true …
EXIT=0

$ python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run
Changed Lean modules: NSFormalization.Section4.A01.SliceWiring
```

### 5.5 Reviewer probes (new, `research/A01/probes/`)

```
$ cd verification && lake env lean ../research/A01/probes/rev157_fidelity.lean
'Rev157Fidelity.converse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev157Fidelity.rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev157Fidelity.carrier_is_velocityField' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev157Fidelity.rows_under_six' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0        (7 verbatim restatements, all discharged by the lane theorems)

$ cd verification && lake env lean ../research/A01/probes/rev157_constructor_loop.lean
'Rev157Ctor.rows_from_constructor' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0        (the claimed constructor really closes the consumer side)

$ cd verification && lake env lean ../research/A01/probes/rev157_supply_side.lean
'Rev157Supply.hasAprioriBound_unfold' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0        (Iff.rfl: HasAprioriBound's `u` has no invariance / no `U` / index `Icc 0 T'`)

$ cd verification && lake env lean ../research/A01/probes/rev157_sigs.lean
@NSFormalization.Section4.A01.velocitySliceSmoothL2 : … → EulerLpTranslation.SmoothL2Field NavierStokes.ProblemStatement.Space
@NSFormalization.Section4.A01.isSobolevDatum_ordinary_of_hslice : … ∃ A, NSFormalization.Section4.D01.IsSobolevDatum (↑m) (↑↑(U t)) A
…
EXIT=0
```

### 5.6 Negative checks (three mutations, each with a positive control)

**Mutation 1 — `hslice` orientation, `.symm` deleted** (`rev157_mut1_hslice.lean`). The file holds a
positive control (the module's body verbatim, *with* `.symm`) which compiles, and the mutant:

```
$ cd verification && lake env lean ../research/A01/probes/rev157_mut1_hslice.lean
../research/A01/probes/rev157_mut1_hslice.lean:61:36: error: Application type mismatch: The argument
  hslice t
has type
  (fun x => w.velocity (↑t, x)) =ᵐ[volume] ↑↑(U t)
but is expected to have type
  ↑↑(U t) =ᵐ[volume] (velocitySliceSmoothL2 w t hST).field
in the application
  hword_jet_full (u t) (fun θ => hu θ t) (U t) (hU t) (velocitySliceSmoothL2 w t hST) (hslice t)
EXIT=1
```
Only the mutant errors. The two consumers genuinely want opposite orientations (§2.3).

**Mutation 2 — the constants** (`rev157_mut2_const.lean`), a *statement*-level mutation, not an
omitted argument (LESSONS 2026-09-14/113):

```
$ cd verification && lake env lean ../research/A01/probes/rev157_mut2_const.lean
…:36:2: error: Type mismatch
  sobolevSpace_norm_le_sobolevNormAt u w.velocity … fun t n hn wrd => ?m.158
has type   ∀ (t : ↑(Icc 0 S)), ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt (↑(q + 1)) w.velocity ↑t
but is expected to have type
           ∀ (t : ↑(Icc 0 S)), ‖u t‖ ≤ 1 * sobolevNormAt (↑(q + 1)) w.velocity ↑t
…:52:2: error: Type mismatch
  sobolevNormAt_two_le_of_cylinder u U hu hU hq w.velocity hslice
has type   ∀ (t : ↑(Icc 0 S)), sobolevNormAt 2 w.velocity ↑t ≤ 16 * ‖u t‖
but is expected to have type
           ∀ (t : ↑(Icc 0 S)), sobolevNormAt 2 w.velocity ↑t ≤ 1 * ‖u t‖
EXIT=1
```
Both constants are the ones the sources produce; neither is a numeral the elaborator invents.

**Mutation 3 — `T = S`** (`rev157_mut3_horizon.lean`). Two positive results and one mutant:

```
$ cd verification && lake env lean ../research/A01/probes/rev157_mut3_horizon.lean
…:53:76: error: Application type mismatch: The argument
  hST
has type   S ≤ T
but is expected to have type   S < T
in the application   lt_of_le_of_lt t.property.right hST
…:54:71: error: (same, in sobolevENorm_slice_ne_top's argument)
…:57:31: error: (same, in velocitySliceSmoothL2 w t hST)
'Rev157Mut3.endpoint_not_in_Ico' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev157Mut3.control_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=1
```
`endpoint_not_in_Ico : ∀ S, 0 < S → ∃ t : Icc 0 S, (↑t : ℝ) ∉ Ico 0 S` is a *proof* that the `T = S`
reading is false at the right endpoint of the pair's index, not just an error message; `control_lt`
is the `S < T` positive control. So `hST : S < T` is the right and necessary shape.

### 5.7 Citations opened at the cited lines (honesty of ATTEMPTS) — all correct

`C01/Evolution.lean:115` (`velocityField`), `C01/VelocityJets.lean:85` (`velocity_slice_smoothL2`),
`C01/MomentumCarrierB.lean:93` (`velocitySliceField`), `D01/DatumToJets.lean:306`
(`exists_smoothL2Field_of_memHInfty`), `:366` (`contDiff_slice`), `D01/SmoothDatum.lean:237`
(`IsSobolevDatum`), `:306`/`:309` (`sobolevENorm` / `sobolevENorm_le_of_isSobolevDatum`),
`A02/SolutionClass.lean:79` (`IsSobolevDatum`), `:114` (the `structure`),
`A01/CarrierBridge.lean:79` (`IsSobolevDatum.congr_field`), `A01/EulerPairing.lean:378`
(`exists_isSobolevDatum_m_of_ae`), `A01/AprioriRows.lean:301` (`sobolevSpace_norm_le_sobolevNormAt`),
`A01/L2Descent.lean:199` (`hword_jet_full`), `A01/OrderTwoCap.lean:163`
(`sobolevNormAt_two_le_of_cylinder`), `:213` (`kbnd_of_sup_bound`), `A01/Horizon.lean:106`
(`HasAprioriBound`), `:166` (`exists_local_shape_of_aprioriBound`), `A04/ZeroSolution.lean:91`
(`zeroSol`). Every one is at the stated line. The only citation issue is N1 (right line, wrong
theorem for the claim being made).
