# A04 unit D1 — review (lane 053)

Reviewed: commit `34d72cd` "[053-A04] Unit D1: derivative of the squared datum
norm along a smooth Sobolev path; inner-product instance on the real Sobolev
carrier", stacked on lane 039 (`fc097fb`).

Files under review:

* `formalization/NSFormalization/Section4/A04/DerivNorm.lean` (new, 174 lines)
* `research/A04/axioms_d1.lean` (new)
* `research/A04/ATTEMPTS_D1.md` (new)

## Verdict

**ACCEPT-WITH-NOTES**

The mathematics is right, the build is clean, the axiom audit is clean, and the
one genuinely new piece of infrastructure — the `InnerProductSpace ℝ
(RealSobolevHilbert s)` instance — introduces **no norm diamond**: I checked it
four ways and every check passes. The statements are the ones
`energyIdentityHigh`'s left-hand side needs, in the right vocabulary, with the
derivative value exposed.

Nothing blocks the merge. The notes are: one **wrong entry in the attempts
record** (finding 3), an **instance-placement** issue that is a merge hazard for
later lanes rather than a bug (finding 2), one **forward-looking spec gap** that
the lead should book before unit G1 starts (finding 6), and three cosmetics.

## Commands and results

All from the worktree `.claude/worktrees/053-A04-unit-d1`, with
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`, one `lake` at a time,
every `lake` invocation from `verification/`.

| # | Command | Result |
|---|---------|--------|
| 1 | `bash scripts/lean-install.sh` | exit 0, ends `== OK` |
| 2 | `cd verification && lake build NSFormalization.Section4.A04.DerivNorm` | **exit 0**, `Build completed successfully (9883 jobs)`; `grep -i 'DerivNorm\|A04'` over the full log → **no lines**, `grep error` → **no lines**. (All warnings in the log are pre-existing ones from `Paper3/*`, `Source/*`.) |
| 3 | `cd verification && lake env lean ../formalization/NSFormalization/Section4/A04/DerivNorm.lean` (forces re-elaboration from source, so the module's own warnings cannot be hidden by a cached replay) | **exit 0, zero bytes of output** — no errors, no warnings, no linter hits from the file |
| 4 | `cd verification && lake env lean ../research/A04/axioms_d1.lean` | **exit 0**; all **7** `#print axioms` are exactly `[propext, Classical.choice, Quot.sound]` (`instInnerProductSpaceRealSobolevHilbert`, `hasDerivAt_datumNormSq`, `hasDerivAt_datumPath`, `hasDerivAt_datumNormSq_of_contDiffOn`, `exists_hasDerivAt_sobolevNormAt_sq`, `d1_exists_hasDerivAt_sobolevNormAt_sq`, `d1_energyIdentityHigh_lhs`). The `energyIdentityHigh`-LHS statement `d1_energyIdentityHigh_lhs` typechecks. |
| 5 | `grep -n 'sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option' DerivNorm.lean` | **no matches at all** (exit 1) |
| 6 | same grep on `research/A04/axioms_d1.lean` | only the seven `#print axioms` lines and the words "axioms"/"axioms_f1n1" inside the header comment. No `sorry`, no `admit`, no `native_decide`, no `axiom` declaration, no `maxHeartbeats`, no `set_option`. |
| 7 | `make check` | **exit 0** — `check_formalization_plan.py --check`, `check_contracts.py`, `test_contract_policy.py` (13 tests OK), `check_work_queue.py` (`30 work items: ownership, contract registration and task cards consistent.`) |

Scratch files used for findings 1 and 3 were written under `/tmp`, run with
`lake env lean`, and deleted. No file inside the worktree was written except
this review. No git write command was run.

## Findings

### 1. `instInnerProductSpaceRealSobolevHilbert` — no norm diamond. Confirmed, four independent ways. (severity: none, this is a pass)

`DerivNorm.lean:103-105`

```lean
instance instInnerProductSpaceRealSobolevHilbert (s : ℝ) :
    InnerProductSpace ℝ (RealSobolevHilbert s) :=
  inferInstanceAs (InnerProductSpace ℝ (realSubspace s).toSubmodule)
```

Mathlib's `InnerProductSpace 𝕜 E` takes the `SeminormedAddCommGroup E` as an
*instance parameter* (`Mathlib/Analysis/InnerProductSpace/Defs.lean:107`), so
the norm the instance talks about is whatever instance search finds for
`NormedAddCommGroup (RealSobolevHilbert s)` at the instance's declaration site.
That is the whole diamond question. Checks run (all pass, `lake env lean`
exit 0):

* `#synth NormedAddCommGroup (RealSobolevHilbert (3:ℝ))` →
  `NSFormalization.Paper3.realSobolevNormedAddCommGroup 3`. This is exactly the
  instance `sobolevENorm` / `sobolevNormAt` / `sobolevNormAt_eq` use. Also
  confirmed by `rfl`:
  `example (s : ℝ) : (inferInstance : NormedAddCommGroup (RealSobolevHilbert s)) = NSFormalization.Paper3.realSobolevNormedAddCommGroup s := rfl` ✔
* `#synth NormedAddCommGroup (RealVectorSobolev (3:ℝ))` →
  `PiLp.normedAddCommGroup 2 fun x => ↥(RealSobolevHilbert 3)`, the pre-existing
  one; the new instance introduces no group instance on the vector carrier.
  Also by `rfl` against `inferInstanceAs (NormedAddCommGroup (PiLp 2 fun _ : Fin 3 => RealSobolevHilbert s))` ✔
* `#synth InnerProductSpace ℝ (RealVectorSobolev (3:ℝ))` →
  `PiLp.innerProductSpace fun x => ↥(RealSobolevHilbert 3)`, i.e. the lift is
  Mathlib's, not a hand-rolled one.
* The induced-norm law holds on **both** carriers, which is the semantic form of
  "no diamond":
  `example (s : ℝ) (x : RealSobolevHilbert s) : ‖x‖ = Real.sqrt (RCLike.re (K := ℝ) ⟪x, x⟫) := norm_eq_sqrt_re_inner x` ✔ and the same for
  `x : RealVectorSobolev s` ✔. (The brief's spelling `RCLike.re (𝕜 := ℝ)` is
  rejected by this Mathlib — the named argument is `K`.)
* **`NormedSpace` diamond, the one the brief did not ask about but which this
  instance does create**: `InnerProductSpace` extends `NormedSpace ℝ E`, and
  `Paper3.realSobolevNormedSpace` already existed
  (`Paper3/RealPositiveDensity.lean:17`). The diamond is benign and closed:
  `example (s : ℝ) : (InnerProductSpace.toNormedSpace : NormedSpace ℝ (RealSobolevHilbert s)) = NSFormalization.Paper3.realSobolevNormedSpace s := rfl` ✔,
  and instance search still returns Paper3's:
  `#synth NormedSpace ℝ (RealSobolevHilbert (3:ℝ))` →
  `NSFormalization.Paper3.realSobolevNormedSpace 3`,
  `#synth Module ℝ (RealSobolevHilbert (3:ℝ))` →
  `(NSFormalization.Paper3.realSobolevNormedSpace 3).toModule`.

The instance is also genuinely **new and necessary**, not a duplicate of
something already reachable. Negative check, in a file importing only lane 039's
`Section4.A04.Continuity` (i.e. everything except `DerivNorm`):

```
error: failed to synthesize InnerProductSpace ℝ ↥(RealSobolevHilbert 3)
error: failed to synthesize InnerProductSpace ℝ (RealVectorSobolev 3)
```

so `ATTEMPTS_D1.md`'s central claim ("no such instance is registered") is
accurate.

### 2. The instance is a *global* instance declared in an A04 leaf; it belongs in `Paper3`. (severity: low — note, not a blocker)

`DerivNorm.lean:103`. There is today **no collision**: a grep over every
non-`.lake` `.lean` file in `formalization/`, `verification/` and `research/`
finds `DerivNorm.lean:103` as the **only** `InnerProductSpace`/`Inner` instance
declaration in project source (every other hit is an `import` or an `open
scoped`). So this is a prospective hazard, not a present bug:

* any other lane that needs the real inner product on the Sobolev carrier must
  now `import NSFormalization.Section4.A04.DerivNorm` — importing an A04
  energy-identity leaf to get a Paper3 algebraic fact;
* more likely, a parallel lane will simply declare its own copy in *its* leaf.
  Two copies would be defeq (both `inferInstanceAs` on the same `Submodule`), so
  no unsoundness, but instance search becomes ambiguous and `rw`/`simp` lemmas
  stated against one copy stop matching goals carrying the other. That is a
  painful, late-discovered merge conflict.

Fix (follow-up lane, not this one): move the three lines to
`formalization/NSFormalization/Paper3/RealPositiveDensity.lean`, immediately
after `realSobolevNormedSpace` (`:17`), and drop the `open
NSFormalization.Source.RealSobolev (realSubspace)` from `DerivNorm.lean`'s
header. Everything checked in finding 1 goes through verbatim there — the
instance body already names `(realSubspace s).toSubmodule`, which is exactly the
term `realSobolevNormedAddCommGroup` and `realSobolevNormedSpace` are built
from.

### 3. `ATTEMPTS_D1.md` records a snag that is **false**: `Ico_mem_nhds` does exist. (severity: low — record accuracy)

`research/A04/ATTEMPTS_D1.md`, §"Small snags fixed while building":

> `Ico_mem_nhds` does not exist in this Mathlib; only `Ioo_mem_nhds`. Used
> `Filter.mem_of_superset (Ioo_mem_nhds …) Ioo_subset_Ico_self`.

`Ico_mem_nhds` **is** available at this pin. It has no source declaration to
grep for because it is auto-generated by the `@[to_dual (reorder := ha hb)]`
attribute on `Ioc_mem_nhds` (`Mathlib/Topology/Order/OrderClosed.lean:614-616`);
Mathlib itself uses it at `Mathlib/Topology/Algebra/Order/Floor.lean:177` and
`Mathlib/Analysis/Convex/Continuous.lean:332`. Verified directly:

```
#check @Ico_mem_nhds
-- @Ico_mem_nhds : ∀ {α} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
--   {a b x : α}, b < x → x < a → Ico b a ∈ nhds x
example {T t : ℝ} (ht : t ∈ Ioo (0:ℝ) T) : Ico (0:ℝ) T ∈ nhds t := Ico_mem_nhds ht.1 ht.2  -- typechecks
```

This is a record defect, not a code defect: the workaround actually used in
`hasDerivAt_datumPath` (`DerivNorm.lean:126-127`) is correct and proves the same
thing. Fix: correct the `ATTEMPTS_D1.md` line to say the lemma was not *found*
(and why — `to_dual` generates it, so it is invisible to a source grep), and
optionally shorten

```lean
have hIco : Ico (0 : ℝ) T ∈ 𝓝 t :=
  Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Ico_self
```

to `have hIco : Ico (0 : ℝ) T ∈ 𝓝 t := Ico_mem_nhds ht.1 ht.2`.

### 4. The second spot-checked snag is accurate. (severity: none)

> `ContDiffOn.differentiableOn` takes `n ≠ 0` (not `1 ≤ n`).

Correct: `Mathlib/Analysis/Calculus/ContDiff/Defs.lean:579`,
`theorem ContDiffOn.differentiableOn (h : ContDiffOn 𝕜 n f s) (hn : n ≠ 0) : DifferentiableOn 𝕜 f s`.
`DerivNorm.lean:128` discharges it with `(by simp)`, which is the codebase
idiom for `(∞ : WithTop ℕ∞) ≠ 0`.

### 5. The statements are the ones `energyIdentityHigh` needs. (severity: none)

**`HasSmoothSobolevPath` restatement.** `DerivNorm.lean:94-98` against
`research/A04/Spec.lean:247-251`: **token-for-token identical**, compared
character by character, including `∀ m : ℕ`, the `(m : ℝ)` cast in both
`RealVectorSobolev (m : ℝ)` and `IsSobolevDatum (m : ℝ) …`, `Ico (0 : ℝ) T` on
both conjuncts, and `ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)`.

**The LHS shape.** `Spec.lean:424-434` asserts, under `HasSmoothSobolevPath T
w.velocity`, for `3 ≤ m` and `t ∈ Ioo (0:ℝ) T`:

```lean
∃ d : ℝ, HasDerivAt (fun r : ℝ => sobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧ …
```

`exists_hasDerivAt_sobolevNormAt_sq` (`DerivNorm.lean:156-172`) delivers exactly
this. On each of the brief's three questions:

* **two-sided `HasDerivAt`?** Yes — `HasDerivAt`, not `HasDerivWithinAt`, on
  both sides, and it is honestly two-sided: `hasDerivAt_datumPath` goes
  `ContDiffOn ℝ ∞ G (Ico 0 T)` → `DifferentiableOn` → (because `Ico 0 T ∈ 𝓝 t`
  for `t ∈ Ioo 0 T`) `DifferentiableWithinAt.differentiableAt` →
  `DifferentiableAt.hasDerivAt`. The derivative produced is the global `deriv G
  t`, not a `derivWithin`. No one-sided sleight of hand.
* **the `(m : ℝ)` cast and `^ 2` as an `ℕ` power?** Yes, and this is checked by
  the machine rather than by eye. `axioms_d1.lean:100-114`
  (`d1_energyIdentityHigh_lhs`) restates the field's LHS in the **contract's own
  vocabulary** — `Contracts.V1.Data.sobolevENorm`, `Data.IsSobolevDatum`,
  `Data.ClassicalSolutionR`, `Data.SpaceTimeField` — and closes it with
  `exact ⟨_, hderiv t ht⟩`. It typechecks, so the spec's
  `sobolevNormAt (m:ℝ) w.velocity r ^ 2` and the library's are the *same term*.
  Stronger still, `d1_exists_hasDerivAt_sobolevNormAt_sq`
  (`axioms_d1.lean:88-98`) feeds a contract-vocabulary `HasSmoothSobolevPath`
  straight into the library lemma as a bare term application
  (`fun _u _T hpath m => …exists_hasDerivAt_sobolevNormAt_sq hpath m`) — that
  only elaborates if the two `HasSmoothSobolevPath`s and the two
  `sobolevNormAt`s are definitionally equal, field for field.
* **is `d = 2⟪G t, deriv G t⟫` exposed so G1 can bound it?** Yes, and in the
  right quantifier order: `∃ G, (identification on Ico 0 T) ∧ ∀ t ∈ Ioo 0 T,
  HasDerivAt … (2 * ⟪G t, deriv G t⟫) t`. `G` is chosen **once, outside** the
  `∀ t`, so G1 gets a single path and a uniform formula for `d`, not a different
  witness per time. (See finding 6 for what G1 still lacks.)

**Interval hygiene at `t = 0`.** The path is smooth on `Ico 0 T` (not `Ioo`, not
`Icc`) — `Ico`, matching the spec. The identification `sobolevNormAt (m:ℝ) u r =
‖G r‖` is asserted on all of `Ico 0 T`, including `r = 0`, and that is justified:
it rests only on the `IsSobolevDatum` conjunct, through `sobolevNormAt_eq`
(`Continuity.lean:85-90`, lane 039), which needs no differentiability and no
interior-point hypothesis. The *derivative* is claimed only on `Ioo 0 T`. So the
`t = 0` worry in the brief does not arise: nothing differentiable is asserted at
the endpoint, and the norm identification there is independent of smoothness.

**Transport.** `HasDerivAt.congr_of_eventuallyEq`
(`Mathlib/Analysis/Calculus/Deriv/Basic.lean:609`) has the signature
`(h : HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) : HasDerivAt f₁ f' x`; the file
supplies `h₁` by `filter_upwards [Ioo_mem_nhds ht.1 ht.2]`, i.e. the two
functions agree on an honest neighbourhood of `t`, not merely within `Ico 0 T`.
Correct.

**Chain of three lemmas.** `hasDerivAt_datumNormSq` (:110) is `HasDerivAt.norm_sq`
(`Mathlib/Analysis/InnerProductSpace/Calculus.lean:215`) specialised, matching
the template `Source/OrdinaryViscousStability.lean:88` cites;
`hasDerivAt_datumPath` (:122) is the regularity step; `hasDerivAt_datumNormSq_of_contDiffOn`
(:135) composes them; `exists_hasDerivAt_sobolevNormAt_sq` (:156) transports. No
gaps.

### 6. Forward-looking: `d` is exposed but **uninterpreted** — G1 cannot yet bound it. (severity: medium, but *not* a defect of this lane)

D1 hands G1 `d = 2⟪G t, deriv G t⟫`. To reach eq:Rhigh, G1 must recognise
`⟪G t, deriv G t⟫` as `⟪u(t), ∂ₜu(t)⟫_{H^m}` and then substitute the momentum
equation. Nothing in `HasSmoothSobolevPath`, in D1, or anywhere in
`Spec.lean` currently says that **`deriv G t` is the order-`m` datum of
`∂ₜu(t,·)`** — the clause asserts only that *some* `C^∞`-in-time path represents
the slices. Without that identification, `d` is a number attached to an abstract
path and eq:Rhigh's right-hand side is unreachable.

This is a spec-level obligation that is currently nobody's: `ATTEMPTS_D1.md`
correctly books "producing `HasSmoothSobolevPath` itself" to A01's
`sobolev_smooth`, but producing it is not the same as identifying its
derivative. Recommend the lead either (a) strengthen `HasSmoothSobolevPath` with
a third conjunct `∀ t ∈ Ioo 0 T, IsSobolevDatum (m:ℝ) (fun x => ∂ₜu (t,x)) (deriv G t)`
(and push the obligation onto A01), or (b) open a small unit for the
interchange, before G1 is scheduled. Either way it should be recorded now rather
than discovered when G1 stalls.

### 7. `axioms_d1.lean`'s `toA02` is dead code. (severity: low, cosmetic)

`research/A04/axioms_d1.lean:61-72` defines the field-by-field bridge
`Data.ClassicalSolutionR → A02.ClassicalSolutionR`. Grep shows it is referenced
nowhere in the file except its own docstring (`:25`). D1 never needs a solution
field — only `w.velocity : SpaceTimeField` and the separate
`HasSmoothSobolevPath` hypothesis — so the bridge is unused, and it is not
covered by any `#print axioms` either. Either delete it or add one line saying it
is carried deliberately for symmetry with `axioms_f1n1.lean` and as a
smoke test that the two structures still agree field-for-field.

### 8. Unused `open`s and an unused API lemma in `DerivNorm.lean`. (severity: low, cosmetic)

`DerivNorm.lean:74-80` opens, from `Section4.A02`, `SpaceTimeScalar`,
`MemForceR`, `IsSobolevPath`, `ClassicalSolutionR`, `forceTimeMeasure`, and from
`Section4.D01`, `sobolevENorm`, `sobolevENorm_le_of_isSobolevDatum`,
`isSobolevDatum_unique` — none of which the module uses (the header is copied
from `Continuity.lean`). Only `SpaceTimeField`, `IsSobolevDatum` and `Space` are
needed. Likewise `open MeasureTheory` and `open scoped ENNReal` appear unused.

Separately, `hasDerivAt_datumNormSq` (:110) is declared as the unit's named API
but never used: `hasDerivAt_datumNormSq_of_contDiffOn` (:135) calls
`(hasDerivAt_datumPath hGc ht).norm_sq` directly rather than routing through it.
That is defensible (the lemma is the row's literal statement, kept as public
API), but routing the composite through it would make the module self-consistent
at zero cost.

Lean emits no warning for either, so neither affects the build.

### 9. `DerivNorm.lean` is in no default build target. (severity: low, pre-existing, lead-level)

`formalization/NSFormalization.lean` contains **zero** `Section4` imports, and
nothing under `verification/` imports `NSFormalization.Section4.A04` (several
`Bindings/*` files import other `Section4` modules, none import A04). So
`lake build` (default target `NSFormalization`) and `lake test` never compile
`DerivNorm.lean`, `Continuity.lean` or `Forcing.lean`; they are reached only by
an explicit `lake build NSFormalization.Section4.A04.DerivNorm` and by
`lake env lean ../research/A04/axioms_d1.lean`.

This is exactly lane 039's situation and not a regression introduced here, but it
means a future refactor can silently break these modules without CI noticing. A
lead-level decision (add an A04 aggregator module to the root, or a `Tests`
binding) rather than a lane-053 fix.

## Summary of required vs. optional follow-ups

| Finding | Action | Required for merge? |
|---|---|---|
| 3 | Correct the `Ico_mem_nhds` line in `ATTEMPTS_D1.md` | No — but do it before the record is relied on |
| 2 | Lift `instInnerProductSpaceRealSobolevHilbert` to `Paper3/RealPositiveDensity.lean` | No — follow-up lane, before another lane needs the inner product |
| 6 | Book the `deriv G t = datum of ∂ₜu` obligation | No — before G1 is scheduled |
| 7, 8 | Cosmetic cleanups | No |
| 9 | Section 4 leaves are outside CI | No — pre-existing, lead-level |

Findings 1, 4, 5 are passes and need no action.
