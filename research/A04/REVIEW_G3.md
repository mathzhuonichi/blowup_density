# Review — A04 unit G3 (`Section4/A04/Gronwall.lean`), lane 041

Reviewer: opus, 2026-09-13.  Worktree `.claude/worktrees/041-A04-unit-g3`,
lane commit `da5b6c2` (3 files: the module, `ATTEMPTS_G3.md`, `axioms_g3.lean`).

## Verdict: **ACCEPT-WITH-NOTES**

The three theorems are correct, sharp, `sorry`-free, standard-axioms, and they
are the right shape for `higherOrderBound`.  **The continuous version suffices
for A04 as specified; the `L¹` version is not needed.**  The notes are all about
the *record*, not the mathematics: one prior-art claim in `ATTEMPTS_G3.md` and
in `COMPARISON.md` row G3 is wrong (a variable-coefficient Grönwall already
exists in the vendored package), one sentence about the `L¹` obstacle is
overstated, and the module takes a whole-`Mathlib` import.

---

## 1. Gates — all pass

All commands run from the worktree after `bash scripts/lean-install.sh`
(which itself ended `== lake test` / `== OK`), `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, no `-j`, one lake at a time, always from `verification/`.

| # | command | result |
|---|---|---|
| 1 | `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.Gronwall` | `Build completed successfully (8763 jobs).`  **exit 0**.  No message mentioning `Gronwall` anywhere in the output |
| 2 | `cd verification && lake env lean ../research/A04/axioms_g3.lean` | **exit 0**, three lines, each exactly `[propext, Classical.choice, Quot.sound]` (see below) |
| 3 | `grep -n "sorry\|admit\|native_decide\|axiom\|maxHeartbeats" formalization/NSFormalization/Section4/A04/Gronwall.lean` | **no hits at all** (not even in comments).  In `research/A04/axioms_g3.lean` the only hits are the three `#print axioms` commands and the doc line naming them |
| 4 | `make check` | **exit 0** — `check_formalization_plan.py --check`, `check_contracts.py`, `test_contract_policy.py` (13 tests OK), `check_work_queue.py` (`30 work items: … consistent`) |
| 5 | `cd verification && lake env lean /tmp/g3rev/pristine.lean` (byte copy of the module, forces full re-elaboration rather than a cache replay) | **zero output** — no errors, no warnings, no linter notes |

Axiom audit verbatim:

```
'NSFormalization.Section4.A04.gronwall_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.gronwall_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.gronwall_integral_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 2. Statements — correct and sharp

Actual declaration lines are `:54`, `:156`, `:186` (the briefing said
`:56/:154/:189`; off by one or two, no consequence).

**`gronwall_integral` (:54).**  `t₀ ≤ t₁`; `y, c, b` `ContinuousOn (Icc t₀ t₁)`;
`c ≥ 0` and `b ≥ 0` **on `Icc t₀ t₁`** (pointwise, not just at endpoints — the
right form); **no `y ≥ 0`**; hypothesis
`∀ t ∈ Icc t₀ t₁, y t ≤ y t₀ + ∫_{t₀}^{t}(c·y + b)`; conclusion
`∀ t ∈ Icc t₀ t₁, y t ≤ (y t₀ + ∫_{t₀}^{t} b)·exp(∫_{t₀}^{t} c)`.  This is the
textbook variable-coefficient Grönwall, quantifiers and interval included.  The
integral orientation is `t₀..t` with `t₀ ≤ t` throughout, so no sign trap.
Totality is not an issue: `c`, `b`, `y` continuous on a compact interval are
interval-integrable, so no `∫ = 0`-on-non-integrable artefact.

Four scratch checks were elaborated against the built module
(`lake env lean /tmp/g3rev/scratch_g3.lean`, **exit 0, no output**):

* **(a) sharpness / non-vacuity.**  `c ≡ 1`, `b ≡ 0`, `y = Real.exp`: the
  hypothesis holds with *equality* (`exp t₀ + ∫_{t₀}^{t} exp = exp t`), and the
  conclusion delivers exactly `exp t ≤ exp t₀ * exp (t − t₀)` — equality.  The
  exponent and the `y t₀` factor are both right, and the bound is attained.
* **(b) no hidden `y ≥ 0`.**  Same instance with `y = fun s => -Real.exp s`:
  hypothesis holds with equality, conclusion is
  `-exp t ≤ (-exp t₀) * exp (t − t₀)` — again equality.  The theorem is correct
  and sharp at negative `y`, confirming `ATTEMPTS_G3.md`'s claim that `y ≥ 0`
  is genuinely not needed.
* **(c) `c ≥ 0` is necessary — negative check.**  A scratch copy of the
  statement with `hcnn` deleted was *proved false* in Lean
  (`drop_c_nonneg_is_false`).  Witness: `t₀ = 0`, `t₁ = t = 1`, `y ≡ 1`,
  `c ≡ -1`, `b ≡ 1`.  Hypothesis: `1 ≤ 1 + ∫₀¹(-1·1 + 1) = 1`, equality.
  Conclusion would read `1 ≤ (1 + ∫₀¹1)·exp(∫₀¹(-1)) = 2·e⁻¹ ≈ 0.7358` — false
  (closed from `Real.exp_one_gt_d9`).  So the sign hypothesis is load-bearing,
  not decorative.
* **(d) `b ≥ 0` is necessary — second negative check.**  Same construction with
  `hbnn` deleted is false (`drop_b_nonneg_is_false`): `y ≡ 1`, `c ≡ 1`,
  `b ≡ -1` on `[0,1]` satisfies the hypothesis with equality and the conclusion
  would read `1 ≤ (1 − 1)·e = 0`.

**`gronwall_deriv` (:156).**  Right derivative `HasDerivWithinAt y (y' x) (Ici x) x`
on the open `Ioo t₀ t₁`, `IntervalIntegrable y' volume t₀ t₁`, `y' ≤ c·y + b` on
`Ioo`.  FTC-2 is applied through
`integral_eq_sub_of_hasDeriv_right_of_le` with `.mono Ioi_subset_Ici_self`
(right direction: `Ioi x ⊆ Ici x`), and the sub-interval restrictions
(`Icc_subset_Icc le_rfl ht'.2`, `uIcc_subset_uIcc_left`) are correct.  At
`t = t₀` the conclusion degenerates to `y t₀ ≤ y t₀`; nothing is asserted about
the endpoints beyond what the hypotheses give.

**`gronwall_integral_mul` (:186).**  `0 ≤ Cgron`, `k ≥ 0` continuous, coefficient
`Cgron * k s`, conclusion `y t ≤ (y t₀ + ∫ b)·exp(Cgron · ∫ k)`.  The hypothesis
term is parsed `(Cgron * k s) * y s + b s`, which is **the same parse, symbol for
symbol**, as `Spec.lean:501-503`'s
`Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 * sobolevNormAt (m:ℝ) w.velocity s
+ sobolevNormAt (m:ℝ) f s`.  `0 ≤ Cgron m ν` is free from `Spec.lean:356`
`Cgron_pos`.  A consumer can apply it with no `ring_nf` massaging.

## 3. Fit for A04 — continuity is available; the `L¹` version is not needed

**Answer: the continuous version suffices for `higherOrderBound` exactly as
specified in `research/A04/Spec.lean`.**  Reasons, checked against the sources:

1. **The coefficient is continuous on every compact subinterval, from the
   contract alone.**  `Contracts/V1/Data.lean:642-644`, `ClassicalSolutionR.sobolev`,
   gives for every integer `m` a datum path `G` with `ContinuousOn G (Ico 0 T)`.
   Hence `s ↦ sobolevNormAt m u s = ‖G s‖` is continuous on `Ico 0 T`, and so is
   its square — this is `COMPARISON.md` row **N1**, implemented in lane 039
   (`Section4/A04/Continuity.lean`, not yet on this branch; `ATTEMPTS_F1N1.md`
   is not present here).  Note this does **not** need the `C^∞`-in-time
   smoothness the module docstring (`:24-27`) appeals to: plain `ContinuousOn`
   from `ClassicalSolutionR.sobolev` already delivers it.  The docstring's
   justification is correct but weaker than what is actually on hand.
2. **The inhomogeneity is continuous on compacts of `[0,∞)`.**
   `Data.lean:544` `MemForceR` carries `ContDiffOn ℝ ∞ G futureTimes`
   (`futureTimes = Ici 0`), so `s ↦ sobolevNormAt m f s` is continuous on every
   `Icc 0 t₁ ⊆ Ici 0`.  This is `COMPARISON.md` row **F1** / lane 039's
   `Forcing.lean`.
3. **Grönwall is never applied up to `S`.**  `higherOrderBound`
   (`Spec.lean:657` region, conclusion `∀ t ∈ Ico 0 S, sobolevENorm m (u t ·) ≤ M`)
   quantifies **strictly below** `S`, and `SolvesBelow` (`Spec.lean:~225`)
   supplies a `ClassicalSolutionR ν a f b` with `w.velocity = u` for *every*
   `b < S`.  So for each `t < S` one picks `t < b < S`, and the whole Grönwall
   step lives on the compact `Icc 0 t ⊂ Ico 0 b`, where both coefficients are
   continuous by (1) and (2).  The velocity is undefined at `S` by design
   (`Spec.lean` on `squaredHTwoIntegral`, citing `STATEMENTS.md` §9 item 15), so
   there is no statement at `t = S` that would force an `L¹`-only argument.
4. **The `L¹`/locally-integrable character of `c` is used only quantitatively,
   at the assembly step.**  Grönwall returns
   `(y 0 + ∫_0^t b)·exp(Cgron·∫_0^t k)`; the single finite `M` comes from
   `∫_0^t k ≤ (squaredHTwoIntegral S u).toReal < ∞` (eq:criterion) and
   `∫_0^t b ≤ ‖f‖_{L¹_t H^m} < ∞` (`MemL1Hm`), both uniform in `t < S`.  Those
   are *bounds on* the integrals, not hypotheses inside the Grönwall lemma.
   This is precisely the split `ATTEMPTS_G3.md` and the module docstring claim,
   and it holds.

   The residual glue is the `ℝ≥0∞ ↔ ℝ` bridge — relating
   `∫ s in 0..t, sobolevNormAt 2 u s ^ 2` (Bochner, real) to
   `squaredHTwoIntegral S u` (a lower Lebesgue integral over `Ioo 0 S`), and the
   same for `forceSobolevENormL1`.  That is units **N1**/**F1**, not G3's job,
   but it is what still stands between G3 and `higherOrderBound`.

**When would the `L¹` version be genuinely needed?**  Only if a consumer needed
the bound *at* `S`, or on an interval where the coefficient is merely integrable
with no continuous representative.  Neither occurs: `higherOrderBound`,
`extendsBeyond` and `lifespanInfiniteOfLocallyFinite` are all stated on
`Ico 0 S` / on horizons strictly below the lifespan, and the paper's own
sentence at `appendix-a-local-theory.tex:146-147` ("Grönwall bounds every `H^m`
norm uniformly up to `S`") is a *uniform* bound on `[0,S)`, which is exactly
what the continuous lemma plus the sup over `t₁ ↑ S` delivers.  Restating G3
with `IntervalIntegrable` coefficients would be a strictly larger campaign for
no consumer.

**Accuracy of `ATTEMPTS_G3.md`'s a.e.-FTC obstacle claim: essentially accurate,
one word overstated.**  Verified:

* `antitoneOn_of_hasDerivWithinAt_nonpos`
  (`Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:496`) demands
  `∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x` — *every* interior
  point, as claimed.  `integral_eq_sub_of_hasDeriv_right_of_le` likewise demands
  the right derivative at every point of `Ioo`.
* The null set where the indefinite integral of an `L¹` function fails to be
  differentiable can indeed be uncountable, so countable-exception variants would
  not rescue the argument.

The overstatement is the sentence "*A rigorous integrable-coefficient proof
therefore **needs** the absolutely-continuous / a.e.-FTC toolkit*".  It does not
*need* it: the classical Picard-iteration proof of Grönwall (iterate
`y ≤ A + ∫ c·y`, evaluate the `n`-fold iterated kernel on the simplex as
`(∫c)ⁿ/n!` by Fubini/symmetry, sum the series) uses no FTC at all and needs only
`c ≥ 0`, measurability and boundedness of `y`.  It would still be a large Lean
campaign and A04 still does not need it, so the *decision* recorded in the log is
right; only the word "needs" should be softened to "is the route we would take".

## 4. Findings

**1. MEDIUM — the prior-art claim is wrong: a variable-coefficient Grönwall
already exists in the vendored package.**
Declaration: `ATTEMPTS_G3.md` §"Routes considered and rejected" item 1; module
docstring `Gronwall.lean:10-18` ("genuinely new to this repository and to
Mathlib's ODE folder" is the phrasing in `COMPARISON.md:215`); `COMPARISON.md`
row **G3**.
What is wrong: all three say the only in-tree Grönwall is the constant-`K`
wrapper `EulerOrdinarySobolev.linear_stability_within`
(`vendor/NavierStokesAndEuler/Euler/OrdinaryEulerL2Stability.lean:46`).  But
`vendor/NavierStokesAndEuler/Euler/OrdinaryVariableGronwall.lean:14`,
`EulerOrdinarySobolev.variable_linear_stability`, is a genuine
**variable-coefficient** Grönwall:

```
theorem variable_linear_stability (T : ℝ) (hT : 0 ≤ T)
    (X X' : ℝ → ℝ) (C : ℝ) (K : C(Icc (0:ℝ) T, ℝ))
    (hcont : ContinuousOn X (Icc 0 T))
    (hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt X (X' t) (Icc 0 T) t)
    (hineq : ∀ t ∈ Ico 0 T, X' t ≤ C * extendPath T hT K t * X t)
    (t : Icc (0:ℝ) T) :
    X t ≤ X 0 * Real.exp (C * realIntegral T hT K t)
```

`sorry`-free, and proved by *the same* integrating-factor route (`Y = X·exp(-C∫K)`
antitone).  It is not a substitute for G3 — it is homogeneous (`b = 0`), only in
differential form, anchored at `t₀ = 0`, and bundles the coefficient as a
`C(Icc 0 T, ℝ)` with the vendor's `extendPath` / `realIntegral` plumbing, so it
cannot state, let alone discharge, `higherOrderBound`'s inhomogeneous
`+ ‖f‖_{H^m}` term.  The lane's work is still needed.  But the record should say
so, and the fact that the identical route is already carried in tree is a
positive signal worth keeping.
Fix (documentation only, no code change): in `ATTEMPTS_G3.md` route 1 and in
`COMPARISON.md` row G3, name `EulerOrdinarySobolev.variable_linear_stability`,
state the three reasons it does not cover A04 (inhomogeneous term, `t₀ = 0`,
bundled-`C(·,ℝ)` coefficient), and drop "genuinely new to this repository" from
`COMPARISON.md:215` and the equivalent claim in the module docstring.  Note also
that it needs no sign condition on `K`, precisely because `b = 0` — which is a
nice cross-check on finding-(d) above: the sign hypotheses in G3 are forced by
the inhomogeneity.

**2. LOW — "needs the a.e.-FTC toolkit" is stronger than justified.**
Declaration: `ATTEMPTS_G3.md` route 2, first bullet.
Fix: soften to "is the route we would take"; mention the FTC-free Picard
iteration as the alternative if a consumer ever needs `b ∈ L¹` or `c ∈ L¹`.  See
§3 above.  Everything else in route 2 (including the partial relaxation sketch
"`c` continuous, `b` only integrable *is* provable") checks out.

**3. LOW — whole-`Mathlib` import in a `formalization/` module.**
Declaration: `Gronwall.lean:1`, `import Mathlib`.
12 of the 370 `NSFormalization` modules do this (`Citations/*`, several
`Paper1/*`), so it has precedent and `make check`/`check_contracts.py` do not
object — but every other `Section4/*` module uses narrow imports, and this module
will sit in the import closure of the A04 consumers.  The file needs only
`Mathlib.Analysis.Calculus.Deriv.MeanValue`,
`Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` and
`Mathlib.Analysis.SpecialFunctions.ExpDeriv`.
Fix (optional): narrow the import before the A04 consumers land on top of it.

**4. LOW — the docstring reads as self-contradictory on first pass.**
Declaration: `Gronwall.lean:15-18` vs `:22-28`.  Lines 15-18 say the paper's
coefficient "is only `L¹` in time"; lines 22-28 then require it continuous.
Both are true (globally `L¹` on `(0,S)`; continuous on each compact
subinterval), and `:26-28` does say so, but a reader hits the tension before the
resolution.
Fix: add "on every compact subinterval of `(0,S)` it is in fact continuous"
to the first paragraph, or move the sentence.

**No findings against the Lean statements or proofs.**  Nothing was changed by
this review; no code was fixed.

## 5. Honesty spot-checks of `ATTEMPTS_G3.md`

Four of the four recorded failures/fixes were reproduced (two were required):

| claim | check | result |
|---|---|---|
| "`continuousOn_primitive_interval'` needs `(μ := volume)` given explicitly, else the `IsLocallyFiniteMeasure` instance is stuck on a metavariable" | mutant copy with `(μ := volume)` deleted | **exactly reproduced**: `mut_mu.lean:64:7: error: typeclass instance problem is stuck  IsLocallyFiniteMeasure ?m.160` |
| "an extra `simp only []` there errors with 'made no progress'" | mutant copy with `simp only []` inserted before `exact ((hY.mul hE).sub hK).hasDerivWithinAt` | **exactly reproduced**: `mut_simp.lean:105:6: error: `simp` made no progress` (plus the knock-on `linarith` failure at `:113`) |
| "Mathlib's ODE Grönwall lemmas take a constant `K`; the file's own TODO says the variable-coefficient version is absent" | read `Mathlib/Analysis/ODE/Gronwall.lean` | **accurate**: `:112` and `:134` both take `{δ K ε : ℝ}`; the TODO at `:25-29` reads "Once we have FTC, prove an inequality for a function satisfying `‖f' x‖ ≤ K x * ‖f x‖ + ε` … with any sign of `K x` and `f x`" |
| "`ContinuousOn.intervalIntegrable` wants `uIcc`; on `Icc` use `.intervalIntegrable_of_Icc h`" | read `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` | **accurate**: `:504` takes `ContinuousOn u (uIcc a b)`, `:508` `intervalIntegrable_of_Icc` takes `(h : a ≤ b)` |

The "What was proved" and "Hypotheses actually needed vs. the paper" sections
match the delivered file in every particular I checked, including the two sign
hypotheses (independently confirmed necessary in §2 (c)/(d)) and the absence of
`y ≥ 0` (confirmed in §2 (b)).

## 6. Bookkeeping

The lane commit touches exactly three files and no generated/shared file
(`PLAN.md`, `logs/AGENT_RUNS.csv`, `collaboration/*`, `verification/contracts.json`
are all untouched) — correct per `CLAUDE.md`, where the lead appends the CSV row
and the PLAN row at merge time.

## 7. Commands, verbatim

```
cd .claude/worktrees/041-A04-unit-g3
bash scripts/lean-install.sh                      # ends "== lake test" ... "== OK"
. scripts/lean-env.sh

cd verification
LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.Gronwall
#   Build completed successfully (8763 jobs).     exit 0, no Gronwall message

lake env lean ../research/A04/axioms_g3.lean
#   three [propext, Classical.choice, Quot.sound] lines, exit 0

lake env lean /tmp/g3rev/pristine.lean            # byte copy, full re-elaboration
#   (no output)                                   exit 0, no warnings

lake env lean /tmp/g3rev/scratch_g3.lean          # 4 sanity/negative checks
#   (no output)                                   exit 0 — all four accepted

lake env lean /tmp/g3rev/mut_mu.lean              # (μ := volume) removed
#   error: typeclass instance problem is stuck  IsLocallyFiniteMeasure ?m.160
lake env lean /tmp/g3rev/mut_simp.lean            # simp only [] inserted
#   error: `simp` made no progress

cd .. && grep -n "sorry\|admit\|native_decide\|axiom\|maxHeartbeats" \
  formalization/NSFormalization/Section4/A04/Gronwall.lean
#   (no hits)

make check
#   check_formalization_plan --check / check_contracts / test_contract_policy (13 OK)
#   / check_work_queue "30 work items: ... consistent"      exit 0
```
