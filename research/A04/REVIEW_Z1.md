# A04 unit Z1 — review

Module under review: `formalization/NSFormalization/Section4/A04/Regularized.lean`
(lane 043, commit `2504f6d`, base `c955e5e`).
Declarations: `regularized_sqrt_deriv` (`:55`), `sqrt_le_primitive_linear` (`:87`).
Records: `research/A04/ATTEMPTS_Z1.md`, `research/A04/axioms_z1.lean`.

## Verdict

**ACCEPT-WITH-NOTES.**

Both statements are faithful to the manuscript's ζ device and to the two
consumers (A04 `regularizedNormDerivative` / `highContinuationIntegral`, C01
`energyDifferentialBound` / `l2Bound`). The proofs are complete, warning-free,
axiom-clean, and the factor-2 convention is the right one. Every finding below
is documentation or ergonomics; none is a mathematical defect and none blocks a
merge. Findings 1 and 2 are wrong statements *in the records*, which is why the
verdict is not a plain ACCEPT.

## 1. Build, axioms, hygiene — all pass

```
$ cd WT && bash scripts/lean-install.sh          # elan + cache + lake test
… == OK                                           (exit 0; `lake test` green)

$ . WT/scripts/lean-env.sh; export LEAN_NUM_THREADS=6
$ cd WT/verification && lake build NSFormalization.Section4.A04.Regularized
Build completed successfully (2666 jobs).         (exit 0, 0.77 s warm)

$ lake env lean ../formalization/NSFormalization/Section4/A04/Regularized.lean
                                                  (no output at all: 0 errors,
                                                   0 warnings, 0 infos; 2.0 s)

$ lake env lean ../research/A04/axioms_z1.lean
'NSFormalization.Section4.A04.regularized_sqrt_deriv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.sqrt_le_primitive_linear' depends on axioms:
  [propext, Classical.choice, Quot.sound]

$ grep -nE 'sorry|admit|native_decide|axiom|maxHeartbeats' \
    formalization/NSFormalization/Section4/A04/Regularized.lean
(none)
# the only `axiom` hits across the diff are `#print axioms` in axioms_z1.lean
# and prose in ATTEMPTS_Z1.md.

$ cd WT && make check
… 30 work items: ownership, contract registration and task cards consistent.
                                                  (exit 0)

$ python3 experiments/build_changed_lean.py --base-ref c955e5e
Changed Lean modules: NSFormalization.Section4.A04.Regularized
Build completed successfully (2666 jobs).         (exit 0)
```

The last command matters: the new module is not imported by `Contracts`/`Tests`
and `NSFormalization.lean` does not reach `Section4`, so it is outside the
registered test closure — but CI's "Compile changed modules outside the
registered test closure" step does build it. No wiring gap.

`git diff --name-only c955e5e HEAD` is exactly the three files; working tree clean.

## 2. Statements against the paper and the consumers — correct

* `appendix-a-local-theory.tex:140-145`: "Young's inequality and division by the
  regularized norm `(‖u‖²_{H^m}+ζ²)^{1/2}`, followed by `ζ↓0`", giving
  eq:highcontinuation. `regularized_sqrt_deriv` is the fixed-ζ half
  (`(√(E+ζ²))' ≤ K√(E+ζ²) + b`) and `sqrt_le_primitive_linear` the post-limit
  integrated half. Both match `research/A04/COMPARISON.md:213`'s unit Z1 brief
  verbatim.
* Forward derivative: `regularized_sqrt_deriv` takes and returns
  `HasDerivWithinAt … (Ici t) t`. Taking it one-sided is a strict improvement
  (a consumer holding `HasDerivAt` passes `.hasDerivWithinAt`); see finding 5
  for the conclusion side.
* **Factor-2 convention is right.** Typechecked both feeds (scratch, deleted):
  - C01 `energyDifferentialBound` is `E' + 2ν‖∇u‖₂² ≤ 2‖f‖₂‖u‖₂` with
    `l2Norm z = √(l2Sq z)`, so with `E = l2Sq ∘ u` the hypothesis
    `E' ≤ 2(K·E + b·√E)` holds with `K = 0`, `b = ‖f‖₂` — dropping the
    nonnegative dissipation. `nlinarith [mul_nonneg hν.le hG]` closes it.
  - A04 `energyIdentityHigh` is `½d + ν‖∇u‖²_{H^m} ≤ C_m y X G + F X`
    (`y = ‖u‖_{H²}`, `X = ‖u‖_{H^m} = √E`, `F = ‖f‖_{H^m}`). Young
    (`νG² + C²y²X²/(4ν) − CyXG = (2νG − CyX)²/(4ν) ≥ 0`) gives
    `d ≤ 2(K·X² + F·X)` with `K = C²y²/(4ν)` — i.e. `Cgron m ν = Chigh m ²/(4ν)`,
    exactly unit G2's constant. The `½` on the paper's identity is precisely why
    Z1's hypothesis carries the `2`.
* **Integrated form is what the consumers need, with `E t₀ ≠ 0`.** The
  conclusion `√(E t) ≤ √(E t₀) + ∫(K√E + b)` is literally
  `highContinuationIntegral`'s bound (`t₀` arbitrary in `[0,t]`) and, at
  `K = 0`, literally `l2Bound`/eq:RL2 (`‖u(t)‖₂ ≤ ‖a‖₂ + ∫‖f‖₂`,
  `04-whole-space.tex:118-120`) and `04-whole-space.tex:102`
  (`y(t) ≤ y(0) + ∫b`, "including times at which `y = 0`").
* **No hidden `E t₀ = 0`.** The endpoint step is
  `hsqrtt0 : √(E t₀ + δ²) ≤ √(E t₀) + δ` (`:165-172`), valid for any
  `E t₀ ≥ 0`; the vanishing case is not special-cased anywhere. Confirmed
  empirically by the instance below, whose `E t₀ = 1`.
* **Positive instance (equality case).** `E = fun t => t²`, `E' = fun t => 2t`,
  `K = 0`, `b = 1` on `Icc 1 2`. Hypothesis `2t ≤ 2(0·t² + 1·√(t²)) = 2t` holds
  with equality; conclusion `√(t²) ≤ √(1²) + ∫₁ᵗ 1`, i.e. `t ≤ 1 + (t−1) = t`,
  also equality. Both the application of `sqrt_le_primitive_linear` and the
  evaluation of the right-hand side to `t` typecheck. So the lemma is sharp
  here and not vacuous.
* **Negative check — `0 ≤ b` is load-bearing.** Two independent confirmations:
  1. The proof breaks if `hbnonneg` is deleted, and breaks exactly where it
     should: recompiling the theorem body with that hypothesis removed gives
     one error, `Unknown identifier 'hbnonneg'` at `have hbx : 0 ≤ b x`
     (`:148`), nowhere else.
  2. The statement is then **false**, not merely unproved. Typechecked
     counterexample: `t₀ = 0`, `t₁ = 1`, `E ≡ 0`, `E' ≡ 0`, `K ≡ 0`, `b ≡ −1`.
     The hypothesis reads `0 ≤ 2(0·0 + (−1)·√0) = 0`, true; the conclusion at
     `t = 1` would read `0 ≤ 0 + ∫₀¹(−1) = −1`, false. (Proved as
     `¬ (∀ …)`, sorry-free.)

## 3. Relation to the Paper 1 template and to lane 041

* **`Paper1.sqrt_energy_le_primitive` (`Paper1/ScalarEnergy.lean:22`) is
  recoverable only with two extra hypotheses.** I typechecked the derivation
  (scratch, deleted): with `K = 0`, `sqrt_le_primitive_linear` plus
  `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` (to identify
  `∫₀ᵗ b` with `N t − N 0`) reproduces it — but only after adding
  `ContinuousOn b (Icc 0 T)` and `∀ t ∈ Icc 0 T, 0 ≤ b t`. Paper1 assumes
  neither: it takes an abstract primitive `N` with `HasDerivAt N (b t) t` on
  `Ioo` and nonnegativity on `Ioo` only, and never requires `b` continuous or
  integrable. See finding 4.
* **The `ContinuousOn` strengthening is exactly lane 041's.** `Gronwall.lean`
  (commit `da5b6c2`) `gronwall_integral` takes
  `hy, hc, hb : ContinuousOn … (Icc t₀ t₁)` with `hcnn, hbnn` on `Icc` — the
  same shape, same reason (an everywhere-defined derivative of the primitive,
  not an a.e. one). The two units compose with no glue: Z1's conclusion is
  literally G3's `hstep` with `y = fun s => √(E s)`, `c = K`, and
  `ContinuousOn y` is `hE.sqrt`. I typechecked that chaining.
* **Available at the consumers.** `COMPARISON.md:208` unit N1 asserts
  `t ↦ sobolevNormAt s u t` is continuous on `Ico 0 T`, and the same for `f`
  under `MemForceR`. Hence `E = ‖u(·)‖²_{H^m}`, `K = Cgron·‖u(·)‖²_{H²}` and
  `b = ‖f(·)‖_{H^m}` are all `ContinuousOn (Icc t₀ t₁)` for any
  `[t₀,t₁] ⊆ [0,T)`. The hypothesis is affordable where Z1 is consumed.

## 4. Honesty spot-checks of `ATTEMPTS_Z1.md`

* `continuousOn_primitive_interval'` namespace — **confirmed**. Under the
  file's `open Set MeasureTheory Topology`, `#check @continuousOn_primitive_interval'`
  fails with `Unknown identifier`; the `intervalIntegral.` prefix used at `:108`
  is required. (It resolves bare only after `open intervalIntegral`.)
* `positivity` on `0 < E t + ζ²` — **not confirmed; the record is wrong.**
  See finding 1.

## Findings

### 1. `ATTEMPTS_Z1.md:90-93` states a `positivity` failure that does not happen — LOW (record accuracy)

*What is wrong.* The bullet "`positivity` for `0 < E t + ζ²` and `0 < 2√(E+δ²)`:
fails, because `positivity` cannot see `E t ≥ 0` (a hypothesis, not syntactic)
nor `ζ ≠ 0`" is false at this pin. Mathlib's `positivity` core falls back to
scanning the local context for atoms, so with `hζ : 0 < ζ` and `hEt : 0 ≤ E t`
in scope it proves both goals. Verified:

```
example (E : ℝ → ℝ) (t ζ : ℝ) (hζ : 0 < ζ) (hEt : 0 ≤ E t) : 0 < E t + ζ ^ 2 := by
  positivity                                        -- exit 0
example (E : ℝ → ℝ) (x δ : ℝ) (hδ : 0 < δ) (hEx : 0 ≤ E x) :
    0 < 2 * Real.sqrt (E x + δ ^ 2) := by positivity -- exit 0
example (E : ℝ → ℝ) (x δ : ℝ) (hδ : 0 < δ) : 0 < E x + δ ^ 2 := by
  positivity  -- error: failed to prove positivity/nonnegativity/nonzeroness
```

Only the third (no nonnegativity hypothesis) fails. Independent corroboration:
the very template this unit generalizes already uses `by positivity` for the
second goal — `Paper1/ScalarEnergy.lean:56`.

*Fix.* Replace the bullet with an accurate one (e.g. "`positivity` does close
both goals here via its local-hypothesis fallback; the explicit
`pow_pos`/`linarith` and `mul_pos` were kept for readability"), or delete it.
No change to `Regularized.lean` is needed — the explicit proofs are fine.

### 2. Stale paper citation carried into the module docstring — LOW (documentation)

*Where.* `Regularized.lean:12-13` ("`paper/sections/appendix-a-local-theory.tex:139-146`,
reused at `02-preliminaries.tex:152` and `04-whole-space.tex:103,121`").

*What is wrong.* `02-preliminaries.tex:152` is the unrelated paragraph "The
temporal support of `F` is a compact subset of `(0,∞)`…". The ζ device is at
**`:143`** ("For `ζ>0`, the derivative of `(‖U‖₂²+ζ²)^{1/2}` is at most `‖F‖₂`").
`grep -n zeta paper/sections/02-preliminaries.tex` returns line 143 only.
Secondary drift: `04-whole-space.tex:103` is the closing `\]` of the display at
`:102` (the ζ sentence is `:100`), and `:121` is the sentence *after* eq:RL2,
which occupies `:118-120`. The appendix range `:139-146` does bracket the right
material.

*Origin.* Inherited from `research/A04/COMPARISON.md:213` and
`research/A04/Spec.lean:456`, i.e. pre-existing drift, not introduced here —
but the new module propagates it.

*Fix.* Cite `02-preliminaries.tex:143`, `04-whole-space.tex:100-102` and
`:117-120`; optionally correct the two upstream files in the same pass.

### 3. `hKnonneg` / `hbnonneg` are stated on `Icc` but used only on `Ioo` — LOW (ergonomics)

*Where.* `sqrt_le_primitive_linear` (`:93-94`); the only uses are `:147-148`,
both under `hx : x ∈ Ioo t₀ t₁`.

*What is wrong.* Nothing mathematically, but the hypotheses are stronger than
the proof needs. Weakening both to `∀ t ∈ Ioo t₀ t₁, …` and changing the two
use sites from `hKnonneg x hxmem` / `hbnonneg x hxmem` to `… x hx` compiles
with no other edit (verified: a namespaced copy with exactly those four
substitutions elaborates clean, exit 0). Note `hEnonneg` genuinely needs the
closed interval — it is applied at `t₀` in `hsqrtt0` (`:166`).

*Why it matters.* This is one of the two hypotheses that currently stop Z1 from
subsuming `Paper1.sqrt_energy_le_primitive`, which assumes `0 ≤ b` on `Ioo`
only (finding 4). It also matches the paper more closely: the differential
inequality is asserted at interior times.

*Fix.* Weaken `hKnonneg` and `hbnonneg` to `Ioo t₀ t₁`.

### 4. "Generalizes `Paper1.sqrt_energy_le_primitive`" overstates the relation — LOW (documentation)

*Where.* `Regularized.lean:14-16`.

*What is wrong.* Z1 generalizes in the two advertised directions (linear term,
no `E t₀ = 0`) but **restricts** in two others, so the Paper 1 lemma is not a
corollary and cannot be retired:

1. Z1 requires `ContinuousOn b (Icc t₀ t₁)`; Paper1 requires nothing of `b`
   beyond nonnegativity on `Ioo` and the existence of a primitive.
2. Z1 hard-codes the primitive as the Lebesgue interval integral
   `∫ s in t₀..x, (K√E + b)`; Paper1 takes an abstract `N` with
   `HasDerivAt N (b t) t`, which is strictly more general (a derivative need
   not be the integrand of its own primitive without integrability).

I typechecked the recovery: with `ContinuousOn b` and `0 ≤ b` on `Icc` added as
hypotheses, `sqrt_le_primitive_linear (K := fun _ => 0)` plus
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` and
`simp`/`rw [hE0, Real.sqrt_zero]` reproduces `sqrt_energy_le_primitive` exactly
(exit 0, ~8 lines). Without those two additions it does not go through.

The docstring already records the continuity strengthening honestly at `:31-39`;
what is missing is the consequence.

*Fix.* One sentence at `:14-16`: Z1 does not subsume the Paper 1 lemma
(abstract primitive, no continuity of `b`); both stay. Finding 3 removes the
second obstruction.

### 5. `regularized_sqrt_deriv` returns a one-sided derivative where the A04 contract asserts a two-sided one — LOW (interface)

*Where.* `:59-60` (`HasDerivWithinAt … (Ici t) t`) versus
`research/A04/Spec.lean:459-470` `regularizedNormDerivative`, which asserts
`∃ d, HasDerivAt (fun r => √(‖u r‖²_{H^m} + ζ²)) d t ∧ d ≤ …`.

*What is wrong.* Nothing unsound — the one-sided *hypothesis* is a genuine
improvement — but because the lemma bundles the derivative with the bound, a
consumer holding `HasDerivAt` can reuse only the inequality conjunct and must
reprove the derivative:

```
obtain ⟨-, hbound⟩ := regularized_sqrt_deriv hζ hEt hKt hbt hdE.hasDerivWithinAt hineq
exact (hdE.add_const (ζ ^ 2)).sqrt (by positivity : (0:ℝ) < E t + ζ ^ 2).ne'
```

(typechecked, exit 0 — two lines, so this is a wart, not a blocker). Relatedly,
the inequality conjunct does not use `hdE` at all: it follows from `hineq`,
`hKt`, `hbt`, `hEt` alone.

*Fix (optional).* Either split the lemma into the algebraic bound (no
derivative hypothesis) plus a derivative lemma, or add a `HasDerivAt` variant
for consumers that have the two-sided derivative. If neither, leave as is and
let G2 pay the two lines.

### 6. The integrability established inside `sqrt_le_primitive_linear` is not exported — INFORMATIONAL

`hgii : IntervalIntegrable g volume t₀ t₁` (`:105`) is proved and used
internally, and A04's `highContinuationIntegral` asserts exactly this
conjunct alongside the bound (it was `REVIEW.md` finding 6 that put it there, to
avoid Mathlib's junk-`0` integral). The consumer must re-derive it from the
same `ContinuousOn` hypotheses — one line, but returning it as a second
conjunct would make the unit drop straight into the contract field. The
inequality as stated is *not* vacuous: continuity is a hypothesis, so the
integral in the conclusion is the real one.

## Scratch files

All scratch Lean used for the checks above (instance, counterexample,
hypothesis-dropping copy, `Ioo`-weakening copy, Paper 1 recovery, consumer
feeds, `positivity`/namespace probes) was written under `/tmp/z1scratch/`,
typechecked with `lake env lean`, and deleted. Nothing was added to the
worktree except this file.
