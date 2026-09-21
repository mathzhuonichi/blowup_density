# A04 — review of `research/A04/Spec.lean` and `research/A04/COMPARISON.md`

Reviewed at `78b0b99` on lane branch `030-A04-spec`, against
`erenup/integration` at `4ba9f2b` (worktree `000-integration`) for the
registered contracts.

## Verdict: **ACCEPT-WITH-NOTES**

The file typechecks clean, `make check` passes, and ten of the eleven
`ContinuationAPI` fields are faithful renderings of the manuscript on the D01
carrier. eq:Rhigh, the `ζ`-step, eq:highcontinuation, the Grönwall consequence,
the restart and `extendsBeyond` (the field `prop:Rcritical1`/`prop:Rcritical2`
actually consume, `research/section4/STATEMENTS.md:498-500`, `:606-608`) are
correct. `squaredHTwoIntegral` is exactly `∫₀^S‖u(t)‖²_{H²}dt` in the paper's
convention. Nothing smuggles in a spectral gap, a Poincaré constant or a mean
reduction.

Two statement defects, both in the single field
`lifespanInfiniteOfLocallyFinite`, must be fixed before this is registered
(findings 1 and 2). One rework is now forced by a merge that landed after the
draft was written (finding 3).

---

## Findings

### 1. **MAJOR** — `lifespanInfiniteOfLocallyFinite`: the criterion hypothesis is quantified over *all* `S`, which is stronger than the paper and cannot be supplied by R43

`Spec.lean:538-540` asks for

```lean
(∀ S : ℝ, 0 < S → squaredHTwoIntegral S u ≠ ⊤)
```

The manuscript (`04-whole-space.tex:121`) says: "For every finite `S` **within
or at the maximal lifespan**, `K(S) < ∞`, and … `∫₀^S‖u‖²_{H²}dt < ∞`."  The
restriction is not decorative.  The hypothesis on `u` in this same field pins
`u` only at horizons `b` with `ofReal b < maximalLifespanR`; at a finite
lifespan `T`, the field `u` is entirely unconstrained on `[T,∞)`
(`research/A02/Spec.lean:210` `IsMaximalSolution` does not pin it either), and
`sobolevENorm` is fail-safe to `⊤` there.  C01's assembly
(`04-whole-space.tex:122-128`) derives the integral bound only on the interval
where the solution exists, so **R43 cannot discharge this hypothesis** at any
`S` past a hypothetical finite lifespan — which is exactly the case the field is
supposed to rule out.  As an obligation on the implementer the extra strength
also makes the field weaker than `prop:local`.

*Fix.*  Restrict to the manuscript's range, e.g.

```lean
(∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanR ν a f →
    squaredHTwoIntegral S u ≠ ⊤)
```

The field stays provable: the derivation the docstring describes ("by
contradiction at a finite supremum") only ever instantiates the hypothesis at
`S = T^ν_{max,R}`, where `ofReal S ≤ maximalLifespanR` holds.

### 2. **MAJOR** — `lifespanInfiniteOfLocallyFinite` drops A02's lifespan-positivity clause, so the field is false at a degenerate datum

`Spec.lean:536-537` writes the solution family out inline:

```lean
(∀ b : ℝ, 0 < b → ENNReal.ofReal b < maximalLifespanR ν a f →
    ∃ w : ClassicalSolutionR ν a f b, w.velocity = u ∧ w.pressure = p)
```

This is `IsMaximalSolution`'s second clause (`research/A02/Spec.lean:212-215`)
**without its first clause** `0 < maximalLifespanR ν a f`.  A02's docstring
(`:180-183`) states precisely why that clause is there: "without it the second
clause is vacuously true of every pair when the datum carries no solution at
all, since the empty supremum of `maximalLifespanR` is `0`."

Consequence: at any `(ν,a,f)` with `0 < ν`, `a ∈ initialClassR`,
`MemForceR f` and `maximalLifespanR ν a f = 0`, take `u = 0`, `p = 0`.  The
family hypothesis is vacuous, `squaredHTwoIntegral S 0 = 0 ≠ ⊤` for every `S`,
and the conclusion asserts `0 = ⊤`.  The field is therefore **not provable from
inside `ContinuationAPI`**; it silently rests on A01's existence half
(`research/A01/Spec.lean:287` `solution`) to rule out such a datum.  No other
field has this problem — `extendsBeyond` and `higherOrderBound` get positivity
for free from `SolvesBelow` at `0 < S`.

*Fix.*  Add `0 < maximalLifespanR ν a f` as a hypothesis (or take
`IsMaximalSolution`-shaped data), so the field is self-contained and matches the
A02 predicate it is transcribing.

### 3. **MODERATE** — the `⟪A03:…⟫` mirrors are now stale: `Contracts.V1.TameProduct` is merged and registered

The draft restates seven A03 objects "because `Contracts/V1/TameProduct.lean` is
not on `erenup/integration` at the time of writing (it is PR #31)"
(`Spec.lean:68-71`, `:104-107`, `:306-308`; `COMPARISON.md` §2 `outerProductTame`
row and §3).  That is no longer true.  On `erenup/integration` at `4ba9f2b` the
file exists at `verification/Contracts/V1/TameProduct.lean` and is registered in
`verification/contracts.json` as `A03.tame_products` (binding `Bindings.TameProduct`,
test `Tests.TameProduct`).

I compared the mirrors against the registered file.  They are **symbol for symbol
identical** — `lift` (`:154`), `partialDeriv` (`:158`), `outerColumn` (`:169`),
`columnsSobolevENorm` (`:178`), `outerSobolevENorm` (`:182`),
`gradientSobolevENorm` (`:192`), `MemHmVector` (`:141`) — and
`ContinuationAPI.outerProductTame` is `TameProductAPI.outerProductTame`
(`TameProduct.lean:345`) verbatim up to the constant name (`Chigh` vs `Ctame`).
So the draft's own exit condition is met.

*Fix.*  Merge `erenup/integration` into the lane branch (the worktree does not
yet contain `verification/Contracts/V1/TameProduct.lean` at all), then
`import Contracts.V1.TameProduct`, delete the seven mirror `def`s from §1,
and replace the `outerProductTame` field with `tame : TameProduct.TameProductAPI`
as `Spec.lean:70-71` promises.

*Sub-note.*  The present draft identifies eq:Rhigh's `C_m` with the tame constant
by reusing `Chigh` in both `energyIdentityHigh` and `outerProductTame`.  After
the import those become two constants (`Chigh` and `tame.Ctame`).  That is
harmless — the manuscript does not require them equal — but decide explicitly:
either keep `Chigh` opaque, or delete it and state `energyIdentityHigh` with
`tame.Ctame`.  Do not leave a silent mismatch in the docstring, which currently
claims "`Chigh` above may be taken to be `Ctame`".

### 4. **MODERATE** — the structure carries `boundedRepresentative` but not the A01/A02 APIs its own fields equally require

`Spec.lean:344-347` justifies carrying `boundedRepresentative` as a field
"because it is an input of the *derivations* below rather than of their
statements", citing `MaximalSolutionAPI.uniqueness` as precedent.  By that rule
three more inputs should be fields, and are not:

* `energyIdentityHigh` and `regularizedNormDerivative` assert that
  `r ↦ ‖u(r)‖²_{H^m}` is *differentiable*.  `ClassicalSolutionR.sobolev`
  (`Data.lean:643`) gives only `ContinuousOn` of the datum path; the
  `C^∞`-in-time datum path is A01's
  `ManuscriptLocalRegularity` clause.  `COMPARISON.md` §4 unit **D1** says this
  in as many words ("**gap**. `ClassicalSolutionR.sobolev` gives only
  `ContinuousOn`; the `C^∞`-in-time datum path is A01's clause").
* `restartBeyond` is A02's `restart` + `restart_datum` + `restart_force` +
  `uniqueness` cashed at the endpoint (`COMPARISON.md` §3, unit **R1**).
* finding 2 above is the third instance.

The precedent cited actually cuts the other way: `MaximalSolutionAPI`
(`research/A02/Spec.lean:312-336`) restates A01's `horizon`, `localSolution` and
`horizonLowerBound` and carries `uniqueness : UniquenessAPI`.  This is not a
fidelity error — the statements are true — but it means a would-be implementer
of `ContinuationAPI` in isolation cannot discharge three fields.  Either carry
`maximal : MaximalSolutionAPI` (which subsumes A01's three fields), or state in
the header why the asymmetry with `boundedRepresentative` is deliberate.

### 5. **MINOR** — `MemL1Hm` and `BoundedIntoHOne` are redundant hypotheses

`MemForceR` (`Data.lean:544`) already contains `MemLp G 1 forceTimeMeasure` for
every integer `m`, which gives `forceSobolevENormL1 (m:ℝ) f ≠ ⊤`, i.e. `MemL1Hm f`;
and its `ContDiffOn ℝ ∞ G futureTimes` gives `BoundedIntoHOne (Icc 0 b) K f` at
every `b` for some finite `K`.  The spec books both as unit **F1**
(`COMPARISON.md` §4) and then still lists them as hypotheses on four fields
(`highContinuationIntegral`, `higherOrderBound`, `extendsBeyond`,
`lifespanInfiniteOfLocallyFinite`, `restartBeyond`).  Redundant hypotheses make
the fields weaker than `prop:local` and push F1 onto every consumer.  The
stated rationale ("so that the contract displays the manuscript's own hypothesis
rather than the ambient Section 4 class") is defensible, but if it is kept the
docstrings should say that a consumer holding `MemForceR` gets them free, with
the F1 pointer at the *use site*, not only in COMPARISON.

### 6. **MINOR** — `highContinuationIntegral` relies on the interval-integral junk value without saying so

`∫ s in t₀..t, …` is Mathlib's Bochner interval integral, which is `0` when the
integrand is not interval-integrable.  The inequality as written is then
generally *false*, so the field silently also demands integrability of
`s ↦ Cgron m ν·‖u(s)‖²_{H²}·‖u(s)‖_{H^m} + ‖f(s)‖_{H^m}` on `[t₀,t]`.  That is a
strengthening, not a weakening, and it is true for a classical solution (unit
N1), but the module docstring documents the `ℝ≥0∞`/`toReal` convention at length
(`Spec.lean:92-101`) and should document this one in the same place.

### 7. **MINOR** — `COMPARISON.md` citation nits

* `higherOrderBound` row: `Euler/OrdinaryEulerHigherEnergy.lean:64,82` —
  `integer_energy_bound` is at `:64` (correct), `integer_energy_uniform` is at
  **`:84`**, not `:82`.
* `outerProductTame` row cites a *worktree* path,
  `/…/026-A03-tame-contract/verification/Contracts/V1/TameProduct.lean:345`.
  The line number is right; the path is now
  `verification/Contracts/V1/TameProduct.lean` on `erenup/integration`.
* Every "PR #31 has not landed / not yet on `erenup/integration`" sentence in
  `Spec.lean` and `COMPARISON.md` is now false (see finding 3).

### Checks that came out clean

* **`squaredHTwoIntegral` is the paper's quantity.**  Elaborated with
  `pp.explicit` it is `lintegral (volume.restrict (Ioo 0 S)) (fun t => sobolevENorm (2:ℝ) (u(t,·)) ^ (2:ℕ))`
  — Lebesgue measure, the interval `(0,S)`, the **inhomogeneous** `H²` norm of
  `Data.sobolevENorm`, squared in `ℝ≥0∞`.  Total, so `≠ ⊤` is literally
  eq:criterion with no integrability side condition.  Matches
  `02-preliminaries.tex:111-113`.
* **No spectral gap / Poincaré / mean-zero.**  `grep -niE
  'poincar|spectral|mean.?zero|gap|torus|periodic|homogeneous'` over `Spec.lean`
  hits only the two docstring passages that *disclaim* them (`:48-51`, `:511-514`),
  consistent with `appendix-a-local-theory.tex:155-157`.  Every norm is the
  inhomogeneous `sobolevENorm`; the low frequencies ride in `H²` itself.
* **eq:Rhigh** (`energyIdentityHigh`) reproduces `appendix-a-local-theory.tex:132-137`
  term for term, including `ν‖∇u‖²_{H^m}` on the left and both right-hand terms;
  `Chigh : ℕ → ℝ` depends on the order alone, as the manuscript's `C_m` does, and
  `Cgron : ℕ → ℝ → ℝ` carries exactly the manuscript's two subscripts.  No
  pressure appears, correctly ("the pressure term vanishes by solenoidality").
* **The `ζ`-step** (`regularizedNormDerivative`) is the honest fixed-`ζ`
  statement: `(√(E+ζ²))' = E'/(2√(E+ζ²))`, and `E/√(E+ζ²) ≤ √(E+ζ²)`,
  `√E/√(E+ζ²) ≤ 1` give exactly the displayed bound; `ζ↓0` returns
  eq:highcontinuation.  The docstring's reason for using the *squared* norm in
  the previous field and the regularized norm here is correct.
* **`extendsBeyond`** is eq:criterion.  `maximalLifespanR` (`Data.lean:657`) is a
  supremum over horizons carrying a solution, so `ofReal S < maximalLifespanR` is
  exactly "there is a classical solution on some `[0,S')` with `S' > S`", i.e.
  "extends smoothly beyond `S`", and it is the shape `prop:Rcritical2` needs at
  `04-whole-space.tex:171`.  The contrapositive remark (`:504-509`) is right.
* **`restartBeyond` does not duplicate A02.**  A02's `restart`
  (`research/A02/Spec.lean:550`) concludes `ofReal (t₀+δ) ≤ maximalLifespanR` at a
  presingular `t₀`; A04's concludes `ofReal (S+δ) ≤ maximalLifespanR` at the
  endpoint, under a `K`-bound on all of `Ico 0 S`.  That is the manuscript's
  `t₀ ↑ S` passage (`appendix-a-local-theory.tex:147-152`) and genuinely A04's.
  The `δ`-before-datum quantifier order matches A02's and A01's
  `horizon_lower_bound` (`research/A01/Spec.lean:338`), and
  `forceSobolevENormL1 1 f ≤ K` is the norm A01 states its bound in.
  `BoundedIntoHOne (Icc 0 (S+1)) K f` is `appendix-a-local-theory.tex:150-151`
  verbatim.  No A01/A02 field is restated.
* **`higherOrderBound`** is "Grönwall bounds every `H^m` norm uniformly up to `S`"
  (`:146-147`), with the `ℝ≥0∞` bound in the shape A02's `restart` consumes its
  `K`.  Stating it at every `m : ℕ` rather than `m ≥ 3` is a strengthening the
  restart needs at `m = 1`, and is discharged by order monotonicity (unit M1).
* **COMPARISON spot-checks** (five, opened at the cited lines):
  `vendor/NavierStokesAndEuler/Euler/OrdinaryEulerHigherEnergy.lean:56`
  `integerEnergyDerivative_bound` ✓ (and the four mismatches listed — Euler via
  `derivative_eq_eulerRhs` at `:42`, uniform-in-time `M` via `WordBound 3 M`,
  `wordEnergy` jet carrier, `Evolution T hT` — are all accurate);
  `:64` `integer_energy_bound` ✓;
  `formalization/NSFormalization/Paper1/ScalarEnergy.lean:22`
  `sqrt_energy_le_primitive` ✓ (and it does assume `hE0 : E 0 = 0` and has no
  linear term, as claimed);
  `verification/Contracts/V1/BoundedRepresentative.lean:173` ✓ `BoundedRepresentativeAPI`,
  `:200` `supNorm_le`, `:213` `eLpNormTop_le` ✓;
  `formalization/FormalPatched/R3MildContinuation.lean:93,67,122` ✓.
* **"Mathlib has no continuous variable-coefficient Grönwall" — TRUE.**  Only four
  Mathlib files mention Grönwall.  `Mathlib/Analysis/ODE/Gronwall.lean:112`
  `le_gronwallBound_of_liminf_deriv_right_le` and `:134`
  `norm_le_gronwallBound_of_norm_deriv_right_le` both bind `{δ K ε : ℝ}` — `K` and
  `ε` are **constants** (`bound : ∀ x ∈ Ico a b, f' x ≤ K * f x + ε`).
  `Mathlib/Analysis/ODE/DiscreteGronwall.lean:50`
  `discrete_gronwall_prod_general` does have variable `c n`, `b n`, and is
  discrete (`u (n+1) ≤ c n * u n + b n`), as COMPARISON says.  There is no
  `Mathlib/Analysis/SpecialFunctions/Gronwall*`.  `ExistUnique.lean` and
  `Geometry/Manifold/IntegralCurve/ExistUnique.lean` only *use* the constant-`K`
  version.  Unit **G3** is a genuine gap.

---

## Commands run and results

```
$ cd /data_8T/ping/blowup_density/.claude/worktrees/030-A04-spec
$ bash scripts/lean-install.sh
… ✔ [9406/9406] Built Tests.Scaling
== OK                                                         # exit 0

$ . scripts/lean-env.sh; export LEAN_NUM_THREADS=6
$ cd verification && lake env lean ../research/A04/Spec.lean
EXIT=0                                                        # no output at all, ~12 s

$ grep -nE '\b(sorry|axiom|admit)\b' research/A04/Spec.lean
12:`structure`; it proves nothing, assumes nothing, introduces no `axiom`, no
13:`sorry` and no abstract propositional variable.  Every field is either data or a
                                                              # docstring only; no term-level occurrence

$ make check                                                  # from the worktree root
python3 experiments/check_formalization_plan.py --check        → ok
python3 experiments/check_contracts.py                         → ok (architecture checks only)
python3 experiments/test_contract_policy.py                    → Ran 13 tests … OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
EXIT=0
```

Measure/convention check on `squaredHTwoIntegral` (scratch file in `/tmp`, not in
the worktree):

```
$ lake env lean /tmp/a04_check.lean     # set_option pp.explicit true in #check …
fun S u =>
  @lintegral Real …
    (@Measure.restrict Real … (@volume Real Real.measureSpace)
      (@Ioo Real … (0 : Real) S))
    fun t => @HPow.hPow ENNReal Nat ENNReal … (sobolevENorm (2 : Real) fun x => u (t, x)) (2 : Nat)
  : Real → SpaceTimeField → ENNReal
```

Mathlib Grönwall survey:

```
$ cd verification/.lake/packages/mathlib
$ grep -ril 'gronwall' Mathlib/ | head
Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean
Mathlib/Analysis/ODE/DiscreteGronwall.lean
Mathlib/Analysis/ODE/Gronwall.lean
Mathlib/Analysis/ODE/ExistUnique.lean
$ ls Mathlib/Analysis/SpecialFunctions/ | grep -i gron      → (none)
$ grep -n '^theorem' Mathlib/Analysis/ODE/Gronwall.lean
112:theorem le_gronwallBound_of_liminf_deriv_right_le {f f' : ℝ → ℝ} {δ K ε : ℝ} {a b : ℝ}
134:theorem norm_le_gronwallBound_of_norm_deriv_right_le {f f' : ℝ → E} {δ K ε : ℝ} {a b : ℝ}
50:theorem discrete_gronwall_prod_general   (DiscreteGronwall.lean, variable c n / b n, discrete)
```

Registered-contract comparison (read-only, from
`/data_8T/ping/blowup_density/.claude/worktrees/000-integration`):
`verification/Contracts/V1/TameProduct.lean:141,154,158,169,178,182,192,345` and
`verification/contracts.json` (`A03.tame_products`, `A03.bounded_representative`).
