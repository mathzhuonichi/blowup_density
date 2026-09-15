# Review — lane 122-A01-a3-split (A2/A2b/A3 split-and-start + the arithmetic core of A3)

Reviewer run: 2026-09-13, worktree `.claude/worktrees/122-A01-a3-split`,
branch `erenup/122-A01-a3-split`, one commit `691f1be` on top of merge-base
`6801945`.  Probes in `/tmp/rev122/` (contents pasted below where they are
evidence; per `logs/LESSONS.md` `/tmp` paths are volatile, so every negative
result is quoted verbatim here).

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean is correct, clean and genuinely useful: the three theorems build, carry
only the standard three axioms, and the claimed seam with A04's ζ-device is real
— I composed `A04.sqrt_le_primitive_linear` into `gronwall_bddAbove_Ico` in ~20
mechanical lines with no adapter (finding 2).  The prose deliverables are honest
about what is *not* done.

But `A3_SPLIT.md` §3b contains a **false negative grep claim** that changes the
plan: the OpenAI/local forced Picard layer *does* have a continuation-from-an-
a-priori-bound theorem, on exactly `exists_local`'s carrier and `Coefficients`
bundle (finding 5, probe compiles).  Row **A2b-a** is therefore not an **L** and
not blocked on **C1c**.  Two further rows are mis-attributed (findings 6, 7) and
one row is missing (finding 8).  None of this touches the committed Lean, so the
fix is a table edit in a follow-up lane, not a rewrite.

---

## 1. Commands run and their results

```
$ . scripts/lean-env.sh ; cd verification
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.Propagation
Build completed successfully (2681 jobs).

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/Propagation.lean
(silent; exit 0)

$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_a3.lean
'NSFormalization.Section4.A01.gronwall_bddAbove_Ico' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.higherOrder_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.higherOrder_bddAbove_lowestOrderSq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
(exit 0)

$ make check
python3 experiments/test_contract_policy.py  -> Ran 13 tests ... OK
python3 experiments/check_work_queue.py      -> 30 work items: ownership, contract registration and task cards consistent.

$ make test
... Replayed Tests.HomogeneousPartialV2
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
(all contracts: "checked; standard logical axioms only")

$ grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/A01/Propagation.lean research/A01/axioms_a3.lean
(no hits in the .lean module; in research/A01/axioms_a3.lean only the word "axioms"
 in the docstring and the three `#print axioms` lines)
```

Also built for the `#check`s below: `NSFormalization.Section4.A04.{Regularized,
HighEnergy,Continuity,Forcing}`, `NSFormalization.Section4.A03.OuterTameProduct`
(9890 jobs), `NSFormalization.Source.OrdinaryForcedLocal`,
`Euler.BoundedMildContinuation`, `Euler.CorrectionContinuation` (3940 jobs).

---

## 2. Findings

### F1 — Compiles, axioms, hygiene. Severity: none (pass)

As above.  `#check` of the three theorems reproduces `A3_SPLIT.md` §2
token-for-token (elaborated forms in `/tmp/rev122/checks.lean`).  Note for the
lead: `Propagation.lean` is imported by **no** `Contracts/` or `Bindings/`
module, so `make test`'s closure does not compile it — only `lake build` does.
That is fine for a split-and-start lane, but the module is not CI-covered until
something consumes it.

### F2 — The claimed A04 seam is real, and costs ~20 lines. Severity: none (pass, positive)

The brief asks whether an adapter is needed between `A04.sqrt_le_primitive_linear`
(`Section4/A04/Regularized.lean:134`, `#check`ed) and `gronwall_bddAbove_Ico`.
**No adapter is needed.**  `sqrt_le_primitive_linear` concludes
`√(E t) ≤ √(E t₀) + ∫ (K √E + b)` on a **compact** `Icc t₀ t₁`; instantiating
`K := fun s => Cgron * k s` makes that literally `gronwall_bddAbove_Ico`'s
`hstep` with `y := fun s => √(E s)`, and the half-open version follows by
applying it once per `t ∈ Ico 0 T₀` on `Icc 0 t`.  `hy0` is then free
(`Real.sqrt_nonneg`) and `hy` is `hE.sqrt`.  Probe
(`/tmp/rev122/adapter.lean`), compiled first try:

```
theorem probe_zeta_device_to_horizon
    {T₀ Cgron Kbnd Bbnd : ℝ} {E E' k b : ℝ → ℝ}
    (hCgron : 0 ≤ Cgron) (hE : ContinuousOn E (Ico 0 T₀))
    (hk : ContinuousOn k (Ico 0 T₀)) (hb : ContinuousOn b (Ico 0 T₀))
    (hEnn : ∀ t ∈ Ico 0 T₀, 0 ≤ E t)
    (hknn : ∀ t ∈ Ico 0 T₀, 0 ≤ k t) (hbnn : ∀ t ∈ Ico 0 T₀, 0 ≤ b t)
    (hkbnd : ∀ t ∈ Ico 0 T₀, (∫ s in (0:ℝ)..t, k s) ≤ Kbnd)
    (hbbnd : ∀ t ∈ Ico 0 T₀, (∫ s in (0:ℝ)..t, b s) ≤ Bbnd)
    (hdE : ∀ t ∈ Ioo 0 T₀, HasDerivAt E (E' t) t)
    (hineq : ∀ t ∈ Ioo 0 T₀, E' t ≤ 2 * ((Cgron * k t) * E t + b t * Real.sqrt (E t))) :
    ∀ t ∈ Ico 0 T₀, Real.sqrt (E t) ≤ (Real.sqrt (E 0) + Bbnd) * Real.exp (Cgron * Kbnd)
```
→ `'probe_zeta_device_to_horizon' depends on axioms: [propext, Classical.choice, Quot.sound]`

So the interface choice recorded in `ATTEMPTS_A3.md` "Decision 1" is verified,
not just asserted.  **Recommendation:** move this probe into the module (or into
`research/A01/probes/`) — it is the lemma A3-M2 will actually call, and it
records the `K = Cgron · k` factorisation requirement, which is the one thing a
future lane could get wrong.

### F3 — Hypothesis set is non-vacuous, and the bound is sharp. Severity: none (pass)

`/tmp/rev122/nonvacuous.lean`: `y = Real.exp`, `k = 1`, `b = 0`, `Cgron = 1`,
`T₀ = 2`, `Kbnd = 2`, `Bbnd = 0`.  Here `hstep` holds with **equality**
(`exp t = 1 + ∫₀ᵗ exp`), and the produced bound is `exp t ≤ exp 2`, sharp as
`t ↑ 2`.  Compiles, standard three axioms.  So the lemma is neither vacuous nor
lossy at the Grönwall step; the only loss is the two cap replacements.

### F4 — `0 ≤ y 0` is necessary: full refutation, stronger than what ATTEMPTS records. Severity: none (pass, positive)

`ATTEMPTS_A3.md` "Decision 3" gives an *arithmetic* counterexample
(`A = B = -1, e₁ = 1, e₂ = 2`) showing the final monotone **proof step** fails.
Reproduced (`/tmp/rev122/attempts_arith.lean`, standard axioms):

```
theorem attempts_decision3_counterexample :
    ∃ A B e₁ e₂ : ℝ, A ≤ B ∧ 0 < e₁ ∧ e₁ ≤ e₂ ∧ ¬ (A * e₁ ≤ B * e₂) :=
  ⟨-1, -1, 1, 2, le_rfl, one_pos, by norm_num, by norm_num⟩
```

Per `logs/LESSONS.md` (2026-09-14, "负向检查不能只用…"), a proof-step
counterexample is *not* proof that the hypothesis is necessary.  I therefore
refuted the whole lemma minus `hy0` (`/tmp/rev122/counterex.lean`): with
`T₀ = 2`, `Cgron = 1`, `k = 1`, `b = 0`, `Kbnd = 2`, `Bbnd = 0` and
`y = fun s => -Real.exp s` (the exact solution of `y' = y`, `y 0 = -1`), `hstep`
holds with **equality** and every other hypothesis holds, yet at `t = 0` the
conclusion reads `-1 ≤ -exp 2`, false.

```
theorem hy0_is_necessary : ¬ NoNonnegInitial
```
→ `'hy0_is_necessary' depends on axioms: [propext, Classical.choice, Quot.sound]`

**`hy0` is load-bearing at the statement level.**  Worth copying this witness
into `ATTEMPTS_A3.md` in place of (or beside) the arithmetic one.

### F5 — §3b's "no forced-path continuation on the OpenAI/local spine" is FALSE. Severity: **HIGH** (plan-changing)

`A3_SPLIT.md` §3b and row **A2b-a** state:

> **OpenAI/local forced Picard layer: no continuation criterion.** … **None
> turns a norm-bounded forced trajectory into a longer one.** … the OpenAI/local
> route must build A2b (an **L**) …

and `A01_SPLIT.md` was edited by this lane to say "Euler/local layer has neither
at any order (grep re-confirmed, lane 122 `A3_SPLIT.md` §3b)".

This is wrong.  The vendored package has, on **exactly** `exists_local`'s
carrier and `Coefficients` bundle:

| declaration | file:line | content |
|---|---|---|
| `EulerBoundedMildContinuation.exists_global_mild_of_bound` | `vendor/NavierStokesAndEuler/Euler/BoundedMildContinuation.lean:39` | *"Genuine finite-time continuation of actual viscous mild solutions from an a priori Sobolev bound"* — a uniform `‖u‖ ≤ R` on every window ⟹ the forced `quadraticDuhamel` solution exists on **all** of `[0,S]` with `‖u‖ ≤ R` |
| `EulerCorrectionContinuation.exists_global_correction_of_bound` | `Euler/CorrectionContinuation.lean:32` | same, zero-initial correction equation, **plus** the divergence-free clause |
| `EulerUniformHeatLocal.exists_uniform_restart_time` | `Euler/UniformHeatLocal.lean:29` | `∃ δ > 0, δ ≤ S`, **depending only on `R` and the `Coefficients`**, restarting from any `‖u₀‖ ≤ R` at any `a` with `a+T ≤ S`, `T ≤ δ` |

The grep the lane says it ran finds these by filename:

```
$ grep -rliE 'extend|continuation|blowup|maximal' --include='*.lean' vendor/NavierStokesAndEuler/Euler/ | grep -iE 'BoundedMild|CorrectionCont'
vendor/NavierStokesAndEuler/Euler/BoundedMildContinuation.lean
vendor/NavierStokesAndEuler/Euler/CorrectionContinuation.lean
```

I verified composability in Lean (`/tmp/rev122/continuation.lean`), by feeding
`exists_global_mild_of_bound` the **same** `ForcedCylinderLocal.coefficients 1 hq
(sobolevPath F hF q)` and the **same** initial vector that
`exists_local` (`Source/OrdinaryForcedLocal.lean:32`) feeds to
`quadraticDuhamel`:

```
theorem probe_forced_continuation_exists
    {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ} (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (F : Icc (0:ℝ) S → SmoothL2Field Space) (hF : …)
    (hu₀ : ‖ordinarySobolev (q+1) a.toLp _‖ ≤ R)
    (hbound : ∀ T (hT : 0 ≤ T) (hTS : T ≤ S) (u : C(Icc 0 T, SobolevSpace 1 (q+1))),
        (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS (coefficients 1 hq (sobolevPath F hF q))
                      (ordinarySobolev (q+1) a.toLp _) u t) → ‖u‖ ≤ R) :
    ∃ u : C(Icc (0:ℝ) S, SobolevSpace 1 (q+1)), ‖u‖ ≤ R ∧ u ⟨0,_,_⟩ = ordinarySobolev (q+1) a.toLp _ ∧
      ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl (coefficients 1 hq (sobolevPath F hF q))
                   (ordinarySobolev (q+1) a.toLp _) u t :=
  exists_global_mild_of_bound 1 q ν hν S hS R hR _ hu₀ (coefficients 1 hq (sobolevPath F hF q)) hbound
```
→ `'probe_forced_continuation_exists' depends on axioms: [propext, Classical.choice, Quot.sound]`

(one-line proof term; the `Coefficients` type and the whole Duhamel equation match
on the nose).

**Consequences for the plan (all three are table edits, no Lean is wrong):**

1. **A2b-a is not an L and not blocked on C1c.**  On the recommended
   OpenAI/local spine it is `exists_global_mild_of_bound` applied to
   `ForcedCylinderLocal.coefficients`: **S** for the bare mild statement, **M**
   for the full `exists_local`-shaped output (the div-free and angle-invariance
   clauses need re-deriving across the glue — the templates are
   `CorrectionContinuation.correction_mild_divergenceFree:17` and
   `ForcedCylinderInvariant.exists_local_forced_mild_invariant:30`, which is how
   `exists_local` gets those clauses in the first place).  HeliCorgi /
   `FormalPatched.R3MildContinuation` is **not** needed for A2b.
2. **A3-L2 collapses.**  If the a-priori bound is available, you do not pick
   `T₀` from `exists_local`'s `∃ T` at all — `exists_global_mild_of_bound` hands
   you the *whole* prescribed `[0,S]`.  `horizon := S`.
3. **`exists_uniform_restart_time` is the first real lead for H1.**  Its `δ`
   depends only on `R` and the coefficient bundle, uniformly over restart points
   — the shape `horizon_lower_bound` wants.  It is stated with `‖u₀‖ ≤ R` in the
   order-`q+1` cylinder norm, whereas H1 (`A01_SPLIT.md:136`) wants dependence
   on `‖a‖_{H¹}` and `‖f‖_{L¹H¹}` only, so it is not literally H1; record it as
   a candidate, not a solution.

Note that `hbound` is a genuine a-priori hypothesis (all windows, all solutions),
so this is not free — it is exactly what A3-S1 plus a carrier-norm comparison
would supply.  But it is "apply an existing theorem", not "build an L".

Everything *else* in §3b checks out: `ElapsedTimePathGluing.join_extend`
(`Euler/ElapsedTimePathGluing.lean:43`) is path concatenation;
`LocalizedBlowup.no_continuous_continuation` (`Source/LocalizedBlowup.lean:36`)
is a Section-3 construction in the opposite direction; `OrdinaryEulerMaximal` /
`EulerC1Limsup` are the inviscid Theorem-1.1 maximal stack.  The error is one of
**omission**, and it happens to be the one file that mattered.

### F6 — `higherOrder_bddAbove_lowestOrderSq` is the wrong specialization for this route. Severity: **medium** (statement fidelity of a docstring/table claim; the theorem is true)

`higherOrder_bddAbove_lowestOrderSq` fixes `k := fun s => (y m₀ s)^2`, i.e. it
ties the **driver order to the family's lowest order**.  Its docstring calls that
"the manuscript's `‖u‖²_{H²}` driver".

The manuscript's driver is the **fixed order 2** — it is literally eq:criterion,
`∫₀^S ‖u(t)‖²_{H²(D)} dt < ∞` (`paper/sections/02-preliminaries.tex:111`) — and
eq:Rhigh is stated "for every integer `m ≥ 3`"
(`appendix-a-local-theory.tex:129`).  The lane's own route sets
`m₀ = q+1 = 7` (`A3_SPLIT.md` §"Recommended route", §3a).  Instantiated there,
`k = (y 7)² = ‖u‖²_{H⁷}` and the hypothesis `hkbnd : ∫₀ᵗ (y 7)² ≤ Kbnd` is an
`L²_tH⁷` bound — i.e. assuming the high-order control one is trying to prove.
The corollary is then circular in the application, and it contradicts the lane's
own row **A3-L1**, which correctly writes `Kbnd` as `∫₀ᵗ ‖u‖²_{H²}`.

Nothing needs to be reproved: `higherOrder_bddAbove` already takes an arbitrary
`k`, so the application instantiates `k := fun s => (y₂ s)^2` for a *separate*
order-2 function.  **Action:** restate row A3-S2′ (and the corollary's docstring)
as "the driver is a fixed low order, supplied outside the propagated family",
or drop the corollary.  Do not cite it as the manuscript's `‖u‖²_{H²}` coupling.

### F7 — A3-L1's blocker is mis-attributed to C1b, and part of it needs no bridge. Severity: **medium**

Lane 119's `C1B_SPLIT.md` *was* genuinely absent at this lane's merge-base
`6801945` (verified: `git ls-tree -r --name-only 6801945 -- research/A01/` has no
C1b file), so §4 and the ATTEMPTS note were accurate when written.  119 has since
merged into integration (`0415366`, "Merge pull request #121"), so the
reconciliation the brief asks for is now possible.  Row-name reconciliation:

* 122's "**C1b at order 0** (initial-value transport)" = 119's rows **C1b-0** /
  **C1b-c5-0**.  Name guessed correctly.  ✔
* 122's "**C1b at orders `2 ≤ m ≤ q+1`** (norm transport)" matches **no** 119
  row — and 119 explicitly **disclaims** it:

  > the Euler `SobolevSpace 1 q` norm is … a sup over derivative words … whereas
  > the D01 order-`m` datum lives against the inhomogeneous Bessel weight.
  > These are **equivalent, not equal**, with `m`-dependent constants in both
  > directions.  **A01 never needs that norm identity:**
  > `ClassicalSolutionR.sobolev` … asks for datum **existence** plus
  > **continuity**, not a norm identity.

  119 is right about `c8`, and 122 is right that **A3-L1 does need a norm
  statement** — `sobolevNormAt 2 (⇑(U t)) ≤ c · ‖u t‖_{SobolevSpace 1 (q+1)}` — to
  turn `exists_local`'s `‖u‖ ≤ ‖u₀‖+1` into `Kbnd`.  So A3-L1 is blocked on
  something that is **not in either table**: a new one-directional norm-comparison
  row.  Also note 119's reviewer finding that C1b's real blocker is **C1b-m-D**
  (the missing D01 finite-order datum constructor), *not* B1/T1 and *not* a
  convention/constant question — A3_SPLIT does not mention C1b-m-D at all.
* The orders: **0 and 2 is not quite right.**  §3a says the order-0 bridge is
  "needed for `y_m 0 = ‖a‖_{H^m}` **and** `hy0 : 0 ≤ y_m 0`".  The second half
  needs no bridge at all: `sobolevNormAt s u t = (sobolevENorm s _).toReal`
  (`Section4/A04/Forcing.lean:74`), so `0 ≤ y_m 0` is `ENNReal.toReal_nonneg`.
  And the initial-time datum **at all orders** is 119's row **C1b-c5-all**,
  marked *ready* (from `a : SmoothL2Field`, via
  `D01/SmoothDatum.lean:278 smoothAngularDatum_isSobolevDatum`) — not blocked.
  What A3-L1 actually needs at order 2 is the *norm* comparison above, for `t > 0`.

### F8 — Missing row: "the order-`m` solution lives on the lowest-order `T₀`". Severity: **medium**

`higherOrder_bddAbove` assumes `hstep` for **every** `m ≥ m₀` on **one** shared
`Ico 0 T₀`.  On the OpenAI spine `exists_local`'s `T` depends on `q`
(§3a records this: "fixed order `q+1`, **no cross-order handle**"), so before the
hypothesis can even be stated one needs `T_m ≥ T₀` for every `m`.  Row **A2b-b**
covers only *agreement* "where both exist"; no row covers *existence* at order
`m` on `T₀`.  That is precisely where `appendix-a-local-theory.tex:66-67` ("the
higher-order bounds in part (ii) hold on the same local interval for every
order") has its content — the Grönwall bound is the *tool* for the bootstrap, not
the statement.  Add the row; F5's `exists_global_mild_of_bound` is the natural
instrument (bounded ⟹ extends to the prescribed `S`, at each fixed `q`).

### F9 — H1: no row, and §3c overstates. Severity: low

`A3_SPLIT.md` has no row for **H1**, and its quantifier order — the thing
`A01_SPLIT.md:136,175` calls "`restart`'s whole point",
`∀ ν>0, ∀ K≠⊤, ∃ δ>0, ∀ a f, … → δ ≤ horizon ν a f` — is not carried over.  §3c's
closing claim that the `C_{m,ν}` discussion "is what makes A3's
`horizon_lower_bound` (H1) readable off the same bound" is too strong: Grönwall
produces an **upper bound on the norms given a horizon**, never a **lower bound
`δ` on the horizon**.  The `δ` must come from a quantitative lifespan
(manuscript: Tao 5.4(ii) eq. (46) rescaled; in tree:
`EulerUniformHeatLocal.exists_uniform_restart_time`, F5 item 3).  Either add an
H1 row with the quantifier order spelled out, or delete the claim.

### F10 — Paper line citations drift. Severity: low

* `Propagation.lean:7` and row **A3** cite `appendix-a-local-theory.tex:147-152`
  for A3.  Lines **148-152** are the *restart* passage ("The `H¹` local existence
  bounds … give a common positive existence duration when restarting at
  `t₀ ↑ S` … One interval extends beyond `S`") — that is **A2b**, not A3.  The
  Grönwall consequence is at **`:146-147`** (A04's own
  `Section4/A04/Gronwall.lean:37` already cites it that way), and the
  "same interval for every order" sentence is at **`:66-67`** — which
  `higherOrder_bddAbove`'s docstring gets right.  Fix the header and the row.
* §3c cites `appendix-a:132-137` for "the constant is independent of the
  interval".  `:132-137` is the eq:Rhigh display; it contains no such sentence.
* (Lesson `logs/LESSONS.md` already has a 2026-09-14 entry on paper line
  citations from lane 120's review — same failure mode.)

### F11 — `FormalPatched` line numbers are wrong. Severity: low

Row **A2b-a** cites `FormalPatched/R3MildContinuation`
`r3EndpointSafeProjected_exists_extension_of_bounded:84` and `_blowup_dichotomy:134`
(inherited from lanes 093/013; the lane honestly flags them as not re-`#check`ed).
Actual:

```
$ grep -n "theorem r3EndpointSafeProjected_exists_extension_of_bounded\|theorem r3EndpointSafeProjected_blowup_dichotomy" \
    formalization/FormalPatched/R3MildContinuation.lean
93:theorem r3EndpointSafeProjected_exists_extension_of_bounded {nu T R : ℝ} (hnu : 0 < nu)
143:theorem r3EndpointSafeProjected_blowup_dichotomy {nu : ℝ} (hnu : 0 < nu)
```

`:93` and `:143`.  Same correction is due in `A01_SPLIT.md` row A2b, which
carries the stale `:84` / `:134` from before this lane.

### F12 — `C_{m,ν}` is `T₀`-free: confirmed, and at the type level. Severity: none (pass)

The brief's check (b).  Confirmed, more strongly than §3c argues:

```
NSFormalization.Section4.A03.outerTameConst : ℕ → ℝ            -- A03/OuterTameProduct.lean:166 (= 6 * vectorTameConst k)
A04 Spec field  Chigh : ℕ → ℝ                                   -- research/A04/Spec.lean:339
A04 Cgron used as  Cgron : ℕ → ℝ → ℝ                            -- Section4/A04/Continuity.lean:132 (m, ν)
```

Types alone forbid a `T₀` (or `t`) dependence.  `research/A04/Spec.lean:344-346`
says the two arguments "are the manuscript's own two subscripts: the order …
and the viscosity".  The Young arithmetic `C_gron = C_m²/(4ν)` is the right
reading of `C_{m,ν}` in eq:highcontinuation
(`appendix-a-local-theory.tex:142-145`).  Inside `Propagation.lean`, `Cgron`/`C m`
appear only multiplied by `k` and inside `exp`, as claimed.

One nit: §3c writes "In Lean the constant enters as A04's
`Chigh m = A03.outerTameConst m`".  `research/A04/Spec.lean:330-338` says the
implementation **may** take that; the contract deliberately keeps `Chigh` opaque.
The conclusion is unaffected.

### F13 — Weakening `k`/`b` continuity to interval-integrability: **do not**. Severity: none (answers the brief's negative check)

`gronwall_bddAbove_Ico` inherits `ContinuousOn k/b` from
`A04.gronwall_integral_mul` → `gronwall_integral`, whose integrating-factor proof
differentiates `x ↦ ∫_{t₀}^x c` pointwise (FTC) and needs `s ↦ exp(-∫c)·b s`
continuous for `integral_mono_on`.  Weakening to `IntervalIntegrable` would mean
reproving A04's `gronwall_integral` via absolute continuity — and would buy
nothing, because the supply side is *already* continuity:
`A04.intervalIntegrable_highContinuationIntegrand`
(`Section4/A04/Continuity.lean:132`) is itself proved by
`apply ContinuousOn.intervalIntegrable` (`:141`) from
`continuousOn_sobolevNormAt_velocity` (`:105`) and `continuousOn_sobolevNormAt_force`
(`:115`).  A04's own module docstring (`Gronwall.lean:37-45`) makes the same
argument.  **No strengthening recommended.**

### F14 — ATTEMPTS is honest. Severity: none (pass)

* The recorded `linter.unusedVariables` warning reproduces exactly.  Reverting
  `fun _ _ => sq_nonneg _` to `fun t _ => sq_nonneg _` in a copy
  (`/tmp/rev122/Propagation_linter.lean`):
  ```
  /tmp/rev122/Propagation_linter.lean:150:25: warning: Variable name `t` is not explicitly referenced.
  ```
  Same line (150), same declaration, no `set_option` used to silence it.  ✔
* Decision 3's counterexample reproduces (F4) and is in fact weaker than the
  truth.  ✔
* Decision 2 (uniform caps instead of `∫₀^{T₀}`) is sound: the improper-integral
  design would need `k ≥ 0` on the **closed** `Icc t T₀`, and eq:criterion is
  stated as a finite `∫₀^S` precisely because nothing is assumed at `S`.  ✔
* Every `file:line` the lane claims to have `#check`ed does exist at that line:
  `Gronwall.lean:202`, `Regularized.lean:134`, `Regularized.lean:98`,
  `HighEnergy.lean:136`, `Continuity.lean:132`, `Continuity.lean:105`,
  `Forcing.lean:105` (an `abbrev`), `Forcing.lean:74`,
  `research/A04/Spec.lean:424` (`energyIdentityHigh`),
  `Source/OrdinaryForcedLocal.lean:32` (`exists_local`, with `hq : 6 ≤ q`, output
  order `q+1`, and the single quantitative clause `‖u‖ ≤ ‖u₀‖ + 1` exactly as
  §3a describes), `Source/OrdinaryCylinderDescent.lean:56-71`.  The two wrong
  ones are the `FormalPatched` pair (F11), which the lane marked as not checked.

---

## 3. Recommended next A3 lane

**★ Row A2b-a′ / A3-L2′ — "forced global mild solution from an a-priori bound"**,
new module `formalization/NSFormalization/Section4/A01/Continuation.lean`.
This is the highest-value follow-up because F5 turns a claimed **L** into an
**S–M**, and it dissolves A3-L2 and (given the bound) the whole "choose `T₀`"
problem.

Exact statement to prove (step 1, **S** — the probe already compiles, see F2/F5):

```lean
theorem forced_global_mild_of_bound {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
        (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))),
        (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) → ‖u‖ ≤ R) :
    ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
      ‖u‖ ≤ R ∧
      u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
      ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq (sobolevPath F hF q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t :=
  EulerBoundedMildContinuation.exists_global_mild_of_bound 1 q ν hν S hS R hR _ hu₀
    (coefficients 1 hq (sobolevPath F hF q)) hbound
```

Inputs, all `#check`ed by this review:
* `EulerBoundedMildContinuation.exists_global_mild_of_bound`
  (`vendor/NavierStokesAndEuler/Euler/BoundedMildContinuation.lean:39`)
* `NSFormalization.Source.ForcedCylinderLocal.coefficients`
  (`Source/ForcedCylinderLocal.lean:52`)
* `NSFormalization.Source.OrdinaryForcedLocal.exists_local`
  (`Source/OrdinaryForcedLocal.lean:32`) — for the shape to match
* build cost measured this review: `lake build NSFormalization.Source.OrdinaryForcedLocal
  Euler.BoundedMildContinuation Euler.CorrectionContinuation` = 3940 jobs, a few
  minutes warm.

Step 2 (**M**, same lane if it fits): restore the two clauses
`exists_local` carries and `exists_global_mild_of_bound` drops —
divergence-freeness (template: `EulerCorrectionContinuation.correction_mild_divergenceFree`,
`Euler/CorrectionContinuation.lean:17`, via `mild_solution_preserves_gradient_zero`)
and angle invariance (template: `ForcedCylinderInvariant.exists_local_forced_mild_invariant`,
`Source/ForcedCylinderInvariant.lean:30`, via `source_translation:19` +
`translationIsometry:13`) — then descend to `U : C(Icc 0 S, EulerMeanSolenoidal.L2)`
by copying the last eight lines of `exists_local` (`ordinaryValue`,
`ordinaryValue_lift`, `Source/OrdinaryCylinderDescent.lean:56,60`).

Do **not** start A3-M1/M2 yet (still gated on A04's `hpr`, correctly recorded),
and do **not** start A3-L1 until the new norm-comparison row from F7 is written
down — it is not a C1b row.

Table edits the same lane should carry (F5–F11): rewrite §3b and row A2b-a;
retarget row A3-L2; restate row A3-S2′ (F6); split row A3-L1's blocker into
"C1b-0 datum (ready)" + "new order-2 norm comparison (open)"; add the missing
`T_m ≥ T₀` row (F8) and an H1 row with its quantifier order (F9); fix the paper
and `FormalPatched` line numbers (F10, F11); and revert the `A01_SPLIT.md` row
A2b sentence "Euler/local layer has neither at any order (grep re-confirmed…)".
