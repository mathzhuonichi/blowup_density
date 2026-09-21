# Review — lane 142-A01-a3-m2-gronwall (row A3-M2, the Grönwall instantiation)

Reviewer run 2026-09-13. Worktree `.claude/worktrees/142-A01-a3-m2-gronwall`,
branch `erenup/142-A01-a3-m2-gronwall`, one commit `778da5b` on merge-base `0f7d31b`.
Probes in `/tmp/rev142/` (ephemeral; every error text quoted below is verbatim from a
probe run made during this review).

## Verdict: **ACCEPT-WITH-NOTES**

The two theorems compile with the three standard axioms, the `hstep` slot really is
`A04.highContinuationIntegral` at `t₀ = 0` with no adapter (§2), the interval
bookkeeping has no gap at `t = 0` (§3), and — the important fidelity point — with
`T₀ := T` the statement is token-for-token the manuscript's sentence at
`appendix-a-local-theory.tex:146-147` ("If eq:criterion holds, Grönwall bounds every `H^m`
norm uniformly up to `S`"), §4. All four recorded ATTEMPTS failures reproduce
(§11 / FINDING 7), one of them with a corrected diagnosis.

Seven notes, none blocking. Two correct the records rather than the Lean: the lane
understates its own non-vacuity (§7 / FINDING 3 — `hkbnd` is *free* for every classical
solution on every `T₀ < T`, so the hole is a value, not a possibility, and this is
provable today), and `hf1 : MemL1Hm f` is not load-bearing (§6 / FINDING 2). One is
mechanical: the lane must be rebased before merge (§10 / FINDING 6).

---

## 1. Compiles / axioms / hygiene — PASS

```
$ . scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 \
    lake build NSFormalization.Section4.A01.ForceCap \
               NSFormalization.Section4.A04.HighContinuationIntegral
Build completed successfully (9956 jobs).

$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.GronwallInstance
Build completed successfully (9957 jobs).
```
(the only warnings in either log are pre-existing vendor `Replayed` linter warnings from
`Formal/R3DivergencePointwise`, `R3LerayL2Operator`, `R3LerayFourierBridge`,
`R3LerayComplexFiberSymbol` — none from the lane's files.)

```
$ cd verification && lake env lean ../formalization/NSFormalization/Section4/A01/GronwallInstance.lean
EXIT=0
0 /tmp/rev142/module_lean.log      # silent

$ cd verification && lake env lean ../research/A01/axioms_a3_m2.lean
EXIT=0
'NSFormalization.Section4.A01.highOrder_bddAbove_of_kbnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.highOrder_bddAbove_all_orders_of_kbnd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Lane142.nonvac_highOrder_bddAbove_of_kbnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane142.nonvac_highOrder_bddAbove_all_orders_of_kbnd' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Four declarations, standard three axioms, exactly as ATTEMPTS claims.

```
$ make check
EXIT=0
Ran 13 tests in 0.043s / OK
30 work items: ownership, contract registration and task cards consistent.
```

Hygiene grep over the three lane files (`GronwallInstance.lean`, `axioms_a3_m2.lean`,
`ATTEMPTS_A3_M2.md`) for `sorry|admit|axiom|native_decide|maxHeartbeats|set_option`: the
only hits are the string `axioms` inside `#print axioms` lines and prose. **No** `sorry`,
`admit`, `axiom` declaration, `native_decide`, `maxHeartbeats` or any `set_option`.
The module declares no `def`/`abbrev`/`structure`/`instance` — two theorems only.

---

## 2. `hstep` is `highContinuationIntegral` at `t₀ = 0`, verbatim — PASS

`#check` with `pp.fullNames` (probe `/tmp/rev142/probe1.lean`, EXIT=0) gives, for the
lane's first export:

```
@NSFormalization.Section4.A01.highOrder_bddAbove_of_kbnd : ∀ {ν : ℝ} {a : …A02.SpatialField}
  {f : …A02.SpaceTimeField} {T : ℝ},
  0 < ν → a ∈ …A02.initialClassR → …D01.MemForceR f → …A04.MemL1Hm f →
    ∀ (w : …A02.ClassicalSolutionR ν a f T), …A04.HasSmoothSobolevPath T w.velocity →
      ∀ {m : ℕ}, 3 ≤ m → ∀ {T₀ Kbnd : ℝ}, 0 < T₀ → T₀ ≤ T →
        (∀ t ∈ Set.Ico 0 T₀, ∫ (s : ℝ) in 0..t, …A04.sobolevNormAt 2 w.velocity s ^ 2 ≤ Kbnd) →
          ∀ t ∈ Set.Ico 0 T₀,
            …A04.sobolevNormAt (↑m) w.velocity t ≤
              (…A04.sobolevNormAt (↑m) w.velocity 0 + (…A04.forceSobolevENormL1 (↑m) f).toReal) *
                Real.exp (…A04.Cgron m ν * Kbnd)
```
and for the second:
```
@NSFormalization.Section4.A01.highOrder_bddAbove_all_orders_of_kbnd : … →
  ∀ (m : ℕ), 3 ≤ m → BddAbove ((fun t => …A04.sobolevNormAt (↑m) w.velocity t) '' Set.Ico 0 T₀)
```
(the `≤ Kbnd` looks like it sits under the `∫` binder only because of the pretty-printer's
precedence; the source has explicit parentheses, and the hypothesis unifies with
`gronwall_bddAbove_Ico`'s `hkbnd` slot, which is also parenthesised.)

Unification evidence for `hstep`: the probe states `gronwall_bddAbove_Ico`'s `hstep` slot
**beta-unreduced**, with the lane's `y`, `k`, `b`, `Cgron` substituted as literal lambdas,
and discharges it by the bare projection — no `integral_congr`, no `ring_nf`:

```lean
theorem hstep_is_highContinuationIntegral_verbatim … :
    ∀ t ∈ Ico (0 : ℝ) T₀,
      (fun t => sobolevNormAt (m : ℝ) w.velocity t) t ≤
        (fun t => sobolevNormAt (m : ℝ) w.velocity t) 0 +
          ∫ s in (0 : ℝ)..t,
            (…A04.Cgron m ν * (fun s => sobolevNormAt 2 w.velocity s ^ 2) s *
                (fun t => sobolevNormAt (m : ℝ) w.velocity t) s
              + (fun s => sobolevNormAt (m : ℝ) f s) s) :=
  fun t ht =>
    (highContinuationIntegral ν a f T hν ha hf hf1 w hpath m hm 0 t le_rfl ht.1
      (lt_of_lt_of_le ht.2 hT₀T)).2
```
`lake env lean /tmp/rev142/probe1.lean` → `EXIT=0`, no errors, no warnings. The claim
"same parse, no adapter" is confirmed: the two integrands are syntactically the same term
up to β, and `A04.Cgron m ν * ‖u‖²_{H²} * ‖u‖_{H^m}` left-associates identically on both
sides.

`A04.highContinuationIntegral`'s conclusion (from the same `#check`) is
`sobolevNormAt (↑m) w.velocity t ≤ sobolevNormAt (↑m) w.velocity t₀ + ∫ s in t₀..t, (Cgron m ν *
sobolevNormAt 2 w.velocity s ^ 2 * sobolevNormAt (↑m) w.velocity s + sobolevNormAt (↑m) f s)`,
i.e. at `t₀ := 0` exactly the above.

The `(2 : ℝ)` / `((2 : ℕ) : ℝ)` order-literal reliance flagged in ATTEMPTS is `rfl` in this
pin (probe `/tmp/rev142/probe5.lean`, EXIT=0):
```lean
example (u : SpaceTimeField) (t : ℝ) :
    sobolevNormAt (((2 : ℕ) : ℝ)) u t = sobolevNormAt (2 : ℝ) u t := rfl
```

---

## 3. Interval bookkeeping — PASS, no gap at `t = 0`

`highContinuationIntegral` wants `0 ≤ t₀`, `t₀ ≤ t`, `t < T`. The lane supplies
`le_rfl : (0:ℝ) ≤ 0`, `ht.1 : 0 ≤ t`, `lt_of_lt_of_le ht.2 hT₀T : t < T`.

* At `t = 0`: `t₀ ≤ t` is `0 ≤ 0` ✓. `t < T` needs `0 < T₀`, which is **not** taken from
  `_hT₀` but from `ht.2 : t < T₀` — i.e. membership `0 ∈ Ico 0 T₀` already forces `T₀ > 0`.
  So `t = 0` is covered without `_hT₀`, and `hstep 0` degenerates correctly to
  `y 0 ≤ y 0 + ∫_0^0 … = y 0`.
* If `T₀ ≤ 0`, `Ico 0 T₀ = ∅` and both conclusions are vacuously true; nothing breaks.
* `gronwall_bddAbove_Ico`'s `hy0 : 0 ≤ y 0` is about the point `0`, which need not lie in
  `Ico 0 T₀`; it is discharged by `sobolevNormAt_nonneg`, which is unconditional. ✓
* `Ico 0 T₀ ⊆ Ico 0 T` (`hIcoSub`) is the only `mono` used, and it is exactly `T₀ ≤ T`. ✓

---

## 4. Statement fidelity — PASS (and the `T₀ := T` case is the manuscript sentence)

**(a) Is `Kbnd` the `L²_tH²` quantity of eq:criterion?** eq:criterion
(`02-preliminaries.tex:111`, verified by `grep -n 'label{eq:criterion}'`, not copied from an
earlier review) is
```
\int_0^S\norm{u(t)}_{H^2(D)}^2\dd t<\infty .
```
The lane's `hkbnd` is `∀ t ∈ Ico 0 T₀, (∫ s in 0..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd`.
The integrand `sobolevNormAt 2 w.velocity s ^ 2` **is** `‖u(s)‖²_{H²}`, and for a
nonnegative integrand the family of running integrals is monotone, so
"`∃ Kbnd`, running integrals ≤ `Kbnd` on `[0,S)`" is equivalent to eq:criterion's
`∫_0^S < ∞` (as an improper limit). With `Kbnd` a parameter rather than existential, the
lane states the quantitative form, which is strictly more informative. **Faithful.**

Importantly, the `⊤`-trap does **not** bite on this side: `ClassicalSolutionR.sobolev 2`
hands over a genuine order-2 datum path, so `sobolevNormAt 2 w.velocity t` is a real
Sobolev norm, not the junk `0` that `sobolevENorm = ⊤` would give. Probe
(`/tmp/rev142/probe5.lean`, EXIT=0):
```lean
theorem order2_norm_is_genuine (w : ClassicalSolutionR ν a f T) :
    ∃ G : ℝ → …Paper3.RealVectorSobolev ((2:ℕ):ℝ),
      ∀ t ∈ Ico (0:ℝ) T, sobolevNormAt 2 w.velocity t = ‖G t‖ := by
  obtain ⟨G, _hGc, hGd⟩ := w.sobolev 2
  exact ⟨G, fun t ht => sobolevNormAt_eq (hGd t ht)⟩
```
(The vacuity warning recorded in `A3_SPLIT.md`'s A3-L1·k row is about the **cylinder/Euler**
side `⇑(U t)`, not about `w.velocity`. Worth keeping straight.)

**The manuscript sentence is the `T₀ := T` case.** `appendix-a-local-theory.tex:146-147`
reads "If \eqref{eq:criterion} holds, Gr\"onwall bounds every $H^m$ norm uniformly up to
$S$." Since the lane allows `T₀ = T` (`hT₀T : T₀ ≤ T`), that case is an instance
(`/tmp/rev142/probe5.lean`, EXIT=0):
```lean
theorem manuscript_case_T₀_eq_T … (hT : 0 < T)
    (hcrit : ∀ t ∈ Ico (0:ℝ) T, (∫ s in (0:ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd) :
    ∀ t ∈ Ico (0:ℝ) T, sobolevNormAt (m:ℝ) w.velocity t ≤ … :=
  highOrder_bddAbove_of_kbnd hν ha hf hf1 w hpath hm hT le_rfl hcrit
```
with `T` playing the manuscript's `S`. This is the strongest fidelity evidence in the lane
and is **not** recorded in ATTEMPTS or `A3_SPLIT.md` — see note 7.

**(b) Is the exponent the manuscript's constant?** The manuscript does not display the
Grönwall output; it displays the differential inequality it comes from,
`eq:highcontinuation` (`appendix-a-local-theory.tex:142-145`):
```
 (\norm{u}_{H^m})' \le C_{m,\nu}\norm{u}_{H^2}^2\norm{u}_{H^m}+\norm{f}_{H^m}.
```
Integrating and applying Grönwall gives exactly
`‖u(t)‖_{H^m} ≤ (‖u(0)‖_{H^m} + ∫_0^t‖f‖_{H^m}) · exp(C_{m,ν}∫_0^t‖u‖²_{H²})`, which the
lane weakens to the two uniform caps. `A04.Cgron m ν` is the formalization's `C_{m,ν}`,
pinned by A3-M1/lane 135 to `Chigh m ^ 2 / (4 * ν)` (`#print` in probe 1:
`def NSFormalization.Section4.A04.Cgron : ℕ → ℝ → ℝ := fun m ν => Chigh m ^ 2 / (4 * ν)`).
So the exponent `Cgron m ν * Kbnd` is the manuscript's constant times the manuscript's
`L²_tH²` quantity. The prefactor `(‖u(0)‖_{H^m} + ‖f‖_{L¹_tH^m})` is an explicit
strengthening of a sentence the manuscript leaves qualitative. **No drift.**

**(c) Load-bearing hypotheses.** See §6 (`hf1` redundant) and §7 (`hkbnd` load-bearing,
and satisfiable), and: `_hT₀ : 0 < T₀` is genuinely unused, correctly prefixed, and harmless
(§3 explains why the `t = 0` endpoint does not need it). `ha : a ∈ initialClassR` **is**
load-bearing — it is consumed inside `A04.highContinuationIntegral` by
`deriv_normSq_absorbed hν ha hf w hpath …` (`HighContinuationIntegral.lean:123,135`), so it
cannot be dropped.

**(d)** See §7 / FINDING 3(ii).

---

## 5. FINDING 1 (severity: none — confirmation). The slot table is accurate.

Every row of the `A3_SPLIT.md` §3.5 table is discharged as claimed, in
`gronwall_bddAbove_Ico`'s declared argument order
(`hCgron, hy0, hy, hk, hb, hknn, hbnn, hkbnd, hbbnd, hstep`, `Propagation.lean:73-81`):
`(A04.Cgron_pos m ν hν).le`, `sobolevNormAt_nonneg`, `continuousOn_sobolevNormAt_velocity w m
|>.mono`, the same at order 2 `.pow 2`, `forceCap_L1`'s three components, `fun _ _ =>
sq_nonneg _`, the lane's `hkbnd`, `forceCap_L1`'s cap, and `hstep`. The all-orders export
uses `higherOrder_bddAbove_fixedDriverSq` with `m_drive := 2` — the *manuscript* driver, not
the `m₀`-driver variant that `Propagation.lean:144-145` explicitly warns against.

## 6. FINDING 2 (severity: LOW — records). `hf1 : MemL1Hm f` is not load-bearing.

It is derivable from `hf : MemForceR f` by `A04.memL1Hm_of_memForceR` (`Forcing.lean:140`),
and `A04.highContinuationIntegral` — the only consumer — binds it as `_hf1` and never uses
it (`HighContinuationIntegral.lean:102`). Probe (`/tmp/rev142/probe1.lean`, EXIT=0) restates
the lane's theorem with the binder deleted and proves it:

```lean
theorem highOrder_bddAbove_of_kbnd_no_hf1 … (hf : MemForceR f) … :=
  …A01.highOrder_bddAbove_of_kbnd hν ha hf (memL1Hm_of_memForceR hf) w hpath hm hT₀ hT₀T hkbnd
```
No strength is lost by keeping it (it is implied, not extra), and it mirrors
`highContinuationIntegral`'s own signature, so this is a style note only. The same note was
already made about `hfin` in lane 137's review (finding 2 there) — the pattern is now
systemic in the A3 chain. **No action required**; if a V2 of the chain is ever cut, drop
`MemL1Hm` from both signatures.

## 7. FINDING 3 (severity: MEDIUM — records understate the result). `hkbnd` is load-bearing, and it is satisfiable for every classical solution on every `T₀ < T`.

Two separate probes, both `/tmp/rev142/probe2.lean`, `EXIT=0`, no errors.

**(i) `hkbnd` is genuinely load-bearing** — a `Kbnd`-free version collapses. If the
conclusion held for *every* `Kbnd` (which is what deleting `hkbnd` and leaving `Kbnd` free
means), then `Kbnd → -∞` drives `exp(Cgron·Kbnd) → 0` and, since `Cgron m ν > 0` and the
prefactor is `≥ 0`, forces the `H^m` norm to vanish:

```lean
theorem exp_collapse {y A C : ℝ} (hC : 0 < C) (hA : 0 ≤ A)
    (h : ∀ K : ℝ, y ≤ A * Real.exp (C * K)) : y ≤ 0

theorem kbnd_free_collapses (hν : 0 < ν) (w : ClassicalSolutionR ν a f T)
    (H : ∀ Kbnd : ℝ, ∀ t ∈ Ico (0:ℝ) T₀, sobolevNormAt (m:ℝ) w.velocity t ≤ … Real.exp (Cgron m ν * Kbnd)) :
    ∀ t ∈ Ico (0:ℝ) T₀, sobolevNormAt (m:ℝ) w.velocity t = 0
```
So the `Kbnd`-free statement is **false** for any classical solution with a nonzero `H^m`
norm anywhere on `[0,T₀)`. This is a proper negative check in the LESSONS sense (restate
without the hypothesis and show the weakened statement is false), not "omit the argument and
re-apply".

**(ii) The hole is a *value*, not a *possibility* — and the lane's own records understate
this.** `ATTEMPTS_A3_M2.md` says `Kbnd := 0` "is only demonstrably correct on the zero
solution". That is true of `Kbnd = 0`, but existence of *some* `Kbnd` is free today for any
`T₀ < T`, with no `D-euler-pairing` and no norm comparison — the order-2 datum norm of a
`ClassicalSolutionR` is continuous on `Ico 0 T` (`continuousOn_sobolevNormAt_velocity w 2`),
hence bounded on the compact `Icc 0 T₀ ⊆ Ico 0 T`:

```lean
theorem kbnd_exists (w : ClassicalSolutionR ν a f T) (_h0 : 0 ≤ T₀) (hT₀ : T₀ < T) :
    ∃ Kbnd : ℝ, ∀ t ∈ Ico (0:ℝ) T₀,
      (∫ s in (0:ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd
```
(proved by `isCompact_Icc.exists_bound_of_continuousOn` + `intervalIntegral.integral_mono_on`,
witness `Kbnd := max M 0 * T₀`).

Consequence for planning, and this is the part worth recording: **on strictly interior
horizons `T₀ < T` the lane's theorems are unconditionally applicable and non-vacuous for
every classical solution, not just `zeroSol`.** What A3-L1·k actually has to deliver is the
*endpoint* case `T₀ = T` — a `Kbnd` that stays finite as `T₀ ↑ T` — which is precisely
eq:criterion at the blow-up time, and/or a `Kbnd` expressed through the datum so that it is
uniform in the restart argument. The recorded `Kbnd := c²·(‖u₀‖+1)²·T₀` is of that kind.
Suggested: add this sentence to `A3_SPLIT.md`'s A3-L1·k row so a future lane does not spend
a day proving `kbnd_exists`.

## 8. FINDING 4 (severity: LOW — consistency). Imports, duplication, packaging.

* **Imports.** Two, both in-tree and both necessary:
  `NSFormalization.Section4.A01.ForceCap`, `NSFormalization.Section4.A04.HighContinuationIntegral`.
  Nothing from `Contracts/`, nothing from `Formal.*`, nothing from `Citations/`. The module
  is in `formalization/`, so `check_contracts.py`'s import policy does not apply to it. No
  definition is restated (zero `def`/`structure`), so there is no bridge obligation.
* **Nobody imports it yet** — it is a leaf. Fine for now; A3-L1·k and the `HasAprioriBound`
  supply lane will be its consumers.
* **Zero-solution reconstruction, MAINT note.** `research/A01/axioms_a3_m2.lean` re-copies
  `datum_zero` / `zeroSol` / `memForceR_zero` / `zero_mem_initialClassR` / `path_zero` /
  `sobolevNormAt_zero`. Counting reconstructions of the zero classical solution across
  `research/`, this file is the **8th** (`A04/REVIEW_CONTRACT.md`, `A04/REVIEW_HPR.md`,
  `D01/REVIEW_SL8_PREP.md`, `D01/REVIEW_CONTRACT_V3.md`, `D01/REVIEW_SL8_ASSEMBLY.md`,
  `D01/negative_simp_p2.lean`, `D01/ATTEMPTS_SIMP.md`, and this one); `path_zero` alone now
  has 5 copies. This is copy-paste in throwaway probe files, so it costs nothing at build
  time, but eight divergent copies is where a silent drift starts (LESSONS already has the
  "conformance file drifted until 090 found it" entry). **MAINT suggestion:** promote the
  zero-solution witness bundle to one committed module (e.g.
  `formalization/NSFormalization/Section4/A02/ZeroSolution.lean`) and have future
  `axioms_*.lean` import it. Not this lane's job.
* **`forceCap_L1` vs `forceCap`.** The lane picked `forceCap_L1` (cap
  `(forceSobolevENormL1 m f).toReal`, `t`-free, needs only `MemForceR`, no `0 < T₀`) over
  `forceCap` (existential `∃ Bbnd` from `∫_0^{T₀}`, needs `0 < T₀`). Consequences: the bound
  is fully explicit and matches the manuscript's own `‖f‖_{L¹_tH^m}` vocabulary, at the cost
  of being slightly **looser** than `forceCap`'s (`∫_0^{T₀}‖f‖_{H^m} ≤ ‖f‖_{L¹_tH^m}`
  always). For the continuation argument, where `T₀ = T` and the whole point is a
  solution-independent constant, the `L¹` choice is the right one — it keeps `R` fixed
  *before* the horizon, which is exactly what `HasAprioriBound` needs (see §12). Correct
  call; worth keeping in the records as a deliberate trade-off, which ATTEMPTS already does.

## 9. FINDING 5 (severity: LOW — packaging). `BddAbove` is the right shape for A3-Tm, the wrong shape for `HasAprioriBound`.

`highOrder_bddAbove_all_orders_of_kbnd` concludes
`∀ m ≥ 3, BddAbove (sobolevNormAt m w.velocity '' Ico 0 T₀)` — an existential supremum, per
order, on a half-open interval, on the **R³** side. That is exactly what
`appendix-a-local-theory.tex:66-67` ("the higher-order bounds in part (ii) hold on the same
local interval for every order") asks for and what row **A3-Tm** consumes. It is *not* what
lane 139's `HasAprioriBound` wants, which is a single explicit `R`, fixed before `T` and
before `u`, on the **cylinder** `ContinuousMap` sup-norm over the closed `Icc 0 T`.

The usable export for `HasAprioriBound` is the *other* one,
`highOrder_bddAbove_of_kbnd`, whose bound `(‖u(0)‖_{H^m} + ‖f‖_{L¹_tH^m})·exp(Cgron·Kbnd)`
is explicit and solution-independent (the point `REVIEW_A2B_INV.md:256-260` already made).
Nothing to change in the lane — but the records should not claim the `BddAbove` packaging
feeds `HasAprioriBound`; they do not claim it, and should not start.

Also note that `m1 sobolev_smooth` wants `ContDiffOn ℝ ∞ G (Ico 0 T)` for the *datum path*,
which neither export touches; `BddAbove` is not a step toward `m1`.

## 10. FINDING 6 (severity: LOW — mechanical, blocks merge until fixed). The lane is behind integration; `scripts/gates.sh` fails on staleness.

```
$ bash scripts/gates.sh NSFormalization.Section4.A01.GronwallInstance
…
== make test        → all contracts "checked; standard logical axioms only"
== make test-mutations → extra_axiom: rejected as required
                          weakened_hypothesis: rejected as required
                          Mutation suite passed.
== check_contracts
AssertionError: Removed stable specification: verification/Contracts/V2/EnergyHighPartial.lean
EXIT=1
```
This is **not** a lane defect. `gates.sh` runs `check_contracts.py --base-ref
origin/erenup/integration`; lane 141 merged `Contracts/V2/EnergyHighPartial.lean` into
integration *after* this lane's merge-base `0f7d31b`, so from the lane's checkout the file
looks deleted. Against the lane's own base it passes:
```
$ python3 experiments/check_contracts.py --base-ref 0f7d31b | tail -3
  "base_compatibility_checked": true,
```
`make test` and `make test-mutations` both pass as shown. **Action for the lead:** rebase
onto current `erenup/integration` and re-run `gates.sh` before merging (no conflicts
expected — the lane touches no registry file; its four files are one new `.lean` plus three
`research/A01/` records).

Also: the lane has no `tasks.py claim` commit. That is correct here — A3-M2 is a sub-row of
A01, not a DAG node with its own work item, and `make check`'s work-queue check passes.

## 11. FINDING 7 (severity: NONE — honesty check). All four recorded failures reproduce; one needs a corrected diagnosis.

* **(1) `∀ m` elaborates as `ℝ`** — reproduced verbatim (`/tmp/rev142/probe3.lean:22`):
```
error: Type mismatch
  NSFormalization.Section4.A01.highOrder_bddAbove_all_orders_of_kbnd hν ha hf hf1 w hpath hT₀ hT₀T hkbnd
has type
  ∀ (m : ℕ), 3 ≤ m → BddAbove ((fun t => sobolevNormAt (↑m) w.velocity t) '' Ico 0 T₀)
but is expected to have type
  ∀ (m : ℝ), 3 ≤ m → BddAbove ((fun t => sobolevNormAt m w.velocity t) '' Ico 0 T₀)
```
  Matches the ATTEMPTS text word for word.
* **(4) `A04.Cgron` does not resolve inside another namespace** — reproduced (I hit it by
  accident writing probe 1 in `namespace Rev142`):
```
/tmp/rev142/probe1.lean:41:13: error(lean.unknownIdentifier): Unknown identifier `A04.Cgron`
```
  Fixed by the full name or by `open`ing `A04`, as ATTEMPTS says.
* **(5) `forceSobolevENormL1` ambiguity** — reproduced verbatim
  (`/tmp/rev142/probe3.lean:29`), and the two definitions really are distinct declarations
  (`A04/Forcing.lean:105`, `D01/HalfOrder.lean:148`):
```
error: Ambiguous term
  forceSobolevENormL1
Possible interpretations:
  NSFormalization.Section4.D01.forceSobolevENormL1 2 f : ENNReal
  NSFormalization.Section4.A04.forceSobolevENormL1 2 f : ENNReal
```
* **(3) `(0 : SpatialField)` `OfNat` failure** — reproduces, **but not for the reason the
  reader will assume**. With `SpatialField` in the `open` list it compiles fine: the whole
  axioms file with `(0 : Space → Space)` replaced by `(0 : SpatialField)` *and*
  `SpatialField` added to the `open …A02 (…)` list runs `EXIT=0`
  (`/tmp/rev142/probe4_spatialfield.lean`). Without adding it to the open list — the lane's
  actual situation — `autoImplicit` silently auto-binds `SpatialField` as a fresh universe
  variable, and you get exactly the recorded pair (`/tmp/rev142/probe4b.lean:60`):
```
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  OfNat SpatialField 0
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Membership SpatialField (Set NSFormalization.Section4.A02.SpatialField)
```
  The give-away is the second message: the *set* is `…A02.SpatialField` while the *element*
  is a bare `SpatialField` — two different things. The lane's workaround
  (`(0 : Space → Space)`) is correct; the cleaner fix is to add `SpatialField` to the `open`
  list. **Candidate LESSONS line:** *an `OfNat X 0` / `Membership X (Set Pkg.X)` pair in
  `research/*.lean` probes almost always means `autoImplicit` auto-bound a name you forgot
  to `open`, not a missing `Zero` instance — compare the two sides of the `Membership`
  message before hunting instances.*

---

## 12. For the lead — what remains for `LocalTheoryAPI.solution` on the OpenAI route

`LocalTheoryAPI` lives only as a draft contract structure, `research/A01/Spec.lean:277`
(four fields: `horizon :283`, `solution :297-299`, `regularity :305-307`,
`horizon_lower_bound :338-343`); there is no Lean declaration of it under `formalization/`,
`vendor/` or `verification/` yet. `solution` must produce
`ClassicalSolutionR ν a f (horizon ν a f)` — the 9-field structure at
`verification/Contracts/V1/Data.lean:624-648`.

**Does `highOrder_bddAbove_all_orders_of_kbnd` already give `HasAprioriBound`? No.** Three
gaps remain between them, and only the first is a row today:

1. **The converse norm comparison** the lane-134 review flagged
   (`research/A01/REVIEW_A2B_INV.md:242-247`, verbatim): "Row **A3-L1·k** supplies
   `sobolevNormAt 2 (⇑(U t)) ≤ c·‖u t‖` — the *converse* direction. A comparison
   `‖u t‖ ≤ c'·(finitely many sobolevNormAt m (⇑(U t)))` is **not currently a row in
   `A3_SPLIT.md`** and should be added." Still not a row. Grönwall bounds the R³ side;
   `HasAprioriBound`'s `‖u‖ ≤ R` is the cylinder `SobolevSpace 1 (q+1)` side.
2. **Interval side** (`REVIEW_A2B_INV.md:248-250`): Grönwall gives `Ico 0 T₀`,
   `HasAprioriBound` needs the closed `Icc 0 T` for every `T ≤ S`.
3. **mild ⟹ energy** (`:251-255`): `HasAprioriBound` quantifies over an arbitrary *mild*
   Duhamel solution; eq:Rhigh is an energy identity for a regular solution.

Also note §9 above: for supplying `R` it is `highOrder_bddAbove_of_kbnd` (explicit constant,
`R` before `u`) that is usable, not the `BddAbove` export.

**Remaining rows, sizes, and the order I would attempt them.**

| # | row | size | depends on | note |
|---|---|---|---|---|
| 1 | **`D-euler-pairing`** (lane 140, in flight, uncommitted) | S–M | — | Euler side owes `∫ψ·(∂ⱼz)ᵢ = ∫(−∂ⱼψ)·zᵢ` per descended `L²` word (`research/D01/FINITE_ORDER_SPLIT.md:56`); gives `HasWeakDerivsL2 (⇑(U t)) m` for `m ≤ q−3`, enough for order 2 at `q ≥ 5`. Unblocks A3-L1·k **and** C1b |
| 2 | **A3-L1·k** | M | 1 | must hand `GronwallInstance.highOrder_bddAbove_of_kbnd` a real `Kbnd` in the recorded `hkbnd` shape. Per §7 / FINDING 3, the *interior* case is already free; the deliverable is the endpoint/uniform `Kbnd := c²·(‖u₀‖+1)²·T₀` |
| 3 | **converse comparison** `‖u t‖_{Sob 1 (q+1)} ≤ c'·(finitely many sobolevNormAt m (⇑(U t)))` | M, **unrowed** | 1 | add the row first; without it Grönwall never reaches `HasAprioriBound` |
| 3′ | interval widening `Ico 0 T₀ → Icc 0 T`, and the mild⟹energy bridge | S / M, **unrowed** | — | both flagged by the 134 review; cheap to state, cheap to forget |
| 4 | **A3-Tm** | M | 2,3 | one `T₀` carrying *every* order — `exists_local`'s `T` depends on `q`. Needed even to state `higherOrder_bddAbove`'s `∀ m` on real solutions |
| 5 | **T1** (`C^j_tH^k_x` all `j,k`, one-sided at 0) | M | 4, E1 (done) | `appendix-a:71-76` |
| 6 | **B1 / c3** (`velocity_smooth`, joint space-time `C^∞`; the `velocity t =ᵐ ⇑(U t)` hand-off) | **L — the single biggest blocker** (`A01_SPLIT.md:207-211`) | 5, A1, Sobolev embedding | existing rungs are C⁰/C¹, spatial-only or per-slice; the torus precedent left it as an unproved hypothesis |
| 7 | **B2** (assemble the 9-field `ClassicalSolutionR`) | S–M | 6, E1 (done), P3 | mostly plumbing once B1 lands |
| 8 | **X1** (package `LocalTheoryAPI`) | S | 7, P1, P3, T1, H1 | last |

Off the critical path, parallelisable now, no A3 dependency: **P2** (Liouville for
`L²`-harmonic, M), **P3** (physical eq:Rpressure, M), **m2 `pressure_recovery`** (M, needs
P2+P3), **A2b-c** (cross-order agreement, S–M), **H1** (M; note F9 — Grönwall gives an
*upper* bound on norms, never a *lower* bound on the horizon, and the tree lead
`exists_uniform_restart_time_invariant` uses the cylinder norm, so it is a candidate, not
literally H1).

Status of the other `LocalTheoryAPI` fields: `horizon` is modelled in lane 139
(`Horizon.lean:97,101`, unmerged); `regularity` is 2/4 discharged and registered as
`A01.regularity_partial` (m3 `projected`, m4 `pressure_potential`), with m1 `sobolev_smooth`
(L) and m2 `pressure_recovery` (M) open; `horizon_lower_bound` has no partial at all.

**Order I would attempt:** finish 1 (in flight) → open a row and a small lane for 3′
(cheap, unblocks nothing but prevents a late surprise) → 2 and 3 in parallel (both need 1) →
then 4 → 5 → 6. Run P2 / P3 / m2 / A2b-c as filler lanes throughout; leave H1 until after 4,
when it is clear whether the cylinder lead can be re-normed.

---

## 13. Commands run

```
$ . scripts/lean-env.sh
$ cd verification && LEAN_NUM_THREADS=6 lake build \
    NSFormalization.Section4.A01.ForceCap NSFormalization.Section4.A04.HighContinuationIntegral
  → Build completed successfully (9956 jobs).
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.GronwallInstance
  → Build completed successfully (9957 jobs).
$ cd verification && lake env lean ../formalization/NSFormalization/Section4/A01/GronwallInstance.lean
  → EXIT=0, silent (0 bytes)
$ cd verification && lake env lean ../research/A01/axioms_a3_m2.lean
  → EXIT=0, 4 × [propext, Classical.choice, Quot.sound]
$ make check                            → EXIT=0 (13 policy tests OK; 30 work items consistent)
$ bash scripts/gates.sh NSFormalization.Section4.A01.GronwallInstance
  → make test OK, make test-mutations OK, check_contracts FAILS on staleness (§10 / FINDING 6)
$ python3 experiments/check_contracts.py --base-ref 0f7d31b
  → "base_compatibility_checked": true
$ cd verification && lake env lean /tmp/rev142/probe1.lean   → EXIT=0 (signatures, hstep verbatim, hf1 dropped)
$ cd verification && lake env lean /tmp/rev142/probe2.lean   → EXIT=0 (Kbnd collapse; kbnd_exists for T₀<T)
$ cd verification && lake env lean /tmp/rev142/probe3.lean   → EXIT=1 as designed (F1, F5 reproduced)
$ cd verification && lake env lean /tmp/rev142/probe4_spatialfield.lean → EXIT=0 (F3 does NOT fire when opened)
$ cd verification && lake env lean /tmp/rev142/probe4b.lean  → EXIT=1 (F3 reproduced verbatim)
$ cd verification && lake env lean /tmp/rev142/probe5.lean   → EXIT=0 (order literal rfl; T₀:=T; no ⊤-trap)
```
