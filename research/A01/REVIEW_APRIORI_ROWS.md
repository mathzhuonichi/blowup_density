# REVIEW — lane 149 (A01 residual a-priori rows), `Section4/A01/AprioriRows.lean`

Reviewer: opus, read-only. Worktree `.claude/worktrees/149-A01-a3-widen-converse`, branch
`erenup/149-A01-a3-widen-converse`, HEAD `06bbef6`. No lane file edited, no git state changed;
nine probe files added under `research/A01/probes/` (`rev149_*.lean`: five checks, four
mutations) and this report.

**Verdict: ACCEPT-WITH-NOTES.** All seven theorems compile, the nine `#print axioms` are the
standard three, the statements say what the records claim they say, the `hword_jet` gap is real and
honestly isolated, and four mutations break as predicted. Five notes: one hypothesis that is
stronger than it needs to be (with a compiled one-line generalization), one over-claim in the
records about invariance, two residual rows missing from the audit, and two cheap things the audit
mis-ranks (both settled by probes here: the *cap* at `T₀ = T` is provable in 15 lines, and the
`Ico → Icc` step the consumer actually needs is free at the cylinder level).

---

## 1. What the lane claims

Two of the residual rows between an assumed sup-bound `‖u‖ ≤ R` and `HasAprioriBound`
(`Horizon.lean:106`), as listed in `research/A01/REVIEW_ORDER_TWO_CAP.md` §"Residual-row audit"
and `research/A01/A3_SPLIT.md:263`:

* **(iii)** the `Ico → Icc` endpoint widening for `T₀ < T` — the lane-147 cap on the closed window,
  and the lane-142 Grönwall conclusion on the closed window, both with unchanged constants;
  `T₀ = T` deliberately not attempted;
* **(ii)** the converse norm comparison (cylinder array norm ≤ energy norm), claimed proved
  **modulo one named hypothesis** `hword_jet`, and with a correction to the audit's naive
  statement: route through the smooth slice `z = v(t,·)`, not through `⇑(U t)`.

## 2. What is actually in Lean (claim by claim)

### (iii) widening — three theorems, all genuine

**`AprioriRows.lean:96` `kbnd_of_sup_bound_Icc`.** Hypothesis list is token-identical to lane 147's
`OrderTwoCap.lean:213` `kbnd_of_sup_bound` except that `(_hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T)` becomes
`(hT₀T : T₀ < T)`; conclusion `Ico 0 T₀ → Icc 0 T₀`, same constant `256 * R ^ 2 * T₀`. The proof is
lane 147's with two changes (`lt_of_le_of_lt ht.2 hT₀T` for `htT`, and `ht.2` instead of `ht.2.le`
in the last `calc` step). Dropping `0 < T₀` is sound: for `T₀ < 0` the conclusion is vacuous
(`Icc 0 T₀ = ∅`), for `T₀ = 0` it is `0 ≤ 0`.

**`:136` `highOrder_bddAbove_of_kbnd_Icc`** and **`:155` `highOrder_bddAbove_all_orders_of_kbnd_Icc`**
are `GronwallInstance.lean:68` / `:115` instantiated at horizon `T` and restricted along
`Icc 0 T₀ ⊆ Ico 0 T` (2 and 4 lines). The constant really is the base theorem's, not a re-derived
lookalike: probe `rev149_checks.lean` §1 states the conclusion in `GronwallInstance`'s **own**
vocabulary (`forceSobolevENormL1`, `Cgron` opened from `A04`) and discharges it by the lane theorem
verbatim — compiles. (`A04.forceSobolevENormL1` is needed because `D01` exports a same-named
constant; opening both makes the bare name ambiguous. The lane's spelling is unambiguous.)

**Answer to brief item 1 — is the `Ico 0 T` hypothesis a real cost?** Yes, numerically, and the
records only half-say it. `highOrder_bddAbove_of_kbnd_Icc` demands `hkbnd` on the **full** horizon
`Ico 0 T`, which is strictly stronger than lane 147's output on `Ico 0 T₀`. The only tree lemma
that supplies it is `kbnd_of_sup_bound` at horizon `T₀ := T` (probe §2, compiles), whose value is
`Kbnd = 256·R²·**T**`, so the assembled exponential is `exp(Cgron·256R²T)`, not
`exp(Cgron·256R²T₀)`. `ATTEMPTS_APRIORI_ROWS.md:29` does say "not `256·R²·T₀`", but the module
docstring (`:24`) and the `A3_SPLIT` update say "keeping the **same** explicit bound", which is true
only at the level of the symbol `Kbnd`. Consequence worth recording: **the lane's two halves of
(iii) do not chain with each other** — `kbnd_of_sup_bound_Icc` produces a cap on `Icc 0 T₀`,
`highOrder_bddAbove_of_kbnd_Icc` consumes one on `Ico 0 T`. See note **N1** for the fix.

**`T₀ = T` is not claimed.** Mutation M4 (`rev149_mut4_endpoint.lean`) instantiates the widened row
at `T₀ := T` and is rejected for want of `T < T` (error quoted in §5).

**What the consumer actually provides.** `HasAprioriBound` (`Horizon.lean:106`) hands you `T ≤ S`
and a `u : C(Icc 0 T, SobolevSpace 1 (q+1))` constrained *only* by the Duhamel equation, and asks
for `‖u‖ ≤ R` — the `ContinuousMap` sup over the **closed** `Icc 0 T`. It provides no `hkbnd`, no
`ClassicalSolutionR`, no `hcont`, and no angle invariance. So these rows are not consumed directly;
they are steps in a bootstrap whose circularity (`Kbnd` depends on the very `R`) is the known
A2b-a′/A3-Tm/H1 spine.

### (ii) converse — backbone and reverse embedding proved, one hypothesis

**`:178` `sobolevSpace_norm_le_of_forall_word`** is exactly the converse of lane 147's
`norm_word_le`: `SobolevSpace 1 q` is a submodule of `SobolevWord q → LiftL2 1` with the Pi (sup)
norm (`vendor/…/Euler/CylinderSobolevSpace.lean:15,44,49,52`), `word 1 u hn w = u.val ⟨⟨n,_⟩,w⟩`
(`:66`), so `pi_norm_le_iff_of_nonneg` after destructuring the index. Correct and unimprovable.

**`:193` `eLpNorm_iteratedFDeriv_le_sobolevENorm_toReal`** = `Finset.single_le_sum` into
`jetSobolevENorm (q+1) z` (`DatumToJets.lean:127`) then `jetSobolevENorm_le_sobolevENorm`
(`:343`), then `.toReal` under `hfin`. Constant `jetSobolevConst (q+1)` (`:316`) is `n`-uniform and
`t`-free; the "one `(2π)^{q+1}`" description matches that definition's own docstring (`:313-315`).

**Brief item 2(c) — `hfin` / `⊤`.** Load-bearing, two ways. (a) Deleting it makes the lane's proof
fail (M3: `hrhs_top` loses its argument; `hfin` occurs only in the proof body, so lesson 077's
`autoImplicit` false-negative does not apply). (b) Probe §5 proves that at
`sobolevENorm (q+1) z = ⊤` the right-hand side is `0`, so the `hfin`-free statement would force
`eLpNorm (iteratedFDeriv ℝ n z) 2 volume = 0` for **every** smooth field with no order-`(q+1)`
datum — false for, e.g., a smooth `L²` field whose order-`(q+1)` jet is not `L²`. I did **not**
build such a field in Lean (it needs a bump series; nothing in the tree has one), so this is a
"would be false" argument, not a Lean refutation. Recorded as such.

**Brief item 2(a) — is `hword_jet` honest and isolated?** Yes.

* It is not a disguised assumption of the conclusion. At `n = 0` it reads `‖value 1 u‖ ≤ …`
  (probe §3: `word 1 u (Nat.zero_le q) Fin.elim0 = value 1 u` by `rfl`), i.e. one coordinate, not
  the array sup `‖u‖`. What it *does* do is carry the whole per-word content, so the added value of
  theorems 6/7 over the hypothesis is exactly the reverse embedding — which is separately proved
  and separately checked. The module and ATTEMPTS say precisely this.
* It is satisfiable in a genuine (if trivial) instance: probe §4 fires
  `sobolevSpace_norm_le_sobolevENorm` on `u = 0`, `z = 0` and gets a real conclusion. The lane's
  `axioms_apriori_rows.lean` exercises only the two components, never the assembly — see **N4**.
* It is one hypothesis, not a bundle: `hz`/`hfin` are discharged downstream for free by
  `DatumToJets.contDiff_slice` + `ClassicalSolutionR.sobolev`, as the ATTEMPTS says.

**Brief item 2(b) — is the "route through the smooth slice" correction right?** Yes for the proof;
the record slightly over-states it for the statement.

* Right: `jetSobolevENorm_le_sobolevENorm` requires `ContDiff ℝ ∞ z` (`DatumToJets.lean:343`), and
  `⇑(U t)` is an `Lp` representative, not a smooth function; and `EulerPairing`'s datum for `⇑U`
  exists only for `m + 3 ≤ q + 1` (`:352`), i.e. order `q − 2`, so `sobolevENorm (q+1) (⇑U)` is
  not constructible from the descent.
* Over-stated: the **conclusion** could still be phrased on `⇑(U t)` exactly as the audit's row (ii)
  asked, because the datum norm is an a.e. invariant. Probe §7 proves
  `sobolevENorm_congr_ae : z =ᵐ[volume] z' → sobolevENorm s z = sobolevENorm s z'` in 6 lines from
  `CarrierBridge.lean:79` `IsSobolevDatum.congr_field`. Under `hslice` the two statements are
  therefore equivalent; only the *proof* must go through the slice. (Cheap export; see **N5**.)

**Brief item 2(d) — how far do lane 140's tools get `hword_jet`, and what is missing?**

From `EulerPairing`, for a **spatial** word `w` of order `n` with `n + 3 ≤ q + 1`:
`exists_descend` (`:296`) gives `Zw` with `ordinaryLift Zw = word 1 u hn w`; `ordinaryLift` is a
linear isometry and `Lp.norm_def` gives `‖word 1 u hn w‖ = ‖Zw‖ = (eLpNorm (⇑Zw) 2 volume).toReal`
(this is lane 147's `eLpNorm_descend_le`, `OrderTwoCap.lean:81`); and `word_hasDerivAt` +
`weakDeriv_pairing_of_lift_hasDerivAt` (`:265`) make `⇑Zc` the distributional `j`-derivative of
`⇑Zw`. So the **norm** side is finished and what is missing is an *identification*, plus two
uncovered regimes:

1. **Angular words.** `hword_jet` quantifies over all `w : Fin n → Fin 4`, and direction `0` is the
   **circle** direction (`standardDirection 0 = (0,1)`, `EulerProof.lean:6529`; the spatial ones are
   `i.succ`, `:6535` — probe §6). No property of the spatial slice `z` controls those words. They
   vanish under angle invariance: probe `rev149_angular_words.lean` proves
   `word 1 u _ (Fin.cons 0 w) = 0` for angle-invariant `u` (orbit is constant ⇒ derivative `0`,
   by `HasDerivAt.unique`). A word with `0` in a non-leading slot vanishes by the same argument
   applied to its prefix (not formalized here). **So discharging `hword_jet` needs `hu`** — see
   note **N2**.
2. **Top three orders.** `exists_descend` needs `n + 3 ≤ q + 1`; `exists_ordinary_value`
   (`Source/OrdinaryCylinderDescent.lean:29`) needs `3 ≤ q` because the ordinary field is the
   `θ = 0` slice of a *continuous* representative (4-dimensional Sobolev embedding). So for
   `n ∈ {q−1, q, q+1}` there is no ordinary field at all — and `‖u‖`, being the sup over **all**
   words up to `q+1`, always contains those three orders. Raising `q` does not help: the sup
   always reaches the top. This is a second, independent gap, correctly flagged in the ATTEMPTS.

**The carrier-bridge lemma that would discharge `hword_jet`** (row (i)/B1-B2), stated precisely:

```lean
-- (a) descent-to-classical-jet identity, for spatial words within the descent's reach
theorem word_descent_ae_partial {q n : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1:ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    {z : Space → Space} (hz : ContDiff ℝ ∞ z) (hUz : (⇑U) =ᵐ[volume] z)
    (hn : n + 3 ≤ q + 1) (w : Fin n → Fin 3) (Zw : EulerMeanSolenoidal.L2)
    (hZw : ordinaryLift Zw = word 1 u (by omega) (fun i => (w i).succ)) :
    (⇑Zw) =ᵐ[volume] fun x => iteratedFDeriv ℝ n z x (fun i => coordinateVector (w i))

-- (b) jet-component bound (elementary: ContinuousMultilinearMap.le_opNorm at unit vectors)
theorem eLpNorm_jet_component_le (n : ℕ) (z : Space → Space) (w : Fin n → Fin 3) :
    eLpNorm (fun x => iteratedFDeriv ℝ n z x (fun i => coordinateVector (w i))) 2 volume
      ≤ eLpNorm (iteratedFDeriv ℝ n z) 2 volume

-- (c) angular words (proved in this review's probe, needs `hu`)
theorem word_angular_eq_zero … : word 1 u _ (Fin.cons 0 w) = 0

-- (d) the top three orders: an L²-level descent for angle-invariant lifts, i.e.
--     ∀ g : LiftL2 1, (∀ θ, translation 1 (0,θ) g = g) → ∃ G : EulerMeanSolenoidal.L2,
--       ordinaryLift G = g      -- Fubini on ℝ³ × S¹, *no* jet/regularity hypothesis
```

(a)+(b)+(c) give `hword_jet` for `n ≤ q − 2`; (d) is what removes the 3-order loss and covers
`n ∈ {q−1, q, q+1}`. (d) is the recommendation: the 3 orders are spent only on producing a
*continuous* representative to slice at `θ = 0`, which an `L²`-level disintegration does not need.
I did not check whether `EulerMeanSolenoidal.L2`'s mean/solenoidal constraints obstruct (d).

## 3. Gaps and residual audit (brief item 3)

The worker's post-lane list — (i) carrier bridge, now also owing `hword_jet`; (iv) `hinv`; the
`T₀ = T` endpoint; the restart spine A2b-a′/A3-Tm/H1 — is **accurate but still incomplete**, and two
of its cost labels are wrong. Re-ranked, cheapest first:

| row | exact obligation | cost | evidence |
|---|---|---|---|
| **(iii-b′) cylinder endpoint** | `‖u‖ ≤ R` on the closed `Icc 0 T` from a bound on `{t : ↑t < T}` | **free** | probe `rev149_cylinder_endpoint.lean` proves it for any `C(Icc 0 T, X)`, `0 < T`, `0 ≤ R` (continuity + `T - T/(n+2) → T`). The endpoint `HasAprioriBound` needs is **not** an energy-side obligation at all |
| **(iii-a′) cap at `T₀ = T`** | `kbnd_of_sup_bound_Icc` with `T₀ := T` | **S (15 lines)** | probe `rev149_endpoint_cap.lean` proves it, same constant `256·R²·T`: the pointwise bound is already unconditional on the closed `Icc 0 T`, so integrability at the endpoint is `ContinuousOn … Ioo 0 t` + `Ioo_ae_eq_Ioc` + `Integrable.mono'`. Only the **Grönwall output** at `t = T` is the hard eq:criterion endpoint (`highContinuationIntegral` needs `t < T`) |
| **(v) datum/forcing bridge** | `HasAprioriBound` is stated for `a : SmoothL2Field Space` and `F : Icc 0 S → SmoothL2Field Space`; the energy route needs `a ∈ initialClassR`, `f : SpaceTimeField` with `MemForceR f`, `MemL1Hm f`, plus `HasSmoothSobolevPath T w.velocity` and `hcont`. Nothing in `Section4/A01` connects `F` to `f` | **M–L, unlisted** | `grep MemForceR formalization/…/A01` hits only `ForceCap`, `GronwallInstance`, `AprioriRows`; every `Continuation*`/`Horizon` theorem speaks `F`/`sobolevPath`/`coefficients` |
| **(iv) `hinv`** | `∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t` for the `u` that `HasAprioriBound` quantifies over | M | as recorded — but it is now needed by (ii) as well, not only by the forward route (N2) |
| **(i) carrier bridge** | `hslice` + horizon matching + the four-part lemma of §2 above | **L** | unchanged; `hword_jet` is a genuine addition to its debt |
| **(iii-b) Grönwall output at `t = T`** | the eq:criterion endpoint | L | unchanged |
| **restart spine** | A2b-a′/A3-Tm/H1, and the circularity `Kbnd = Kbnd(R)` | L | unchanged |

## 4. Notes (what I would change; none blocks the merge)

* **N1 (statement, 1-line generalization, verified).** Give the two widened Grönwall rows an
  intermediate horizon: replace `(hT₀T : T₀ < T) (hkbnd : ∀ t ∈ Ico 0 T, …)` by
  `(hT₀T₁ : T₀ < T₁) (hT₁T : T₁ ≤ T) (hkbnd : ∀ t ∈ Ico 0 T₁, …)`. Strictly more general
  (`T₁ := T` is the current statement), same two-line proof, and it lets a caller keep
  `Kbnd = 256·R²·T₁`. Compiled as `rev149_generalized_horizon.lean`. Since `AprioriRows.lean` is
  not a frozen contract, this can be folded in now or in the A01 SIMP lane.
* **N2 (records, over-claim).** `ATTEMPTS_APRIORI_ROWS.md:126-128` and the `A3_SPLIT` update say
  "(iv) untouched — the converse is invariance-free". True of the *proved* part; false of the
  *gap*: `hword_jet` ranges over angular words, which only `hu` kills (probe
  `rev149_angular_words.lean`). Fix: "(iv) `hinv` is now also required by (ii): `hword_jet`'s
  angular words vanish only under angle invariance".
* **N3 (records, cost).** `A3_SPLIT`'s "(iii) `T₀ = T` is the hard endpoint" should be split:
  cap at `T₀ = T` is S (probe), Grönwall output at `t = T` is the hard one, and the endpoint the
  consumer really needs is free at the cylinder level (probe). Worth recording so the next lane
  does not pay for the wrong one.
* **N4 (conformance).** `research/A01/axioms_apriori_rows.lean` has non-vacuity for the backbone and
  the reverse embedding but none for the two assembled theorems (6/7), i.e. nothing exercises
  `hword_jet` at all. Probe §4 is a 6-line witness that can be pasted in. Also: `AprioriRows` is
  compiled on this PR (`build_changed_lean.py` lists it) but belongs to no registered-contract
  closure, so after merge `make test` will not compile it — same limitation already recorded for
  `OrderTwoCap`/`Propagation`; add both to the next A01 contract bundle.
* **N5 (cheap export).** `sobolevENorm_congr_ae` (probe §7, 6 lines) would let the converse be
  stated on `⇑(U t)` verbatim as residual row (ii) asks, and is reusable wherever `hslice` moves a
  datum norm across an a.e. equality.

Honesty check of the records: I opened every declaration cited by `ATTEMPTS_APRIORI_ROWS.md` at the
cited line — `DatumToJets.lean:316` (`jetSobolevConst`), `CylinderSobolevSpace.lean:44/49/52/66/70`,
`SmoothDatum.lean:388-390` (U1b(ii) "untouched"), `A3_SPLIT.md:261/263`, `Horizon.lean:106` — all
correct. The "failed / rejected approaches" section matches what the tree actually forbids
(`⇑U`'s datum stops at `q−2`; `DatumToJets` needs `ContDiff`; `zero_le` vs `bot_le`). The
`A3_SPLIT.md` edit is a pure append (2 lines).

## 5. Commands and results

All from `/data_8T/ping/blowup_density/.claude/worktrees/149-A01-a3-widen-converse`, after
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake run from `verification/`, one at a time.

| command | result |
|---|---|
| `lake build NSFormalization.Section4.A01.AprioriRows` | EXIT 0, `Build completed successfully (9981 jobs)`. Warnings only from replayed upstream modules (`Paper3.SobolevDirectionalDerivative` deprecation etc.); `grep AprioriRows` on the log: no hit |
| `lake env lean ../formalization/NSFormalization/Section4/A01/AprioriRows.lean` | EXIT 0, **0 bytes** |
| `lake env lean ../research/A01/axioms_apriori_rows.lean` | EXIT 0; all **9** declarations `depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `grep -nE 'sorry\|admit\|native_decide\|maxHeartbeats\|axiom'` on the two lane `.lean` files | only docstring/`#print axioms` hits; **zero** code hits, no `set_option` at all |
| `make check` | EXIT 0 (`test_contract_policy` 13 tests OK, `check_work_queue` 30 items consistent) |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | EXIT 0, `base_compatibility_checked: true` (no contract touched) |
| `python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run` | `Changed Lean modules: NSFormalization.Section4.A01.AprioriRows` |
| `lake env lean ../research/A01/probes/rev149_checks.lean` | EXIT 0, 0 bytes — §1 constant identity, §2 `Kbnd = 256R²T` at horizon `T`, §3 `word … Fin.elim0 = value` by `rfl`, §4 assembly non-vacuity, §5 `⊤`-collapse, §6 `standardDirection 0 = (0,1)`, §7 `sobolevENorm_congr_ae` |
| `lake env lean ../research/A01/probes/rev149_angular_words.lean` | EXIT 0, 0 bytes — angular words vanish under `hu` |
| `lake env lean ../research/A01/probes/rev149_endpoint_cap.lean` | EXIT 0, 0 bytes — the cap **at `T₀ = T`**, same constant |
| `lake env lean ../research/A01/probes/rev149_cylinder_endpoint.lean` | EXIT 0, 0 bytes — `Ico → Icc` is free for a `ContinuousMap` |
| `lake env lean ../research/A01/probes/rev149_generalized_horizon.lean` | EXIT 0, 0 bytes — N1's generalization |

### Negative checks (mutations — all four reproduce)

**M1 `rev149_mut1_le.lean`** — `T₀ < T` weakened to `T₀ ≤ T` in `kbnd_of_sup_bound_Icc`, lane proof
kept verbatim (`set_option autoImplicit false`):

```
error: Application type mismatch: The argument
  hT₀T
has type
  T₀ ≤ T
but is expected to have type
  T₀ < T
in the application
  lt_of_le_of_lt ht.right hT₀T
```

So `T₀ < T` is load-bearing **for this route** (it is what makes `hcont`'s `Ico 0 T` cover
`uIcc 0 t`). The statement at `T₀ = T` is not false — probe `rev149_endpoint_cap.lean` proves it by
a different integrability argument. Recorded that way rather than as "the hypothesis is necessary".

**M2 `rev149_mut2_const.lean`** — constant `jetSobolevConst (q+1)` replaced by `1`:

```
error: Application type mismatch: The argument
  jetSobolevENorm_le_sobolevENorm (q + 1) hz
has type
  jetSobolevENorm (q+1) z ≤ ENNReal.ofReal (jetSobolevConst (q+1)) * sobolevENorm (↑(q+1)) z
but is expected to have type
  jetSobolevENorm (q+1) z ≤ ENNReal.ofReal 1 * sobolevENorm (↑(q+1)) z
```

**M3 `rev149_mut3_nofin.lean`** — `hfin` deleted (used only in the proof body, so no `autoImplicit`
re-binding): `error: Unknown identifier 'hfin'` at the `hrhs_top` step.

**M4 `rev149_mut4_endpoint.lean`** — the widened Grönwall row used at `T₀ := T`:

```
error: Application type mismatch: The argument
  lt_irrefl T
has type
  ¬T < T
but is expected to have type
  T < T
```

confirming `T₀ = T` is genuinely out of the lane's scope.
