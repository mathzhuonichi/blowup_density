# REVIEW — lane 147 (A01 row A3-L1·k), `Section4/A01/OrderTwoCap.lean`

Reviewer: opus, read-only. Worktree `.claude/worktrees/147-A01-a3-l1k-glue`, branch
`erenup/147-A01-a3-l1k-glue`, HEAD `daf14ca`. No lane file edited; one probe added
(`research/A01/probes/rev147_checks.lean`) and this report.

**Verdict: ACCEPT-WITH-NOTES.** Every claim in the brief is reproduced. The Lean is correct, the
constants are honest, the plug-in into `GronwallInstance` is real, and three mutations break as
expected. The notes are one hypothesis that is stronger than it needs to be (verified weakening
given), one cheap missing export, and two over-claims in the records.

---

## 1. What the lane claims

Row A3-L1·k of `research/A01/A3_SPLIT.md`: turn the mild sup-bound `‖u‖ ≤ R` on the cylinder
Sobolev path into the Grönwall integral cap `Kbnd`, the last open hypothesis of
`Section4/A01/GronwallInstance.lean`. Three deliverables: (1) a *quantitative* twin of lane 140's
Euler pairing with constant 1 and `M := ‖u‖²`; (2) the order-2 comparison
`sobolevNormAt 2 ≤ 16·‖u‖`; (3) the cap `Kbnd := 256·R²·T₀` in the exact `hkbnd` shape.

## 2. What is actually in Lean (claim by claim)

**Claim 1 — quantitative Euler twin.** `OrderTwoCap.lean:90` `hasWeakDerivsL2Bound_of_word` and
`:112` `hasWeakDerivsL2Bound_of_cylinder`. Hypothesis lists are **token-identical** to lane 140's
`EulerPairing.lean:316` / `:340` (checked side by side: `u : SobolevSpace 1 (q+1)`, `hu` the angle
invariance, `U`, `hU : ordinaryLift U = value 1 u`, `m`, `hm : m + 3 ≤ q + 1`); only the conclusion
changes. `#check @hasWeakDerivsL2Bound_of_cylinder` prints

```
… → NSFormalization.Section4.D01.HasWeakDerivsL2Bound (↑↑U) (‖u‖ ^ 2) m
```

so the predicate is D01's, **not** a shadowed local copy (lesson 111 trap ruled out by `#check`,
not by `open`). Compared token for token with `D01/FiniteOrderNorm.lean:352`:

```
def HasWeakDerivsL2Bound (z : Space → Space) (M : ℝ) : ℕ → Prop
  | 0 => MemLp z 2 volume ∧ (eLpNorm z 2 volume).toReal ^ 2 ≤ M
  | (m+1) => (MemLp z 2 volume ∧ (eLpNorm z 2 volume).toReal ^ 2 ≤ M) ∧ ∀ j, ∃ w, … ∧ (pairing)
```

nothing weaker is proved: the recursive call at `:102` passes the **same** `M = ‖u‖ ^ 2` (constant 1,
no `16^k` drift), and the size clause at each level is discharged by `eLpNorm_descend_le` (`:80`),
which is `Lp.norm_def` + `ordinaryLift.norm_map` (`ordinaryLift` is a `→ₗᵢ[ℝ]`,
`vendor/…/Euler/MeanOrdinaryLift.lean:24`) + `norm_word_le`.

`norm_word_le` (`:74`) is `norm_le_pi_norm` on `SobolevWord q → LiftL2 1`. That is sound: the
cylinder Sobolev space is `ClosedSubmodule ℝ (SobolevWord q → LiftL2 period)`
(`vendor/…/Euler/CylinderSobolevSpace.lean:44,49`) with the **inherited Pi (sup) norm**
(`sobolevNormedAddCommGroup`, `:51`), and `word 1 u hn w = u.val ⟨⟨n,_⟩,w⟩` (`:66`) is literally a
component. So `‖word‖ ≤ ‖u‖` with constant 1 — correct.

`M = ‖u‖²` is the `ContinuousMap`-free array norm at fixed time: in
`hasWeakDerivsL2Bound_of_cylinder` the argument is `u : SobolevSpace 1 (q+1)` (an element, not a
path); the `ContinuousMap` sup norm only enters later, via
`ContinuousMap.norm_coe_le_norm u t : ‖u t‖ ≤ ‖u‖` at `:176`. ✔

**Claim 2 — order-2 comparison.** `:126` `sobolevENorm_two_toReal_le :
(sobolevENorm ((2:ℕ):ℝ) (⇑U)).toReal ≤ 16 * ‖u‖` under `hq : 4 ≤ q`. Route verified against the
cited declarations: `D01/FiniteOrderNorm.lean:420` `norm_isSobolevDatum_le_two` (`‖A‖² ≤ 256·M`)
and `A04/Forcing.lean:126` `sobolevENorm_eq` (`sobolevENorm s z = ‖A‖ₑ` for any datum) — **both
line numbers correct**. The `√` step is `nlinarith` from `a² ≤ 256b²`, `a,b ≥ 0`, `(a-16b)² ≥ 0`;
mathematically valid.

`q ≥ 4` bookkeeping: `hasWeakDerivsL2Bound_of_cylinder … 2 (by omega)` needs `2 + 3 ≤ q + 1`, i.e.
`4 ≤ q`. **`hq` is load-bearing** — dropping the binder (with `set_option autoImplicit false in`,
so lesson-077's silent-rebinding trap cannot hide it) gives

```
mutD_nohq.lean:132:53: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints  0 ≤ a ≤ 3   where a := ↑q
```

The consumer's `hq : 6 ≤ q` (`Horizon.lean:106`) is strictly stronger, so no mismatch.

Numeral defeq `(2:ℝ)` vs `((2:ℕ):ℝ)`: **confirmed by `rfl`**, `research/A01/probes/rev147_checks.lean`
example (1) (the worker's ATTEMPTS cites a now-vanished `/tmp/num.lean` — see Note 4).
`sobolevNormAt_two_le_of_cylinder` (`:144`) is then a `show`-unfold of
`A04.sobolevNormAt s u t = (sobolevENorm s (fun x => u (t,x))).toReal` (`Forcing.lean:74`),
`rw [hslice t]`, `exact`.

**Claim 3 — the cap.** `:164` `sobolevNormAt_two_sq_le_of_sup` (pointwise `≤ 256·R²`, no
integrability) and `:186` `kbnd_of_sup_bound`. The interval-integral bound is genuine, not a
formality: integrability comes from `hcont.pow 2 |>.mono hsub |>.intervalIntegrable` with
`hsub : uIcc 0 t ⊆ Ico 0 T` (needs `t < T`, i.e. `T₀ ≤ T`); the bound itself is
`intervalIntegral.integral_mono_on ht0 hII intervalIntegrable_const hle_pt`, then
`∫ const = t·256R² ≤ T₀·256R²` by `mul_le_mul_of_nonneg_right ht.2.le`. `0 < T₀` is genuinely
unused (named `_hT₀`, honest).

`#check @kbnd_of_sup_bound` prints the conclusion as

```
∀ t ∈ Set.Ico 0 T₀, ∫ (s : ℝ) in 0..t, A04.sobolevNormAt 2 v s ^ 2 ≤ 256 * R ^ 2 * T₀
```

which is `GronwallInstance.lean:73-74`'s `hkbnd` token for token with `v := w.velocity`,
`Kbnd := 256*R^2*T₀`. The plug-in probe `research/A01/probes/otc_plugin.lean` is real: it applies
`highOrder_bddAbove_of_kbnd hν ha hf hf1 w hpath hm hT₀ hT₀T (kbnd_of_sup_bound u U hu hU hq
w.velocity hslice hR (continuousOn_sobolevNormAt_velocity w 2) hT₀ hT₀T)` and the stated conclusion
hard-codes `Real.exp (A04.Cgron m ν * (256 * R ^ 2 * T₀))`, so `Kbnd` really unifies with the
lane's value. The continuity input is `A04.continuousOn_sobolevNormAt_velocity`
(`Section4/A04/Continuity.lean:105`, `ContinuousOn … (Ico 0 T)` from `w.sobolev m`) — a tree lemma,
no new assumption. **Beyond the tree's own inputs the probe adds exactly `hslice` and `hR`** (`u`,
`U`, `hu`, `hU`, `hq` are precisely what `Source/OrdinaryForcedLocal.lean:32` `exists_local` and
`Horizon.lean:166` `exists_local_shape_of_aprioriBound` already hand out). The same cap also fits
the all-orders consumer `highOrder_bddAbove_all_orders_of_kbnd` (`GronwallInstance.lean:120`),
same `hkbnd` signature.

## 3. Gaps / findings

**F1 (medium, statement strength — the one substantive note). `hslice` is stronger than the
tree can deliver and than the proof needs.** It asks for literal function equality
`(fun x => v (↑t, x)) = ⇑(U t)`. `⇑(U t)` is an `Lp` representative, defined only up to a.e.; lane
140 itself documents the hand-off as **a.e.** — `EulerPairing.lean:377`
`exists_isSobolevDatum_m_of_ae` with `(hv : v =ᵐ[volume] ⇑U)`, "the B1 hand-off
`velocity t =ᵐ ⇑(U t)`". Weakening is cheap and I verified it:
`research/A01/probes/rev147_checks.lean` example (4) proves the same
`(sobolevENorm 2 z).toReal ≤ 16·‖u‖` from `hz : z =ᵐ[volume] ⇑U`, by inserting one line
`IsSobolevDatum.congr_field hA hz.symm` before `sobolevENorm_eq`. *Fix:* in a follow-up (not this
lane's frozen file), restate `hslice` as `∀ t, (fun x => v (↑t, x)) =ᵐ[volume] ⇑(U t)` and route
deliverable 2 through `congr_field`. Leaving it as is does not make anything false; it just puts an
unnecessary obligation on the carrier-bridge row.

**F2 (low, missing cheap export — the `⊤ ↦ 0` trap).** The recorded statement
`(sobolevENorm 2 (⇑U)).toReal ≤ 16·‖u‖` is **vacuously true whenever the enorm is `⊤`** (probe
example (3)) — exactly the vacuity the A3-L1·k row itself warned about
("`sobolevENorm=⊤⇒sobolevNormAt=0`"). The *proof* does establish finiteness (it goes through a real
datum `A`), but a consumer reading only the statement does not learn it. *Fix:* export the one-liner
`sobolevENorm ((2:ℕ):ℝ) (⇑U) ≠ ⊤` (probe example (2), 4 lines, standard axioms) so the non-vacuity
is on the record, not only in the proof.

**F3 (low, over-claim in `A3_SPLIT.md`).** The lane's edit says the three rows are "now the **only**
gap between the a-priori sup-bound and `HasAprioriBound`". Too strong. `Kbnd = 256·R²·T₀` is a
function of the very `R` one is trying to establish, and the Grönwall output grows like
`exp(Cgron·256R²T₀)`, so rows (i)–(iii) close the *conditional* implication
"`‖u‖ ≤ R` ⇒ explicit high-order bound depending on `R`", not `HasAprioriBound` (which needs one `R`
fixed **before** `T ≤ S` and before `u`). Closing that still needs the restart/continuation rows
already in the same table (`A2b-a′`, `A3-Tm`, `H1`). *Fix (one line):* replace "the only gap between
the a-priori sup-bound and `HasAprioriBound`" with "the only gap between an **assumed** sup-bound
`‖u‖ ≤ R` and the Grönwall high-order bound; `HasAprioriBound` additionally needs A2b-a′ / A3-Tm /
H1".

**F4 (low, hygiene).** `ATTEMPTS_ORDER_TWO_CAP.md` cites `/tmp/num.lean` for the numeral check —
the volatile-probe mistake lesson 106 records. *Fix (one line):* point at
`research/A01/probes/rev147_checks.lean` example (1) instead.

### Residual-row audit (brief item 4)

The worker's three rows are **accurate but not complete**. Exact statements, plus what is missing:

| # | Exact obligation | Status |
|---|---|---|
| (i) carrier bridge / `hslice` discharge | produce `v : A02.SpaceTimeField` and `w : ClassicalSolutionR ν a f T` with `w.velocity = v` and `∀ t : Icc 0 T, (fun x => v (↑t,x)) = ⇑(U t)` (F1: should be `=ᵐ[volume]`), from the cylinder pair `(u,U)` of `Horizon.lean:166` / `exists_local` | **open, L.** Also requires the `ClassicalSolutionR`'s horizon `T` to be *the same* `T` as the cylinder path's `Icc 0 T` — `exists_local`'s `T` is chosen by the local theory, so this is a matching obligation the list does not name |
| (ii) converse norm comparison | `∃ C, ∀ t, ‖u t‖_{SobolevSpace 1 (q+1)} ≤ C · sobolevNormAt (q+1) (⇑(U t))` (`C` `t`-free) — the reverse of this lane's forward `sobolevNormAt 2 (⇑(U t)) ≤ 16·‖u t‖` | **open, M.** Note the order asymmetry: forward is order 2, converse must be order `q+1` (sup over all words up to `q+1`) |
| (iii) `Ico → Icc` widening | from `∀ t ∈ Ico 0 T₀, bound` to `∀ t : Icc 0 T₀, bound`, then `T₀ = T` | **open, but splits.** For `T₀ < T` it is genuinely cheap (S): `T₀ ∈ Ico 0 T`, so `continuousOn_sobolevNormAt_velocity` is available *at* `T₀` and the limit closes it. For `T₀ = T` it is the hard endpoint the 142 note already calls "row A3-L1·k's real content" |

**"mild ⇒ energy bridge" (third row of the 142 note) is subsumed** — it is row (i): the energy side
is `sobolevNormAt … w.velocity`, so producing the `ClassicalSolutionR` *is* the mild⇒energy bridge.
The ATTEMPTS says so and I agree.

**Missing from the list:** the inputs `hu` (angle invariance) and `U` itself for the `u` that
`HasAprioriBound` (`Horizon.lean:106`) quantifies over. That predicate constrains `u` only by the
Duhamel equation — not by angle invariance — whereas both `exists_local` and this lane need
`∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t`. Once that is in hand, `U` is free
(`Section4/A01/Continuation.lean:147` `forced_ordinary_descent`, which is the last eight lines of
`exists_local` factored out). So the real fourth row is **unit A2b's `hinv`**, already tracked
elsewhere in `A3_SPLIT.md` but absent from this lane's residual list.

**Cheapest of the residuals: (iii) restricted to `T₀ < T`** — pure interval/continuity bookkeeping
on lemmas that already exist. Then (ii); (i) is the largest.

### Non-blocking observations

* **CI coverage.** `OrderTwoCap` is compiled on this PR by `experiments/build_changed_lean.py`
  (dry-run confirms `Changed Lean modules: NSFormalization.Section4.A01.OrderTwoCap`), but it is in
  no registered-contract closure, so after merge `make test` will not compile it — the same
  limitation `A3_SPLIT.md` §4 already records for `Propagation.lean`. Add it to the next A01
  contract bundle. `research/A01/*.lean` (axioms + probes) are under none of
  `verification/ formalization/ vendor/NavierStokesAndEuler/`, so they are **never** CI-compiled —
  lesson 068's conformance-drift risk applies; the A01 SIMP/tester lane must re-run them.
* Non-vacuity is only the **zero** cylinder field (axioms file). That is a genuine conclusion
  (`HasWeakDerivsL2Bound 0 0 2`) but it is also the case where every inequality is `0 ≤ 0`. The
  worker's reason for not doing a nonzero witness (needs a real angle-invariant cylinder field plus
  its ordinary lift) is correct and matches what lane 137 had to build for `MemForceR`. F2's
  finiteness export is the cheap partial substitute and I recommend it instead.
* `exists_isSobolevDatum_norm_le`'s own norm conclusion is discarded at `:132` (`⟨A, hA, _⟩`) and
  re-derived via `norm_isSobolevDatum_le_two`; harmless (the latter has the numeral `256` already
  evaluated), flagging only for the simplifier lane.

## 4. Commands and results

All from `/data_8T/ping/blowup_density/.claude/worktrees/147-A01-a3-l1k-glue`, after
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake run from `verification/`.

| command | result |
|---|---|
| `lake build NSFormalization.Section4.A01.OrderTwoCap` | `Build completed successfully (9952 jobs)`, EXIT 0. 50 warnings, **all from replayed upstream modules** (`Source/PacketForceExtension`, `Source/ViscosityPacket`, `Paper3/SobolevDirectionalDerivative`, …); `grep OrderTwoCap` on the log: no hit, i.e. zero warnings from the lane's own lines |
| `lake env lean ../formalization/NSFormalization/Section4/A01/OrderTwoCap.lean` | EXIT 0, **0 bytes** |
| `lake env lean ../research/A01/axioms_order_two_cap.lean` | EXIT 0; all **8** declarations `depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `lake env lean ../research/A01/probes/otc_plugin.lean` | EXIT 0, 0 bytes (plug-in into `highOrder_bddAbove_of_kbnd` type-checks) |
| `lake env lean ../research/A01/probes/rev147_checks.lean` (new, this review) | EXIT 0, 0 bytes — (1) `((2:ℕ):ℝ) = (2:ℝ) := rfl`; (2) `sobolevENorm 2 (⇑U) ≠ ⊤` under the lane's hypotheses; (3) the `⊤ ↦ 0` vacuity of the bare `.toReal` bound; (4) the a.e. weakening of `hslice` |
| `make check` | EXIT 0 |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | EXIT 0, `base_compatibility_checked: true` (no contract touched by this lane) |
| `python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run` | `Changed Lean modules: NSFormalization.Section4.A01.OrderTwoCap` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|set_option\|maxHeartbeats'` on the 3 lane `.lean` files | one hit, `OrderTwoCap.lean:49` — **inside the module docstring** ("No `sorry`, no `axiom`"), stripped by `hooks/post_lean.py`'s block-comment filter; same wording as `D01/Transverse.lean:38`, `A04/PressureDrop.lean:46` etc. Zero code hits |

### Negative checks (mutations — all three reproduce)

1. **`256 → 64`** in `kbnd_of_sup_bound`'s conclusion (internal pointwise bound left at `256`):
```
/tmp/rev147/mutA_64.lean:219:27: error: unsolved goals
… ⊢ t * (256 * R ^ 2) ≤ T₀ * (256 * R ^ 2) → … = 64 * R ^ 2 * T₀   [ring failed]
```
2. **drop `hT₀T : T₀ ≤ T`** (with `set_option autoImplicit false in`, and the `t < T` step replaced
   by a bare `linarith` so no argument is merely omitted):
```
/tmp/rev147/mutB2.lean:203:25: error: linarith failed to find a contradiction
… _hT₀ : 0 < T₀   ht : t ∈ Ico 0 T₀   ht0 : 0 ≤ t   a✝ : T ≤ t   ⊢ False
failed
```
   i.e. without `T₀ ≤ T` the integrand is outside `hcont`'s and `hpt`'s domain — the hypothesis is
   load-bearing, not decorative.
3. **`M := ‖u‖` instead of `‖u‖²`** in the word-level induction:
```
/tmp/rev147/mutC_M.lean:95:49: error: Application type mismatch: The argument
  eLpNorm_descend_le u hn w Zw hZw
has type   (eLpNorm (↑↑Zw) 2 volume).toReal ^ 2 ≤ ‖u‖ ^ 2
but is expected to have type   (eLpNorm (↑↑Zw) 2 volume).toReal ^ 2 ≤ ‖u‖
```
   (the `L²` size clause of `HasWeakDerivsL2Bound` is on the **square**, so `M` must be `‖u‖²`;
   `‖u‖` would be false for `‖u‖ < 1`.)
4. **drop `hq : 4 ≤ q`** (with `autoImplicit false`): `omega could not prove the goal … 0 ≤ q ≤ 3`
   (quoted in §2).

Mutation sources and logs: `/tmp/rev147/` (volatile — the error text above is the record, per
lesson 106).

---

### For the lead

ACCEPT and merge. Then, in the A01 SIMP/tester follow-up (not a new-mathematics lane):
F2's 4-line finiteness export; F1's a.e. restatement of `hslice` **before** anyone starts the
carrier-bridge row; and the two one-line record fixes F3 (`A3_SPLIT.md` wording) and F4
(`/tmp/num.lean` citation).
