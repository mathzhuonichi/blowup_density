# REVIEW — lane 145 (D01 · row D-quant), the quantitative finite-order datum constructor

Reviewer: opus, read-only, worktree `.claude/worktrees/145-D01-quantitative-constructor`, HEAD `f7e18fd`
(base `origin/erenup/integration` at `ed22b2f`).  Probes written to `research/D01/probes/rev145_*.lean`.

## verdict: **ACCEPT-WITH-NOTES**

The mathematics is right, the proofs are real, every gate is green, and the negative checks break in
exactly the expected places.  All notes are cosmetic or planning-level; none blocks the merge.

---

## 1. What the lane claims

Three deliverables making lane 132's `exists_isSobolevDatum_of_memLp_derivs` quantitative:

1. order-0 bound `‖orderZeroDatum hz‖ ≤ ‖hz.toLp‖` (`c₀ = 1`);
2. raising bound `‖A'‖² ≤ 4·(‖A‖² + ∑ⱼ‖C j‖²)`;
3. the quantitative constructor `HasWeakDerivsL2Bound z M m → ∃ A, IsSobolevDatum m z A ∧ ‖A‖² ≤ 16^m·M`,
   transferred to *any* datum by `isSobolevDatum_unique`, with the `m = 2` instance `‖A‖² ≤ 256·M`
   and a non-vacuity lemma for `SmoothL2Field`.

Plus a three-step reading of what A3-L1·k still needs (`ATTEMPTS_FINITE_ORDER_NORM.md` §"三步分解").

## 2. What is actually in Lean

`formalization/NSFormalization/Section4/D01/FiniteOrderNorm.lean`, 463 lines, **16** declarations
(the ATTEMPTS says 15 — see F5), no `sorry`/`admit`/`axiom`/`native_decide`, no `set_option`.

**§0 — the Pythagoras identity is genuine.**  `eLpNorm_component_sq_sum` (`:68`) is proved from
`EuclideanSpace.norm_eq` fibrewise + `lintegral_finsetSum'`, with real measurability side conditions
(`hmeas` via `AEStronglyMeasurable.enorm.pow_const`); `norm_toLp_component_sq_sum` (`:98`) descends it
to real norms with `ENNReal.toReal_sum` and honest `≠ ∞` witnesses from `memLp_component`.  Not a
`simp` shortcut, not assumed.

**§1 — no direction error in the order-0 chain.**  I opened the three tree lemmas:

| cited factor | actual statement | direction |
|---|---|---|
| `Paper3.cyclesToAngularRealVector_norm_le` (`AngularRealVectorBochner.lean:24`) | `‖cyclesToAngularRealVector s v‖ ≤ frequencyUnit ^ \|s\| * ‖v‖` | `≤` |
| `Paper3.realProjectionTo_norm_le` (`RealPositiveDensity.lean:41`) | `‖realProjectionTo s h‖ ≤ ‖h‖` | `≤` |
| `MeasureTheory.Lp.norm_fourier_eq` | equality (Plancherel) | `=` |

So the worker's claim "`≤` is what the tree provides" is **confirmed**: the tree states the two
transport factors as inequalities, and the lane uses `abs_zero, Real.rpow_zero, one_mul` (`:123`) to
turn `frequencyUnit ^ |0|` into `1`.  Every inequality points the safe way for an *upper* bound on
`‖orderZeroDatum‖`; nothing is silently assumed `≤ 1` in the direction where `= 1` would be needed.
`orderZeroDatum hz = cyclesToAngularRealVector 0 v` is `rfl` against `OrderZeroDatum.lean:96` — checked.
(The `OrderZeroDatum.lean:40-53` "absent piece" citation is **correct**; the lane proves the Pythagoras
half of it and legitimately sidesteps the vector-isometry half, which is only needed for `=`, not `≤`.)

**§2 — the constants are real, the `4` is sharp for the inequality as stated.**
`coord_smul_deriv_ae` (`:150`) re-derives `(2πi)·(ξⱼ·(A i)) =ᵐ frequencyUnit·(C j i)` from
`db_cycles_full` (`FiniteOrderConstructor.lean:95`).  `frequencyUnit := 2 * Real.pi`
(`Source/FourierConvention.lean:15`) and `hk` (`:224`) proves `‖2πi‖ₑ = ‖(frequencyUnit:ℂ)‖ₑ`
honestly (`Complex.norm_I`, `abs_of_pos Real.pi_pos`), so the two constants **cancel exactly** and
`eLpNorm_coord_smul_eq` is an *equality*, not a bound — no slack there.
`norm_raiseHilbert_le` (`:236`) then gives the four-term `‖raise (A i)‖ ≤ ‖A i‖ + ∑ⱼ‖C j i‖` via
`norm_raiseIntegrand_le` (`FiniteOrderDatum.lean:105`) + `eLpNorm_add_le`/`eLpNorm_sum_le`, and the
`nlinarith` at `:321` is the genuine `(a+b₀+b₁+b₂)² ≤ 4(a²+b₀²+b₁²+b₂²)` (six `sq_nonneg` cross terms,
equality when all four are equal).  **4 is the sharp Cauchy–Schwarz constant for that inequality.**
See F2 for why the *route* is nevertheless 4× lossy per order.

**§3 — the hypothesis is honest and non-vacuous.**  `HasWeakDerivsL2Bound` (`:352`) is structurally
`HasWeakDerivsL2` with `(eLpNorm · 2 volume).toReal ^ 2 ≤ M` conjoined at every node; because
`MemLp` is conjoined at the same node, the `.toReal` cannot silently be the `⊤ ↦ 0` junk value, and
`0 ≤ M` follows from the predicate.  `hasWeakDerivsL2_of_bound` (`:368`) proves the forgetful map.
The induction (`:375`) really multiplies by 16: `4` (Cauchy–Schwarz) × `4` (`1 + 3` directions) —
mutation B below turns the step's closing goal into `M * 4^m * 16 = M * 4^m * 4`, which is the
arithmetic in the clear.

**Non-vacuity, concrete.**  `research/D01/probes/rev145_nonvacuity.lean` (compiles, exit 0) builds a
genuinely **nonzero, smooth, compactly supported** field (`ContDiffBump` × `EuclideanSpace.single 0 1`,
with `probeField 0 = EuclideanSpace.single 0 1` proved), packages it as a `SmoothL2Field`, and runs the
whole `m = 2` chain end to end to `∃ M A, HasWeakDerivsL2Bound probeField M 2 ∧ IsSobolevDatum 2 … ∧
‖A‖² ≤ 256·M` with a finite real `M`.  The same probe's `#check @IsSobolevDatum` confirms the module
resolves D01's copy (`SmoothDatum.lean:237`), not A02's (`SolutionClass.lean:79`) — no `open` ambiguity.

---

## 3. Findings

### F2 · medium (mathematical note, not a defect) — `16^m` is 4× lossy per order; the sharp constant is `4^m`

The brief asks whether `4` is Cauchy–Schwarz or hidden slack.  Answer: `4` is the sharp constant *of
the inequality proved*, but the inequality itself is not the sharp route.  Since
`sobolevBesselWeight 1 ξ = (1+‖ξ‖²)^{1/2}` and `‖ξ‖² = ∑ⱼ ξⱼ²` on `EuclideanSpace`, Plancherel gives the
**identity**

```
‖raiseHilbert (A i)‖²_{L²} = ‖A i‖² + ∑ⱼ ‖(ξⱼ)·(A i)‖² = ‖A i‖² + ∑ⱼ ‖C j i‖²
```

(the second equality is exactly this lane's own `eLpNorm_coord_smul_eq`).  Routing instead through the
pointwise triangle bound `√(1+‖ξ‖²) ≤ 1 + ∑ⱼ|ξⱼ|` + `eLpNorm_add_le` costs the factor 4.  With the
identity, `c_{m+1} = 4·c_m` and `c_m = 4^m`, i.e. **16 at `m = 2`, not 256**.  The §0 machinery the lane
already has (`lintegral_finsetSum'`) is what such a proof needs.

Answer to "is `16^m` what `‖u‖_{H^m} ≲ ∑‖∂^α u‖` gives up to constants": yes *up to an `m`-dependent
constant* — both are `O(C^m)` with `C` depending only on the dimension — but `16^m` is not the constant
that comparison gives; `4^m` is (with this lane's normalization, where `M` uniformly bounds each single
derivative rather than their sum).  **Irrelevant to the consumer**: A01's `Kbnd` needs only some
`t`-free constant.  Record as the D01 simplifier/V2 item; do not block.

### F6 · medium (planning correction) — A3-L1·k step (i) is already done in the tree

`ATTEMPTS_FINITE_ORDER_NORM.md:56-62` and the new `A3_SPLIT.md` row list "(ii) the `sobolevNormAt 2 = ‖A‖`
identification" as a residual "obligation on the A04 side".  It is **already proved**, twice:

* `A04.Forcing.sobolevENorm_eq` (`Section4/A04/Forcing.lean:126`): `IsSobolevDatum s z A → sobolevENorm s z = ‖A‖ₑ`;
* `A03.VectorTameProduct.sobolevENorm_eq` (`Section4/A03/VectorTameProduct.lean:71`), a second copy;
* and the `≤` half alone — all A3-L1·k needs — is `D01.sobolevENorm_le_of_isSobolevDatum`
  (`Section4/D01/SmoothDatum.lean:309`).

Probe `research/D01/probes/rev145_a04_bridge.lean` (compiles, exit 0) discharges steps (i)+(ii)
*together* in twelve lines:

```lean
theorem probe_sobolevNormAt_le (u : SpaceTimeField) (t M : ℝ)
    (h : HasWeakDerivsL2Bound (fun x => u (t, x)) M 2) :
    sobolevNormAt ((2 : ℕ) : ℝ) u t ≤ 16 * Real.sqrt M
```

Fix: strike residual (ii) from `A3_SPLIT.md`'s D-quant note; the residual is **only** the Euler side.

### F7 · info — the exact statement the A01 glue lane must prove

Lane 140's `Section4/A01/EulerPairing.lean` (on integration, **not in this worktree** — that is why
the worker could not open it) already gives the *qualitative*
`hasWeakDerivsL2_of_cylinder : HasWeakDerivsL2 (⇑U) m` (`:340`) by induction over descended derivative
words.  The missing lane is its quantitative twin, with the bound threaded through the same induction:

```lean
theorem hasWeakDerivsL2Bound_of_word {q : ℕ} (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u) :
    ∀ (m n : ℕ) (hn : n ≤ q) (_hnm : n + m + 3 ≤ q) (w : Fin n → Fin 4)
      (Zw : EulerMeanSolenoidal.L2), ordinaryLift Zw = word 1 u hn w →
      NSFormalization.Section4.D01.HasWeakDerivsL2Bound (⇑Zw) (‖u‖ ^ 2) m

theorem hasWeakDerivsL2Bound_of_cylinder {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ, sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (m : ℕ) (hm : m + 3 ≤ q + 1) :
    HasWeakDerivsL2Bound (⇑U) (‖u‖ ^ 2) m
```

Note the bound is literally `M := ‖u t‖²_{SobolevSpace 1 (q+1)}` with **constant 1**, so A3-L1·k's
`t`-free constant is `c = 16` (from `‖A‖² ≤ 256·M`).  It needs `q ≥ 4` at `m = 2`.

Its whole analytic content is two facts, both verified to hold *as stated* in
`research/D01/probes/rev145_a3l1k_glue.lean` (compiles, exit 0):

```lean
theorem probe_norm_word_le {q n} (u : SobolevSpace 1 q) (hn : n ≤ q) (w : Fin n → Fin 4) :
    ‖word 1 u hn w‖ ≤ ‖u‖ := norm_le_pi_norm (u : SobolevWord q → LiftL2 1) _
-- (SobolevSpace is a submodule of the finite word-indexed product; its norm is the sup norm)

theorem probe_eLpNorm_descend … (hZw : ordinaryLift Zw = word 1 u hn w) :
    (eLpNorm (⇑Zw) 2 volume).toReal ^ 2 ≤ ‖u‖ ^ 2
-- (Lp.norm_def + ordinaryLift.norm_map: `ordinaryLift` is a `→ₗᵢ[ℝ]`, MeanOrdinaryLift.lean:24)
```

So the remaining lane is bookkeeping over lane 140's existing induction, not new analysis.  The
worker's prose ("each word's `L²` norm is bounded by `‖u t‖_{SobolevSpace 1 (q+1)}`") is correct; the
mechanism is the sup norm on the word-indexed array plus the `ordinaryLift` isometry.

### F3 · low — `coord_smul_deriv_ae` is a verbatim duplicate of code inside `memLp_coord_smul_datum`

`FiniteOrderNorm.lean:161-203` is line-for-line the `have heq` block of
`FiniteOrderConstructor.lean:171-221` (diffed; the only differences are line wrapping, two comments and
one level of indentation).  The ATTEMPTS says so honestly and the reason given (the `have` is not
exported and cannot be recovered from the `MemLp` conclusion) is **correct** — I checked
`memLp_coord_smul_datum`'s statement, which returns only `MemLp`.  Fix for the D01 simplifier lane (not
this one): hoist `coord_smul_deriv_ae` into `FiniteOrderConstructor.lean` and rewrite
`memLp_coord_smul_datum` as its ten-line consequence; both public statements stay byte-identical and
~50 duplicated lines disappear.

### F4 · low — three `file:line` citations are off (the LESSONS "line numbers propagate" trap)

| written | actual | where |
|---|---|---|
| `AngularRealVectorBochner.lean:26` | **`:24`** (`:26` is the first proof line) | `FiniteOrderNorm.lean:19`, `ATTEMPTS…:13`, `FINITE_ORDER_SPLIT.md` row D-quant |
| `RealPositiveDensity.lean:40` | **`:41`** | `FiniteOrderNorm.lean:23`, `ATTEMPTS…:15`, row D-quant |
| `FiniteOrderDatum.lean:115` | **`:105`** | `ATTEMPTS…:32` |

`OrderZeroDatum.lean:40-53`, `FiniteOrderConstructor.lean:269`, `Forcing.lean:74`, `DatumPathContinuity.lean:103`
all check out.  Cheapest fix: correct the two `.md` files only and leave the module docstring for the
simplifier lane (changing it forces a rebuild for a comment).

### F5 · low — one declaration is not in the axiom audit

The module has **16** declarations; `research/D01/axioms_finite_order_norm.lean` prints 15.  Missing:
`hasWeakDerivsL2_of_bound` (`FiniteOrderNorm.lean:368`).  One-line fix: add
`#print axioms hasWeakDerivsL2_of_bound` after line 23, and change "15 declarations" to "16" in
`ATTEMPTS_FINITE_ORDER_NORM.md:4`.

### F8 · low — the module is outside every registered contract closure

`experiments/build_changed_lean.py` reports `Changed Lean modules: NSFormalization.Section4.D01.FiniteOrderNorm`,
so CI compiles it **on this PR**; but nothing under `verification/` imports it, so after the merge it
falls out of `make test` (same status as `FiniteOrderDatum.lean`, already noted in
`FINITE_ORDER_SPLIT.md`).  Add it to the next D01 contract bundle.

### F9 · low — "`c₀ = 1` is sharp" is prose, not a theorem

`ATTEMPTS…:21-22` asserts the transport/projection factors "are in fact isometries on the relevant
subspace at `s = 0`".  Nothing in Lean certifies that; what is certified is the `≤`, which is the
correct and only needed direction.  Keep the sentence but read it as commentary.

---

## 4. Commands and results

All from the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake from `verification/`.

```
$ lake build NSFormalization.Section4.D01.FiniteOrderNorm
EXIT=0   Build completed successfully (9927 jobs).
         (every warning in the log is pre-existing upstream: Source/FiniteHilbertBochner,
          Source/RealSobolev, Paper3/*, vendor/HeliCorgi/Formal/*; zero lines mention
          FiniteOrderNorm — `grep -c FiniteOrderNorm build.log` = 0)

$ lake env lean ../formalization/NSFormalization/Section4/D01/FiniteOrderNorm.lean
EXIT=0   (0 bytes of output)

$ lake env lean ../research/D01/axioms_finite_order_norm.lean
EXIT=0   15 lines, each exactly:
         '…' depends on axioms: [propext, Classical.choice, Quot.sound]
         (eLpNorm_two_sq, eLpNorm_component_sq_sum, norm_toLp_component_sq_sum,
          norm_orderZeroDatum_le, coord_smul_deriv_ae, eLpNorm_coord_smul_eq,
          norm_raiseHilbert_le, norm_raise_le, HasWeakDerivsL2Bound, weakDerivsBound_mono,
          exists_isSobolevDatum_norm_le, norm_isSobolevDatum_le_of_memLp_derivs,
          norm_isSobolevDatum_le_two, weakDerivsBound_mono_le,
          exists_hasWeakDerivsL2Bound_smooth)   — see F5 for the 16th declaration

$ grep -nE 'sorry|admit|\baxiom\b|native_decide|set_option' <module> <axioms file>
         only FiniteOrderNorm.lean:39, inside the module docstring ("No `sorry`, no `axiom`")

$ make check                                  EXIT=0  (13 policy tests OK; 30 work items consistent)
$ make test                                   EXIT=0  (10148 jobs; every registered contract
                                                      "checked; standard logical axioms only")
$ make test-mutations                         EXIT=0  implementation_refactor: accepted /
                                                      admitted_proof, extra_axiom,
                                                      weakened_hypothesis: rejected as required
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
                                              EXIT=0  base_compatibility_checked: true
$ python3 experiments/build_changed_lean.py   Changed Lean modules: NSFormalization.Section4.D01.FiniteOrderNorm
```

### Negative checks (three substantive mutations, none a dropped argument)

Copies of the module under `research/D01/probes/`, typechecked with `lake env lean`; none is in the build.

**A · `rev145_mutA_drop_sum.lean`** — `norm_raise_le`'s conclusion changed to `≤ 4 * ‖A‖ ^ 2`
(the `+ ∑ⱼ ‖C j‖²` term deleted).  EXIT=1:

```
rev145_mutA_drop_sum.lean:312:23: error: unsolved goals
case calc.step
…
hcomp : ∀ (i : Fin 3), ‖raiseHilbert (A.ofLp i) ⋯‖ ^ 2 ≤ 4 * (‖A.ofLp i‖ ^ 2 + ∑ j, ‖(C j).ofLp i‖ ^ 2)
⊢ 4 * (‖A‖ ^ 2 + ∑ j, ‖C j‖ ^ 2) ≤ 4 * ‖A‖ ^ 2
```

i.e. the derivative term is genuinely load-bearing in the vector assembly.

**B · `rev145_mutB_4pow.lean`** — the induction constant `(16 : ℝ)` replaced by `(4 : ℝ)` throughout
(and `256`→`16`, so only the raising step is under test).  EXIT=1:

```
rev145_mutB_4pow.lean:410:37: error: unsolved goals
…
hAnorm : ‖A‖ ^ 2 ≤ 4 ^ m * M
hCnorm : ∀ (j : Fin 3), ‖C j‖ ^ 2 ≤ 4 ^ m * M
⊢ M * 4 ^ m * 16 = M * 4 ^ m * 4
```

This is the clean confirmation that the step multiplies by **16 = 4 (Cauchy–Schwarz) × 4 (1 + 3 directions)**.

**C · `rev145_mutC_64.lean`** — the `m = 2` constant `256` replaced by `64`.  EXIT=1:

```
rev145_mutC_64.lean:426:41: error: unsolved goals
hb : ‖A‖ ^ 2 ≤ 16 ^ 2 * M
⊢ False
```

### Non-vacuity and glue probes (all compile, EXIT=0)

```
research/D01/probes/rev145_nonvacuity.lean    concrete nonzero ContDiffBump field → the full
                                              m = 2 chain with a finite real M; also
                                              #check @IsSobolevDatum → D01's copy, not A02's
research/D01/probes/rev145_a04_bridge.lean    steps (i)+(ii) of A3-L1·k in 12 lines (F6)
research/D01/probes/rev145_a3l1k_glue.lean    the two facts the Euler-side lane needs (F7)
```

## 5. Recommendation

Merge.  Before merging, apply the two one-line record fixes (F5 axiom line + "16 declarations",
F4 line numbers in the two `.md` files); leave F2 (sharper `4^m`) and F3 (hoist the duplicated
transport) to the D01 simplifier lane, and strike A3-L1·k residual (ii) per F6 when recording.
