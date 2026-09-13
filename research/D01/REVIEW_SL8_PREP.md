# Review — lane 111 (`erenup/111-D01-p2-sl8-prep`, HEAD `213988a`)

Reviewer: opus, 2026-09-13.  Scope: `OrderZeroAlgebra.lean`, `MomentumSlice.lean`, `SL8_SPLIT.md`,
`ATTEMPTS_SL8_PREP.md`, `axioms_sl8_prep.lean`.  Base predates lanes 106 (PR #109) and 108 (PR #110),
both now merged into `origin/erenup/integration`; interface fit against them was checked separately
(§3, §5).

## Verdict: **ACCEPT-WITH-NOTES**

Everything the lane claims compiles, the axioms are clean, the statements say what the report says
they say, and — the strongest evidence — **the entire SL8_SPLIT table (rows i.1 … iii.3) was
re-assembled by the reviewer and compiles end to end**, producing
`SmoothSquareIntegrableJets (fun x => pressureGradient u.pressure t x)` (= P2) from nothing but the
lane's exports plus a verbatim transcription of lane 108's merged corollary.  The notes are
bookkeeping (stale blocker line, one off-by-2 line cite, one duplicated lemma that 106 now also
carries) and one small missing export.

---

## 1. Compiles / axioms / hygiene — PASS

```
$ . scripts/lean-env.sh
$ cd verification && LEAN_NUM_THREADS=6 lake build \
    NSFormalization.Section4.D01.OrderZeroAlgebra NSFormalization.Section4.D01.MomentumSlice
…
Build completed successfully (9921 jobs).
[exited with code 0]
```
(the only warnings in the log come from `vendor/HeliCorgi/Formal/*`, replayed, pre-existing.)

```
$ cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/OrderZeroAlgebra.lean
exit=0      (silent)
$ cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/MomentumSlice.lean
exit=0      (silent)
```

```
$ cd verification && lake env lean ../research/D01/axioms_sl8_prep.lean
'NSFormalization.Section4.D01.isSobolevDatum_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.orderZeroDatum_add' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.orderZeroDatum_sub' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.lerayComplement_orderZeroDatum_add' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.lerayComplement_orderZeroDatum_sub' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.memLp_pressureGradient_slice' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.memLp_temporalDerivative_slice' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.contDiff_temporalDerivative_slice' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.sum_partialDeriv_temporalDerivative_eq_zero' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.pressureGradient_apply' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.partialDeriv_gradient_eq_sndFDeriv' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.partialDeriv_pressureGradient_symm' … [propext, Classical.choice, Quot.sound]
exit=0
```
All 12 exported declarations, exactly the three standard axioms.

```
$ make check
…
python3 experiments/test_contract_policy.py
Ran 13 tests in 0.046s
OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
make-check-exit=0
```

Hygiene grep over both modules for `sorry|admit|axiom|native_decide|maxHeartbeats|set_option`:
two hits, both inside the module docstrings (`"No `sorry`, no `axiom`; …"`).  **No `set_option`,
no heartbeat bump, no `native_decide`, no real `sorry`/`axiom`.**

`git diff --stat` vs base: 5 files, 499 insertions, 0 deletions.  Nothing frozen was touched.

---

## 2. Statement fidelity — PASS

Signatures printed with `set_option pp.fullNames true` (`/tmp/rev111/probe_sig.lean`), abbreviated:

| declaration | hypotheses (exactly) |
|---|---|
| `isSobolevDatum_sub` | `{s} {z w} {A B}`, `SchwartzPairable z`, `SchwartzPairable w`, `IsSobolevDatum s z A`, `IsSobolevDatum s w B` → `IsSobolevDatum s (z - w) (A - B)` |
| `orderZeroDatum_add` | `hz hw : MemLp _ 2 volume` — **no continuity, as claimed** |
| `orderZeroDatum_sub` | `hz hw : MemLp _ 2 volume` — **no continuity** |
| `lerayComplement_orderZeroDatum_add/_sub` | `hz hw : MemLp _ 2 volume` |
| `memLp_pressureGradient_slice` | `u`, `ht : t ∈ Ioo 0 T` — **no `hf`** |
| `memLp_temporalDerivative_slice` | `u`, `hf : MemForceR f`, `ht : t ∈ Ioo 0 T` |
| `contDiff_temporalDerivative_slice` | `u`, `hf`, `ht` |
| `sum_partialDeriv_temporalDerivative_eq_zero` | `u`, `ht`, `x` — **no `hf`** |
| `pressureGradient_apply` | `p t y j` only (standalone) |
| `partialDeriv_gradient_eq_sndFDeriv` | `p t`, `hg : ContDiff ℝ ∞ (∇p slice)`, `hφ : ContDiff ℝ ∞ (p(t,·))`, `i j x` |
| `partialDeriv_pressureGradient_symm` | `u`, `ht`, `i j x` — **no `hf`** |

No hidden extra hypotheses anywhere; three results are even *weaker*-hypothesised than the report
claims (they do not need `hf`).

**Namespace observation (F-5 below).**  Despite `open NSFormalization.Section4.A02 (… MemForceR)`,
the enclosing namespace wins and the exported statements carry
`NSFormalization.Section4.D01.MemForceR` (from `D01/ForceClass.lean:158`), not A02's.  The two
in-tree copies are definitionally equal — checked:
`example : @NSFormalization.Section4.A02.MemForceR = @NSFormalization.Section4.D01.MemForceR := rfl`
compiles.  `D01/Pressure.lean` already has the same behaviour, so this is pre-existing and harmless.

### Non-vacuity — PASS (`/tmp/rev111/probe_vacuity.lean`, exit 0, no errors)

* Group 1: `MemLp (0 : Space → Space) 2 volume` is inhabited; `orderZeroDatum_add` and
  `isSobolevDatum_sub` instantiate on it.
* Group 2: `ClassicalSolutionR` carries `horizon_pos : 0 < T`, so `Ioo 0 T` is never empty
  (`nonempty_Ioo.mpr u.horizon_pos`).  Stronger: the reviewer **built a witness**,
  `def zeroSol {ν} : ClassicalSolutionR ν 0 0 1` (zero velocity/pressure/data/force), and
  `theorem memForceR_zero : MemForceR (0 : VelocityField)`, then instantiated
  `memLp_temporalDerivative_slice zeroSol memForceR_zero (t := 1/2)`.  Compiles.  The whole
  hypothesis package of `MomentumSlice` is therefore inhabited, not vacuous.

### Shape fit with lane 094 (real, in-tree) — PASS

`/tmp/rev111/probe_fit.lean` FIT 1, compiles, exit 0:

```lean
example (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) (ht : t ∈ Ioo (0:ℝ) T) :
    Leray.lerayComplement 0 (orderZeroDatum (memLp_temporalDerivative_slice u hf ht)) = 0 :=
  Leray.lerayComplement_eq_zero_of_transverse 0 _
    (orderZeroDatum_transverse_of_divergence_free
      (memLp_temporalDerivative_slice u hf ht)
      (contDiff_temporalDerivative_slice u hf ht)
      (fun x => sum_partialDeriv_temporalDerivative_eq_zero u ht x))
```
094's `orderZeroDatum_transverse_of_divergence_free` (`OrderZeroSymbol.lean:532`) wants
`hdiv : ∀ x, ∑ j, partialDeriv j z x j = 0`; 111's lemma supplies it with no coercion, no `show`.

### Shape fit with lane 108 (merged; statement transcribed) — PASS

108's module is not in this worktree and the worktree must not be rebased, so the reviewer
**transcribed 108's corollary verbatim** from
`git show origin/erenup/integration:formalization/NSFormalization/Section4/D01/OrderZeroCurl.lean`
(lines 510–516) and carried it as a hypothesis.  `/tmp/rev111/probe_fit.lean` FIT 2, exit 0:

```lean
example
    (h108 : ∀ {z : Space → Space} (hz : MemLp z 2 volume) (_hsmooth : ContDiff ℝ ∞ z)
      (_hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i),
      Leray.lerayComplement 0 (orderZeroDatum hz) = orderZeroDatum hz)
    (u : ClassicalSolutionR ν a f T) (ht : t ∈ Ioo (0:ℝ) T) :
    Leray.lerayComplement 0 (orderZeroDatum (memLp_pressureGradient_slice u ht))
      = orderZeroDatum (memLp_pressureGradient_slice u ht) :=
  h108 (memLp_pressureGradient_slice u ht)
    (contDiff_pressureGradient_slice u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩)
    (fun i j x => partialDeriv_pressureGradient_symm u ht i j x)
```
*What was compared:* the hypothesis type is a character-for-character copy of 108's binders; the
elaborator then confirmed 111's three terms fill them.  What is **not** verified is that the
transcription equals the merged `.olean` — but the text came straight out of `git show` of the
merged commit, and the three binder types are short.

---

## 3. Consistency with the tree — PASS with two duplication notes

**Imports.**  `OrderZeroAlgebra` imports `OrderZeroDatum`, `ForceClass`, `LerayDatum`; all three are
used (`orderZeroDatum`, `isSobolevDatum_add`/`_unique`/`schwartzPairable_of_memLp`,
`Leray.lerayComplement`).  `MomentumSlice` imports `Pressure`, `DivergenceTime`; both used.  No
unused imports, no restated definitions — both modules are pure theorem files with zero `def`s.

**No name collisions.**  Repo-wide grep for the 12 new names found exactly one other
`isSobolevDatum_sub`, at `Section4/A03/VectorTameProduct.lean:186`, in a *different namespace*
(`Section4.A03`) with a *different* statement: it needs `hs : 2 ≤ s` and `LocIntField F/G`, and its
conclusion is `IsSobolevDatum s (fun x => F x - G x) (A - B)`.  It cannot serve 111's purpose — the
SL8 seed lives at `s = 0`, where `2 ≤ 0` is false.  111's version (all `s`, `SchwartzPairable`) is
the right one and is not a duplicate.

### Duplication with lane 106 (merged, PR #109)

Two findings, both created by 111's base predating 106 — the worker's `ATTEMPTS` claim that
"`Section4/A01/PressureGauge.lean` … [is] absent from this worktree's `A01/` (only
`ConvectionDivergence`, `ProjectedEquation`, `RadialPotential`)" is **verified true**
(`ls` on the worktree vs `git ls-tree origin/erenup/integration`).

* **`pressureGradient_apply` is an exact duplicate.**  106 has it at
  `A01/PressureGauge.lean:84`, namespace `NSFormalization.Section4.A01.PressureGauge`, with the
  *identical* statement (only the bound variable is `x` instead of `y`).  111 adds a second copy at
  `D01/MomentumSlice.lean:119` in `NSFormalization.Section4.D01`.  Different namespaces, so **no
  compile clash after rebase**, but it is redundant.  Note 106 proves it from
  `pressureGradient_fderiv_slice` (Riesz form), 111 from `WithLp.ofLp_sum`/`PiLp.single_apply` —
  independently, which is a mild cross-check that the statement is right.
* **`partialDeriv_pressureGradient_symm` vs 106's `hasSymmetricJacobian_pressureGradient`.**
  Verified defeq-compatible in both directions (`/tmp/rev111/probe_106.lean`, exit 0):
  ```lean
  example {G} (h : HasSymmetricJacobian G) :
      ∀ (i j : Fin 3) (x : Space), partialDeriv i G x j = partialDeriv j G x i :=
    fun i j x => h.2 x i j                      -- 106 ⇒ 108's hcurl, by `rfl`
  example {G} (hd : Differentiable ℝ G)
      (h : ∀ i j x, partialDeriv i G x j = partialDeriv j G x i) :
      HasSymmetricJacobian G := ⟨hd, fun x i j => h i j x⟩
  ```
  **Which is the better shape?  106's.**  It takes a bare `hp : ContDiffOn ℝ ∞ p (Ico 0 T ×ˢ univ)`
  and `ht : t ∈ Ico 0 T` — so it works for any pressure field (not just `u.pressure` of a
  `ClassicalSolutionR`) and at `t = 0` as well; and its bundled `HasSymmetricJacobian` is what
  `A01/RadialPotential`'s gauge machinery consumes.  111's raw shape is the exact `hcurl` 108 wants,
  but that is one `.2 x i j` away from 106's.  **After rebase the assembly lane should call**
  `(hasSymmetricJacobian_pressureGradient u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩).2 x i j`
  **and a SIMP lane should retire `partialDeriv_pressureGradient_symm`,
  `partialDeriv_gradient_eq_sndFDeriv` and `D01.pressureGradient_apply`** in favour of 106's
  (106's `fderiv_apply_component` / `fderiv_fderiv_apply` are `private`, so if the second-derivative
  identity is wanted publicly, promote 111's `partialDeriv_gradient_eq_sndFDeriv` and delete 106's
  two privates — that is the one piece 111 has that 106 does not expose).

### Validation of `SL8_SPLIT.md` — every row checked, and the whole table re-assembled

**Cited line numbers.**  All verified by `grep -n` on this worktree / on
`origin/erenup/integration` for 108:

| cited | actual | ok |
|---|---|---|
| `Pressure.lean:196` `temporalDerivative_slice_eq` | 196 | ✓ |
| `Pressure.lean:376` `pressureGradient_slice_smoothSquareIntegrableJets` | 376 | ✓ |
| `OrderZeroDatum.lean:96` `orderZeroDatum` / `:103` `isSobolevDatum_orderZeroDatum` / `:67` `memLp_component` | 96 / 103 / 67 | ✓ |
| `LerayDatum.lean:255` `lerayComplement` / `:316` `lerayComplement_eq_zero_of_transverse` | 255 / 316 | ✓ |
| `ForceClass.lean:286` `isSobolevDatum_unique` / `:261` `isSobolevDatum_add` / `:213` `schwartzPairable_of_memLp` | 286 / 261 / 213 | ✓ |
| `LerayLowering.lean:155` `lerayComplement_lowerVectorL` / `:202` `isSobolevDatum_lower` / `:214` `isSobolevDatum_lower_iff` | 155 / 202 / 214 | ✓ |
| `DatumToJets.lean:298` `memHInfty_iff_smoothSquareIntegrableJets` | 298 | ✓ |
| `DatumToJets.lean:502` `contDiff_pressureGradient_slice` | **504** | ✗ off by 2 (F-4) |
| `OrderZeroSymbol.lean:532` `orderZeroDatum_transverse_of_divergence_free` | 532 | ✓ |
| `Longitudinal.lean:280` `lerayComplement_eq_self_of_curl_free` | 280 | ✓ |
| `DivergenceTime.lean:131` `spatialDivergence_temporalDerivative_eq_zero` | 131 | ✓ |
| `SmoothJets.lean:52` `SmoothL2.memLp` | 52 | ✓ |
| all `MomentumSlice`/`OrderZeroAlgebra` self-cites (57, 64, 84, 108, 172, 87, 106) | all exact | ✓ |

**Row i.6's negative claim is true.**  `Longitudinal.lerayComplement_eq_self_of_curl_free:280` reads
`{Z : EulerLpTranslation.SmoothL2Field Space} … (m : ℕ) {A : RealVectorSobolev ((m:ℝ)+1)}`, so it
needs a bundled `SmoothL2Field` and order `(m:ℝ)+1`, which cannot be `0` for `m : ℕ`.  The table is
right that order 0 is 108's job.

**Row ii.4's claim is true.**  `isSobolevDatum_lower_iff {s r} (hrs : r ≤ s) {z} {A} :
IsSobolevDatum r z (lowerVectorL s r hrs A) ↔ IsSobolevDatum s z A` — exactly as quoted.

**The table is derivable as written.**  `/tmp/rev111/probe_assembly.lean` re-derives rows
i.1(for `h`), i.2, i.4, i.6+i.7, ii.1–ii.4, iii.1–iii.3, terminating in

```lean
theorem row_iii3 (h108 : H108) (u : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (ht : t ∈ Ioo (0:ℝ) T) :
    SmoothSquareIntegrableJets (fun x : Space => pressureGradient u.pressure t x)
```

with `H108` the verbatim 108 statement as a hypothesis.  `lake env lean /tmp/rev111/probe_assembly.lean`
→ **exit 0, no output.**  Total body ≈ 55 lines.  Every claimed "S"/"≈10 lines" size held; the `M`
in row i.6 is 108's merged work, not the assembly lane's.  So the table's sizes are honest and the
route is real, not aspirational.

Two route details the table gets right and that the assembly lane must not skip: row i.2 genuinely
needs `isSobolevDatum_unique` (the two `MemLp` witnesses are for syntactically different functions —
`fun x => temporalDerivative …` vs the residual minus `∇p` — so `funext` + uniqueness, not `rfl`),
and row ii.2's rewrite must go `← lerayComplement_lowerVectorL` then `hii1`.

**One shortcut the table missed (informational, not a defect):**
`Leray.leray_datum_lower` (`LerayLowering.lean:229`) collapses ii.2+ii.3 — but it needs an
*order-`m`* transverse statement for `lerayComplement m Am`, which is not available, so the table's
`lerayComplement_lowerVectorL` + `isSobolevDatum_unique` route is the correct one.

---

## 4. Honesty of `ATTEMPTS_SL8_PREP.md` — PASS, three failures reproduced verbatim

No compile-level blocker is *claimed* anywhere in ATTEMPTS (the only blocker claimed is
mathematical: lane 108).  The four recorded tactic failures were spot-checked; three reproduce
exactly, the fourth is a file-absence claim already verified in §3.

1. **"`PiLp.proj 2 (fun _ => ℝ) j` stuck … `Fin 3 → Module (?m y) ℝ`"** —
   `/tmp/rev111/probe_attempts.lean`:
   ```
   error: typeclass instance problem is stuck, it is often due to metavariables
     Fin 3 → Module ?m.7 ℝ
   ```
   Reproduced; the `(𝕜 := ℝ)` in the module is necessary.
2. **"`EuclideanSpace.single_apply` is deprecated → emits a warning (breaks the 'silent' check)"** —
   `/tmp/rev111/probe_attempts2.lean`:
   ```
   warning: `EuclideanSpace.single_apply` has been deprecated: Use `PiLp.single_apply` instead
   ```
   Reproduced (and it further fails to elaborate: `failed to synthesize instance RCLike ℕ`).
3. **"`Finset.sum_ite_eq'` missed because the guard is `if j = c`"** —
   `/tmp/rev111/probe_attempts3.lean`, `pressureGradient_apply`'s proof with `sum_ite_eq'`
   substituted for `sum_ite_eq`:
   ```
   error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
     ∑ x, if x = j then ?b x else 0
   in the target expression
     (∑ c, if j = c then (fderiv ℝ (fun y => p (t, y)) y) (EuclideanSpace.single c 1) else 0) =
       (fderiv ℝ (fun y => p (t, y)) y) (EuclideanSpace.single j 1)
   ```
   Reproduced verbatim, guard orientation exactly as recorded.
4. **"`isSobolevDatum_sub` was missing from `ForceClass.lean` (only `isSobolevDatum_add:261`)"** —
   confirmed: `ForceClass.lean` has `isSobolevDatum_add` at 261 and no `_sub`.

ATTEMPTS is accurate.  One line is slightly generous: it says the `MemLp` route to
`SchwartzPairable` made the "direct-from-definition by layer linearity" fallback unnecessary — that
is correct and visible in the one-line proofs.

---

## 5. Findings

| # | severity | finding |
|---|---|---|
| **F-1** | **MEDIUM-LOW** | **`SL8_SPLIT.md`'s blocker summary is stale.**  "The only remaining true blocker is lane 108" / row i.6 `blocker: 108` was true at the lane's base but **108 merged** (PR #110, `origin/erenup/integration`).  Row i.6 is now an in-tree one-liner, `Leray.lerayComplement_zero_orderZeroDatum_eq_self`.  Fix at merge time (three cells + the "Blocker summary" bullet), or let the assembly lane's first commit do it. |
| **F-2** | **MEDIUM-LOW** | **The momentum-residual `SmoothL2` witness is not exported.**  Table row i.1 names `h`'s `SmoothL2`/`MemLp` as an input but 111 only *inlines* it (twice, as `hpart`, in `MomentumSlice.lean:66-71` and `:86-91`).  Every row from i.2 onward needs it, so the assembly lane must re-type those 5 lines.  Ship it as `smoothL2_momentumResidual_slice` (body copied verbatim from either `hpart`). |
| **F-3** | **LOW** | **Duplicate of 106.**  `D01.pressureGradient_apply` is statement-identical to `A01.PressureGauge.pressureGradient_apply:84`, and `partialDeriv_pressureGradient_symm` is `.2`-equivalent to 106's more general `hasSymmetricJacobian_pressureGradient`.  Unavoidable given the base; hand to a SIMP lane (see §3 for which to keep). |
| **F-4** | **LOW** | `SL8_SPLIT.md` cites `DatumToJets.lean:502` for `contDiff_pressureGradient_slice`; actual line **504**.  Every other cite is exact. |
| **F-5** | **LOW / informational** | Exported statements carry `D01.MemForceR`, not the `A02.MemForceR` the `open` line suggests (namespace shadowing).  Verified `rfl`-equal to A02's, and `D01/Pressure.lean` already behaves this way, so nothing breaks — but the two in-tree `MemForceR` copies (`A02/SolutionClass.lean:100`, `D01/ForceClass.lean:158`) are a latent trap worth a `LESSONS.md` line. |
| **F-6** | **LOW / informational** | `partialDeriv_gradient_eq_sndFDeriv` takes both `hg : ContDiff ℝ ∞ (∇p slice)` and `hφ : ContDiff ℝ ∞ (p(t,·))`, but `hg` follows from `hφ` via `contDiff_pressureGradient_slice`.  Redundant binder; callers must supply both.  Harmless, tidy-up material. |
| **F-7** | **LOW** | `MomentumSlice.lean`'s docstrings name `Longitudinal.lerayComplement_eq_self_of_longitudinal` / `…_of_curl_free` as the consumers of the curl-free output.  The `hcurl` *shape* matches `…_of_curl_free`, but that lemma cannot be applied at order 0 (`SmoothL2Field` + order `(m:ℝ)+1`) — the real consumer is 108's `Leray.lerayComplement_zero_orderZeroDatum_eq_self`.  `SL8_SPLIT.md` row i.6 states this correctly; only the module docstring is imprecise. |

No HIGH or MEDIUM-HIGH findings.  Nothing blocks the merge.

---

## 6. What the SL8 assembly lane should do first

Rebase onto `origin/erenup/integration` (picking up 106 and 108), then open a new
`formalization/NSFormalization/Section4/D01/PressureJets.lean` importing `OrderZeroAlgebra`,
`MomentumSlice`, `OrderZeroCurl` (108), `OrderZeroSymbol`, `LerayLowering`, and
`A01/PressureGauge` (106).  The whole thing is ≈55 lines and was already compiled by this review
as `/tmp/rev111/probe_assembly.lean`; the only substitution is replacing the `H108` hypothesis with
the merged lemma.  Order of work:

1. **Export the missing residual witness (F-2), first commit.**  Write, in `MomentumSlice` or the
   new module,
   `theorem smoothL2_momentumResidual_slice (u) (hf) (ht) : A05.SmoothL2 (fun x => f (t,x) - advection u.velocity t x + ν • spatialLaplacian u.velocity t x)`
   with body
   `smoothL2_add (smoothL2_sub (forceSlice_smoothL2_of_memForceR hf (le_of_lt ht.1)) (advection_slice_smoothL2 u ht)) (smoothL2_const_smul (laplacian_slice_smoothL2 u ht) ν)`.
   Everything below refers to `hres := smoothL2_momentumResidual_slice u hf ht` and `hres.memLp`.
2. **Row i.2** — `orderZeroDatum (memLp_temporalDerivative_slice u hf ht) = orderZeroDatum hres.memLp - orderZeroDatum (memLp_pressureGradient_slice u ht)`.
   Bridge: `rw [← orderZeroDatum_sub]`, then
   `isSobolevDatum_unique (isSobolevDatum_orderZeroDatum (memLp_temporalDerivative_slice u hf ht)) (hcongr ▸ isSobolevDatum_orderZeroDatum (hres.memLp.sub (memLp_pressureGradient_slice u ht)))`
   where `hcongr : (residual) - (∇p) = (fun x => temporalDerivative u.velocity t x)` is
   `funext fun x => (temporalDerivative_slice_eq u ht x).symm`.
3. **Row i.4** — one term, no tactics:
   `Leray.lerayComplement_eq_zero_of_transverse 0 _ (orderZeroDatum_transverse_of_divergence_free (memLp_temporalDerivative_slice u hf ht) (contDiff_temporalDerivative_slice u hf ht) (fun x => sum_partialDeriv_temporalDerivative_eq_zero u ht x))`.
4. **Row i.6** — now in-tree, one term:
   `Leray.lerayComplement_zero_orderZeroDatum_eq_self (memLp_pressureGradient_slice u ht) (contDiff_pressureGradient_slice u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩) hcurl`
   with `hcurl := fun i j x => (NSFormalization.Section4.A01.PressureGauge.hasSymmetricJacobian_pressureGradient u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩).2 x i j`
   — **use 106's lemma, not 111's** (`.2 x i j` is `rfl`-accepted as `hcurl`; 106's version is
   strictly more general, see §3).  `fun i j x => partialDeriv_pressureGradient_symm u ht i j x` is
   the drop-in fallback if 106 is unavailable.
5. **Row i.7** — `have := congrArg (Leray.lerayComplement 0) (row_i2 …); rw [map_sub, row_i4 …, row_i6 …] at this; exact (sub_eq_zero.mp this.symm).symm`.
   (`map_sub` here is exactly `lerayComplement_orderZeroDatum_sub`'s content; using `map_sub`
   directly on the `congrArg` is one step shorter than routing through the named lemma, so 111's
   `lerayComplement_orderZeroDatum_add/_sub` end up convenience wrappers rather than load-bearing.)
6. **Rows (ii)+(iii), the finish** — one `refine`:
   `memHInfty_iff_smoothSquareIntegrableJets.mp ⟨contDiff_pressureGradient_slice u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩, fun m => …⟩`;
   inside, `obtain ⟨_, hjets⟩ := memHInfty_iff_smoothSquareIntegrableJets.mpr hres`,
   `obtain ⟨Am, hAm⟩ := hjets m`, `h0m := Nat.cast_nonneg m`,
   witness `Leray.lerayComplement (m:ℝ) Am`, then `(Leray.isSobolevDatum_lower_iff h0m).mp` of:
   `hii1 : lowerVectorL (m:ℝ) 0 h0m Am = orderZeroDatum hres.memLp` by
   `isSobolevDatum_unique (Leray.isSobolevDatum_lower h0m hAm) (isSobolevDatum_orderZeroDatum _)`;
   `hii2` by `rw [← Leray.lerayComplement_lowerVectorL, hii1]`; finish
   `rw [hii2, ← row_i7 …]; exact isSobolevDatum_orderZeroDatum _`.
   Note `lowerVectorL` is `NSFormalization.Section4.D01.lowerVectorL` (defined in
   `D01/HalfOrder.lean:103`), **not** `Leray.lowerVectorL` — the `SL8_SPLIT.md` table writes it
   unqualified and this cost the reviewer one compile.
7. Then register the result as the P2 contract field and cross-check against
   `Pressure.pressureGradient_slice_smoothSquareIntegrableJets:376` (the equivalent finish the table
   lists), and fix F-1/F-4 in `SL8_SPLIT.md`.

---

## Commands run (all from the worktree, after `. scripts/lean-env.sh`)

| command | result |
|---|---|
| `cd verification && LEAN_NUM_THREADS=6 lake build …OrderZeroAlgebra …MomentumSlice` | `Build completed successfully (9921 jobs).` exit 0 |
| `cd verification && lake env lean ../formalization/…/OrderZeroAlgebra.lean` | silent, exit 0 |
| `cd verification && lake env lean ../formalization/…/MomentumSlice.lean` | silent, exit 0 |
| `cd verification && lake env lean ../research/D01/axioms_sl8_prep.lean` | 12 decls, all `[propext, Classical.choice, Quot.sound]`, exit 0 |
| `make check` | contract policy 13/13 OK; 30 work items consistent; exit 0 |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option'` on both modules | docstring text only |
| `lake env lean /tmp/rev111/probe_sig.lean` | 12 signatures printed, exit 0 |
| `lake env lean /tmp/rev111/probe_fit.lean` | exit 0 (094 fit + 108 fit + `MemForceR` `rfl`) |
| `lake env lean /tmp/rev111/probe_assembly.lean` | **exit 0** — full SL8 table i.1→iii.3 assembled |
| `lake env lean /tmp/rev111/probe_vacuity.lean` | exit 0 — `zeroSol`, `memForceR_zero`, instantiation |
| `lake env lean /tmp/rev111/probe_106.lean` | exit 0 — 106 `HasSymmetricJacobian` ↔ 108 `hcurl` |
| `lake env lean /tmp/rev111/probe_attempts{,2,3}.lean` | three recorded failures reproduced verbatim |
| `git fetch origin erenup/integration` (read-only) + `git show`/`git ls-tree`/`git grep` on it | 106 and 108 contents inspected; worktree not rebased |
