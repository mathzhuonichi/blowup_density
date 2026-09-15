# REVIEW — lane 102 (A04 unit G1, SL5 rows 5b / 5f / 5g)

Reviewer: opus, 2026-09-13.  Worktree `.claude/worktrees/102-A04-sl5-columns-norms`, HEAD `6f895a1`.
Light/strict review, Lean run by the reviewer.

## Verdict: **ACCEPT-WITH-NOTES**

All four checks pass.  The three rows are proved as stated (5g is stronger than the brief asked —
an equality, not a `≤`), the axioms are clean, the module compiles warning-free, and the two norm
identifications plug into the SL5 target with **no shape mismatch** (verified by a scratch `calc`).
Every finding below is documentation- or duplication-level; none affects the mathematics.

---

## 1. Commands and results

| # | command (from the worktree) | result |
|---|---|---|
| 1 | `bash scripts/lean-install.sh` | `== OK` (idempotent; ends with `lake test`, all `Tests.*` replayed, "standard logical axioms only") |
| 2 | `cd verification && lake build NSFormalization.Section4.A04.NonlinearColumns` | `Build completed successfully (9896 jobs).` |
| 3 | `cd verification && lake env lean ../formalization/NSFormalization/Section4/A04/NonlinearColumns.lean` | **prints nothing**, exit 0 |
| 4 | `cd verification && lake env lean ../research/A04/axioms_sl5_columns.lean` | 7 declarations, each `[propext, Classical.choice, Quot.sound]` — see below |
| 5 | `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' …/NonlinearColumns.lean` | no match (exit 1) |
| 6 | `make check` | architecture checks OK; `test_contract_policy.py` 13/13 OK; `check_work_queue.py` "30 work items … consistent" |
| 7 | `git diff --stat origin/erenup/integration...HEAD` | 4 files, +295/−3; `verification/` untouched |

Axiom audit (command 4), verbatim declaration list:
`exists_outerColumn_datum`, `exists_outerColumn_datum_succ`, `sqrt_sum_norm_sq_derivDatumStep_eq`,
`sqrt_sum_norm_sq_derivDatumStep_eq_slice`, `columnsSobolevENorm_toReal_sq_eq_sum`,
`outerSobolevENorm_toReal_sq_eq_sum`, `sqrt_sum_norm_sq_columnData_eq` — all exactly
`[propext, Classical.choice, Quot.sound]`.

Reviewer scratches (in `/tmp/rev102/`, **not** committed; the single `sorry` is in the 5h skeleton
and stands for 5a+5c+5d.amb+5i):

* `check.lean` — 4 fidelity checks, all elaborate (only the deliberate 5h `sorry` warning);
* `simp.lean`, `resolve.lean` — the SIMP-lane and name-resolution findings below, exit 0.

---

## 2. Statement fidelity

### (a) Row 5b — is it non-vacuous, and is the cast bridge sound?

**Non-vacuity: yes, verified.**  `MemHmVector (m+1) (u.velocity (t,·))` is obtainable from
`ClassicalSolutionR` in four lines, with no `2 ≤ m` needed (reviewer scratch, elaborates):

```lean
example {ν a f T} (u : A02.ClassicalSolutionR ν a f T) {t} (ht : t ∈ Ico (0:ℝ) T) (m : ℕ) :
    MemHmVector (m + 1) (fun x : Space => u.velocity (t, x)) := by
  refine ⟨(C01.velocity_slice_smoothL2 u ht).memLp, ?_⟩
  obtain ⟨A, hA⟩ := (C01.velocity_slice_memHInfty u ht).2 (m + 1)
  rw [A03.sobolevENorm_eq hA]; exact enorm_ne_top
```

`MemLp` comes from `A05.SmoothL2.memLp` (`A05/SmoothJets.lean:52`); the enorm half from the datum
clause of `A02.MemHInfty` (`SolutionClass.lean:88-90`) through `A03.sobolevENorm_eq`.  Both halves
are already exported by `C01/VelocityJets.lean:65,85` (`velocity_slice_memHInfty` /
`velocity_slice_smoothL2`).  So 5b applies to the real object, and 5g's hypothesis `hC` is
inhabited on the admissible class.

**Cast bridge: sound.**  `isSobolevDatum_castOrder` (`LaplacianAssembly.lean:81`) is
`by subst h; exact hA` — a genuine `subst` on the propositional equality `s = s'`, not a `cast`
across non-defeq types and not an axiom; `castOrder h A := h ▸ A` (`:87`) is the matching transport,
and `cast_mid_order m : ((m+1:ℕ):ℝ) = (m:ℝ)+1` (`:103`) is `by push_cast; ring`.  The witness
`⟨castOrder (cast_mid_order m) A, isSobolevDatum_castOrder (cast_mid_order m) hA⟩` typechecks
because `castOrder h A` and `h ▸ A` are the same term.  No junk, no new axiom (confirmed by the
axiom audit).

The finiteness route is the one the lane claims: `le_columnsSobolevENorm` (`OuterTameProduct.lean:112`)
⇒ `outerProductTame` (`:157`), with the `H²` factor from `sobolevENorm_two_le`
(`VectorTameProduct.lean:228`).  Correct and cheaper than the brief's `tameProductVector` suggestion
(2 vector norms instead of 4 norms, two of them scalar-component); the ATTEMPTS records this as a
deliberate substitution, which is honest.

### (b) Row 5f — is `derivDatumStep` the summand, and does the slice form feed `grad`?

**Yes, syntactically.**  Reviewer `rfl` example (elaborates):

```lean
example (m : ℕ) (j : Fin 3) (A' : RealVectorSobolev ((m:ℝ)+1)) :
    derivDatumStep m j A'
      = ((WithLp.toLp 2 fun i =>
          angularDirectionalDerivativeReal ((m:ℝ)+1) (coordinateVector j) (A' i)) :
         RealVectorSobolev (m:ℝ)) := rfl
```

`derivDatumStep` (`LaplacianAssembly.lean:95`) is literally the body of the summand in
`gradientSobolevENorm_toReal_sq_eq_datum_sum` (`LaplacianDatum.lean:130`), so
`sqrt_sum_norm_sq_derivDatumStep_eq` is exactly that lemma plus `Real.sqrt_sq`, with no restatement
drift.

**Slice corollary right side is literally `gradientSobolevNormAt (m:ℝ) u t`** (the statement says so;
`gradientSobolevNormAt` is `LaplacianDatum.lean:87`).  This is the *same expression* SL3 bounds:
`inner_datum_laplacian_le' : ⟪G, L⟫ ≤ - gradientSobolevNormAt (m:ℝ) u t ^ 2`
(`LaplacianAssembly.lean:354-362`).  So 5h can pass one and the same real `grad` into
`inner_energy_assembly`'s `hlap` and `hnl` — the shapes agree.  The hypothesis shape
(`hsl : A05.SmoothL2 (fun x => u (t,x))` + order-`(m+1)` datum) is copied from `inner_datum_laplacian_le'`,
which is the right precedent, and the `let Z … have hg := rfl` pattern follows 088's heartbeat
warning rather than inlining the defeq.

### (c) Row 5g — finiteness, vacuity, and `⊤.toReal = 0` junk

The lane's claim that `outerProductTame` is **not** needed here is correct and is an improvement:
under `hC : ∀ j, IsSobolevDatum (m:ℝ) (outerColumn z z j) (C j)` one gets
`sobolevENorm (m:ℝ) (outerColumn z z j) = ‖C j‖ₑ ≠ ⊤` for every `j`, hence
`∑ⱼ (…)^2 ≠ ⊤`, hence `outerSobolevENorm (m:ℝ) z z ≠ ⊤`.  **Both sides of the conclusion are
therefore genuinely finite reals and no `⊤.toReal = 0` collapse is possible.**

What happens when a column datum does *not* exist: `hC` is simply unsatisfiable, the lemma says
nothing about that `z`, and no false statement is asserted.  (In that degenerate case
`outerSobolevENorm = ⊤` and `.toReal = 0`, so an *unconditional* version of this lemma would indeed
be junk — the lane correctly keeps `hC` as a hypothesis rather than assuming finiteness separately.)
Non-vacuity is supplied in the same module by `exists_outerColumn_datum`, itself non-vacuous by (a).

The auxiliary `columnsSobolevENorm_toReal_sq_eq_sum` likewise carries `hfin`, so the same argument
applies one level down.

### (d) Do 5f/5g give exactly the two SL5 factors after 5e?

**Yes.**  Reviewer 5h skeleton (elaborates; only the first step is `sorry`):

```lean
calc - (inner ℝ G N : ℝ)
    = ∑ j : Fin 3, (inner ℝ (derivDatumStep m j A') (C j) : ℝ) := by sorry   -- 5a+5c+5d.amb+5i
  _ ≤ Real.sqrt (∑ j : Fin 3, ‖derivDatumStep m j A'‖ ^ 2)
        * Real.sqrt (∑ j : Fin 3, ‖C j‖ ^ 2) := sum_inner_le_sqrt_mul_sqrt _ _ _   -- 5e (095)
  _ = gradientSobolevNormAt (m:ℝ) u t
        * (outerSobolevENorm (m:ℝ) (fun x => u (t,x)) (fun x => u (t,x))).toReal := by
      rw [sqrt_sum_norm_sq_derivDatumStep_eq_slice m hsl hA',    -- 5f (102)
        sqrt_sum_norm_sq_columnData_eq m hC]                      -- 5g (102)
```

Three things this settles:

1. 5e's `E` is instantiated at `RealVectorSobolev (m:ℝ)` for **both** slots — `derivDatumStep m j A'`
   and `C j` are the same type, no coercion needed.
2. The final `rw` closes the goal, i.e. 5f and 5g produce *literally* the two factors of the SL5
   target as written in `SL5_SPLIT.md:6-8`.
3. The product `gradientSobolevNormAt · (outerSobolevENorm …).toReal` is exactly what
   `A04.outerNormAt_le` (`HighEnergy.lean:187`) then converts into eq:Rhigh's
   `C·‖u‖_{H²}·‖u‖_{H^m}·‖∇u‖_{H^m}` (`appendix-a-local-theory.tex:132`, via eq:tame `:17`), so the
   chain down to `inner_energy_Rhigh` is shape-complete.

Remaining gaps are exactly the `sorry` step: **5a**, **5c**, and the 5i/order reconciliations inside
5h.  See §5.

---

## 3. Consistency

* **Imports canonical.**  Only `NSFormalization.Section4.A04.LaplacianAssembly` and
  `NSFormalization.Section4.A03.OuterTameProduct`.  No `Contracts.*`, no `Formal.*`, no vendor import.
* **No restated definitions.**  The module declares **zero** `def`s — seven theorems only.  All
  objects (`outerColumn`, `columnsSobolevENorm`, `outerSobolevENorm`, `derivDatumStep`, `castOrder`,
  `gradientSobolevNormAt`) come from the canonical modules.
* **`columnsSobolevENorm_toReal_sq_eq_sum` vs `LaplacianDatum.lean:96`.**  It *is* the strict
  generalization, not a duplicate statement: the reviewer checked that 096 is a direct instance —

  ```lean
  example {s z} (hfin : ∀ j : Fin 3, sobolevENorm s (partialDeriv j z) ≠ ⊤) :
      (gradientSobolevENorm s z).toReal ^ 2 = ∑ j : Fin 3, (sobolevENorm s (partialDeriv j z)).toReal ^ 2 :=
    columnsSobolevENorm_toReal_sq_eq_sum hfin          -- elaborates
  ```

  However the **proof body is copied verbatim** (same `ENNReal.toReal_rpow` / `Real.rpow_natCast` /
  `Real.rpow_mul` / `norm_num` / `ENNReal.toReal_sum` / `ENNReal.toReal_pow` script, ~10 lines), and
  the general lemma sits *downstream* of the special one, so 096 cannot currently be re-derived from
  it.  See finding 2.

---

## 4. Findings

| # | severity | location | finding | fix |
|---|---|---|---|---|
| 1 | **low (doc)** | `NonlinearColumns.lean:57`, docstrings `:175,178`; `ATTEMPTS_SL5_COLUMNS.md` §5g | The `open A03 (… sobolevENorm_eq)` is **shadowed**: inside `namespace NSFormalization.Section4.A04`, the unqualified `sobolevENorm_eq` at `:177,182` resolves to `A04.sobolevENorm_eq` (`Forcing.lean:126`, reachable via `LaplacianDatum → HighEnergy → Continuity → Forcing`), not to the opened `A03.sobolevENorm_eq`.  Verified with `#check @sobolevENorm_eq` under the module's exact `open` block.  The two are statement- and proof-identical (`Forcing.lean:122` says so explicitly), so **no mathematical impact**; the docstring and ATTEMPTS attribution are simply wrong. | Either drop `sobolevENorm_eq` from the `open` list and cite `A04.sobolevENorm_eq`, or qualify the two uses as `A03.sobolevENorm_eq`.  Cosmetic — fine to defer to the SIMP lane. |
| 2 | **low (dup)** | `NonlinearColumns.lean:144-157` vs `LaplacianDatum.lean:96-109` | ~10 lines of identical `ENNReal.toReal` script.  The new lemma is the generalization (proved above), but lives downstream, and it is a statement purely about `A03.columnsSobolevENorm` with no A04 content — a mild layering inversion. | SIMP lane: move `columnsSobolevENorm_toReal_sq_eq_sum` into `A03/OuterTameProduct.lean` right after `le_columnsSobolevENorm`, then replace `gradientSobolevENorm_toReal_sq_eq_sum`'s body with `columnsSobolevENorm_toReal_sq_eq_sum hfin` (one line) and keep `NonlinearColumns` re-exporting or citing it.  Net −20 lines. |
| 3 | **low (dup)** | `NonlinearColumns.lean:87-105` | `exists_outerColumn_datum_succ` re-proves the whole finiteness chain at order `m+1`.  The reviewer verified it is a two-line consequence of the order-`m` version: `obtain ⟨A, hA⟩ := exists_outerColumn_datum (m+1) (by omega) hz j; exact ⟨castOrder (cast_mid_order m) A, isSobolevDatum_castOrder (cast_mid_order m) hA⟩` (elaborates).  Also `1 ≤ m` suffices in place of `2 ≤ m` (also verified). | SIMP lane: collapse the `succ` proof to the two lines; keep `2 ≤ m` if you prefer hypothesis uniformity with the rest of SL5 (the paper's regime is `m ≥ 3` anyway). |
| 4 | **low (doc)** | `NonlinearColumns.lean` module docstring, line 9 | Cites `HighEnergy.lean:101,106`.  Actual: `inner_energy_assembly` `:100`, `inner_energy_Rhigh` `:136`.  Inherited verbatim from `SL5_SPLIT.md:4`, so pre-existing, not introduced here. | Fix both when SL5_SPLIT is next touched. |
| 5 | **low (doc)** | `research/A04/SL5_SPLIT.md:14-21` and rows 5c / 5h / closing line | The "Branch note" still says the lane "branched **before** PR #94", that `LaplacianAssembly.lean` is "**absent from this worktree**" and "do **not** import it here".  That was lane 095's situation; lane 102 correctly *does* import it.  The note is scoped as "this lane" but on `erenup/integration` it now reads as a standing prohibition.  Likewise 5c's inputs still say "5a + 5b" (5b is now DONE, so 5c's only blocker is 5a), 5h's inputs still list 5f/5g, and the closing critical-path line `5i → 5a → 5b/5c → 5f/5g → 5h` is stale. | Rewrite the branch note as a dated history line ("lane 095 predated #94; lanes ≥ 102 import `LaplacianAssembly` normally") and refresh the three cells.  Purely editorial. |
| 6 | **info** | repo-wide | `formalization/NSFormalization.lean` imports no `Section4` module, and `.github/workflows` runs only `make check`, so **`NonlinearColumns` is never compiled by CI** — same as `LaplacianAssembly`, `HighEnergy`, `NonlinearPairing` and the rest of Section4.  Pre-existing systemic gap, **not** a lane defect; noted so it is not mistaken for coverage. | Out of scope; a future MAINT lane could add a Section4 aggregate target. |

**Honesty of ATTEMPTS: confirmed.**

* Three cited declarations opened and read: `gradientSobolevENorm_toReal_sq_eq_datum_sum`
  (`LaplacianDatum.lean:130`) — RHS summand is as claimed; `outerProductTame`
  (`OuterTameProduct.lean:157`) — RHS is `C·‖z‖_{H²}·‖z‖_{H^k}` as claimed, `hk : 2 ≤ k`;
  `exists_sobolevDatum` (`VectorTameProduct.lean:77`) — signature as claimed.  All other cited line
  numbers (`OuterTameProduct.lean:68,75,79,112`; `VectorTameProduct.lean:48,71,228`;
  `LaplacianDatum.lean:87,96,130`; `LaplacianAssembly.lean:81,87,95,103`) check out.
* **Branch claim verified**: `git merge-base HEAD origin/erenup/integration` = `d3e7f0d` ("Record
  lane 102"), and `00076ca` ("Merge pull request #94 … erenup/088-A04-sl3-assembly") is an ancestor
  of `HEAD`; `LaplacianAssembly.lean` exists at `HEAD~1`.  The lane did branch **after** #94.
* The "failed / rejected approaches" section is accurate: rejection 1 (`tameProductVector`) is a
  genuine simplification and is labelled as such, not as a compile failure; rejection 3 is consistent
  with the `rfl` check above.
* `SL5_SPLIT.md` rows 5b / 5f.grad / 5g.outer were updated accurately (declaration names, module,
  routes, and the "delivered as `=`" note all match the code).  The un-updated neighbouring cells are
  finding 5.

---

## 5. The SL5 endgame

What is left, in dependency order.

1. **5a — pointwise divergence form (M, the real work).**  `advection u t x = ∑ⱼ partialDeriv j (outerColumn z z j) x`
   for `z = u(t,·)`, under `DifferentiableAt ℝ z x` and `spatialDivergence u t x = 0`.  Nothing new is
   blocking it: `C01/Trilinear.lean:91-98` already supplies `hadv`/`hbasis`/`hmap`, and the step from
   advection form `∑ⱼ zⱼ ∂ⱼ z` to divergence form is `HasFDerivAt.smul` + the `PiLp.proj` chain rule
   plus the divergence-free cancellation, then `Fin.sum_univ_three`.  Estimate ~80-120 lines, one lane.
   This is the only row with genuine analytic content still open on the non-`5i` side.
2. **5c — the nonlinear datum (S–M), needs 5a + 5b.**  `N = ∑ⱼ derivDatumStep m j (castOrder (cast_mid_order m) Bⱼ)`
   with `Bⱼ` from `exists_outerColumn_datum_succ` (**now available**, this lane).  The recipe is 088's
   `isSobolevDatum_laplacian` with *one* derivative step instead of two: `isSobolevDatum_partialDeriv`
   per column, `isSobolevDatum_add` over the three `j`, `isSobolevDatum_unique` against the given `hN`,
   rewriting the field along 5a.  Each `Wⱼ` must be repackaged as a `SmoothL2Field` (088's
   `Z.directionalField` pattern) — that repackaging, not the datum algebra, is the fiddly part.
   Estimate ~60-90 lines once 5a lands.
3. **5h — the assembly (M), needs 5c + 5i + 5f + 5g.**  §2(d) above shows the **last two steps already
   close**; what remains is the first `calc` step, i.e. (i) substitute 5c, (ii) `inner_sum` to
   distribute, (iii) 5d.amb / `sum_real_inner_angularDirectionalDerivativeReal` for the summed IBP,
   (iv) the three order reconciliations `G = Λ_{m+1→m} A'`, `Cⱼ = Λ_{m+1→m} Bⱼ`
   (`isSobolevDatum_lowerVectorL` + `isSobolevDatum_unique` + `coe_lowerVectorL`) and
   `Dⱼ G = Λ_{m→m-1}(Dⱼ A')` (`directionalDerivative_orderLowering_comm`), all from #94, glued by
   **5i** (`inner_loweringMid_transfer` / `real_inner_lowering_transfer`, lane 095).  Use
   `abs_sum_inner_le_sqrt_mul_sqrt` instead of `sum_inner_le_sqrt_mul_sqrt` so the sign of the IBP
   need not be tracked.  Estimate ~100-150 lines.

Order to run them: **5a → 5c → 5h**.  5a and 5c are separable lanes; 5h should wait for both.  After
5h, `hnl` feeds `inner_energy_Rhigh` through `outerNormAt_le` (`HighEnergy.lean:187`), whose left side
is already exactly 5g's right side — that seam needs no new lemma.

One note for whoever writes 5h: it will almost certainly obtain its order-`m` column data `Cⱼ` by
*lowering* the order-`(m+1)` data `Bⱼ` and identifying them with `isSobolevDatum_unique`, rather than
by calling `exists_outerColumn_datum` (the order-`m` row) directly.  That is fine —
`exists_outerColumn_datum` remains the standalone existence statement and is what makes 5g
non-vacuous — but do not expect both 5b variants to appear in the final proof.
