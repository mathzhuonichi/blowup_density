# Review — lane 115 (SIMP-A04), simplifier + tester pass over the SL3 cluster

Reviewer: opus (`/lane-review`, light & strict).  Commit under review: `d4f5f1d`
(`[115-SIMP-A04] …`), one commit on merge-base `b7e2b7e`.
Worktree `.claude/worktrees/115-SIMP-A04`, branch `erenup/115-SIMP-A04`.  Read/build only;
probes in `/tmp/rev115/`, error text pasted below (per `LESSONS.md` 2026-09-14).

> Note on diffing: `origin/erenup/integration` has moved on since the lane branched
> (`94bec50`, lanes 110/111/114 merged), so `git diff origin/erenup/integration` shows spurious
> deletions.  The lane's real diff is `git diff b7e2b7e d4f5f1d` — 6 files, +316/−7.

## Verdict

**ACCEPT-WITH-NOTES.**

The engineering claim is exactly true and fully reproduced: the only source change is 11 dead
`open`/`open scoped` tokens (2 whole lines) across the four SL3 modules, every statement and
proof body is byte-identical, the build closure is unchanged (9897 jobs pre- and post-edit,
measured on both sides), all four modules elaborate silently, the 62 conformance declarations
carry only the three standard axioms, and `make check` / `make test` pass.

The notes are about the **tester half**, not the simplifier half: four of the seven negative
checks (N1–N4) fail with `Unknown identifier`, which is the "a name is unbound" failure mode,
not evidence that the hypothesis is load-bearing; and four of the five non-vacuity witnesses are
trivial objects (zero field, zero `L²` element, `s = r = t = 0`).  I wrote real negative checks
for the two exports named in the brief and for the flagship datum identity — **all the
hypotheses in question are genuinely load-bearing**, so no mathematics is wrong; the lane's
*evidence* for that was weak, not its conclusion.  Plus three small record inaccuracies, and one
finding of the lane's own MAINT list that is real and **understated** (Finding 6).

---

## Finding 1 — [Pass] Diff discipline: only `open` tokens, exactly 11 across 2 whole lines

```
$ git diff b7e2b7e d4f5f1d --stat
 .../Section4/A04/LaplacianAssembly.lean            |   3 +-
 .../Section4/A04/LaplacianDatum.lean               |   5 +-
 .../Section4/A04/LaplacianPairing.lean             |   2 +-
 .../NSFormalization/Section4/A04/RealPairing.lean  |   2 +-
 research/A04/ATTEMPTS_SIMP.md                      | 183 +++++++++++++++++++++
 research/A04/negative_simp_sl3.lean                | 128 ++++++++++++++
 6 files changed, 316 insertions(+), 7 deletions(-)
```

Every `+`/`-` line under `formalization/` is an `open` or `open scoped` line.  Token tally
matches the claim: `LaplacianAssembly` −`Set` + whole `open scoped ENNReal InnerProductSpace
ComplexConjugate` line (4 tokens, 1 line); `LaplacianDatum` −`Set` −`MeasureTheory`, whole
`open scoped ENNReal` line, −`columnsSobolevENorm` from the A03 open-list (4 tokens, 1 line);
`LaplacianPairing` −`ComplexConjugate` −`ENNReal` (2); `RealPairing` −`ENNReal` (1).
**Total 11 tokens, 2 whole lines.**  Line counts verified against the merge-base:
138/199/225/370 = 932 → 137/199/225/369 = 930, as tabled in `ATTEMPTS_SIMP.md`.

## Finding 2 — [Pass] Compiles, closure unchanged, axioms standard, gates green

All from `WT/verification` after `. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, one `lake`
at a time.

| command | tail |
|---|---|
| `lake build …A04.{LaplacianDatum,LaplacianPairing,RealPairing,LaplacianAssembly}` | `Build completed successfully (9895 jobs).` |
| `lake build …A04.{NonlinearColumns,NonlinearPairing,NonlinearBound,NonlinearDatum}` | `Build completed successfully (9903 jobs).` |
| `lake build` the 6-target set of `ATTEMPTS_SIMP.md` (**post-edit**, worktree) | `Build completed successfully (9897 jobs).` |
| the same 6-target set **pre-edit** (run in the integration root, whose four A04 files are byte-identical to `b7e2b7e` — `git diff b7e2b7e HEAD -- …/A04/` is empty) | `Build completed successfully (9897 jobs).` |
| `lake env lean ../formalization/…/A04/{LaplacianDatum,LaplacianPairing,RealPairing,LaplacianAssembly}.lean` | each 0 bytes of output, exit 0 |
| `lake env lean ../research/A04/axioms_sl3.lean` | 21 decls, each `[propext, Classical.choice, Quot.sound]` |
| `lake env lean ../research/A04/axioms_sl3_pairing.lean` | 10 decls, all standard |
| `lake env lean ../research/A04/axioms_sl3_real.lean` | 11 decls, all standard |
| `lake env lean ../research/A04/axioms_sl3_assembly.lean` | 20 decls, all standard |
| `make check` (repo root) | `Ran 13 tests … OK`; `30 work items: ownership, contract registration and task cards consistent.` |
| `make test` (repo root) | exit 0; 19 unique `Contract BlowupDensity.Tests.*: checked; standard logical axioms only`, 0 `error:` lines |

The pre/post job counts were measured independently on both sides (9897 = 9897), so the
"closure unchanged" claim is confirmed rather than taken on trust.  62 = 21+10+11+20
conformance declarations, as claimed.

## Finding 3 — [Medium] N1–N4 are not evidence of load-bearingness (`Unknown identifier`)

`lake env lean ../research/A04/negative_simp_sl3.lean` reproduces exactly as documented:
7 errors at the `N?` lines, none at the `V?` lines.  But the first four read:

```
../research/A04/negative_simp_sl3.lean:76:48: error(lean.unknownIdentifier): Unknown identifier `hA`
../research/A04/negative_simp_sl3.lean:85:33: error(lean.unknownIdentifier): Unknown identifier `hA`
../research/A04/negative_simp_sl3.lean:98:44: error(lean.unknownIdentifier): Unknown identifier `hL`
../research/A04/negative_simp_sl3.lean:104:29: error(lean.unknownIdentifier): Unknown identifier `hA`
```

Each N-block deletes a binder from the `example`'s telescope but leaves the proof term
`… m hG hA' hA` citing it.  The resulting error says only *"you cannot name a hypothesis you did
not assume"* — it would be produced identically by a theorem whose hypothesis is pure decoration.
This is the exact failure mode the reviewer brief calls out, and it is weaker than the standard
`LESSONS.md` bar (the `autoImplicit false` guard is applied correctly, but it is guarding a check
that carries no information).  The `ATTEMPTS_SIMP.md` conclusion sentence — "Every hypothesis /
conclusion part is load-bearing" — is therefore **not supported by N1–N4**.

The conclusion is nonetheless **true**.  I proved it by collapse
(`/tmp/rev115/p2_collapse.lean`, `/tmp/rev115/p5_n1_collapse.lean`): state the weakened claim as
a closed `Prop`, then *prove* that it entails something manifestly false.

* `WeakenedNoHL` = `inner_datum_laplacian_le'` with `hL : IsSobolevDatum m (Δu) L` dropped and
  `L` universally quantified.  Two proved consequences (both
  `[propext, Classical.choice, Quot.sound]`, no `sorry`):

  ```lean
  theorem datum_zero_of_weakenedNoHL (H : WeakenedNoHL) (Z : SmoothL2Field Space) (m : ℕ) :
      smoothAngularDatum (m + 2) (m : ℝ) (by push_cast; linarith) Z = 0
  theorem physical_pairing_zero_of_weakenedNoHL (H : WeakenedNoHL) (Z : SmoothL2Field Space)
      (m : ℕ) (i : Fin 3) (ψ : SchwartzMap Space ℂ) :
      ∫ x : Space, ψ x * ((Z.field x i : ℝ) : ℂ) = 0
  ```

  (take `L := G`, so `‖G‖² ≤ -‖∇u‖² ≤ 0`.)  I.e. without `hL` the statement asserts that *every*
  smooth `L²` field vanishes distributionally — false for any Gaussian.  **`hL` is load-bearing.**

* Control (`/tmp/rev115/p3_control.lean`): the same two conclusions **without** `H` are not
  provable, so the collapse proofs really use the hypothesis:

  ```
  /tmp/rev115/p3_control.lean:13:2: error: `simp` made no progress
  /tmp/rev115/p3_control.lean:19:2: warning: aesop: failed to prove the goal after exhaustive search.
  /tmp/rev115/p3_control.lean:18:46: error: unsolved goals
  ⊢ (angularDirectionalDerivative s a) ⟨val, property⟩ = 0
  ```

* I also tried the brief's `exact?` route on `WeakenedNoHL` directly
  (`/tmp/rev115/p1_assembly_nohL.lean`); it is inconclusive here, not a clean negative:

  ```
  /tmp/rev115/p1_assembly_nohL.lean:25:26: error: (deterministic) timeout at `whnf`,
  maximum number of heartbeats (1000000) has been reached
  ```

  So collapse, not `exact?`, is the right technique for this cluster — worth a `LESSONS.md` line.

* The analogous collapse for **N1** (`gradientSobolevENorm_toReal_sq_eq_datum_sum` without `hA`,
  `A := 0` ⇒ `‖∇Z‖_{H^m} = 0` for every `Z`) is mathematically immediate but did not close in
  Lean: the datum-sum RHS is elaborated at `RealSobolevHilbert (↑m + 1 - 1)`, not `↑m`, so
  `WithLp.toLp_zero` will not fire —

  ```
  Application type mismatch: The argument 0 has type
    Fin 3 → ↥(NSFormalization.Source.RealSobolev.RealSobolevHilbert (↑m + 1 - 1))
  but is expected to have type
    Fin 3 → ↥(NSFormalization.Source.RealSobolev.RealSobolevHilbert ↑m)
  ```

  Not a defect of the lane (the order cast is `add_sub_cancel_right`, not `rfl`), recorded so the
  next tester lane does not re-discover it.

## Finding 4 — [Low] N5–N7 test the exported *shape*, not the truth of the weakening

N5–N7 weaken the conclusion and still cite the real theorem, so they fail with a type mismatch:

```
../research/A04/negative_simp_sl3.lean:121:2: error: Type mismatch
  real_inner_angularDirectionalDerivative s a f g
has type
  ⟪f, (angularDirectionalDerivative s a) g⟫_ℝ = -⟪(angularDirectionalDerivative s a) f, g⟫_ℝ
but is expected to have type
  ⟪f, (angularDirectionalDerivative s a) g⟫_ℝ = ⟪(angularDirectionalDerivative s a) f, g⟫_ℝ
```

That is a genuine *tester* signal (it pins the exported statement against silent drift), but it
does not show the weakened statement is false — it only shows this proof term does not prove it.
Closed by collapse (`/tmp/rev115/p2_collapse.lean`, standard axioms):

```lean
theorem deriv_eq_zero_of_weakenedPairing (H : WeakenedPairing) (s : ℝ) (a : Space)
    (f : Lp ℂ 2 (volume : Measure Space)) : angularDirectionalDerivative s a f = 0
theorem distributional_deriv_zero_of_weakenedPairing (H : WeakenedPairing) (s : ℝ) (a : Space)
    (h : Lp ℂ 2 (volume : Measure Space)) : ∂_{a} (angularRealization s h) = 0
```

Dropping the minus makes `D_a` the zero operator at every order and direction, hence (via
`angularRealization_directionalDerivative`) makes every distributional directional derivative in
the range of `angularRealization s` vanish.  **The sign is load-bearing.**  The same argument
applies verbatim to N7 (`inner_angularDirectionalDerivative_right`, the ℂ version that N6's
proof is the real part of).

## Finding 5 — [Low-Medium] Non-vacuity: V1 is good, V0/V2/V3/V4 are trivial objects

V1 is the strong one — it quantifies over an **arbitrary** `Z : SmoothL2Field Space` and any `m`,
and exhibits the three datum hypotheses simultaneously at orders `m, m+1, m+2`.  Good.

V0, V2 and V4 are witnessed by the **zero** field / zero spacetime field / `0 : Lp ℂ 2 volume`,
and V3 by `s = r = t = 0` (all three order inequalities are `le_refl`).  These show the classes
are non-empty but do not exercise the theorems on anything where the identities say more than
`0 = 0`.  I strengthened them (`/tmp/rev115/p4_nonvacuity.lean`, elaborates silently,
`unitBall_ne_zero` on standard axioms):

```lean
noncomputable def unitBall : Lp ℂ 2 (volume : Measure Space) :=
  indicatorConstLp 2 (measurableSet_ball (x := (0 : Space)) (ε := 1))
    (measure_ball_lt_top (x := (0 : Space)) (r := 1)).ne (1 : ℂ)
theorem unitBall_ne_zero : unitBall ≠ 0        -- via norm_indicatorConstLp, measure_ball_pos
```

and then ran both pairing exports on it at **strict, pairwise-distinct** orders
(`s = 1, r = 0, t = -1`) and a **nonzero** direction (`coordinateVector 0`):
`real_inner_lowering_pairing 1 0 (-1) … unitBall` and
`real_inner_angularDirectionalDerivative 1 (coordinateVector 0) unitBall unitBall` both
type-check.  A future tester lane should use this shape rather than `0`.

## Finding 6 — [Medium] The `namespace Paper3`-inside-A04 finding is real, and understated

Verified: `LaplacianPairing.lean` is `namespace NSFormalization.Paper3` at `:46`–`:199` and
`RealPairing.lean` at `:56`–`:225`, exactly as the MAINT table says.  Three things the lane did
not report, all of which make the case for the MAINT lane stronger:

1. **There is already a back-edge from D01 into A04.**  `Section4/D01/LerayLowering.lean`
   (lane 085, commit `3c0c132`) has
   `import NSFormalization.Section4.A04.LaplacianPairing` and
   `import NSFormalization.Section4.A04.RealPairing`, and consumes
   `angularOrderLowering_eq_dilation_mid`, `angularOrderLoweringMid_coeFn`,
   `lowering_mid_symbol_eq` and `angularOrderLowering_self` (`LerayLowering.lean:105–135`).
   D01 is the *root* of the critical chain (D01 → A01 → A02 → A04), so this is a genuine
   inverted module edge, not a cosmetic namespace mismatch.
2. **Neither file actually depends on A04.**  `grep -n 'Section4.A04' LaplacianPairing.lean
   RealPairing.lean` returns only the `import` lines and two docstring mentions — no
   `Section4.A04` declaration is used.  `LaplacianPairing`'s sole import
   (`A04.LaplacianDatum`) is pure transport of the Paper3/Source closure.  So the MAINT move is
   clean: re-point the two imports at the real `Paper3/`/`Source/` modules and the bodies relocate
   with no mathematical change.
3. **No name collisions.**  All 21 `NSFormalization.Paper3` declarations introduced in these two
   A04 files were checked against every other `def`/`theorem`/`lemma`/`abbrev` in
   `formalization/NSFormalization`: zero duplicates.  So the 2026-09-14 `LESSONS.md` ambiguity
   hazard (109's `alias` + double `open`) does **not** apply here; the move is low-risk.
   Nothing under `Paper3/` or `Source/` imports `Section4.*`, so the target layer stays acyclic.

**Recommended MAINT scope:** move the `LaplacianPairing.lean` and `RealPairing.lean` bodies to
`Paper3/` modules next to `AngularFourierDilation` / `SobolevDirectionalDerivative`, re-point
`D01/LerayLowering.lean`, `A04/LaplacianAssembly.lean`, `A04/NonlinearPairing.lean` at the new
homes, and re-run `axioms_sl3_pairing.lean` / `axioms_sl3_real.lean` (which cite these names
unqualified — they will keep working, the namespace is unchanged).  The rest of the lane's MAINT
table (`castOrder*`, `isSobolevDatum_lowerVectorL`, `angularMid_comm`, …) checked out line by
line; see Finding 7.

## Finding 7 — [Low] Three record inaccuracies in `ATTEMPTS_SIMP.md`

1. **Misattribution.**  "Findings 1–2 of `REVIEW_SL3.md` … were **already applied by a later
   lane**" is wrong.  `REVIEW_SL3.md` reviewed lane 066's *pre-merge* commit `e779166`; the
   merged 066 commit `8e4450e` already has no `set_option` in `LaplacianDatum.lean` and already
   derives `hfin` internally.  So the fixes were applied **in lane 066 itself, in response to the
   review, before merge** — no later lane was involved.
   `git log -- …/A04/LaplacianDatum.lean` lists only `8e4450e` (066), `38585d4` (109-MAINT) and
   `d4f5f1d` (115); and `git show 38585d4 -- …/LaplacianDatum.lean` shows 109 changed something
   else entirely (it re-pointed `gradientSobolevENorm_toReal_sq_eq_sum` at the promoted
   `A03.columnsSobolevENorm_toReal_sq_eq_sum`).  Substance is fine — the fixes *are* in the
   tree — only the attribution is wrong.
2. **Contract count.**  "all 17 registered `Tests.*` contracts" — there are **19**
   (`make test` emits 19 unique `Contract BlowupDensity.Tests.*: checked` lines;
   `verification/contracts.json` has 19 entries at this merge-base).
3. **Two off-by-one line citations:** `A03.columnsSobolevENorm_toReal_sq_eq_sum` is at
   `LaplacianDatum.lean:101` (not `:102`); the internal `have hfin` is at `:128` (not `:127`).
   Every other `file:line` in the MAINT table and the "removable-but-kept imports" list was
   spot-checked and is correct (`RealPairing:66,77`; `LaplacianAssembly:80,86,184,201,218,226,232`;
   `DerivativeDatum:134,141`; `A05/SmoothJets:44`; `LaplacianAssembly:216` really does carry the
   `D01.isSobolevDatum_lower` (lane 085, `D01/LerayLowering.lean:202`) pointer).

## Finding 8 — [Low, process] `negative_simp_sl3.lean` mixes must-fail and must-pass blocks

The file is deliberately non-compiling (7 expected errors), so the 5 non-vacuity examples in it
can never be used as a green regression check — a later lane that breaks V1 would see "7 errors"
and move on.  Suggest a MAINT split: non-vacuity examples into a file that must elaborate
silently, negative checks into `research/A04/probes/` (the location `LESSONS.md` 2026-09-14
prescribes for probes worth keeping).  No action needed in this lane.

---

## Commands run (reviewer)

All from `.claude/worktrees/115-SIMP-A04`, `. scripts/lean-env.sh` first, `lake` only from
`verification/`, `LEAN_NUM_THREADS=6`, one `lake` at a time.

```
git diff b7e2b7e d4f5f1d --stat ; git diff b7e2b7e d4f5f1d -- formalization/
git log --oneline -- formalization/NSFormalization/Section4/A04/LaplacianDatum.lean
git show 8e4450e:…/LaplacianDatum.lean | grep -n set_option          # → (nothing)
cd verification
lake build …A04.{LaplacianDatum,LaplacianPairing,RealPairing,LaplacianAssembly}      # 9895 jobs
lake build …A04.{NonlinearColumns,NonlinearPairing,NonlinearBound,NonlinearDatum}    # 9903 jobs
lake build <6-target set>                                    # 9897 jobs (worktree, post-edit)
( in the integration root, same 6 targets )                  # 9897 jobs (pre-edit baseline)
lake env lean ../formalization/…/A04/{4 modules}.lean        # silent, exit 0
lake env lean ../research/A04/axioms_sl3{,_pairing,_real,_assembly}.lean   # 21/10/11/20, standard
lake env lean ../research/A04/negative_simp_sl3.lean         # exit 1, 7 errors at N?, none at V?
lake env lean /tmp/rev115/p1_assembly_nohL.lean              # exact? → whnf timeout (inconclusive)
lake env lean /tmp/rev115/p2_collapse.lean                   # 4 collapse theorems, standard axioms
lake env lean /tmp/rev115/p3_control.lean                    # controls fail, as required
lake env lean /tmp/rev115/p4_nonvacuity.lean                 # nonzero witness + strict orders, silent
lake env lean /tmp/rev115/p5_n1_collapse.lean                # order-cast wrinkle, see Finding 3
cd .. ; make check ; make test
```

`#print axioms` on the reviewer's collapse theorems:

```
'datum_zero_of_weakenedNoHL' depends on axioms: [propext, Classical.choice, Quot.sound]
'physical_pairing_zero_of_weakenedNoHL' depends on axioms: [propext, Classical.choice, Quot.sound]
'deriv_eq_zero_of_weakenedPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'distributional_deriv_zero_of_weakenedPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'unitBall_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Merge recommendation

Merge as is.  Findings 3/4/5 are about evidence quality, and the reviewer probes above settle
the underlying questions in the lane's favour, so nothing needs to be re-proved.  Before merge
the lead may want the three one-line corrections of Finding 7 applied to `ATTEMPTS_SIMP.md`
(attribution, 17 → 19, two line numbers); Findings 6 and 8 are input to the MAINT lane, not to
this one.
