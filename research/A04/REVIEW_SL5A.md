# Lane 100 review — A04 unit G1, SL5 row 5a (advection in divergence form)

Reviewer: opus (lane-review, light/strict, ran the Lean).
Commit under review: `cf45ba2` `[100-A04] SL5 row 5a …`.
Worktree: `.claude/worktrees/100-A04-sl5a-divergence-form` (read/build only).

## Verdict

**ACCEPT-WITH-NOTES.**  The three declarations compile clean, carry only the
standard three axioms, and prove what row 5a is supposed to prove.  The `rfl`
bridge is a genuine definitional identity (independently re-derived below, per
summand — nothing is hidden in the `Finset.sum`), the main identity has exactly
the function shape row 5c needs (verified by running the `rw … at hN`), and the
hypotheses are minimal and discharged correctly on `Ico 0 T`, `t = 0` included.
All notes are documentation-level; none blocks the merge and none touches the
Lean.

## Findings

### F1 — nit (docs), `AdvectionDivergence.lean:9-10` — `eq:Rhigh` cited to the wrong file

The module header says the estimate is `eq:Rhigh` of
`paper/sections/04-whole-space.tex`.  The label `eq:Rhigh` is actually declared at
`paper/sections/appendix-a-local-theory.tex:132`; `04-whole-space.tex` contains no
`Rhigh` at all (`grep -rn "Rhigh" paper/` finds only the appendix and the two
`paper/originals/` copies).  `research/A04/SL5_SPLIT.md` already cites the appendix
correctly for the neighbouring `‖∇u‖_{H^m}` (`appendix-a-local-theory.tex:134`), so
this is an internal inconsistency, not a disagreement about the mathematics.
Fix: change the docstring pointer to `paper/sections/appendix-a-local-theory.tex:132`.
(The lane inherited this from the task brief, which also said "04-whole-space.tex
eq:Rhigh"; flagging so it does not propagate to the sibling 5b–5h modules.)

Note this does **not** affect fidelity: the paper's eq:Rhigh is obtained by
"pairing the equation with `u` in `H^m`, integrating by parts, and using
eq:Rproduct", and the `‖∇u‖_{H^m}` factor on its right-hand side is exactly what
the integration by parts produces once the advection is in divergence form
`∑_j ∂_j(u_j u)` — i.e. row 5a is the right identity for the right step, and it
puts `u ⊗ u` under the norm so that eq:Rproduct (`appendix-a-local-theory.tex:17`,
`‖u⊗u‖_{H^k} ≤ C_k‖u‖_{H^2}‖u‖_{H^k}` = `outerSobolevENorm`) applies.

### F2 — nit (docs), `research/A04/SL5_SPLIT.md` "Branch note" — now stale

The branch note still says PR #94's `Section4/A04/LaplacianAssembly.lean` is
"**absent from this worktree**" and must be read via `git show`, "do **not** import
it here".  That was true in lane 095's worktree; in lane 100's it is present
(`formalization/NSFormalization/Section4/A04/LaplacianAssembly.lean`, with
`castOrder` :87, `derivDatumStep` :95, `isSobolevDatum_laplacian` :134).  Lane 100
updated row 5a of this table but left the note.  Row 5c will import that module
directly, so the prohibition should go.  The lead is already reconciling this file
against lane 102, so fold the fix into that reconciliation.

### F3 — note (scoping, not a defect) — row 5c is probably `M`, not `S–M`

See the row 5c paragraph below.  The table's size assumes the `SmoothL2Field`
wrapper for each column is comparable to 088's `directionalField` repackaging; it
is not.  No action for lane 100.

### F4 — informational — no contract/Tests registration, so the axiom audit is not CI-enforced

The commit touches no `Contracts/` or `Tests/` file (verified), which is correct
for an intermediate sub-lemma — registration belongs at the G1/A04 level.  The
consequence is that the 3-axiom result lives only in the scratch
`research/A04/axioms_sl5a.lean` and is not re-checked by CI.  Expected and fine;
recording it so the eventual A04 contract registration does not assume this module
is already covered.

### Checks that found nothing

* No `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats` (grep clean).
* No definition is restated: the module declares three `theorem`s and no
  `def`/`abbrev`/`structure` (grep clean).  The only occurrences of `fderiv` are in
  docstrings (`:23`, `:61`, `:63`); `HasFDerivAt` occurs nowhere, so lane 093's
  Leibniz rule (`convection_term`, the `HasFDerivAt.smul` chain) is **not**
  duplicated — it is consumed through `convectionDivergence_eq_advection`.
* Imports are the four canonical modules `A01.ConvectionDivergence`,
  `A03.OuterTameProduct`, `A02.SolutionClass`, `D01.DatumToJets`; all four are used
  (A01 for the bridge, A03 for `partialDeriv`/`outerColumn`, A02 for
  `ClassicalSolutionR`/`SpaceTimeField`/`SpatialField`, D01 for `contDiff_slice`).
  `lake env lean` prints nothing at all, so the linters flag no unused import,
  variable or `open`.
* The `SpaceTimeField` claim is correct: `A02/SolutionClass.lean:67` is
  `abbrev SpaceTimeField := VelocityField`, reducible, so passing
  `u : SpaceTimeField` to lane 093's `VelocityField`-typed lemmas needs no coercion
  (as the compiling proof demonstrates).

## Statement fidelity

### (a) The `rfl` bridge is genuinely definitional

Hand re-derivation.  `partialDeriv j v x` unfolds
(`A03/OuterTameProduct.lean:59`, `:56`, `ProblemStatement.lean:60`) as

```
partialDeriv j v x
  = spatialDerivative (lift v) 0 x (coordinateVector j)        -- partialDeriv
  = fderiv ℝ (fun y : Space => (lift v) (0, y)) x (e j)        -- spatialDerivative
  = fderiv ℝ (fun y : Space => v (0, y).2) x (e j)             -- lift
  = fderiv ℝ v x (e j)                                         -- Prod.snd ∘ Prod.mk (iota), then eta
```

With `v := outerColumn z z j = fun x' => (z x' j) • z x'` (`:68`) and
`z := fun y => u (t, y)`, each summand beta-reduces to
`fderiv ℝ (fun y => (u (t,y) j) • u (t,y)) x (e j)`, which is verbatim the summand
of `convectionDivergence` (`A01/ConvectionDivergence.lean:60-62`, the same spelling
as `research/A01/Spec.lean:103-105`).

**No `Finset.sum` reindexing is hidden.**  I did not take the lane's word for this:
both sides are `∑ j : Fin 3, _` over the same `Finset.univ` with the same binder, so
the only way a permutation could sneak in is via the bodies.  I checked the bodies
directly, outside the module, at `/tmp/rev100_defeq.lean`: (i) the per-summand
equality holds by `rfl` for a *variable* `j`, and (ii) the two `fun j : Fin 3 => _`
bodies are equal by `rfl` as functions of `j` — a strictly stronger statement than
the bridge, which rules out any reindexing being absorbed by the sum.  (iii)
`convectionDivergence u t x = ∑ j, fderiv …` is `rfl`.  All three compile, exit 0.

### (b) The shape row 5c consumes

The main identity is a function equality whose LHS is literally
`(fun x => advection u t x)`, i.e. syntactically the subterm appearing in
`hN : IsSobolevDatum (m:ℝ) (fun x => advection w.velocity t x) N`
(`MomentumDatum.lean:167-179`).  I confirmed the rewrite by running it rather than
by inspection — `/tmp/rev100_scratch.lean`:

```lean
example {u : SpaceTimeField} {t : ℝ} {m : ℕ}
    {N : NSFormalization.Paper3.RealVectorSobolev (m : ℝ)}
    (hdiff : ∀ x, DifferentiableAt ℝ (fun y => u (t, y)) x)
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hN : IsSobolevDatum (m : ℝ) (fun x => advection u t x) N) :
    IsSobolevDatum (m : ℝ)
      (fun x => ∑ j : Fin 3,
        partialDeriv j (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j) x) N := by
  rw [advection_eq_sum_partialDeriv_outerColumn hdiff hdiv] at hN
  exact hN
```

compiles, exit 0.  So `rw … at hN` works directly on the `IsSobolevDatum`
hypothesis; row 5c needs no `funext`/`congr` massaging and no pointwise variant.
Stating row 5a as a function identity rather than a pointwise one was the right
call.

### (c) Hypotheses: minimal, obtainable, not vacuous

`hdiff : ∀ x, DifferentiableAt ℝ (fun y => u (t,y)) x` and
`hdiv : ∀ x, spatialDivergence u t x = 0` are exactly the two hypotheses of lane
093's `convectionDivergence_eq_advection` (`:113`), quantified over `x` because the
conclusion is a function identity.  Both are load-bearing:

* Dropping `hdiv` makes the statement **false** — 093's Leibniz rule
  (`convectionDivergence_eq_advection_add_smul_div`) gives
  `∇·(u⊗u) = (u·∇)u + (∇·u)•u`, so the extra `(∇·u)•u` survives.
* Dropping `hdiff` breaks the Leibniz step: Mathlib's `fderiv` returns junk `0` at a
  point of non-differentiability, so `advection` would collapse to `0` while the
  column derivatives need not, and the two sides decouple.

Neither is vacuous, and nothing about the identity is satisfied for a degenerate
reason: it is an unconditional consequence of the two hypotheses, and the `rfl`
bridge on its own is unconditional.  Obtainability is demonstrated by the corollary,
which discharges both from a real `ClassicalSolutionR`.

**The corollary's `t ∈ Ico 0 T` is correct, including `t = 0`.**  Both sources are
stated on precisely that set: `ClassicalSolutionR.velocity_smooth` is
`ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)` and `ClassicalSolutionR.divergence` is
`∀ t ∈ Ico 0 T, ∀ x, spatialDivergence velocity t x = 0`
(`A02/SolutionClass.lean:120,128`).  So `Ico 0 T` is simultaneously sufficient and
the widest set available — there is no data at `t = T` or `t < 0`, and narrowing to
`Ioo 0 T` would needlessly lose the initial time, which SL5/G1 will want.  The
`t = 0` endpoint is the subtle one and is handled correctly: the slab is one-sided
in time there, and `D01.contDiff_slice` (`DatumToJets.lean:366`) is written for
exactly that case ("including at `t = 0`, where the slab is one-sided in time"),
composing with the affine inclusion `x ↦ (t,x)` whose preimage of the slab is all of
`Space`.  `w.divergence t ht` applies unchanged at `t = 0`.

## Honesty of `ATTEMPTS_SL5A.md`

Checked, and it is accurate.  I opened the three cited declarations:
`convectionDivergence` is at `A01/ConvectionDivergence.lean:60`,
`convectionDivergence_eq_advection` at `:113`, `contDiff_slice` at
`D01/DatumToJets.lean:366` — all three line numbers are exact.  `A03` `:59`/`:68`,
vendor `:63`/`:67` and `A02:67` also check out.

The specific claim to verify was that **step (i) was pure `rfl`, not the anticipated
`HasFDerivAt.smul` chain**.  Confirmed on both halves: the source of
`convectionDivergence_eq_sum_partialDeriv_outerColumn` is literally `:= rfl`
(`AdvectionDivergence.lean:62`), and the module contains no `HasFDerivAt` occurrence
anywhere.  The `HasFDerivAt.smul` chain exists, but in lane 093's private
`convection_term`, where it belongs; lane 100 consumes its conclusion instead of
re-deriving it.  The "Failed approaches: None" entry is unusual but is consistent
with everything I can observe (a `rfl` that closes is a `rfl` that closes), and the
file is candid that this is why the entry is empty rather than padding it.

## Commands and results

All from the lane worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake run
only from `verification/`, one lake process at a time.

| command | result |
|---|---|
| `bash scripts/lean-install.sh` | idempotent replay, final line `== OK` |
| `lake build NSFormalization.Section4.A04.AdvectionDivergence` | final line `Build completed successfully (9884 jobs).` Every warning printed is `Replayed` from an unrelated upstream module (`Source/PacketForceExtension`, `Source/ViscosityPacket`, `Paper3/RealVectorPositiveDensity`, `Paper3/SobolevDirectionalDerivative`); none originates in this file |
| `lake env lean ../formalization/NSFormalization/Section4/A04/AdvectionDivergence.lean` | **printed nothing**, exit 0 |
| `lake env lean ../research/A04/axioms_sl5a.lean` | 3 declarations, each `depends on axioms: [propext, Classical.choice, Quot.sound]`, exit 0 — matches the output captured in the file's comment block verbatim |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' …/AdvectionDivergence.lean` | no match |
| `make check` | `test_contract_policy.py` 13 tests `OK`; `check_work_queue.py` `30 work items: ownership, contract registration and task cards consistent.`; architecture checks pass |
| `lake env lean /tmp/rev100_defeq.lean` (reviewer scratch, 3 independent defeq re-derivations) | exit 0 |
| `lake env lean /tmp/rev100_scratch.lean` (reviewer scratch, row 5c `rw … at hN`) | exit 0 |
| `git show --stat cf45ba2` | 4 files: the module (+104), `ATTEMPTS_SL5A.md` (+53), `SL5_SPLIT.md` (+9/−4), `axioms_sl5a.lean` (+22).  No `Contracts/`, no `Tests/`, no `paper/` |

Reviewer scratch files were written to `/tmp`, outside the repository; the worktree
is unmodified apart from this review file.

## Row 5c: what 5a hands it, and what is still missing

Row 5c must produce `N = ∑_j derivDatumStep m j (castOrder … B_j)` from
`hN : IsSobolevDatum (m:ℝ) (fun x => advection w.velocity t x) N`.  **From 5a it
gets exactly the right first move and nothing is left to adapt**: one
`rw [advection_eq_sum_partialDeriv_outerColumn hdiff hdiv] at hN` (verified above)
turns `hN` into a statement about `fun x => ∑_j partialDeriv j (outerColumn z z j) x`,
and on a `ClassicalSolutionR` the corollary supplies the same rewrite with both
hypotheses already discharged from `velocity_smooth` and `divergence`.  **From 5b**
(lane 102, `exists_outerColumn_datum_succ`) it gets, per column, some
`B_j` with `IsSobolevDatum ((m:ℝ)+1) (outerColumn z z j) B_j`.  **From 088**
(`LaplacianAssembly.lean`, present in this worktree despite the stale branch note)
it gets `castOrder` (`:87`) to reconcile the `((m+1:ℕ):ℝ)` vs `(m:ℝ)+1` order
spellings, `derivDatumStep` (`:95`) for the single derivative step, plus
`isSobolevDatum_add` / `isSobolevDatum_unique` to sum the three `j` and match
against the rewritten `hN`; `isSobolevDatum_laplacian` (`:134`) is the template to
copy with one derivative step instead of two.

The real cost is the `SmoothL2Field` wrapper, and I think the table under-sizes it.
`D01.isSobolevDatum_partialDeriv` (`DerivativeDatum.lean:245`) is stated for
`{Z : SmoothL2Field Space}` and concludes about `partialDeriv j Z.field`, so each
column `W_j = u_j • u` must be bundled as a `SmoothL2Field`
(`vendor/.../Euler/LpSmoothField.lean:31`), whose two fields are
`smooth : ContDiff ℝ ∞ field` and `integrable : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n field) 2 volume`.
Smoothness is cheap (`contDiff_slice` plus `ContDiff.smul` against the projection
`EuclideanSpace.proj j`).  `integrable` is not: it asks for **every** iterated
Fréchet jet of a *product* to be in `L²`, which is a Leibniz-expansion argument
needing an `L^∞` factor — materially more than 088's `Z.directionalField`
repackaging, which inherits both fields from an existing `SmoothL2Field` by an index
shift.  That is why I would call 5c **M** rather than **S–M** (F3), and why the
cleanest split is to have 5b's lane hand 5c the bundled `SmoothL2Field` for each
`W_j` (it is already proving the `H^{m+1}` enorm is finite via
`A03.tameProductVector`, so it is closest to the product estimates), or to factor
out a reusable "product of a smooth `L^∞` scalar component with a `SmoothL2Field` is
a `SmoothL2Field`" helper in A03.  With that wrapper in hand the rest of 5c is the
`isSobolevDatum_laplacian` copy and is genuinely **S**.  Nothing in 5c is gated on
an unowned or unmerged item.
