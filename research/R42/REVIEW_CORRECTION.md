# Review — lane 075, task R42 item 1e-i (correction datum path + additivity assembly)

Reviewer: independent opus reviewer, read/build only.
Under review: commit `1e88356` (3 files, +302, no deletions):
`formalization/NSFormalization/Section4/R42/CorrectionPath.lean`
(`exists_datumPath_of_localized` :60–170, `sobolev_add_of_localized` :172–200),
`research/R42/ATTEMPTS_CORRECTION.md`, `research/R42/axioms_correction.lean`.

## Verdict

**ACCEPT-WITH-NOTES.**

Both lemmas are true, stated at exactly the shape `ClassicalSolutionR.sobolev`
demands, and honestly reported.  The construction is the one `LIFESPAN_SPLIT.md`
item 1e-i sketched, improved in two places: the hard cutoff `1_{t ≥ 0}` replaces
the "compact support in `t > 0`" requirement (`angularPath` only needs
`ContDiff` + `HasCompactSupport`, not positivity of time), and the datum is read
off `I03.angularPath_pairing` directly instead of routing through
`isSobolevDatum_unique`.  All four recorded frictions reproduce character for
character.  Zero warnings from the new file, standard three axioms, `make check`
green.

Every hypothesis of `exists_datumPath_of_localized` is discharged by
`InsertionFamilyAPI` with no extra assumption — including `t₁ := T − 2ε² > 0`,
which I initially expected to be a missing side condition (see finding 1).

The notes below are consumability and bookkeeping items for the assembly lane,
not defects in this lane's Lean.  Nothing needs to change in the reviewed code.

## Findings

### 1. (INFO, not a defect) `t₁ := T − 2ε² > 0` **is** guaranteed by the API

The obvious worry about `exists_datumPath_of_localized` is `ht₁ : 0 < t₁`:
`InsertionFamilyAPI.history` (`Contracts/V1/InsertionFamily.lean:224`) gives
`u_ε = v` only for `0 ≤ t ≤ T − 2ε²`, and `InsertionFamilyAPI` itself constrains
its `ε₀` only by `eps_pos` and `eps_le_scaling` (`:160, :164`).  The bound comes
one level up:

* `ScalingAPI.eps_time` (`Contracts/V1/Scaling.lean:209`):
  `∀ ε ∈ Ioc 0 scaling.ε₀, 2 * ε ^ 2 < min correction.T correction.δ`
  (and identically `CorrectionAPI.eps_time`, `Correction.lean:310`).

With `eps_le_scaling : ε₀ ≤ scaling.ε₀`, every `ε ∈ Ioc 0 A.ε₀` lies in
`Ioc 0 A.scaling.ε₀`, so `2ε² < min T δ ≤ T` and `T − 2ε² > 0`.  **The consumer
needs no additional hypothesis.**  Worth one line in the assembly lane's proof
comment, since the route is two records up from where `history` is stated.

### 2. (INFO) Hypothesis-by-hypothesis match against `InsertionFamilyAPI`

For `d := fun z => A.velocity ε z − A.scaling.correction.v z`
(= `InsertionFamilyAPI.velocityDifference ε`, `:411`, definitionally):

| lemma hypothesis | API source | glue |
|---|---|---|
| `ContDiffOn ℝ ∞ d (Ico 0 T ×ˢ univ)` | `velocity_smooth` (`:196`) for `u_ε`, and `reference.velocity_smooth` on `Ico 0 (T+δ) ×ˢ univ` via `reference_velocity` (`:150`) for `v` | `ContDiffOn.mono` (`δ > 0`) then `ContDiffOn.sub` — the brief's expected `sub`, confirmed |
| `∀ t ∈ Ico 0 T, tsupport (fun x => d (t,x)) ⊆ ball x₀ r` | `velocityDifference_support` (`:231`) | none (token-identical) |
| `∀ t, 0 ≤ t → t ≤ t₁ → ∀ x, d (t,x) = 0` | `history` (`:224`) | `sub_eq_zero_of_eq` |
| `0 < t₁`, `t₁ = T − 2ε²` | finding 1 | `linarith` off `eps_time` |
| `S < T` | supplied by the caller | see finding 3 |

No hypothesis is stronger than what the API provides, and none is so weak that a
wrong `d` could sneak through: `hsupp` + `hhist` + `hd` are all used (the first
two for `HasCompactSupport F`, `hhist` also for smoothness across `t = 0`).

### 3. (INFO) `S < T` is the right guard; horizon exactly `T` is out of reach, and does not need to be

`LIFESPAN_SPLIT.md` item **1** (`sol_on_shorter`) asks for a
`ClassicalSolutionR ν a (force ε) S` for every `0 < S < family.T`, and
`maximalLifespanR` is a supremum over such `S`, so `S < T` is exactly the shape
needed; `S ≤ T` would be wrong to even attempt.  The strictness is also inherent
to the construction: the cutoff window is `[S, (S+T)/2]`, and at `S = T` one
would need `d` smooth up to and including `t = T`, which the API does not give
(`velocity_smooth` stops at `Ico 0 T`).  Flagging it only so the assembly lane
does not go looking for a horizon-`T` version.

Degeneracy: for `S ≤ 0` the conclusion is vacuous (`Ico 0 S = ∅`), and for
`T ≤ 0` the hypotheses `hd`/`hsupp` are vacuous too — harmless, since
`sol_on_shorter` supplies `0 < S` and `CorrectionAPI.time_pos` gives `0 < T`.
For `S > 0` the conclusion has real content: `IsSobolevDatum` pins the pairing of
`G t` against every Schwartz test, and `D01.isSobolevDatum_unique`
(`ForceClass.lean:286`) makes `G t` unique, so no wrong `G` satisfies it.

### 4. (LOW) The assembly lane must still rewrite `v + d` into `u_ε` by hand

`sobolev_add_of_localized` concludes about
`fun x => v (t,x) + d (t,x)`, whereas `ClassicalSolutionR.sobolev` for the
inserted solution needs `fun x => u_ε (t,x)`.  With `d := u_ε − v` these are
*propositionally* equal, not defeq (`add_sub_cancel`), and with the
`velocity_formula` route (`d := w_ε + U_ε`) they differ by `add_assoc`.  Either
way a `funext`/`abel` + `▸` step is needed and neither lemma provides it.  I
verified the step is two lines (scratch, compiles):

```lean
have : (fun x : Space => v (t, x) + (u (t, x) - v (t, x))) = fun x => u (t, x) := by
  funext x; abel
exact this ▸ h
```

Not worth a respin, but if a follow-up lane touches this file, restating lemma 2
with a hypothesis `hu : ∀ t x, u (t,x) = v (t,x) + d (t,x)` and concluding about
`u` would make it consumable with no glue at all.

### 5. (LOW) `hvc`/`hdc` are obtainable from `velocity_smooth`, but not as a one-liner

The brief asks whether the two slice-continuity hypotheses come from the API's
`velocity_smooth`.  They do, including at `t = 0`, but the step is a
`ContinuousOn.comp` through the slice embedding rather than a `.continuous`
projection (`ContDiffOn` holds on `Ico 0 T ×ˢ univ`, which is not a neighbourhood
of `(0, x)`).  Verified in scratch:

```lean
example {T : ℝ} (u : ℝ × Space → Space)
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) : Continuous (fun x : Space => u (t, x)) := by
  rw [← continuousOn_univ]
  exact hu.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun x _ => ⟨ht, mem_univ _⟩)
```

`I02/Mixed.lean:52` has a `continuous_slicePath` but it is stated for a globally
`ContDiff` field, so it does not apply here.  Three lines in the assembly lane,
or a small shared helper if a second consumer appears.

### 6. (LOW, process) The four tactic frictions are not in `logs/LESSONS.md`

`CLAUDE.md` rule 4 sends cross-task frictions to `logs/LESSONS.md`, one line
each, newest on top.  All four are cross-task Lean-tactic lessons (they are not
about R42 mathematics), and none of them currently appears there — I grepped for
`dsimp`, `notMem_tsupport`, `split_ifs`, `if_pos`, `deprecat`: no hits.  The
`ATTEMPTS_CORRECTION.md` record is excellent and satisfies the primary
requirement; two one-line LESSONS entries (the `set`/`dsimp` one and the
`if_pos`/`if_neg` deprecation) would keep the next lane from paying twice.

### 7. (INFO) The module is not yet in any CI-compiled closure

`formalization/NSFormalization.lean` imports no `Section4` module at all (0 hits),
and CI runs `make check` + `lake -d verification test`, which builds only the
registered contracts' import closure.  So `Section4/R42/CorrectionPath.lean` is
**not** compiled by CI until an R42 V2 contract/binding pulls it in.  This is the
pre-existing convention for every `Section4/*` module, not a lane defect — noted
so the R42 contract lane knows the first CI exposure of this file is its own PR.

## Consistency (check 3)

* Imports are exactly `NSFormalization.Section4.D01.ForceClass` and
  `NSFormalization.Section4.A02.SolutionClass`; `I03.Angular` arrives
  transitively through `D01/ForceClass.lean:2`.  Canonical only.
* No restated definitions: the only local bindings are three `set`s (`b`, `χ`,
  `F`) inside one proof.
* The docstring claim "`A02.IsSobolevDatum` and `D01.IsSobolevDatum` are
  definitionally equal" **verified** by a scratch `example ... := rfl` (below);
  likewise `A02.SpaceTimeField = VelocityField := rfl`.
* `set_option pp.fullNames true` printing confirms the conclusion is token-for-token
  `ClassicalSolutionR.sobolev` with `T := S`, `self.velocity := d`, same
  `A02.IsSobolevDatum`, same `A02.SpaceTimeField`, same `↑m` coercion,
  same `ContDiffOn ℝ (↑⊤)`.

## Honesty of ATTEMPTS (check 4)

All three cited declarations open at the cited lines:
`D01.contDiff_angularPath` `ForceClass.lean:133`,
`D01.schwartzPairable_of_isSobolevDatum` `ForceClass.lean:250`,
`D01.isSobolevDatum_add` `ForceClass.lean:261`;
`I03.angularPath` `Angular.lean:90`, `I03.angularPath_pairing` `Angular.lean:97`.
All four frictions reproduce:

1. **`dsimp only [hFdef]` makes no progress on a `set` binding.**  Reproduced:
   `fail_if_success dsimp only [hFdef]` succeeds (dsimp errors out with no
   progress) while `simp only [hFdef]` unfolds and beta-reduces. ✅
2. **`image_eq_zero_of_notMem_tsupport` mis-infers under an ascription.**
   Reproduced verbatim — with the target `d (pt, px) = 0` the elaborator unifies
   `f := d`, `x := (pt, px)` and reports
   *"has type `px ∉ tsupport fun x => d (pt, x)` but is expected to have type
   `(pt, px) ∉ tsupport d`"*. ✅  The recorded fix (elaborate with no ascription,
   re-ascribe afterwards) is the right one.
3. **`split_ifs` consumes a sign hypothesis from context.**  Reproduced: with
   `hq0 : 0 ≤ q.1` in context, `split_ifs with h0` yields a *single* goal and
   warns `unused name: h0`; without it, two goals. ✅
4. **`if_pos`/`if_neg` deprecated at v4.34.0-rc2.**  Reproduced:
   `` `if_pos` has been deprecated: Use `ite_eq_left` instead `` and
   `` `if_neg` has been deprecated: Use `ite_eq_right` instead ``. ✅

One correction of emphasis, not of fact: `ATTEMPTS_CORRECTION.md` says the datum
is obtained "no `isSobolevDatum_unique` needed" — right, and worth stating as the
deliberate improvement over the `LIFESPAN_SPLIT.md` sketch, which routed through
it.  Likewise the sketch asked for spacetime support in `t > 0`
(`= D01.MemForceCompact`); the implementation's `F` is supported in
`Icc 0 b ×ˢ closedBall x₀ r`, which touches `t = 0`, and that is fine because
`I03.angularPath` asks only for `ContDiff` + `HasCompactSupport`.  The split
document is the stale one here, not the module.

## Commands run

All from `/data_8T/ping/blowup_density/.claude/worktrees/075-R42-correction-path`,
after `bash scripts/lean-install.sh` (idempotent; ended `== OK`),
`. scripts/lean-env.sh`, `export LEAN_NUM_THREADS=6`, one lake process at a time.

| command | result |
|---|---|
| `cd verification && lake build NSFormalization.Section4.R42.CorrectionPath` | `Build completed successfully (9879 jobs).` — no warning attributable to the new file (all warnings are pre-existing `Paper3.*` / `Source.*` linter noise) |
| `cd verification && lake env lean ../formalization/NSFormalization/Section4/R42/CorrectionPath.lean` | prints nothing, `RC=0` |
| `cd verification && lake env lean ../research/R42/axioms_correction.lean` | 2 declarations, each `[propext, Classical.choice, Quot.sound]` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' …/CorrectionPath.lean` | no match (`RC=1`) |
| `make check` | architecture checks OK, `test_contract_policy` 13 tests OK, `check_work_queue` 30 items OK |
| `git show --stat 1e88356` | 3 files, +302/−0; no `Contracts/V1/*`, no `Tests/*`, no `paper/*` touched; worktree clean |
| scratch `/tmp/rev075/scratch.lean` | `example : A02.IsSobolevDatum = D01.IsSobolevDatum := rfl` ✅; `A02.SpaceTimeField = VelocityField := rfl` ✅; `if_pos`/`if_neg` deprecation warnings ✅; `image_eq_zero_of_notMem_tsupport` mis-inference ✅ |
| scratch `/tmp/rev075/scratch2.lean`, `scratch3.lean` | `dsimp`-on-`set` no-progress ✅; `split_ifs` hypothesis consumption ✅ |
| scratch `/tmp/rev075/scratch4.lean` | slice-continuity from `ContDiffOn` (finding 5) and the `v + d → u_ε` rewrite (finding 4) both compile |
| scratch `/tmp/rev075/scratch5.lean` (`pp.fullNames`) | conclusion token-identical to `ClassicalSolutionR.sobolev` |

## What the R42 assembly lane must still supply

With 1e-i closed, the `sobolev` clause of `ClassicalSolutionR ν a (force ε) S`
for `0 < S < T` is fully sourced: `reference.sobolev` on `Ico 0 (T+δ)` for `v`,
`exists_datumPath_of_localized` on `Ico 0 S` for `d = u_ε − v` (hypotheses per
finding 2, `t₁ > 0` per finding 1), `sobolev_add_of_localized` to add them, plus
the two short glue steps of findings 4 and 5.  What remains for
`LIFESPAN_SPLIT.md` item **1** (`sol_on_shorter`) is **1f**, the
`pressure_gradient` field: `∇p_ε = ∇π + ∇P_ε` with `∇π` from
`reference.pressure_gradient` and `∇P_ε` in `L²` from
`pressureDifference_support`, needing a gradient-slice additivity in `L²` that
nobody has written yet — that is the last M-sized piece of item 1, and it is
independent of everything this lane did.  Item **2** (`blowup_essSup`) still
needs **2a**, the pointwise-`SpeedUnboundedAt`-plus-continuity ⟹ `essSup` lower
bound via `IsOpenPosMeasure`; that is **in progress as lane 080**, so the
assembly lane should consume it rather than duplicate it.  Beyond the two items,
the R42 **V2 contract** must decide how the lifespan clauses enter: today
`InsertionFamilyAPI` has no `sobolev` field at all and `InsertionLifespanAPI`
(`InsertionFamily.lean`, end) is deliberately unregistered, so V2 has to add the
hypotheses under which `T^ν_{max,R}(a, g_ε) = T` and `T + δ < T^ν_{max,R}(a, g)`
become provable — at minimum the A02 maximal-solution theory and A03's
`‖z‖_∞ ≤ C‖z‖_{H²}`, both named in that record's own docstring — and then pull
`Section4/R42/CorrectionPath.lean` into the registered import closure, which is
where this file first meets CI (finding 7).
