# Review — lane 072, task R42 (lifespan-clause split-and-start)

Reviewer: independent opus reviewer, read/build only.
Under review: `formalization/NSFormalization/Section4/R42/Lifespan.lean`,
`research/R42/LIFESPAN_SPLIT.md`, `research/R42/ATTEMPTS_LIFESPAN.md`,
`research/R42/axioms_lifespan.lean` (commit `6df67fd`, 4 files, +492, no deletions).

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean is correct, clean and honestly reported: six lemmas, all six true and
usefully stated, zero warnings from the file, standard three axioms, `make check`
green, and both spot-checked frictions reproduce character for character.

The notes are all against the **split document**, which is this lane's principal
deliverable.  Three of the items it files as *missing D01 units* / *blocked, do not
attempt* are **already proved and already registered contract fields** at this
lane's own base commit.  The claims are stale inheritances from
`research/R42/ATTEMPTS.md §5` (lane 027), which lane 028 (`D01/ForceClass.lean`)
superseded; the lane cites `ATTEMPTS.md §5` and did not re-check it.  Findings 1–3
below are markdown-only corrections, but they matter: a split document exists to
size the remaining work, and as written it tells the next lane not to attempt two
pieces that are one-liners today.

## Gate results (exact commands)

All from the worktree root `.claude/worktrees/072-R42-lifespan-split`, after
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`; lake only from `verification`.

| # | command | result |
|---|---|---|
| 1 | `bash scripts/lean-install.sh` | exit 0, `== OK` |
| 2 | `cd verification && lake build NSFormalization.Section4.R42.Lifespan` | **exit 0**, `Build completed successfully (9872 jobs)` |
| 2b | same, output grepped for `R42\|Lifespan` | **no matches** — every warning in the build log is pre-existing (`Source/RealSobolev`, `Paper3/*`, `Source/BoundedViscosityUniqueness`) |
| 3 | `cd verification && lake env lean ../formalization/NSFormalization/Section4/R42/Lifespan.lean` | exit 0, **0 bytes of output** — linter-clean |
| 4 | `cd verification && lake env lean ../research/R42/axioms_lifespan.lean` | exit 0; all six declarations `depends on axioms: [propext, Classical.choice, Quot.sound]` |
| 5 | `grep -nE "sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option"` on `Lifespan.lean` + `axioms_lifespan.lean` | only the six `#print axioms` lines of the checker file; **nothing** in `Lifespan.lean` |
| 6 | `make check` | **exit 0** — plan check, `check_contracts` (13 registered contracts), 13 policy tests, `30 work items … consistent` |
| 7 | `git diff --stat erenup/integration...HEAD` | 4 files, `+492`, no deletions, no stray edits |

Informational: the branch is **21 commits behind** `erenup/integration`; the merge
lane must rebase and re-run.  Also informational: `Section4.R42.Lifespan` is
imported by no module, so `make test` / the default `lake build` do not compile it.
That is the established pattern here (17 other Section 4 modules are orphans the
same way — `A02.Maximal`, `A04.*`, `B01.*`, `B02.*`, `C01.*`, `D01.LeraySymbol`,
`D01.OrderZeroDatum`), so no action is requested.

## The six lemmas

All six check out.  Statement-level review:

1. **`limsup_eq_top_of_le_add_const`** — `{L : Filter α}` **arbitrary filter**, `f g : α → ℝ≥0∞`,
   `hC : C ≠ ⊤`, `hle : ∀ a, f a ≤ g a + C`, `htop : limsup f L = ⊤ ⟹ limsup g L = ⊤`.
   `C ≠ ⊤` **is** a hypothesis, and it is load-bearing: at `C = ⊤`, `f ≡ ⊤`, `g ≡ 0`
   satisfies `hle` and `htop` with `limsup g L = 0`.  Sanity case `g ≡ 0`, `f ≡ C`: `htop`
   fails, as it must.  The proof is the right one (contradiction, `exists_between`,
   `eventually_lt_of_limsup_lt`, `limsup_le_of_le`) and is filter-generic — `ℝ≥0∞` being a
   complete lattice supplies the cobounded instances, so no `NeBot` is needed; degenerate
   `L = ⊥` is harmless because `limsup f ⊥ = 0 ≠ ⊤`.
2. **`eLpNormTop_le_ofReal`** — `(∀ x, ‖w x‖ ≤ C)`, `0 ≤ C ⟹ eLpNorm w ⊤ volume ≤ ofReal C`. Correct.
3. **`eLpNormTop_le_add`** — `‖u‖_∞ ≤ ‖u + w‖_∞ + ofReal C` under `∀ x, ‖w x‖ ≤ C`.
   **Direction is correct**: it is the *reverse* triangle inequality, obtained from
   `u = (u + w) + (-w)` and `eLpNorm_neg`, and it is exactly the shape `hle` of (1)
   wants with `f = ‖u‖_∞`, `g = ‖u + w‖_∞`.  Both `AEStronglyMeasurable` hypotheses are
   genuinely needed by `eLpNorm_add_le`.
4. **`limsup_eLpNormTop_add_eq_top`** — the `04-whole-space.tex:35` transfer.  Composition
   of (1) and (3) with `C := ofReal C`, `ENNReal.ofReal_ne_top`.  Instantiation reading
   (`L := 𝓝[<] T`, `u := U_ε`, `w := v + w_ε`) is right: `Filter.limsup · (𝓝[<] T)` is
   `MaximalPartial.limsupLeft T` and `eLpNorm · ⊤ volume` is `MaximalPartial.speedENorm`,
   both definitionally (`MaximalPartial.lean:101,106`).
5. **`hasCompactSupport_of_tsupport_subset_ball`** — `tsupport d ⊆ Metric.ball c r ⟹ HasCompactSupport d`,
   via `isCompact_closedBall` (proper space) + `isClosed_tsupport`.  Correct, including the
   degenerate `r ≤ 0`.
6. **`exists_isSobolevDatum_of_contDiff_hasCompactSupport`** — every **real** order `s`
   (not just `ℕ`), through `D01.exists_isSobolevDatum_of_contDiff_memLp`
   (`SmoothDatum.lean:290`), whose own conclusion is at every real `s`.  `IsSobolevDatum`
   here **is** the D01 restatement of `Contracts.V1.Data.IsSobolevDatum`
   (`SmoothDatum.lean:237` "restated verbatim"; the `rfl` bridge is
   `verification/Bindings/DatumLemmas.lean`).  The new content is the step
   `ContDiff ∞ + HasCompactSupport ⟹ all jets in L²`; I checked that no such producer
   already exists (the in-tree `SmoothSquareIntegrableJets` producers are all
   solution-slice/force-slice, `D01/Pressure.lean`, `D01/DatumToJets.lean`), so this is
   not a duplicate.

No lemma is vacuous, over-hypothesised or mis-oriented.  Nothing in `Lifespan.lean`
needs to change.

## Assessment of Finding A (`u_ε` is not compactly supported)

**Correct, and correctly consequential.**  Verified against the contract:
`InsertionFamilyAPI.velocity_formula` (`Contracts/V1/InsertionFamily.lean:173`) is
`u_ε = v + w_ε + U_ε` with `v = scaling.correction.v = reference.velocity`
(`reference_velocity`, `:148`), and `reference : Data.ClassicalSolutionR ν a g (T+δ)`
(`:141`) whose `sobolev` field is a general `H^∞` datum path with no support control.
What is compactly supported is only the difference: `velocityDifference_support`
(`:240`) gives `tsupport (u_ε(t,·) − v(t,·)) ⊆ ball x₀ r` for `t ∈ Ico 0 T`.  So the
`sobolev` field of `u_ε` is genuinely `datum(v) + datum(w_ε + U_ε)`, and the lane's two
support/datum lemmas correctly attach to the **correction**, not to `u_ε`.  The lane is
right to call this a correction of the task's framing.

**But the sizing that follows from it is wrong** (see findings 1–2).  The split calls
1e an `L` blocker with two missing D01 units.  One of the two exists.  What is
actually left of 1e is *only* time-continuity of the correction's datum path, and even
that has close existing machinery the split never mentions:

* additivity (1e-ii) is **done**: `D01.isSobolevDatum_add` (`ForceClass.lean:261`,
  side condition `SchwartzPairable`, discharged for a continuous field with an
  order-`0` datum by `schwartzPairable_of_isSobolevDatum`, `ForceClass.lean:250`) and
  `D01.isSobolevPath_add` (`ForceClass.lean:320`).  Continuity of the *sum* path is then
  `ContinuousOn.add`.  Both are registered: `Contracts/V1/DatumLemmas.lean:296,309`.
* time-continuity (1e-i) is the only real content, as the task suspected.  Concretely it
  needs: `d := u_ε − v` is `ContDiffOn ℝ ∞` on `Ico 0 T ×ˢ univ`, spatially
  `tsupport ⊆ ball x₀ r` at every `t < T`, and vanishes for `t ≤ T − 2ε²` (`history`,
  `:230`).  For a fixed `S < T`, multiply by a time cutoff supported in `[0,(S+T)/2]` and
  equal to `1` on `[0,S]`; the product is globally `ContDiff` with **compact spacetime
  support in `t > 0`**, i.e. `D01.MemForceCompact`.  Then `I03.angularPath` +
  **`D01.contDiff_angularPath` (`ForceClass.lean:133`)** gives an order-`m` datum path
  that is `ContDiff ℝ ∞` *in time*, agreeing with `d`'s datum on `Ico 0 S` by
  `isSobolevDatum_unique`.  That is exactly the "`C^∞` in time clause … new in lane 028"
  the `DatumLemmas` docstring advertises, and it is what closes 1e-i.  The residual work
  is the cutoff/extension bookkeeping — an **M**, not an **L**, and it is R42-shaped
  rather than a new D01 unit.  `Contracts/V1/DatumLemmas.lean:260` confirms the framing:
  `solution_slice_smoothJets` deliberately "**discards**" the `ContinuousOn G` conjunct,
  "so nothing below asserts time regularity of the datum path".

## Assessment of Finding B (strict vs non-strict reference lifespan)

**The diagnosis is correct; the remedy analysis is incomplete and one of the two
offered options is not available.**

Correct and verified:

* `InsertionLifespanAPI.referenceLifespan` (`InsertionFamily.lean:427`) demands
  `ENNReal.ofReal (family.T + family.margin) < Data.maximalLifespanR ν family.a family.g`,
  with `family.margin = A.scaling.correction.δ` (`:341`).
* `maximalLifespanR = ⨆ S, ⨆ _ : Nonempty (ClassicalSolutionR ν a f S), ofReal S`
  (`Data.lean:657`), and `reference` is a solution on the **half-open** `[0,T+δ)`.  So
  `le_iSup₂` yields only `≤`.  The strict `<` is **genuinely underivable** from
  `reference` alone: `maximalLifespanR = ofReal (T+δ)` is consistent with everything the
  record carries.  The lane is right, and this matches the contract's own docstring
  (`InsertionFamily.lean:403-408`).
* `A02.referenceLifespan` (`MaximalPartial.lean:210`) does produce **its own** `δ_A`, with
  no relation to `family.margin`.  The mismatch the lane flags is real.

What the paper actually says (checked): `02-preliminaries.tex:34-36` defines "*regular
through `T`*" as "extends smoothly to `[0,T+δ]` for some `δ>0`", and
`04-whole-space.tex:32` hypothesises "(v,π,g) … **regular through `T+δ`** for some `δ>0`".
So the manuscript's reference is regular **through** `T+δ` — a solution strictly past
`T+δ` — which is `Data.RegularThrough ν a g (T+δ)` verbatim.  The project's own plan had
it this way too: `research/section4/STATEMENTS.md:332` writes
`reference : IsClassicalSolution … (Set.Icc 0 (T+δ))` (closed) **next to**
`referenceLifespan : T + δ < Tmax`.  `InsertionFamilyAPI` deliberately weakened this to
the half-open `[0,T+δ)`, and that weakening — not A02 — is what makes the clause
unreachable.

Consequences the split misses:

* There is a **third, S-sized** resolution the split does not list, using a lemma the
  split itself lists at line 20 as available and then never uses: add the paper's literal
  hypothesis `RegularThrough ν a g (family.T + family.margin)` to an R42-V2 (equivalently,
  strengthen `reference` to a solution on `[0, T+δ+δ')`, or read it on the closed
  `Icc 0 (T+δ)`), then apply **`A02.regularThrough_iff`** (`MaximalPartial.lean:200`) at
  `T' = T+δ` with `0 < T+δ`.  That is the field, verbatim, in one step — **no margin
  identification at all**, and `family.margin` is untouched.  The strengthening is free
  downstream: `CorrectionAPI` only needs the reference on the open `(0,T+δ)`
  (`Correction.lean:546-550`) and `InsertionFamilyAPI.reference` is recovered by
  `A02.restrict`.
* The split's option **(i)** — "taking `family.margin := δ_A` when the family is built
  (i.e. R42 chooses the margin from A02)" — is **not available as stated**.  `margin` is
  the projection `A.scaling.correction.δ` of a `ScalingAPI` that `insertionFamilyStatement`
  (`InsertionFamily.lean:390-395`) receives as a **universally quantified input**
  (`∀ S : ScalingAPI ν P … ∃ A, A.scaling = S`).  R42 cannot choose it.  It becomes
  available only if an R42-V2 re-plumbs the statement to quantify over the reference
  first, derive `δ_A`, and *then* instantiate `correctionStatement` (which does take `δ`
  as an input, `Correction.lean:543`) at `δ_A`.  That re-plumbing is real and is worth
  saying out loud; the split's one-clause phrasing hides it.

Net: the lane's conclusion — "#6 is not an S piece for this lane; flag it" — stands.  Its
severity label ("L / policy") is defensible for option (i) but overstated overall, since
option (iii) is S once the contract carries the paper's own hypothesis.

## Findings

### 1. MAJOR (research doc) — `LIFESPAN_SPLIT.md` §1e and "Blocked" item 1e: "there is **no** `IsSobolevPath` additivity lemma" is false

*Declaration/location:* `research/R42/LIFESPAN_SPLIT.md:106-111` and `:198`.

*What is wrong:* both additivity lemmas exist at this lane's base commit and are
**registered** contract fields of the enabled contract `D01.datum_lemmas`:

* `NSFormalization.Section4.D01.isSobolevDatum_add` — `formalization/NSFormalization/Section4/D01/ForceClass.lean:261`, registered as `Contracts/V1/DatumLemmas.lean:296`;
* `NSFormalization.Section4.D01.isSobolevPath_add` — `ForceClass.lean:320`, registered as `Contracts/V1/DatumLemmas.lean:309`;

and `ForceClass.lean:320`'s own docstring says it closes exactly the gap
`research/R42/COMPARISON.md §4.3` reported.  The source the split cites
(`research/R42/ATTEMPTS.md §5`) predates lane 028 and is stale.

*Fix:* rewrite 1e to state that (ii) is **done** (naming the two lemmas, their
`SchwartzPairable` side condition, and `schwartzPairable_of_isSobolevDatum` as its
discharger), that `ContinuousOn` of the sum path is `ContinuousOn.add`, and that the
residual is (i) alone.  Re-size 1e from **L** to **M** and move it out of the
"do not attempt" list as a *D01-assisted R42* item, not a missing D01 unit.

### 2. MAJOR (research doc) — split item #3 and "Blocked" item 3: `F_R + C_c^∞ ⊆ F_R` is already proved *and* already specialised to R42

*Declaration/location:* `research/R42/LIFESPAN_SPLIT.md:43` (sized **M**), `:140-148`, `:200`
("do not attempt in this lane").

*What is wrong:* the unit exists as
`D01.memForceR_add_compact` (`ForceClass.lean:344`), registered at
`Contracts/V1/DatumLemmas.lean:348`; and there is a **dedicated** lemma for precisely this
situation, `D01.memForceR_of_compact_difference` (`ForceClass.lean:401`), registered at
`Contracts/V1/DatumLemmas.lean:381`:

```
memForceR_of_compact_difference :
  ∀ g gε, MemForceR g → MemForceCompact (fun z => gε z - g z) → MemForceR gε
```

Its second argument is literally `InsertionFamilyAPI.forceDifference_compact ε hε`
(`InsertionFamily.lean:272`).  The registered docstring even says so: "`g ∈ F_R` … R42 must
carry it as a hypothesis" and "Route 1 above is therefore the one R42 can discharge
today."  So split item #3 is **S**, a single application, given the hypothesis `hg`.

*Fix:* re-size #3 from **M** to **S ✅ (available)**, name
`memForceR_of_compact_difference`, delete it from the "Blocked (M/L) — do not attempt"
list, and keep only the true residual, which the lane already states correctly elsewhere:
`InsertionFamilyAPI` carries no `hg : MemForceR g`, so an R42-V2 must add that hypothesis
field.  Note the knock-on: with #3 available, item **#4**'s `hg_ε` argument is no longer
blocked, so #4's only remaining inputs are #1, #2 and 4a.

### 3. MINOR (research doc) — the closest existing time-regularity machinery is not mentioned

*Declaration/location:* `research/R42/LIFESPAN_SPLIT.md:106-111`.

*What is wrong:* 1e-i is presented as if nothing in the tree produces a time-regular datum
path.  `D01.contDiff_angularPath` (`ForceClass.lean:133`) produces one — `ContDiff ℝ ∞` in
time — for any globally smooth, spacetime-compactly-supported field, and it is what
`memForceR_of_memForceCompact` (`ForceClass.lean:189`) uses to put `F_c` inside `F_R`.

*Fix:* record the route sketched in the Finding-A section above (time cutoff at `S < T`
→ `MemForceCompact` → `contDiff_angularPath` → `isSobolevDatum_unique` to transfer back),
and say what remains: the cutoff/extension bookkeeping and the `Ico 0 S` vs `Ici 0`
domain shuffle.

### 4. MINOR (research doc) — `#6`'s remedy list is incomplete and option (i) is not available as stated

*Declaration/location:* `research/R42/LIFESPAN_SPLIT.md:154-175`, `:201`.

*What is wrong:* see "Assessment of Finding B".  Two points: (a) the split lists
`A02.regularThrough_iff` among the reused registered interfaces (`:20`) but never applies
it, missing the one-step route at `T' = T+δ` under the paper's literal hypothesis
"regular through `T+δ`" (`02-preliminaries.tex:34-36`, `04-whole-space.tex:32`); (b) option
(i) presumes R42 can choose `family.margin`, which it cannot — `margin` is a projection of
the `ScalingAPI` that `insertionFamilyStatement` takes as an input.

*Fix:* add the third option (R42-V2 carries `RegularThrough ν a g (T+δ)`, or `reference`
is strengthened to a solution past `T+δ`; then `regularThrough_iff` at `T+δ` closes the
field, **S**).  Restate option (i) with the re-plumbing it actually requires
(quantify over the reference first, take `δ := δ_A` from `A02.referenceLifespan`, then
instantiate `correctionStatement` at `δ_A`).  Record that the root cause is the
`[0,T+δ)`-vs-`Icc 0 (T+δ)` weakening relative to `research/section4/STATEMENTS.md:332`.

### 5. NIT — citation drift

`LIFESPAN_SPLIT.md:4` cites `InsertionFamily.lean:421-434` for `InsertionLifespanAPI`
(actual `421-436`) and says it has "two fields" (three: `family`, `referenceLifespan`,
`lifespan`; the two *clauses* is what is meant).  `:165` cites `InsertionFamily.lean:407-413`
for the docstring sentence, which actually sits at `403-408`.  Harmless.

## Honesty spot-checks

Both requested frictions were re-run as isolated Lean probes against this worktree's
toolchain.  **Both reproduce exactly as recorded.**

* `ATTEMPTS_LIFESPAN.md §4.1` — `add_le_add_right` orientation.  Probe
  `(hle a).trans (add_le_add_right ha.le C)` for the goal `f a ≤ b + C`:

  ```
  error: Application type mismatch: The argument
    add_le_add_right (LT.lt.le ha) C
  has type
    C + g a ≤ C + b
  but is expected to have type
    g a + C ≤ b + C
  ```

  The recorded wrong-side orientation `C + g a ≤ C + b` is verbatim what Lean reports.

* `ATTEMPTS_LIFESPAN.md §4.3` — the `le_top` cast to `ω`.  `#check` gives
  `ContDiff.continuous_iteratedFDeriv : ↑m ≤ n → ContDiff 𝕜 n f → …` with `n : ℕ∞ω`, and
  the probe `hz.continuous_iteratedFDeriv le_top` on `hz : ContDiff ℝ ∞ z` fails with

  ```
  error: Application type mismatch: The argument hz
  has type ContDiff ℝ ∞ z
  but is expected to have type ContDiff ℝ ω z
  ```

  exactly the "`le_top` forces the smoothness index to `ω`" the lane recorded, and the
  `by exact_mod_cast le_top` used in `Lifespan.lean:171` is the right fix.

The gates table in `ATTEMPTS_LIFESPAN.md §6` also matches what I measured.  §2's
Option A / Option B discussion is a fair and useful self-criticism: the lane proved the
named Option-B piece, and correctly records that the binding should prefer Option A
because `InsertionFamilyAPI.blowup` is already stated for the full `u_ε` and Option B
would additionally need a uniform bound on `v + w_ε` near `T`.  §3 is Finding A and is
right.  I found no overclaiming anywhere in the attempts record.

## Required before merge

Findings 1, 2 and 4 — markdown edits to `research/R42/LIFESPAN_SPLIT.md` (and the
one-line pointer in `ATTEMPTS_LIFESPAN.md §5` that repeats the stale `ATTEMPTS.md §5`
claim).  No Lean change is requested.  Findings 3 and 5 are optional.
