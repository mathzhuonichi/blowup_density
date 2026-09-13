# Review — lane 052, task A02, units U2 (`velocity_unique`) and U3 (`pressure_gauge`)

Reviewer: independent opus reviewer. Worktree
`.claude/worktrees/052-A02-units-u2-u3`, HEAD `cdd92d6`, base `ed8c27a`
(merge of lane 049, PR #50). Diff = 3 files, +415 lines, all new:
`formalization/NSFormalization/Section4/A02/Uniqueness.lean` (+252),
`research/A02/axioms_u2u3.lean` (+38), `research/A02/ATTEMPTS_U2U3.md` (+125).
No existing file touched.

## Verdict: **ACCEPT**

Both `UniquenessAPI` fields are proved, verbatim, from standard logical axioms
only. Every hypothesis of the source uniqueness theorem is discharged from
`ClassicalSolutionR` fields plus the already-merged lanes 033/049; the pressure
gauge is produced in the `∃ c : ℝ → ℝ` form the contract demands, including at
`t = 0`. The reuse requirement is met and the `ATTEMPTS` log is honest. The two
findings below are cosmetic documentation nits in the `.md` log; nothing in the
Lean needs to change.

---

## 1. Builds and audits

### 1.1 Toolchain

```
cd WT && bash scripts/lean-install.sh
  → == OK
. WT/scripts/lean-env.sh ; export LEAN_NUM_THREADS=6   (no -j anywhere)
```

### 1.2 Module build — **PASS**

```
cd WT/verification && lake build NSFormalization.Section4.A02.Uniqueness
  → Build completed successfully (9940 jobs).   EXIT=0
```

Re-run after `touch`ing `Section4/A02/Uniqueness.lean` so the file is genuinely
re-elaborated, redirecting the full log:

```
touch formalization/NSFormalization/Section4/A02/Uniqueness.lean
cd WT/verification && lake build NSFormalization.Section4.A02.Uniqueness > /tmp/rev052_build.txt
  → EXIT=0
grep -c "Section4/A02/Uniqueness.lean" /tmp/rev052_build.txt  → 0
grep -c "error:"                        /tmp/rev052_build.txt  → 0
```

**Zero diagnostics are attributed to the file.** Every `warning:` in the log
names a pre-existing upstream module (`Source/FiniteHilbertBochner.lean`,
`Source/BoundedReferenceComparison.lean`, `Source/RealSobolev.lean`,
`Paper3/RealPositiveDensity.lean`, `Source/BoundedViscosityUniqueness.lean:21`,
…), all present on the base branch. The `ATTEMPTS` §5 claim "`Uniqueness` builds
with no warnings of its own" is confirmed.

### 1.3 Axiom audit and spec conformance — **PASS**

```
cd WT/verification && lake env lean ../research/A02/axioms_u2u3.lean   → EXIT=0
'NSFormalization.Section4.A02.velocity_unique_core'  depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.velocity_unique'       depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.pressure_gauge_core'   depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.pressure_gauge'        depends on axioms: [propext, Classical.choice, Quot.sound]
```

All four are exactly the three standard axioms — in particular no `sorryAx`.
Both spec-typed `example`s (`axioms_u2u3.lean:24-30` and `:33-38`) elaborated
with no error and no output, i.e. `velocity_unique` and `pressure_gauge` each
inhabit the copied spec type by `exact`-level defeq.

### 1.4 Forbidden tokens — **PASS**

```
grep -nE "sorry|admit|native_decide|\baxiom\b|maxHeartbeats" \
  formalization/NSFormalization/Section4/A02/Uniqueness.lean \
  research/A02/axioms_u2u3.lean research/A02/ATTEMPTS_U2U3.md
```

Three hits, all prose: `axioms_u2u3.lean:3` and `:11` ("axiom audit", inside a
doc-comment and a `--` comment) and `ATTEMPTS_U2U3.md:5` ("no `sorry`").
`Uniqueness.lean` itself has **no hits at all**. No `set_option` of any kind in
the file.

### 1.5 `make check` — **PASS**

```
cd WT && make check   → MAKE_EXIT=0
  python3 experiments/test_contract_policy.py → Ran 13 tests … OK
  python3 experiments/check_work_queue.py     → 30 work items: ownership,
      contract registration and task cards consistent.
  (architecture check JSON emitted, no failure)
```

---

## 2. Spec conformance

`research/A02/Spec.lean` imports `Contracts.V1.Data`; the `UniquenessAPI`
structure is at `:263`, `velocity_unique` at `:267-272`, `pressure_gauge` at
`:277-281`. Compared token by token against `Uniqueness.lean:120-126` /
`:244-249` and the two `example`s:

* **`velocity_unique` — verbatim.** `∀ (ν : ℝ) (a : SpatialField) (f :
  SpaceTimeField), 0 < ν → a ∈ initialClassR → MemForceR f → ∀ (T₁ T₂ : ℝ) (u₁ :
  ClassicalSolutionR ν a f T₁) (u₂ : ClassicalSolutionR ν a f T₂), ∀ t ∈ Ico
  (0 : ℝ) (min T₁ T₂), ∀ x : Space, u₁.velocity (t, x) = u₂.velocity (t, x)` —
  identical, including binder names, the `(0 : ℝ)` ascription and `min T₁ T₂`.
* **`pressure_gauge` — verbatim**, ending
  `PressureGaugeEquivOn (Ico (0 : ℝ) (min T₁ T₂)) u₁.pressure u₂.pressure`,
  with the argument order `p := u₁.pressure`, `q := u₂.pressure` preserved.

The `Contracts` → `A02.SolutionClass` substitution is the project's standard
one (`NSFormalization` is a dependency of `Contracts` and cannot import it) and
is documented in `axioms_u2u3.lean:17-21`. I checked the substituted objects are
token-for-token copies: `SolutionClass.lean:114-138` `ClassicalSolutionR` vs
`Contracts/V1/Data.lean:624-648`, `:109-110` `PressureGaugeEquivOn` vs
`Data.lean:589`, `:97` `initialClassR` vs `Data.lean:509`, `:100-106`
`MemForceR` vs `Data.lean:544`. All agree (`MemHInfty` differs only in line
wrapping).

### 2.1 The gauge form — **correct, and the `t = 0` endpoint is genuinely proved**

`PressureGaugeEquivOn (I) (p) (q) := ∃ c : ℝ → ℝ, ∀ t ∈ I, ∀ x, q (t,x) = p (t,x)
+ c t`. This is the **function-of-time** form, not the gradient form, and the
lane produces exactly it: `Uniqueness.lean:233` supplies the explicit witness

```
c := fun s => u₂.pressure (s, 0) - u₁.pressure (s, 0)
```

and `:239` discharges the goal in the shape
`u₂.pressure (t,x) = u₁.pressure (t,x) + (u₂.pressure (t,0) - u₁.pressure (t,0))`.
`c` is a single function of time, independent of `x` — spatial constancy per
time is what `hInterior`/`hEndpoint` establish.

`momentum` is a field on `Ioo 0 T` only (`SolutionClass.lean:130`), so `t = 0`
carries no PDE. The lane handles it as a separate continuity step, exactly as
the spec docstring and COMPARISON row U3 require:

* `pressure_time_continuousOn` (`:70-74`) gives `ContinuousOn (fun s => p (s,y))
  (Ico 0 T)` from `pressure_smooth` on the `Ico`-slab — **one-sided continuity
  at `0` is available precisely because the smoothness slab is `Ico 0 T ×ˢ univ`,
  closed at the left endpoint.**
* `φ s := (p₂(s,x) − p₁(s,x)) − (p₂(s,0) − p₁(s,0))` is `ContinuousOn` on
  `Ico 0 (min T₁ T₂)` (`:204-213`, four `.mono` restrictions), vanishes on
  `Ioo 0 (min T₁ T₂)` by the interior step, and `0 ∈ closure (Ioo 0 (min T₁ T₂))`
  gives `(𝓝[Ioo …] 0).NeBot`. `tendsto_nhds_unique` between the
  `ContinuousWithinAt` limit `φ 0` and the eventually-zero limit `0` yields
  `φ 0 = 0` (`:219-231`).

The final `rcases ht.1.lt_or_eq` at `:236` splits `Ico` into `Ioo` and `{0}` and
covers both. The interval in the conclusion is therefore genuinely `Ico`, not
`Ioo` — no silent weakening.

### 2.2 The theorems are **stronger** than the spec

`velocity_unique := fun _ _ _ hν _ _ _ _ u₁ u₂ => velocity_unique_core hν u₁ u₂`
(`:127`) and the same shape at `:250`. Both **discard `a ∈ initialClassR` and
`MemForceR f`**; the cores (`:81`, `:133`) take only `0 < ν` plus the two
`ClassicalSolutionR` bundles. No extra hypothesis was added anywhere, and two of
the spec's own hypotheses turn out to be unnecessary — uniqueness holds for any
datum/force for which two classical solutions happen to exist. Consumers can use
the `_core` forms when they lack the class memberships. This is a strengthening,
not a deviation.

---

## 3. Mathematics

### 3.1 U2: `classical_uniqueness_on_Icc` and the union

`Source/BoundedViscosityUniqueness.lean:23` has 15 hypotheses. Each is
discharged, and I checked each against the source signature:

| source hypothesis | discharged by | checked |
| --- | --- | --- |
| `hT : 0 < T` | `hT'pos`, from `T' = (t + min T₁ T₂)/2` and `hm` | ✔ |
| `hν : 0 < ν` | the lemma's own `hν` | ✔ |
| `hu, hv : ContDiffOn ℝ ∞ · (Comparison.slab 0 T')` | `uᵢ.velocity_smooth.mono` | ✔ |
| `hp, hq` (pressures) | `uᵢ.pressure_smooth.mono` | ✔ |
| `heu, hev : UniformFiniteEnergy (Icc 0 T') ·` | lane 033/049 `ClassicalSolutionR.uniformFiniteEnergy` (`A02/Energy.lean:157`) | ✔ |
| `hB0, hB` (velocity sup-bound on `Icc 0 T'`) | lane 049 `exists_velocity_bound` (`A02/Bounds.lean:214`) — **`u₁` only**, which is all the source asks | ✔ |
| `hG0, hG` (gradient sup-bound) | lane 049 `exists_gradient_bound` (`A02/Bounds.lean:240`) — `u₁` only | ✔ |
| `hdu, hdv` (divergence on `Ioo 0 T'`) | `uᵢ.divergence` on `Ico 0 Tᵢ`, weakened by `hs.1.le` / `.trans` | ✔ |
| `hNS` (equal residuals on `Ioo 0 T'`) | `uᵢ.momentum`, both `= f (s,y)` | ✔ |
| `hzero` | `(u₁.initial y).trans (u₂.initial y).symm`, both `= a y` | ✔ |

`Comparison.slab` is **`Icc`**-based, not `Ico`:
`vendor/NavierStokesAndEuler/NavierStokes/PeriodicUniqueness.lean:35`,
`slab a b = Icc a b ×ˢ univ`. The `.mono` calls at `:96-99` therefore have to
prove `Icc 0 T' ×ˢ univ ⊆ Ico 0 Tᵢ ×ˢ univ`, which is exactly what the supplied
`fun _ hz => ⟨⟨hz.1.1, lt_of_le_of_lt hz.1.2 hT'Tᵢ⟩, hz.2⟩` does, using the
*strict* `T' < Tᵢ`. The direction is right. I confirmed the `slab` unfolding
independently:

```lean
example (a b : ℝ) : NavierStokes.PeriodicUniqueness.slab a b
    = Set.Icc a b ×ˢ (Set.univ : Set NavierStokes.ProblemStatement.Space) := rfl
```

**Residual identification.** Verified independently with a scratch file
(`lake env lean /tmp/rev052_rfl.lean` → EXIT=0, then deleted), both pointwise
and at the function level:

```lean
example (ν : ℝ) (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) :
    NSFormalization.Source.residual ν u p t x
      = NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x := rfl

example (ν : ℝ) (u : VelocityField) (p : PressureField) :
    NSFormalization.Source.residual ν u p
      = NavierStokesR3.ProblemStatement.navierStokesResidual ν u p := rfl
```

Both close by `rfl`. Reading the two definitions confirms why:
`Source/Insertion.lean:21-24` and
`vendor/…/NavierStokes/R3/ProblemStatement.lean:57-62` are the same expression
`temporalDerivative + advection - ν • spatialLaplacian + pressureGradient`, the
second merely fully qualified. The `calc` at `:108-114` is therefore sound, and
`u₁.momentum`/`u₂.momentum` (both `= f (s,y)`) give the equality the source
needs.

**The union (implication I2).** `Ico 0 (min T₁ T₂) = ⋃_{T' < min} Icc 0 T'` is
done pointwise: given `t`, take `T' = (t + min T₁ T₂)/2`, so `t < T' < min T₁ T₂`,
apply the source theorem on `Icc 0 T'` and evaluate at `t ∈ Icc 0 T'` (`:116`).
This needs no set-union lemma and is correct; note `hm : 0 < min T₁ T₂` (from
`lt_min u₁.horizon_pos u₂.horizon_pos`) is what the three `linarith` calls at
`:89` consume from context.

### 3.2 U3: equal gradients → spatially constant difference

1. **Equal pressure gradients on `Ioo 0 (min T₁ T₂)` (`:151-178`).** From
   `u₁.momentum`/`u₂.momentum` the full residuals are equal. U2 gives equal
   velocities on the slab, so the velocity part agrees: `hsd` via
   `Restrict.spatialDerivative_eq_of_eqOn`, `htemp` via
   `Restrict.temporalDerivative_eq_of_eqOn` (the latter needs the *interior*
   time `ht : t ∈ Ioo …`, correctly supplied), then `hadv`/`hlap` by
   `simp only [advection/spatialLaplacian, hsd, hval]`. `navierStokesResidual`
   parses as `((∂ₜu + adv u − ν • Δu) + ∇p)`, so after rewriting the first
   summand to `u₂`'s, `add_left_cancel hres` (`:178`) isolates
   `pressureGradient u₁.pressure t y = pressureGradient u₂.pressure t y` for
   **every** `y`. Correct.
2. **`inner_pressureGradient` is domain-agnostic (`:188-189`).** The lemma lives
   in `vendor/…/NavierStokes/PeriodicUniqueness.lean:307`, a periodic file, but
   `#check` gives the statement
   ```
   inner_pressureGradient : ∀ (p : NavierStokes.ProblemStatement.PressureField)
     (t : ℝ) (x w : NavierStokes.ProblemStatement.Space),
     inner ℝ w (pressureGradient p t x) = (fderiv ℝ (fun y => p (t, y)) x) w
   ```
   — **no periodicity, `UnitPeriods` or torus hypothesis of any kind**, and
   `Space` is `EuclideanSpace ℝ (Fin 3)`
   (`vendor/…/NavierStokes/ProblemStatement.lean:30`), not a torus. It is a pure
   unfolding of the coordinate definition of `pressureGradient` against
   `fderiv_apply_eq_sum`. Reusing it here is legitimate; only the *file* is
   periodic, not the lemma. `ext w` then upgrades the pointwise gradient
   equality to equality of the two `fderiv`s as continuous linear maps.
3. **Slice differentiability (`:61-67`).** `pressure_slice_differentiableAt`
   uses `Ico_mem_nhds_iff.mpr ht` with `ht : t ∈ Ioo 0 T`, so `Ico 0 T ∈ 𝓝 t`;
   `prod_mem_nhds … univ_mem` puts `(t,y)` in the *interior* of the smoothness
   slab, hence `ContDiffAt`, hence `DifferentiableAt` after composing with
   `z ↦ (t,z)`. Correct, and it is exactly why this step is restricted to
   interior times.
4. **Constancy (`:191-196`).** `fderiv_fun_sub` + `hfd` + `sub_self` gives
   `fderiv (p₂-slice − p₁-slice) y = 0` for all `y`; Mathlib's
   ```
   is_const_of_fderiv_eq_zero : Differentiable 𝕜 f → (∀ x, fderiv 𝕜 f x = 0)
     → ∀ x y, f x = f y
   ```
   is stated for `f : E → G` on a normed space `E` over an `IsRCLikeNormedField`,
   which `ℝ³` is; the connectedness the informal argument invokes is supplied by
   Mathlib's ambient-normed-space hypothesis. Instantiating at `x` and `0` gives
   `D t x = D t 0`, i.e. the constant is `c t = p₂(t,0) − p₁(t,0)` — the same
   `c` later handed to the existential. Consistent.
5. **Endpoint.** See §2.1. Correct and genuinely needed.

---

## 4. Reuse and dedupe — **PASS**

`Uniqueness.lean:1-4` imports `A02.Energy`, `A02.Bounds`, `A02.Restrict`,
`Source.BoundedViscosityUniqueness`. All three `A02` modules import the single
`A02/SolutionClass.lean` (verified: `Restrict.lean:1`, `Energy.lean:1`,
`Bounds.lean:1`), so the lane-040 dedupe holds and there is no duplicate
environment entry — the build confirms it.

`Restrict`'s public lemmas are used at the two call sites:
`spatialDerivative_eq_of_eqOn` (`Restrict.lean:125`) at `Uniqueness.lean:149`
and `temporalDerivative_eq_of_eqOn` (`Restrict.lean:142`) at `:159`. No
re-proved copy remains.

```
grep -rn "private" formalization/NSFormalization/Section4/A02/
  → Uniqueness.lean:61: private theorem pressure_slice_differentiableAt
  → Uniqueness.lean:70: private theorem pressure_time_continuousOn
```

Exactly the two pressure-slice helpers, and no others anywhere in `A02`. They
have **no equivalent in `Restrict.lean`**:

```
grep -n "DifferentiableAt\|ContinuousOn\|ContDiffAt\|contDiffAt" \
  formalization/NSFormalization/Section4/A02/Restrict.lean
  → (no matches)
```

`Restrict.lean`'s `section Congr` contains only slab-congruence facts
(`slice_eq_of_eqOn`, `scalarSlice_eq_of_eqOn`, `spatialDerivative_eq_of_eqOn`,
`pressureGradient_eq_of_eqOn`, `temporalDerivative_eq_of_eqOn`,
`navierStokesResidual_eq_of_eqOn`, `ClassicalSolutionR.congr`) — none of which
asserts differentiability or continuity of a slice. The two helpers are
genuinely new, as `ATTEMPTS` §1 claims.

---

## 5. Honesty spot-checks — **both reproduce**

I reconstructed the two recorded snags by `sed`-patching a copy of the source in
`/tmp` and elaborating it with `lake env lean` (the worktree source was never
modified).

### 5.1 `ATTEMPTS` §4 bullet 2 — the `EventuallyEq` annotation

Replacing `Uniqueness.lean:225` with an un-annotated `have hev :=`:

```
lake env lean /tmp/rev052_snagA.lean   → EXIT=1
/tmp/rev052_snagA.lean:226:6: error: don't know how to synthesize implicit argument `a`
  @eventually_nhdsWithin_of_forall ℝ … (Ioo 0 (min T₁ T₂)) ?m.1101
    (fun s => 0 = φ s) fun s hs => Eq.symm (hzero_on s hs)
```

The failure is real and at exactly the claimed site: without the
`(fun _ : ℝ => (0:ℝ)) =ᶠ[…] φ` ascription the elaborator cannot pin the filter /
`f₁` argument. The log's description ("higher-order unification is ambiguous,
fixed by annotating the `EventuallyEq` witness's type explicitly") is accurate.

### 5.2 `ATTEMPTS` §4 bullet 3 — explicit `min_le_left T₁ T₂`

Replacing all eight `min_le_left T₁ T₂` / `min_le_right T₁ T₂` at `:206-212`
with `min_le_left _ _` / `min_le_right _ _`:

```
lake env lean /tmp/rev052_snagB.lean   → EXIT=1
/tmp/rev052_snagB.lean:205:18: error: don't know how to synthesize implicit argument `t`
  @ContinuousOn.mono … (Ico 0 T₁) (Ico 0 (min T₁ ?m.847))
    (pressure_time_continuousOn u₁.pressure_smooth x)
    (Ico_subset_Ico (le_refl 0) (min_le_left T₁ ?m.847))
/tmp/rev052_snagB.lean:206:9: error: don't know how to synthesize implicit argument `b₁`
  @Ico_subset_Ico ℝ Real.instPreorder 0 0 (min T₁ ?m.847) T₁ (le_refl 0) (min_le_left T₁ ?m.847)
```

The dangling `?m.847` in the `T₂` slot is exactly the "trailing `T₂`
metavariable … uninferable inside an un-annotated `have`" the log describes.
Accurate.

Both scratch files were deleted after the check.

---

## 6. Findings

### F1 — severity: **none (positive note)** — `velocity_unique`, `pressure_gauge`

The delivered theorems are **stronger than the spec**: the cores
`velocity_unique_core` (`Uniqueness.lean:81`) and `pressure_gauge_core` (`:133`)
use neither `a ∈ initialClassR` nor `MemForceR f`, only `0 < ν` and the two
`ClassicalSolutionR` bundles. The spec fields are obtained by discarding those
two hypotheses (`:127`, `:250`). No extra hypothesis was introduced anywhere.
No fix needed; downstream units (U5, U7, U8, U9) may prefer the `_core` forms.

### F2 — severity: **cosmetic** — `research/A02/ATTEMPTS_U2U3.md:5`

The log cites `` `UniquenessAPI` (`research/A02/Spec.lean:268-290`) ``. The
actual structure is `Spec.lean:263-281`, with `velocity_unique` at `:267-272`
and `pressure_gauge` at `:277-281`; line 290 is already inside the next section's
doc-comment. The module docstring in `Uniqueness.lean:10` has the correct range
(`:263-281`), as do the `axioms_u2u3.lean` doc-comments, so this is an isolated
typo in the log.

**Fix:** change `Spec.lean:268-290` to `Spec.lean:263-281` in
`ATTEMPTS_U2U3.md:5`.

### F3 — severity: **cosmetic** — `research/A02/ATTEMPTS_U2U3.md:109`

The log reports the snag-5.1 error as `` "don't know how to synthesize
placeholder `b`" ``. The reproduced message names implicit argument `` `a` ``
(the filter argument of `eventually_nhdsWithin_of_forall`), not `b`. Same error
class, same line, same cause — only the metavariable's name in the quoted text
differs (plausibly from an earlier variant of the `have`). The substantive claim
is correct.

**Fix:** quote the actual message, or drop the backticked placeholder name.

---

## 7. Commands run, in order

```
cd WT && bash scripts/lean-install.sh                                   → == OK
. WT/scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
cd WT/verification && lake build NSFormalization.Section4.A02.Uniqueness
                                    → Build completed successfully (9940 jobs); EXIT=0
touch …/A02/Uniqueness.lean ; lake build … > /tmp/rev052_build.txt      → EXIT=0
  grep -c "Section4/A02/Uniqueness.lean" /tmp/rev052_build.txt          → 0
  grep -c "error:"                       /tmp/rev052_build.txt          → 0
cd WT/verification && lake env lean ../research/A02/axioms_u2u3.lean    → EXIT=0
  4 × "depends on axioms: [propext, Classical.choice, Quot.sound]"
  both spec-typed `example`s elaborate silently
grep -nE "sorry|admit|native_decide|\baxiom\b|maxHeartbeats" (3 changed files)
                                    → 3 hits, all inside comments/prose
grep -rn "private" formalization/NSFormalization/Section4/A02/
                                    → 2 hits, both in Uniqueness.lean (§4)
grep -n "DifferentiableAt\|ContinuousOn\|ContDiffAt" …/A02/Restrict.lean → no matches
cd WT && make check                                                     → EXIT=0
cd WT/verification && lake env lean /tmp/rev052_rfl.lean                → EXIT=0
  (residual = navierStokesResidual by rfl, pointwise and function-level;
   slab a b = Icc a b ×ˢ univ by rfl; #check of the two Mathlib/vendor lemmas)
cd WT/verification && lake env lean /tmp/rev052_snagA.lean              → EXIT=1 (expected)
cd WT/verification && lake env lean /tmp/rev052_snagB.lean              → EXIT=1 (expected)
```

Lake was invoked only from `WT/verification`, one at a time, never with `-j`.
No git write command was run; the only file written in the worktree is this
review.
