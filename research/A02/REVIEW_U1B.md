# Review — lane 049, task A02 unit U1b (`Section4/A02/Bounds.lean`)

Reviewer: opus lane reviewer. Worktree `.claude/worktrees/049-A02-unit-u1b`, commit
`c8768ba`. Read/build only; no code was changed.

## Verdict: **ACCEPT**

The two theorems are exactly the `hB0/hB` and `hG0/hG` hypotheses of
`Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc`, on the nose, with
`T := b`. The new jet-side order shift is correct with constant `1`, and the
"two jet norms" risk is **not** realized: `A03.jetENorm`, `D01.jetSobolevENorm`
and `Contracts.V1.BoundedRep.jetSobolevENorm` are the *same* definition, checked
by `rfl` (see F1). Everything is `sorry`-free on the three standard axioms. No
blocking or major findings; four informational notes below.

---

## 1. Gate results

| gate | result |
|---|---|
| `lake build NSFormalization.Section4.A02.Bounds` | exit 0, `Build completed successfully (9880 jobs)`, 2.2 s wall (replay) |
| fresh elaboration `lake env lean ../formalization/.../A02/Bounds.lean` | exit 0, **zero messages** — no warning, info or error originates in the file |
| `lake env lean ../research/A02/axioms_u1b.lean` | elaborates; `'…u1b_shapes_ok' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `#print axioms` on `exists_velocity_bound`, `exists_gradient_bound`, `jetENorm_dirDeriv_le` | each `[propext, Classical.choice, Quot.sound]` |
| `grep -nE "sorry\|admit\|native_decide\|axiom\|maxHeartbeats"` on `Bounds.lean` + `axioms_u1b.lean` | no hits in `Bounds.lean`; in `axioms_u1b.lean` only the docstring line 15 and the `#print axioms` command at line 46 |
| `make check` | `Ran 13 tests … OK`; `30 work items: ownership, contract registration and task cards consistent.` (8.5 s) |
| `make test` (extra) | all `Tests.*` contracts `checked; standard logical axioms only`; every warning emitted comes from pre-existing `Paper3/*`, `Source/*` modules, none from A02 |
| `make test-mutations` (extra) | `implementation_refactor: accepted`, `admitted_proof/extra_axiom/weakened_hypothesis: rejected as required` |
| `lake build` (whole default target, extra) | `Build completed successfully (9953 jobs)` |

Exact commands (run from the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`,
one lake at a time, all lake invocations from `verification/`):

```
cd verification && lake build NSFormalization.Section4.A02.Bounds
cd verification && lake env lean ../formalization/NSFormalization/Section4/A02/Bounds.lean
cd verification && lake env lean ../research/A02/axioms_u1b.lean
cd verification && lake env lean /tmp/u1b_check2.lean      # scratch cross-checks, see §3
make check ; make test ; make test-mutations
```

---

## 2. Shape — do the theorems fit `classical_uniqueness_on_Icc`?

`BoundedViscosityUniqueness.lean:23` (with `open NavierStokes.ProblemStatement (spatialDerivative …)`):

```
(hB0 : 0 ≤ B) (hB : ∀ t ∈ Icc (0:ℝ) T, ∀ x, ‖u (t,x)‖ ≤ B)
(hG0 : 0 ≤ G) (hG : ∀ t ∈ Icc (0:ℝ) T, ∀ x, ‖spatialDerivative u t x‖ ≤ G)
```

`#check` output of the two lane theorems:

```
exists_velocity_bound : ∀ {ν T} {a f} (u : ClassicalSolutionR ν a f T) {b : ℝ},
  0 ≤ b → b < T → ∃ B, 0 ≤ B ∧ ∀ t ∈ Icc 0 b, ∀ (x : Space), ‖u.velocity (t, x)‖ ≤ B
exists_gradient_bound : ∀ {ν T} {a f} (u : ClassicalSolutionR ν a f T) {b : ℝ},
  0 ≤ b → b < T → ∃ Gb, 0 ≤ Gb ∧ ∀ t ∈ Icc 0 b, ∀ (x : Space),
    ‖NavierStokes.ProblemStatement.spatialDerivative u.velocity t x‖ ≤ Gb
```

* same set `Icc 0 b`, `∀ x` unrestricted, `0 ≤ ·` conjunct present;
* the printed head is literally `NavierStokes.ProblemStatement.spatialDerivative`
  (`Bounds.lean` gets it from `open NavierStokes.ProblemStatement` at `:66`, and the
  `NavierStokesR3.ProblemStatement` namespace is *not* opened there, so no ambiguity);
* `axioms_u1b.lean:41-45` discharges the call with a bare `exact` — no `simpa`, no
  `convert`, no conversion lemma — which is the strongest possible confirmation of shape.

Assumption ledger of the scratch application (`axioms_u1b.lean`):

* `heu`/`hev` ← `u.uniformFiniteEnergy hb0 hbT` and `v.uniformFiniteEnergy hb0 hbT`
  (lane 033, `A02/Energy.lean:252`; confirmed by
  `git log -- …/A02/Energy.lean` → `11af78b [033-A02] Unit U1a …`). Both energy
  slots, one per solution. ✓
* `hB0/hB`, `hG0/hG` ← `u.exists_velocity_bound` / `u.exists_gradient_bound`, i.e. for
  **one** of the two solutions only, as the source theorem requires. ✓
* Nothing else: `exists_velocity_bound`/`exists_gradient_bound` take only
  `u : ClassicalSolutionR ν a f T`, `0 ≤ b`, `b < T`. **No** `0 < ν`, no
  `a ∈ initialClassR`/`MemHInfty a`, no `MemForceR f`, no typeclass side conditions.
  `ClassicalSolutionR` (`SolutionClass.lean:100-124`) is used only through
  `velocity_smooth` and `sobolev`. ✓
* The remaining scratch parameters (`hu hv hp hq hdu hdv hNS hzero`, `0 < b`, `0 < ν`)
  are the caller's, as the brief anticipates. See N1 for a tightening.

---

## 3. Mathematics

### F1 (checked, clean) — the jet norm is one norm, not two

`A03.jetENorm m z = ∑ j ∈ range (m+1), eLpNorm (iteratedFDeriv ℝ j z) 2 volume`
(`A03/BoundedRepresentative.lean:106`) and
`D01.jetSobolevENorm m v` (`D01/DatumToJets.lean:127`) have byte-identical bodies.
Verified as definitional, not merely "looks the same":

```lean
example (m : ℕ) (v : Space → Space) : D01.jetSobolevENorm m v = A03.jetENorm m v := rfl  -- ✓
example (m : ℕ) (v : Space → Space) : D01.SmoothJetsUpTo m v = A03.SmoothL2UpTo m v := rfl -- ✓
example (s : ℝ) (z A)              : D01.IsSobolevDatum s z A = A02.IsSobolevDatum s z A := rfl -- ✓
```

and the registered contract agrees: `verification/Bindings/BoundedRepresentative.lean`
carries `boundedRep_jetSobolevENorm_eq : Contracts.V1.BoundedRep.jetSobolevENorm m v
= A03.jetENorm m v := rfl`, and binds `supNorm_le := A03.enorm_le_jetENorm`. So the
`A03.enorm_le_jetENorm` used at `Bounds.lean:129,169` is exactly the registered
`A03.bounded_representative`'s embedding, and `D01.jetSobolevENorm_le_sobolevENorm`
at `:132,174` speaks about the same quantity. **No mismatch.**

### F2 (checked, clean) — the constant in the order shift is 1

`norm_iteratedFDeriv_dirDeriv_le` (`:77`):
`‖iteratedFDeriv ℝ j (∂ᵢw) x‖ ≤ ‖iteratedFDeriv ℝ (j+1) w x‖`, no constant.
`ContinuousLinearMap.norm_iteratedFDeriv_comp_left` *does* introduce the factor
`‖L‖` with `L = ContinuousLinearMap.apply ℝ Space (coordinateVector i)`, and the proof
kills it with `hL : ‖L‖ ≤ 1` (`:81-84`) followed by
`mul_le_of_le_one_left (norm_nonneg _) hL` (`:90`). `hL` is proved by
`opNorm_le_bound` from `f.le_opNorm (coordinateVector i) : ‖f eᵢ‖ ≤ ‖f‖ * ‖eᵢ‖` closed
by `simp [coordinateVector]` — i.e. **yes, `‖eᵢ‖ = 1` is the load-bearing step**.
Independently checked:

```lean
example (i : Fin 3) : ‖NavierStokes.ProblemStatement.coordinateVector i‖ = 1 := by
  simp [NavierStokes.ProblemStatement.coordinateVector]   -- ✓
```

(`coordinateVector i = EuclideanSpace.single i 1`, `vendor/…/NavierStokes/ProblemStatement.lean:39`.)
The `norm_iteratedFDeriv_fderiv` step is the exact Mathlib identity
`‖iteratedFDeriv j (fderiv f) x‖ = ‖iteratedFDeriv (j+1) f x‖`, constant-free.

The sum step `jetENorm_dirDeriv_le` (`:106`) is then
`∑_{j≤2} ‖D^j ∂ᵢw‖_{L²} ≤ ∑_{j≤2} ‖D^{j+1}w‖_{L²} = ∑_{1≤j≤3} ‖D^j w‖_{L²}
≤ ∑_{0≤j≤3} ‖D^j w‖_{L²}`, the last step dropping the nonnegative order-0 term via
`le_self_add` and reindexing by `Finset.sum_range_succ'`. Correct, constant `1`.
In `ℝ≥0∞` the dropped term is `≥ 0` unconditionally, so nothing is hidden in a
finiteness side condition.

### F3 (checked, clean) — uniformity in `t` comes from `sobolev`'s `ContinuousOn`, not from a hidden path class

`Bounds.lean:217-220` / `:243-246`:

```lean
obtain ⟨G, hGc, hGd⟩ := u.sobolev 2          -- resp. u.sobolev 3
have hsub : Icc 0 b ⊆ Ico 0 T := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hbT⟩
obtain ⟨C, hC⟩ := (isCompact_Icc).exists_bound_of_continuousOn (hGc.mono hsub)
```

`hGc` is exactly the `ContinuousOn G (Ico 0 T)` conjunct of
`ClassicalSolutionR.sobolev` (`SolutionClass.lean:119-121`), used at orders **2**
(velocity) and **3** (gradient). `grep -n "HasSmoothSobolevPath" Bounds.lean` → no hits.
The *datum* conjunct is passed separately to
`D01.smoothSquareIntegrableJets_slice` as `(fun m => (u.sobolev m).imp fun _ h => h.2)`,
which by its own docstring does not use the `ContinuousOn` half — so the two halves are
used for the two different jobs, exactly as the module docstring's sub-step (iv) claims.
`hC0 : 0 ≤ C` comes from `hC 0 ⟨le_rfl, hb0⟩`, which is where `hb0` is genuinely needed.

### F4 (checked, clean) — the physical/jet identification and the factor 3

`spatialDerivative u t x = fderiv ℝ (fun y => u (t,y)) x` is definitional
(`vendor/…/NavierStokes/ProblemStatement.lean:59`); verified by `rfl`. The operator
norm is reduced to three coordinate images by `A05.opNorm_le_sum`
(`‖T‖ ≤ ∑ i, ‖T eᵢ‖`, an ℓ²≤ℓ¹ estimate on three terms), costing the factor `3` in the
final constant `3 * (C_∞ * jetSobolevConst 3 * C_t)`. Each `T eᵢ` is `A05.dirDeriv i (slice) x`
by definition (`A05/SmoothJets.lean:87`), and `∂ᵢ(slice)` is back in the all-jet-`L²`
class by `D01.smoothSquareIntegrableJets_dirDeriv` (`DatumToJets.lean:479`, itself
`A05.SmoothL2.dir`). So the gradient route is
`‖∂ᵢ(slice) x‖ ≤ C_∞ · jetENorm 2 (∂ᵢ slice) ≤ C_∞ · jetENorm 3 (slice)
≤ C_∞ · C₃ · sobolevENorm 3 (slice) ≤ C_∞ · C₃ · ‖G t‖` — it never needs a datum for
`∂ᵢu`, which is precisely why the open datum-side shift is bypassed. Sound.

---

## 4. Honesty spot-checks of `research/A02/ATTEMPTS_U1B.md`

**Claim 2 (`mul_le_mul_left'` "not in the module's Mathlib import closure"): TRUE.**
Scratch file importing only `NSFormalization.Section4.A02.Bounds`:

```
/tmp/u1b_check1.lean:5:8:  error: Unknown identifier `mul_le_mul_left'`
/tmp/u1b_check1.lean:6:54: error: Unknown identifier `mul_le_mul_left'`
```

(This is counter-intuitive — the name is ordinary Mathlib — so it was worth checking;
the claim is accurate as stated, and the `gcongr` substitution is legitimate.)

**Claim on the open datum-side shift at `SmoothDatum.lean:388`: TRUE.**
Lines 386-390 read, verbatim:

```
* U1b(ii), the order shift `‖∇v‖_{H²} ≤ ‖v‖_{H³}` on the angular datum carrier, is
  untouched: `norm_smoothAngularDatum_le` is a **one-sided** bound in the physical Bessel
  iterates, not a comparison of two datum norms. -/
```

and `exists_isSobolevDatum_fderiv` (`SmoothDatum.lean:400-405`) concludes
`∃ A : RealVectorSobolev s, IsSobolevDatum s (fun x => fderiv ℝ z x v) A` with **no**
norm comparison — a non-quantitative existence, exactly as the attempts file says.
The stated build/axiom results in the attempts file also reproduce.

---

## 5. Findings

All informational; none blocks the merge.

1. **N1 — informational — `research/A02/axioms_u1b.lean:26-31,34`.** The scratch
   assumes `hu`, `hp` and `hdu` as parameters, but all three are already derivable
   from `u`'s own fields: `Comparison.slab 0 b = Icc 0 b ×ˢ univ`
   (`vendor/…/NavierStokes/PeriodicUniqueness.lean:35`) and `Icc 0 b ⊆ Ico 0 T`, so
   `u.velocity_smooth.mono` gives `hu`, `u.pressure_smooth.mono` gives `hp`, and
   `u.divergence` (stated on `Ico 0 T`) gives `hdu` on `Ioo 0 b`. The scratch is
   therefore *conservative*, never unsound — it understates what the class already
   supplies. Fix (optional, for U2): derive them rather than assume them, leaving
   only `hv/hq/hdv/hNS/hzero` and `0 < ν` as genuine caller obligations.

2. **N2 — cosmetic — `research/A02/axioms_u1b.lean:24`.** `hbpos : 0 < b` and
   `hb0 : 0 ≤ b` are both taken; `hb0` is `hbpos.le`. Fix: drop `hb0` and write
   `hbpos.le` at the two use sites.

3. **N3 — informational — module reachability.** `formalization/lakefile.toml`
   declares `[[lean_lib]] name = "NSFormalization"` with no globs and
   `formalization/NSFormalization.lean` imports no `Section4` module, so
   `Section4/A02/Bounds.lean` is compiled only when named explicitly (as this lane's
   gate does) and is not in any default build target. This is the **status quo** for
   the sibling `Section4/A02/Energy.lean` too, so it is not a lane defect — recording
   it so that U2 remembers to `import NSFormalization.Section4.A02.Bounds` and so the
   lane's module keeps getting built by name in CI.

4. **N4 — informational — defeq bridges relied on.** `Bounds.lean` freely mixes
   `A02.IsSobolevDatum` (from `u.sobolev`) with `D01.IsSobolevDatum`
   (`D01.sobolevENorm_le_of_isSobolevDatum`), and `D01.SmoothJetsUpTo` with
   `A03.SmoothL2UpTo`. All three identifications are `rfl` (verified in F1), which is
   the documented intent of the verbatim restatements. No action; noted because a
   future edit to either copy would break `Bounds.lean` silently at the *use* sites
   rather than at a bridge lemma.
