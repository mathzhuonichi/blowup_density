# C01 unit U6 — review

Reviewed commit `213aea6` on worktree `.claude/worktrees/044-C01-unit-u6`.
Scope: `formalization/NSFormalization/Section4/C01/Trilinear.lean`,
`research/C01/axioms_u6.lean`, `research/C01/ATTEMPTS_U6.md`.
Spec fields under review: `trilinearHolder`, `trilinearAbsorbed`,
`laplacianSqENorm` of `BlowupDensity.C01.Draft.EnergyAbsorptionAPI`
(`research/C01/Spec.lean:410-473`).

## Verdict

**ACCEPT-WITH-NOTES.**

The three theorems are the spec fields verbatim, they are discharged with no
extra hypotheses and no extra axioms, the mathematics is correct, and the
`ℝ≥0∞` statement is **not** vacuous: a consumer can extract a genuine real
inequality from it (verified by compiling a scratch consumer, §3.4 below).
The notes are all non-blocking and none of them requires a change to land this
unit.

## 1. Commands and results

All from the worktree, `LEAN_NUM_THREADS=6`, no `-j`, lake only from
`verification/`.

```
$ cd WT && bash scripts/lean-install.sh
... == OK                                            exit 0

$ cd WT/verification && lake build NSFormalization.Section4.C01.Trilinear
Build completed successfully (9354 jobs).           exit 0

$ cd WT/verification && lake build NSFormalization.Section4.C01.Trilinear 2>&1 | grep -i Trilinear
(no output)                                          -- no warning/info from the module

$ cd WT/verification && lake env lean ../formalization/NSFormalization/Section4/C01/Trilinear.lean
(no output)                                          exit 0
   -- fresh elaboration, not a cache replay: zero errors, zero linter warnings

$ cd WT/verification && lake env lean ../research/C01/axioms_u6.lean
'NSFormalization.Section4.C01.trilinearHolder'   depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.trilinearAbsorbed' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.laplacianSqENorm'  depends on axioms: [propext, Classical.choice, Quot.sound]
                                                     exit 0
   -- the three spec-typed `example`s elaborated (no errors reported)

$ grep -nE "sorry|admit|native_decide|axiom|maxHeartbeats" \
    formalization/NSFormalization/Section4/C01/Trilinear.lean research/C01/axioms_u6.lean
axioms_u6.lean:21,66,67,68   -- `#print axioms` lines and the docstring that names them
Trilinear.lean:38,40         -- docstring prose
   -- no `sorry`, no `admit`, no `native_decide`, no `axiom` declaration,
   -- no `maxHeartbeats`, and no `set_option` of any kind in the module

$ cd WT && make check
check_formalization_plan.py --check / check_contracts.py /
test_contract_policy.py (13 tests OK) / check_work_queue.py
"30 work items: ownership, contract registration and task cards consistent."
                                                     exit 0
```

## 2. Spec conformance

Diffed `research/C01/Spec.lean:191,202,212,410-473` against
`research/C01/axioms_u6.lean` line by line.

* `advectionWork`, `criticalL3`, `laplacianSq` are restated in `axioms_u6.lean`
  **character-for-character** as in `Spec.lean` (same binder, same type
  ascription, same `(inner ℝ (advection (lift z) 0 x) (laplacian z x) : ℝ)`),
  and against the same names: both files `open BlowupDensity.Contracts.V1
  (lift gradientTensor laplacian SmoothSquareIntegrableJets)` and
  `BlowupDensity.Contracts.V1.Data`, so `lift`, `laplacian`, `gradientTensor`,
  `SmoothSquareIntegrableJets`, `SpatialField`, `Space` are the contract's own
  objects, not local re-definitions. `slice` is not used by any of the three
  fields.
* The three `example` types are the three spec-field types verbatim, modulo the
  substitution `C₁ := BlowupDensity.Bindings.gradientL6.Csix` in
  `trilinearAbsorbed`.
* Each is discharged by `fun z hz => NSFormalization.Section4.C01.<thm> z hz` —
  a bare application, eta-expanded. No extra hypothesis, no side goal, no
  `simp`/`convert`, no `Nonempty`/`Classical.choice`-style escape. The bridge
  from the contract's vocabulary to the A05 objects is definitional (`rfl`),
  recorded at `verification/Bindings/GradientL6.lean:27-37`.
* `C₁` is the **registered** constant, not a fresh existential:
  `Contracts.V1.GradientL6API.Csix` is bound to
  `NSFormalization.Section4.A05.gradientL6Const` at
  `verification/Bindings/GradientL6.lean:43`, and the module proves
  `trilinearAbsorbed` with literally that `gradientL6Const`
  (`Trilinear.lean:216`), obtained from the registered clause
  `A05.eLpNorm_gradTensor_six_le`, which is what
  `GradientL6API.gradientLSix` is bound to (`Bindings/GradientL6.lean:46`).
  No new constant is introduced anywhere in the module.

## 3. Mathematics

### 3.1 `advection_norm_le` and the gradient norm

`Trilinear.lean:89-114` proves `‖(z·∇)z (x)‖ ≤ ‖z x‖ · ‖gradTensor z x‖`.

* `advection (lift z) 0 x = fderiv ℝ z x (z x)` by `rfl`; the vendor definition
  (`vendor/.../ProblemStatement.lean:63-64`) is
  `spatialDerivative u t x (u (t,x))`, so this is the convention `(z·∇)z`, i.e.
  `∑ⱼ zⱼ ∂ⱼz`. Correct.
* The norm on the right is `‖gradTensor z x‖` with
  `gradTensor v x = WithLp.toLp 2 (fun j => dirDeriv j v x)`
  (`A05/GradientL6.lean:44-45`), so `‖gradTensor z x‖ = (∑ⱼ ‖∂ⱼz(x)‖²)^{1/2}
  = (∑_{i,j} |∂ⱼz_i(x)|²)^{1/2}` — the **Frobenius** tensor norm of
  `01-introduction.tex:103`, not an operator norm. This is **the same object**,
  not merely the same norm, as the left-hand side of the registered `L⁶`
  clause (`A05/GradientL6.lean:63-65`: `eLpNorm (gradTensor v) 6 volume ≤
  ENNReal.ofReal gradientL6Const * eLpNorm (lap v) 2 volume`). No norm
  mismatch is possible.
* The proof is honest finite Cauchy–Schwarz: basis expansion of `z x`,
  `norm_sum_le`, `norm_smul`, then `Real.sum_mul_le_sqrt_mul_sqrt`, with the
  two `√(∑ ·²)` factors identified by `EuclideanSpace.norm_eq` and
  `PiLp.norm_eq_of_L2`. Correct.

### 3.2 Hölder exponents

`![(1:ℝ)/3, 1/6, 1/2]` with `1/3 + 1/6 + 1/2 = 1` (checked by `norm_num`; also
discharged inside the proof as the `∑ p i = 1` hypothesis of
`ENNReal.lintegral_prod_norm_pow_le`, whose signature is
`(∀ i ∈ s, AEMeasurable (f i) μ) → ∑ i ∈ s, p i = 1 → (∀ i ∈ s, 0 ≤ p i) → …`).
The three factors are matched to `‖z‖ₑ^3`, `‖∇z‖ₑ^6`, `‖Δz‖ₑ^2` and reassembled
into `eLpNorm z 3`, `eLpNorm (gradTensor z) 6`, `eLpNorm (lap z) 2` via
`eLpNorm_eq_lintegral_rpow_enorm_toReal` and `(a^k)^{1/k} = a`. Correct, and
the exponent triple is the paper's (`04-whole-space.tex:109-110`).

The hypothesis `hz : SmoothL2 z` is used in `trilinearHolder` **only** for
continuity ⟹ `AEMeasurable` of the three fields (lines 127-134). Nothing
stronger is smuggled in. In `laplacianSqENorm` it is used for
`MemLp (lap z) 2`, which is exactly what makes the equality true rather than
`⊤ = 0`.

### 3.3 The `ℝ≥0∞` statement is not vacuous

Three separate ways a bound like this could be empty, and where each stands:

1. **Empty hypothesis class** — no. `SmoothSquareIntegrableJets` is
   field-for-field the vendor's `SmoothL2Field`; every Schwartz field is in it,
   and `EnergyAbsorptionAPI.velocityJets` (`Spec.lean:295-299`) is what puts
   every velocity slice in it.
2. **Right-hand side always `⊤`** — no. On the class,
   `eLpNorm (lap z) 2 volume < ⊤` (`MemLp`, proved in-module at line 233) and
   `eLpNorm (gradTensor z) 6 volume ≤ ofReal C · ‖Δz‖₂ < ⊤` by the **registered**
   clause. The remaining factor `criticalL3 z = eLpNorm z 3 volume` is finite on
   the class mathematically (`L² ∩ L⁶ ⊂ L³`, and `H¹(R³) ↪ L⁶`), and every
   downstream field that consumes `trilinearAbsorbed` carries the hypothesis
   `ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤ ofReal (ν/4)`
   (`Spec.lean:514,536,580,602`), which forces it finite outright. So the RHS is
   a finite number in every use.
3. **Left-hand side fail-safe in the wrong direction** — this is the one real
   caveat, see Finding 1. `advectionWork z` is a Bochner integral, so if
   `x ↦ ⟨(z·∇)z(x), Δz(x)⟩` were not integrable, Mathlib's junk value makes
   `advectionWork z = 0`, the left side collapses to `0`, and the inequality
   holds trivially. The module proves the inequality unconditionally — the
   Mathlib step it rests on,
   `enorm_integral_le_lintegral_enorm : ‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ`, has **no**
   integrability hypothesis (verified by `#check`) — so nothing in these three
   fields certifies that `advectionWork z` is the true integral.

   This is not unsoundness: nothing false is proved, the bound is a correct
   statement about the term `advectionWork z` that every other field of the
   contract also uses, and on the hypothesis class the integrand **is**
   integrable (by the very Hölder bound this file proves). It is a strength
   gap, and it is the specification's own design: `Spec.lean:159-162` says the
   work integrals are "integrable" functions and assigns that duty to
   `velocityJets`. The practical consequence is that the burden of ruling out
   the junk value lands entirely on `enstrophyIdentity` (unit U7), which asserts
   an **equality** containing the same `advectionWork` and therefore cannot be
   proved at all unless the integral converges.

### 3.4 Consumer check (scratch, compiled then deleted)

To settle "can a consumer extract a real inequality", I compiled

```lean
theorem real_absorbed (z : SpatialField) (hz : SmoothSquareIntegrableJets z)
    (hfin : criticalL3 z ≠ ⊤) :
    |advectionWork z| ≤
      BlowupDensity.Bindings.gradientL6.Csix * (criticalL3 z).toReal * laplacianSq z
```

from `trilinearAbsorbed` + `laplacianSqENorm` + `gradientL6Const_pos` alone
(`ENNReal.ofReal_mul`, `ENNReal.ofReal_toReal hfin`,
`ENNReal.ofReal_le_ofReal_iff`). `lake env lean` on it: **exit 0, no errors**.
So the two trilinear fields plus the bridge do deliver the manuscript's
`|⟨(u·∇)u, Δu⟩| ≤ C₁‖u‖₃‖Δu‖₂²` as an inequality between real numbers, with the
registered constant, under exactly the finiteness the downstream smallness
hypothesis supplies. The scratch file lived in `/tmp/u6rev/` and has been
deleted; nothing was written into the worktree except this review.

### 3.5 `laplacianSqENorm`

`eLpNorm (lap z) 2 volume ^ (2:ℝ) = ENNReal.ofReal (laplacianSq z)` is proved by
squaring the in-tree `I02.eLpNorm_two_eq_ofReal_sqrt` with
`Real.sq_sqrt (integral_nonneg …)`, after establishing
`Integrable (fun x => ‖lap z x‖^2)` from `MemLp (lap z) 2`. It is an honest
equality (both sides are genuinely finite on the class, so neither side is a
junk value), and it is the field `Spec.lean:471-473` asks for. Correct.

## 4. Findings

**Finding 1 — minor, non-blocking. `trilinearHolder` / `trilinearAbsorbed`
(`Trilinear.lean:121`, `:214`): the statements do not certify that
`advectionWork z` is a convergent integral.**

*What.* The `ℝ≥0∞` route makes the inequality unconditional, which is elegant,
but it means the left-hand side is `ENNReal.ofReal |advectionWork z|` where
`advectionWork z` is Mathlib's Bochner integral — `0` by junk if the integrand
is not integrable. In that case the inequality is trivially true and says
nothing. Nothing false is proved and the three spec fields are discharged
exactly as written, so this is not a defect of the unit; it is a deferred
obligation that the specification itself parks on `velocityJets` /
`enstrophyIdentity` (`Spec.lean:159-162`). Note that the COMPARISON plan for U6
(`research/C01/COMPARISON.md:176`) called for `MemLp z 3` by interpolation,
i.e. a Bochner route that would have produced integrability as a by-product;
`ATTEMPTS_U6.md` records and justifies the deviation, but does not record that
this is what it costs.

*Fix (cheap, no new mathematics).* The proof already contains the missing
statement. Hoist the internal `hstep1`/`hHolder` chain (lines 154-208) into a
named lemma

```lean
theorem lintegral_advectionWork_enorm_le (z : SpatialField) (hz : SmoothL2 z) :
    ∫⁻ x, ‖(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)‖ₑ ∂volume ≤
      criticalL3 z * eLpNorm (gradTensor z) 6 volume * eLpNorm (lap z) 2 volume
```

and add the one-line corollary: when `criticalL3 z ≠ ⊤` the right side is
finite, continuity gives `AEStronglyMeasurable`, and
`hasFiniteIntegral_iff_enorm` then gives
`Integrable (fun x => ⟪(z·∇)z x, Δz x⟫_ℝ) volume`. That makes the left-hand
side demonstrably the true work integral and will very likely be needed by U7
anyway. Suggest booking it as a U7 prerequisite rather than reopening U6.

**Finding 2 — informational. `ATTEMPTS_U6.md`, the `Matrix.cons_val_two` note:
the snag is real and reproducible, but the attributed cause is slightly off.**

The note says `norm_num`'s default simp set reduces `![…] 0` and `![…] 1` but
not `![…] 2`, "`Matrix.cons_val_two` is `rfl` but not `@[simp]`". The behaviour
is exactly as described (see §5), but plain `simp` **does** reduce `![…] 2` on
this pin, so simp-tagging is not the discriminator — the blocker is specific to
`norm_num`. Harmless; worth a word if the note is ever reused as guidance.

**Finding 3 — informational. Module not yet imported by anything.**
`NSFormalization.Section4.C01.Trilinear` is imported by no other module and is
not in `formalization/NSFormalization.lean`. CI still compiles it: the
`lean-contracts` job runs `experiments/build_changed_lean.py --base-ref`, whose
`targets()` maps any changed `formalization/**.lean` to a lake target
(`.github/workflows/contracts.yml`, "Compile changed modules outside the
registered test closure"). The conformance file `research/C01/axioms_u6.lean` is
**not** compiled by CI (`research/` is skipped by `targets()`), same as the
existing `research/A02/axioms_u1a.lean`. No action; noted so nobody assumes the
axiom check is machine-enforced on every PR.

## 5. Honesty spot-check of `ATTEMPTS_U6.md`

Two recorded snags, re-run at this pin:

```
-- "Matrix.cons_val_two is not reduced by norm_num"
example : (![(1:ℝ)/3, 1/6, 1/2] 2) = 1/2 := by norm_num
  → error: unsolved goals  ⊢ ![1/3, 1/6, 1/2] 2 = 1/2                    REPRODUCED

example : ∑ i : Fin 3, (![(1:ℝ)/3, 1/6, 1/2] i) = 1 := by
  norm_num [Fin.sum_univ_three]
  → error: unsolved goals  ⊢ 1/2 + ![1/3, 1/6, 1/2] 2 = 1                REPRODUCED

example : ∑ i : Fin 3, (![(1:ℝ)/3, 1/6, 1/2] i) = 1 := by
  norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  → exit 0                          -- the file's verbatim tactic, line 201: works

-- caveat (Finding 2): plain simp DOES reduce index 2 on this pin
example : ∑ i : Fin 3, (![(1:ℝ)/3, 1/6, 1/2] i) = 1 := by simp [Fin.sum_univ_three]
  → error: unsolved goals  ⊢ 3⁻¹ + 6⁻¹ + 2⁻¹ = 1     -- matrix reduced, arithmetic left

-- "mul_le_mul_right'/mul_le_mul_left' not in scope for ℝ≥0∞"
example (a b c : ℝ≥0∞) (h : a ≤ b) : a * c ≤ b * c := mul_le_mul_right' h c
example (a b c : ℝ≥0∞) (h : a ≤ b) : c * a ≤ c * b := mul_le_mul_left' h c
  → error: Unknown identifier `mul_le_mul_right'`
  → error: Unknown identifier `mul_le_mul_left'`                          REPRODUCED
```

Both snags are accurate; `mul_le_mul'` (used at `Trilinear.lean:224`) is indeed
the available lemma. `ATTEMPTS_U6.md`'s "Commands" section reproduces exactly
(9354 jobs, three standard-axiom lines). No overstated claim found.
