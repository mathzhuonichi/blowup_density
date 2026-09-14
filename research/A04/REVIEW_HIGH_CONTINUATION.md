# Review — lane 135, A04 unit G2 (`regularizedNormDerivative`)

Reviewer run 2026-09-13 (Opus 5). Branch `erenup/135-A04-g2-highcontinuation`, one commit
`96432f2` on top of merge-base `554c5f2` with `origin/erenup/integration`.
Diff: 4 files, 359 insertions, **0 deletions** — nothing existing is touched.

Target: `paper/sections/appendix-a-local-theory.tex:139-145` (line numbers re-checked live,
not copied from an earlier review); spec field `research/A04/Spec.lean:459-470`
`regularizedNormDerivative`; `research/A04/COMPARISON.md` §4 unit **G2** (and the constant of
the §2 `Cgron` row).

## Verdict: **ACCEPT-WITH-NOTES**

The mathematics is right, the statement is token-identical to the spec, the constant is the
one Young's inequality gives (and is *sharp*), all four declarations carry only the three
standard axioms, and the theorem is non-vacuously instantiable. Six findings, none blocking:
two are honesty corrections to `ATTEMPTS_HIGH_CONTINUATION.md`, two are MAINT notes, two are
hand-off information for the next lane.

---

## 1. Compiles / axioms / hygiene — **PASS**

```
$ . scripts/lean-env.sh && cd verification
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.HighContinuation
Build completed successfully (9952 jobs).
EXIT=0
```
(the only warnings in the log are pre-existing vendor HeliCorgi linter warnings —
`R3DivergencePointwise.lean:25`, `R3LerayL2Operator.lean:34,61`, `R3LerayFourierBridge.lean:73`,
`R3LerayComplexFiberSymbol.lean:42` — none from the new module.)

```
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A04/HighContinuation.lean
EXIT=0        (0 bytes of output — silent)
```

```
$ LEAN_NUM_THREADS=6 lake env lean ../research/A04/axioms_high_continuation.lean
EXIT=0
'NSFormalization.Section4.A04.Cgron_pos'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.young_high_real'           depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.young_absorption_high'     depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.regularizedNormDerivative' depends on axioms: [propext, Classical.choice, Quot.sound]
```
The conformance `example` in that file elaborates (it is the last declaration; the file exits 0).

```
$ make check
EXIT=0    ... Ran 13 tests ... OK
          30 work items: ownership, contract registration and task cards consistent.
$ make test
EXIT=0    ... every registered contract "checked; standard logical axioms only"
```
(`make test` was run even though no contract is registered for this module, to confirm the new
`def Cgron` in the `NSFormalization.Section4.A04` namespace breaks nothing downstream. It does not.)

Hygiene grep over both new Lean files:
```
$ grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/A04/HighContinuation.lean \
    research/A04/axioms_high_continuation.lean
research/A04/axioms_high_continuation.lean:11:`research/A04/axioms_energy_identity_high.lean`): its type is the spec field
research/A04/axioms_high_continuation.lean:30:#print axioms Cgron_pos
research/A04/axioms_high_continuation.lean:31:#print axioms young_high_real
research/A04/axioms_high_continuation.lean:32:#print axioms young_absorption_high
research/A04/axioms_high_continuation.lean:33:#print axioms regularizedNormDerivative
```
Only the intended `#print axioms` lines and one prose hit. No `sorry`, no `admit`, no `axiom`,
no `native_decide`, no `set_option`, no heartbeat bump. `git status --short` in the worktree is
empty.

## 2. Statement fidelity — **PASS**

### (a) Machine token-diff against the spec field

`research/A04/Spec.lean:460-470` vs `HighContinuation.lean:137-147`, tokenized
(identifiers/numerals/punctuation) and `difflib`-diffed:

```
spec tokens 148 module tokens 151
--- +++
@@ -148 +148,4 @@
 t
+:
+=
+by
```

**148 of 148 spec tokens identical, in order.** The only difference is the module's trailing
`:= by` (the proof). Not even a namespace qualifier differs — both sides write the bare
`sobolevNormAt`, `Cgron`, `Real.sqrt`, `HasDerivAt`, `Ioo`, and the module's `open` block
(`Set`; `A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)`;
`D01 (MemForceR)`) supplies exactly the names the spec writes unqualified.

The spec field's own line citation in the module docstring (`Spec.lean:459-470`) and the
manuscript citation (`appendix-a-local-theory.tex:139-145`) were both re-opened live and are
correct (`:142` is `\begin{equation}\label{eq:highcontinuation}`, `:144` the display,
`:140` "Young's inequality and division by the regularized norm").

Shapes against the spec structure: `Cgron : ℕ → ℝ → ℝ` (`Spec.lean:354`) — module
`def Cgron (m : ℕ) (ν : ℝ) : ℝ`, same. `Cgron_pos : ∀ (m : ℕ) (ν : ℝ), 0 < ν → 0 < Cgron m ν`
(`Spec.lean:356`) — module identical, verbatim.

### (b) Against the manuscript, and the arithmetic of the constant

The manuscript sentence is `:140-141` "Young's inequality and division by the regularized norm
`(‖u‖²_{H^m}+ζ²)^{1/2}`, followed by `ζ↓0`, imply eq:highcontinuation". The module states the
**pre-limit** form, which is what the spec docstring (`Spec.lean:436-458`) describes as "the
statement at each fixed `ζ > 0` ... the only form in which the manuscript's sentence is a
theorem about a differentiable function". The module's statement is exactly that: the RHS
carries `√(‖u‖²+ζ²)` where the manuscript's post-limit display carries `‖u‖_{H^m}`. Since
`‖u‖_{H^m} ≤ √(‖u‖²+ζ²)`, the fixed-`ζ` form is **weaker** than eq:highcontinuation and
becomes it in the limit — the honest intermediate, not a disguised strengthening. Correct.

**The constant.** eq:Rhigh's cross term is `C_m a n g` with `a = ‖u‖_{H²}`, `n = ‖u‖_{H^m}`,
`g = ‖∇u‖_{H^m}`. Young at weight `ν`: `C_m a n g ≤ ν g² + (C_m a n)²/(4ν)`, so
`½ d ≤ (C_m²/(4ν)) a² n² + F n` and `C_{m,ν} = C_m²/(4ν)`. This is what `Cgron` is, and it
matches `COMPARISON.md` §1 ("Carrying out (2) explicitly gives `C_{m,ν} = (C_m)²/(4ν)`") and
the §2 `Cgron` row ("gap, but trivial: it is `(Chigh m)²/(4ν)` once (2) is done").

The certificate in the proof is the perfect square: `νg² + (C²/4ν)a²n² − Can·g = (2νg − Can)²/(4ν) ≥ 0`
(`HighContinuation.lean:93-99`, `field_simp; ring` then `div_nonneg (sq_nonneg _)`). No sign slip.

Concrete probe (`/tmp/rev135/p1_arith.lean`), the brief's numbers `ν = 1, C = 2, a = n = g = 1`:

```lean
theorem probe_concrete (d F : ℝ) (h : (1/2)*d + (1:ℝ)*1^2 ≤ 2*1*1*1 + F*1) :
    (1/2)*d ≤ (2:ℝ)^2/(4*1)*1^2*1^2 + F*1 :=
  young_high_real (ν := 1) (C := 2) (a := 1) (n := 1) (g := 1) one_pos h
example : (2:ℝ)^2/(4*1)*1^2*1^2 = 1 := by norm_num
```
i.e. hypothesis `½d + 1 ≤ 2 + F` gives conclusion `½d ≤ 1 + F` — **consistent with the brief**.

And the constant is **sharp**, so it cannot be an off-by-a-factor:
```lean
theorem young_constant_cannot_be_halved :
    ¬ (∀ (d g a n F ν C : ℝ), 0 < ν →
        ((1/2)*d + ν*g^2 ≤ C*a*n*g + F*n) → (1/2)*d ≤ C^2/(8*ν)*a^2*n^2 + F*n) := by
  intro H; have := H 2 1 1 1 0 1 2 one_pos (by norm_num); norm_num at this
```
(counterexample `d = 2, F = 0` at the equality point `2νg = Can`.)
```
$ lake env lean /tmp/rev135/p1_arith.lean
EXIT=0
'Rev135.probe_concrete'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev135.young_constant_cannot_be_halved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Directions of the two `ζ` inequalities.** Both live in `regularized_sqrt_bound`
(`Regularized.lean:65-79`, unit Z1, already reviewed) and are used the right way round:
`h2 : b·√E ≤ b·√(E+ζ²)` (from `Real.sqrt_le_sqrt`, i.e. `n ≤ √(n²+ζ²)`, applied to the
**forcing** term so it loses its `‖u‖_{H^m}` factor) and `hKz : 0 ≤ K·ζ²` together with
`hKS2 : K·√(E+ζ²)² = K·(E+ζ²)` (i.e. `E/√(E+ζ²) ≤ √(E+ζ²)`, applied to the **coefficient**
term). After `div_le_iff₀` the goal is `d ≤ 2K(E+ζ²) + 2b√(E+ζ²)` and the hypothesis is
`d ≤ 2(KE + b√E)` — the two inequalities bridge exactly that gap, in the weakening direction.

The one rewrite inside this lane, `rw [Real.sqrt_sq hnnn]` (`HighContinuation.lean:164`), is
also in the right direction: the goal at that point contains `√(n²)` and it is rewritten to
`n`, matching `young_absorption_high`'s output `½d₀ ≤ Cgron·a²·n² + F·n` for `linarith`.
`hnnn : 0 ≤ sobolevNormAt m w.velocity t` is `ENNReal.toReal_nonneg` (the norm is a `.toReal`),
so the side condition is discharged, not assumed.

### (c) Load-bearing hypotheses

All three probes use the module's own proof text, with `set_option autoImplicit false`
(the `formalization/` package has `autoImplicit` on; see `logs/LESSONS.md` 2026-09-14).

| hypothesis | test | result |
|---|---|---|
| `a ∈ initialClassR` | `/tmp/rev135/p3_no_ha.lean`: restate without it, proof routed through `energyIdentityHigh_core` (which also lacks it) | **compiles, EXIT=0**, `[propext, Classical.choice, Quot.sound]` — the hypothesis is genuinely unused, exactly as `ATTEMPTS_HIGH_CONTINUATION.md` claims. It is kept for spec fidelity, which is right. |
| `3 ≤ m` → `2 ≤ m` | `/tmp/rev135/p4_weak_m.lean` | **FAILS as expected** |
| `0 < ν` → `0 ≤ ν` | `/tmp/rev135/p5_weak_nu.lean` | **FAILS as expected** |

```
$ lake env lean /tmp/rev135/p4_weak_m.lean
EXIT=1
/tmp/rev135/p4_weak_m.lean:26:69: error: Application type mismatch: The argument
  hm
has type
  2 ≤ m
but is expected to have type
  3 ≤ m
in the application
  @energyIdentityHigh_core ν a f T hν hf w hpath m hm

$ lake env lean /tmp/rev135/p5_weak_nu.lean
EXIT=1
/tmp/rev135/p5_weak_nu.lean:26:53: error: Application type mismatch: The argument
  hν
has type
  0 ≤ ν
but is expected to have type
  0 < ν
in the application
  energyIdentityHigh_core hν
```

On `0 ≤ ν`: the first failure is at `energyIdentityHigh_core`, before `Cgron` is reached, but
the brief's reasoning holds downstream too — `Cgron_pos` and `young_absorption_high` both take
`0 < ν` explicitly, and at `ν = 0` Lean's division junk makes `Cgron m 0 = 0`
(`/tmp/rev135/p7_dup.lean`, `example (m : ℕ) : Cgron m 0 = 0 := by simp [Cgron]`, accepted),
so the `0 ≤ ν` statement would assert the strictly stronger and false
`(√(E+ζ²))' ≤ ‖f‖_{H^m}`. Both weakenings are correctly refused.

### (d) Non-vacuity — **PASS**, and stronger than asked

`/tmp/rev135/p2_vacuity.lean` rebuilds `zeroSol` (`research/A04/REVIEW_ENERGY_HIGH.md`
appendix / `research/D01/REVIEW_SL8_ASSEMBLY.md` App. A) in this import closure and instantiates
**the reviewed theorem itself** at `ν = 1, T = 1, m = 3, t = 1/2, ζ = 1/3`:

```lean
theorem g2_on_zeroSol : ∃ d : ℝ, HasDerivAt (fun r => √(sobolevNormAt 3 (zeroSol 1).velocity r ^2 + (1/3)^2)) d (1/2) ∧ … :=
  regularizedNormDerivative 1 0 0 1 one_pos zero_mem_initialClassR memForceR_zero (zeroSol 1)
    (path_zero 1) 3 le_rfl (1/2) (by constructor <;> norm_num) (1/3) (by norm_num)

theorem d_forced_zero  … : d = 0                        -- by HasDerivAt.unique
theorem zeroSol_display … = 0                            -- the RHS degenerates to 0
theorem exists_d_is_deriv … : deriv (fun r => √(… + ζ^2)) t ≤ RHS   -- the ∃ is not an escape hatch
```
```
$ lake env lean /tmp/rev135/p2_vacuity.lean
EXIT=0
'Rev135V.g2_on_zeroSol'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev135V.d_forced_zero'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev135V.zeroSol_display'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev135V.exists_d_is_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

So (i) the whole hypothesis package — including `0 < ζ` and `HasSmoothSobolevPath` — is
inhabited; (ii) on the zero solution `d` is **forced** to `0` by `HasDerivAt.unique` against
the constant path `r ↦ √(0+ζ²)`, and the display degenerates correctly to `0 ≤ 0`.

**Is the inequality trivially true elsewhere?** No, for two independent reasons.

* The `∃ d` is not a free choice. `HasDerivAt` determines `d` uniquely, and `exists_d_is_deriv`
  above turns the field into the quantifier-free `deriv (fun r => √(‖u(r)‖²+ζ²)) t ≤ RHS` on
  the *general* hypotheses (not just on `zeroSol`). An implementation cannot satisfy the field
  by picking a convenient `d`.
* With `f = 0` and `ζ` small the bound reads `(√(E+ζ²))' ≤ C_{m,ν}‖u‖²_{H²}·√(E+ζ²)`, a genuine
  homogeneous linear differential inequality with **no slack**: as `ζ↓0` the RHS tends to
  `C_{m,ν}‖u‖²_{H²}‖u‖_{H^m}` and the left side to the Dini derivative of `‖u‖_{H^m}`. It is
  exactly the inequality that Grönwall consumes in move (4); it is false for a field whose
  `H^m` norm grows faster than `exp(C∫‖u‖²_{H²})`.
* The `.toReal` vacuity risk (a `⊤` norm reading as `0`) was already closed by the G1 review
  (`REVIEW_ENERGY_HIGH.md` §2(d), `sobolevENorm_velocity_ne_top` / `_force_ne_top` /
  `gradientSobolevENorm_velocity_ne_top`); this lane inherits it and adds no new `.toReal` slot.
* Unchanged caveat inherited from G1: no **nonzero** classical solution exists in tree yet
  (that is A01's job), so `zeroSol` is still the only available inhabitant.

## 3. Consistency with the tree — **PASS**, findings 3-4

* **Imports.** Exactly two, both consumed: `A04.EnergyIdentityHigh` (for `energyIdentityHigh`,
  `Chigh`, `Chigh_pos`, `sobolevNormAt`, `HasSmoothSobolevPath`) and `A04.Regularized` (for
  `regularized_sqrt_bound`). No `Mathlib` import added; nothing superfluous.
* **No restated definitions.** The module adds exactly one new `def`, `Cgron`, which has no
  in-tree predecessor: `grep -rn "Cgron" formalization/ verification/ --include='*.lean'` finds
  only this module (plus the local binders of finding 4) and
  `grep -rn "4 \* ν\|4\*ν"` over `Section4/` finds only this module. Not a duplicate.
* **Is `young_high_real` a Mathlib duplicate?** No. `/tmp/rev135/p7_dup.lean` checks the three
  nearest Mathlib forms and all are unweighted or conjugate-exponent:
  `two_mul_le_add_sq : 2*a*b ≤ a^2 + b^2`, `four_mul_le_sq_add : 4*a*b ≤ (a+b)^2`,
  `Real.young_inequality : a*b ≤ |a|^p/p + |b|^q/q` (Hölder conjugates). None is the
  `ε`-weighted `y·g ≤ ν g² + y²/(4ν)` that the absorption needs; getting there from
  `two_mul_le_add_sq` requires the same rescaling the lane does explicitly. A naive
  `nlinarith [sq_nonneg (2*ν*g − y), hν]` on the *divided* form fails
  (`linarith failed to find a contradiction`) — which independently justifies the lane's
  `field_simp`-then-`ring` perfect-square route recorded in ATTEMPTS.
* **Is it a tree duplicate?** No. `Paper1.critical_energy_absorption`
  (`Paper1/ScalarEnergy.lean:68`) and `Paper1.absorbed_energy_inequality`
  (`Paper1/ScalarEnergyAuxiliary.lean:12`) — named by `COMPARISON.md` §4 as the G2 template —
  are a *smallness-based* absorption (`C·y ≤ ν/2` as a hypothesis), not Young's AM-GM. They are
  the critical-order step of C01/R43, a different lemma. `A01/Propagation.lean:34` describes
  this Young step in prose but proves no lemma for it.
* **`COMPARISON.md` §4 booking.** G2 is booked as size **S**, "arithmetic once G1 and Z1 exist",
  depends on G1 + Z1 — which is exactly what landed. `Cgron`'s value matches §1/§2 verbatim.
  One deviation from the Z1 booking, see finding 3.

### Finding 3 (low, MAINT note) — two Z1 lemmas are now dead code

`COMPARISON.md` §4 books Z1 as delivering the *derivative* form
`(d/dt)√(E+ζ²) ≤ K√(E+ζ²) + b`. This lane deliberately consumes only the inequality half
`regularized_sqrt_bound`. A tree-wide grep shows the derivative halves now have **zero**
consumers:

```
$ grep -rn "regularized_sqrt_hasDerivWithinAt\|regularized_sqrt_deriv" formalization/ research/ verification/ --include='*.lean'
formalization/.../HighContinuation.lean:44,45   (docstring only)
research/A04/axioms_z1.lean:6,7                 (axiom audit only)
```
and `sqrt_le_primitive_linear`, the other Z1 export, does **not** call them either — it inlines
`((hdE x hx).add_const (δ^2)).sqrt hpos.ne'` at `Regularized.lean:172-174`.

Not a defect of this lane (the lane's choice is forced by the spec's two-sided `HasDerivAt`),
and I do **not** recommend deleting them: they are the literal Z1 deliverable of the
`COMPARISON.md` booking and the `02-preliminaries.tex:152` / `04-whole-space.tex:103,121`
reuse sites named there have not been built yet. **Record on the MAINT list** and revisit once
C01/I01 have taken their `ζ` steps; if those also go two-sided, drop both.

### Finding 4 (low, MAINT note) — `Cgron` is shadowed by two local binders in its own namespace

`def Cgron` now lives in `NSFormalization.Section4.A04`, where two existing declarations bind
a *local* `Cgron` of a different type:

* `Gronwall.lean:202` `theorem gronwall_integral_mul {t₀ t₁ Cgron : ℝ} …`
* `Continuity.lean:132` `theorem intervalIntegrable_highContinuationIntegrand … (Cgron : ℕ → ℝ → ℝ) …`

Everything compiles (locals shadow, and `make test` is green), but a future lane writing
`Cgron m ν` *inside* those declarations gets the binder, not the def — the same class of trap
as the `open`-shadowing lesson of 2026-09-14. Concretely the next lane **must pass `A04.Cgron`
explicitly** when applying `intervalIntegrable_highContinuationIntegrand`. Rename the binders
(`Cg`, `Ccoef`) in a MAINT pass; do not touch them in this lane.

## 4. Honesty of `ATTEMPTS_HIGH_CONTINUATION.md` — **PASS with two corrections**

Everything checkable was reproduced: the four axiom lines, the `2.8 s` build with no heartbeat
bump, the `make check` exit 0, the load-bearing table (§2(c) above), the route (steps 1-4 match
the proof text line for line).

### Finding 1 (note) — the recorded `HasDerivAt.add_const` diagnosis is wrong

ATTEMPTS records: "`HasDerivAt.add_const` reported `Unknown constant` under a minimal
`import Mathlib.Analysis.SpecialFunctions.Sqrt` probe; it needs
`Mathlib.Analysis.Calculus.Deriv.Add` (pulled in transitively …)".

The *symptom* reproduces verbatim:
```
$ cat /tmp/rev135/p9_min2.lean
import Mathlib.Analysis.SpecialFunctions.Sqrt
#check @HasDerivAt.add_const
$ lake env lean /tmp/rev135/p9_min2.lean
EXIT=1
/tmp/rev135/p9_min2.lean:2:8: error(lean.unknownIdentifier): Unknown constant `HasDerivAt.add_const`
```
but the *diagnosis* is not the cause. Under **the same minimal import**, the term-level use
compiles:
```
$ cat /tmp/rev135/p8_minimal.lean
import Mathlib.Analysis.SpecialFunctions.Sqrt
example (E : ℝ → ℝ) (E' t ζ : ℝ) (h : HasDerivAt E E' t) :
    HasDerivAt (fun r => E r + ζ ^ 2) E' t := h.add_const (ζ ^ 2)
$ lake env lean /tmp/rev135/p8_minimal.lean
EXIT=0
```
The real reason is that there is no constant of that name at all — generalized dot notation
unfolds `HasDerivAt` and resolves `h.add_const` to **`HasFDerivAtFilter.add_const`**:
```
$ lake env lean /tmp/rev135/p11_name.lean      # set_option pp.fullNames true in #print foo
theorem foo : ∀ (E : ℝ → ℝ) (E' t ζ : ℝ), HasDerivAt E E' t → HasDerivAt (fun r => E r + ζ^2) E' t :=
fun E E' t ζ h => HasFDerivAtFilter.add_const (ζ ^ 2) h
```
No action on the module (the real module imports everything anyway and is correct); the
ATTEMPTS sentence should be corrected so the next lane does not chase a phantom import. This is
also an instance of the standing lesson "`#check`, not `grep`, decides existence" — here even
`#check` on the guessed name is misleading, because dot notation resolves through the unfolding.

### Finding 2 (note) — "a `HasDerivWithinAt` cannot be upgraded to `HasDerivAt`" is too strong

The route exists and is two lines:
```lean
theorem two_sided_of_one_sided {f : ℝ → ℝ} {d t : ℝ}
    (hr : HasDerivWithinAt f d (Ici t) t) (hl : HasDerivWithinAt f d (Iic t) t) :
    HasDerivAt f d t := by
  have h := hl.union hr
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h
```
```
$ lake env lean /tmp/rev135/p6_misc.lean
'Rev135M.two_sided_of_one_sided' depends on axioms: [propext, Classical.choice, Quot.sound]
```
What is true — and is what the lane actually relied on — is that a **single** one-sided
derivative cannot be upgraded, and `Regularized.lean` exposes only the `Ici` half
(`regularized_sqrt_hasDerivWithinAt`), so routing through it would have required inventing an
`Iic` twin for no gain when `energyIdentityHigh` already hands over a two-sided `HasDerivAt`.
**The lane's decision is correct**; only the blanket phrasing in ATTEMPTS and in the module
docstring (`HighContinuation.lean:44-45`, "cannot be upgraded") should be softened to "cannot be
upgraded from the `Ici` half alone". Statement-free, so no re-review needed if fixed.

---

## 5. For the lead — what the next unit needs, and the contract question

### Naming: there is a `G3` collision

`COMPARISON.md` §4's unit **G3** is the *variable-coefficient Grönwall*, and it is **already
done and in tree**: `formalization/NSFormalization/Section4/A04/Gronwall.lean` (lane 041) with
`gronwall_integral:70`, `gronwall_deriv:172`, `gronwall_integral_mul:202`, logged in
`research/A04/ATTEMPTS_G3.md` / `REVIEW_G3.md` / `axioms_g3.lean`. The unit the brief calls
"G3 = `highContinuationIntegral`" is a **different** step — the `ζ↓0` integral field at
`Spec.lean:471-494`, which sits between §4's G2 and G3 and consumes Z1's integral form, not the
Grönwall. Suggest calling it **G2b** (or "Z1↓0") in the next brief to stop the collision
propagating the way the paper line numbers did in lesson 117.

### What `highContinuationIntegral` needs

From **this module**:
* `Cgron` — it appears literally in the field statement (`Spec.lean:475`, `:487`). Nothing else
  from this module is *statement*-level.
* `young_absorption_high` — needed in the proof, to produce `sqrt_le_primitive_linear`'s
  `hineq`. But the exact hypothesis that lemma wants is the **absorbed squared-norm bound**,
  and that is currently *inline* at `HighContinuation.lean:159-165` inside
  `regularizedNormDerivative`'s proof. **Recommendation:** hoist those seven lines into a named
  lemma in this module (or, cheaper, let the next lane add it there), shape:
  ```lean
  theorem sq_deriv_absorbed_bound (… energyIdentityHigh's hypotheses …) (t ∈ Ioo 0 T) :
      deriv (fun r => sobolevNormAt (m:ℝ) w.velocity r ^ 2) t ≤
        2 * (Cgron m ν * sobolevNormAt 2 w.velocity t ^ 2 * sobolevNormAt (m:ℝ) w.velocity t ^ 2
             + sobolevNormAt (m:ℝ) f t * Real.sqrt (sobolevNormAt (m:ℝ) w.velocity t ^ 2))
  ```
  The `∃ d → deriv` conversion is one `HasDerivAt.deriv` (pattern proved in
  `/tmp/rev135/p2_vacuity.lean`'s `exists_d_is_deriv`).
* `regularizedNormDerivative` itself is **not** consumed by G2b. `sqrt_le_primitive_linear`
  takes the *squared-norm* derivative and re-does its own `δ`-regularization internally
  (`Regularized.lean:161-208`). So the G2 field is, for the tree, an endpoint — it exists
  because the spec asks for it, not because the next unit needs it. Worth knowing before the
  contract decision below.

From **`Regularized.lean`**, exactly two lemmas, both by name:
* `sqrt_le_primitive_linear` (`Regularized.lean:134`) — gives
  `√(E t) ≤ √(E t₀) + ∫_{t₀}^t (K√E + b)`; with `E = ‖u‖²_{H^m}` (so `√E = ‖u‖_{H^m}` by
  `Real.sqrt_sq`), `K = fun s => Cgron m ν * ‖u(s)‖²_{H²}`, `b = fun s => ‖f(s)‖_{H^m}` it is
  **exactly** the field's second conjunct. Its `ContinuousOn (Icc t₀ t₁)` hypotheses for
  `E, K, b` are all available: `continuousOn_sobolevNormAt_velocity` (`Continuity.lean:105`)
  and `continuousOn_sobolevNormAt_force` (`:114`), mono'd along `Icc t₀ t ⊆ Ico 0 T`.
* `primitive_integrand_intervalIntegrable` (`Regularized.lean:115`) — needed *internally* by
  the above. For the field's **first conjunct** the better lemma already exists and is stated in
  the spec's own spelling, `Cgron` parameter and all:
  **`A04.intervalIntegrable_highContinuationIntegrand` (`Continuity.lean:132`)**. So the
  `IntervalIntegrable` half of `highContinuationIntegral` is **free** — one application (with
  `A04.Cgron` passed explicitly, finding 4).

**Size: S**, not M. Every analytic ingredient is proved; the work is bookkeeping — hoist the
absorbed bound, `∃ d → deriv`, plumb three `ContinuousOn`s and two nonnegativity families,
and two `Real.sqrt_sq` rewrites to land on the spec's spelling. The one place to watch is the
`t₀ = 0` endpoint: `energyIdentityHigh` gives derivatives only on `Ioo 0 T`, and
`sqrt_le_primitive_linear` needs them only on `Ioo t₀ t` ⊆ `Ioo 0 T`, with continuity on the
closed `Icc t₀ t ⊆ Ico 0 T` — so the field's `0 ≤ t₀` is exactly right and no one-sided
derivative at `0` is needed. (This is also why `Ico 0 T` appears in `HasSmoothSobolevPath`.)

### Should the A04 contract register `regularizedNormDerivative` + `Cgron` now?

First, a correction to the premise: **there is no A04 contract at any version.**
`verification/contracts.json` has 22 ids and none is `A04.*`; `verification/Contracts/V1/` has
no `Continuation.lean`. So the question is when to open **A04 V1**, not V2.

**Recommendation: wait for `highContinuationIntegral`, then register one batch.** Reasons:

1. `regularizedNormDerivative` is an *intermediate* with no in-tree consumer (see above). Its
   only consumer is the next field. Freezing its spelling one lane before its only consumer is
   written is the classic way to buy a V2 — and `Contracts/V1/*` is frozen by CI, so a V2 is
   the only repair.
2. The natural V1 batch is the three differential fields + their two constants:
   `Chigh`, `Chigh_pos` (G1, lane 128, already contract-ready per `G1_SPLIT.md`), `Cgron`,
   `Cgron_pos`, `energyIdentityHigh`, `regularizedNormDerivative`, `highContinuationIntegral`.
   That is a coherent "differential-side partial API", the same shape as
   `C01.energy_absorption_partial` and `B02.homogeneous_partial`. One contract lane, one
   review, instead of two.
3. Contract shape is already settled and does **not** depend on G2b: carry `Cgron` as the
   spec's **opaque** `ℕ → ℝ → ℝ` field plus `Cgron_pos`, and let the *binding* supply
   `A04.Cgron = Chigh m ^ 2 / (4*ν)`. Registering the concrete value as the contract would
   over-specify against `Spec.lean:350-353` ("the manuscript displays no formula, so none is
   pinned here"). `ATTEMPTS_HIGH_CONTINUATION.md`'s own note agrees and correctly says no `rfl`
   bridge is owed (`A04.Cgron` is a fresh `def`, no upstream original).
4. Counter-argument, for the record: `A01/Propagation.lean` (already merged) is written against
   this machinery and its docstring already names `A04.sqrt_le_primitive_linear` and a `Cgron`
   scalar. If A01's lane needs an *importable* contract before A04's differential side is
   finished, registering a two-field `A04.constants` (`Chigh`/`Chigh_pos`/`Cgron`/`Cgron_pos`)
   early would be cheap and is unlikely ever to need a V2. That is the only early registration
   I would support.

---

## Appendix — probe inventory (`/tmp/rev135/`, volatile; error text quoted above)

| file | purpose | exit |
|---|---|---|
| `build_main.log`, `lean_main.log`, `conf.log`, `makecheck.log`, `maketest.log` | check 1 | 0 / 0 / 0 / 0 / 0 |
| `spec_field.txt`, `mod_field.txt` | token diff inputs, check 2(a) | — |
| `p1_arith.lean` | concrete Young instance + sharpness of `C²/(4ν)` | 0 |
| `p2_vacuity.lean` | `zeroSol` instantiation, `d` forced to 0, `∃ d` = `deriv` | 0 |
| `p3_no_ha.lean` | positive control: core without `a ∈ initialClassR` | 0 |
| `p4_weak_m.lean` | negative: `2 ≤ m` | 1 (quoted) |
| `p5_weak_nu.lean` | negative: `0 ≤ ν` | 1 (quoted) |
| `p6_misc.lean` | `Ici`+`Iic` → `HasDerivAt` upgrade exists | 0 for the theorem |
| `p7_dup.lean` | `Cgron m 0 = 0`; Mathlib AM-GM candidates | — |
| `p8_minimal.lean`, `p9_min2.lean`, `p11_name.lean` | finding 1 | 0 / 1 / 0 |
