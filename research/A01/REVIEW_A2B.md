# Review — lane 126-A01-a2b-continuation (A01 unit A2b: forced continuation from an a-priori bound)

Reviewer run: 2026-09-13, worktree `.claude/worktrees/126-A01-a2b-continuation`,
branch `erenup/126-A01-a2b-continuation`, one commit `cab6178` on top of merge-base
`3d56e21`.  Probes in `/tmp/rev126/` — per `logs/LESSONS.md` `/tmp` paths are volatile,
so every result that matters is pasted verbatim below, including the full source of the
two probes that decide finding **F6**.

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean is correct and clean: five theorems, `Build completed successfully (3941 jobs)`,
`lake env lean` silent, all five `#print axioms` = `[propext, Classical.choice, Quot.sound]`,
`make check` and `make test` green, no forbidden tokens.  `forced_global_mild_of_bound` is
**byte-identical** to the statement lane 122's review asked for (machine diff, exit 0), and
`forced_global_of_bound`'s conclusion is `exists_local`'s conclusion clause for clause with
`T := S` and the norm bound generalised to a free `R` — nothing is hidden, nothing is dropped.
The engineering judgement (expose the invariance clause rather than drop the invariance and
descent clauses) is the right one for A3's consumer.

But the **recorded GAP is materially overstated**, and both of its stated blockers fail under
test (**F6**, HIGH, plan-changing):

* the *resource* blocker is wrong twice — the template needs `maxHeartbeats 300000`, not
  800000, and `set_option maxHeartbeats` is **not forbidden** in this repo (ten merged modules
  use it, including the very file the lane cites);
* the *mathematical* blocker is wrong — angle invariance does **not** need a global mild
  uniqueness.  `exists_global_mild_of_bound` is built by iterating windows whose length is
  chosen precisely so that `kernelMass · L < 1` holds, i.e. **the continuation's own windows
  are the uniqueness regime**.  I proved the per-window invariance unconditionally, twice,
  standard axioms, in ~5 s each (§F6b, full source below).

The missing piece is therefore not "build a Grönwall mild uniqueness (an L campaign)" but
"fork the 45-line continuation induction so it carries the invariance clause" — an **M**.
Also: the committed failure probe does not parse at all (**F6a**), `hinv` is stated one
premise too strong (**F4**, free to fix), three prose pointers are dead or wrong (**F7**),
and `research/A01/A01_SPLIT.md` conflicts with integration (**F8**, for the lead at merge).

None of this makes any committed Lean wrong.  The fixes are: one `hinv` premise, the
`A01_SPLIT.md` A2b cell, three pointers, and the ATTEMPTS gap section.

---

## 1. Commands run and their results

```
$ . scripts/lean-env.sh ; cd verification
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Source.OrdinaryForcedLocal \
      Euler.BoundedMildContinuation Euler.CorrectionContinuation
Build completed successfully (3940 jobs).

$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.Continuation
Build completed successfully (3941 jobs).

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/Continuation.lean
(silent; exit 0; output file 0 bytes)

$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_a2b.lean        # exit 0
'NSFormalization.Section4.A01.forced_global_mild_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forced_mild_divergenceFree'  depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forced_ordinary_descent'     depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forced_global_of_bound'      depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forced_uniform_restart_time' depends on axioms: [propext, Classical.choice, Quot.sound]

$ make check
python3 experiments/test_contract_policy.py  -> Ran 13 tests ... OK
python3 experiments/check_work_queue.py      -> 30 work items: ownership, contract registration
                                                and task cards consistent.

$ make test                                                              # exit 0
... ℹ [10123/10123] Replayed Tests.DatumLemmasV3
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked;
      standard logical axioms only
(22 contracts, all "checked; standard logical axioms only"; 0 lines matching `error:`)

$ grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/A01/Continuation.lean research/A01/axioms_a2b.lean
research/A01/axioms_a2b.lean:3:  (docstring word "axioms")
research/A01/axioms_a2b.lean:9..13: the five `#print axioms` lines
(no hits at all in the .lean module)
```

Also built for the probes below: `Euler.SmoothL2Series`, `Euler.OrdinaryCauchyInterpolation`
(4682 jobs cumulative).

---

## 2. Findings

### F1 — Compiles, axioms, hygiene. Severity: none (pass)

As above.  Two notes for the lead, neither blocking:

* `Continuation.lean` is imported by **nothing** in `Contracts/`, `Bindings/` or `Tests/` —
  only by `research/A01/axioms_a2b.lean`.  So `make test`'s closure does not compile it and
  the module is **not CI-covered** until something consumes it.  Identical to the note in
  `REVIEW_A3.md` F1 about `Propagation.lean`; two A01 modules now sit outside the gate.
* the `local instance : Fact (0 < (1 : ℝ))` at `Continuation.lean:74` duplicates the one in
  `Source/OrdinaryForcedLocal.lean:15`; it is `local` in both, so harmless.

### F2 — `forced_global_mild_of_bound` is verbatim the requested statement. Severity: none (pass)

Machine diff against `git show origin/erenup/integration:research/A01/REVIEW_A3.md` §3, the
theorem block including the one-line proof term:

```
$ git show origin/erenup/integration:research/A01/REVIEW_A3.md \
    | awk '/^theorem forced_global_mild_of_bound/,/hbound$/' > /tmp/rev126/review_stmt.txt
$ sed -n '81,98p' formalization/NSFormalization/Section4/A01/Continuation.lean > /tmp/rev126/lane_stmt.txt
$ diff -u /tmp/rev126/review_stmt.txt /tmp/rev126/lane_stmt.txt ; echo $?
0
```

Character for character.  Elaborated form (`#check` with `pp.fullNames`) matches the vendor
theorem `EulerBoundedMildContinuation.exists_global_mild_of_bound`
(`vendor/NavierStokesAndEuler/Euler/BoundedMildContinuation.lean:39`) specialised at
`period := 1`, `u₀ := ordinarySobolev (q+1) a.toLp _`, `C := coefficients 1 hq (sobolevPath F hF q)`.

### F3 — `forced_global_of_bound` is `exists_local`'s conclusion on `S`, clause for clause. Severity: none (pass)

`exists_local` (`formalization/NSFormalization/Source/OrdinaryForcedLocal.lean:32`) vs
`forced_global_of_bound` (`Continuation.lean:155`), both `#check`ed with `pp.fullNames`:

| # | `exists_local` | `forced_global_of_bound` | verdict |
|---|---|---|---|
| — | `∃ T (hT : 0 < T) (hTS : T ≤ S)` | *(none — the interval is the prescribed `S`)* | intended: this is the whole point (`T₀ := S`) |
| 1 | `‖u‖ ≤ ‖u₀‖ + 1` | `‖u‖ ≤ R`, with `hu₀ : ‖u₀‖ ≤ R` | **generalisation**, not a weakening: `R` is a free parameter and `R := ‖u₀‖+1` is admissible |
| 2 | `u ⟨0,…⟩ = ordinarySobolev (q+1) a.toLp _` | identical | ✓ |
| 3 | `U ⟨0,…⟩ = a.toLp` | identical | ✓ |
| 4 | `∀ t, ordinaryLift (U t) = value 1 (u t)` | identical | ✓ |
| 5 | `∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0` | identical | ✓ |
| 6 | `∀ t, u t = quadraticDuhamel 1 ν hν hT.le hTS C u₀ u t` | same with `hS.le`, `le_rfl` | ✓ (`T := S`) |
| 7 | `∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t` | identical | ✓ but *assumed*, see F4 |

Nothing else is hidden: the extra hypotheses over `exists_local` are exactly `hR`, `hu₀`,
`hbound`, `hinv`.  `hR`/`hu₀` are the price of clause 1's generalisation; `hbound` is the
vendor's own a-priori bound (`BoundedMildContinuation.lean:42-44`, verbatim); `hinv` is F4.

### F4 — `hinv` is genuine, but stated one premise too strong. Severity: **medium** (design; free to fix)

**In words.**  `hinv` says: *every* continuous path `u : [0,S] → H^{q+1}(cylinder)` that
satisfies the forced Duhamel equation with datum `ordinarySobolev (q+1) a.toLp _` and
coefficient bundle `coefficients 1 hq (sobolevPath F hF q)` is fixed by every auxiliary-angle
translation `sobolevTranslation 1 (q+1) (0,θ)`.

**Is it the same clause `exists_local` proves?  No — it is the ∀-side of it.**  `exists_local`
produces *one* solution and proves *that one* invariant (`ForcedCylinderInvariant.lean:71-112`).
`hinv` demands invariance of *all* solutions.  `exists_local`'s own output does **not** satisfy
`hinv` on its own interval, because `exists_local` says nothing about other solutions.  The
asymmetry is forced: `forced_global_mild_of_bound` is a black box that returns *some* `u`, so
the consumer has no handle on which one — hence the ∀.

**Is it a genuine mathematical hypothesis (not a disguised `False`)?  Yes.**  On this carrier
both the datum and the force path are angle-invariant for *every* `a` and `F` with no extra
hypotheses (`ordinarySobolev_angle`, `Source/OrdinaryCylinderDescent.lean:71` — used exactly
so at `OrdinaryForcedLocal.lean:52-53`), so nothing in the setup forces a non-invariant
solution to exist.  And it is dischargeable in the regime where uniqueness holds (F6b).

**But the `‖u‖ ≤ R` premise is missing and is free.**  In the proof `hinv` is applied only to
the `u` returned by `forced_global_mild_of_bound`, which already carries `hu : ‖u‖ ≤ R`.
Adding that premise strictly weakens the hypothesis (strictly strengthens the theorem) at zero
cost.  Probe `/tmp/rev126/hinv_weak.lean`, identical five-line proof:

```lean
theorem forced_global_of_bound' … 
    (hinv : ∀ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))), ‖u‖ ≤ R →      -- ← added
        (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl … u t) →
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) :
    … := by
  obtain ⟨u, hu, hi, hm⟩ := forced_global_mild_of_bound hq hν hS hR a F hF hu₀ hbound
  have hinvu := hinv u hu hm
  have hd := forced_mild_divergenceFree hq hν hS a ha F hF u hm
  obtain ⟨U, hU0, hUl⟩ := forced_ordinary_descent hq hS a u hi hinvu
  exact ⟨u, U, hu, hi, hU0, hUl, hd, hm, hinvu⟩
```
→ `'forced_global_of_bound'' depends on axioms: [propext, Classical.choice, Quot.sound]` (exit 0)

This matters beyond tidiness: the `R`-bounded form is **exactly** what the window-uniqueness
route of F6b can discharge, and the unrestricted form is not.  As written, the lane's `hinv`
asks the next lane for something strictly harder than it needs.

**Design judgement — exposing `hinv` is right; dropping the clauses would be wrong.**  The two
clauses are not independent: `forced_ordinary_descent` needs invariance because
`ordinaryValue_lift` (`Source/OrdinaryCylinderDescent.lean:60`) *consumes* it, so dropping
invariance also costs clauses 3 and 4 — i.e. the ordinary-`L²` output `U`, which is precisely
what A02's `ClassicalSolutionR` bridge and A3's `T₀ := S` consumer want.  A theorem with
clauses 1,2,5,6 only would not be "the local theory on `[0,S]`".  Keeping the full shape with
one honest hypothesis is the better trade, provided the hypothesis is the weakest one that works.

### F5 — Non-vacuity. Severity: **low** (pass with one caveat)

The lane's `example` in `research/A01/axioms_a2b.lean:23-38` is **not** a zero-data
instantiation — it re-applies `forced_global_mild_of_bound` under literally the same
hypotheses.  That is the anti-pattern `logs/LESSONS.md` records ("负向检查不能只用「省略参数
再 apply 原定理」"): it shows the signature elaborates, not that anything is satisfiable.

Actual instantiation, on `zeroField : SmoothL2Field Space`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothFieldAlgebra.lean:72`), probe
`/tmp/rev126/nonvac.lean`, `set_option autoImplicit false`, exit 0:

```lean
/-- (c1) zero data is divergence-free: `ha` is satisfiable. -/
example : ∀ x, EulerSmoothLimit.divergence (zeroField : SmoothL2Field Space).field x = 0 := by
  intro x; simp [EulerSmoothLimit.divergence, zeroField]

/-- (c2) zero data satisfies `hu₀` for every `R ≥ 0`. -/
example {q : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    ‖ordinarySobolev (q + 1) (zeroField : SmoothL2Field Space).toLp
      (zeroField : SmoothL2Field Space).translation_contDiff‖ ≤ R := by
  refine (ordinarySobolev_norm_le_tensor zeroField (q + 1)).trans ?_
  have h : tensorNorm (q + 1) (zeroField : SmoothL2Field Space) = 0 := by
    simp [tensorNorm, zeroField_jet]
  rw [h]; exact hR
```

So `ha` and `hu₀` are jointly satisfiable on concrete data.  `hbound` itself I could **not**
instantiate, and I do not think it is cheaply instantiable: it quantifies over *all* solutions
on *all* windows with no norm restriction, so satisfying it is essentially an a-priori estimate
plus a uniqueness statement.  That is not a defect of this lane — `hbound` is the vendor's own
hypothesis copied verbatim, with the same status inside the vendor, and A3-S1 is exactly the
task of supplying it.  It is certainly not *contradictory*: it is a universally quantified
implication whose conclusion `‖u‖ ≤ R` is satisfiable (take `R` large and `u` the Picard
solution), and the vendor derives a non-trivial existence statement from it.  Recorded as
"inherited, open", not as a hole.

### F6 — The recorded GAP is overstated; both stated blockers fail. Severity: **HIGH** (plan-changing)

The lane records (`Continuation.lean:45-60`, `ATTEMPTS_A2B.md:53-94`, and the new
`A01_SPLIT.md` A2b cell) two independent blockers for clause (2b):
(i) `hsmall : kernelMass S · L < 1` is false for large `S` and the vendor has no global mild
uniqueness — *mathematical*; (ii) the template needs `maxHeartbeats 800000`, "which this
lane's hard rules forbid" — *resource*.  Neither survives.

#### F6a — The committed probe does not parse; the real blocker there is a missing `rfl`, and the heartbeat number is 300000, not 800000

`research/A01/probes/a2b_invariant_FAILED.lean` puts its 14-line `/-! … -/` header **before**
the `import` lines:

```
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/a2b_invariant_FAILED.lean
../research/A01/probes/a2b_invariant_FAILED.lean:15:0: error: invalid 'import' command,
  it must be used in the beginning of the file
```

So as committed it reproduces nothing.  Moving the three imports to the top (`/tmp/rev126/a2b_invariant_fixed.lean`),
the recorded errors do reproduce, **verbatim** in text and column, shifted by exactly the
14-line header — which confirms the lane ran a pre-header copy and transcribed honestly
(`ATTEMPTS_A2B.md:82,84` cite `67:90` and `75:8`; I get `81:90` and `89:8`):

```
/tmp/rev126/a2b_invariant_fixed.lean:81:90: error: unsolved goals
…
⊢ (heatOperator 1 (q + 1) (2 * ν * ↑s).toNNReal) u₀ = (freeHeatPath 1 (q + 1) ν S u₀) s
/tmp/rev126/a2b_invariant_fixed.lean:89:8: error: (deterministic) timeout at `whnf`,
  maximum number of heartbeats (200000) has been reached
```

The first error is **not** a resource problem — it is a one-token proof bug.
`freeHeatPath period q ν T u₀` is *defined* as `fun t => heatOperator period q (2*ν*t.val).toNNReal u₀`
(`vendor/NavierStokesAndEuler/Euler/SobolevHeatVolterra.lean:50-53`), so the goal is `rfl`.
Appending `rfl` after the `rw [← heatOperator_translation, hi θ]` at line 83:

```
$ LEAN_NUM_THREADS=6 lake env lean /tmp/rev126/a2b_800k_fixed.lean       # maxHeartbeats 800000
exit=0        (4.7 s user, 5.4 s wall)
```

Bisecting the budget on the fixed file:

```
n=200000 -> FAIL: (deterministic) timeout at `whnf`
n=250000 -> FAIL: (deterministic) timeout at `isDefEq`
n=300000 -> OK
n=400000 -> OK
```

**`maxHeartbeats 300000`** — 1.5× the default, ~5 s — not 800000.  And more importantly:

**`set_option maxHeartbeats` is not forbidden in this repository.**  `CLAUDE.md` does not
mention it; `.claude/hooks/post_lean.py:17` greps only for
`\bsorry\b|\badmit\b|\bnative_decide\b|^\s*axiom\b`; `.claude/skills/lane-review/SKILL.md:18`
asks the simplifier to "drop **unneeded** `maxHeartbeats`".  Ten merged modules use it:

```
formalization/NSFormalization/Paper3/RealPositiveDensity.lean:8       8000000
verification/Bindings/Correction.lean:130                            2000000
formalization/NSFormalization/Section4/A03/ScalarTameProduct.lean:249 1200000
formalization/NSFormalization/Source/ForcedCylinderInvariant.lean:5    800000   ← the cited file
formalization/NSFormalization/Paper1/PeriodicH3RepresentativeBridge.lean:3  800000
formalization/NSFormalization/Paper3/AngularRealVectorBochner.lean:8   800000
formalization/NSFormalization/Source/LocalReferenceInsertion.lean:17   800000
formalization/NSFormalization/Section4/B01/Temporal.lean:71            400000
formalization/NSFormalization/Section4/A03/RealAngularProduct.lean:111 400000
formalization/NSFormalization/Section4/B01/Spatial.lean:126            400000
```

The lane invented the constraint and then recorded a GAP because of it.  This is the item the
brief asked me to settle: it is a per-file `set_option` decision for the lead, and the number
is **300000**.

#### F6b — Angle invariance does **not** need global mild uniqueness: the continuation's own windows are the uniqueness regime

This is the substantive correction.  Read `exists_global_mild_of_bound`'s proof
(`Euler/BoundedMildContinuation.lean:48-72`): it obtains `δ` from
`EulerUniformHeatLocal.exists_uniform_restart_time` and then induces along a grid, each step
solving on a window `b = min δ (S-a) ≤ δ` and gluing with `EulerTimePathGluing.gluePath` +
`EulerQuadraticMildPasting.glue_quadratic_mild`.

Now read where that `δ` comes from (`Euler/UniformHeatLocal.lean:42-54`):

```lean
obtain ⟨δ, hδ, hδS, hb, hl⟩ := exists_positive_time_budget ν
  (C.ballBound (R+1)) (C.ballLipschitz (R+1)) 1 S (by norm_num) hS
…
have hsmall : (T+2*parabolicConstant ν*Real.sqrt T)*C.ballLipschitz (R+1) < 1 :=
  (mul_le_mul_of_nonneg_right hmass hL).trans_lt hl
```

`exists_positive_time_budget` (`Euler/VolterraUniqueness.lean:69`) *guarantees*
`(δ + 2·parabolicConstant ν·√δ)·L < 1`, and
`(δ + 2·parabolicConstant ν·√δ) = kernelMass δ (parabolicKernelBound ν)` by
`parabolicKernelBound_integral` (`Euler/SobolevHeatKernel.lean:145`) — this identification is
already made in-repo at `Source/ForcedCylinderInvariant.lean:104-105`.

**So `hsmall` — the very hypothesis the lane declares unreachable — holds on every window the
continuation uses, by construction.**  `kernelMass S · L < 1` being false for large `S` is
irrelevant: nobody needs it on all of `[0,S]`.

Two probes settle it.  Both compile, both standard axioms, both ~5–6 s.  **Probe 1**
(`/tmp/rev126/window_inv.lean`, needs `maxHeartbeats 400000`; 300000 fails) — invariance of
*every* `R`-bounded solution on *every* window `≤ δ`, with `hsmall` **discharged**, not assumed:

```lean
import NSFormalization.Source.OrdinaryForcedLocal
import Euler.BoundedMildContinuation
set_option maxHeartbeats 400000
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanSmoothRepresentative
open EulerCylinderSobolevSpace EulerSmoothFieldSobolevTime EulerQuadraticSource
open EulerSobolevHeat EulerVolterraConvolution EulerUniformHeatLocal
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open scoped Topology ContDiff
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem probe_window_invariance {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ S ∧
      ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S), T ≤ δ →
        ∀ u₀ : SobolevSpace 1 (q + 1),
          (∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u₀ = u₀) →
          ∀ u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)), ‖u‖ ≤ R →
            (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
              (coefficients 1 hq (sobolevPath F hF q)) u₀ u t) →
            ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  set f := sobolevPath F hF q with hfdef
  set C := coefficients 1 hq f with hCdef
  obtain ⟨δ, hδ, hδS, _, hl⟩ :=
    exists_positive_time_budget ν (C.ballBound R) (C.ballLipschitz R) 1 S (by norm_num) hS
  refine ⟨δ, hδ, hδS, ?_⟩
  intro T hT hTS hTδ u₀ hi u hu hsol θ t
  have hsmall : kernelMass T (parabolicKernelBound ν) * C.ballLipschitz R < 1 := by
    have hmass := EulerUniformHeatLocal.parabolic_mass_mono ν T δ hTδ
    have hL := C.ballLipschitz_nonneg R hR
    have := mul_le_mul_of_nonneg_right hmass hL
    simpa only [kernelMass, parabolicKernelBound_integral ν T hT] using this.trans_lt hl
  set G := (C.comp (timeInclusion hTS)).apply with hGdef
  have hG : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace 1 (q + 1) => G p.1 p.2) :=
    (C.comp (timeInclusion hTS)).continuous
  have hf : ∀ (θ : AddCircle (1 : ℝ)) s, sobolevTranslation 1 q (0, θ) (f s) = f s :=
    fun θ s => ordinarySobolev_angle q (F s).toLp (F s).translation_contDiff θ
  have hFL : ∀ (s : Icc (0 : ℝ) T) (x y : SobolevSpace 1 (q + 1)),
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖G s x - G s y‖ ≤ C.ballLipschitz R * ‖x - y‖ :=
    fun s x y hx hy => C.apply_sub_bound R hR (timeInclusion hTS s) x y hx hy
  have hsolF : ∀ s : Icc (0 : ℝ) T,
      u s = freeHeatPath 1 (q + 1) ν T u₀ s +
        ∫ r in (0 : ℝ)..s.val, heatKernel 1 q ν hν r
          (G (projIcc 0 T hT (s.val - r)) (u (projIcc 0 T hT (s.val - r)))) := hsol
  let A := sobolevTranslation 1 (q + 1) (0, θ)
  let v : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)) :=
    ⟨fun s => A (u s), A.continuous.comp u.continuous⟩
  have hv : ‖v‖ ≤ R := by
    apply (ContinuousMap.norm_le _ hR).mpr
    intro s
    change ‖sobolevTranslation 1 (q + 1) (0, θ) (u s)‖ ≤ R
    rw [sobolevTranslation_norm]
    exact (ContinuousMap.norm_coe_le_norm u s).trans hu
  have hcov : ∀ (s : Icc (0 : ℝ) T) (w : SobolevSpace 1 (q + 1)),
      G s (A w) = sobolevTranslation 1 q (0, θ) (G s w) :=
    fun s w => source_translation 1 hq f (0, θ) (hf θ) (timeInclusion hTS s) w
  have hsolv : ∀ s : Icc (0 : ℝ) T,
      v s = freeHeatPath 1 (q + 1) ν T u₀ s +
        ∫ r in (0 : ℝ)..s.val, heatKernel 1 q ν hν r
          (G (projIcc 0 T hT (s.val - r)) (v (projIcc 0 T hT (s.val - r)))) := by
    intro s
    change A (u s) = _
    rw [hsolF s, map_add]
    have hfree : A (freeHeatPath 1 (q + 1) ν T u₀ s) = freeHeatPath 1 (q + 1) ν T u₀ s := by
      change sobolevTranslation 1 (q + 1) (0, θ)
        (heatOperator 1 (q + 1) (2 * ν * s.val).toNNReal u₀) = _
      rw [← heatOperator_translation, hi θ]
      rfl
    rw [hfree]
    congr 1
    change (translationIsometry 1 (q + 1) (0, θ))
      (∫ r in (0 : ℝ)..s.val, heatKernel 1 q ν hν r
        (G (projIcc 0 T hT (s.val - r)) (u (projIcc 0 T hT (s.val - r))))) = _
    rw [← (translationIsometry 1 (q + 1) (0, θ)).intervalIntegral_comp_comm]
    apply intervalIntegral.integral_congr
    intro r _
    change A (heatKernel 1 q ν hν r (G _ (u _))) = heatKernel 1 q ν hν r (G _ (A (u _)))
    rw [hcov, heatKernel_translation]
  have huv := mild_solution_unique T hT (heatKernel 1 q ν hν) (parabolicKernelBound ν)
    (heatKernel_joint_continuous 1 q ν hν) (parabolicKernelBound_integrable ν T hT)
    (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound 1 q ν hν r hr.1 y)
    (freeHeatPath 1 (q + 1) ν T u₀) G hG R (C.ballLipschitz R)
    (C.ballLipschitz_nonneg R hR) hFL hsmall v u hv hu hsolv hsolF
  exact congrArg (fun w : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)) => w t) huv
```
```
$ LEAN_NUM_THREADS=6 lake env lean /tmp/rev126/window_inv.lean        # 4.5 s user, 5.2 s wall
exit=0
'probe_window_invariance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Probe 2** (`/tmp/rev126/restart_inv.lean`, `maxHeartbeats 600000`; 400000 fails): the *same*
theorem with the restart shape — `∀ b T, 0 ≤ b, b + T ≤ S, T ≤ δ`, `timeWindow b T hb hbT` in
place of `timeInclusion hTS`, and the conclusion's equation written in the explicit
`heatOperator + ∫ heatKernel (C.apply (timeWindow …) …)` form that
`exists_uniform_restart_time` actually outputs.  Only those three textual substitutions; the
proof body is unchanged (`source_translation` accepts any time point, so the covariance step
is indifferent to the shift).

```
$ LEAN_NUM_THREADS=6 lake env lean /tmp/rev126/restart_inv.lean       # 5.4 s user, 6.1 s wall
exit=0
'probe_restart_window_invariance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Probe 2 **is** the per-window invariance the continuation induction consumes.  What is left to
do is therefore: carry the clause through the induction and the glue — not build a uniqueness
theory.  See §3.

The parts of the lane's gap note that **are** correct and worth keeping: there is no pointwise
route (the source is covariant, not invariant, `ForcedCylinderInvariant.lean:19-26`), so a
uniqueness step is genuinely needed; and `mild_solution_unique` (`Euler/VolterraUniqueness.lean:22`)
genuinely is the only mild uniqueness in the vendor's `Euler/` tree, with
`inviscid_correction_unique` (`Euler/InviscidCorrectionUniqueness.lean:25`) genuinely being the
inviscid strong equation.  The error is the jump from "no *global* uniqueness" to "invariance
unreachable".

### F7 — Dead and wrong pointers. Severity: **low**

| where | says | actual |
|---|---|---|
| `Continuation.lean:10`, `ATTEMPTS_A2B.md:11` | `tmp/REVIEW_A3_for_126.md` | does not exist, not tracked anywhere (`tmp/` is gitignored). The file is `research/A01/REVIEW_A3.md`, present on `origin/erenup/integration` (absent from this lane's merge-base, which is why the lane used a scratch copy). `logs/LESSONS.md` already records this exact trap. |
| `Continuation.lean:191`, `ATTEMPTS_A2B.md:49` | `A01_SPLIT.md:136` for H1 | the H1 rows are `:147` and `:186`; `:136` is an unrelated C1b datum-constructor line |
| `ATTEMPTS_A2B.md:82,84` | errors from `…/probes/a2b_invariant.lean`, lines `67`/`75` | committed file is `a2b_invariant_FAILED.lean`, lines `81`/`89` (see F6a) |
| `Continuation.lean:10` | `research/A01/A3_SPLIT.md` §3b | ✓ exists on `origin/erenup/integration` (not in the merge-base); resolves after merge |

All fifteen Lean `file:line` citations in `Continuation.lean` and `ATTEMPTS_A2B.md` **check
out**, and so do the two `FormalPatched/R3MildContinuation` numbers `:93` / `:143` in the new
`A01_SPLIT.md` cell:

```
BoundedMildContinuation.lean:39   theorem exists_global_mild_of_bound
CorrectionContinuation.lean:17    theorem correction_mild_divergenceFree
VolterraUniqueness.lean:22        theorem mild_solution_unique
UniformHeatLocal.lean:29          theorem exists_uniform_restart_time
DivergenceFreeHeat.lean:110       theorem mild_solution_preserves_gradient_zero
InviscidCorrectionUniqueness.lean:25  theorem inviscid_correction_unique
SobolevHeatKernel.lean:145        theorem parabolicKernelBound_integral
Source/ForcedCylinderLocal.lean:32    theorem leray_gradient_zero
Source/ForcedCylinderLocal.lean:52    def coefficients
Source/ForcedCylinderInvariant.lean:5   set_option maxHeartbeats 800000
Source/ForcedCylinderInvariant.lean:19  theorem source_translation
Source/ForcedCylinderInvariant.lean:30  theorem exists_local_forced_mild_invariant
Source/OrdinaryCylinderDescent.lean:56  def ordinaryValue
Source/OrdinaryCylinderDescent.lean:60  theorem ordinaryValue_lift
Source/OrdinaryForcedLocal.lean:32      theorem exists_local
FormalPatched/R3MildContinuation.lean:93   r3EndpointSafeProjected_exists_extension_of_bounded
FormalPatched/R3MildContinuation.lean:143  r3EndpointSafeProjected_blowup_dichotomy
```

### F8 — `A01_SPLIT.md` conflicts with integration. Severity: **medium** (for the lead at merge)

The lane branched from `3d56e21`; `origin/erenup/integration` has since rewritten the **same
three rows** (A2, A2b, A3) of `research/A01/A01_SPLIT.md` — lane 122's follow-up edit.  The
lane touched only the A2b line, but the hunk overlaps:

```
$ git merge-file -p ours.md base.md theirs.md > merged.md ; echo $?
1
$ grep -n '^<<<<<<<\|^=======\|^>>>>>>>' merged.md
86:<<<<<<<
90:=======
94:>>>>>>>
```

Both texts are correct and complementary.  Integration's A2b cell records "not blocked on C1c,
corrected lane 122 (F5)" and points at `A3_SPLIT.md` rows A2b-a′/A2b-a and lane 122's probe
`research/A01/probes/a2b_continuation_probe.lean`; the lane's records "DONE (lane 126)" with
the five theorem names.  **Resolution for the lead:** take integration's A2 and A3 cells
unchanged (the lane did not touch them), take the lane's A2b cell, re-attach integration's two
pointers, and **rewrite the A2b gap sentence per F6** — as it stands it would freeze a blocker
that does not exist into the plan table:

> ~~"`mild_solution_unique` needs `kernelMass S·L<1`, false for large `S`; no global mild uniqueness in vendor; small-window template needs `maxHeartbeats 800000`"~~
> → "(2b) angle-invariance not restored **in this lane**: needs the invariance clause carried through `exists_global_mild_of_bound`'s window induction.  No global uniqueness is required — the continuation's windows already satisfy `kernelMass·L<1` by construction (`UniformHeatLocal.lean:42-54`); per-window invariance verified in `REVIEW_A2B.md` §F6b.  Next row A2b-b, size **M**."

### F9 — One uniqueness the sweep missed (informational, no verdict impact)

`ATTEMPTS_A2B.md` sweeps the vendor's `Euler/` tree only.  The local tree has
`formalization/NSFormalization/Source/BoundedViscosityUniqueness.lean:23
classical_uniqueness_on_Icc` — a genuine Grönwall-type uniqueness **under an a-priori bound**
(`‖u‖ ≤ B`, `‖∇u‖ ≤ G`), i.e. the shape the gap note says does not exist — and
`Source/OrdinaryViscousUniqueness.lean:26 velocity_unique`.  Both are on the **classical** R³
PDE (smooth fields, `residual ν u p`), not the cylinder mild equation, so reaching them needs
the C1b/C1c bridge and they are not a shortcut here.  Worth one line in `ATTEMPTS_A2B.md` so
the next lane does not re-derive the sweep.  (`logs/LESSONS.md` already has the rule: negative
sweeps need filename + theorem-name + docstring passes; this one only covered `vendor/…/Euler/`.)

---

## 3. Recommended next A2b lane

**★ Row A2b-b — "invariance-carrying forced continuation"**, extending
`formalization/NSFormalization/Section4/A01/Continuation.lean` (or a sibling
`ContinuationInvariant.lean` to keep the frozen module untouched).  Goal: delete `hinv` from
`forced_global_of_bound` entirely, so A01's A3 takes `T₀ := S` from the a-priori bound alone.

Three steps, all templated from code that already exists, total ≈ **150–190 lines**, one
`set_option maxHeartbeats 600000`.  Size **M**, one lane.

1. **`exists_uniform_restart_time_invariant`** — **S–M**, ≈ 80 lines.
   Merge (a) the 20-line body of `EulerUniformHeatLocal.exists_uniform_restart_time`
   (`Euler/UniformHeatLocal.lean:41-62`; `exists_positive_time_budget` is public at
   `Euler/VolterraUniqueness.lean:69`, so the same `δ` is re-derivable outside the vendor) with
   (b) the verified body of **probe 2** above (`/tmp/rev126/restart_inv.lean`, compiles,
   standard axioms).  Output: one `δ > 0` such that every window `[b, b+T]`, `T ≤ δ`, with
   invariant datum `‖u₀‖ ≤ R` has a solution with `‖·‖ ≤ R+1` **and** that solution — indeed
   every `(R+1)`-bounded solution on that window — is angle-invariant.
   *The whole proof is already written and checked; this step is transcription.*

2. **`gluePath_invariant`** — **S**, ≈ 10 lines.
   `EulerTimePathGluing.gluePath a b ha hb u v hmatch` is invariant when `u` and `v` are:
   case split on `t ≤ a` with `glueFunction_left` / `glueFunction_right`
   (`Euler/TimePathGluing.lean:46,51`) and unfold `extendPath` (`= u ∘ projIcc`).

3. **`forced_global_mild_invariant_of_bound`** — **M**, ≈ 60 lines.
   Fork `EulerBoundedMildContinuation.exists_global_mild_of_bound`'s induction
   (`Euler/BoundedMildContinuation.lean:48-72`, 25 lines; `advance_time_eq` / `advance_grid`
   at `:14,21` are reusable as-is) adding
   `∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t` to the inductive existential.
   Everything the added clause needs is already in the vendor proof or free:
   * base case datum invariance — `ordinarySobolev_angle` (`Source/OrdinaryCylinderDescent.lean:71`),
     no hypotheses on `a`;
   * restart datum `u ⟨a,ha,le_rfl⟩` invariance — the inductive hypothesis;
   * `‖u ⟨a,ha,le_rfl⟩‖ ≤ R` — already derived at `BoundedMildContinuation.lean:67-68`;
   * step invariance — step 1; glue invariance — step 2.
   Then `forced_global_of_bound` drops `hinv` and keeps all seven clauses.

**Do immediately, independent of the above (5 minutes):** adopt `forced_global_of_bound'`
from §F4 — add `‖u‖ ≤ R` to `hinv`'s premises.  Same proof, strictly stronger theorem, and it
is the exact form steps 1–3 discharge.  If lane A2b-b slips, also export
`probe_window_invariance` (§F6b) as a standalone theorem: it already gives unconditional
invariance on any window `≤ δ`, which is what `A02.restart` consumes.

**Do not** open an L campaign for a Grönwall mild uniqueness on the viscous cylinder equation.
F6b shows it is not on the path to (2b).  If one is ever wanted for its own sake, the honest
statement is "global uniqueness among `R`-bounded solutions by chaining `mild_solution_unique`
along the same grid", which needs one genuinely missing lemma — *restriction of a `[0,S]`
Duhamel solution to a sub-window* (the vendor has `windowSource` / `glue_quadratic_mild` only
in the gluing direction, `Euler/QuadraticMildPasting.lean:16,39`).  That is a separate row and
is **not** needed for A2b.

## 4. Fix list for this lane before merge

| # | file | fix | severity |
|---|---|---|---|
| 1 | `Continuation.lean` `hinv`, `A01_SPLIT.md` A2b cell, `ATTEMPTS_A2B.md` §gap | add `‖u‖ ≤ R` to `hinv` (F4) | medium |
| 2 | `ATTEMPTS_A2B.md` §gap, `Continuation.lean:45-60`, `A01_SPLIT.md` A2b cell | rewrite the gap per F6: 300000 not 800000, `maxHeartbeats` not forbidden, no global uniqueness needed, next row = A2b-b (M) | **high** |
| 3 | `research/A01/probes/a2b_invariant_FAILED.lean` | move the three `import` lines above the header comment so the file parses; add the missing `rfl` note or keep it as the recorded failure with a one-line "(the first error is a missing `rfl`)" | medium |
| 4 | `Continuation.lean:10`, `ATTEMPTS_A2B.md:11,49,82,84` | `tmp/REVIEW_A3_for_126.md` → `research/A01/REVIEW_A3.md`; `A01_SPLIT.md:136` → `:147`; probe filename and line numbers | low |
| 5 | `ATTEMPTS_A2B.md` | one line on `Source/BoundedViscosityUniqueness.lean:23` (F9) | low |
| 6 | *(lead, at merge)* `research/A01/A01_SPLIT.md` | resolve the conflict per F8 | medium |
