# A01 — review of lane 113-SIMP-A01 (simplifier + tester pass)

Reviewer: opus (lane-review), 2026-09-14.  Branch `erenup/113-SIMP-A01` @ `cc9db6c`,
one commit on base `d3f7060`.  Worktree `.claude/worktrees/113-SIMP-A01`.
Probes lived in `/tmp/rev113/` (volatile) — **their full source is embedded in §6 below**
so the evidence survives, per `logs/LESSONS.md` (2026-09-14, "/tmp 探针是易失的").

## Verdict: **ACCEPT-WITH-NOTES**

The lane does what it claims and nothing else.  Every exported statement in the four A01
modules is byte-identical to the base; only the bodies and docstrings of the two `private`
helpers of `PressureGauge.lean` changed; everything builds, is silent, and carries exactly
the three standard axioms; `make check` and `Tests.RegularityPartial` are green.

The notes are about the **tester** half, not the simplifier half.  The lane's negative-check
method (drop a hypothesis, then apply the original theorem with the argument omitted) only
ever demonstrates that the *signature* has the argument.  Re-running the checks properly
shows the method got one of its own eleven claims wrong: **`hsym` in
`pressure_potential_of_pointwise` is not load-bearing — it is implied by the other two
hypotheses** (F1).  Two other hypotheses are genuinely load-bearing, and I proved that by
exhibiting counterexamples rather than by type errors (F2, F3).  None of this requires a
code change in this lane (the statements are frozen); F1 is a V2 note.

---

## 1. Statements unchanged — verified

`git diff d3f7060 HEAD` touches exactly six files, one of them under `formalization/`:

```
 formalization/NSFormalization/Section4/A01/PressureGauge.lean |  28 ++--
 research/A01/ATTEMPTS_SIMP.md                                 | 176 +++++++
 research/A01/negative_simp.lean                               | 140 ++++++
 research/A01/nonvacuity_simp.lean                             |  70 +++
 research/A01/probes/nonvac_probe.lean                         |  51 +++
 research/A01/probes/simp_helpers.lean                         |  21 +++
 6 files changed, 467 insertions(+), 19 deletions(-)
```

`git diff --numstat` on `formalization/` = `9  19  .../A01/PressureGauge.lean`, matching the
lane's claimed `+9/−19`.  The hunk is confined to the two `private` helpers
`fderiv_apply_component` and `fderiv_fderiv_apply` (bodies + docstrings).  The other three
modules are untouched (zero bytes changed), so nothing exported by them can have moved.

Independently of reading the diff, I extracted every declaration signature (everything from
the `theorem`/`def`/`abbrev` keyword up to the `:=`) from `git show d3f7060:<file>` and from
the branch file and diffed them:

```
=== PressureGauge ===     9 decls, 0 signature differences
=== RadialPotential ===   8 decls, 0 signature differences
=== ConvectionDivergence === 5 decls, 0 signature differences
=== ProjectedEquation === 1 decls, 0 signature differences
```

`#check` on all 17 exported declarations elaborates on the branch (`/tmp/rev113/checks.lean`,
exit 0, 78 lines of output).  Since the imports are unchanged and no exported declaration's
*text* changed, the elaborated signatures cannot have drifted.

Line counts: `PressureGauge` 221 → 211, `ConvectionDivergence` 140, `ProjectedEquation` 68,
`RadialPotential` 246 — all exactly as claimed.

## 2. Compiles / axioms / gates — all green

```
$ cd verification && LEAN_NUM_THREADS=6 lake build \
    NSFormalization.Section4.A01.{PressureGauge,RadialPotential,ConvectionDivergence,ProjectedEquation} \
    Tests.RegularityPartial
info: Tests/RegularityPartial.lean:17:0: Contract BlowupDensity.Tests.checkedRegularityPartial:
  checked; standard logical axioms only
Build completed successfully (9953 jobs).            exit 0   (incremental PressureGauge 2.07 s)

$ for f in PressureGauge RadialPotential ConvectionDivergence ProjectedEquation; do
    lake env lean ../formalization/NSFormalization/Section4/A01/$f.lean; done
--- PressureGauge: exit=0 lines=0 ---
--- RadialPotential: exit=0 lines=0 ---
--- ConvectionDivergence: exit=0 lines=0 ---
--- ProjectedEquation: exit=0 lines=0 ---            (all silent)

$ lake env lean ../research/A01/axioms_{a01,p1,m4}.lean       exit 0 each
  15 declarations (5 + 3 + 7), every one:
  depends on axioms: [propext, Classical.choice, Quot.sound]

$ lake env lean ../research/A01/negative_simp.lean            exit 1, 12 error messages
  (11 blocks; N10 emits two — matches the lane's own write-up)
$ lake env lean ../research/A01/nonvacuity_simp.lean          exit 0, 0 output lines
$ lake env lean ../research/A01/probes/simp_helpers.lean      exit 0
$ lake env lean ../research/A01/probes/nonvac_probe.lean      exit 0

$ make check
  check_contracts.py OK; test_contract_policy.py  Ran 13 tests  OK;
  check_work_queue.py  "30 work items: ownership, contract registration and task cards consistent."
```

No `sorry`, no new axiom, no `native_decide`, no import-policy change (`verification/` untouched).

## 3. Findings

### F1 — `hsym` in `pressure_potential_of_pointwise` is NOT load-bearing.  Severity: medium (spec note, V2)

The lane's block **N10** asserts `hsym` is load-bearing.  It is not.  `hsym` follows from the
other two hypotheses:

* `pressureGradient_fderiv_slice` (the module's own Riesz identity) gives
  `fderiv ℝ (p(t,·)) = fun x => innerSL ℝ (∇p(t,x))`;
* `hsm` makes that `C^∞`, and with `hdp` the Mathlib lemma `contDiff_infty_iff_fderiv`
  upgrades `p(t,·)` itself to `ContDiff ℝ ∞`;
* Clairaut (`ContDiffAt.isSymmSndFDerivAt`, exactly as `hasSymmetricJacobian_pressureGradient`
  already does) then yields the symmetric Jacobian.

I proved this outright (`/tmp/rev113/neg_gauge.lean`, source in §6.3):

```
theorem hsym_redundant {T : ℝ} (p : PressureField)
    (hsm : ∀ t ∈ Ico (0:ℝ) T, ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y))
    (hdp : ∀ t ∈ Ico (0:ℝ) T, Differentiable ℝ (fun y : Space => p (t, y))) :
    ∀ t ∈ Ico (0:ℝ) T, HasSymmetricJacobian (fun y : Space => pressureGradient p t y)

theorem pressure_potential_of_pointwise_without_hsym {T : ℝ} (p : PressureField)
    (hsm : …) (hdp : …) :
    PressureGaugeEquivOn (Ico (0:ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient p z.1 z.2)) p :=
  pressure_potential_of_pointwise p (hsym_redundant p hsm hdp) hsm hdp
```

```
$ lake env lean /tmp/rev113/neg_gauge.lean
exit=0                                    (silent — no errors, no warnings)
'Rev113.Gauge.hsym_redundant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev113.Gauge.pressure_potential_of_pointwise_without_hsym'
    depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Action: none in this lane.**  `pressure_potential_of_pointwise` is a frozen statement and a
redundant hypothesis is sound, merely non-minimal (and the sole in-tree consumer,
`pressure_potential_of_classicalSolution`, supplies it from
`hasSymmetricJacobian_pressureGradient` at no cost).  This is a note for a V2 / for whoever
writes the contract: the minimal hypothesis set is `hsm` + `hdp`.  It should also be recorded
that the lane's `ATTEMPTS_SIMP.md` §2(c) N10 claim ("for each export with a load-bearing
hypothesis") is wrong for N10.

### F2 — `hdiv` in `navierStokesResidual_eq_iff_projected` IS load-bearing (refutable without it).  Severity: none (confirmation)

Not merely unprovable: **false**.  Dropping `hdiv` makes the iff force
`(∇·u) • u(t,x) = 0` for every spatially differentiable field.  The linear field
`u(t,y) = y₀ e₀` has `∇·u = 1` and `u(t,e₀) = e₀ ≠ 0`.

```
$ lake env lean /tmp/rev113/neg_convdiv.lean
exit=0    (two `EuclideanSpace.single_apply` deprecation warnings only)
'Rev113.ConvDiv.hdiv_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Statement proved: `(∀ ν u p t x F, DifferentiableAt … → (residual = F ↔ projected form)) → False`.

### F3 — `hG` in `hasFDerivAt_radialPotential` IS load-bearing (counterexample).  Severity: none (confirmation)

`G(y) = y₁ e₀` is `ContDiff ℝ ∞` and `¬ HasSymmetricJacobian G` (proved: `G_not_symm`).  Its
radial potential is `∫₀¹⟪G(ry),y⟫dr = y₁y₀/2` (proved: `pot_eq`), whose derivative at `e₀`
along `e₁` is `1/2`, while the claimed derivative `innerSL ℝ (G e₀) = innerSL ℝ 0 = 0`.

```
$ lake env lean /tmp/rev113/neg_radial.lean
exit=0    (deprecation / unused-simp-arg warnings only)
'Rev113.Radial.hG_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev113.Radial.G_not_symm'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

### F4 — the lane's negative-check method cannot tell F1 from F2/F3.  Severity: medium (method)

All eleven blocks of `research/A01/negative_simp.lean` have the same shape: restate the
theorem minus one hypothesis, then prove it by applying the original theorem with that
positional argument omitted.  That always fails, and the failure is always the same fact —
*the theorem's signature still has the argument*.  It says nothing about whether the weaker
statement is provable by other means.  N10's actual error text is:

```
../research/A01/negative_simp.lean:130:2: error: Type mismatch
  pressure_potential_of_pointwise p ?m.47 ?m.49
has type
  (∀ t ∈ Ico 0 ?m.45, Differentiable ℝ fun y => p (t, y)) →
    PressureGaugeEquivOn (Ico 0 ?m.45) (pressurePotential fun z => pressureGradient p z.1 z.2) p
but is expected to have type
  PressureGaugeEquivOn (Ico 0 T) (pressurePotential fun z => pressureGradient p z.1 z.2) p
```

— which is exactly the same evidence N3 and N6 produce, yet N10's hypothesis is removable and
N3's/N6's are not.  The lane's own defence of the method ("a block that *did* compile would be
a genuine finding") is true but one-sided: a block that *fails* is not a finding at all.

Recommended `logs/LESSONS.md` line (lead to add):
*「负向检查只用"省略参数再 apply 原定理"是无效的：它只证明签名里有这个参数，不证明假设是必要的
(113 审稿：`pressure_potential_of_pointwise` 的 `hsym` 用这法子"通过"了，实际可由 `hsm`+`hdp` 推出)。
必须 (a) 删假设后重述 + `set_option autoImplicit false in` + 独立尝试证明，或 (b) 给反例。」*

I checked whether `autoImplicit` silently re-bound anything (the 077 trap): it did not — every
block is wrapped in `set_option autoImplicit false in`, correctly.

### F5 — non-vacuity witnesses are all degenerate.  Severity: low

`research/A01/nonvacuity_simp.lean` compiles silently, and the hypothesis classes it inhabits
are the right ones.  But every witness is trivial, so no conclusion is exercised:

* NV1/NV2 use `G = id`, whose Jacobian is the identity — `HasSymmetricJacobian` holds because
  `fderiv_fun_id` reduces the condition to `e_i j = e_j i`, not because of any symmetry content.
* NV3/NV4 use the **zero pressure**, so `∇p ≡ 0`: `hasSymmetricJacobian_pressureGradient`'s
  Clairaut content is never touched, and NV4's `PressureGaugeEquivOn` conclusion relates
  `0` to `0` with gauge `c ≡ 0` — it would hold for any theorem of that shape.
* NV5 uses the zero velocity field, so `advection`, `convectionDivergence` and the divergence
  are all `0` simultaneously.
* `T` is a free `ℝ` in NV3/NV4, so the statements also cover `T ≤ 0` where `Ico 0 T = ∅`;
  they are `∀ T` so this is not fatal, but it means the reader cannot tell from the example
  alone that a nonempty time interval was used.

This is a weaker check than the file's docstring implies ("shows the hypothesis class is
inhabited (so the theorem is not vacuously about an empty class)") — the class is inhabited,
but only by its degenerate point.  I built a **non-degenerate** witness
(`/tmp/rev113/nonvac_strong.lean`, source in §6.4): `P(t,y) = y₀y₁`, for which

```
theorem P_grad_ne_zero (t : ℝ) : pressureGradient P t (coordinateVector 1) ≠ 0
theorem P_symm_jac (T : ℝ) {t : ℝ} (ht : t ∈ Ico (0:ℝ) T) :
    HasSymmetricJacobian (fun x : Space => pressureGradient P t x)
      ∧ pressureGradient P t (coordinateVector 1) ≠ 0
theorem P_gauge (T : ℝ) : PressureGaugeEquivOn (Ico (0:ℝ) T)
    (pressurePotential (fun z : SpaceTime => pressureGradient P z.1 z.2)) P
```

```
$ lake env lean /tmp/rev113/nonvac_strong.lean
exit=0
'Rev113.NonVac.P_gauge'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev113.NonVac.P_symm_jac'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Not a blocker — the lane's examples are correct, just weak.  If a follow-up lane touches this
file, `P` above is a drop-in stronger NV4/NV3.

`ClassicalSolutionR` being left uninhabited is correctly flagged by the lane as an A02-level
obligation and is out of a SIMP lane's scope — I agree.

### F6 — `pressureGradient_apply` is now duplicated verbatim by lane 111.  Severity: low (merge hygiene)

The MAINT list flags `PressureGauge.lean:84 pressureGradient_apply` as a promotion candidate
but does not mention that PR #114 (lane 111, merged into integration *after* this lane
branched at `d3f7060`) added an identical theorem:

| | statement |
|---|---|
| `NSFormalization.Section4.A01.PressureGauge.pressureGradient_apply` (`PressureGauge.lean:84`) | `pressureGradient p t x j = fderiv ℝ (fun y => p (t, y)) x (coordinateVector j)` |
| `NSFormalization.Section4.D01.pressureGradient_apply` (`D01/MomentumSlice.lean:127`) | `pressureGradient p t y j = fderiv ℝ (fun z => p (t, z)) y (coordinateVector j)` |

Same statement up to bound-variable names; two different proofs (A01 routes through the Riesz
identity `pressureGradient_fderiv_slice`, 4 lines; D01 unfolds the sum directly, 6 lines).
This is an honest omission — the file simply did not exist in this worktree.

**Which should be canonical.**  Neither module imports the other; nothing in `formalization/`
imports `A01.PressureGauge`; the one consumer, `verification/Bindings/RegularityPartial.lean`,
imports the three A01 modules but `open`s only `Set` and `NavierStokes.ProblemStatement`
(`Contracts/V1/RegularityPartial.lean` mentions A01 in comments only, so the import policy is
intact).  So there is no ambiguity *today* — but a later module that `open`s both
`…Section4.D01` and `…Section4.A01.PressureGauge` will hit the bare-name `Ambiguous term` trap
from the 109 lesson.  Recommendation, in the repo's own promotion style:

1. The fact is pure `pressureGradient` calculus about the **upstream** definition, with no A01
   and no D01 content.  Canonical home = one Source-level "`pressureGradient` calculus" module
   holding `pressureGradient_fderiv_slice` **and** `pressureGradient_apply`; both call sites
   then `alias`.  That is what the lane's own MAINT row already proposes.
2. If a single existing copy must be picked instead: keep **A01's**.  It is the elder (merged
   first), it is a 4-line corollary of `pressureGradient_fderiv_slice` — which has to live
   somewhere regardless — and `D01.MomentumSlice`'s closure (`D01.Pressure` → `ForceClass`,
   `A03.OuterTameProduct`, `A05.SmoothJets`, `Source.FourierPhysicalJets`,
   `Paper3.AngularTameProduct`) is far heavier than A01's, so aliasing in the other direction
   would cost `A01.PressureGauge` a large import (measure it first — lesson 087).

Either way this is a MAINT-lane item, not a change for 113.

### F7 — minor citation slip in `ATTEMPTS_SIMP.md`.  Severity: very low

§1 says `fderiv_clm_apply` "is reachable through the existing
`import Mathlib.Analysis.Calculus.FDeriv.Mul` in `RadialPotential` — no new import."
The "no new import" half is correct (the module compiles unchanged).  The attribution is not:
`fderiv_clm_apply` is declared in `Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:143`, and is
reached transitively, not from `FDeriv/Mul.lean`.

Everything else in `ATTEMPTS_SIMP.md` checks out.  I verified every `file:line` citation in the
MAINT table against the post-edit files:

```
PressureGauge.lean:62    theorem pressureGradient_fderiv_slice (p : PressureField) …      OK
PressureGauge.lean:84    theorem pressureGradient_apply (p : PressureField) …             OK
PressureGauge.lean:117   theorem contDiff_gradSlice {T : ℝ} {p : PressureField}           OK
PressureGauge.lean:64      have basisL : ∀ (u : Space) (j : Fin 3), …                     OK
PressureGauge.lean:66      have expand : ∀ (u : Space),                                   OK
RadialPotential.lean:110 theorem inner_fderiv_symm {G : SpatialField} …                   OK
RadialPotential.lean:114   have expand : ∀ (u : Space),                                   OK
RadialPotential.lean:117   have basis_inner : ∀ (u : Space) (j : Fin 3),                  OK
RadialPotential.lean:238   have hcoord : ∀ i : Fin 3, (inner ℝ (G x) (coordinateVector i) : ℝ) = (G x) i   OK
```

The "left alone" reasons in §1 are also sound: I confirmed `coordinateVector` is still used at
`PressureGauge.lean:64,65,67,68,85,86,147–157`, so removing it from `fderiv_apply_component`
left no dead code, and all four modules elaborate with zero warnings, so there is indeed
nothing for `linter.unusedVariables` / `linter.unusedSimpArgs` to trim.

### F8 — the lane is based on `d3f7060`, two merges behind integration.  Severity: informational

`origin/erenup/integration` is at `20dc9b6` (includes PR #112 and #114); the lane's merge-base
is `d3f7060`.  A plain `git diff` against integration therefore shows spurious deletions of
`B02/ApproxCompact.lean`, `D01/MomentumSlice.lean`, `D01/OrderZeroAlgebra.lean` and the
records files — those are *not* lane changes.  I reviewed `d3f7060..HEAD` throughout.

The rebase is clean: the set of files the lane touches and the set of files integration
touched since `d3f7060` are **disjoint** (verified with `comm -12` on the two `--name-only`
lists), including the usual `PLAN.md` / `AGENT_RUNS.csv` / `LESSONS.md` conflict points.

## 4. Statement-fidelity of my own probes

A negative check is worthless if the reviewer's restatement drifts from the real theorem.  I
pinned all three by deriving my `H` from the real theorem plus the dropped hypothesis
(`/tmp/rev113/fidelity.lean`, §6.5):

```
$ lake env lean /tmp/rev113/fidelity.lean
fidelity EXIT=0        (two `linter.unusedVariables` name warnings only)
```

Each `example` is `fun … => <real theorem> …`, so the conclusion, binder order and implicit /
explicit status in my probes are exactly the frozen ones.

## 5. Commands run (complete list)

```
git -C .claude/worktrees/113-SIMP-A01 merge-base HEAD origin/erenup/integration   -> d3f7060
git diff --stat/--numstat/--name-only d3f7060 HEAD
git show d3f7060:formalization/NSFormalization/Section4/A01/*.lean   (signature extraction)
comm -12 <(git diff --name-only d3f7060 HEAD) <(git diff --name-only d3f7060 origin/erenup/integration)
. scripts/lean-env.sh ; cd verification ; export LEAN_NUM_THREADS=6
lake build NSFormalization.Section4.A01.{PressureGauge,RadialPotential,ConvectionDivergence,ProjectedEquation} Tests.RegularityPartial
lake env lean ../formalization/NSFormalization/Section4/A01/{4 modules}.lean
lake env lean ../research/A01/{axioms_a01,axioms_p1,axioms_m4}.lean
lake env lean ../research/A01/{negative_simp,nonvacuity_simp}.lean
lake env lean ../research/A01/probes/{simp_helpers,nonvac_probe}.lean
lake env lean /tmp/rev113/{checks,fidelity,neg_convdiv,neg_radial,neg_gauge,nonvac_strong}.lean
make check
```

Results are quoted inline in §2–§4.

## 6. Reviewer probe sources (embedded — the `/tmp/rev113` copies are volatile)

### 6.1 `neg_convdiv.lean` — `hdiv` is load-bearing (refutation)

```lean
import NSFormalization.Section4.A01.ConvectionDivergence

/-!
Reviewer probe (lane 113), real negative check #1.
Is `hdiv` load-bearing in `navierStokesResidual_eq_iff_projected`?
We show the hypothesis-free version is **refutable**, not merely unprovable.
-/

noncomputable section
namespace Rev113.ConvDiv

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01

/-- `u(t,y) = y₀ e₀`: linear (so spatially differentiable), divergence `1`, nonzero at `e₀`. -/
def Lin : Space →L[ℝ] Space := (EuclideanSpace.proj (0 : Fin 3)).smulRight (coordinateVector 0)

def U : VelocityField := fun z => Lin z.2

theorem U_slice (t : ℝ) : (fun y : Space => U (t, y)) = ⇑Lin := rfl

theorem spatialDerivative_U (t : ℝ) (x : Space) : spatialDerivative U t x = Lin := by
  rw [spatialDerivative, U_slice, Lin.fderiv]

theorem div_U (t : ℝ) (x : Space) : spatialDivergence U t x = 1 := by
  rw [spatialDivergence]
  simp [spatialDerivative_U, Lin, coordinateVector, Fin.sum_univ_three,
    EuclideanSpace.single_apply]

theorem U_ne (t : ℝ) : U (t, coordinateVector 0) ≠ 0 := by
  intro h
  have h0 : (U (t, coordinateVector (0 : Fin 3))) 0 = (0 : Space) 0 := by rw [h]
  simp [U, Lin, coordinateVector, EuclideanSpace.single_apply] at h0

set_option autoImplicit false in
/-- **`hdiv` is load-bearing**: without it the statement is FALSE. -/
theorem hdiv_load_bearing
    (H : ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) (F : Space),
        DifferentiableAt ℝ (fun y : Space => u (t, y)) x →
        (NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = F
          ↔ temporalDerivative u t x - ν • spatialLaplacian u t x
              = (F - convectionDivergence u t x) - pressureGradient p t x)) :
    False := by
  have hdiff : DifferentiableAt ℝ (fun y : Space => U (0, y)) (coordinateVector 0) := by
    rw [U_slice]; exact Lin.differentiableAt
  have key := (H 0 U (fun _ => 0) 0 (coordinateVector 0)
      (NavierStokesR3.ProblemStatement.navierStokesResidual 0 U (fun _ => 0) 0
        (coordinateVector 0)) hdiff).mp rfl
  have hres : NavierStokesR3.ProblemStatement.navierStokesResidual 0 U (fun _ => 0) 0
      (coordinateVector 0)
      = temporalDerivative U 0 (coordinateVector 0) + advection U 0 (coordinateVector 0)
        - (0 : ℝ) • spatialLaplacian U 0 (coordinateVector 0)
        + pressureGradient (fun _ => 0) 0 (coordinateVector 0) := rfl
  rw [hres, convectionDivergence_eq_advection_add_smul_div U 0 (coordinateVector 0) hdiff] at key
  have h3 := sub_eq_zero_of_eq key
  have h4 : spatialDivergence U 0 (coordinateVector 0) • U (0, coordinateVector 0)
      = (temporalDerivative U 0 (coordinateVector 0)
          - (0 : ℝ) • spatialLaplacian U 0 (coordinateVector 0))
        - (((temporalDerivative U 0 (coordinateVector 0) + advection U 0 (coordinateVector 0)
              - (0 : ℝ) • spatialLaplacian U 0 (coordinateVector 0)
              + pressureGradient (fun _ => 0) 0 (coordinateVector 0))
            - (advection U 0 (coordinateVector 0)
              + spatialDivergence U 0 (coordinateVector 0) • U (0, coordinateVector 0)))
          - pressureGradient (fun _ => 0) 0 (coordinateVector 0)) := by abel
  have h5 : spatialDivergence U 0 (coordinateVector 0) • U (0, coordinateVector 0) = 0 := by
    rw [h4]; exact h3
  rw [div_U, one_smul] at h5
  exact U_ne 0 h5

end Rev113.ConvDiv
```

### 6.2 `neg_radial.lean` — `hG` is load-bearing (counterexample)

```lean
import NSFormalization.Section4.A01.RadialPotential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Reviewer probe (lane 113), real negative check #2.
Is `hG : HasSymmetricJacobian G` load-bearing in `hasFDerivAt_radialPotential`?
Counterexample: `G(y) = y₁ e₀` is `ContDiff ℝ ∞` but has a non-symmetric Jacobian,
its radial potential is `p(y) = y₁y₀/2`, and `∇p(e₀) = e₁/2 ≠ 0 = G(e₀)`.
-/

noncomputable section
namespace Rev113.Radial

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01.RadialPotential
open scoped ContDiff RealInnerProductSpace

/-- `G(y) = y₁ e₀`: smooth, but `∂₀G₁ = 0 ≠ 1 = ∂₁G₀`. -/
def M : Space →L[ℝ] Space := (EuclideanSpace.proj (1 : Fin 3)).smulRight (coordinateVector 0)

def G : SpatialField := fun y => M y

theorem G_contDiff : ContDiff ℝ ∞ G := M.contDiff

/-- `G` really fails the symmetric-Jacobian hypothesis. -/
theorem G_not_symm : ¬ HasSymmetricJacobian G := by
  rintro ⟨-, hsym⟩
  have h := hsym 0 0 1
  rw [show G = ⇑M from rfl, M.fderiv] at h
  simp [M, coordinateVector, PiLp.single_apply] at h

/-- The radial potential of `G` is `y ↦ y₁y₀/2`. -/
theorem pot_eq : (fun y : Space => ∫ r in (0:ℝ)..1, (inner ℝ (G (r • y)) y : ℝ))
    = fun y : Space => (y 1 * y 0) / 2 := by
  funext y
  have hi : ∀ r : ℝ, (inner ℝ (G (r • y)) y : ℝ) = r * (y 1 * y 0) := by
    intro r
    simp [G, M, coordinateVector, real_inner_smul_left, EuclideanSpace.inner_single_left,
      ]
  simp only [hi]
  rw [intervalIntegral.integral_mul_const, integral_id]
  ring

set_option autoImplicit false in
/-- **`hG` is load-bearing**: without it the statement is FALSE. -/
theorem hG_load_bearing
    (H : ∀ (G' : SpatialField), ContDiff ℝ ∞ G' → ∀ x : Space,
        HasFDerivAt (fun y => ∫ r in (0:ℝ)..1, (inner ℝ (G' (r • y)) y : ℝ))
          (innerSL ℝ (G' x)) x) :
    False := by
  have h := H G G_contDiff (coordinateVector 0)
  rw [pot_eq] at h
  have hG0 : G (coordinateVector (0 : Fin 3)) = 0 := by
    simp [G, M, coordinateVector]
  rw [hG0, map_zero] at h
  have hpt : (coordinateVector (0 : Fin 3) : Space) + (0:ℝ) • (coordinateVector (1 : Fin 3) : Space)
      = coordinateVector 0 := by simp
  have h' : HasFDerivAt (fun y : Space => ((y 1 : ℝ) * y 0) / 2) (0 : Space →L[ℝ] ℝ)
      ((coordinateVector (0 : Fin 3) : Space) + (0:ℝ) • (coordinateVector (1 : Fin 3) : Space)) := by
    rw [hpt]; exact h
  have hγ : HasDerivAt
      (fun s : ℝ => (coordinateVector (0 : Fin 3) : Space) + s • (coordinateVector (1 : Fin 3) : Space))
      (coordinateVector 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (coordinateVector (1 : Fin 3))).const_add
      (coordinateVector (0 : Fin 3))
  have hcomp := h'.comp_hasDerivAt 0 hγ
  simp only [ContinuousLinearMap.zero_apply] at hcomp
  have hfun : ((fun y : Space => ((y 1 : ℝ) * y 0) / 2) ∘
      fun s : ℝ => (coordinateVector (0 : Fin 3) : Space) + s • (coordinateVector (1 : Fin 3) : Space))
      = fun s : ℝ => s / 2 := by
    funext s
    simp [coordinateVector, PiLp.single_apply]
  rw [hfun] at hcomp
  have hreal : HasDerivAt (fun s : ℝ => s / 2) (1/2) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).div_const 2
  have hcontra := hcomp.unique hreal
  norm_num at hcontra

end Rev113.Radial
```

### 6.3 `neg_gauge.lean` — `hsym` is redundant (F1)

```lean
import NSFormalization.Section4.A01.PressureGauge

/-!
Reviewer probe (lane 113), real negative check #3.
Is `hsym` load-bearing in `pressure_potential_of_pointwise`?
Claim: NO — `hsym` follows from `hsm` + `hdp`.  Indeed `fderiv (p(t,·)) = innerSL ∘ ∇p(t,·)`
(Riesz, `pressureGradient_fderiv_slice`), so `hsm` makes that derivative `C^∞`; with `hdp`
`contDiff_infty_iff_fderiv` upgrades `p(t,·)` to `C^∞`, and Clairaut then gives the
symmetric Jacobian.  We prove the hypothesis-free statement outright.
-/

noncomputable section
namespace Rev113.Gauge

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01.RadialPotential
open NSFormalization.Section4.A01.PressureGauge
open scoped ContDiff RealInnerProductSpace

/-! The two `private` helpers of `PressureGauge.lean`, copied verbatim (post-113 proofs)
    because they are not exported. -/

private theorem fderiv_apply_component {G : Space → Space} {x : Space}
    (hG : DifferentiableAt ℝ G x) (v : Space) (b : Fin 3)
    {H : Space → ℝ} (hH : H = fun y : Space => (G y) b) :
    (fderiv ℝ G x v) b = fderiv ℝ H x v := by
  have heq : H = ⇑(EuclideanSpace.proj b) ∘ G := hH
  rw [heq, ((EuclideanSpace.proj b).hasFDerivAt.comp x hG.hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply]
  rfl

private theorem fderiv_fderiv_apply {f : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v w : Space) :
    fderiv ℝ (fun y : Space => (fderiv ℝ f y) w) x v = (fderiv ℝ (fderiv ℝ f) x v) w := by
  rw [fderiv_clm_apply hf (differentiableAt_const w)]; simp

set_option autoImplicit false in
/-- **`hsym` is NOT load-bearing**: it is implied by `hsm` + `hdp`. -/
theorem hsym_redundant {T : ℝ} (p : PressureField)
    (hsm : ∀ t ∈ Ico (0:ℝ) T, ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y))
    (hdp : ∀ t ∈ Ico (0:ℝ) T, Differentiable ℝ (fun y : Space => p (t, y))) :
    ∀ t ∈ Ico (0:ℝ) T, HasSymmetricJacobian (fun y : Space => pressureGradient p t y) := by
  intro t ht
  have hgrad := hsm t ht
  have hfd : fderiv ℝ (fun y : Space => p (t, y))
      = fun x : Space => (innerSL ℝ (pressureGradient p t x) : Space →L[ℝ] ℝ) := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    simpa using pressureGradient_fderiv_slice p t x v
  have hslice : ContDiff ℝ ∞ (fun z : Space => p (t, z)) := by
    rw [contDiff_infty_iff_fderiv]
    refine ⟨hdp t ht, ?_⟩
    rw [hfd]
    exact (innerSL ℝ (E := Space)).contDiff.comp hgrad
  refine ⟨hgrad.differentiable (by simp), ?_⟩
  intro x i j
  have hGdiff : DifferentiableAt ℝ (fun y : Space => pressureGradient p t y) x :=
    (hgrad.differentiable (by simp)) x
  have hff : DifferentiableAt ℝ (fderiv ℝ (fun z : Space => p (t, z))) x :=
    ((hslice.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have hsymm := (hslice.contDiffAt (x := x)).isSymmSndFDerivAt (n := ∞) (by simp)
  have hcomp : ∀ (a b : Fin 3),
      (fderiv ℝ (fun y : Space => pressureGradient p t y) x (coordinateVector a)) b
        = (fderiv ℝ (fderiv ℝ (fun z : Space => p (t, z))) x (coordinateVector a))
            (coordinateVector b) := by
    intro a b
    have hH : (fun y : Space => (fderiv ℝ (fun z : Space => p (t, z)) y) (coordinateVector b))
        = fun y : Space => ((fun y : Space => pressureGradient p t y) y) b :=
      funext (fun y => (pressureGradient_apply p t y b).symm)
    rw [fderiv_apply_component hGdiff (coordinateVector a) b hH,
      fderiv_fderiv_apply hff (coordinateVector a) (coordinateVector b)]
  rw [hcomp i j, hcomp j i]
  exact hsymm.eq (coordinateVector i) (coordinateVector j)

set_option autoImplicit false in
/-- Therefore the `hsym`-free version of `pressure_potential_of_pointwise` is provable. -/
theorem pressure_potential_of_pointwise_without_hsym {T : ℝ} (p : PressureField)
    (hsm : ∀ t ∈ Ico (0:ℝ) T, ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y))
    (hdp : ∀ t ∈ Ico (0:ℝ) T, Differentiable ℝ (fun y : Space => p (t, y))) :
    NSFormalization.Section4.A02.PressureGaugeEquivOn (Ico (0:ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient p z.1 z.2)) p :=
  pressure_potential_of_pointwise p (hsym_redundant p hsm hdp) hsm hdp

end Rev113.Gauge
```

### 6.4 `nonvac_strong.lean` — non-degenerate non-vacuity witness (F5)

```lean
import NSFormalization.Section4.A01.PressureGauge

/-!
Reviewer probe (lane 113): the lane's non-vacuity file uses only the ZERO pressure and the
IDENTITY field, for which `HasSymmetricJacobian` and the gauge conclusion are degenerate
(`∇p ≡ 0`, both sides of `PressureGaugeEquivOn` are `0`).  Here is a NON-degenerate witness:
`p(t,y) = y₀y₁`, for which `∇p(t,·) ≠ 0` and the Clairaut content of
`hasSymmetricJacobian_pressureGradient` is actually exercised.
-/

noncomputable section
namespace Rev113.NonVac
open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01.RadialPotential
open NSFormalization.Section4.A01.PressureGauge
open scoped ContDiff RealInnerProductSpace

/-- Coordinate projection with its type pinned (otherwise `𝕜` stays a metavariable). -/
def pr (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj i

theorem pr_apply (i : Fin 3) (y : Space) : pr i y = y i := rfl

/-- `p(t,y) = y₀ y₁`. -/
def P : PressureField := fun z => z.2 0 * z.2 1

theorem P_slice (t : ℝ) : (fun y : Space => P (t, y)) = fun y : Space => (y 0 : ℝ) * y 1 := rfl

theorem P_contDiff : ContDiff ℝ ∞ (fun z : SpaceTime => P z) := by
  have h0 : ContDiff ℝ ∞ (fun z : SpaceTime => (z.2 0 : ℝ)) :=
    (pr 0).contDiff.comp contDiff_snd
  have h1 : ContDiff ℝ ∞ (fun z : SpaceTime => (z.2 1 : ℝ)) :=
    (pr 1).contDiff.comp contDiff_snd
  exact h0.mul h1

theorem P_contDiffOn (T : ℝ) :
    ContDiffOn ℝ ∞ P (Ico (0:ℝ) T ×ˢ (univ : Set Space)) := P_contDiff.contDiffOn

/-- The gradient really is nonzero: `(∇P(t,·))₀ (e₁) = 1`. -/
theorem P_grad_ne_zero (t : ℝ) : pressureGradient P t (coordinateVector 1) ≠ 0 := by
  intro h
  have h0 : pressureGradient P t (coordinateVector (1 : Fin 3)) 0 = (0 : Space) 0 := by rw [h]
  rw [pressureGradient_apply] at h0
  have hp0 : HasFDerivAt (fun y : Space => (y 0 : ℝ)) (pr 0)
      (coordinateVector 1) := (pr 0).hasFDerivAt
  have hp1 : HasFDerivAt (fun y : Space => (y 1 : ℝ)) (pr 1)
      (coordinateVector 1) := (pr 1).hasFDerivAt
  have hd : HasFDerivAt (fun y : Space => (y 0 : ℝ) * y 1)
      ((coordinateVector (1 : Fin 3) : Space) 0 • (pr 1)
        + (coordinateVector (1 : Fin 3) : Space) 1 • (pr 0))
      (coordinateVector 1) := hp0.mul hp1
  rw [P_slice, hd.fderiv] at h0
  simp [pr, coordinateVector] at h0

/-- The Clairaut output is about a genuinely non-constant gradient field. -/
theorem P_symm_jac (T : ℝ) {t : ℝ} (ht : t ∈ Ico (0:ℝ) T) :
    HasSymmetricJacobian (fun x : Space => pressureGradient P t x)
      ∧ pressureGradient P t (coordinateVector 1) ≠ 0 :=
  ⟨hasSymmetricJacobian_pressureGradient (P_contDiffOn T) ht, P_grad_ne_zero t⟩

/-- A non-degenerate instance of the m4 conclusion. -/
theorem P_gauge (T : ℝ) :
    NSFormalization.Section4.A02.PressureGaugeEquivOn (Ico (0:ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient P z.1 z.2)) P :=
  pressure_potential_of_pointwise P
    (fun t ht => hasSymmetricJacobian_pressureGradient (P_contDiffOn T) ht)
    (fun t ht => contDiff_gradSlice (P_contDiffOn T) ht)
    (fun t ht => (NSFormalization.Section4.D01.contDiff_slice_scalar (P_contDiffOn T) ht).differentiable (by simp))


end Rev113.NonVac
```

### 6.5 `fidelity.lean` — the probes' `H`s are the real theorems minus one hypothesis

```lean
import NSFormalization.Section4.A01.ConvectionDivergence
import NSFormalization.Section4.A01.RadialPotential
import NSFormalization.Section4.A01.PressureGauge

/-! Fidelity: each `H` used in the reviewer's negative probes is EXACTLY the real theorem
    with one hypothesis deleted — shown by deriving `H` from the real theorem plus that
    hypothesis (so the conclusion/binders were transcribed correctly). -/

noncomputable section
namespace Rev113.Fidelity
open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open NSFormalization.Section4.A01.RadialPotential
open NSFormalization.Section4.A01.PressureGauge
open scoped ContDiff RealInnerProductSpace

set_option autoImplicit false in
example : ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) (F : Space),
    DifferentiableAt ℝ (fun y : Space => u (t, y)) x →
    spatialDivergence u t x = 0 →
    (NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = F
      ↔ temporalDerivative u t x - ν • spatialLaplacian u t x
          = (F - convectionDivergence u t x) - pressureGradient p t x) :=
  fun ν u p t x F hu hdiv => navierStokesResidual_eq_iff_projected ν u p t x F hu hdiv

set_option autoImplicit false in
example : ∀ (G' : SpatialField), HasSymmetricJacobian G' → ContDiff ℝ ∞ G' → ∀ x : Space,
    HasFDerivAt (fun y => ∫ r in (0:ℝ)..1, (inner ℝ (G' (r • y)) y : ℝ))
      (innerSL ℝ (G' x)) x :=
  fun G' hG hsm x => hasFDerivAt_radialPotential hG hsm x

set_option autoImplicit false in
example : ∀ (T : ℝ) (p : PressureField),
    (∀ t ∈ Ico (0:ℝ) T, HasSymmetricJacobian (fun y : Space => pressureGradient p t y)) →
    (∀ t ∈ Ico (0:ℝ) T, ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y)) →
    (∀ t ∈ Ico (0:ℝ) T, Differentiable ℝ (fun y : Space => p (t, y))) →
    NSFormalization.Section4.A02.PressureGaugeEquivOn (Ico (0:ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient p z.1 z.2)) p :=
  fun T p hsym hsm hdp => pressure_potential_of_pointwise p hsym hsm hdp

end Rev113.Fidelity
```
