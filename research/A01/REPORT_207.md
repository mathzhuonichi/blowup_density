# REPORT 207 — unconditional cylinder tame and local constructor

## 1. Theorems, exact statements and constants

Route A is closed. Both mixed-product orientations have constant
`‖L‖ * sobolevEmbeddingConstant 1 3`. Finite cylinder words, including angular
words, are identified a.e. with smooth derivatives. The recursive Leibniz
estimate counts at most 2^n leaves. The finite commutator sign is verified
before applying Lp.ext and the norm bound.

The explicit constants are:

```lean
tameAssemblyConstant q =
  (Fintype.card (SobolevWord (q+1)) : ℝ) * (2:ℝ)^(q+1) *
    sobolevEmbeddingConstant 1 3

tameAssemblyA q = max (A q) (tameAssemblyConstant q / 4)
E q = mildNormConstant q
A q = mildNormConstant q * (1 + A03.outerTameConst (q+1))
```

The word cardinality is the exact number of all Fin 4 words of lengths
0 through q+1, namely ∑(j=0,…,q+1) 4^j. The embedding constant is the vendor's
proved cylinder H³ constant. No claim that the older fixed A alone suffices
is needed: the existing factor-sixteen forcing chain accepts tameAssemblyA.

The exported statements (with the source namespaces open) are:

```lean
theorem smoothCylinderCoordinateTame {q : ℕ} (hq : 6 ≤ q) :
    SmoothCylinderCoordinateTame q hq (tameAssemblyConstant q)

theorem cylinderCoordinateTame_unconditional {q : ℕ} (hq : 6 ≤ q) :
    CylinderCoordinateTame q hq (tameAssemblyConstant q)

theorem cylinderCoordinateTame_exists' {q : ℕ} (hq : 6 ≤ q) :
    ∃ C : ℝ, CylinderCoordinateTame q hq C

theorem cylinderCommutatorBound_unconditional {q : ℕ} (hq : 6 ≤ q)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q))
    (hV : restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v) :
    familyNorm (cylinderCommutator hq v V) ≤
      tameAssemblyA q * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖) *
        cylinderWordGradient V

theorem forcingFamilyBound_unconditional {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    ForcingFamilyBound hq hν a F hF (E q) (tameAssemblyA q)

theorem finiteMildEnergy' {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    FiniteMildEnergy hq hν a ha F hF (E q) (tameAssemblyA q)

theorem hb_of_base'' {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF
      (aprioriRadius a F hF R₆ E (fun q => tameAssemblyA q^2/(4*ν)) q)

theorem a01_constructor_unconditional {ν Smax : ℝ} (hν : 0 < ν) (hSmax : 0 < Smax)
    (f : A02.SpaceTimeField) (hf : D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) :
    ∃ S : ℝ, 0 < S ∧ S ≤ Smax ∧
      ∃ (velocity : A02.SpaceTimeField)
        (w : A02.ClassicalSolutionR ν (fun x : Space => velocity (0, x)) f S),
        w.velocity = velocity
```

The full family radius is thus
`aprioriRadius a F hF R₆ E (fun q => tameAssemblyA q^2/(4*ν))`.
There is no analytic hypothesis in finiteMildEnergy' or hb_of_base''; the latter
retains its ordinary base-solution and radius data. The constructor probe
constructs that base solution and a positive local horizon itself.

All 22 new TameAssembly declarations and all 34 restored signed-chain
declarations print exactly `[propext, Classical.choice, Quot.sound]`.
The two probe theorems have the same audit. Actual zero-data examples pass.

## 2. Files

* New `formalization/NSFormalization/Section4/A01/TameAssembly.lean`.
* New-to-this-checkout `SignedLimit.lean` and `SignedPassage.lean`, restored
  byte-for-byte from `origin/erenup/204-A01-signed-passage` at commit
  `46e15f81db7cbbe9dd419f954c8a7d1df95dadc4`; no proof edits to those sources.
* New `research/A01/axioms_tame_assembly.lean` (56 declaration audits and
  examples), `ATTEMPTS_TAME_ASSEMBLY.md`, and this report.
* New `research/A01/probes/a01_constructor_unconditional.lean` (fixed-base
  constructor and unconditional existential-local-horizon milestone).
* Updated A3-M2 forcing, envelope and signed-passage rows in `A3_SPLIT.md`
  to DONE, and appended closure notes to the historical A3-M2 rows.

No existing Lean module changed; no push, merge or rebase. All work stayed
inside the supplied worktree. The available lane-206 review file was absent,
so no recommendation to switch to route B applied.

## 3. Gaps and error text

**No analytic gap remains in the requested cylinder tame/forcing/finite-energy
assembly.** The original fixed-constant predicates/theorems are immutable:
`CylinderCommutatorBound` has no constant argument, and
`cylinderCoordinateTame_exists` / `forcingFamilyBound_of_cylinder'` already
exist as conditional theorems. New unconditional names and the expanded
commutator conclusion preserve the larger certified constant without editing
them.

**Horizon correction:** an arbitrary prescribed S>0 is not supplied by
base-order local existence. The requested milestone was therefore proved on
an existential positive S≤Smax, from hf/ha/positivity only. The exact fixed-S
conclusion is also proved as `constructor_of_base`, retaining the base mild
solution on S. No unconditional arbitrary-time/global-existence theorem is
claimed. No remaining analytic hypothesis is hidden inside a new predicate.
The initial datum in the conclusion remains `velocity(0,·)`, as requested.

Resolved Lean diagnostics included `Type mismatch` between wordAtLevel and
finite words, `OuterMeasureClass ?m.588 (LiftDomain 1)` from an under-specified
coercion, and the missing build artifact:

```text
object file '.../NSFormalization/Section4/A01/ConstructorAssembly.olean'
of module NSFormalization.Section4.A01.ConstructorAssembly does not exist
```

The final module, audit and probe have no unresolved errors or warnings.
ATTEMPTS records the fixes and mathematical scope checks.

## 4. Commands

All Lean shells source `. scripts/lean-env.sh`; Lake runs only from
`verification/`, with `LEAN_NUM_THREADS=6`. Logs are untracked `tmp/*207.log`.

* `lake build NSFormalization.Section4.A01.TameAssembly`: exit 0; all new
  modules diagnostic-free. Captured build output includes replayed pre-existing
  dependency warnings and the Lake success banner, so the raw build log is
  not literally silent.
* `lake env lean ../formalization/NSFormalization/Section4/A01/TameAssembly.lean`:
  exit 0, **zero output bytes**.
* `lake env lean ../research/A01/axioms_tame_assembly.lean`: exit 0; all 56
  declarations have exactly the standard three axioms; examples pass.
* `lake build NSFormalization.Section4.A01.ConstructorAssembly
  NSFormalization.Section4.A01.PressureRegularity
  NSFormalization.Section4.A04.ZeroSolution`: exit 0, probe dependencies.
* `lake env lean ../research/A01/probes/a01_constructor_unconditional.lean`:
  exit 0; two standard-three-axiom audit lines, zero-data example passes.
* `make check`: exit 0.
* `make test`: exit 0, registered contract suite.
* `make test-mutations`: exit 0; implementation refactor accepted, three
  invalid mutations rejected.
* `git diff --check`: exit 0.

No prohibited proof commands. One commented declaration-local heartbeat
setting, 400000. Source-restoration hashes match the lane-204 Git blobs.

## Review notes applied (2026-09-16, lead)

- The enlarged forcing constant `tameAssemblyA q = max (A q) (tameAssemblyConstant q / 4)` enters the forcing chain through lane 205's re-cut theorem (`CoordinateTame.lean`, the conditional recut that accepts any `C`), not by editing lane 200's fixed-constant predicate.
- This milestone does not yet inhabit `LocalTheoryAPI` (`research/A01/Spec.lean:167-230, 338-343`): registration still needs (i) initial-datum identification `velocity (0,x) = a x` pointwise (from `hU0`, `hslice` and continuity), (ii) the manuscript regularity/pressure-gauge fields (`ManuscriptLocalRegularity`: all-order Sobolev time smoothness, Helmholtz pressure recovery including `t = 0`, projected equation on `Ioo`, pressure gauge equivalence), and (iii) the **H¹-uniform** `horizon_lower_bound` (paper Appendix A:147-150) — individual H⁷-based local existence and all-order persistence on its interval do not supply it. These are the next lanes.
