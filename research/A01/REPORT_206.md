# REPORT 206 — cylinder interpolation and one mixed-product orientation (partial)

## 1. Theorems, exact statements and constants

**The requested `SmoothCylinderCoordinateTame` theorem is not proved.** This
lane delivers unconditional analytic progress on the cylinder fallback, not
A3-M2 closure or an unconditional constructor.

Write `M n := cylinderWordMaximum V n`. For available orders this is the
maximum of the L² norms of all **Fin 4** words of length n. The key statements
are:

```lean
cylinderWordMaximum_logconvex {s : ℕ} (u : SobolevSpace 1 s)
  (n : ℕ) (h : n+2 ≤ s) :
  (cylinderWordMaximum u (n+1))^2 ≤
    cylinderWordMaximum u n * cylinderWordMaximum u (n+2)

cylinderWordMaximum_product_le_gradient {q a b : ℕ} (hq : 6 ≤ q)
  (V : SobolevSpace 1 (2+q)) (ha0 : 1 ≤ a) (hb0 : 1 ≤ b)
  (ha : a ≤ 2+q) (hb : b ≤ 2+q) (hab : a+b ≤ (2+q)+7) :
  cylinderWordMaximum V a * cylinderWordMaximum V b ≤
    ‖restrictOperator 1 (Nat.succ_le_succ hq)
      (restrictOperator 1 (by omega : q+1 ≤ 2+q) V)‖ * cylinderWordGradient V

cylinderMixedProduct_left {q a b : ℕ} (hq : 6 ≤ q)
  (V : SobolevSpace 1 (2+q)) (ha0 : 1 ≤ a) (hb0 : 1 ≤ b)
  (ha : 3+a ≤ 2+q) (hb : b ≤ 2+q) (hab : a+b ≤ (2+q)+4)
  (w : Fin a → Fin 4) (v : Fin b → Fin 4)
  (L : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ) :
  ‖scalarProduct 1 (by omega : 3 ≤ 3) L (boundedWordBlock 1 3 a ha w V)
      (word 1 V hb v)‖ ≤
    (‖L‖ * sobolevEmbeddingConstant 1 3) *
      (‖restrictOperator 1 (Nat.succ_le_succ hq)
        (restrictOperator 1 (by omega : q+1 ≤ 2+q) V)‖ * cylinderWordGradient V)
```

The interpolation constants are **one**. The genuine left-oriented mixed
product constant is **`‖L‖ * sobolevEmbeddingConstant 1 3`**, with vendor definition
`sobolevEmbeddingConstant 1 3 = (3 * cylinderEmbeddingConstant 1) *
(Fintype.card (SobolevWord 3) : ℝ)` (word count 85). No uniform commutator
constant C is certified. Angular dependence is allowed throughout; no descent
or smoothness hypothesis is needed for these finite-carrier statements.

Supporting theorems retain the exact two words in integration by parts, prove
finite-interval cross/pair/between interpolation, compare word maxima with
restrictions, and bound every positive-order word by the actual gradient
array. There are 13 public declarations, each with precisely the standard
three axioms.

## 2. Files

* New `formalization/NSFormalization/Section4/A01/SmoothTame.lean` (13 declarations).
* New `research/A01/axioms_smooth_tame.lean`: all 13 axiom audits and actual
  zero-data examples, without assuming the universal tame estimate.
* New `research/A01/ATTEMPTS_SMOOTH_TAME.md`: descent consumer audit, negative
  examples, analytic scope, and resolved Lean diagnostics.
* Updated the requested forcing-bound row of `research/A01/A3_SPLIT.md`.
* This report, `research/A01/REPORT_206.md`.

No existing Lean module or verification contract was changed. Work stayed
inside the supplied worktree; no push, merge, or rebase.

## 3. Gaps and error text

The ONE existing named analytic input remains exactly:

```lean
SmoothCylinderCoordinateTame q hq C :=
  ∀ (V : SobolevSpace 1 (2+q)) (f : LiftDomain 1 → Vector3),
    (value 1 V : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f →
    (∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x)) →
    (∀ j, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative 1 w f) 2 (liftMeasure 1)) →
    ∀ i : Fin 4,
      familyNorm (cylinderCoordinateCommutator hq
        (restrictOperator 1 (by omega : q+1 ≤ 2+q) V) V i) ≤
      C * ‖restrictOperator 1 (Nat.succ_le_succ hq)
        (restrictOperator 1 (by omega : q+1 ≤ 2+q) V)‖ * cylinderWordGradient V
```

The transported-factor embedding orientation, finite/smooth Leibniz word
identification and combinatorial summation into this inequality remain open.
The new interpolation is not a substitute for these steps. This is not the
complete cylinder-interpolation fallback requested by the brief, nor an
isolation of a new, smaller R³ hypothesis. It is a partial implementation.
No additional named analytic premise was introduced.

The invariant descent route also needs invariant smooth approximation and
invariance at the arbitrary mild-competitor/maximal-limit application point.
The current `ForcingFamilyBound` has no invariance binder. The invariance of
`CylinderWiring.hpairs` cannot alone discharge this earlier obligation.

This checkout differs from the task snapshot: lane 204's file is absent:

```text
rg: formalization/NSFormalization/Section4/A01/SignedPassage.lean: No such file or directory
```

The existing envelope chain still assumes `CylinderSignedRootLimit`.
Therefore no `hb_of_base'''`, unconditional family, or
`a01_constructor_unconditional` is exported. This is a separate checkout
limitation, not hidden inside the smooth tame input.

Resolved elaboration errors included `Application type mismatch` for a
simplified word index, `invalid 'calc' step` for multiplication order, and
`(deterministic) timeout at whnf, maximum number of heartbeats (400000) has been reached`.
The gradient sum proof was fixed by explicit intermediate types. Final Lean
checks have no unresolved errors. See ATTEMPTS for details.

## 4. Commands

All Lean commands source `. scripts/lean-env.sh`, use `LEAN_NUM_THREADS=6`,
and run Lake from `verification/`. Local logs are in untracked `tmp/*206.log`.

* `lake build NSFormalization.Section4.A01.SmoothTame`: exit 0. The new module
  is diagnostic-free. Standard Lake output replays existing dependency
  warnings and prints a success banner, so the standard build is not literally
  silent; output was captured rather than suppressed as evidence.
* `lake env lean ../formalization/NSFormalization/Section4/A01/SmoothTame.lean`:
  exit 0, zero output bytes.
* `lake env lean ../research/A01/axioms_smooth_tame.lean`: exit 0; every public
  declaration prints exactly `[propext, Classical.choice, Quot.sound]`, and
  the two zero-data examples pass.
* `make check` from the worktree root: exit 0.
* `make test`: exit 0, registered contract suite.
* `make test-mutations`: exit 0; implementation refactor accepted and the three
  invalid mutations rejected.
* `git diff --check`: exit 0.

No prohibited proof commands were added. The single heartbeat override is
commented, declaration-local, and 400000.
