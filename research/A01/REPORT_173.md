# Lane 173 — A01 row (iv), HANDOFF P9a

## 1. Theorems proved — route β

The invariant-bound consumer loop is closed. All names below are in
`NSFormalization.Section4.A01`. The exact new predicate is:

```lean
def HasAprioriBoundInv {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
      (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))),
      (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) →
      (∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) → ‖u‖ ≤ R
```

The four theorem signatures are:

```lean
theorem HasAprioriBound.toInv {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℝ) (hb : HasAprioriBound hq hν a F hF R) :
    HasAprioriBoundInv hq hν a F hF R
```

```lean
theorem forced_global_mild_core_of_boundInv {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : HasAprioriBoundInv hq hν a F hF R) :
    ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
      ‖u‖ ≤ R ∧
      u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq (sobolevPath F hF q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t
```

```lean
theorem forced_global_of_boundInv {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : HasAprioriBoundInv hq hν a F hF R) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
        ‖u‖ ≤ R ∧
        u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t
```

```lean
theorem localTheory_on_prescribed_horizon_of_boundInv {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : HasAprioriBoundInv hq hν a F hF R) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
        ‖u‖ ≤ R ∧
        u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t
```

## 2. What is in Lean now

New module `formalization/NSFormalization/Section4/A01/AprioriInvariance.lean`;
conformance `research/A01/axioms_hinv.lean`; both-route investigation and failed
shortcut diagnostic in `research/A01/ATTEMPTS_HINV.md`; lane note appended to
`research/A01/A3_SPLIT.md` row (iv).

The core continuation induction maintains angle invariance before each invocation of
the restricted bound. `forced_global_of_boundInv` adds the ordinary `L²` path, its
initial value, descent, and divergence freedom. Its conclusion is token-identical to
`forced_global_of_bound_unconditional`; the local-theory conclusion is token-identical
to `localTheory_on_prescribed_horizon`. The positive probe
`research/A01/probes/fix173_consumer_match.lean` checks the full continuation match with
a one-line `exact`. All five declarations print exactly
`[propext, Classical.choice, Quot.sound]`. The conformance example specializes to
ν = 1, q = 6, S = 1 and zero datum/force, and exercises the full seven-clause export;
the invariant uniform bound remains its explicitly open supply-side premise.
No existing Lean module was edited and no heartbeat option was added.

## 3. Gaps and exact failed residual

No remaining row-(iv) gap for route β. The actual uniform estimate
`HasAprioriBoundInv hq hν a F hF R` remains a supply-side obligation; this lane
removes the missing `hinv` premise, not the energy/carrier/endpoint estimates.
Existing consumers remain unchanged; supply-side callers can use either full consumer.

Route α (`duhamel_angle_invariant` for every unrestricted Duhamel solution) was
not proved. The available cylinder uniqueness theorem requires
`kernelMass T k * L < 1`; the unrestricted HeliCorgi theorem uses a different
mild contract. Extending uniqueness over arbitrary cylinder windows or converting
the contracts was not attempted after route β closed. No claim of absence of
uniqueness throughout the tree is made.

A direct attempt to turn the weaker predicate into the old predicate failed with:

```text
../research/A01/hinv_direct_probe.lean:22:2: error: Type mismatch
  hb T hT hTS u hsol
has type
  (∀ (θ : AddCircle 1) (t : ↑(Icc 0 T)), (sobolevTranslation 1 (q + 1) (0, θ)) (u t) = u t) → ‖u‖ ≤ R
but is expected to have type
  ‖u‖ ≤ R

```

This shortcut is replaced by the proved invariance-carrying induction. There is
no α compilation error: its candidates were inspected at the signature level.

## 4. Commands and results

All shells sourced `. scripts/lean-env.sh`; all Lake calls used `verification/`.

- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.AprioriInvariance`:
  exit 0, 3944 jobs; no Lean diagnostics. Repeated with `--quiet`: exit 0, zero output.
- `lake env lean ../formalization/NSFormalization/Section4/A01/AprioriInvariance.lean`:
  exit 0, zero output.
- `lake env lean ../research/A01/axioms_hinv.lean`: exit 0;
  exactly the requested three axioms on all five declarations; the full-export
  positive-time example passes.
- `lake env lean ../research/A01/probes/fix173_consumer_match.lean`: exit 0, zero output.
- `make check` from worktree root: passed (27 registered contracts,
  13 policy tests, 30 consistent work items).
- `LEAN_NUM_THREADS=6 lake test` from `verification/` (the `make test` target):
  exit 0, 10528 jobs, registered contract type/axiom checks pass.
- `make test-mutations` from root: exit 0; all three mutation classes rejected.
- `git diff --check`: passed.

Only this worktree was edited. No push, merge, or rebase.
