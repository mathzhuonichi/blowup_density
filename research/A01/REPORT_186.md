# REPORT 186 — A3-U common horizon

## 1. Theorems with exact statements

Conditional reduction completed: one `U := U₆` works at every cylinder order on
`[0,S]`. Restriction of heat, the actual forced source, ordinary Duhamel,
the gained mild path and the canonical forced mild equation are proved.
The full statements of the remaining named input and the three consumer exports
are below (namespace `NSFormalization.Section4.A01`). The primary two conclusions
fix datum and force canonically; the last is lane 178's existential `hall`.

```lean
def MildUniqueness : Prop :=
  ∀ (ν S : ℝ) (hν : 0 < ν) (hS : 0 < S)
    (a : SobolevSpace 1 7) (f : C(Icc (0 : ℝ) S, SobolevSpace 1 6))
    (u v : C(Icc (0 : ℝ) S, SobolevSpace 1 7)),
    (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl (coefficients 1 le_rfl f) a u t) →
    (∀ t, v t = quadraticDuhamel 1 ν hν hS.le le_rfl (coefficients 1 le_rfl f) a v t) →
    u = v
```

```lean
theorem compatible_carriers_of_bounds (huniq : MildUniqueness)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℕ → ℝ) (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (R q))
    (hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ (q : ℕ) (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)),
          ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S) ∧
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q+1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t
```

```lean
theorem compatible_carriers_of_boundsInv (huniq : MildUniqueness)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℕ → ℝ) (hb : ∀ q (hq : 6 ≤ q), HasAprioriBoundInv hq hν a F hF (R q))
    (hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ (q : ℕ) (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)),
          ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S) ∧
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q+1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t
```

```lean
theorem compatible_carriers_hall (huniq : MildUniqueness)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℕ → ℝ) (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (R q))
    (hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ (q : ℕ) (hq : 6 ≤ q),
        ∃ (u₀ : SobolevSpace 1 (q + 1))
          (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
          (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
          ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S) ∧
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t,
            sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq f) u₀ u t
```

## 2. Files

- New `formalization/NSFormalization/Section4/A01/CommonHorizon.lean`: eleven public declarations.
- New `research/A01/axioms_a3_common_horizon.lean`: all eleven print exactly the standard three axioms; two unconditional positive-horizon zero examples, including canonical smooth `a := 0`, `F := 0`.
- New `research/A01/ATTEMPTS_A3_COMMON_HORIZON.md`: search audit, proof route and diagnostics.
- Updated `research/A01/A3_SPLIT.md`: A3-U common horizon row.
- Updated `research/A01/B1_LADDER.md` §R3/R4: what `hall` reduces to.
- This report, `research/A01/REPORT_186.md`.

No existing Lean module, vendor file, contract, or build configuration was edited.

## 3. Gaps with error text

**Unproved: `MildUniqueness`.** Its exact statement is above, and it is an explicit
parameter of both exports, not concealed inside `hall`. The available vendor
`mild_solution_unique` requires `kernelMass T k * L < 1`; continuity bounds the
paths but does not imply that inequality for the entire prescribed interval.
The remaining proof is arbitrary-competitor uniqueness by iteration on small
shifted windows. No unconditional A3-U completion is claimed. `hfs` and the
all-order bounds also remain supplied inputs, as requested.

Resolved implementation diagnostic (not evidence of an analytic obstruction):

```
(deterministic) timeout at `whnf`, maximum number of heartbeats (400000) has been reached
```

Explicit `calc`/`congrArg₂`, a bundled source, controlled path extensionality and
reduction of the target's `let` resolved it. Final module and audit have no errors.

## 4. Commands and results

Every Lean shell sourced `. scripts/lean-env.sh`; all lake commands ran from
`verification/` with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section4.A01.CommonHorizon`: PASS (3945 jobs).
- `lake -q build NSFormalization.Section4.A01.CommonHorizon`: PASS, zero output.
- `lake env lean ../formalization/NSFormalization/Section4/A01/CommonHorizon.lean`: PASS, zero output.
- `lake env lean ../research/A01/axioms_a3_common_horizon.lean`: PASS, eleven declarations, exactly `[propext, Classical.choice, Quot.sound]` each; both examples checked.
- Root `make check`: PASS.
- Root `make test`: PASS.
- Root `make test-mutations`: PASS, all required mutations rejected.
- `git diff --check`: PASS.

Committed on `erenup/186-A01-a3-common-horizon`; no push, merge or rebase.
