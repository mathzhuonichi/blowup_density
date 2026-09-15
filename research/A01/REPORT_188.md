# REPORT 188 — whole-horizon mild uniqueness

## 1. Theorems with exact statements

Proved `mildUniqueness : MildUniqueness`, discharging lane 186's A3-U uniqueness
input. The predicate is unchanged, token for token:

```lean
def MildUniqueness : Prop :=
  ∀ (ν S : ℝ) (hν : 0 < ν) (hS : 0 < S)
    (a : SobolevSpace 1 7) (f : C(Icc (0 : ℝ) S, SobolevSpace 1 6))
    (u v : C(Icc (0 : ℝ) S, SobolevSpace 1 7)),
    (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl (coefficients 1 le_rfl f) a u t) →
    (∀ t, v t = quadraticDuhamel 1 ν hν hS.le le_rfl (coefficients 1 le_rfl f) a v t) →
    u = v
```

The radius is `R := max ‖u‖ ‖v‖`, the Lipschitz constant is
`L := C.ballLipschitz R`, and `δ` comes from
`exists_positive_time_budget ν 0 L 1 S`. The exact contraction condition is
`kernelMass δ (parabolicKernelBound ν) * L < 1`, identified using
`parabolicKernelBound_integral`. Finite induction includes the endpoint S.

The seven new signatures follow, in namespace `NSFormalization.Section4.A01`.
The first two use these ambient variables:

```lean
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {S : ℝ} (hS : 0 ≤ S) (K : ℝ → Y →L[ℝ] X) (k : ℝ → ℝ)
  (hK : ContinuousOn (fun p : ℝ × Y => K p.1 p.2) (Ioi 0 ×ˢ (univ : Set Y)))
  (hk : IntegrableOn k (Ioc 0 S)) (hk0 : ∀ r ∈ Ioc 0 S, 0 ≤ k r)
  (hbound : ∀ r ∈ Ioc 0 S, ∀ y, ‖K r y‖ ≤ k r * ‖y‖)
```

```lean
theorem volterra_window_bound (d : C(Icc (0 : ℝ) S, X))
    (f : C(Icc (0 : ℝ) S, Y)) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ t, ‖f t‖ ≤ L * ‖d t‖)
    (hd : d = convolution S hS K k hK hk hk0 hbound f)
    {a b δ : ℝ} (_hb : 0 ≤ b) (hbS : b ≤ S) (hδS : δ ≤ S)
    (hbδ : b ≤ a + δ) (hpast : ∀ t : Icc (0 : ℝ) S, t.val ≤ a → d t = 0) :
    ‖d.comp (timeInclusion hbS)‖ ≤
      (kernelMass δ k * L) * ‖d.comp (timeInclusion hbS)‖
```

```lean
theorem volterra_eq_zero (d : C(Icc (0 : ℝ) S, X))
    (f : C(Icc (0 : ℝ) S, Y)) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ t, ‖f t‖ ≤ L * ‖d t‖)
    (hd : d = convolution S hS K k hK hk hk0 hbound f)
    {δ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S)
    (hsmall : kernelMass δ k * L < 1) : d = 0
```

```lean
theorem quadratic_mild_unique {q : ℕ} {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (a : SobolevSpace 1 (q+1)) (u v : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl C a u t)
    (hv : ∀ t, v t = quadraticDuhamel 1 ν hν hS.le le_rfl C a v t) : u = v
```

```lean
theorem mildUniqueness : MildUniqueness
```

```lean
theorem compatible_carriers_of_boundsInv'
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
theorem compatible_carriers_of_bounds'
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
theorem compatible_carriers_hall'
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

- New `formalization/NSFormalization/Section4/A01/MildUniqueness.lean`: seven public theorems, no heartbeat overrides.
- New `research/A01/axioms_mild_uniqueness.lean`: seven standard-three-axiom audits and a positive-horizon `∃!` zero-data/zero-force example.
- New `research/A01/ATTEMPTS_MILD_UNIQUENESS.md`: quantitative argument, search audit, alternative restart route, and resolved diagnostics.
- Updated `research/A01/A3_SPLIT.md`: A3-U uniqueness input discharged.
- New `research/A01/REPORT_188.md`: this report.

No existing Lean module, vendor source, contract, or build configuration changed.
The bounds and smooth-force premises of the common-carrier consumers remain.

## 3. Gaps with error text

No remaining gap or Lean error for this lane. All seven public declarations
print exactly `[propext, Classical.choice, Quot.sound]`.

Resolved development diagnostics included:

```
error: don't know how to synthesize implicit argument `s`
error: don't know how to synthesize implicit argument `a`
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  indicator (Real.le✝ r) ?f δ
```

Explicit indicator endpoints and membership types fixed these errors;
`ATTEMPTS_MILD_UNIQUENESS.md` records the details. No proof escape hatch or
additional assumption was introduced.

## 4. Commands and results

Every Lean shell sourced `. scripts/lean-env.sh`; all lake processes ran from
`verification/` with `LEAN_NUM_THREADS=6`.

- `lake -q build NSFormalization.Section4.A01.MildUniqueness`: PASS, zero output.
- `lake env lean ../formalization/NSFormalization/Section4/A01/MildUniqueness.lean`: PASS, zero output.
- `lake env lean ../research/A01/axioms_mild_uniqueness.lean`: PASS; all seven exact axiom sets and the non-vacuity example checked.
- Root `make check`: PASS (architecture, contract policy, work queue).
- `lake test` from `verification/` (the target of root `make test`): PASS; existing dependency warnings replayed, no new-module warnings.
- Root `make test-mutations`: PASS; implementation refactor accepted, admitted proof / extra axiom / weakened hypothesis rejected as required.
- `git diff --check`: PASS.

Committed on `erenup/188-A01-mild-uniqueness`. No push, merge, or rebase.
