# REPORT 198 — cylinder mild energy premises

## 1. Theorems with exact statements and named inputs

All vendor premises are constructed for every finite-order mild competitor on
its given subwindow. No additional premises hypothesis is needed.
The identity metric and full family `SobolevWord (q+1)` give the integrated
root-energy estimate with the actual limiting forcing norm Z left explicit.
The source restriction already existed in `ForcedSourceUpgrade`; this lane
adds the raw and pressure restrictions, divergence preservation for arbitrary
competitors, retains the genuine maximal-approximation limit, and applies the
vendor theorem. No all-order constructor is used.

The root is exactly `euclideanWordNorm`, so lane 196's comparisons apply.
The encoding uses Unit as the outer index and the complete word family as the
inner index, all with weight one; the cutoff is q+1 (external cutoff q−5 in
the correction notation). Metric parameters are c=1, scale=1, direction=0,
radius=1, radius derivative=0, growth coefficients a=b=0, and k=1.

Exact principal theorem statements (with the module's imports and opens):

```lean
theorem energyRawTime_restriction {q : ℕ} (hq : 6 ≤ q) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (W : TimeLp T (SobolevSpace 1 ((q+1)+1)))
    (hW : (fun t => truncateOperator 1 (q+1) (W t)) =ᵐ[timeMeasure T] extendPath T hT u) :
    (fun t => truncateOperator 1 q (energyRawTime hq hT hTS f u W t)) =ᵐ[timeMeasure T]
      extendPath T hT (energyRawPath hq hTS
        ((truncateOperator 1 q).compLeftContinuous ℝ _ f) u)
```

```lean
theorem energyPressureTime_restriction {q : ℕ} (hq : 6 ≤ q) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (W : TimeLp T (SobolevSpace 1 ((q+1)+1)))
    (hW : (fun t => truncateOperator 1 (q+1) (W t)) =ᵐ[timeMeasure T] extendPath T hT u) :
    (fun t => truncateOperator 1 q (energyPressureTime hq hT hTS f u W t)) =ᵐ[timeMeasure T]
      extendPath T hT (energyPressurePath hq hTS
        ((truncateOperator 1 q).compLeftContinuous ℝ _ f) u)
```

```lean
theorem energy_velocity_divergenceFree {q : ℕ} (hq : 6 ≤ q) {ν S T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS (coefficients 1 hq f)
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) :
    ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0
```

```lean
theorem energy_maximal_limit {q : ℕ} (hq : 6 ≤ q) {ν S T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u₀ : SobolevSpace 1 (q+1)) (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS (coefficients 1 hq f) u₀ u t) :
    ∃ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u))
        Filter.atTop (𝓝 U)
```

```lean
theorem energyRootPath_apply {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) (t : Icc (0 : ℝ) T) :
    energyRootPath u t = euclideanWordNorm (u t)
```

```lean
theorem mild_energy_estimate_of_cylinder {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) :
    ∃ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U) ∧
      ∀ s t (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T),
        energyRootPath u ⟨t, h0s.trans hst, htT⟩ - energyRootPath u ⟨s, h0s, hst.trans htT⟩ ≤
          ∫ r in Icc s t, cylinderEnergyForcing hq hT hTS F hF u U r ∂timeMeasure T
```

```lean
theorem finiteMildEnergy_of_estimate {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ)
    (hforcing : ForcingFamilyBound hq hν a F hF E A)
    (henvelope : EnvelopeConversion hq hν a F hF E A) :
    FiniteMildEnergy hq hν a ha F hF E A
```

The final theorem is conditional on precisely two lane-199 inputs. These
are not hypotheses of `mild_energy_estimate_of_cylinder`. Their exact targets
are below; `energyGradientNorm U r` is the square root of the sum of squares of
all four directional derivative words through q+1 of the reindexed higher
representative. Thus the nonlinear pairing has the requested
`A * (16 * low) * root * g` shape. No general-data values of E,A are proved.

```lean
def ForcingFamilyBound {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U) →
      ∀ᵐ r ∂timeMeasure T,
        extendPath T hT (energyRootPath u) r * cylinderEnergyForcing hq hT hTS F hF u U r ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u r)‖) *
            extendPath T hT (energyRootPath u) r * energyGradientNorm U r +
          (E * ‖sobolevPath F hF (q+1)‖) * extendPath T hT (energyRootPath u) r
```

```lean
def EnvelopeConversion {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U) →
      (∀ s t (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T),
        energyRootPath u ⟨t, h0s.trans hst, htT⟩ - energyRootPath u ⟨s, h0s, hst.trans htT⟩ ≤
          ∫ r in Icc s t, cylinderEnergyForcing hq hT hTS F hF u U r ∂timeMeasure T) →
      (∀ᵐ r ∂timeMeasure T,
        extendPath T hT (energyRootPath u) r * cylinderEnergyForcing hq hT hTS F hF u U r ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u r)‖) *
            extendPath T hT (energyRootPath u) r * energyGradientNorm U r +
          (E * ‖sobolevPath F hF (q+1)‖) * extendPath T hT (energyRootPath u) r) →
    ∃ (x : C(Icc (0 : ℝ) T, ℝ)) (d g : ℝ → ℝ),
      (∀ t, 0 ≤ x t) ∧ (∀ t, ‖u t‖ ≤ Real.sqrt (x t)) ∧
      Real.sqrt (x ⟨0, le_rfl, hT⟩) ≤
        E * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT x) (d t) t) ∧
      ∀ t ∈ Ioo 0 T,
        (1/2) * d t + ν * (g t)^2 ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
            (extendPath T hT u t)‖) * Real.sqrt (extendPath T hT x t) * g t +
          (E * ‖sobolevPath F hF (q+1)‖) * Real.sqrt (extendPath T hT x t)
```

Named-input satisfiability: `ha` is initial solenoidality; `hF` is the
restriction of force-jet continuity; `hu` is the restricted standard mild
identity. The representative theorem's divergence/gradient, approximation,
and a.e. restriction hypotheses are standard properties, all discharged in
the cylinder application. `ForcingFamilyBound` is a forcing/commutator family-norm bound, requiring an
additional bridge beyond the signed tensor pairing estimate, restricted to
actual competitors and their maximal limits. `EnvelopeConversion`
restricts the dissipative energy-majorant construction to those same
competitors with their integrated estimate and pairing bound. Neither asks
for smoothness of an Lp representative or continuation beyond the horizon.
Both residual inputs are proved on zero data for every competitor and every
maximal limit, and the new assembly theorem is applied in the conformance
example. General nonzero proofs remain lane 199.

## 2. Files

* `formalization/NSFormalization/Section4/A01/MildEnergyPremises.lean`:
  21 declarations; existing Lean modules untouched.
* `research/A01/axioms_energy_premises.lean`: audits every declaration and
  six zero-data helpers; unconditional zero-data assembly example.
* `research/A01/ATTEMPTS_ENERGY_PREMISES.md`: positive and negative routes,
  satisfiability and compiler diagnostics.
* `research/A01/A3_SPLIT.md`: requested A3-M2 update with premises / forcing
  bound / envelope subrows.
* `research/A01/REPORT_198.md`: this report.

## 3. Gaps and error text

No vendor-premises gap remains. The integrated estimate retains Z and has
already dropped dissipation. Therefore recovering the everywhere-interior
differentiable envelope is a substantive analytic obligation, not merely
scalar differentiation of this inequality. Lane 199 must prove the forcing
family pairing and the envelope/dissipation conversion. Unconditional
`FiniteMildEnergy` and general-data constants are not claimed.

Negative scalar example: root=1, Z=0 satisfies the integrated root estimate,
but d=0, nu=g=1 violates `(1/2)*d + nu*g^2 ≤ 0`. Its arithmetic contradiction
is kernel checked. No nonzero PDE counterexample to the residual predicates
is asserted.
The scalar example rules out recovery of a prescribed nonzero dissipation
from the root estimate alone; it does not refute `EnvelopeConversion`, whose
`g` is existential.

Resolved diagnostics included:

```
(deterministic) timeout at `whnf`, maximum number of heartbeats (400000) has been reached
Tactic `rfl` failed: ... energyValueFamily ... is not definitionally equal to ... euclideanWordNorm
```

The first was resolved by typed congruence steps, the second by the proved
bounded-word value identity. There are no remaining Lean errors. Four
commented declaration-local heartbeat limits are 400000; no greater limit,
placeholder proof, or extra axiom is introduced.

## 4. Commands

All Lean shells source `. scripts/lean-env.sh`; Lake runs only from
`verification/` with `LEAN_NUM_THREADS=6`. Shared dependency symlink checked.

* `lake build NSFormalization.Section4.A01.MildEnergyPremises`: exit 0,
  10247 jobs. The module has no warnings. The build is not literally silent:
  Lake replays warnings from pre-existing dependencies (`tmp/build198.log`).
* `lake env lean ../formalization/NSFormalization/Section4/A01/MildEnergyPremises.lean`:
  exit 0, zero output (`tmp/module198.log`).
* `lake env lean ../research/A01/axioms_energy_premises.lean`: exit 0;
  27 reports, all exactly `[propext, Classical.choice, Quot.sound]`, and all
  examples pass (`tmp/axioms198.log`).
* `make check` from worktree root: exit 0 (`tmp/check198.log`).
* `lake test` from `verification/`: exit 0 (`tmp/test198.log`).
* `make test-mutations`: exit 0; refactor accepted and all three invalid
  mutations rejected (`tmp/mutations198.log`).
* `git diff --check` and forbidden proof-token checks: checked before commit.
* Diff claim (reviewed at lane HEAD `608e9ad`, base `2f86a2f`, integration then `5666c27`): the lane-only
  commit changes one new module plus records; the current integration two-dot diff also reflects later
  integration additions.

Only this worktree was changed. No push, merge, or rebase was performed.
