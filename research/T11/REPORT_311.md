# REPORT 311 — T11 U9a existence route probe

## 1. Theorems and exact statements

R2 is selected: native Fourier coefficient paths with A01's causal-window and
common-horizon strategy, reusing R1's endpoint-safe analytic tools. The delivered
first rung is unconditional real-vector heat contraction, smoothing, semigroup,
coherence and incompressibility preservation. A nonzero forced classical solution
also has all three unchanged regularity fields. General quantitative existence
remains the exact named input. The conditional bilinear bound is only the abstract
operator-norm estimate; it is not advertised as a proved convolution bound.

The following are the exact 17 theorem signatures from the delivered module
(namespace `NSFormalization.Section3.T11`; imports and open declarations as there):

```lean
theorem torusMultiplier_norm_le (s r : ℝ) (m : PeriodicFrequency → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ k, |m k| ≤ C) (he : ∀ k, m (-k) = m k)
    (A : PeriodicSobolev s) :
    ‖torusMultiplier s r m C hC hm he A‖ ≤ C * ‖A‖

theorem torus_weight_eq (k : PeriodicFrequency) :
    periodicFrequencyWeight k = NSFormalization.Paper1.periodicFrequencyWeight k

theorem torus_weight_neg (k : PeriodicFrequency) :
    periodicFrequencyWeight (-k) = periodicFrequencyWeight k

theorem torusHeatSymbol_neg (ν t : ℝ) (k : PeriodicFrequency) :
    torusHeatSymbol ν t (-k) = torusHeatSymbol ν t k

theorem torusHeat_norm_le (s : ℝ) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (A : PeriodicSobolev s) : ‖torusHeat s hν ht A‖ ≤ ‖A‖

theorem torusHeatSmoothing_norm_le (s : ℝ) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (A : PeriodicSobolev s) :
    ‖torusHeatSmoothing s hν ht A‖ ≤ torusSmoothingKernel ν t * ‖A‖

theorem torusHeatSmoothing_apply (s : ℝ) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (A : PeriodicSobolev s) (i : Fin 3) (k : PeriodicFrequency) :
    (torusHeatSmoothing s hν ht A).1 i k =
      ((Real.sqrt (periodicFrequencyWeight k) * torusHeatSymbol ν t k : ℝ) : ℂ) *
        A.1 i k

theorem torusHeat_zero (s : ℝ) {ν : ℝ} (hν : 0 ≤ ν) (A : PeriodicSobolev s) :
    torusHeat s hν (le_refl 0) A = A

theorem torusHeat_add (s : ℝ) {ν t u : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (A : PeriodicSobolev s) :
    torusHeat s hν (add_nonneg ht hu) A = torusHeat s hν ht (torusHeat s hν hu A)

theorem torusHeatSmoothing_coherent (s : ℝ) {ν t u : ℝ}
    (hν : 0 < ν) (ht : 0 < t) (hu : 0 ≤ u) (A : PeriodicSobolev s) :
    torusHeatSmoothing s hν (add_pos_of_pos_of_nonneg ht hu) A =
      torusHeat (s + 1) hν.le hu (torusHeatSmoothing s hν ht A)

theorem torusHeat_solenoidal (s : ℝ) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (A : PeriodicSobolev s) (hA : IsSolenoidalPeriodicDatum A) :
    IsSolenoidalPeriodicDatum (torusHeat s hν ht A)

theorem torus_bilinear_bound {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (A B : PeriodicSobolev 3) :
    ‖C.analytic.bilinear A B‖ ≤ ‖C.analytic.bilinear‖ * ‖A‖ * ‖B‖

theorem torusConstantDatum_isDatum (s : ℝ) (c : Space) :
    IsPeriodicDatum s (fun _ ↦ c) (torusConstantDatum s c)

theorem torusConstantDatum_smul (s r : ℝ) (c : Space) :
    IsPeriodicDatum s (fun _ ↦ r • c) (r • torusConstantDatum s c)

theorem torusHomogeneousSolution_regularity (ν T : ℝ) (hT : 0 < T) (c : Space)
    (b d : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (hb0 : b 0 = 1)
    (hd : ∀ t, HasDerivAt b (d t) t) :
    PeriodicLocalRegularity ν (fun _ ↦ c) (fun z ↦ d z.1 • c) T
      (torusHomogeneousSolution ν T hT c b d hb hb0 hd)

theorem quantitative_lifespan_lower_bound (H : PeriodicQuantitativeLocalInput) :
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
      ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
        ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
          (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) →
            ENNReal.ofReal δ ≤ maximalLifespanT ν a g

theorem nonzero_forced_witness :
    ∃ (K : ℝ≥0∞) (a : SpatialField) (g : SpaceTimeField),
      K ≠ ⊤ ∧ a ∈ initialClassT ∧ periodicSobolevENorm 1 a ≤ K ∧
      ContDiff ℝ ∞ g ∧ IsPeriodicOn univ g ∧
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) ∧
      ∃ w : ClassicalSolutionT 1 a g 1,
        PeriodicLocalRegularity 1 a g 1 w ∧
        w.velocity (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0
```

## 2. Files and delivered Lean objects

New files:

- `formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean`:
  33 named declarations, including the one residual input, the exact two-space
  operator/forced mild/numeric ball contracts, the canonical heat construction,
  the homogeneous classical constructor and 17 theorems.
- `research/T11/probes/existence_probe.lean`: original regularity structure copied
  verbatim, all three fields closed for constructed witnesses; exact input shape,
  linear first-rung tests and nonzero force/solution with finite common K.
- `research/T11/axioms_existence_probe.lean`: 33 `#guard_msgs` checks require exactly
  `[propext, Classical.choice, Quot.sound]`, including definitions and named instances.
- `research/T11/EXISTENCE_ROUTE.md`: route evidence, exact symbols and constants,
  exact U9b–e targets and size estimates; the three future quantified statements
  were also elaborated as `#check` expressions in a local scratch probe.
- `research/T11/ATTEMPTS_EXISTENCE_PROBE.md`: searches, actual error text, fixes,
  non-vacuity and exact unresolved input.
- This report.

Only existing-file change: one appended U9a status entry at the end of T11_SPLIT §1.
No existing Lean module, registered contract, build configuration, generated ledger,
PLAN, NEXT_SESSION or LESSONS was edited. This report records the next-session state
under the user's new-files-only scope. No push, merge or rebase was performed.

## 3. Gaps and errors

`PeriodicQuantitativeLocalInput` is not discharged. The contract has no general
inhabitant; convolution boundedness, strong heat continuity/complete-carrier
packaging, forced Picard construction, common-horizon bootstrap, physical pressure
recovery and H¹-uniform lifespan remain U9b–e. The precise statements and dependencies
are in EXISTENCE_ROUTE. Neither the general local-theory API nor continuation API
is claimed complete by this probe.

The U9→U10 edge has an independent quantifier issue: smooth compact forcing has
finite norms separately at each order, not a common finite K for all orders.
The input and original restart target were kept unchanged. This requires explicit
lead reconciliation, not a silent higher-order or fixed-force substitution.

Resolved diagnostic examples: `failed to synthesize instance of type class Norm
(↥(PeriodicSobolev 3) →L[ℝ] ↥(PeriodicSobolev 3) →L[ℝ] ↥(PeriodicSobolev 2))`,
`Unknown constant Real.integrableOn_exp_neg_Ioi`, `Unknown option pp.width`.
The full exact failure text and resolutions are in ATTEMPTS. No final Lean error remains.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`; Lake ran only from `verification/`
with `LEAN_NUM_THREADS=6`.

| Command | Result |
| --- | --- |
| `lake build NSFormalization.Section3.T11.LocalExistenceProbe` | Exit 0, 9905 jobs; new module built, zero source errors/warnings. |
| `lake env lean ../formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean` | Exit 0, empty output. |
| `lake env lean ../research/T11/probes/existence_probe.lean` | Exit 0, empty output. |
| `lake env lean ../research/T11/axioms_existence_probe.lean` | Exit 0; all 33 exact three-axiom guards passed. |
| `lake env lean ../tmp/311/route-statements.lean` | Exit 0; exact proposed U9b/c/d statements elaborate. |
| `make check` from worktree root | Exit 0; plan/contract/policy/work-queue checks pass, 45 work items consistent. |
| `lake test` from verification (the `make test` target's Lake command) | Exit 0; registered-contract test suite passes. |
| `LEAN_NUM_THREADS=6 make test-mutations` from root | Exit 0; refactor accepted and three invalid mutations rejected. |

Local raw gate logs are in ignored `tmp/311/`; summaries above are the retained record.
