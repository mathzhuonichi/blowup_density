# REPORT_444 — T17 U10

## 1. Theorems and constant

Closed `force_spatial_memLp`, `mixedConst_nonneg`, and `force_mixed_bound` at the concrete `correctionData`. The constant is exactly the real value of the finite ENNReal witness from `Paper1.CorrectionMixedNorms.physical_force_mixed_bound`, as in I02. It is fixed before ε. Both infinity endpoints are included.

Exact constant and nonnegativity declarations:

```lean
def mixedConst (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (p q : ℝ≥0∞) : ℝ :=
  (Classical.choose (physical_force_mixed_bound ν hv x₀ T hθ hη hθc hηc p q)).toReal

theorem mixedConst_nonneg (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ p q, 1 ≤ p → 1 ≤ q → 0 ≤ mixedConst ν hv x₀ T hθ hη hθc hηc p q :=
  fun _ _ _ _ => ENNReal.toReal_nonneg

```

Exact common premise block:

```lean
variable (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T δ r : ℝ) (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2) (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r)

```

Exact field statements:

```lean
theorem force_spatial_memLp :
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x => correctionForce ν v
        (correctionData v x₀ T θ η O θR ε₀) ε (t, x))) p periodicTorusMeasure

theorem force_mixed_bound
    (hcube : closure (ball x₀ r) ⊆ interior fundamentalCube) (hε₀ : ε₀ ≤ 1) :
    ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      mixedLebesgueENormT q p (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ≤
        ENNReal.ofReal (mixedConst ν hv x₀ T hθ hη hθc hηc p q * ε ^ (alphaT p q + 1))
```

`alphaT p q = Contracts.V1.alpha p q` is checked by `rfl` in the probe. Slices use continuity and compactness of the torus. The bound uses `force_eq`, slice support inside the cube, pointwise equality of lifted periodization and single copy, T15's attained mixed-norm bridge, and exponent-generic Haar/Lebesgue equality. Restricting the time measure to positive times only decreases Paper1's whole-time norm.

## 2. Files

- `formalization/NSFormalization/Section3/T17/Mixed.lean`: four declarations, complete proofs.
- `research/T17/probes/mixed_closes.lean`: literal field types by `exact`, alpha drift example, cube-centred witness with nonzero constant reference, positive threshold, all p,q including infinity.
- `research/T17/axioms_u10.lean`: all module declarations audited.
- `research/T17/ATTEMPTS_U10.md`: failed approaches and exact diagnostics.
- `research/T17/T17_SPLIT.md`: U10 status line.
- `research/T17/REPORT_444.md`: this report.

No existing Lean module changed. Only the requested existing status document was edited.

## 3. Gaps and errors

No residual proof goals. G1 remains an assembly/spec issue: explicit `hv : ContDiff ℝ ∞ v` is required. The bound also uses the same cube placement condition as U9 and ε₀ ≤ 1. These are explicit premises, not hidden inputs. The witness instantiates all of them.

The failed exponent rewrite reported `Tactic rewrite failed: motive is not type correct` because rewriting entered the dependent proof supplying `Classical.choose`. Keeping that constant fixed under `congrArg` resolves it. The first attempt also omitted section-variable `include` declarations. All exact errors, including namespace and build-order probe failures, are retained in ATTEMPTS; none remain.

## 4. Commands and results

All Lean commands ran after sourcing `scripts/lean-env.sh`, from `verification/`, with `LEAN_NUM_THREADS=6`.

- Dependency closure build: Energy, ForceSupport, T15.Mixed, Paper1.CorrectionMixedNorms — passed (10019 jobs).
- `lake build NSFormalization.Section3.T17.Mixed` — passed (10020 jobs).
- `lake env lean ../formalization/NSFormalization/Section3/T17/Mixed.lean` — exit 0, zero output.
- `lake env lean ../research/T17/probes/mixed_closes.lean` — exit 0; all six named declarations print exactly `[propext, Classical.choice, Quot.sound]`.
- `lake env lean ../research/T17/axioms_u10.lean` — exit 0; all four declarations print exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` — passed, including 13 policy tests and 45-item queue consistency.
- `lake test` (the `make test` target's Lean command, run from verification) — exit 0, 10911 jobs.
- `python3 experiments/test_contract_mutations.py` (`make test-mutations` target) — passed; all three mutations rejected.

No incomplete proofs, added axioms, native decision procedure, or heartbeat override. Nothing pushed, merged, or rebased.
