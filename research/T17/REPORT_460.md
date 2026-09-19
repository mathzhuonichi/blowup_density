# Lane 460 / T17 U13

## 1. Theorem and exact statement

The requested theorem is false. Proved instead:

```lean
theorem not_correctionStatementSlab : ¬ correctionStatementSlab
```

Here the proposition is exactly:

```lean
def correctionStatementSlab : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ → IsPeriodicOn (Ico (0 : ℝ) (place.T + δ)) v →
    ContDiffOn ℝ ∞ v (Ico (0 : ℝ) (place.T + δ) ×ˢ (univ : Set Space)) →
    (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ ball place.x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place v r δ D)
```

The witness is `slabCounterexample (t,x) = if 0 ≤ t then 0 else x`,
with `Nonvacuity.place`, ν = 1, r = 1/4, δ = 1, and zero packet fields.
All antecedents hold, including smoothness at zero *within* the slab.
At t = -1, x = 0, i = 0, global periodicity would say e₀ = 0.
This is a kernel-checked refutation of the whole requested statement,
not a structure of replacement goals.

## 2. Files

- `formalization/NSFormalization/Section3/T17/SlabBridge.lean`: exact definition,
  explicit counterexample, its slab periodicity/smoothness/divergence proofs,
  nonperiodicity, and the negation theorem.
- `research/T17/probes/slab_from_classical.lean`: **negative** regression probe;
  the requested successful arbitrary-classical-reference probe is not supplied.
- `research/T17/axioms_u13.lean`: all seven declarations audited; every output
  is exactly `[propext, Classical.choice, Quot.sound]`.
- `research/T17/ATTEMPTS_U13.md`: route decision, exact compilation failure,
  fix, residual and repository discrepancies.
- `research/T17/T17_SPLIT_U13.md`: U13 status in a new companion file, because
  the ground rules forbid editing existing files.
- `research/T17/REPORT_460.md`: this report.

No existing module, contract, binding, test, or record was changed.
The pre-existing untracked lane brief is excluded from the commit.

## 3. Gaps and error text

Exact impossible field: `CorrectionAPI.reference_periodic : IsPeriodicOn univ v`.
`IsPeriodicOn` is genuinely set-relative in its time argument; using `univ`
requires every real time, whereas the classical field uses `Ico 0 (T+δ)`.
Neither cutoff route (i) nor direct-profile route (ii) can transfer global
periodicity back to the unchanged original v. A T17 V2 with slab-relative
reference periodicity, or an extended-reference conclusion, is necessary.
No `correctionStatementSlab_holds`, `localPotentialAPI_slab`, or completed
analytic field transfer is claimed. This obstruction does not establish a
need for T16 V2.

The sole Lean proof-development failure was:
```
../formalization/NSFormalization/Section3/T17/SlabBridge.lean:37:79: error: unsolved goals
S : ℝ
z : SpaceTime
hz : z ∈ Ico 0 S ×ˢ univ
⊢ 0 = ?m.29

S : ℝ
⊢ Space
```
It was resolved by specifying the zero constant in `contDiffOn_const`.
The final module has no errors or output when elaborated directly.

## 4. Commands and results

The explicit Lean build/elaboration commands use the sourced
`scripts/lean-env.sh`, run from `verification/`, and set `LEAN_NUM_THREADS=6`.
The repository mutation script also invokes Lake from `verification/`.

- `lake build NSFormalization.Section3.T17.Assembly`: exit 0, 10032 jobs.
- `lake build NSFormalization.Section3.T17.SlabBridge`: exit 0, 10033 jobs;
  existing dependency warnings replayed, new module clean.
- `lake env lean ../formalization/NSFormalization/Section3/T17/SlabBridge.lean`:
  exit 0, zero output.
- `lake env lean ../research/T17/probes/slab_from_classical.lean`:
  exit 0, zero output (negative probe).
- `lake env lean ../research/T17/axioms_u13.lean`: exit 0; exactly the standard
  three axioms for every declaration.
- `lake test`: exit 0.
- `make check`: passed (48 registered contracts); existing informational
  source-manifest/copy-token diagnostics remain in the check output.
- `python3 experiments/test_contract_mutations.py`: exit 0; all four mutation
  cases behaved as required.
- `git diff --check`: exit 0.
