# REPORT 202 — finite coordinate expansion; analytic estimate still open

## 1. Theorems with exact statements and constants

This is a partial delivery under the satisfiability rule. It does not prove an
unconditional cylinder Kato–Ponce estimate or unconditional forcing bound.
All declarations are in `NSFormalization.Section4.A01`.

Write `D_i(v,V) := cylinderCoordinateCommutator hq v V i`, the literal
scalar-product minus product-word family in the module, and

```lean
G(V) := Real.sqrt (∑ i : Fin 4, ∑ w : SobolevWord (q+1),
  ‖(derivativeOperator 1 (q+1) i
    (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V)).val w‖^2)
L(v) := ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖
```

Here G is implemented as `cylinderWordGradient`; L is notation only in this
report. Exact theorem content:

* `cylinderCommutator_eq_sum`: for all finite v,V,
  `cylinderCommutator hq v V = ∑ i : Fin 4, D_i(v,V)`.
* `cylinderCoordinateCommutator_empty`: for all finite v,V,i,
  `D_i(v,V) (emptyWord (q+1)) = 0`.
* `cylinderCommutator_empty`: for all finite v,V,
  `cylinderCommutator hq v V (emptyWord (q+1)) = 0`.
* `cylinderCommutator_le`: assuming `CylinderCoordinateTame q hq C`, for every
  compatible v,V, `familyNorm (cylinderCommutator hq v V) ≤ (4*C)*L(v)*G(V)`.
* `cylinderCommutatorBound_exists`: assuming
  `∃ C : ℝ, CylinderCoordinateTame q hq C`, concludes
  `∃ C : ℝ, ∀ v V, restrictOperator 1 _ V = v →
    familyNorm (cylinderCommutator hq v V) ≤ C*L(v)*G(V)`.
  The output witness is four times the input witness.
* `cylinderCommutatorBound`: `CylinderCoordinateTame q hq C → C ≤ 4*A q →
  CylinderCommutatorBound q hq`.
* `forcingFamilyBound_of_cylinder'`: for q,hq,ν,S,hν,a,F,hF with exactly
  lane 200's types, `CylinderCoordinateTame q hq (4*A q) →
  ForcingFamilyBound hq hν a F hF (E q) (A q)`.

No recut constant is claimed. The fixed constant remains
`A q = mildNormConstant q * (1 + A03.outerTameConst (q+1))`, a candidate.
The arithmetic factor four from coordinates is proved; no analytic constant
has been certified.

## 2. Files

* New `formalization/NSFormalization/Section4/A01/CommutatorBound.lean`.
* New `research/A01/ATTEMPTS_COMMUTATOR_BOUND.md`.
* New `research/A01/axioms_commutator_bound.lean`.
* New `research/A01/REPORT_202.md` (this report).
* Requested forcing-bound sub-row updated in `research/A01/A3_SPLIT.md`.

No existing Lean module was edited. The requested record update is the only
edit to an existing file. No push, merge or rebase was performed.

## 3. Gaps with error text

The ONE named analytic input for the fixed API is
`CylinderCoordinateTame q hq (4*A q)`, exactly:

```lean
∀ (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)),
  restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v →
  ∀ i : Fin 4, familyNorm (cylinderCoordinateCommutator hq v V i) ≤
    (4*A q) * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖ *
      cylinderWordGradient V
```

The missing work includes the mixed-product cylinder interpolation proof,
full Leibniz expansion and its identification/passage to finite elements,
and certification of a uniform constant. These are collected into the one
finite coordinate estimate, not represented as separately supplied premises.
The coordinate decomposition and empty-word cancellation are unconditional;
the existential constant and forcing theorem are conditional. Thus the main
unconditional deliverable remains open.

Resolved diagnostic: `error: Tactic rfl failed: The left-hand side ... is not
definitionally equal to the right-hand side ...` for closed-subspace sums.
An explicit linear-map sum identity fixed it. There is no remaining Lean error.
See ATTEMPTS for the ordinary/cylinder mismatch and negative examples.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`, ran from `verification/`,
and used `LEAN_NUM_THREADS=6`.

* `lake build NSFormalization.Section4.A01.CommutatorBound`: exit 0.
  Build log contains replayed upstream warnings and Lake's success banner;
  the new module has no diagnostics. This is not a literally silent Lake build.
* `lake env lean ../formalization/NSFormalization/Section4/A01/CommutatorBound.lean`:
  exit 0, exactly 0 output bytes.
* `lake env lean ../research/A01/axioms_commutator_bound.lean`: exit 0;
  all ten public declarations print exactly
  `[propext, Classical.choice, Quot.sound]`. Includes compatible zero data,
  coordinate and full-family zero inequalities, and a negative pairing example.
* `make check` from the worktree root: exit 0.
* `make test`: exit 0 (registered contract suite).
* `make test-mutations`: exit 0; all three infrastructure mutations rejected.
* `git diff --check`: exit 0.

Logs are worktree-local `tmp/{build,direct,axioms,check}_202.log` (untracked).
