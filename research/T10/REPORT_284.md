# Report 284 — T10 physical bridge

## 1. Theorems and exact statements

The three `TorusDataAPI` physical-layer fields are proved verbatim:

```lean
theorem torusLift_injective :
    ∀ z w : SpatialField, IsPeriodicSpatial z → IsPeriodicSpatial w →
      torusLift z = torusLift w → z = w

theorem torusLift_surjective :
    ∀ Z : PeriodicTorus → Space,
      ∃ z : SpatialField, IsPeriodicSpatial z ∧ torusLift z = Z

theorem mean_decomposition :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      Integrable (torusLift z) periodicTorusMeasure →
        (∀ x : Space, constantPartT z x + meanZeroPartT z x = z x) ∧
          IsMeanZeroT (meanZeroPartT z)
```

Four reusable physical bridge lemmas are also proved:

```lean
theorem periodic_shift_int {E : Type*} [Add E] {z : Space → E}
    (hz : IsPeriodicSpatial z) (x : Space) (k : Fin 3 → ℤ) :
    z (x + ∑ i, (k i : ℝ) • coordinateVector i) = z x

theorem torusLift_apply_of_periodic {E : Type*} [Add E] {z : Space → E}
    (hz : IsPeriodicSpatial z) (x : Space) :
    torusLift z (fun i ↦ (x i : UnitAddCircle)) = z x

theorem isPeriodicSpatial_torusLift_comp {E : Type*} [Add E]
    (Z : PeriodicTorus → E) :
    IsPeriodicSpatial (fun x : Space ↦ Z (fun i ↦ (x i : UnitAddCircle)))

theorem meanT_const (c : Space) : meanT (fun _ : Space ↦ c) = c
```

## 2. Files

- `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean` contains all
  seven proofs.  It reuses the canonical definitions without modifying
  `PeriodicData.lean`.
- `research/T10/probes/physical_bridge_closes.lean` checks the three field
  statements verbatim, checks all four bridge signatures, and gives a concrete
  zero-field non-vacuity example.
- `research/T10/axioms_physical_bridge.lean` audits every theorem.
- `research/T10/ATTEMPTS_PHYSICAL_BRIDGE.md` records the repository search,
  successful route, and exact failed diagnostics.
- `research/T10/REPORT_284.md` is this report.

## 3. Gaps and diagnostics

There is no mathematical or interface gap and no residual named hypothesis.
The exact transient build/elaboration diagnostics are recorded in
`ATTEMPTS_PHYSICAL_BRIDGE.md`; all were resolved.  No existing module was
edited, no heartbeat override was required, and no prohibited proof primitive
is present.

The key reuse is `Paper1.unitPeriods_integer_translate` and
`Paper1.torusLift_coe_of_unitPeriods` from
`Paper1/FourierReconstructionAdapter.lean`.  The new theorem names expose those
facts in T10 vocabulary.  Surjectivity is constructive, and mean zero follows
from Bochner integral subtraction plus normalized Haar mass one.

## 4. Commands and results

- From `verification/`,
  `. ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.PhysicalBridge`:
  passed (`9355/9355` jobs); output only replayed existing dependency warnings.
- From `verification/`, `lake env lean` on `PhysicalBridge.lean` and
  `physical_bridge_closes.lean`: passed with zero output.
- From `verification/`, `lake env lean` on
  `axioms_physical_bridge.lean`: passed; every declaration printed exactly
  `[propext, Classical.choice, Quot.sound]`.
- From the worktree root, `. scripts/lean-env.sh && make check`: passed; 13
  policy tests and all 45 work items were consistent.  The informational
  manifest retains the repository baseline's copied-source `source_hashes_match:
  false` and existing `Paper1/BoundaryCorollary.lean:90` token; this lane did
  not modify either source.
- `git diff --check` and the prohibited-token scan over the three Lean
  deliverables: passed.
