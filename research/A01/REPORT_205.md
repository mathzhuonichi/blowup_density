# REPORT 205 — smooth-to-finite coordinate tame transfer (partial)

## 1. What is proved

**The unconditional existential requested for lane 205 remains open.** This is
a partial delivery under the single-named-hypothesis exception, not a proved
cylinder Kato–Ponce constant.

The new module proves the full recursive Leibniz expansion on smooth cylinder
fields (`cylinderLeibniz_eq`), its commutator cancellation
(`cylinderCommutatorLeibniz_eq`), and the transport-minus-product sign
(`cylinderCoordinateLeibniz_sign`). It also proves continuity of the actual
finite coordinate commutator and the exact `cylinderWordGradient`.

The principal transfer theorem is, with no loss of constant:

```lean
cylinderCoordinateTame (hq : 6 ≤ q)
  (h : SmoothCylinderCoordinateTame q hq C) : CylinderCoordinateTame q hq C
```

`smoothCylinderCoordinateTame_iff` proves the converse as well. The proof uses
actual smooth H-infinity heat/mollifier approximation. The low field is
restricted from the same approximated high field, so compatibility is exact.
There is no remaining finite-order limit-passage premise.

`cylinderCoordinateTame_exists` is explicitly conditional:

```lean
(∃ C : ℝ, SmoothCylinderCoordinateTame q hq C) →
  ∃ C : ℝ, CylinderCoordinateTame q hq C
```

The numerical recut is `coordinateTameA q C := max (A q) (C/4)`.
`coordinateTameA_absorbs` proves `C ≤ 4 * coordinateTameA q C`, and
`cylinderCommutatorBound_recut` proves, assuming the smooth estimate,

```text
familyNorm (cylinderCommutator hq v V)
  ≤ coordinateTameA q C * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖)
      * cylinderWordGradient V
```

`forcingFamilyBound_of_cylinder_recut` then supplies the unchanged lane-200
predicate `ForcingFamilyBound hq hν a F hF (E q) (coordinateTameA q C)`.
For the old fixed A, `cylinderCommutatorBound_of_smooth` and
`forcingFamilyBound_of_smooth` compose with lane 202's original theorems,
assuming `SmoothCylinderCoordinateTame q hq (4*A q)`.

## 2. What is in Lean and in the records

* New `formalization/NSFormalization/Section4/A01/CoordinateTame.lean`:
  18 public definitions/theorems, all audited.
* New `research/A01/axioms_coordinate_tame.lean`: prints every public
  declaration's axioms and checks compatible zero coordinate/full-family
  inequalities without assuming a universal tame estimate.
* New `research/A01/ATTEMPTS_COORDINATE_TAME.md`: positive steps, exact scope,
  source-interface checks, rejected substitutions, and elaboration diagnostics.
* Updated only the requested forcing-bound sub-row of `research/A01/A3_SPLIT.md`.
* This four-part report, `research/A01/REPORT_205.md`.

No existing Lean module, vendor source, or verification module was edited.
No push, merge, or rebase was performed. No angular-invariant recut is claimed.

## 3. The remaining gap, exactly

The ONE analytic hypothesis `SmoothCylinderCoordinateTame q hq C` is:

```lean
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

Its uniform constant is not supplied. The smooth mixed-product interpolation
estimate, its identification with the finite product words, and certification
of C remain inside this single input. The smooth Leibniz identity is proved
separately; no a.e. finite-word identification theorem is claimed.

Ordinary R³ tame results have Fin 3 words and different carriers; the general
cylinder estimate includes angular dependence. The available cylinder
high-times-high bounds do not replace the high coefficient norm by the fixed
order-seven low norm. `A q` and `coordinateTameA q C` are numerical candidates
until the corresponding smooth estimate is supplied. The zero examples do
not establish the universal analytic hypothesis for nonzero fields.

## 4. Commands and results

Lean commands sourced `. scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
ran Lake only from `verification/`. Logs are local untracked `tmp/*205*.log`.

* `lake build NSFormalization.Section4.A01.CoordinateTame`: exit 0.
  The new module has no diagnostics. Standard Lake output replays existing
  upstream warnings and prints its success banner; this is **not a literally
  silent standard Lake build**.
* `lake env lean ../formalization/NSFormalization/Section4/A01/CoordinateTame.lean`:
  exit 0, exactly 0 output bytes.
* `lake env lean ../research/A01/axioms_coordinate_tame.lean`: exit 0.
  All 18 public declarations print exactly the axiom set
  `[propext, Classical.choice, Quot.sound]`; the zero examples pass.
* `make check` at the worktree root: exit 0.
* `make test`: exit 0, registered contract suite.
* `make test-mutations`: exit 0; the three invalid mutations were rejected,
  and the implementation refactor was accepted.
* `git diff --check`: exit 0.

No prohibited proof commands or new logical assumptions were introduced.
The two heartbeat settings are declaration-local, commented, and 400000.
Local irreducibility attributes prevent elaboration from unfolding the
analytic product constructions; they do not change definitions or kernel proofs.
