# Lane 206-A01-smooth-tame — `SmoothCylinderCoordinateTame`: the per-coordinate mixed-product tame estimate for smooth cylinder fields (the last analytic input of A3-M2)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/206-A01-smooth-tame` (git branch `erenup/206-A01-smooth-tame`, based on branch `erenup/205-A01-coordinate-tame`
= `origin/erenup/integration` + lane 205's `Section4/A01/CoordinateTame.lean` (`def SmoothCylinderCoordinateTame q hq C`, the smooth Leibniz expansion
`cylinderLeibniz_eq`/`cylinderCommutatorLeibniz_eq`/`cylinderCoordinateLeibniz_sign`, the transfer `cylinderCoordinateTame (h : SmoothCylinderCoordinateTame q hq C) :
CylinderCoordinateTame q hq C`, `cylinderCoordinateTame_exists`)). On integration: lane 202 (`CommutatorBound.lean`), 200 (`ForcingFamilyBound.lean`: `def A q`,
`forcingFamilyBound_of_cylinder`), 204 (`SignedPassage.lean`: the envelope side is unconditional), 196 (`MildGronwall.lean`: word-norm comparisons
`mildNormConstant`), A03 (`Section4/A03/ScalarTameProduct.lean:254` `tameProductScalar`, `OuterTameProduct.lean:177` `outerProductTame`, `VectorTameProduct.lean`),
lanes 153/161 (`L2Descent.lean`, `DatumPathContinuous.lean`: descent of cylinder data to R³ data preserving restriction), 192 (`CylinderWiring.lean`: competitors carry
angular invariance `hinv : sobolevTranslation … (0,θ) u = u`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7, `research/A01/REPORT_205.md` (§3: exact
statement, verbatim below), `research/A01/ATTEMPTS_COORDINATE_TAME.md` and `ATTEMPTS_COMMUTATOR_BOUND.md` (the ordinary/cylinder mismatch), `research/A01/REVIEW_200-A01-forcing-bound.md`
§3 (route + vendor names: `coordinateProduct_tame`, `tame_outer_product` in `OrdinaryTameProduct.lean:63,:83`, `wordMaximum_product_le` in `OrdinaryWordInterpolation.lean:52`),
and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on zero data (never as certification of a general premise).
- **Satisfiability rule:** if one genuinely missing analytic fact remains, isolate it as ONE named hypothesis with the exact statement; do not label a candidate constant
  as a proved Kato–Ponce constant.

## Target (lane 205, verbatim)
```lean
SmoothCylinderCoordinateTame q hq C :=
  ∀ (V : SobolevSpace 1 (2+q)) (f : LiftDomain 1 → Vector3),
    (value 1 V : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f →
    (∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x)) →
    (∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative 1 w f) 2 (liftMeasure 1)) →
    ∀ i : Fin 4, familyNorm (cylinderCoordinateCommutator hq (restrictOperator 1 _ V) V i) ≤
      C * ‖restrictOperator 1 (Nat.succ_le_succ hq) (restrictOperator 1 _ V)‖ * cylinderWordGradient V
```

## Route — try the DESCENT first (it may turn the last analytic input into wiring)
1. **Angular-invariant re-cut.** The only elements the forcing chain ever applies the bound to are the competitors' words (lane 192's `hpairs`: `sobolevTranslation 1 (q+1) (0,θ) u = u`,
   and their maximal-regularity states). Check the call sites (`ForcingFamilyBound.lean`, `CommutatorBound.lean`, `CoordinateTame.lean`) and, if they only need angular-invariant
   `V`, define `SmoothCylinderCoordinateTameInv` (same statement with `∀ θ, sobolevTranslation … (0,θ) V = V`) and prove that lane 205's transfer and lane 202's chain accept it
   (a one-line lemma per consumer, or a re-cut of `cylinderCoordinateTame` to the invariant class). Say exactly which consumer needs what.
2. **Descent to R³.** For angular-invariant smooth `f`, the angle derivative is zero and every word reduces to spatial words (`Fin 3`); the cylinder norms are the R³ norms times
   the angle period (lanes 153/161's descent lemmas, `value_restrictOperator`, `word_descent_ae_top/full`). Then the mixed products are exactly the R³ tame products of A03
   (`tameProductScalar`, `outerProductTame`, `VectorTameProduct`) with the low factor at order 7 (order-two cap shape `16·‖·‖`): prove `SmoothCylinderCoordinateTameInv q hq C`
   with `C` explicit from A03's constants and lane 196's `mildNormConstant`, hence `CylinderCoordinateTame` (invariant class) ⇒ `CylinderCommutatorBound` ⇒ `ForcingFamilyBound`
   ⇒ (with 204) `FiniteMildEnergy` ⇒ `hb`. Export `hb_of_base'''`/the unconditional family and the A01 milestone probe `a01_constructor_unconditional` (import
   `PressureRegularity`/`ConstructorAssembly`: the classical constructor with **no** analytic hypothesis besides `hf`, `ha`, positivity).
3. **Fallback (only if the descent is blocked):** prove the genuine cylinder interpolation (vendor `coordinateProduct_tame`/`tame_outer_product`/`wordMaximum_product_le`
   transplanted with the angle direction as a fourth coordinate), or isolate the exact missing R³ tame inequality as the single named input.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/SmoothTame.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_SMOOTH_TAME.md` (negative examples), update `research/A01/A3_SPLIT.md` A3-M2 rows (final status), conformance `research/A01/axioms_smooth_tame.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.SmoothTame` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`
from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constants / files / gaps with error text / commands). Also write it to `research/A01/REPORT_206.md`.
