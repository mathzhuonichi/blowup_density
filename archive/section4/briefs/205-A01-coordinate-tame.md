# Lane 205-A01-coordinate-tame — `CylinderCoordinateTame`: the per-coordinate cylinder Kato–Ponce/Moser estimate for compatible finite Sobolev elements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/205-A01-coordinate-tame` (git branch `erenup/205-A01-coordinate-tame`, based on branch `erenup/202-A01-commutator-bound`
= `origin/erenup/integration` + lane 202's `Section4/A01/CommutatorBound.lean` (`cylinderCoordinateCommutator`, `cylinderWordGradient`, `def CylinderCoordinateTame q hq C`,
`cylinderCommutator_eq_sum`, `cylinderCoordinateCommutator_empty`, `cylinderCommutator_le`, `cylinderCommutatorBound_exists` — all conditional on the coordinate tame estimate)).
On integration: lane 200 (`ForcingFamilyBound.lean`: `cylinderCommutator`, `def A q`, `forcingFamilyBound_of_cylinder`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7,
`research/A01/REPORT_202.md` (§3: the exact statement, verbatim below), `research/A01/ATTEMPTS_COMMUTATOR_BOUND.md` (the ordinary/cylinder mismatch and negative examples),
`research/A01/REVIEW_200-A01-forcing-bound.md` §3 (route; vendor lemma names with file:line) and `REVIEW_202-…md` when present, the vendor's `AsymmetricTransport.lean`,
`TransportL2Time.lean`, `H6NonlinearProduct.lean:146` (`fieldDerivative_smul`), `BaseTransportCommutator.lean:48` (`scalarCommutator_recurrence`),
`ExternalTransportCommutator.lean:18, :38` (`word_derivative_comm`, `transportCommutator_eq_sum`), `OrdinaryTameProduct.lean:63, :83` (`coordinateProduct_tame`,
`tame_outer_product`), `OrdinaryWordInterpolation.lean:52` (`wordMaximum_product_le`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on zero data.
- **Satisfiability rule:** if one genuinely missing analytic fact remains, isolate it as ONE named hypothesis with the exact statement; never label a candidate constant
  as a proved Kato–Ponce constant.

## Target (lane 202, verbatim)
```lean
CylinderCoordinateTame q hq C :=
  ∀ (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)), restrictOperator 1 _ V = v →
    ∀ i : Fin 4, familyNorm (cylinderCoordinateCommutator hq v V i) ≤ C * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖ * cylinderWordGradient V
```
Deliver first the existential `∃ C, CylinderCoordinateTame q hq C` (then `cylinderCommutatorBound_exists` closes); then either an explicit `C ≤ 4·A q` (keeping lane 200's
API) or the honest re-cut (`A' q := max (A q) (C/4)`, with the one-line lemma that lane 200's chain accepts it). **Angular-invariant re-cut allowed:** the competitors
(lane 192's `hpairs`) satisfy `sobolevTranslation … (0,θ) u = u` (angular invariance); if the estimate is only reachable on the ordinary-lift subspace, re-cut
`CylinderCoordinateTame` to angular-invariant `v, V` and prove that lane 202/200's chain only ever applies it to such elements (say exactly where).

## Route
Leibniz expansion of each word of the coordinate commutator (`fieldDerivative_smul`, `scalarCommutator_recurrence`, `word_derivative_comm`, `transportCommutator_eq_sum`):
every nonempty word puts at least one derivative on the coefficient `v` and the rest on `V`, or vice versa; bound each mixed product by a cylinder tame/interpolation
lemma (transplant `coordinateProduct_tame` / `tame_outer_product` / `wordMaximum_product_le` from ordinary smooth carriers to the cylinder — or, via the angular-invariant
re-cut, descend to R³ where A03's `tameProductScalar` (`ScalarTameProduct.lean:254`) and `outerProductTame` (`OuterTameProduct.lean:177`) apply, with the `L²`
descent lemmas of lanes 153/161 preserving restriction); pass by smoothing/density to compatible finite Sobolev elements; sum the word family; identify the exact gradient
norm `cylinderWordGradient V`.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/CoordinateTame.lean` (namespace `NSFormalization.Section4.A01`): the Leibniz expansion, the cylinder (or
   descended) tame lemma, `cylinderCoordinateTame_exists`, `cylinderCoordinateTame` (explicit or re-cut), and the compositions closing `cylinderCommutatorBound` and
   `forcingFamilyBound_of_cylinder'`.
2. Records `research/A01/ATTEMPTS_COORDINATE_TAME.md`, update `research/A01/A3_SPLIT.md` A3-M2 sub-row "forcing bound", conformance `research/A01/axioms_coordinate_tame.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.CoordinateTame` (silent), `lake env lean` on the module (0 output), the axioms file,
`make check` from the worktree root.

## Report
Commit on your branch; end with four parts. Also write it to `research/A01/REPORT_205.md`.
