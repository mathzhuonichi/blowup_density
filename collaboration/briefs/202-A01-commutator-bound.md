# Lane 202-A01-commutator-bound — `CylinderCommutatorBound`: the cylinder word-commutator (Kato–Ponce/Moser) estimate for compatible finite Sobolev elements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/202-A01-commutator-bound` (git branch `erenup/202-A01-commutator-bound`, based on branch
`erenup/200-A01-forcing-bound` = `origin/erenup/integration` + lane 200's `Section4/A01/ForcingFamilyBound.lean` (`def cylinderCommutator`, `def CylinderCommutatorBound q hq`,
`def E q`, `def A q`, `forcingFamilyBound_of_cylinder (hcomm : CylinderCommutatorBound q hq) : ForcingFamilyBound …`); lane 200 is landing, its defs will not change).
Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7, `research/A01/REPORT_200.md` §3 (the exact statement), `research/A01/REVIEW_200-A01-forcing-bound.md` §3
(analytic assessment and the concrete route — verbatim below), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules;
  new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on zero data.
- **Satisfiability rule:** if one genuinely missing analytic fact remains, isolate it as ONE named hypothesis with the exact statement; do not label a
  candidate constant as a proved Kato–Ponce constant.

## Statement (lane 200, verbatim)
```lean
def CylinderCommutatorBound (q : ℕ) (hq : 6 ≤ q) : Prop :=
  ∀ (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)),
    restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v →
    familyNorm (cylinderCommutator hq v V) ≤
      A q * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖) *
        Real.sqrt (∑ i : Fin 4, ∑ w : SobolevWord (q+1),
          ‖(derivativeOperator 1 (q+1) i (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V)).val w‖^2)
```
Pure spatial estimate on the four-dimensional cylinder (angle + three spatial directions; `Fin 4` is correct), quadratic under `(v,V) ↦ (λv,λV)`, low norm at
order 7 with the first power, no divergence-freeness needed.

## Route (reviewer 200, verbatim)
Start with the actual maps `asymmetricTransport_apply` (vendor `AsymmetricTransport.lean:27`) and `transportL2Bilinear`/`transportL2Bilinear_apply`
(`TransportL2Time.lean:23, :30`). Expand each word using `fieldDerivative_smul` (`H6NonlinearProduct.lean:146`) and `scalarCommutator_recurrence`
(`BaseTransportCommutator.lean:48`); `word_derivative_comm` and `transportCommutator_eq_sum` (`ExternalTransportCommutator.lean:18, :38`) give the exact
transport identity (empty-word commutator vanishes; every other word has a derivative on the coefficient and on the transported field). Bound the mixed
derivative products with a **cylinder** tame/interpolation lemma: A03's `tameProductScalar` (`ScalarTameProduct.lean:254`) and `outerProductTame`
(`OuterTameProduct.lean:177`) are R³ datum estimates — using them requires a proved cylinder extension or restricting the hypothesis to the ordinary-lift
subspace and proving that restriction for competitors (one cannot silently descend arbitrary angular-dependent `V` to R³). The vendor's
`coordinateProduct_tame`, `tame_outer_product` (`OrdinaryTameProduct.lean:63, :83`) and `wordMaximum_product_le` (`OrdinaryWordInterpolation.lean:52`) are
useful interpolation models with ordinary smooth carriers: prove the cylinder version and pass by smoothing/density to compatible finite Sobolev elements,
preserving restriction. Sum the full word family and identify the exact gradient norm. **First prove an existential finite `C q`**
(`∃ C, ∀ v V, … ≤ C * ‖v|₇‖ * ‖∇V‖_{words}`), then either derive an explicit `C` and prove `C ≤ 16 * A q` (keeping lane 200's API), or export
`CylinderCommutatorBound` for a re-cut `A' q := max (A q) (C/16)` with a one-line lemma showing lane 200's chain accepts the larger constant (say which).

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/CommutatorBound.lean` (namespace `NSFormalization.Section4.A01`): the cylinder tame/interpolation
   lemma(s), the word-commutator expansion, `cylinderCommutatorBound_exists : ∃ C, …`, and `cylinderCommutatorBound : CylinderCommutatorBound q hq` (or the
   re-cut variant), plus the unconditional corollary `forcingFamilyBound_of_cylinder'` composing with lane 200.
2. Records `research/A01/ATTEMPTS_COMMUTATOR_BOUND.md` (negative examples), update `research/A01/A3_SPLIT.md` A3-M2 sub-row "forcing bound", conformance
   `research/A01/axioms_commutator_bound.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.CommutatorBound` (silent), `lake env lean` on the module (0 output), the axioms
file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constants / files / gaps with error text / commands). Also write it to
`research/A01/REPORT_202.md`.
