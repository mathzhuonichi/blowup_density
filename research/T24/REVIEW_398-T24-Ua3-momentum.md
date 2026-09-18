ACCEPT

## What the lane claims

The lane claims the raw-field theorem `NSFormalization.Section3.T24.momentum`, proving the affine momentum identity for every admissible `b`, with force
`F + ∂ₜb − νΔb + (U·∇)b + (b·∇)U + (b·∇)b`. This is the paper’s proposition and equation (`paper/sections/03-torus.tex:668-696`, especially `:674-676`), and the registered field is `research/T24/Spec.lean:1047-1051`.

## What is in Lean

- The affine definitions are present in [AffineBasics.lean](/data_8T/ping/blowup_density/.claude/worktrees/398-T24-Ua3-momentum/formalization/NSFormalization/Section3/T24/AffineBasics.lean:18), with `AffineAdmissible` exactly as the Spec conjunction (`:23-27`), `affineVelocity`/`affinePressure` (`:30-37`), and the six-term `affineForce` (`:40-46`).
- The expansion lemma is [AffineMomentum.lean](/data_8T/ping/blowup_density/.claude/worktrees/398-T24-Ua3-momentum/formalization/NSFormalization/Section3/T24/AffineMomentum.lean:43-55). It explicitly uses additivity and bilinear advection; no placeholder or named input is used.
- `momentum` is [AffineMomentum.lean](/data_8T/ping/blowup_density/.claude/worktrees/398-T24-Ua3-momentum/formalization/NSFormalization/Section3/T24/AffineMomentum.lean:88-103). Its quantifier order is `∀ b`, admissibility, `∀ t ∈ Ioo 0 1`, `∀ x`; hypotheses are precisely raw `ContDiffOn` velocity smoothness and the packet residual identity. The proof consumes both hypotheses at `:105-121`.
- The registered-vocabulary probe discharges the canonical packet field at [affine_momentum_closes.lean](/data_8T/ping/blowup_density/.claude/worktrees/398-T24-Ua3-momentum/research/T24/probes/affine_momentum_closes.lean:46-61), and proves zero admissibility/non-vacuity at `:67-91`. The separate nonzero curl-bump probe compiles and prints standard axioms.
- Whole-tree Section 4 search found no missing affine momentum lemma; the hits are unrelated solution-structure momentum fields (`formalization/NSFormalization/Section4/R42/*`, `A02/*`).

## Gaps

No blocking gap. The theorem is conditional on the packet residual clause, as required by the raw-field import rule, and does not silently add positivity or pressure hypotheses. The cylinder parameters are not assumed positive in this standalone algebraic theorem, but admissibility is retained verbatim and the theorem itself does not need those inequalities.

Negative check: `research/T24/probes/rev398_negative.lean` flips the sign of `(b·∇)b`. Lean rejects the attempted equality with the substantive remaining goal `⊢ False`, displaying the two sides with `+ crossAdvection b b 0 0` versus `- crossAdvection b b 0 0` (rather than succeeding by dropped arguments).

## Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineMomentum`: `Build completed successfully (3007 jobs).`
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T24/AffineMomentum.lean`: exit 0, no errors.
- `lake env lean` on `affine_momentum_closes.lean`, `affine_momentum_nonzero.lean`, and `axioms_ua3.lean`: exit 0. Every printed declaration has exactly `[propext, Classical.choice, Quot.sound]`.
- `make check`: exit 0; architecture, contract-policy, and work-queue checks pass.
- `scripts/gates.sh NSFormalization.Section3.T24.AffineMomentum`: exit 0; mutation suite reports `extra_axiom: rejected as required`, `weakened_hypothesis: rejected as required`, `Mutation suite passed`, and `check_contracts` passes.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`: exit 0 with `base_compatibility_checked: true`.
- `git diff --name-only origin/erenup/integration-section3...HEAD`: only the lane’s new module and research artifacts are listed; no existing module is modified.
- Hygiene grep over the lane module/probes found no `sorry`, `admit`, `native_decide`, or declaration-level `axiom`; no `maxHeartbeats` is present.
