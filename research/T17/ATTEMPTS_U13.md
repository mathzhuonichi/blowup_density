# U13 attempts

Route decision: neither (i) nor (ii) can prove the unchanged statement.
`CorrectionAPI.reference_periodic : IsPeriodicOn univ v` is an independent,
global obligation. Agreement in the correction window cannot transfer it.
The counterexample is zero at nonnegative times and the spatial identity at
negative times. It is smooth and periodic on every classical slab, and
has zero divergence at every positive time, but fails periodicity at t = -1.

First compilation of the counterexample used `contDiffOn_const.congr` without
specifying the constant. Exact error:
```
../formalization/NSFormalization/Section3/T17/SlabBridge.lean:37:79: error: unsolved goals
S : ℝ
z : SpaceTime
hz : z ∈ Ico 0 S ×ˢ univ
⊢ 0 = ?m.29

S : ℝ
⊢ Space
```
Fixed by specifying `(c := (0 : Space))`.

Exact residual field: `IsPeriodicOn univ v`, i.e.
`∀ t ∈ univ, ∀ x : Space, ∀ i : Fin 3,
v (t, x + coordinateVector i) = v (t, x)`.
The missing implication from slab periodicity and slab smoothness is false,
not an unproved analytic lemma. `not_correctionStatementSlab` proves this
for the complete requested quantifier block, including all geometry premises.
A T17 V2 with slab-relative reference periodicity, or a conclusion about an
extended reference instead of the original velocity, is required. This
counterexample does not show that T16 needs a V2.

Repository discrepancy: `grep -rn 'G5' research/T17` returned no matches;
the supplied G5 discussion is in the lane brief but not SPEC_ISSUES.md.
The canonical `localPotentialAPI` theorem is in T16/Assembly.lean, not
T16/LocalPotential.lean. No existing file is edited; the split status is
recorded in the new T17_SPLIT_U13.md to respect the new-files-only rule.
