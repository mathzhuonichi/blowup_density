# U10 attempts (lane 444)

Successful route: continuous torus slices; force_eq; periodize single-copy equality on the closed cube; exponent-generic Haar/Lebesgue identity; restriction monotonicity in time; finite Paper1 constant. No mathematical residual.

## first

Section variables used only in proofs require include; eLpNorm_mono_measure takes the function first.

```text
../formalization/NSFormalization/Section3/T17/Mixed.lean:52:21: error(lean.unknownIdentifier): Unknown identifier `hv`
../formalization/NSFormalization/Section3/T17/Mixed.lean:52:29: error(lean.unknownIdentifier): Unknown identifier `δ`
../formalization/NSFormalization/Section3/T17/Mixed.lean:52:31: error(lean.unknownIdentifier): Unknown identifier `r`
../formalization/NSFormalization/Section3/T17/Mixed.lean:52:33: error(lean.unknownIdentifier): Unknown identifier `hvper`
../formalization/NSFormalization/Section3/T17/Mixed.lean:52:47: error(lean.unknownIdentifier): Unknown identifier `hθ`
../formalization/NSFormalization/Section3/T17/Mixed.lean:52:50: error(lean.unknownIdentifier): Unknown identifier `hη`
../formalization/NSFormalization/Section3/T17/Mixed.lean:52:53: error(lean.unknownIdentifier): Unknown identifier `hθc`
../formalization/NSFormalization/Section3/T17/Mixed.lean:52:57: error(lean.unknownIdentifier): Unknown identifier `hηc`
../formalization/NSFormalization/Section3/T17/Mixed.lean:52:61: error(lean.unknownIdentifier): Unknown identifier `hθsupp`
../formalization/NSFormalization/Section3/T17/Mixed.lean:52:68: error(lean.unknownIdentifier): Unknown identifier `hηsupp`
../formalization/NSFormalization/Section3/T17/Mixed.lean:53:6: error(lean.unknownIdentifier): Unknown identifier `hr2`
../formalization/NSFormalization/Section3/T17/Mixed.lean:53:10: error(lean.unknownIdentifier): Unknown identifier `hεtime`
../formalization/NSFormalization/Section3/T17/Mixed.lean:53:17: error(lean.unknownIdentifier): Unknown identifier `hεspace`
../formalization/NSFormalization/Section3/T17/Mixed.lean:70:52: error(lean.unknownIdentifier): Unknown identifier `hθsupp`
../formalization/NSFormalization/Section3/T17/Mixed.lean:70:59: error(lean.unknownIdentifier): Unknown identifier `hηsupp`
../formalization/NSFormalization/Section3/T17/Mixed.lean:69:28: error(lean.unknownIdentifier): Unknown identifier `hεspace`
../formalization/NSFormalization/Section3/T17/Mixed.lean:75:23: error(lean.unknownIdentifier): Unknown identifier `δ`
../formalization/NSFormalization/Section3/T17/Mixed.lean:75:35: error(lean.unknownIdentifier): Unknown identifier `hvper`
../formalization/NSFormalization/Section3/T17/Mixed.lean:75:69: error(lean.unknownIdentifier): Unknown identifier `hθsupp`
../formalization/NSFormalization/Section3/T17/Mixed.lean:75:76: error(lean.unknownIdentifier): Unknown identifier `hηsupp`
../formalization/NSFormalization/Section3/T17/Mixed.lean:76:6: error(lean.unknownIdentifier): Unknown identifier `hr2`
../formalization/NSFormalization/Section3/T17/Mixed.lean:76:16: error(lean.unknownIdentifier): Unknown identifier `hεspace`
../formalization/NSFormalization/Section3/T17/Mixed.lean:76:31: error(lean.unknownIdentifier): Unknown identifier `hεtime`
../formalization/NSFormalization/Section3/T17/Mixed.lean:82:57: error(lean.invalidField): Invalid field `trans`: The environment does not contain `Function.trans`, so it is not possible to project the field `trans` from an expression
  eLpNorm_mono_measure ?m.344
of type
  ?m.335 ≤ ?m.334 → eLpNorm ?m.344 ?m.333 ?m.335 ≤ eLpNorm ?m.344 ?m.333 ?m.334
../formalization/NSFormalization/Section3/T17/Mixed.lean:82:31: error: Application type mismatch: The argument
  Measure.restrict_le_self
has type
  Measure.restrict ?m.341 ?m.342 ≤ ?m.341
of sort `Prop` but is expected to have type
  ?m.331 → ?m.336
of sort `Type (max ?u.206 ?u.207)` in the application
  eLpNorm_mono_measure Measure.restrict_le_self

```

## second

Congruence before commuting factors produces the wrong equality.

```text
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
../formalization/NSFormalization/Section3/T17/Mixed.lean:88:2: error: unsolved goals
case e_a
ν : ℝ
v : SpaceTimeField
hv : ContDiff ℝ ∞ v
x₀ : Space
T δ r : ℝ
hvper : IsPeriodicOn univ v
θ : Space → ℝ
η : ℝ → ℝ
O : Set Space
θR ε₀ : ℝ
hθ : ContDiff ℝ ∞ θ
hη : ContDiff ℝ ∞ η
hθc : HasCompactSupport θ
hηc : HasCompactSupport η
hθsupp : tsupport θ ⊆ ball 0 θR
hηsupp : tsupport η ⊆ Ioo (-2) 2
hr2 : r < 1 / 2
hεtime : ∀ ε ∈ Ioc 0 ε₀, 2 * ε ^ 2 < min T δ
hεspace : ∀ ε ∈ Ioc 0 ε₀, ε * θR < r
hcube : closure (ball x₀ r) ⊆ interior fundamentalCube
hε₀ : ε₀ ≤ 1
p q : ℝ≥0∞
inst✝ : Fact (1 ≤ p)
a✝ : 1 ≤ q
ε : ℝ
hε : ε ∈ Ioc 0 (correctionData v x₀ T θ η O θR ε₀).ε₀
H : VelocityField := Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)
hH : Continuous H
hc : HasCompactSupport H
hs : ∀ (t : ℝ), (tsupport fun x => H (t, x)) ⊆ interior fundamentalCube
heq :
  ∀ (t : ℝ),
    0 ≤ t →
      (torusLift fun x => correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε (t, x)) =
        torusLift fun x => H (t, x)
hb :
  Classical.choose ⋯ < ∞ ∧
    ∀ ε ∈ Ioc 0 1,
      mixedNorm p q (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) ≤
        ENNReal.ofReal (ε ^ (-2 + 3 / p.toReal + 2 / q.toReal)) * Classical.choose ⋯
⊢ ENNReal.ofReal (ε ^ (-2 + p.toReal⁻¹ * 3 + q.toReal⁻¹ * 2)) = Classical.choose ⋯
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
../formalization/NSFormalization/Section3/T17/Mixed.lean:89:2: error: unsolved goals
case e_a
ν : ℝ
v : SpaceTimeField
hv : ContDiff ℝ ∞ v
x₀ : Space
T δ r : ℝ
hvper : IsPeriodicOn univ v
θ : Space → ℝ
η : ℝ → ℝ
O : Set Space
θR ε₀ : ℝ
hθ : ContDiff ℝ ∞ θ
hη : ContDiff ℝ ∞ η
hθc : HasCompactSupport θ
hηc : HasCompactSupport η
hθsupp : tsupport θ ⊆ ball 0 θR
hηsupp : tsupport η ⊆ Ioo (-2) 2
hr2 : r < 1 / 2
hεtime : ∀ ε ∈ Ioc 0 ε₀, 2 * ε ^ 2 < min T δ
hεspace : ∀ ε ∈ Ioc 0 ε₀, ε * θR < r
hcube : closure (ball x₀ r) ⊆ interior fundamentalCube
hε₀ : ε₀ ≤ 1
p q : ℝ≥0∞
inst✝ : Fact (1 ≤ p)
a✝ : 1 ≤ q
ε : ℝ
hε : ε ∈ Ioc 0 (correctionData v x₀ T θ η O θR ε₀).ε₀
H : VelocityField := Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)
hH : Continuous H
hc : HasCompactSupport H
hs : ∀ (t : ℝ), (tsupport fun x => H (t, x)) ⊆ interior fundamentalCube
heq :
  ∀ (t : ℝ),
    0 ≤ t →
      (torusLift fun x => correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε (t, x)) =
        torusLift fun x => H (t, x)
hb :
  Classical.choose ⋯ < ∞ ∧
    ∀ ε ∈ Ioc 0 1,
      mixedNorm p q (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) ≤
        ENNReal.ofReal (ε ^ (-2 + 3 / p.toReal + 2 / q.toReal)) * Classical.choose ⋯
⊢ Classical.choose ⋯ = ENNReal.ofReal (ε ^ (-2 + p.toReal⁻¹ * 3 + q.toReal⁻¹ * 2))

```

## build

First successful build emitted a ring diagnostic; replaced with explicit exponent equality for silent module checking.

```text
ℹ [10020/10020] Built NSFormalization.Section3.T17.Mixed (3.2s)
info: NSFormalization/Section3/T17/Mixed.lean:90:2: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Build completed successfully (10020 jobs).
```

## build2

Rewriting the exponent also enters the dependent Classical.choose proof.

```text
trace: .> LEAN_PATH=/data_8T/ping/blowup_density/verification/.lake/packages/Cli/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/batteries/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/Qq/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/aesop/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/proofwidgets/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/importGraph/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/plausible/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/lean4export/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/mathlib/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/Comparator/.lake/build/lib/lean:/data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/vendor/NavierStokesAndEuler/.lake/build/lib/lean:/data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/lib/lean:/data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/verification/.lake/build/lib/lean /data_8T/ping/blowup_density/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean /data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/NSFormalization/Section3/T17/Mixed.lean -o /data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/lib/lean/NSFormalization/Section3/T17/Mixed.olean -i /data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/lib/lean/NSFormalization/Section3/T17/Mixed.ilean -c /data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/ir/NSFormalization/Section3/T17/Mixed.c --setup /data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/ir/NSFormalization/Section3/T17/Mixed.setup.json --json
error: NSFormalization/Section3/T17/Mixed.lean:90:6: Tactic `rewrite` failed: motive is not type correct:
  fun _a => ENNReal.ofReal (ε ^ _a) * Classical.choose ⋯ = Classical.choose ⋯ * ENNReal.ofReal (ε ^ (alphaT p q + 1))
Error: Application type mismatch: The argument
  physical_force_mixed_bound ν hv x₀ T hθ hη hθc hηc p q
has type
  ∃ C < ∞,
    ∀ ε ∈ Ioc 0 1,
      mixedNorm p q (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) ≤
        ENNReal.ofReal (ε ^ (-2 + 3 / p.toReal + 2 / q.toReal)) * C
but is expected to have type
  ∃ x < ∞,
    ∀ ε ∈ Ioc 0 1,
      mixedNorm p q (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) ≤ ENNReal.ofReal (ε ^ _a) * x
in the application
  Classical.choose ⋯

Explanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that 'congrArg' implies that 'm a = m b', which can be used with lemmas such as 'Eq.mpr' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.

Possible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and 'Decidable' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well).

ν : ℝ
v : SpaceTimeField
hv : ContDiff ℝ ∞ v
x₀ : Space
T δ r : ℝ
hvper : IsPeriodicOn univ v
θ : Space → ℝ
η : ℝ → ℝ
O : Set Space
θR ε₀ : ℝ
hθ : ContDiff ℝ ∞ θ
hη : ContDiff ℝ ∞ η
hθc : HasCompactSupport θ
hηc : HasCompactSupport η
hθsupp : tsupport θ ⊆ ball 0 θR
hηsupp : tsupport η ⊆ Ioo (-2) 2
hr2 : r < 1 / 2
hεtime : ∀ ε ∈ Ioc 0 ε₀, 2 * ε ^ 2 < min T δ
hεspace : ∀ ε ∈ Ioc 0 ε₀, ε * θR < r
hcube : closure (ball x₀ r) ⊆ interior fundamentalCube
hε₀ : ε₀ ≤ 1
p q : ℝ≥0∞
inst✝ : Fact (1 ≤ p)
a✝ : 1 ≤ q
ε : ℝ
hε : ε ∈ Ioc 0 (correctionData v x₀ T θ η O θR ε₀).ε₀
H : VelocityField := Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)
hH : Continuous H
hc : HasCompactSupport H
hs : ∀ (t : ℝ), (tsupport fun x => H (t, x)) ⊆ interior fundamentalCube
heq :
  ∀ (t : ℝ),
    0 ≤ t →
      (torusLift fun x => correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε (t, x)) =
        torusLift fun x => H (t, x)
hb :
  Classical.choose ⋯ < ∞ ∧
    ∀ ε ∈ Ioc 0 1,
      mixedNorm p q (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) ≤
        ENNReal.ofReal (ε ^ (-2 + 3 / p.toReal + 2 / q.toReal)) * Classical.choose ⋯
hexp : -2 + 3 / p.toReal + 2 / q.toReal = alphaT p q + 1
⊢ ENNReal.ofReal (ε ^ (-2 + 3 / p.toReal + 2 / q.toReal)) * Classical.choose ⋯ =
    Classical.choose ⋯ * ENNReal.ofReal (ε ^ (alphaT p q + 1))
Some required targets logged failures:
- NSFormalization.Section3.T17.Mixed
error: build failed
```

## build3

Changing rpow notation alone does not prevent dependent rewriting; fixed using congrArg with the chosen constant fixed.

```text
trace: .> LEAN_PATH=/data_8T/ping/blowup_density/verification/.lake/packages/Cli/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/batteries/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/Qq/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/aesop/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/proofwidgets/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/importGraph/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/plausible/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/lean4export/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/mathlib/.lake/build/lib/lean:/data_8T/ping/blowup_density/verification/.lake/packages/Comparator/.lake/build/lib/lean:/data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/vendor/NavierStokesAndEuler/.lake/build/lib/lean:/data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/lib/lean:/data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/verification/.lake/build/lib/lean /data_8T/ping/blowup_density/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean /data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/NSFormalization/Section3/T17/Mixed.lean -o /data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/lib/lean/NSFormalization/Section3/T17/Mixed.olean -i /data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/lib/lean/NSFormalization/Section3/T17/Mixed.ilean -c /data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/ir/NSFormalization/Section3/T17/Mixed.c --setup /data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/ir/NSFormalization/Section3/T17/Mixed.setup.json --json
error: NSFormalization/Section3/T17/Mixed.lean:92:6: Tactic `rewrite` failed: motive is not type correct:
  fun _a => ENNReal.ofReal (ε ^ _a) * Classical.choose ⋯ = Classical.choose ⋯ * ENNReal.ofReal (ε ^ (alphaT p q + 1))
Error: Application type mismatch: The argument
  physical_force_mixed_bound ν hv x₀ T hθ hη hθc hηc p q
has type
  ∃ C < ∞,
    ∀ ε ∈ Ioc 0 1,
      mixedNorm p q (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) ≤
        ENNReal.ofReal (ε ^ (-2 + 3 / p.toReal + 2 / q.toReal)) * C
but is expected to have type
  ∃ x < ∞,
    ∀ ε ∈ Ioc 0 1,
      mixedNorm p q (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) ≤ ENNReal.ofReal (ε ^ _a) * x
in the application
  Classical.choose ⋯

Explanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that 'congrArg' implies that 'm a = m b', which can be used with lemmas such as 'Eq.mpr' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.

Possible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and 'Decidable' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well).

ν : ℝ
v : SpaceTimeField
hv : ContDiff ℝ ∞ v
x₀ : Space
T δ r : ℝ
hvper : IsPeriodicOn univ v
θ : Space → ℝ
η : ℝ → ℝ
O : Set Space
θR ε₀ : ℝ
hθ : ContDiff ℝ ∞ θ
hη : ContDiff ℝ ∞ η
hθc : HasCompactSupport θ
hηc : HasCompactSupport η
hθsupp : tsupport θ ⊆ ball 0 θR
hηsupp : tsupport η ⊆ Ioo (-2) 2
hr2 : r < 1 / 2
hεtime : ∀ ε ∈ Ioc 0 ε₀, 2 * ε ^ 2 < min T δ
hεspace : ∀ ε ∈ Ioc 0 ε₀, ε * θR < r
hcube : closure (ball x₀ r) ⊆ interior fundamentalCube
hε₀ : ε₀ ≤ 1
p q : ℝ≥0∞
inst✝ : Fact (1 ≤ p)
a✝ : 1 ≤ q
ε : ℝ
hε : ε ∈ Ioc 0 (correctionData v x₀ T θ η O θR ε₀).ε₀
H : VelocityField := Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)
hH : Continuous H
hc : HasCompactSupport H
hs : ∀ (t : ℝ), (tsupport fun x => H (t, x)) ⊆ interior fundamentalCube
heq :
  ∀ (t : ℝ),
    0 ≤ t →
      (torusLift fun x => correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε (t, x)) =
        torusLift fun x => H (t, x)
hb :
  Classical.choose ⋯ < ∞ ∧
    ∀ ε ∈ Ioc 0 1,
      mixedNorm p q (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) ≤
        ENNReal.ofReal (ε ^ (-2 + 3 / p.toReal + 2 / q.toReal)) * Classical.choose ⋯
hexp : -2 + 3 / p.toReal + 2 / q.toReal = alphaT p q + 1
⊢ ENNReal.ofReal (ε ^ (-2 + 3 / p.toReal + 2 / q.toReal)) * Classical.choose ⋯ =
    Classical.choose ⋯ * ENNReal.ofReal (ε ^ (alphaT p q + 1))
Some required targets logged failures:
- NSFormalization.Section3.T17.Mixed
error: build failed
```

## probe

Probe run after failed dependency build.

```text
../research/T17/probes/mixed_closes.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/lib/lean/NSFormalization/Section3/T17/Mixed.olean' of module NSFormalization.Section3.T17.Mixed does not exist

```

## probe2

Same dependency failure on the next attempt.

```text
../research/T17/probes/mixed_closes.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/444-T17-U10-mixed-bound/formalization/.lake/build/lib/lean/NSFormalization/Section3/T17/Mixed.olean' of module NSFormalization.Section3.T17.Mixed does not exist

```

## probe3

Incorrect namespace opens and periodicity binder count.

```text
../research/T17/probes/mixed_closes.lean:10:35: error(lean.unknownIdentifier): Unknown constant `NSFormalization.Section4.I02.spatialDivergence`
../research/T17/probes/mixed_closes.lean:58:6: error(lean.unknownIdentifier): Unknown identifier `interior_fundamentalCube`
../research/T17/probes/mixed_closes.lean:54:72: error: unsolved goals
y : Space
hy : y ∈ closure (ball cubeCentre (1 / 4))
hyc : y ∈ closedBall cubeCentre (1 / 4)
hnorm : ‖y - cubeCentre‖ ≤ 1 / 4
⊢ y ∈ interior fundamentalCube
../research/T17/probes/mixed_closes.lean:99:4: error: Tactic `rfl` failed: Expected the goal to be a binary relation

Hint: Reflexivity tactics can only be used on goals of the form `x ~ x` or `R x x`

θR : ℝ
θ : Space → ℝ
O : Set Space
hθR : 0 < θR
hθsm : ContDiff ℝ ∞ θ
hθcs : HasCompactSupport θ
hθsupp : tsupport θ ⊆ ball 0 θR
hOopen : IsOpen O
hKO : ∅ ⊆ O
hθone : EqOn θ (fun x => 1) O
hθrange : ∀ (x : Space), θ x ∈ Icc 0 1
η : ℝ → ℝ
hηsm : ContDiff ℝ ∞ η
hηcs : HasCompactSupport η
hηrange : ∀ (t : ℝ), η t ∈ Icc 0 1
hηone : EqOn η (fun x => 1) (Icc (-1) 1)
hηsupp : tsupport η ⊆ Ioo (-2) 2
ε₁ : ℝ
hε₁pos : 0 < ε₁
hεtime₁ : ∀ ε ∈ Ioc 0 ε₁, 2 * ε ^ 2 < min 1 1
hεspace₁ : ∀ ε ∈ Ioc 0 ε₁, ε * θR < 1 / 4
v : SpaceTimeField := fun x => coordinateVector 0
hv : ContDiff ℝ ∞ v
hvdiv : ∀ (t : ℝ) (x : Space), spatialDivergence v t x = 0
hvne : v ≠ 0
z : ℝ
a✝ : z ∈ univ
k : Space
⊢ ∀ (i : Fin 3), v (z, k + coordinateVector i) = v (z, k)

```

## probe4

Remaining incorrect spatialDerivative namespace.

```text
../research/T17/probes/mixed_closes.lean:10:35: error(lean.unknownIdentifier): Unknown constant `NSFormalization.Section4.I02.spatialDerivative`

```

