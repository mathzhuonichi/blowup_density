ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed HEAD `f8d9d930e192f852c3901beabfcb3fcbde107191` against local remote-tracking integration `f6f258d49ed89f724e7ed23bfbe0e5816cf0f33e`; no fetch or git mutation. This accepts A3-M2 closure with the enlarged constant and the existential-local-horizon milestone, **not an inhabitant of the full A01 LocalTheoryAPI**. No proof-source fix is required. Two exact documentation fixes are in part 3.

Read CLAUDE.md, lane-review SKILL.md, LESSONS first 40 lines, HANDOFF §0/P7, reports 205–207, attempts 206–207 and review 200 §3. Review 206 is absent. Existing toolchain/package symlinks were inspected and used; the installer was not rerun in this read-only review.

Path abbreviations below: `TA` = `formalization/NSFormalization/Section4/A01/TameAssembly.lean`; `CT` = the same directory's `CoordinateTame.lean`; `ST` = `SmoothTame.lean`; `CB` = `CommutatorBound.lean`; `FFB` = `ForcingFamilyBound.lean`; `P` = `research/A01/probes/a01_constructor_unconditional.lean`. Other unqualified A01 module filenames refer to that same formalization directory. All citations use actual source line numbers.

REPORT_207:13–20 constants agree with TA:349,375, CT:191 and FFB:22,26. Its seven module theorem statements match TA:354,364,369,378,392,399,408, including every hypothesis and the radius `aprioriRadius a F hF R₆ E (fun q => tameAssemblyA q^2/(4*ν))`. In particular `hb_of_base''` still needs an actual base mild solution and its norm bound; these are ordinary data, not discharged by positivity on an arbitrarily prescribed horizon.

The milestone's exact statement (P:46):

```lean
theorem a01_constructor_unconditional {ν Smax : ℝ} (hν : 0 < ν) (hSmax : 0 < Smax)
    (f : A02.SpaceTimeField) (hf : D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) :
    ∃ S : ℝ, 0 < S ∧ S ≤ Smax ∧
      ∃ (velocity : A02.SpaceTimeField)
        (w : A02.ClassicalSolutionR ν (fun x : Space => velocity (0, x)) f S),
        w.velocity = velocity
```

The fixed-horizon statement (P:20), also checked literally:

```lean
theorem constructor_of_base {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (f : A02.SpaceTimeField) (hf : D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7))
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath (C01.forcePath (S := S) hf)
        (C01.forcePath_jetLp_continuous (S := S) hf) 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t) :
    ∃ (velocity : A02.SpaceTimeField)
      (w : A02.ClassicalSolutionR ν (fun x : Space => velocity (0, x)) f S),
      w.velocity = velocity
```

Thus the additional positivity is `hSmax : 0 < Smax`, and the datum is a bundled `SmoothL2Field Space` with pointwise divergence zero. There is no `hb`, `henergy`, smooth-tame premise, invariant-data premise, or pressure-supply premise in the milestone. Its conclusion does not identify the initial slice with `a.field`.

## 2. What is in Lean

1. **Both mixed orientations.** ST:221–260 applies `scalarProduct_norm` to the coefficient H³ block and the other word in L². The underlying product is genuinely `L(value W) • B` (`vendor/NavierStokesAndEuler/Euler/SobolevL2Product.lean:17,30,40`). TA:14–46 instead embeds the transported vector block and constructs the L² representative of `L(u) • value v`. It does not incorrectly swap scalar-vector multiplication. Both use `value_ae_bound` and have precisely `‖L‖ * sobolevEmbeddingConstant 1 3`; TA:50–88 supplies the right-oriented word bound. The embedding is the cylinder H³ embedding, not an R³-only estimate (`vendor/NavierStokesAndEuler/Euler/CylinderSobolevEmbedding.lean:18,55`). Its constant already includes the vector factor 3 and cardinality of `SobolevWord 3` (85). The extra embedding orders enter the word maximum; the Sobolev carrier's sup norm is handled by `pi_norm_le_iff_of_nonneg`, with no unrecorded sum factor. ST:187–214 supplies the constant-one interpolation.

2. **Finite/smooth identification including angular words.** TA:94–102 uses `wordAtLevel_ae`, `wordAtLevel_value` and `toJet_word`. Opened the supplier (`vendor/NavierStokesAndEuler/Euler/SobolevWordLevel.lean:23–39`): its word is `Fin n → Fin 4`, with no invariance or spatial-only restriction. TA:123–143 uses `boundedWordBlock_value` and actual `coeFn_toLp` identities to identify each product. TA:235–243 uses translation differentiation for the derivative operator. TA:250–298 identifies productHq, its words and the scalar product, then uses CT:74–84 for the **negative** Leibniz expansion. The `Lp.ext` at TA:324 is justified by three genuine a.e. statements: the commutator identity, the constructed leaf-sum representative, and `Lp.coeFn_neg`. No representative equality is inferred merely from suggestive notation.

3. **Leaf count and constants.** TA:158–191 inducts on n, adding two independently represented L² branches and using `2^(n+1)=2*2^n`. TA:194–232 treats the commutator's empty word as zero and bounds the surviving branches by the same `2^n`. Each leaf has positive orders a,b and `a+b≤q+2` (TA:106–143); either the coefficient or transported block has three embedding orders available. TA:332–343 bounds the word length by q+1 and the velocity functional norm by 1. TA:354–361 then uses `familyNorm_le_sum_norm` (opened `vendor/NavierStokesAndEuler/Euler/FiniteMetricEnergy.lean:45`) and the exact finite word cardinality. `SobolevWord q := Σ n : Fin (q+1), Fin n.val → Fin 4` (`vendor/NavierStokesAndEuler/Euler/CylinderSobolevSpace.lean:15`), so REPORT_207:23–24's sum of powers is correct. The separate coordinate sum costs four (CB:82–93), outside the coordinate estimate. CT:197–213 proves `C≤4*max(A q,C/4)`, hence `4*C≤16*tameAssemblyA q`. Neither the Fin 4 directions nor the inherited low-norm factor 16 has been lost.

4. **Density and forcing.** TA:364 uses CT:150–174's genuine smooth approximation/continuity transfer. The unused `_hfL` at TA:356 is benign: TA proves a stronger estimate without the smooth predicate's all-order L² premise, and density supplies that premise when transferring. The finite statement has no smoothness restriction. No ENNReal `.toReal` or infinite-norm shortcut occurs in this estimate. Compatible pairs include every V with v its restriction, and the finite theorem is not vacuous.

   The lead's question about lane 200 has a precise answer: **its theorem does not take arbitrary enlarged A**. FFB:186–191 says:

   ```lean
   (hcomm : CylinderCommutatorBound q hq) :
     ForcingFamilyBound hq hν a F hF (E q) (A q)
   ```

   CT:221–263 is a separately proved recut forcing assembly, reusing lane 200's forcing identity, maximal restriction, force-word bound and norm triangle inequality. Its relevant statement is:

   ```lean
   {C : ℝ} (h : SmoothCylinderCoordinateTame q hq C) :
     ForcingFamilyBound hq hν a F hF (E q) (coordinateTameA q C)
   ```

   TA:396 applies this theorem. This is a valid reuse of the existing predicate and lower-level chain, not an application of a nonexistent arbitrary-A version of FFB:186. Likewise the original `CylinderCommutatorBound` predicate and primed fixed-A theorem are not proved unconditional; TA:378 states the honest enlarged conclusion explicitly.

5. **Signed chain and Grönwall.** TA:399–405 applies `SignedPassage.lean:630–639` with `E=mildNormConstant`, so the necessary initial normalization is preserved. That theorem calls `SignedLimit.lean:166–177`, then the root-comparison/envelope assembly. TA:418–419 supplies the energy family to `MildGronwall.lean:204–218`, whose last line applies `mildGronwall` at :171. The actual name is `mildGronwall`, not the brief's `mildGronwall'`; no separate primed export is claimed by REPORT_207 or needed. The absorbing coefficient is exactly `tameAssemblyA q^2/(4*ν)`. Both `SignedPassage.lean` and `SignedLimit.lean` have **empty direct diffs against integration**, confirming the restoration claim and excluding an unnoticed alternate signed proof.

6. **Constructor and horizon.** P:1–6 imports the actual TameAssembly, CylinderWiring, JointRepresentative, ConstructorAssembly and PressureRegularity modules. P:35–43 calls their landed theorems; there are no copies of those proofs. P:53–58 obtains `0<S≤Smax` and a base order-6 mild solution from `exists_local_quadratic_mild`, then invokes the fixed-base constructor. `CylinderWiring.lean:36–57` supplies the same U at every order and `U 0=a.toLp`; `JointRepresentative.lean:552–564` supplies the a.e. slice equality and joint smoothness on Ico; `PressureRegularity.lean:362–389` supplies pressure for that same family. No empty interval can witness the milestone because S is strictly positive. The horizon is selected before the all-order conclusion; it is not chosen anew for each order.

   Opened with `sed -n` the cited paper passages: `paper/sections/02-preliminaries.tex:75–119` and `paper/sections/appendix-a-local-theory.tex:60–125,140–154`. The existential horizon is the correct local-existence shape on `[0,S)`, and the all-order common interval matches Appendix A:66–77. An arbitrary positive prescribed S would not follow from this local theorem. The correction is mathematically honest, but does not complete every field of `LocalTheoryAPI` (part 3).

7. **Non-vacuity, hygiene and mutations.** The audit's actual zero-data commutator example (`research/A01/axioms_tame_assembly.lean:65–70`) and the positive-horizon zero-force/data constructor (P:63–69) both pass, without assuming the desired universal estimate. These are satisfiability examples, not evidence that replaces the general proofs. All 56 printed declarations have exactly `[propext, Classical.choice, Quot.sound]` after whitespace normalization; both constructor audits do too. The six proof modules in the merge-base diff contain zero prohibited tokens. TA:247 is its sole heartbeat override, declaration-local, 400000, with the reason at :246. The inherited CB:41, CT:103,147 and ST:154 overrides obey the same rule; the restored signed modules have none. No existing Lean module or verification file is modified in the merge-base diff; the only modified existing record is the authorized A3_SPLIT.md. Its DONE entries at :70–72 are justified for this enlarged-constant/base-horizon result.

   `rev207_half.lean` copies the final constant/summation proof but divides C by two; it fails at :23 with the original bound versus the requested half-bound. `rev207_sign.lean` copies the commutator identification proof and removes the RHS minus sign; it fails at :64 against `congrFun hs x`. Neither mutation drops an argument. `rev207_controls.lean` restores exactly those two mathematical changes and passes with zero output, excluding a broken probe harness as the reason for failure. These tests establish proof sensitivity, not that no different proof could ever improve the numerical constant.

## 3. Gaps and exact fixes

No remaining named analytic input was found in the delivered tame → forcing → finite-energy → base-bound chain. The constructor's output is intentionally weaker than a solution for the specified initial datum. P:35 discards `_hU0`, and `ConstructorAssembly.lean:308` fills `initial` by reflexivity for the initial slice. This is faithful to the requested milestone and to REPORT_207:121, but must not be presented as the final paper contract.

Whole-tree `grep -rn` searches were run before assessing absence/scope claims, with patterns `mildGronwall|exists_local|horizon_lower_bound|velocity.*initial|initial.*velocity|PressureGaugeEquivOn|pressure_potential`, and additional searches for `exists_uniform_restart_time|initialClassR.*[Ss]mooth|[Ss]mooth.*initialClassR|smoothL2Field_of|of_initialClass`, plus the three fixed/recut theorem names. The report declares no remaining tame analytic gap; its fixed-name limitation is confirmed by CT:177 and CB:118. Historical missing artifacts are resolved, not accepted as current missing lemmas.

Closest contract candidates were opened rather than dismissed: `CylinderWiring.lean:43` already has the initial L² equality; `JointRepresentative.lean:552` has the slice equality; `D01/DatumToJets.lean:306` already supplies a SmoothL2Field from smooth all-order datum data; `ConstructorAssembly.lean:287,320–323` already chooses the radial pressure and proves its gradient identity. `ContinuationInvariant.lean:156–172` provides a uniform restart theorem, but its bound is on order-(q+1) cylinder data with q≥6 and a fixed force path. It does not provide `Spec.lean:338`'s H¹-ball uniformity. `Horizon.lean:43–65` explicitly documents this difference. These findings mean “not assembled by this lane”, not that all needed ingredients are absent from the tree.

Lead's remaining A01 registration work:

- Convert the manuscript's `a∈initialClassR` to the existing smooth carrier; retain `hU0`, combine it with `hslice` and the toLp a.e. identity, and use continuity to prove `velocity (0,x)=a x` pointwise. Reindex the resulting ClassicalSolutionR by the actual a.
- Choose a total `horizon : ℝ → SpatialField → SpaceTimeField → ℝ` and its corresponding solution from existential local existence (a fixed positive Smax, e.g. 1, suffices for qualitative choice). `research/A01/Spec.lean:277–307` calls the field `solution`, not `exists_local`; an exists_local theorem is a supplier for that field. Bridge the local A02 solution structure to the canonical contract structure field by field.
- Assemble `ManuscriptLocalRegularity` (`Spec.lean:167–230`): all-order Sobolev time smoothness, Helmholtz pressure recovery including t=0, projected equation on Ioo, and pressure gauge equivalence to the radial potential. The current probe does not export these extra fields; its radial-pressure construction is a useful supplier, not the completed gauge-contract proof.
- Supply the additional **H¹-uniform** `horizon_lower_bound` (`Spec.lean:338–343`, paper Appendix A:147–150). Individual H⁷-based local existence and all-order persistence on its interval do not imply this quantified uniform bound. This is not automatically a one-line registration task.
- Register the chosen contract version/bindings/tests and audits in the compiled CI closure. This lane adds no verification registration.

Exact one-line documentation fixes (no Lean fix):

1. Replace REPORT_207.md:25–26 with: “The cylinder H³ constant is proved; lane 205's `forcingFamilyBound_of_cylinder_recut` re-proves the forcing assembly with `tameAssemblyA`, while lane 200's `forcingFamilyBound_of_cylinder` itself remains fixed at `A q`.”
2. After REPORT_207.md:121 add: “This milestone does not yet inhabit `LocalTheoryAPI`: registration still needs initial-datum identification, the manuscript regularity/pressure-gauge fields, and the H¹-uniform `horizon_lower_bound`.”

## 4. Commands and results

All Lean shells sourced `. scripts/lean-env.sh`, exported `LEAN_NUM_THREADS=6`, and ran lake only in `verification/`, one lake process at a time. `make` and the gate script ran from this worktree root. The direct module check is genuinely zero bytes. The build has dependency-warning replay and a success banner, but no TameAssembly diagnostics; this agrees with REPORT_207:140–143, not literal global build silence. The gate script masks make-test status in a pipeline, so `make test` was also run independently and returned 0.

Each output below is exact, with at most its first and last 40 lines quoted; truncation notices are outside code blocks. Full command captures were kept under `/tmp/rev207_*.log`, not in tracked records. Axiom output is line-wrapped: regex extraction of `depends on axioms: [...]` found 56 lists, all exactly the required triple. Thus counting physical lines ending with the bracket would undercount.

`lake build NSFormalization.Section4.A01.TameAssembly` — exit 0, 219 output lines.

First 40 lines:

```text
⚠ [8927/9641] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10092/10256] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10112/10256] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

139 middle lines omitted. Last 40 lines:

```text
⚠ [10153/10256] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
ℹ [10168/10256] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10173/10256] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10176/10256] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10190/10256] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [10240/10256] Replayed NSFormalization.Section4.A01.AprioriFamily
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10241/10256] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10256 jobs).
```

`lake env lean ../formalization/NSFormalization/Section4/A01/TameAssembly.lean` — exit 0, 0 output lines.

No output (0 bytes).

`lake env lean ../research/A01/axioms_tame_assembly.lean` — exit 0, 96 output lines.

First 40 lines:

```text
'NSFormalization.Section4.A01.cylinderRightProduct_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderRightProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderRightProduct_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderRightProduct_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderMixedProduct_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderWord_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderMixedWord_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderL2Bound_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderLeibniz_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderCommutatorLeibniz_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.cylinderDerivative_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderCoordinateCommutator_ae' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.cylinderCoordinateWord_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.tameAssemblyConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.smoothCylinderCoordinateTame' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderCoordinateTame_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.cylinderCoordinateTame_exists'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.tameAssemblyA' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderCommutatorBound_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.forcingFamilyBound_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.finiteMildEnergy'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.hb_of_base''' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.strong_time_square_integral_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.mapped_time_square_integral_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.maximal_word_square_integral_limit' depends on axioms: [propext,
 Classical.choice,
```

16 middle lines omitted. Last 40 lines:

```text
 Quot.sound]
'NSFormalization.Section4.A01.signed_transport_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signed_source_pairing_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signed_scalar_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.regularized_signed_energy_inequality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signed_subintervalWeight_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signed_forcing_integral_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signedRootCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedRootCoefficient_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedApproximationForcing_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signed_scalar_multiplier_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signed_weighted_square_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedGradientOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedGradientOperator_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedGradientOperator_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedApproximationDissipation_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signedGradientOperator_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedInverseRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.maximal_weighted_dissipation_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.cylinderSignedEnergyPassage' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderSignedRootLimit_of_forcingBound'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.finiteMildEnergy_of_forcingBound''' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`lake build NSFormalization.Section4.A01.ConstructorAssembly NSFormalization.Section4.A01.PressureRegularity NSFormalization.Section4.A04.ZeroSolution` — exit 0, 205 output lines.

First 40 lines:

```text
⚠ [8925/9047] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10090/10260] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10110/10260] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

125 middle lines omitted. Last 40 lines:

```text
warning: ../vendor/HeliCorgi/Formal/R3DivergencePointwise.lean:25:19: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10149/10260] Replayed Formal.R3LerayL2Operator
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:34:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:61:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10150/10260] Replayed Formal.R3LerayFourierBridge
warning: ../vendor/HeliCorgi/Formal/R3LerayFourierBridge.lean:73:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10151/10260] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
ℹ [10166/10260] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10171/10260] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10174/10260] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10188/10260] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
Build completed successfully (10260 jobs).
```

`lake env lean ../research/A01/probes/a01_constructor_unconditional.lean` — exit 0, 2 output lines.

```text
'NSFormalization.Section4.A01.constructor_of_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.a01_constructor_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/A01/probes/rev207_half.lean` — exit 1, 11 output lines.

```text
../research/A01/probes/rev207_half.lean:23:2: error: Type mismatch: After simplification, term
  hsum
 has type
  ∑ i_1, ‖cylinderCoordinateCommutator hq ((restrictOperator 1 ⋯) V) V i i_1‖ ≤
    ↑(Fintype.card (SobolevWord (q + 1))) *
      (2 ^ (q + 1) *
        (sobolevEmbeddingConstant 1 3 * (‖(restrictOperator 1 ⋯) ((restrictOperator 1 ⋯) V)‖ * cylinderWordGradient V)))
but is expected to have type
  ∑ i_1, ‖cylinderCoordinateCommutator hq ((restrictOperator 1 ⋯) V) V i i_1‖ ≤
    ↑(Fintype.card (SobolevWord (q + 1))) * (2 ^ (q + 1) * sobolevEmbeddingConstant 1 3) / 2 *
      (‖(restrictOperator 1 ⋯) ((restrictOperator 1 ⋯) V)‖ * cylinderWordGradient V)
```

`lake env lean ../research/A01/probes/rev207_sign.lean` — exit 1, 11 output lines.

```text
../research/A01/probes/rev207_sign.lean:64:2: error: Type mismatch
  congrFun hs x
has type
  ((fun x => (⇑L ∘ f) x • fieldDerivative 1 (standardDirection i) (iteratedFieldDerivative 1 w.snd f) x) -
        iteratedFieldDerivative 1 w.snd fun x => (⇑L ∘ f) x • fieldDerivative 1 (standardDirection i) f x)
      x =
    (-cylinderCommutatorLeibniz w.snd (⇑L ∘ f) (fieldDerivative 1 (standardDirection i) f)) x
but is expected to have type
  L (f x) • fieldDerivative 1 (standardDirection i) (iteratedFieldDerivative 1 w.snd f) x -
      iteratedFieldDerivative 1 w.snd (fun x => L (f x) • fieldDerivative 1 (standardDirection i) f x) x =
    cylinderCommutatorLeibniz w.snd (⇑(velocityComponents 1 0 i) ∘ f) (fieldDerivative 1 (standardDirection i) f) x
```

`lake env lean ../research/A01/probes/rev207_controls.lean` — exit 0, 0 output lines.

No output (0 bytes).

`make check` — exit 0, 28234 output lines.

First 40 lines:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 524,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
{
  "registered_contracts": 29,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
      "NSFormalization.Section4.I01.Extension",
```

28154 middle lines omitted. Last 40 lines:

```text
      "NavierStokes.TransitionRamp",
      "NavierStokes.TransportPrimitive",
      "NavierStokes.TrueConeLoop",
      "NavierStokes.UniformAngularReset",
      "NavierStokes.UniformBlockBounds",
      "NavierStokes.UniformCone",
      "NavierStokes.UniformFourierAlias",
      "NavierStokes.UniformHarmonicInteraction",
      "NavierStokes.UniformPrimaryWeights",
      "NavierStokes.ValidBandGluing",
      "NavierStokes.ValidDyadicBandCover",
      "NavierStokes.VariableGaugeMean",
      "NavierStokes.ViscousPropagator",
      "NavierStokes.VolterraAnalyticBounds",
      "NavierStokes.VolterraParity",
      "NavierStokes.VolterraRegularity",
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.GradientL6V2"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`make test` — exit 0, 344 output lines.

First 40 lines:

```text
lake -d verification test
⚠ [8778/9351] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9875/10511] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9876/10511] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
ℹ [10241/10511] Replayed Tests.Thresholds
info: Tests/Thresholds.lean:13:0: Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only
⚠ [10248/10573] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR
```

264 middle lines omitted. Last 40 lines:

```text

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:104:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
ℹ [10548/10573] Replayed Tests.GradientL6V2
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
ℹ [10553/10573] Replayed Tests.EnergyHighPartialV2
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
ℹ [10556/10573] Replayed Tests.DatumLemmasV3
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
ℹ [10557/10573] Replayed Tests.Correction
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
ℹ [10558/10573] Replayed Tests.MaximalPartial
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
ℹ [10559/10573] Replayed Tests.Uniqueness
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
ℹ [10560/10573] Replayed Tests.HomogeneousNorm
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
ℹ [10565/10573] Replayed Tests.HomogeneousPartialV2
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
ℹ [10568/10573] Replayed Tests.MaximalPartialV2
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
ℹ [10571/10573] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10572/10573] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10573/10573] Replayed Tests.EnergyAbsorptionV4
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
```

`scripts/gates.sh NSFormalization.Section4.A01.TameAssembly` — exit 0, 28496 output lines.

First 40 lines:

```text
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 524,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
{
  "registered_contracts": 29,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
```

28416 middle lines omitted. Last 40 lines:

```text
info: Tests/Thresholds.lean:13:0: Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only
info: Tests/Scaling.lean:18:0: Contract BlowupDensity.Tests.checkedScaling: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartial.lean:15:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartial: checked; standard logical axioms only
info: Tests/Packet.lean:14:0: Contract BlowupDensity.Tests.checkedPacket: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV3.lean:41:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3: checked; standard logical axioms only
info: Tests/DatumLemmasV2.lean:23:0: Contract BlowupDensity.Tests.checkedDatumLemmasV2: checked; standard logical axioms only
info: Tests/EnergyHighPartial.lean:17:0: Contract BlowupDensity.Tests.checkedEnergyHighPartial: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV2.lean:32:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV2: checked; standard logical axioms only
info: Tests/InsertionLifespan.lean:24:0: Contract BlowupDensity.Tests.checkedInsertionLifespan: checked; standard logical axioms only
info: Tests/InsertionFamily.lean:19:0: Contract BlowupDensity.Tests.checkedInsertionFamily: checked; standard logical axioms only
info: Tests/RegularityPartial.lean:17:0: Contract BlowupDensity.Tests.checkedRegularityPartial: checked; standard logical axioms only
info: Tests/BochnerPartial.lean:14:0: Contract BlowupDensity.Tests.checkedBochnerPartial: checked; standard logical axioms only
info: Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked; standard logical axioms only
info: Tests/BoundedRepresentative.lean:14:0: Contract BlowupDensity.Tests.checkedBoundedRepresentative: checked; standard logical axioms only
info: Tests/CorrectionV2.lean:28:0: Contract BlowupDensity.Tests.checkedCorrectionV2: checked; standard logical axioms only
info: Tests/HomogeneousPartial.lean:15:0: Contract BlowupDensity.Tests.checkedHomogeneousPartial: checked; standard logical axioms only
info: Tests/GradientL6.lean:13:0: Contract BlowupDensity.Tests.checkedGradientL6: checked; standard logical axioms only
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` — exit 0, 28202 output lines.

First 40 lines:

```text
{
  "registered_contracts": 29,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
      "NSFormalization.Section4.I01.Extension",
      "NSFormalization.Section4.I01.Quiet",
      "NSFormalization.Source.Insertion",
      "NSFormalization.Source.PacketEndpoint",
      "NSFormalization.Source.PacketEnergy",
      "NSFormalization.Source.PacketForceExtension",
      "NSFormalization.Source.PacketPressure",
      "NSFormalization.Source.PacketScaling",
      "NSFormalization.Source.ParabolicScaling",
      "NSFormalization.Source.SelectedPacketEnergy",
      "NSFormalization.Source.ViscosityPacket",
      "NSFormalization.Source.ViscosityScaling",
      "NavierStokes.ActivationBounds",
      "NavierStokes.ActivationCone",
      "NavierStokes.ActivationContinuation",
      "NavierStokes.ActivationHolomorphic",
      "NavierStokes.ActivationStocks",
      "NavierStokes.ActiveAnnulusWeight",
      "NavierStokes.ActualBaseResidual",
      "NavierStokes.ActualBaseVelocityBounds",
      "NavierStokes.ActualCandidateAssembly",
      "NavierStokes.ActualCandidateConstruction",
      "NavierStokes.ActualCarrierGeometry",
      "NavierStokes.ActualCarrierTransport",
      "NavierStokes.ActualCarrierTransportBase",
```

28122 middle lines omitted. Last 40 lines:

```text
      "NavierStokes.TerminalEdgeFactor",
      "NavierStokes.TerminalHistoryBridge",
      "NavierStokes.TerminalPressure",
      "NavierStokes.TerminalStress",
      "NavierStokes.TimeLocalization",
      "NavierStokes.TorusAverages",
      "NavierStokes.TorusInverse",
      "NavierStokes.TorusMeanRequestRebase",
      "NavierStokes.TransitionRamp",
      "NavierStokes.TransportPrimitive",
      "NavierStokes.TrueConeLoop",
      "NavierStokes.UniformAngularReset",
      "NavierStokes.UniformBlockBounds",
      "NavierStokes.UniformCone",
      "NavierStokes.UniformFourierAlias",
      "NavierStokes.UniformHarmonicInteraction",
      "NavierStokes.UniformPrimaryWeights",
      "NavierStokes.ValidBandGluing",
      "NavierStokes.ValidDyadicBandCover",
      "NavierStokes.VariableGaugeMean",
      "NavierStokes.ViscousPropagator",
      "NavierStokes.VolterraAnalyticBounds",
      "NavierStokes.VolterraParity",
      "NavierStokes.VolterraRegularity",
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.GradientL6V2"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

`git diff --name-only origin/erenup/integration...HEAD` — exit 0, 20 output lines.

```text
formalization/NSFormalization/Section4/A01/CommutatorBound.lean
formalization/NSFormalization/Section4/A01/CoordinateTame.lean
formalization/NSFormalization/Section4/A01/SignedLimit.lean
formalization/NSFormalization/Section4/A01/SignedPassage.lean
formalization/NSFormalization/Section4/A01/SmoothTame.lean
formalization/NSFormalization/Section4/A01/TameAssembly.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_COMMUTATOR_BOUND.md
research/A01/ATTEMPTS_COORDINATE_TAME.md
research/A01/ATTEMPTS_SMOOTH_TAME.md
research/A01/ATTEMPTS_TAME_ASSEMBLY.md
research/A01/REPORT_202.md
research/A01/REPORT_205.md
research/A01/REPORT_206.md
research/A01/REPORT_207.md
research/A01/axioms_commutator_bound.lean
research/A01/axioms_coordinate_tame.lean
research/A01/axioms_smooth_tame.lean
research/A01/axioms_tame_assembly.lean
research/A01/probes/a01_constructor_unconditional.lean
```

`git diff origin/erenup/integration -- formalization/NSFormalization/Section4/A01/SignedPassage.lean formalization/NSFormalization/Section4/A01/SignedLimit.lean` — exit 0, 0 output lines.

No output (0 bytes).

`git diff --check` — exit 0, 0 output lines.

No output (0 bytes).

Additional read-only checks: package symlink present; `git diff --name-only origin/erenup/integration...HEAD -- verification/` produced no output; regex hygiene scan produced zero prohibited tokens in each of the six proof modules. Whole-tree gap-search commands described in part 3 returned the cited candidates. No tracked lane source, records, index, or refs were changed by the review. The only new workspace files are this report and the three permitted `rev207_*.lean` probes.
