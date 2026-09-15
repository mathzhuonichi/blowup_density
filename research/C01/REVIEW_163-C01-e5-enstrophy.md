ACCEPT

## 1. What the lane claims

The worker claims six new declarations and completion of row E5: two order-one word
collapses, the shifted-window enstrophy derivative, the carrier-B integration-by-parts
identity, its specialization to the classical solution, and a clamp-free theorem at every
interior time (`research/C01/REPORT_163.md:3-49`).  Those are exactly the deliverables in
the lane brief; the report explicitly leaves E6, E7, and the final `enstrophyIdentity`
assembly out of scope (`research/C01/REPORT_163.md:51-55`).

The mathematical claim is faithful.  The manuscript tests the equation against `-Δu`
at `paper/sections/04-whole-space.tex:106`, uses the Laplacian norm in the nonlinear bound
at `paper/sections/04-whole-space.tex:108-110`, and reaches the squared-gradient derivative
at `paper/sections/04-whole-space.tex:113-115`.  The local specification spells out the
corresponding identity and its integration-by-parts obligation at
`research/C01/Spec.lean:475-494`.  Row E5 itself asks for precisely the two equalities
implemented here (`research/C01/ENERGY_SPLIT.md:116`).

## 2. What is in Lean

All six reported theorems exist with the claimed statements:

- `wordEnergy_one` is exactly
  `wordEnergy 1 A = wordEnergy 0 A + ∑ i : Fin 3,
  ‖(A.directionalField (axis i)).toLp‖ ^ 2`
  (`formalization/NSFormalization/Section4/C01/Enstrophy.lean:34-44`).
- `wordInner_sum_one` is the reported `range (1+1)` pairing sum, equal to the
  order-zero pairing plus the three directional pairings
  (`formalization/NSFormalization/Section4/C01/Enstrophy.lean:46-61`).
- `enstrophyDerivative_hasDerivAt` has exactly `w`, `hf`, `0<c`, `c≤S`, `S<T`, and
  `r∈Ioo 0 (S-c)`, and concludes the shifted/clamped raw `toLp` derivative with value
  `2 * ∑ᵢ⟪∂ᵢu,∂ᵢ∂ₜu⟫`
  (`formalization/NSFormalization/Section4/C01/Enstrophy.lean:65-91`).
- `directional_pairing_sum_eq_neg_laplacian` states exactly
  `∑ᵢ⟪∂ᵢA,∂ᵢB⟫ = -⟪laplacianField A,B⟫`
  (`formalization/NSFormalization/Section4/C01/Enstrophy.lean:164-175`).
- `enstrophyDerivative_eq_neg_laplacian` specializes that value identity with the
  exact coefficient `-2` (`formalization/NSFormalization/Section4/C01/Enstrophy.lean:177-191`).
- `enstrophyDerivative_classical_unconditional` concludes, for every
  `t∈Ioo 0 T`, `HasDerivAt` of the global raw integral
  `∫x,∑ᵢ‖fderiv u(s,·) x (axis i)‖²` with derivative
  `-2 * ⟪laplacianField u(t), temporalSliceField(t)⟫`
  (`formalization/NSFormalization/Section4/C01/Enstrophy.lean:193-204`).

The proof route also matches the cited mathematics.  The vendor defines a word of length
one as one coordinate directional derivative and `wordEnergy s` as the sum over word
lengths in `range (s+1)`
(`vendor/NavierStokesAndEuler/Euler/OrdinarySmoothWords.lean:31-40,91-95`).  Its time
lemma differentiates this energy to twice the corresponding pairing sum
(`vendor/NavierStokesAndEuler/Euler/OrdinaryWordTime.lean:69-97`).  The lane applies that
lemma at orders one and zero and subtracts
(`formalization/NSFormalization/Section4/C01/Enstrophy.lean:132-160`).  Finally,
`field_directional_inner` says `⟪∂ᵥA,B⟫=-⟪A,∂ᵥB⟫`
(`vendor/NavierStokesAndEuler/Euler/OrdinaryL2Integration.lean:33-50`), while the tree's
`laplacianField` is exactly `∑ᵢ∂ᵢ∂ᵢ`
(`formalization/NSFormalization/Source/OrdinaryViscousStability.lean:11-30`), so the
implemented sign is correct.  The raw integral is bridged from the directional `Lp` norm
sum by `gradientSq_eq_sum`
(`formalization/NSFormalization/Section4/C01/Vocabulary.lean:111-133`).

No hypothesis makes the result vacuous.  The window theorem's `hr : r∈Ioo 0 (S-c)` forces
the interval to be nonempty, and all named hypotheses are used in its construction
(`formalization/NSFormalization/Section4/C01/Enstrophy.lean:92-136`).  There is no
`ENNReal.toReal` in the new module.  More
concretely, the conformance file instantiates the results at `ν=1`, `T=2`, window
`[1/2,1]`, and interior times `1/4`/`1`
(`research/C01/axioms_e5.lean:26-37`), using the actual `memForceR_zero` and `zeroSol`
(`formalization/NSFormalization/Section4/A04/ZeroSolution.lean:71-75,87-105`).  That file
typechecks.

Hygiene is clean: the new proof module contains no `sorry`, `admit`, `axiom`,
`native_decide`, or `maxHeartbeats`.  The base diff adds only the new Lean module and
three new lane records, and changes the requested E5 row in `ENERGY_SPLIT.md`; no existing
Lean module was modified.  All six declarations print exactly
`[propext, Classical.choice, Quot.sound]` (`research/C01/axioms_e5.lean:19-24` and the
gate output below).

## 3. Gaps

There is no E5 gap.  The report's only gap statement is the explicitly out-of-scope E6/E7
and final assembly (`research/C01/REPORT_163.md:51-55`).  I searched the whole required
`formalization/NSFormalization/Section4/{D01,A03,A04,A01,C01}` tree before accepting it.
There is no declaration named `enstrophyIdentity`, and no physical carrier-B theorem
pairing `laplacianField` with `pressureGradientField`.  The closest hit,
`A04.pressure_drop`, instead proves `⟪G,P⟫=0` when `G` is a Sobolev datum of the velocity
itself and `P` is a datum of the pressure gradient
(`formalization/NSFormalization/Section4/A04/PressureDrop.lean:211-231`).  Likewise,
`A04.inner_energy_assembly` is an inequality-oriented generic datum lemma
(`formalization/NSFormalization/Section4/A04/HighEnergy.lean:82-123`), and the existing
C01 arithmetic lemmas are the ordinary energy identities, not the E7 enstrophy formula
(`formalization/NSFormalization/Section4/C01/EnergyIdentity.lean:67-111`).  Thus these
hits do not invalidate the report's scoped gap statement.

The substantive negative mutation is retained at
`research/C01/probes/rev163_flip_sign.lean:17-27`.  It keeps the same function, binders,
and hypotheses but flips the main theorem's derivative coefficient from `-2` to `+2`.
Lean rejects the unchanged proof term with the expected derivative-value type mismatch;
the exact error is in part 4.

The target `lake build` is not byte-silent because Lake replays diagnostics from imported,
pre-existing modules.  It reports no diagnostic from `Enstrophy.lean`, and direct Lean on
that module is byte-silent.  This is not a lane defect.

## 4. Commands and results

All Lean shells sourced `scripts/lean-env.sh`; every `lake` command was run from
`verification/`, sequentially, with the build using `LEAN_NUM_THREADS=6`.

```text
$ cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.Enstrophy
⚠ [9542/9839] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused: PiLp.single_apply
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused: PiLp.single_apply
⚠ [10193/10303] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused: Complex.smul_re
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused: Complex.smul_im
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
⚠ [10197/10303] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead
⚠ [10204/10303] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
⚠ [10207/10303] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.
ℹ [10210/10303] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this: ring_nf
⚠ [10215/10303] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10218/10303] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused: Function.comp_def
⚠ [10236/10303] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead
⚠ [10246/10303] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'
⚠ [10249/10303] Replayed Formal.R3StokesL2Operator
warning: ../vendor/HeliCorgi/Formal/R3StokesL2Operator.lean:111:2: Try this: letI̵
⚠ [10250/10303] Replayed Formal.R3L2ScalarAux
warning: ../vendor/HeliCorgi/Formal/R3L2ScalarAux.lean:26:2: Try this: letI̵
⚠ [10258/10303] Replayed Formal.FlowMapNonextendibilityCriterion
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:40:16: Variable name `ht0` is not explicitly referenced.
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:40:30: Variable name `htT` is not explicitly referenced.
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:43:16: Variable name `ht0` is not explicitly referenced.
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:43:30: Variable name `htT` is not explicitly referenced.
⚠ [10259/10303] Replayed Formal.UniformRestartContinuation
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:36:16: Variable name `ht0` is not explicitly referenced.
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:36:30: Variable name `htT` is not explicitly referenced.
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:39:16: Variable name `ht0` is not explicitly referenced.
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:39:30: Variable name `htT` is not explicitly referenced.
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:95:0: Definition `FlowMapUniformRestartPackage.toContinuationPackage` is a proposition; use `theorem` instead of `def`
⚠ [10260/10303] Replayed Formal.R3SobolevCarrier
warning: ../vendor/HeliCorgi/Formal/R3SobolevCarrier.lean:80:2: try 'simp' instead of 'simpa'
⚠ [10263/10303] Replayed Formal.R3CoordinateLinearAux
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:10:11: Variable name `x` is not explicitly referenced.
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:10:13: Variable name `y` is not explicitly referenced.
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:11:12: Variable name `c` is not explicitly referenced.
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:11:14: Variable name `x` is not explicitly referenced.
⚠ [10266/10303] Replayed Formal.R3DivergencePointwise
warning: ../vendor/HeliCorgi/Formal/R3DivergencePointwise.lean:25:19: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
⚠ [10270/10303] Replayed Formal.R3LerayL2Operator
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:34:2: try 'simp' instead of 'simpa'
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:61:2: try 'simp' instead of 'simpa'
⚠ [10271/10303] Replayed Formal.R3LerayFourierBridge
warning: ../vendor/HeliCorgi/Formal/R3LerayFourierBridge.lean:73:2: try 'simp' instead of 'simpa'
⚠ [10272/10303] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'
Build completed successfully (10303 jobs).
exit 0
```

The displayed build output preserves every replayed source location and diagnostic text;
Lake's repeated explanatory `Note`/`Hint` paragraphs are omitted.  None refers to the new
module.

```text
$ cd verification && . ../scripts/lean-env.sh && lake env lean ../formalization/NSFormalization/Section4/C01/Enstrophy.lean
<no output>
exit 0
```

```text
$ cd verification && . ../scripts/lean-env.sh && lake env lean ../research/C01/axioms_e5.lean
'NSFormalization.Section4.C01.wordEnergy_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.wordInner_sum_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.enstrophyDerivative_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.directional_pairing_sum_eq_neg_laplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.C01.enstrophyDerivative_eq_neg_laplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.C01.enstrophyDerivative_classical_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit 0
```

```text
$ . scripts/lean-env.sh && make check
python3 experiments/check_formalization_plan.py --check
...
  "task_count": 30,
  "source_counts": {"formalization": 473, "vendor/NavierStokesAndEuler": 2486, "vendor/HeliCorgi": 129},
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
...
  "registered_contracts": 26,
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.061s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
exit 0
```

`make check` printed 25,366 lines because `check_contracts.py` emits every registered
closure; the two `...` markers above replace only those large JSON arrays.  The command
was run unfiltered and exited 0.  `source_hashes_match: false` is expected after adding a
new formalization source and is non-fatal in this gate.

```text
$ cd verification && . ../scripts/lean-env.sh && lake env lean ../research/C01/probes/rev163_flip_sign.lean
../research/C01/probes/rev163_flip_sign.lean:27:2: error: Type mismatch
  enstrophyDerivative_classical_unconditional w hf ht
has type
  HasDerivAt (fun s => ∫ (x : Space), ∑ i, ‖(fderiv ℝ (fun y => w.velocity (s, y)) x) (axis i)‖ ^ 2)
    (-2 * ⟪(laplacianField (velocitySliceField w ⋯)).toLp, (temporalSliceField w hf ht).toLp⟫) t
but is expected to have type
  HasDerivAt (fun s => ∫ (x : Space), ∑ i, ‖(fderiv ℝ (fun y => w.velocity (s, y)) x) (axis i)‖ ^ 2)
    (2 * ⟪(laplacianField (velocitySliceField w ⋯)).toLp, (temporalSliceField w hf ht).toLp⟫) t
exit 1 (expected)
```

```text
$ git diff --name-only origin/erenup/integration...HEAD
formalization/NSFormalization/Section4/C01/Enstrophy.lean
research/C01/ATTEMPTS_E5.md
research/C01/ENERGY_SPLIT.md
research/C01/REPORT_163.md
research/C01/axioms_e5.lean
```

The diff scan for `sorry|admit|axiom|native_decide` and per-declaration
`maxHeartbeats` produced no code hit.  `verification/` was not touched, so the brief's
conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration` gates do not apply.
