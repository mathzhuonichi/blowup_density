ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims a cube-free raw-field `DomainPlacementData u p f K`, a
constructor for every prescribed positive-radius interior ball, the canonical
geometry theorem, a translated non-vacuity example, and a standard-axiom audit
(`research/T23/REPORT_476.md:5-43`).  Those core claims are accurate.

The paper says to choose one compact `K_*` containing the carrier and spatial
force support and, for all sufficiently small positive `ε`, require
`2ε² < T` and `x₀ + εK_* ⊆ B`
(`paper/sections/03-torus.tex:101-106`).  For the bounded-domain corollary it
then says that the construction works in any prescribed interior ball and that
the supports are chosen in a smaller closed ball strictly inside `Ω`
(`paper/sections/03-torus.tex:646-655`).  Thus the lane's free-center,
non-periodic interpretation is the right mathematics; no fundamental cube or
origin condition belongs here.

The sixteen fields in the production record
(`formalization/NSFormalization/Section3/T23/Placement.lean:35-112`) match the
sixteen fields in the reconciled spec
(`research/T23/Spec.lean:374-450`) after the brief's required raw-field
substitution `P.carrier ↦ K` and `P.force ↦ f`.  This also agrees with the raw
T15 record, with exactly `chartBall_in_cube` removed
(`formalization/NSFormalization/Section3/T15/Scaling.lean:106-190`).

## 2. What is in Lean

The implementation defines
`Kstar = K ∪ Prod.snd '' tsupport f`, proves it compact from `hK` and `hf`,
chooses a positive norm bound, and defines the positive margin
`chartRadius - dist x₀ chartCenter`
(`formalization/NSFormalization/Section3/T23/Placement.lean:118-166`).  Its
single threshold is

```lean
min (min (1 / 2) (T / 4))
  (margin / (2 * (R + 1)))
```

(`formalization/NSFormalization/Section3/T23/Placement.lean:171-176`).  The
closed upper endpoint is handled strictly in both time and space
(`formalization/NSFormalization/Section3/T23/Placement.lean:199-252`).  This is
the intended T15 construction pattern
(`formalization/NSFormalization/Section3/T15/Assembly.lean:17-83`) and the
compact-union step matches the cited supplier
(`verification/Bindings/CorrectionV2.lean:528-539`).

`domainPlacementData` has the promised hypotheses and fills all sixteen fields
(`formalization/NSFormalization/Section3/T23/Placement.lean:260-282`).  Its
`T`, `chartCenter`, `chartRadius`, and `x₀` projections are definitionally the
inputs (`formalization/NSFormalization/Section3/T23/Placement.lean:284-326`).
The separate theorem concludes the API's literal geometry expression for that
canonical placement (`formalization/NSFormalization/Section3/T23/Placement.lean:331-343`),
which matches the spec field (`research/T23/Spec.lean:715-721`).  The ball
hypothesis is deliberately named `_hball` only in the record constructor,
where the record has no `Ω` field; the geometry theorem consumes the honest
named `hball`.  No interval is empty: `eps_pos` is a record field and `time_pos`
and `chartRadius_pos` are strict (`formalization/NSFormalization/Section3/T23/Placement.lean:40-56,91-105`).

The translated probe really uses center `(5,5,5)`, ball radius `1`, domain
radius `2`, proves the origin is outside the domain, constructs the placement,
and consumes every field including `eps_time`
(`research/T23/probes/placement_closes.lean:25-69,124-149`).  Hence the result
is not made vacuous by an origin/cube assumption.  In particular
`translatedPlacement.ε₀` itself witnesses the nonempty scale interval by
`eps_pos`, and its temporal conclusion is exercised at
`research/T23/probes/placement_closes.lean:132-135`.

All twenty declarations listed in the axiom audit
(`research/T23/axioms_u1.lean:13-32`) print exactly
`[propext, Classical.choice, Quot.sound]`.  There is no local
`sorry`/`admit`/`axiom` declaration/`native_decide`, no `maxHeartbeats`, and no
unsafe boundary import.  The sole production import is the safe T15 bridge
(`formalization/NSFormalization/Section3/T23/Placement.lean:1`); the forbidden
candidate really is unsafe because it imports the sorry-bearing module
(`formalization/NSFormalization/Paper1/BoundaryCorollaryCorrected.lean:1`,
`formalization/NSFormalization/Paper1/BoundaryCorollary.lean:82-90`).

## 3. Gaps

The core deliverable in the lane title and Goal is complete.  One exact
follow-up remains before the stronger planning status should be called fully
complete: `T23_SPLIT` additionally requested production lemmas for prescribed
closed-ball compactness, separation from `frontier Ω`, and a smaller closed
ball around `x₀` (`research/T23/T23_SPLIT.md:40`), but the production module
ends after `interiorBall_in_domain`
(`formalization/NSFormalization/Section3/T23/Placement.lean:328-345`) and the
worker report says there is no U1 gap (`research/T23/REPORT_476.md:48-50`).

This is a note rather than rejection because these are elementary downstream
geometry helpers, not missing fields or a weakness in the constructed
placement.  The exact fixes are:

1. Add a named compactness theorem for
   `Metric.closedBall chartCenter chartRadius` using `isCompact_closedBall`.
2. Add a named theorem producing `ρ > 0` with
   `Metric.closedBall x₀ ρ ⊆ Metric.ball chartCenter chartRadius` from
   `x₀_mem` (for example `ρ = margin / 2`).
3. Add the frontier-separation theorem with an explicit `hΩ : IsOpen Ω`, or
   strengthen its premise to containment in `interior Ω`.  The current
   `hball : closure (ball ...) ⊆ Ω`
   (`formalization/NSFormalization/Section3/T23/Placement.lean:264`) does not by
   itself imply separation from the frontier of an arbitrary set (take `Ω` to
   be the same closed ball).

The required whole-Section4 search before declaring that gap was:

```text
$ grep -rn -E "(closedBall|closure \(Metric\.ball|frontier.*ball|ball.*frontier|disjoint_frontier|smaller.*ball|exists.*Metric\.ball)" formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/R42/CorrectionPath.lean:138:  -- `F` has compact spacetime support: outside `[0,b] × closedBall x₀ r` it is `0`.
formalization/NSFormalization/Section4/R42/CorrectionPath.lean:140:    refine HasCompactSupport.intro (K := Icc (0 : ℝ) b ×ˢ Metric.closedBall x₀ r)
formalization/NSFormalization/Section4/R42/CorrectionPath.lean:141:      (isCompact_Icc.prod (isCompact_closedBall x₀ r)) ?_
formalization/NSFormalization/Section4/R42/CorrectionPath.lean:149:      · -- `pt ≤ b`: `px ∉ closedBall`, so `d (pt, px) = 0`.
formalization/NSFormalization/Section4/R42/CorrectionPath.lean:150:        have hpx : px ∉ Metric.closedBall x₀ r := fun hmem => hp ⟨⟨h0, hpb⟩, hmem⟩
formalization/NSFormalization/Section4/R42/CorrectionPath.lean:154:          fun hmem => hpx (Metric.ball_subset_closedBall (hsupp' hmem))
formalization/NSFormalization/Section4/R42/Lifespan.lean:163:  IsCompact.of_isClosed_subset (isCompact_closedBall c r) (isClosed_tsupport d)
formalization/NSFormalization/Section4/R42/Lifespan.lean:164:    (h.trans Metric.ball_subset_closedBall)
formalization/NSFormalization/Section4/R42/PressureGradient.lean:88:with support inside the compact `closedBall x₀ r`, and
formalization/NSFormalization/Section4/R42/PressureGradient.lean:116:    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ r)
formalization/NSFormalization/Section4/R42/PressureGradient.lean:117:      (hsupp_g.trans (hsupp.trans Metric.ball_subset_closedBall))
formalization/NSFormalization/Section4/B02/Annular.lean:349:    apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Space) (2 * R))
formalization/NSFormalization/Section4/B02/Annular.lean:351:    refine closure_minimal (fun ξ hξ => ?_) Metric.isClosed_closedBall
formalization/NSFormalization/Section4/B02/Annular.lean:353:    simp only [Metric.mem_closedBall, dist_zero_right]
formalization/NSFormalization/Section4/B02/AnnularSchwartz.lean:54:    apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Space) R)
formalization/NSFormalization/Section4/B02/AnnularSchwartz.lean:59:    simp only [Metric.mem_closedBall, dist_zero_right]
formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:297:  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:309:    have hxb : x ∈ Metric.closedBall (0 : Space) b.rIn := by
formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:310:      refine Metric.mem_closedBall.mpr ?_
formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:311:      exact le_trans (Metric.mem_closedBall.mp (hR hx)) (le_max_left _ _)
formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:313:    rw [b.one_of_mem_closedBall hxb]
formalization/NSFormalization/Section4/D01/OrderZeroSymbol.lean:53:  bump.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff]; exact hx)
formalization/NSFormalization/Section4/D01/OrderZeroSymbol.lean:65:  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * (↑n + 1)))
formalization/NSFormalization/Section4/D01/OrderZeroSymbol.lean:67:  rw [mem_closedBall_zero_iff, not_le] at hx
```

These are only generic closed-ball uses; there is no Section4 theorem providing
the missing domain-placement geometry.  The unsafe general frontier template is
instead at `formalization/NSFormalization/Paper1/BoundaryCorollaryCorrected.lean:19-23`.

One reporting note: `make check` did exit zero, but its exact output also says
`source_hashes_match: false` and reports eleven repository-wide copied-source
tokens.  The worker's shorter success summary
(`research/T23/REPORT_476.md:82-83`) should mention those facts.  The known
`BoundaryCorollary.lean:90` token is unrelated to this import closure.

## 4. Commands and results

All Lake commands were run from `verification/` after
`. ../scripts/lean-env.sh`, with no concurrent Lake invocation.

### Module build

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T23.Placement
⚠ [8778/9159] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9835/9897] Replayed NSFormalization.Source.RealSobolev
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
⚠ [9839/9897] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9846/9897] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9849/9897] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9859/9897] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9862/9897] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
ℹ [9874/9897] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [9891/9897] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
Build completed successfully (9897 jobs).
EXIT=0
```

There is no warning from `Placement.lean` itself.

### Direct checks

```text
$ lake env lean ../formalization/NSFormalization/Section3/T23/Placement.lean
<no output>
EXIT=0

$ lake env lean ../research/T23/probes/placement_closes.lean
<no output>
EXIT=0
```

The axiom file exited zero and printed:

```text
'NSFormalization.Section3.T23.DomainPlacementData' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementCarrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementCarrier_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementCarrier_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementRadius' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementRadius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.norm_le_domainPlacementRadius' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementMargin' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementMargin_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementThreshold_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementThreshold_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.domainPlacementThreshold_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementThreshold_space' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementData' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementData_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.domainPlacementData_chartCenter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.domainPlacementData_chartRadius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.domainPlacementData_x₀' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.interiorBall_in_domain' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

### Negative mutation

The reviewer probe flips the sign of the main temporal placement conclusion,
without dropping an argument
(`research/T23/probes/rev476_eps_time_flip.lean:17-21`).  It fails exactly at
the changed statement:

```text
$ lake env lean ../research/T23/probes/rev476_eps_time_flip.lean
../research/T23/probes/rev476_eps_time_flip.lean:21:2: error: Type mismatch
  place.eps_time
has type
  ∀ ε ∈ Ioc 0 place.ε₀, 2 * ε ^ 2 < place.T
but is expected to have type
  ∀ ε ∈ Ioc 0 place.ε₀, place.T < 2 * ε ^ 2
EXIT=1
```

### Hygiene and repository checks

```text
$ git diff --name-status origin/erenup/integration-section3...HEAD
A formalization/NSFormalization/Section3/T23/Placement.lean
A research/T23/ATTEMPTS_U1.md
A research/T23/REPORT_476.md
M research/T23/T23_SPLIT.md
A research/T23/axioms_u1.lean
A research/T23/probes/placement_closes.lean
```

Thus no pre-existing Lean module was modified.  `git diff --check` and the
targeted forbidden-token, `maxHeartbeats`, and unsafe-import scans all produced
no output and exited zero.

`make check` is the four-command target at `Makefile:3-7`.  Its raw captured
output was 63,360 lines / 2,626,863 bytes with SHA-256
`50c70e75df9366b669858927aac3974a67d7442700bd9d61dfea01427e6e0479`.
The exact head/status/tail retained from that run was:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 707,
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
  "registered_contracts": 52,
  ... 63,323 closure-enumeration lines ...
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
EXIT=0
```

No path under `verification/` appears in the branch diff, so the conditional
`scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates do not
apply to this lane.

Fixes: add the three named geometry helpers above (with `IsOpen Ω` for frontier
separation), and amend the worker report's `make check` line to disclose
`source_hashes_match: false` plus the repository-wide token count.
