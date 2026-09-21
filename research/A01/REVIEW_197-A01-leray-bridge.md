REJECT

## 1. What the lane claims

The mathematical claim in the fixed report is now substantially accurate. The
canonical theorem is said to derive lane 195's projected-datum identity without
`hsol`, `hgrad`, physical agreement, or an independently assumed physical datum
(`research/A01/REPORT_197.md:3-7`). It also correctly retracts the first report's
understatement of lane 194: `residualCarrier`, its all-order paths, and the physical
residual bridge are credited at `research/A01/REPORT_197.md:11-23`.

The source contains every theorem named in the report. In particular,
`leray_value_solenoidal`, `leray_value_complement_gradient`,
`laplacianEvaluation_solenoidal`, `cylinderResidual_solenoidal`,
`residual_difference_gradient`, and `ordinaryResidual_helmholtz` occur at
`formalization/NSFormalization/Section4/A01/LerayBridge.lean:183,189,195,204,224,276`.
The physical and canonical exports occur at the claimed locations:
`residualDatum_jointRepresentative` at `LerayBridge.lean:324`,
`physicalResidual_eq_residualDatum` at `LerayBridge.lean:342`,
`hprojected_of_canonical_pairs` at `LerayBridge.lean:356`, and
`hprojected_of_cylinder'` at `LerayBridge.lean:438`. The five time-derivative
helpers are present at
`formalization/NSFormalization/Section4/A01/LerayBridgeTime.lean:30,43,59,82,105`.

The conclusion of `hprojected_of_cylinder'` is the required lane-195 statement:
for every `t in Ioo 0 S`, it identifies `lowerVectorL m 0 (R t)` with
`A t - Leray.lerayComplement 0 (A t)`, where the canonical `A` is lane 194's
`residualDatum` (`LerayBridge.lean:469-480`). This is token-for-token the
`hprojected` body in the landed consumer
(`origin/erenup/integration:formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:251-253`).
It matches the paper's projected equation and whole-space pressure split
`partial_t u - nu Delta u = P(f-div(u tensor u))` and
`grad p = (I-P)(f-div(u tensor u))`
(`paper/sections/02-preliminaries.tex:76-100`).

There is, however, one report/interface claim that is no longer sufficient for
the superseding check point. The report explicitly targets the old `cb1e875`
`PressureSupply` prefix and says that `ha` is not a binder
(`research/A01/REPORT_197.md:63-78`). The actual exported binders are:

1. implicit `q`, `hq`, implicit `nu,S`, `hnu,hS`, `f,hf,a`;
2. `U,hpaths`;
3. one selected-order `u,hU,hdiv,hduh`;
4. `velocity,hslice,hc3`;
5. the all-order same-carrier `hpairs` family;
6. implicit `m`, `hm,hm2`, then `B,R,hB,hR`

(`LerayBridge.lean:438-475`). This does match the older locally available
`PressureSupply` prefix, but it does not match the fix6 shape specified in this
review brief: the submitted theorem retains the redundant selected-order
`u/hU/hdiv/hduh` block and has no `ha` binder. The local ref
`erenup/180-A01-b2-assembly` still shows the older declaration, so the requested
fix6 interface was not actually replayed in this worktree.

## 2. What is in Lean

### Cylinder Helmholtz decomposition

The formerly assumed `hsol` and `hgrad` are now proved.

* The vendor defines `leray period q` as identity minus the Sobolev gradient
  projection (`formalization/NSFormalization/Source/ForcedCylinderLocal.lean:24-30`).
  That gradient projection is the orthogonal `starProjection` onto the closed
  span of genuine cylinder gradients
  (`vendor/NavierStokesAndEuler/Euler/EulerProof.lean:1264-1278`).
* `leray_gradient_zero` proves that the projected value has zero gradient
  projection (`ForcedCylinderLocal.lean:32-41`), and the vendor equivalence turns
  exactly that into membership in `divergenceFreeSpace`
  (`vendor/NavierStokesAndEuler/Euler/DivergenceFreeHeat.lean:45-60`). The lane's
  quoted theorem is therefore
  `leray_value_solenoidal` (`LerayBridge.lean:182-186`).
* The complementary value is definitionally the star projection and hence lies
  in `gradientSpace`; the lane's quoted theorem is
  `leray_value_complement_gradient` (`LerayBridge.lean:175-192`).
* The full residual is handled, not merely its source. Second derivative words
  preserve the constraint (`LerayBridge.lean:194-201`), so the viscous Laplacian
  plus projected source is solenoidal (`LerayBridge.lean:203-215`). The proof of
  `residual_difference_gradient` cancels the common Laplacian, transports
  advection through `restrict_advection`, and leaves the gradient projection with
  the correct sign (`LerayBridge.lean:224-253`). Angular invariance then descends
  both memberships (`LerayBridge.lean:255-293`).

At datum level the proof is also honest. Lowering really transports a datum of
the same field (`formalization/NSFormalization/Section4/D01/LerayLowering.lean:199-208`).
Smooth curl-free order-zero data are fixed by the complement
(`formalization/NSFormalization/Section4/D01/OrderZeroCurl.lean:478-504`), while
smooth divergence-free data are transverse and killed by it
(`formalization/NSFormalization/Section4/D01/OrderZeroSymbol.lean:482-491` and
`formalization/NSFormalization/Section4/D01/LerayDatum.lean:314-337`). Thus the
finite decomposition at `LerayBridge.lean:97-102` has the intended mathematical
content and no hidden `top.toReal = 0` or empty-interval device.

### Lane 194 to lane 195

This connection is now discharged without an agreement hypothesis. Lane 194
fixes one order-six carrier using the selected order-seven pair
(`formalization/NSFormalization/Section4/A01/ComplementPath.lean:528-535`), gives
it all-order paths (`ComplementPath.lean:536-572`), and defines its order-zero
datum (`ComplementPath.lean:574-576`). The decisive force-inclusive result is
`residualDatum_physicalSlice` (`ComplementPath.lean:612-621`), backed by
`residualCarrier_physical` (`ComplementPath.lean:578-600`). The latter explicitly
identifies the cylinder force with physical `f`: `C01.forcePath` is the physical
slice by rfl (`formalization/NSFormalization/Section4/C01/JetPaths.lean:82-90`),
and its `toLp` representative is used at `ComplementPath.lean:592-599`.

`residualDatum_jointRepresentative` supplies lane 195's exact `hres` for
`jointRepresentative U hpaths` by applying that theorem with
`jointRepresentative_slice`; the only final normalization is unfolding
`momentumResidualOfVelocity` and commuting addition
(`LerayBridge.lean:324-338`; definition at
`formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:50-59`).
No force agreement or physical residual agreement is assumed. The follow-up
uniqueness theorem at `LerayBridge.lean:340-351` is consequently unconditional
apart from the datum being compared.

### Canonical export, consumer, and the remaining 189 wiring

The internal canonical bridge chooses lane 194's same order-seven pair, derives
both smooth representatives and Helmholtz memberships, and transfers an arbitrary
consumer order through the common time derivative
(`LerayBridge.lean:379-430`). It retains `hnu : 0 < nu` and `hS : 0 < S`
(`LerayBridge.lean:301-302,438-440`), so its open interval is nonempty; there is no
vacuity at `S <= 0`.

The positive probe closes a locally copied `interior_momentum_identity` with no
`hres`, `hprojected`, Helmholtz, or agreement hypothesis
(`research/A01/probes/leray_bridge_195.lean:149-208`). Its replay succeeded and
its theorem has exactly the three standard axioms. The narrower export probe also
succeeds (`research/A01/probes/rev197_consumer_gap.lean:20-64`). However, that
consumer file defines its own lane-195 theorems (`leray_bridge_195.lean:33-130`)
instead of importing the now-landed `InteriorMomentum.lean`; the current worktree
does not contain the landed module because the branch is 29 commits behind.
Therefore the claim is type-compatible but the requested replay of the landed
consumer/fix6 composition has not been performed.

For the lead, the exact remaining 189 assembly is wiring, not another projector
theorem. Lane 194's `exists_complement_joint_representative` already gives the
existential `G`, slab smoothness, and slice agreement
(`ComplementPath.lean:648-657`). Its complement datum identity is at
`ComplementPath.lean:326-335`. Lane 189's accepted converse
`hasSymmetricJacobian_of_lerayComplement_orderZeroDatum`
(`erenup/189-A01-pressure-regularity:formalization/NSFormalization/Section4/A01/PressureRegularity.lean:257-270`)
gives the symmetric-Jacobian conjunct; `MemLp` follows from the L2 carrier and
slice agreement. This bridge plus lane 195 gives the interior pointwise equality
conjunct. The only remaining step to prove `PressureSupply`'s `exists G, ...` is
to instantiate those three results for the same `complementCarrier`, choose the
canonical velocity `jointRepresentative U hpaths` (the witness supplied at
`formalization/NSFormalization/Section4/A01/JointRepresentative.lean:552-563`),
and package the already supplied equality, smoothness, and
`MemLp`/symmetric-Jacobian conjuncts.

The zero-pair check is genuine: it constructs actual zero L2 carriers, datum
facts, smooth representatives, and both cylinder memberships before applying the
comparison (`research/A01/axioms_leray_bridge.lean:28-41`). It does not use
`False.elim`, an infinite norm, or an empty time interval.

All 25 source declarations print exactly
`[propext, Classical.choice, Quot.sound]`; the complete audit list is
`research/A01/axioms_leray_bridge.lean:7-15,43-58`.

## 3. Gaps and rejection findings

1. **Blocking hard-rule violation: the proof needs 800000 heartbeats.**
   `residual_difference_gradient` is wrapped in `maxHeartbeats 800000`
   (`LerayBridge.lean:220-224`), although the brief permits at most 400000.
   The attempts record knowingly reports this value
   (`research/A01/ATTEMPTS_LERAY_BRIDGE.md:30-38`). The canonical consumer and
   positive reviewer probe also use 800000
   (`research/A01/probes/leray_bridge_195.lean:147` and
   `research/A01/probes/rev197_consumer_gap.lean:18`). A fresh probe repeats the
   actual proof body under the allowed ceiling
   (`research/A01/probes/rev197_heartbeat_400k.lean:14-46`) and fails:

   ```text
   ../research/A01/probes/rev197_heartbeat_400k.lean:33:17: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (400000) has been reached

   Note: Use `set_option maxHeartbeats <num>` to set the limit.

   Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
   ../research/A01/probes/rev197_heartbeat_400k.lean:40:2: error: (deterministic) timeout at `tactic execution`, maximum number of heartbeats (400000) has been reached

   Note: Use `set_option maxHeartbeats <num>` to set the limit.

   Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
   ```

2. **The branch is not based on the current integration tree.** It is
   `ahead 4, behind 29`. The required exact command
   `git diff origin/erenup/integration --stat` does not show only the new bridge
   module and records: it reports 40 files, including deletions of the landed
   `InteriorMomentum.lean` and `MildGronwall.lean`. The three-dot name list also
   reintroduces lane 194's `ComplementPath.lean` because the merge base predates
   #199, even though the local and integration blob hashes are identically
   `26b7ffd7f670489ed550d60756335823069429a1`. Thus no pre-existing Lean source
   was textually modified, but the required clean current-base diff is not met.

3. **The superseding fix6 consumer interface is not replayed.** The export and
   report still target the old `cb1e875` selected-order prefix, not the stated
   fix6 `ha` plus same-carrier all-order `hpairs` context. The consumer probe
   redefines lane 195 instead of importing the landed module. The source suppresses
   the unused-variable linter at `LerayBridge.lean:433`: `velocity/hslice/hc3`
   are interface-only and do not enter the proof, while the inner theorem explicitly
   names the selected-order divergence input `_hdiv` (`LerayBridge.lean:363`).
   These are interface and drift-check failures, not objections to the core
   Helmholtz proof.

The worker report makes no remaining mathematical "not in the tree" claim.
For the interface gap above, the required whole-tree search

```text
rg -n 'interior_momentum_identity(_of_complement_paths)?|hprojected_of_cylinder.|PressureSupply|exists_complement_joint_representative|exists_smooth_lerayComplement_representative|pressureGradientField_of_carrier' formalization/NSFormalization/Section4
```

returns only `hprojected_of_cylinder`, `hprojected_of_cylinder'`, and
`exists_complement_joint_representative` in this stale worktree; it finds no
`InteriorMomentum` consumer or `PressureSupply`. Read-only inspection of
`origin/erenup/integration` confirms that `InteriorMomentum.lean` is landed, so
it must be replayed after updating the branch rather than being declared absent
from the project.

The substantive wrong-sign mutation remains valid. It changes subtraction to
addition while retaining all hypotheses
(`research/A01/probes/rev197_sign_mutation.lean:9-16`) and fails exactly as expected:

```text
../research/A01/probes/rev197_sign_mutation.lean:16:47: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?a + ?b - ?b
in the target expression
  P = P + G + G

A P G : RealVectorSobolev 0
hdecomp : A = P + G
hsol : (Leray.lerayComplement 0) P = 0
hgrad : (Leray.lerayComplement 0) G = G
⊢ P = P + G + G
```

Required fixes:

1. Refactor `residual_difference_gradient` so its actual proof elaborates at
   `maxHeartbeats <= 400000`; remove or lower all three 800000 wrappers and rerun
   the 400000 proof-body probe.
2. Update the lane onto current `origin/erenup/integration` so #199's lane-194
   files disappear from the three-dot patch and the two-dot stat contains no
   unrelated deletions.
3. Change the exported wrapper to the specified fix6 binder shape (`ha`, canonical
   force/datum, same-carrier all-order `hpairs`, `hpaths`, and
   `velocity/hslice/hc3`), and replay the actual landed
   `interior_momentum_identity` or `_of_complement_paths` without independent
   `hprojected` or `hresidualAgreement`.
4. Update `REPORT_197.md` and `ATTEMPTS_LERAY_BRIDGE.md` to record the compliant
   heartbeat value and the actual fix6/landed-consumer replay.

## 4. Commands and results

All Lake commands were run from `verification/` after
`. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`. No git command changed refs,
the index, or commits.

`lake build NSFormalization.Section4.A01.LerayBridge` exited 0. The exact full
output is 205 lines / 11,970 bytes of replayed dependency warnings; it contains
no diagnostic naming `LerayBridge.lean` and ends exactly:

```text
Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
Build completed successfully (10249 jobs).
```

`lake env lean ../formalization/NSFormalization/Section4/A01/LerayBridge.lean`:

```text
(zero output; exit 0)
```

`lake env lean ../research/A01/axioms_leray_bridge.lean` exited 0 with the exact
output:

```text
'NSFormalization.Section4.A01.physicalResidual_datum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.gradient_datum_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.solenoidal_datum_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.solenoidal_datum_zero_of_cylinder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.gradient_datum_fixed_of_cylinder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.projected_datum_of_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.lowered_projected_datum_of_cylinder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.hprojected_of_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinder_source_complement_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.leray_value_solenoidal' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.leray_value_complement_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.laplacianEvaluation_solenoidal' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderResidual_solenoidal' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.residual_difference_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.ordinaryLift_unprojectedResidual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.ordinaryResidual_helmholtz' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.residualDatum_jointRepresentative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.physicalResidual_eq_residualDatum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.hprojected_of_canonical_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.hprojected_of_cylinder'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.LerayBridgeTime.vectorRepresentative_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.LerayBridgeTime.vectorRepresentative_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.LerayBridgeTime.jointRepresentative_temporalDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.LerayBridgeTime.ae_eq_of_isSobolevDatum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.LerayBridgeTime.jointRepresentative_temporalDerivative_of_cylinder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

There was no fourth axiom and no missing declaration.

`lake env lean ../research/A01/probes/leray_bridge_195.lean`:

```text
'NSFormalization.Section4.A01.canonical_interior_momentum_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`lake env lean ../research/A01/probes/rev197_consumer_gap.lean`:

```text
(zero output; exit 0)
```

The wrong-sign and 400000-heartbeat probes exited 1 with the exact expected
errors pasted in part 3.

`LEAN_NUM_THREADS=6 make check` exited 0. Its full output is 28,234 lines /
1,159,606 bytes; the exact final block is:

```text
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`git diff --check origin/erenup/integration...HEAD` had zero output and exited 0.
The exact forbidden-token search over both new modules, the axiom file, and all
lane/reviewer probes had zero output. The exact heartbeat search was:

```text
research/A01/probes/leray_bridge_195.lean:147:set_option maxHeartbeats 800000 in
research/A01/probes/rev197_consumer_gap.lean:18:set_option maxHeartbeats 800000 in
formalization/NSFormalization/Section4/A01/LerayBridge.lean:220:set_option maxHeartbeats 800000 in
```

No file under `verification/` is in either lane diff, so the conditional
`scripts/gates.sh` and `check_contracts.py --base-ref origin/erenup/integration`
commands were not applicable. The current worktree contains only the mandated
review-report modification and the permitted `rev197_heartbeat_400k.lean` probe
from this review; no Lean source or lane record was edited.
