REJECT

## 1. What the lane claims

The sixth-fix report claims three things:

1. `PressureSupply` carries the canonical datum/force context, the same-carrier
   all-order `hpairs` family, all-order paths, and lane 190's selected
   representative, while its body remains the four required properties of one
   pressure-gradient field (`research/A01/REPORT_180.md:5-48`).
2. `rows_from_constructor_full` performs the landed 192 -> 190 -> pressure ->
   180 consumer loop with only `hb` and a scoped `PressureSupply` supplier as
   analytic inputs (`research/A01/REPORT_180.md:58-85`).
3. `rev180_194_195_197_pressure_supply.lean` is a real 194 -> 195 -> 197
   composition probe and states lane 197's current projector bridge
   (`research/A01/REPORT_180.md:89-97`).

Claims 1 and 2 are correct. Claim 3 is false and is a mandatory sixth-fix
deliverable, so the lane is not acceptable yet.

### F1 — blocking: the claimed lane-197 handoff is not the current export

The committed probe introduces its own hypothesis named
`hprojected_of_cylinder` at
`research/A01/probes/rev180_194_195_197_pressure_supply.lean:61-76`. That
hypothesis is generic in an arbitrary `w` and `hcomplement`, and its right side
uses `Classical.choose (hcomplement.2 t)`. It is the old lane-195 adapter input,
not lane 197's current export.

At review time branch `erenup/197-A01-leray-bridge` is at `3460456`. Its
current fix-6 export is named `hprojected_of_cylinder''` and has the complete
`PressureSupply` prefix (`hq hν hS f hf a ha U hpairs hpaths velocity hslice
hc3`); its conclusion is tied specifically to
`ComplementPath.residualDatum hf hν hS a U hpairs t`
(`erenup/197-A01-leray-bridge:formalization/NSFormalization/Section4/A01/LerayBridge.lean:459-498`).
This is also the shape the operative brief referred to as
`hprojected_of_cylinder'`; the branch advanced by one further fix/name after
the brief was written.

The reviewer probe copies the current conclusion at
`research/A01/probes/rev180_sixth_bridge_mismatch.lean:41-47` and attempts the
committed probe's handoff at line 63. Lean rejects it:

```text
../research/A01/probes/rev180_sixth_bridge_mismatch.lean:63:2: error: Type mismatch
  h197
has type
  ∀ (t : ℝ) (ht : t ∈ Ioo 0 S),
    (lowerVectorL 6 0 ⋯) (R ⟨t, ⋯⟩) =
      ComplementPath.residualDatum hf hν hS a U hpairs ⟨t, ⋯⟩ -
        (Leray.lerayComplement 0) (ComplementPath.residualDatum hf hν hS a U hpairs ⟨t, ⋯⟩)
but is expected to have type
  ∀ (t : ℝ) (ht : t ∈ Ioo 0 S),
    (lowerVectorL 6 0 ⋯) (R ⟨t, ⋯⟩) = Classical.choose ⋯ - (Leray.lerayComplement 0) (Classical.choose ⋯)
```

The committed probe also assumes `hresidualAgreement` instead of deriving it
from lane 194 (`research/A01/probes/rev180_194_195_197_pressure_supply.lean:58-60`),
even though lane 194 proves the physical residual bridge in
`formalization/NSFormalization/Section4/A01/ComplementPath.lean:578-621`.
Finally, `hclosedSlices` assumes the entire `MemLp ∧ HasSymmetricJacobian`
conclusion (`research/A01/probes/rev180_194_195_197_pressure_supply.lean:77-84`)
without identifying the exact lane-189 helper or saying which clauses it
supplies. Thus the file compiles, but it does not establish the cross-lane
compatibility that the sixth brief specifically required.

## 2. What is actually in Lean

### The production interface is correct

`PressureSupply` has the requested binder order
`hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3`
(`formalization/NSFormalization/Section4/A01/ConstructorAssembly.lean:365-389`).
Its `hpairs` conjunction is alpha/qualification-identical to lane 194's family:
ordinary realization, divergence freedom, angular invariance, and the canonical
force/datum Duhamel equation at every order `p ≥ 6`
(`ConstructorAssembly.lean:370-381`, `ComplementPath.lean:516-526`). Its body
is unchanged: one `G`, interior identity on `Ioo 0 S`, joint smoothness on
`Ico 0 S ×ˢ univ`, and per-time `MemLp ∧ HasSymmetricJacobian`
(`ConstructorAssembly.lean:390-396`).

`CarrierConstructorFull` retains exactly that family and the same `U`
(`ConstructorAssembly.lean:402-431`). `carrierConstructorFull_of_hyps` obtains
its order-`q` carrier data from `hpairs q hq`, not from a second carrier
(`ConstructorAssembly.lean:435-444`). The resulting `ClassicalSolutionR`
contains the requested velocity and closed slice identity. Its structure fields
have the correct `Ico`/`Ioo` domains
(`formalization/NSFormalization/Section4/A02/SolutionClass.lean:114-138`), and
they are assembled at `ConstructorAssembly.lean:300-328`.

The consumer loop is also faithful. `cylinderPair_of_bounds` returns one `U`,
the complete family, and `hpaths`
(`formalization/NSFormalization/Section4/A01/CylinderWiring.lean:36-57`).
`rows_from_constructor_full` opens precisely those witnesses, passes `U` and
`hpaths` to lane 190, and then asks for `PressureSupply`
(`ConstructorAssembly.lean:583-590`). Only after construction does it
specialize `hpairs q hq` for the comparison rows
(`ConstructorAssembly.lean:591-595`). The only analytic inputs left in the
theorem are `hb` and `hpressure` (`ConstructorAssembly.lean:547-572`).

The named context is not vacuous. `hS : 0 < S` makes the horizon genuine, and
the all-order zero cylinder family constructs an actual `PressureSupply`
(`research/A01/probes/rev180_pressure_supply_zero.lean:98-165`). The
conformance file also applies the assembly theorem to the zero pair and
produces a `ClassicalSolutionR` whose velocity is zero
(`research/A01/axioms_b2_assembly.lean:34-96`). There is no `⊤.toReal`,
empty-horizon, or dropped-argument trick.

The mathematical domains agree with the paper: the local theory gives a common
interval with all spatial/time orders and one-sided initial derivatives
(`paper/sections/appendix-a-local-theory.tex:60-77`), while its mild equation is
the projected forced equation (`paper/sections/appendix-a-local-theory.tex:109-116`).
The module's conditional construction is a faithful field-by-field realization
of those facts; it does not claim to prove the remaining pressure supply.

### Hygiene

The only production module in the branch delta is the new
`ConstructorAssembly.lean`; no pre-existing Lean module was changed. The other
tracked changes are records and probes. There is no `sorry`, `admit`, `axiom`,
or `native_decide` in the lane Lean files and no `maxHeartbeats` override. Every
audited production declaration prints exactly
`[propext, Classical.choice, Quot.sound]`. The branch is `0` commits behind and
`8` ahead of `origin/erenup/integration`.

## 3. Gaps

The constructor itself has no record-field hole. The honest remaining
cross-lane work is:

1. use the exact current lane-197 export and adapt its canonical
   `residualDatum` conclusion to lane 195 without replacing it by an older,
   stronger generic hypothesis;
2. derive residual agreement from the landed lane-194 theorem rather than
   assuming it;
3. obtain the closed-slab pressure representative from lane 189's exact
   interface. On branch `erenup/189-A01-pressure-regularity`, the relevant
   theorem is `exists_smooth_lerayComplement_representative`; it returns the
   slice identity, slab smoothness, and both per-time clauses
   (`erenup/189-A01-pressure-regularity:formalization/NSFormalization/Section4/A01/PressureRegularity.lean:398-423`).
   `MemLp` comes from a.e. equality with the `Lp` complement carrier at lines
   419-420; `HasSymmetricJacobian` comes from the Helmholtz-converse lemma
   `hasSymmetricJacobian_of_lerayComplement_orderZeroDatum` at lines 254-270.

I checked the entire landed `formalization/NSFormalization/Section4` tree before
accepting that dependency:

```text
$ grep -rn "exists_smooth_lerayComplement_representative\|hasSymmetricJacobian_of_lerayComplement_orderZeroDatum\|memLp_of_isSobolevDatum_zero\|hprojected_of_cylinder'" formalization/NSFormalization/Section4
<no output>
```

So these exact exports are not yet landed; they exist on the cited 189/197
branches. This remaining work is expected assembly work, but the committed
probe must represent it honestly and exactly.

## 4. Commands and results

All Lean commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

### Branch and delta

```text
$ git rev-list --left-right --count origin/erenup/integration...HEAD
0	8

$ git diff --name-only origin/erenup/integration...HEAD -- formalization/NSFormalization/Section4/A01
formalization/NSFormalization/Section4/A01/ConstructorAssembly.lean

$ git diff --name-only origin/erenup/integration...HEAD -- verification
<no output>
```

Because `verification/` is untouched, the conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration` gates do not apply.
`make check` still ran its ordinary architecture/contract checks.

The exact tracked stat was:

```text
 .../Section4/A01/ConstructorAssembly.lean          | 597 +++++++++++++++++++++
 research/A01/A3_SPLIT.md                           |  62 ++-
 research/A01/ATTEMPTS_B2_ASSEMBLY.md               | 222 ++++++++
 research/A01/REPORT_180.md                         | 133 +++++
 research/A01/REVIEW_180-A01-b2-assembly.md         | 376 +++++++++++++
 research/A01/axioms_b2_assembly.lean               | 145 +++++
 .../probes/rev180_194_195_197_pressure_supply.lean | 141 +++++
 .../probes/rev180_actual_supplier_pipeline.lean    |  75 +++
 research/A01/probes/rev180_constructor_loop.lean   |  71 +++
 research/A01/probes/rev180_divergence_closed.lean  |  31 ++
 research/A01/probes/rev180_h189_unsat.lean         |  57 ++
 research/A01/probes/rev180_hsob_compat.lean        |  26 +
 research/A01/probes/rev180_mutation_fail.lean      |  49 ++
 .../rev180_pressure_gradient_representative.lean   | 152 ++++++
 .../A01/probes/rev180_pressure_residual_fail.lean  |  17 +
 .../rev180_pressure_supply_hpairs_mismatch.lean    |  65 +++
 .../A01/probes/rev180_pressure_supply_zero.lean    | 167 ++++++
 .../probes/rev180_rows_supplier_mismatch.lean      |  27 +
 .../A01/probes/rev180_sobolev_residual_fail.lean   |  20 +
 19 files changed, 2432 insertions(+), 1 deletion(-)
```

The reviewer-only mismatch probe is untracked and therefore not in that
worker-commit stat.

### Build and direct checks

The unfiltered build exited `0`; it replayed warnings only from pre-existing
dependencies and no warning from `ConstructorAssembly`. Exact concise capture:

```text
$ set -o pipefail; LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ConstructorAssembly 2>&1 | tail -n 1
Build completed successfully (10255 jobs).
EXIT: 0
```

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/ConstructorAssembly.lean
<no output>
EXIT: 0
```

The axiom audit exited `0` with exact output:

```text
'NSFormalization.Section4.A01.constructedVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.constructedVelocity_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.constructedVelocity_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.velocity_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.velocitySobolev_of_hslice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.pressurePotential_contDiffOn_slab' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.momentum_of_supplied_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.carrierConstructor_of_localTheory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.CarrierConstructorFullClamped' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.PressureSupply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.CarrierConstructorFull' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.carrierConstructorFull_of_hyps' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.apriori_rows_of_hslice_same_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.rows_from_constructor_full' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Probes

The following positive probes all exited `0`:

```text
rev180_194_195_197_pressure_supply.lean       <no output>
rev180_actual_supplier_pipeline.lean          <no output>
rev180_divergence_closed.lean                 <no output>
rev180_h189_unsat.lean                        <no output>
rev180_hsob_compat.lean                       <no output>
rev180_pressure_gradient_representative.lean  <no output>
rev180_pressure_supply_hpairs_mismatch.lean   <no output>
rev180_pressure_supply_zero.lean              <no output>
```

`rev180_constructor_loop.lean` exited `0` with exact output:

```text
'NSFormalization.Section4.A01.PressureSupply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.rows_from_constructor_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.carrierConstructorFull_of_hyps' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The historical negative probes failed as documented:

```text
rev180_pressure_residual_fail.lean:15:56: error: Application type mismatch: The argument
  hc3
has type
  ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)
but is expected to have type
  ContDiff ℝ ∞ (pressureGradientOfVelocity ν f velocity)
EXIT: 1

rev180_rows_supplier_mismatch.lean:25:2: error: Type mismatch
  exists_joint_smooth_representative hS
has type
  ∀ (U : C(↑(Icc 0 S), ↥EulerMeanSolenoidal.L2)),
    (∀ (j m : ℕ),
        ∃ G,
          ContDiffOn ℝ (↑j) G (Icc 0 S) ∧
            ∀ (t : ↑(Icc 0 S)), NSFormalization.Section4.D01.IsSobolevDatum (↑m) (↑↑(U t)) (G ↑t)) →
      ∃ u, (∀ (t : ↑(Icc 0 S)), (fun x => u (↑t, x)) =ᵐ[volume] ↑↑(U t)) ∧ ContDiffOn ℝ ∞ u (Ico 0 S ×ˢ univ)
but is expected to have type
  ∀ (U : C(↑(Icc 0 S), ↥EulerMeanSolenoidal.L2)),
    ∃ velocity,
      (∀ (t : ↑(Icc 0 S)), (fun x => velocity (↑t, x)) =ᵐ[volume] ↑↑(U t)) ∧ ContDiffOn ℝ ∞ velocity (Ico 0 S ×ˢ univ)
EXIT: 1

rev180_sobolev_residual_fail.lean:18:52: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  b ≥ 0
  a ≥ 0
  a - b ≥ 2
where
 a := ↑m
 b := ↑q
EXIT: 1
```

The mandatory substantive mutation flips the slice time from `t` to `-t`; it
fails because the theorem proves the original statement, not because an
argument was dropped:

```text
../research/A01/probes/rev180_mutation_fail.lean:46:2: error: Type mismatch
  carrierConstructor_of_localTheory hS u U hU hdiv f velocity hslice hsob hc3 G hG_int hG
has type
  ∃ w, w.velocity = velocity ∧ ∀ (t : ↑(Icc 0 S)), (fun x => w.velocity (↑t, x)) =ᵐ[volume] ↑↑(U t)
but is expected to have type
  ∃ w, w.velocity = velocity ∧ ∀ (t : ↑(Icc 0 S)), (fun x => w.velocity (-↑t, x)) =ᵐ[volume] ↑↑(U t)
EXIT: 1
```

The new sixth-interface reproduction is the F1 error quoted above and exits
`1` as expected.

### Repository check

The full unfiltered `make check` exited `0`. The exact displayed tail from the
successful pipefail-protected rerun was:

```text
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
EXIT: 0
```

### Required fixes

1. Replace the probe's locally invented old `hprojected_of_cylinder` hypothesis
   with the exact current lane-197 fix-6 export statement (currently
   `hprojected_of_cylinder''` at branch commit `3460456`), including its full
   prefix and canonical `residualDatum` conclusion; adapt lane 195 by datum
   uniqueness if necessary.
2. Derive `hresidualAgreement` from landed lane 194 instead of assuming it.
3. State/use lane 189's exact complement-representative obligation and record
   explicitly that it supplies slab smoothness, `MemLp`, and symmetric Jacobian;
   update `REPORT_180.md:89-97` so it no longer claims the current probe already
   does these things.
