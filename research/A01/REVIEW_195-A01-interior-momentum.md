REJECT

## 1. What the lane claims

The worker report is internally honest: it claims Goals 1 and 2, and explicitly says
that Goal 3/P4b is only conditional on an additional `hprojected` supplier and is not
closed (`research/A01/REPORT_195.md:5-21`, `research/A01/REPORT_195.md:130-138`,
`research/A01/REPORT_195.md:153-162`).  The four displayed signatures in the report
match the declarations in Lean: `jointRepresentative_temporalDerivative`
(`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:54-73`),
`vectorRepresentative_sub` (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:25-34`), the cylinder
specialization (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:100-124`), and the conditional final
identity (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:200-243`).  The four additional declarations
listed at `research/A01/REPORT_195.md:103-116` also exist with the described types at
`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:38-49`,
`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:77-90`,
`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:127-141`, and
`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:146-193`.

The underlying mathematical sign is correct.  The paper has
`∂ₜu - νΔu = -P div(u⊗u) + Pf` and
`∇p = (I-P)(f-div(u⊗u))` (`paper/sections/02-preliminaries.tex:80-92`);
the tree defines the unprojected residual as `f - advection + νΔu` and the pressure
gradient as that residual minus `temporalDerivative`
(`formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:50-59`).

## 2. What is in Lean

1. **Goal 1 is correct, including the endpoint discipline.**
   `vectorRepresentative_hasDerivAt` composes the datum derivative with the component
   evaluation CLMs built from `PiLp.proj`, the Sobolev subtype, `angularEvaluation`,
   and `Complex.reCLM`, then reassembles the vector (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:38-49`).
   Thus this is genuine bounded-linear evaluation commuting with differentiation at
   order `s >= 2`, not use of the order-three spatial derivative theorem.  The main
   proof obtains `Icc 0 S in nhds t` from the two strict inequalities, applies
   `hderiv.hasDerivAt`, and transfers the derivative through an eventually pointwise
   equality (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:65-73`).  The equality used is
   `vectorRepresentative_eq_of_datums`, not `jointRepresentative_slice`: both the
   order-two canonical datum and `G r` represent the same `U r`
   (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:70-72`; the source equality theorem is
   `formalization/NSFormalization/Section4/A01/JointRepresentative.lean:442-452`).
   `jointRepresentative_slice` is only an a.e. slice statement
   (`formalization/NSFormalization/Section4/A01/JointRepresentative.lean:483-495`) and is not misused.  The conclusion is
   exactly the ambient `fderiv`-based `temporalDerivative`
   (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:53-56`) and is
   stated only for `t in Ioo 0 S`; there is no conclusion at `0` or `S`.

2. **Goal 2 is genuine pointwise linearity.**
   `vectorRepresentative_sub` is quantified over arbitrary `A B : RealVectorSobolev s`
   and every `x`, and proves the result directly with `map_sub` and real-part
   linearity (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:25-34`).  It does not pass through an a.e.
   equality.  This agrees with the pointwise definition of `vectorRepresentative`
   (`formalization/NSFormalization/Section4/A01/JointRepresentative.lean:383-388`).

3. **The cylinder derivative theorem consumes lane 169 correctly.**
   Lane 169 gives `HasDerivAt (extendPath ... A) (R t) t` on `Ioo`, for
   `m + 2 <= q + 1` (`formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean:344-360`).
   The delivered theorem feeds its within version into Goal 1
   (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:117-124`) and obtains a pointwise-in-`x` identity on
   `Ioo`.  Its exact derivative carrier is `ordinaryResidualPath`, defined as the
   ordinary adjoint descent of the cylinder residual
   (`formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean:170-176`).  It is not literally the separately named
   `projectedResidualOrdinaryPath`; that name is the specialization where the cylinder
   force is `sobolevPath F hF q` (`formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean:228-243`).  Likewise,
   `ordinaryLift_projectedResidualOrdinaryPath` (`formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean:266-282`) is
   not used here.  Calling the result the ordinary projected residual is nevertheless
   semantically accurate because the cylinder residual uses `ForcedCylinderLocal.leray`.

4. **The order-zero assembly after a projected-datum identity is valid.**
   `interior_momentum_identity_of_datums` subtracts the two order-zero datum
   relations, rewrites `A - (A - complement A)`, obtains a.e. equality, and upgrades
   it using continuity of both spatial slices (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:178-193`).
   The regularity of `temporalDerivative` is taken only on the open interior slab
   (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:169-173`; upstream theorem
   `vendor/NavierStokesAndEuler/NavierStokes/ResidualRegularity.lean:36-52`).

5. **Axioms, non-vacuity, and hygiene pass.**
   The conformance file prints all eight declarations (`research/A01/axioms_interior_momentum.lean:10-17`)
   and contains exactly three constructed zero examples (`research/A01/axioms_interior_momentum.lean:19-52`,
   `research/A01/axioms_interior_momentum.lean:54-69`,
   `research/A01/axioms_interior_momentum.lean:75-145`).  The last fixes `q=6`,
   `m=2`, and `nu=S=1` and discharges
   every named input, so these are genuine inhabitants rather than empty-interval or
   `top.toReal` tricks.  `hS : 0 < S` also prevents the interior interval from being
   empty in the main theorem (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:200-203`).  There is no
   `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` in the new Lean
   files.  The only formalization module in the branch diff is a newly added module;
   no pre-existing Lean module was modified.

## 3. Gaps and findings

### Blocking: the requested P4b theorem is not proved

The final theorem adds

```lean
hprojected : forall t in Ioo 0 S,
  lowerVectorL (m : Real) 0 ... (R t) = A t - Leray.lerayComplement 0 (A t)
```

at `formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:226-228` and
uses it directly at `formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:236-237`.
This equality is the central bridge that the brief
asked the lane to establish, so a theorem conditional on it is strictly weaker than
Goal 3.  The permitted conformance probe with the brief inputs but without that extra
hypothesis (`research/A01/probes/rev195_missing_bridge.lean:17-48`) reproduces the
failure:

```text
../research/A01/probes/rev195_missing_bridge.lean:46:89: error: unsolved goals
...
⊢ ∀ (t : ℝ) (ht : t ∈ Ioo 0 S),
    (lowerVectorL (↑m) 0 ⋯) (R ⟨t, ⋯⟩) =
      A ⟨t, ⋯⟩ - (Leray.lerayComplement 0) (A ⟨t, ⋯⟩)
```

This is the reason for `REJECT`; it is not a build or soundness failure.

### What `hprojected` really contains, and the lane-197 obligation

The cylinder projector is `id - sobolevGradientProjection`
(`formalization/NSFormalization/Source/ForcedCylinderLocal.lean:24-30`), whereas the
datum complement is a Fourier multiplier on `RealVectorSobolev`
(`formalization/NSFormalization/Section4/D01/LerayDatum.lean:251-264`).  The existing
lowering theorem only says that this datum complement commutes with `lowerVectorL`
(`formalization/NSFormalization/Section4/D01/LerayLowering.lean:150-156`).

Moreover, the final theorem takes independent physical `f` and cylinder `fc`:
`R` is a datum of the projected cylinder residual built from `fc`
(`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:204-216`), while
`A` is a datum of the physical residual built from `f`
(`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:217-225`).
Therefore `hprojected` is not merely “the two projectors
agree.”  It also bundles the missing force/carrier and physical-residual agreement
between `fc` and `f`.  `hres` itself does not provide that connection; it only says
that `A` represents the physical residual.

Lane 197 should prove a theorem with conclusion exactly

```lean
forall t in Ioo 0 S,
  lowerVectorL (m : Real) 0 (Nat.cast_nonneg m) (R t) =
    A t - Leray.lerayComplement 0 (A t)
```

from (a) an explicit canonical-force/descent relation tying `fc` to the physical
`f`, (b) the velocity descent `hU` and representative slice agreement, (c) `R` as
the datum of `ordinaryResidualPath`, and (d) `A` as the datum of the matching
physical residual.  Its mathematical core must show that cylinder `leray 1 q`, on
the angle-independent descended field, transports to the ordinary R3 Leray
projection and hence to `A - lerayComplement 0 A`.  It must not assume pressure or
the time-derivative identity.  Once proved, `interior_momentum_identity` should derive
the present `hprojected` argument internally.

The worker's “not yet in the tree” claim survives the required whole-Section4
search.  The searches

```text
grep -rnE 'ordinary.*[Ll]eray|[Ll]eray.*ordinary|projectedResidual.*lerayComplement|lerayComplement.*projectedResidual|hprojected|momentumResidualOfVelocity.*ordinaryResidual|ordinaryResidual.*momentumResidualOfVelocity' formalization/NSFormalization/Section4
grep -rnE 'ordinaryLift.*(gradientProjection|solenoidalProjection|starProjection|leray)|((gradientProjection|solenoidalProjection|starProjection|leray).*)ordinaryLift' formalization/NSFormalization/Section4 vendor/NavierStokesAndEuler/Euler vendor/HeliCorgi/Formal
```

found no completed ordinary-lift/projector intertwining theorem.  The first search
found only the assumed `hprojected` uses in `ConstructorPressure.lean:99,136` and
this lane, plus unrelated lowering consumers; the second produced no output.
`projectedResidualOrdinaryPath`, its lift theorem, and the lowering commutation are
real ingredients (`DatumPathDeriv.lean:238,268`; `LerayLowering.lean:155`), but none
has the missing conclusion.

### Lane-194 interface note for the lead (non-blocking by itself)

The now-visible lane-194 brief asks for a per-time existential physical residual
datum and complement realization, plus a smooth representative with a.e. slices
(`origin/erenup/integration:collaboration/briefs/194-A01-complement-path.md:27-46`).
Lane 195 instead accepts a globally selected `A : Icc 0 S -> RealVectorSobolev 0`
and `w : Icc 0 S -> EulerMeanSolenoidal.L2` (`formalization/NSFormalization/Section4/A01/InteriorMomentum.lean:220-225`).
The shapes are mathematically compatible after choosing the per-time `A` and
packaging/proving the `L2` carrier, but they are not literally the same exported
shape.  An adapter is needed.  More importantly, lane 194's promised physical
residual agreement can supply the `hres` side, but it does not by itself connect the
independent `fc` to `f`; that belongs in lane 197.  Per the lead's instruction, this
interface mismatch is a planning finding, not an additional rejection reason.

### Negative mutation

The substantive mutation widens Goal 1 from `Ioo 0 S` to `Icc 0 S`
(`research/A01/probes/rev195_interval_mutation.lean:12-26`).  Reusing the proof fails
at exactly the expected endpoint step:

```text
../research/A01/probes/rev195_interval_mutation.lean:26:51: error: Application type mismatch: The argument
  ht.left
has type
  0 ≤ t
but is expected to have type
  0 < t
in the application
  Icc_mem_nhds ht.left
```

This is a statement mutation, not omission of an argument, and confirms that the
strict interior hypothesis is load-bearing.

## 4. Commands and results

All Lake commands ran from `verification/` after sourcing `scripts/lean-env.sh`,
with `LEAN_NUM_THREADS=6`.

```text
$ lake build NSFormalization.Section4.A01.InteriorMomentum 2>&1 | tail -1
Build completed successfully (10031 jobs).
exit 0
```

The unfiltered build emitted only replayed warnings from imported pre-existing
modules; there was no warning from `InteriorMomentum.lean`.  The requested silent
variant and the direct module check were both exactly empty:

```text
$ lake -q --log-level=error build NSFormalization.Section4.A01.InteriorMomentum
exit 0; no output
$ lake env lean ../formalization/NSFormalization/Section4/A01/InteriorMomentum.lean
exit 0; no output
```

The axiom file compiled, including all three zero examples, with exact output:

```text
'NSFormalization.Section4.A01.vectorRepresentative_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.vectorRepresentative_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.jointRepresentative_temporalDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.ae_eq_of_isSobolevDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.jointRepresentative_temporalDerivative_of_cylinder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.pressureGradientOfVelocity_contDiffOn_interior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.interior_momentum_identity_of_datums' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.interior_momentum_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

`make check` exited 0.  Its exact tail was:

```text
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The standard gate script was also run.  Its exact filtered status output was:

```text
== make check
Ran 13 tests in 0.042s
OK
30 work items: ownership, contract registration and task cards consistent.
== lake build NSFormalization.Section4.A01.InteriorMomentum
Build completed successfully (10031 jobs).
== make test
== make test-mutations
== check_contracts
== gates OK
```

No file under `verification/` was touched, but the requested base-ref checker was
nevertheless run explicitly:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration | tail -3
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
exit 0
```

Hygiene and branch-diff output:

```text
$ rg -n '\b(sorry|admit|axiom|native_decide)\b' <new Lean files>
(no output)
$ rg -n 'set_option[[:space:]]+maxHeartbeats|maxHeartbeats' <new Lean files>
(no output)
$ git diff --name-status origin/erenup/integration...HEAD
A formalization/NSFormalization/Section4/A01/InteriorMomentum.lean
M research/A01/A3_SPLIT.md
A research/A01/ATTEMPTS_INTERIOR_MOMENTUM.md
A research/A01/REPORT_195.md
A research/A01/axioms_interior_momentum.lean
$ git diff --check origin/erenup/integration...HEAD
(no output; exit 0)
```

Fixes required:

1. Prove the lane-197 residual/projector carrier bridge from explicit canonical
   force and physical-residual agreement, then remove `hprojected` as an input to
   the exported `interior_momentum_identity`.
2. Add the small adapter from lane 194's per-time existential/raw-field export to
   the selected `A` and `L2` carrier shape consumed here.
3. Update the report's named-input discussion to say that the current
   `hprojected` bundles force/residual carrier agreement as well as projector
   identification.
