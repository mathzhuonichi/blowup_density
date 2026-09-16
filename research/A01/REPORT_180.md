# Lane 180 report — A01 B2 constructor assembly, sixth fix

## 1. Exact pressure boundary

`PressureSupply` now retains the same-carrier, all-order cylinder family used
by lanes 194/195/197, together with the canonical solenoidal datum and force.
Its exact declaration is:

```lean
def PressureSupply {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (f : SpaceTimeField)
    (hf : NSFormalization.Section4.D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpairs : ∀ p (hp : 6 ≤ p),
      ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (p + 1)),
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (p + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hp
            (sobolevPath (NSFormalization.Section4.C01.forcePath (S := S) hf)
              (NSFormalization.Section4.C01.forcePath_jetLp_continuous
                (S := S) hf) p))
          (ordinarySobolev (p + 1) a.toLp a.translation_contDiff) u t)
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) : Prop :=
  ∃ G : SpaceTimeField,
    (∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
      G (t, x) = pressureGradientOfVelocity ν f velocity (t, x)) ∧
    ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
    ∀ t ∈ Ico (0 : ℝ) S,
      MemLp (fun x : Space => G (t, x)) 2 volume ∧
      RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x))
```

This is lane 194's `hpairs` spelling, including angular invariance and the
canonical force/Duhamel equation at every `p ≥ 6`.  A single order-`q`
solution is no longer an argument.  The conclusion is unchanged: one field
with the interior identity, closed-slab smoothness, per-time `MemLp`, and
symmetric spatial Jacobian.

`CarrierConstructorFull` carries the same `hpairs`, `hpaths`, and lane-190
representative.  `carrierConstructorFull_of_hyps` specializes
`hpairs q hq` internally to obtain the `u/hU/hdiv/hduh` data required by the
fixed-pair constructor; the angular-invariance and Duhamel fields remain
available to the upstream pressure pipeline.

## 2. Family-preserving consumer loop

`rows_from_constructor_full` now invokes the family-returning lane-192 theorem
by its exact name:

```lean
obtain ⟨U, _hU0, hpairs, hpaths⟩ :=
  cylinderPair_of_bounds hf hν hS a ha R hb
obtain ⟨velocity, hslice, hc3⟩ :=
  exists_joint_smooth_representative hS U hpaths
have hpressure' := hpressure U hpairs hpaths velocity hslice hc3
```

It no longer calls `constructorInputs_of_bounds`, which specializes the family
at `q` and therefore cannot feed lane 194.  After construction, the consumer
specializes `hpairs q hq` only to expose the output `u`, its norm bound, and the
two comparison rows.  Consequently, apart from the canonical
force/datum/positivity context, the only analytic hypotheses of the consumer
are `hb` and the scoped `PressureSupply` instance for the selected objects.

The fixed-pair conclusion remains

```lean
∃ w : ClassicalSolutionR ν (fun x => velocity (0,x)) f S,
  w.velocity = velocity ∧
  ∀ t : Icc (0 : ℝ) S,
    (fun x => w.velocity (↑t,x)) =ᵐ[volume] ⇑(U t)
```

and all `ClassicalSolutionR` fields are discharged exactly as before.

## 3. Composition and satisfiability probes

`probes/rev180_194_195_197_pressure_supply.lean` imports the landed
`ComplementPath` and `InteriorMomentum` modules.  It uses lane 194's actual
complement path and joint representative, calls
`interior_momentum_identity_of_complement_paths`, and states the current
lane-197 `hprojected_of_cylinder` conclusion as the explicit bridge hypothesis.
The resulting interior identity, smooth complement field, residual agreement,
and closed-slab slice package assemble directly into the new
`PressureSupply`.  The carrier in `hpairs`, `hpaths`, the complement
construction, and the target is literally the same `U`.

`probes/rev180_pressure_supply_zero.lean` supplies a constant-zero realization
at every order `p ≥ 6`, including angular invariance and the canonical zero
Duhamel equation.  It also proves the canonical zero datum is solenoidal and
constructs `G := 0`, so the recut proposition has a concrete inhabitant.

The fifth review's
`probes/rev180_pressure_supply_hpairs_mismatch.lean` is retained under its
historical name but is now a positive check: the exact family passes through
`PressureSupply` verbatim.  The failed single-order design is recorded as
negative example 5 in `ATTEMPTS_B2_ASSEMBLY.md`.

The earlier supplier and consumer probes were updated to call
`cylinderPair_of_bounds`, retain `hpairs`, and pass `ha` through the pressure
boundary.  The historical negative probes for the unscoped lane-190 and
arbitrary-velocity pressure interfaces remain unchanged.

## 4. Verification

The following gates were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`:

```text
lake build NSFormalization.Section4.A01.ConstructorAssembly
lake env lean ../formalization/NSFormalization/Section4/A01/ConstructorAssembly.lean
lake env lean ../research/A01/axioms_b2_assembly.lean
# each positive rev180 probe individually
# each historical negative probe individually, requiring a nonzero exit
make check
```

The module build and direct check succeed.  All positive probes, including the
194/195/197 pipeline, zero supply, family handoff, actual supplier pipeline,
and consumer loop, compile.  The axiom audit reports exactly
`[propext, Classical.choice, Quot.sound]` for every production declaration.
The repository `make check` gate succeeds.

## Lead note (2026-09-16, sixth review)

The sixth codex review accepted the production constructor interface and rejected only the research-side cross-lane
pipeline probe (stale copy of lane 197's export; `hresidualAgreement` assumed). Lead decision: the probe is marked
historical (`probes/historical_rev180_194_195_197_pressure_supply.lean`); the real cross-lane pipeline is lane 189's
`pressureSupply_of_pieces` (branch `erenup/189-A01-pressure-regularity`, reviewed ACCEPT-WITH-NOTES), which proves this
module's `PressureSupply` verbatim from the landed lanes 194/195/197 and imports this module once it lands. The
constructor is therefore conditional on exactly `hb` (lanes 193/196/198/199) and `PressureSupply` (lane 189).
