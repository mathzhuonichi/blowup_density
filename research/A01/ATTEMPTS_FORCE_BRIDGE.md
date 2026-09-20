# Lane 167 — attempts and decisions for the A01 force bridge

## Consumer interface audit

The constructor-facing API begins with a global paper force

```lean
f : A02.SpaceTimeField
hf : D01.MemForceR f
```

and needs a carrier path and its jet-continuity proof for `HasAprioriBound` and
`localTheory_on_prescribed_horizon`:

```lean
F : Icc (0 : ℝ) S → SmoothL2Field Space
hF : ∀ n, Continuous fun t => (F t).jetLp n
```

These data already exist canonically:

```lean
F := C01.forcePath hf
hF := C01.forcePath_jetLp_continuous hf
```

The physical force is not reconstructed from `F`.  The constructor keeps `f' := f`, reuses `hf`,
and obtains `A04.MemL1Hm f` from `A04.memL1Hm_of_memForceR hf`.  This is the direction implemented
by `forcePath_of_memForceR`.

## Rejected carrier-to-global direction

The first version defined `forceOfPath F` by reading `F(t).field` on `[0,S]` and setting it to zero
after `S`.  The zero tail gives compact time support, but it does not give a smooth global force.
If the endpoint slice is nonzero, the value at `S` is nonzero and every value immediately to its
right is zero, so the extension is discontinuous at `S`.

The reviewer probe `research/A01/probes/rev167_endpoint.lean` proves this obstruction for a
concrete nonzero compactly supported force in `F_R`:

```lean
¬ ForcePathSmoothness (C01.forcePath (S := (2 : ℝ)) endpointBump_memForceR)
```

Thus the old `ForcePathSmoothness`, `memForceR_forceOfPath`, `memL1Hm_forceOfPath`, and reverse
round-trip declarations were deleted.  They described only the exceptional subclass flat to all
orders at the right endpoint and were not the row the constructor consumes.  The old `hF` argument
to `memForceR_forceOfPath` was dead because the stronger smoothness premise subsumed it; deleting
that API removes the unused hypothesis.

`forceOfPath` remains only as a finite-horizon comparison operation.  No global smoothness or force
class membership is claimed for it.  Its supported statement is the pointwise on-horizon identity

```lean
forceOfPath (C01.forcePath (S := S) hf) (t.1, x) = f (t.1, x).
```

## Initial datum and lane 162

The previous statement

```lean
(∀ x, EulerSmoothLimit.divergence a.field x = 0) → a.field ∈ A02.initialClassR
```

treated pointwise divergence as a bare premise.  The cylinder output instead gives membership in
`EulerLiftedGradientSpace.divergenceFreeSpace`.  The reworked `initialClassR_of_smoothL2` imports
`Section4/A01/ConstructorDivergence.lean` and takes the hypotheses required by lane 162's
`divergence_ae_of_cylinder`: a cylinder slice `u`, its ordinary descent `U`, angular invariance,
`ordinaryLift U = value 1 u`, cylinder divergence-freeness, and
`a.field =ᵐ[volume] ⇑U`.

Applying that bridge yields a.e. vanishing of the coordinate divergence of `a.field`.  Since `a`
is a `SmoothL2Field`, the coordinate-divergence function is continuous; equality a.e. to zero is
therefore equality everywhere.  This supplies `A02.IsSolenoidal`, while `a.smooth` and
`a.integrable` supply `D01.MemHInfty`.

For a later time-dependent candidate velocity, lane 162's stronger
`divergence_of_cylinder_pointwise_of_contDiff` still requires the full `Z`/`hslice`/c3 spatial
smoothness handoff.  This lane does not claim those constructor inputs are already available.

## Non-vacuity and implementation notes

`research/A01/axioms_force_bridge.lean` prints every declaration's transitive axioms.  It constructs
a concrete nonzero compact spacetime bump in `MemForceR`, applies the canonical carrier package,
and checks the on-horizon identity at the nonzero endpoint.  It also instantiates every lane-162
hypothesis for the zero cylinder slice and obtains zero-field initial-class membership.

No `sorry`, `admit`, new axiom, `native_decide`, or heartbeat override is used.
