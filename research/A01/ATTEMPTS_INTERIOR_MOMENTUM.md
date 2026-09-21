# Lane 195: interior momentum attempts

## Scope

This lane intentionally exports a conditional interior identity. Proving the
cylinder/Fourier projector bridge belongs to lane 197, not lane 195. The
generic bounded-evaluation derivative, the cylinder derivative consumer, the
order-zero assembly, and the lane-194 interface adapter are proved without
`sorry` or new axioms.

## What `hprojected` honestly says

The short name hides two logically distinct facts. Its equality identifies the
cylinder Leray projector after ordinary descent and order lowering with the
Fourier multiplier `A - lerayComplement 0 A`. Because `R` is built from the
cylinder force `fc` while `A` represents the physical residual built from `f`,
the same equality also asserts agreement between the physical force/residual of
the joint representative and the descended unprojected cylinder residual.
`hres` alone does not connect those two carriers.

The supplier chain is therefore:

* lane 197 compares the projectors under its cylinder Helmholtz-decomposition
  and representative inputs (`hprojected_of_cylinder` has this exact target);
* lane 194 supplies the complement path, its joint representative, and the a.e.
  physical residual bridge;
* lane 192 supplies the canonical wiring
  `fc = sobolevPath (C01.forcePath hf)
  (C01.forcePath_jetLp_continuous hf) q` and
  `u₀ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff`, with `a`
  solenoidal.

The compatibility theorem `interior_momentum_identity` retains the composite
argument because lane 197's checked consumer theorem exports that equality
verbatim. The new lane-194 adapter does split the honest halves: its
`hprojected` compares the projectors on lane 194's selected `residualSlice`
datum, while `hresidualAgreement` separately states that this descended slice
agrees a.e. with the physical residual of the joint representative.

## Lane-194 adapter

Lane 194 is not imported because its branch is not merged. Its exported shape
is copied into `interior_momentum_identity_of_complement_paths` as a hypothesis:
after the outer `w` witness is introduced, it provides all datum paths and, for
each closed-interval time, an existential datum of `residualSlice` together
with its complement datum. The separate a.e. residual bridge is an explicit
adapter input. The adapter defines

```lean
A t := Classical.choose (hcomplement.2 t)
```

and uses `Classical.choose_spec` for both the physical residual and complement
facts. Lane 194's a.e. slice equality transfers the complement datum directly
to the smooth joint representative. Consequently no artificial globally
selected `A`, `L²` packaging of `w`, or endpoint regularity is required from an
assembly caller.

## Positive and negative checks

`rev195_canonical_inputs.lean` checks that both assembly exports accept lane
192's canonical `fc` and `u₀` expressions, while retaining the solenoidal datum
hypothesis. `rev195_missing_bridge.lean` is deliberately negative: removing
the composite bridge leaves exactly that equality unsolved, recording that the
identity is not derivable without it. `rev195_interval_mutation.lean` remains
the endpoint mutation; replacing `Ioo` by `Icc` fails at `Icc_mem_nhds`.
