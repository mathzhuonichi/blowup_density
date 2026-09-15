# Lane 187 — force-path `hfs` attempts

## Target

For the canonical carrier `F := C01.forcePath hf`, prove for every `q : ℕ`

```lean
ContDiffOn ℝ ∞
  (extendPath S hS.le
    (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q))
  (Icc (0 : ℝ) S).
```

The consumer only asks for `q ≥ 6`; the proof does not use that lower bound.

## Successful route

`MemForceR` gives an order-`q` path `G : ℝ → RealVectorSobolev q`, its realization property
`IsSobolevPath q f G`, and `ContDiffOn ℝ ∞ G (Ici 0)`.  The missing object was a fixed bounded
linear reconstruction

```lean
datumSobolevCLM q : RealVectorSobolev q →L[ℝ] SobolevSpace 1 q.
```

It is assembled as follows.

1. `jetOfDatumCLM q j` bundles `D01.jetOfDatum q j` as a continuous linear map, using
   `D01.norm_jetOfDatum_le`.
2. `datumWordCLM` evaluates the reconstructed order-`j` physical tensor on the spatial parts of a
   cylinder word and applies `ordinaryLift`.  Angular directions have spatial part zero.
3. `datumArrayCLM` collects the finitely many words in the ambient derivative array.
4. `datumArrayCLM_mem_sobolevSubspace` proves that this array satisfies the closed derivative-graph
   constraints for every datum.  On the dense family `schwartzDatum`, the array agrees with
   `ordinarySobolev` of the explicit `schwartzSmoothField`; compatibility then extends by
   `denseRange_weightedFourierLp`, the real projection, finite-product density, continuity, and
   closedness of `sobolevSubspace`.
5. `datumSobolevCLM` is `datumArrayCLM.codRestrict` to that closed subspace.

For a datum representing a smooth field, `datumSobolevCLM_eq_ordinarySobolev` identifies this
reconstruction with the vendor carrier.  The main proof composes `datumSobolevCLM q` with `G`,
restricts `Ici 0` to `Icc 0 S`, and uses `projIcc_of_mem` to remove `extendPath` on the target set.

## Rejected route and exact error

The first draft projected the ambient derivative array orthogonally onto `sobolevSubspace`.  This
would have made compatibility automatic, but the vendor's `LiftL2` ambient space has no registered
real inner-product instance.  Lean reported:

```text
failed to synthesize instance of type class
  InnerProductSpace ℝ (SobolevWord q → ↥(LiftL2 1))
```

The density/closedness proof above avoids adding instances or modifying vendor code and proves the
stronger fact that the unprojected reconstruction is already compatible.

## Packaging note

The requested lane-167 clauses are retained literally in `forcePath_of_memForceR_smooth`.  Lean's
ordinary `And` is nondependent: the proof term in the earlier continuity conjunct cannot be used as
the proof argument of `sobolevPath F` in a later conjunct.  The final clause therefore quantifies
that proof explicitly after `q`; proof irrelevance makes the resulting path independent of the
chosen proof.  A consumer destructs the package and applies the final clause to the preceding `hF`.

## Audits

`research/A01/axioms_hfs.lean` prints every declaration in the new module; every output is exactly
`[propext, Classical.choice, Quot.sound]`.  It also instantiates both exported theorems at
`f := 0`, `S := 1`, using `A04.memForceR_zero`.
