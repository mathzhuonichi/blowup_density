# Lane 192 — wiring all-order bounds to `hsob` and the cylinder pair

## Result

`Section4/A01/CylinderWiring.lean` closes the assembly step from the one allowed analytic input

```lean
hb : ∀ q (hq : 6 ≤ q),
  HasAprioriBound hq hν a (C01.forcePath (S := S) hf)
    (C01.forcePath_jetLp_continuous (S := S) hf) (R q)
```

to one ordinary carrier `U` on `Icc 0 S`.  For every `q ≥ 6`, that same carrier is represented by
an order-`q+1` cylinder path `u` with `hU`, divergence-freeness, angular invariance, and the exact
canonical forced Duhamel equation.  The same `U` has an order-`m` datum path of class `C^j` for
every `j,m`.  `cylinderPair_of_boundsInv` proves the identical conclusion from
`HasAprioriBoundInv`.

The constructor exports are `constructorInputs_of_bounds` and
`constructorInputs_of_boundsInv`.  At a fixed `q ≥ 6`, each returns one existential containing
`U`, `u`, the initial value, `hU`, `hdiv`, and the exact lane-180 `hsob` binder.  The former split
exports were deleted: separate existential calls do not provide any equality between their carrier
witnesses.  The stronger `cylinderPair_of_bounds` exports retain every `C^j_t H^m_x` datum path in
the same existential as `U`.

## Proof route

1. Set `F := C01.forcePath (S := S) hf` and
   `hF := C01.forcePath_jetLp_continuous (S := S) hf`.
2. Lane 187's `forcePath_sobolevPath_contDiffOn` discharges `hfs` at every order from `hf`.
3. Lane 188's primed form of lane 186, `compatible_carriers_of_bounds'` (or its `Inv` form),
   selects one `U` and compatible cylinder paths at every order.  No uniqueness hypothesis remains
   in the theorem signature.
4. `forced_mild_divergenceFree` obtains `hdiv` directly from each exact Duhamel equation and `ha`.
5. The compatible order family is repackaged verbatim as lane 178's `hall`; then
   `datumPath_contDiffOn_all_orders` gives all `j,m` datum paths for the same `U`.

Step 5 is the same construction as `compatible_carriers_hall'`, but starts from its stronger
source `compatible_carriers_of_bounds'`: the weaker `hall'` conclusion existentially hides that
its force and initial witnesses are canonical, while `forced_mild_divergenceFree` needs those
canonical witnesses.  Retaining them is what makes `hdiv` and `hsob` refer to the very same `U`;
no additional assumption or analysis is introduced.

No norm-radius sign premise or initial-norm premise is added here: lane 186 enlarges each radius
internally by the initial norm before calling the prescribed-horizon theorem.

## Constructor-shape check and adaptation

The inspected head of `erenup/180-A01-b2-assembly` has already incorporated the fix2 horizon:
`carrierConstructor_of_localTheory` uses `u,U : C(Icc 0 S, ...)`,
`hU : ∀ t, ordinaryLift (U t) = value 1 (u t)`,
`hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0`, and

```lean
hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
  ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
  ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)
```

Thus no `T := S` transport and no `S+1` clamp adapter was needed.  The only Lean elaboration
adaptation was writing `(S := S)` on `C01.forcePath` and
`C01.forcePath_jetLp_continuous` in exported binder types: their horizon is implicit and is not
inferable from `hf` alone before the surrounding dependent type has elaborated.

The stronger `carrierConstructorFull_of_hyps` on lane 180 universally quantifies its three named
inputs over every seven-clause pair.  This lane instead targets the requested fixed compatible
pair and therefore feeds `carrierConstructor_of_localTheory` directly; it does not claim the
universal `CarrierConstructorFull` premise.

## The only remaining analytic input (besides lanes 189 and 190)

For the A01 pipeline after this wiring, the only remaining analytic input besides `hpg` (lane 189)
and `hc3` (lane 190) is A3-M2's all-order family `hb` above (or the invariant version).  Mild
uniqueness is no longer an input: lane 188 proves it.  Force time smoothness is no longer an input:
lane 187 derives it from `MemForceR`.  Cross-order carrier compatibility and all-order `hsob` are
theorems of this lane once `hb` is supplied.

Expected non-circular closure of `hb` (prose sketch, not proved here): first choose the order-six
local horizon and its order-six radius.  For an arbitrary higher-order mild solution on a
subwindow, lower it to order six and use lane 188 uniqueness to identify that lowering with the
already controlled base-order solution.  Lane 149's norm comparison then controls the `H²`
integral using the fixed **base-order** radius, not the unknown higher-order radius `R q`.  With
that integral cap fixed, lane 179's full-horizon Grönwall estimate permits each higher-order
`R q` to be chosen from the datum, force, horizon, and base-order bound before quantifying over
the higher-order solution.

Routing this argument through `cylinderPair_of_bounds` or `constructorInputs_of_bounds` would be
circular: both the all-order constructor carrier and its constructor-facing export already assume
the all-order family `hb` that this argument is meant to establish.  Likewise, feeding a
higher-order `R q` into the existing `256 * R^2 * T` cap and then using the resulting exponential
to choose that same `R q` is circular.  The order-six radius is the independent driver that avoids
both loops.

## Diagnostics and non-vacuity

Resolved while elaborating the new module:

* `Ambiguous term Space` after opening both `EulerSmoothLimit` and
  `NavierStokes.ProblemStatement`; fixed by keeping the latter `Space` and qualifying divergence.
* `don't know how to synthesize implicit argument S` at `C01.forcePath hf` in theorem headers;
  fixed by the explicit horizon annotation described above.

There are no unresolved Lean errors and no heartbeat override.  The conformance audit proves the
radius-zero `HasAprioriBound` family for zero initial datum and zero force.  Lane 188 uniqueness
identifies every mild solution with the zero path (including a direct treatment of the degenerate
`T = 0` window), whose norm is zero; the audit then instantiates `cylinderPair_of_bounds` without
assuming `hb`.
