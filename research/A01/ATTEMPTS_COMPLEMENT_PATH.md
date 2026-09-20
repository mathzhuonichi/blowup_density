# Lane 194 — complement path

## Successful route

- Copied and namespaced the unprojected formula and finite smoothness proof from
  lane 189's `PressureRegularity.lean` with attribution; no branch import.
  Taking the complement of 178's projected residual would give the wrong object.
- `residual_datumPath` applies the existing cylinder regularity ladder and
  invariant-cylinder datum descent. The exact finite requirement is
  `k ≥ 6`, `k + 2 + 2*j ≤ q + 1`; the all-order proof takes
  `k := max 6 m`, `q := k + 2 + 2*j` and lowers to `m`.
- Restriction to order six proves that every such residual has the same ordinary
  L² value as the fixed residual built with the order-eight velocity (q=7).
- `datumPhysical := ordinaryValue 0 ∘ datumSobolevCLM 0` reconstructs an arbitrary
  zero-order datum. Its right-inverse identity follows first on smooth fields,
  then on the dense Schwartz datum family. This supplies the actual L² carrier.
- `lerayComplement_lowerVectorL` plus `isSobolevDatum_lower_iff` identify the
  complement at every order with the one fixed zero-order physical carrier.
- 190's generic representative theorem applies directly: its
  `EulerMeanSolenoidal.L2` is plain `Lp Space 2 volume`, without a divergence
  constraint. No time derivative is used at either endpoint.
- For the physical residual identity, the vendor's derivative and advection
  realization lemmas identify the cylinder values with derivatives of *any*
  smooth velocity representative. The auxiliary angular derivative contributes
  zero. Fubini descends the a.e. equality without taking an L² pointwise section.

## Failed probes and resolutions

1. Direct `inferInstance` for `T2Space (RealVectorSobolev 0)` produced:
   `failed to synthesize T2Space (RealVectorSobolev 0)` and
   `(deterministic) timeout at typeclass, maximum number of heartbeats (20000)`.
   Supplying `TopologicalSpace.t2Space_of_metrizableSpace` directly avoids the
   irrelevant topological instance search.
2. Rewriting large dependent cylinder expressions produced
   `(deterministic) timeout at isDefEq, maximum number of heartbeats (400000)`.
   Factored the three-term linear algebra into `map_residual`/`residual_fixed`
   and used explicit congruences for the Laplacian and bilinear terms. All
   heartbeat settings are per declaration, commented, and at most 400000.
3. `ext t` on continuous maps valued in L² also descended into the Lp quotient:
   the subsequent `change` saw an a.e.-equality goal. Replaced it by
   `apply ContinuousMap.ext; intro t`.
4. `IsSobolevDatum (↑0)` did not match `IsSobolevDatum 0`. Used an explicit
   `rw [Nat.cast_zero]` bridge, rather than unfolding the datum realization.
5. The first non-vacuity run reported the missing object file
   `Euler/SmoothL2Series.olean`. Built this existing dependency and reran.

## Satisfiability and scope

`hf` is the standard `MemForceR` restriction; `hν` and `hS` restrict viscosity
and horizon to positive values. `a` is an ordinary smooth L² initial field.
`U` is the common L² velocity path. `hpairs` copies the all-order cylinder-pair
conjunction in lane 192: common ordinary realization, divergence freedom,
angular invariance, and the exact forced mild equation with `F := forcePath hf`.
These are the standard local-theory properties on a common closed horizon;
there is no pressure, time-derivative, or residual-smoothness input.
The redundant velocity datum paths and initial-value equality exported by 192
are not needed as additional inputs here.

The separate physical-identification lemmas quantify a smooth spatial
representative and its a.e. equality to `U t`; these are restrictions of the
standard notion of representative, not assumptions of the existence theorem.
No pressure construction or projected momentum identification is claimed.
