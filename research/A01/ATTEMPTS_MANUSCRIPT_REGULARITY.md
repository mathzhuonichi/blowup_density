# Lane 209 — manuscript regularity

## Target and interface

`ManuscriptRegularity.lean` copies the complete `ManuscriptLocalRegularity`
structure, including all four field types, verbatim from `Spec.lean`.
`ClassicalSolutionR` is the existing A02 structure; `IsSobolevDatum` is the
definitionally equal D01 predicate. `IsLerayComplement` copies the draft's
three-clause characterization. The existing convection and radial-potential
definitions are reused.

`LocalSolution.lean` is absent from this checkout. The authorized fallback is
implemented: `manuscriptLocalRegularity_of_pipeline w hf U hslice hpaths`
applies to an arbitrary classical solution with the carrier constructor's
exported slice identity. No equality identifying the pressure witness is needed.

## Successful proof routes

1. Choose the order-zero-in-time datum path at each Sobolev order. Uniqueness
   (`isSobolevDatum_unique`) identifies every finite-order path with it on
   `Icc 0 S`; `ContDiffOn.congr`, `contDiffOn_infty`, and restriction to `Ico`
   give the one common smooth path. Transport the physical slice using
   `IsSobolevDatum.congr_field` and `hslice`.
2. Prove pressure recovery for **every** classical solution with admissible
   force. `PressureGauge` supplies symmetry of its pressure gradient and the
   solution supplies its L² bound. On the interior, momentum identifies
   `f - advection u - grad p` with `dt u - ν Δu`. D01's divergence/time
   commutation kills the first term. C01's `laplacianField_divergence_zero`
   and `laplacianField_velocitySlice_field` kill the second.
3. At zero, only spatial derivatives are taken. The new generic
   `contDiffOn_spatial_fderiv` uses Mathlib's parameter-dependent derivative
   theorem with spatial set `univ`, preserving the original time set without
   assuming an extension. Thus the spatial divergence of
   `f - advection u - grad p` is continuous on `Ico 0 S`. Its interior zero
   identity extends by `Set.EqOn.of_subset_closure` and
   `closure_Ioo w.horizon_pos.ne`. This proves the endpoint without invoking
   a two-sided temporal derivative there or exposing the complement carrier.
4. `projected_of_classicalSolution` reuses the proved momentum/projected
   equivalence. `PressureGauge.pressure_potential_of_classicalSolution`
   supplies the gauge on the entire half-open slab.

## Rejected paths and Lean corrections

- The constructor's existential result exposes the velocity and its slices,
  **not** the radial-pressure equality used internally. A proof requiring that
  equality would impose an unnecessary export change. The existing gauge
  theorem applies to arbitrary smooth pressure and avoids this issue.
- It is not valid simply to turn `∀ j, ∃ G, C^j G` into `∃ G, C∞ G` without
  identifying witnesses. The proof uses datum uniqueness explicitly.
- The first attempt at `rw [fderiv_fun_sub hdt (hdl.const_smul ν)]` failed with
  `Did not find an occurrence of the pattern`: the lemma retained a Pi-space
  scalar action. Normalize `Pi.smul_apply` in the local equality before rewriting.
- `ContinuousOn.comp` names its inner function `f`, not `g`. Giving that
  function explicitly removes an expensive unresolved inference problem.
  The initial unannotated attempt exhausted 200000/400000 heartbeats; merely
  raising the limit did not fix it. The corrected declaration uses the allowed
  local, commented 400000 budget and compiles without diagnostics.
- `horizon_pos.ne` has the orientation required by `closure_Ioo`;
  `horizon_pos.ne'` asks for the reversed interval.

## Satisfiability and conformance

No new analytic input remains. The audit file actually constructs the carrier
from the base mild solution via lane 207 bounds, lane 192 paths, lane 190 smooth
representative, lane 189 pressure supply, and lane 180 constructor, then applies
the new theorem to the returned `w` and its returned slice identity. It also
runs this construction on concrete zero data, with positive viscosity and
positive upper horizon. The final result has all four regularity fields.

All nine declarations in the new module and both named audit theorems print
exactly `[propext, Classical.choice, Quot.sound]`. The four-field structure is
text-identical to the draft structure. The module has no diagnostics under
`lake env lean`; the full pipeline audit compiles. See `REPORT_209.md` for gates.

The H¹-uniform horizon lower bound and contract registration are outside this
lane. This result does not claim to inhabit the whole `LocalTheoryAPI`.
