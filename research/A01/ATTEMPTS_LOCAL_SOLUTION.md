# Lane 208 — datum and chosen local solution

## Successful route

`initialClassR` is precisely smooth all-integer Sobolev datum membership plus
pointwise solenoidality, not merely an equivalence class. Reuse
`D01.exists_smoothL2Field_of_memHInfty` (DatumToJets), retaining its pointwise
field identity. `divergence_eq_coordinate_sum` and the physical coordinate-vector
definition identify the two divergence conventions.

Reassemble the lane-207 probe without discarding `hU0`. The joint representative's
zero slice equals `a.toLp` almost everywhere; `a.toLp_ae` identifies the latter
with `a.field`. `D01.contDiff_slice` at zero and `Continuous.ae_eq_iff_eq` turn this
into equality of functions. `transport_initial` changes only the initial proof;
velocity and pressure are definitionally preserved.

Fix Smax=1, obtain an existential positive horizon, then choose it under the three
contract hypotheses. Invalid inputs have horizon 1. `localHorizon_spec` supplies
both positivity and Nonempty at precisely that horizon. `localSolution` is a
noncomputable data definition, not a proposition-valued theorem; downstream lanes
must refer to this definition to use the same solution. Proof irrelevance makes
changes of hypothesis proofs immaterial.

## Failed attempts and fixes

* Direct `exact ha.2 x` failed: Euler divergence is a trace, while the manuscript
  divergence is a coordinate sum. Expand the proved trace-to-coordinate identity
  and `coordinateVector`; no new analytic premise is needed.
* A bare dependent `if` lacked a Decidable instance: use `classical` inside the
  total definition. The deprecated `dif_pos` produced a warning; use
  `dite_eq_left` with the full typed conjunction.
* The canonical solution-type conformance example is data and initially required
  `noncomputable section`; adding it fixed code-generation checking.

## Scope and registration

No named analytic input was added. The formalization layer cannot import the
canonical contract structure under repository policy. Its A02 restatement is
converted by the existing `Bindings.maximalPartial_ofA02`; the conformance file
checks the exact canonical solution-field type with that conversion.

The requested review §5 does not exist in this checkout: the registration list
is under §3 of REVIEW_207-A01-tame-assembly.md. It was read there.

This choice establishes qualitative existence only. Neither all the manuscript
regularity fields nor an H¹-uniform lower bound for this chosen horizon has been
proved here. In particular, arbitrary choice of an H⁷-based horizon does not
establish H¹ uniformity; lane 210 must address the actual chosen definition or
coordinate a replacement together with its dependent solution and regularity.
