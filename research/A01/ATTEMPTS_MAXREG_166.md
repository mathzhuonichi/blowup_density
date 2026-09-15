# Lane 166: forced nonlinear maximal regularity

## Implemented result

`A01/ForcedMaximalRegularity.lean` evaluates the actual `ForcedCylinderLocal.coefficients` along the given continuous mild path. `nonlinearSource` is continuous by the existing coefficient map continuity; no higher solution regularity is an input.

`forced_mild_maximal_regularity` feeds the original `quadraticDuhamel` equality directly to `EulerSobolevMaximalRegularity.viscous_mild_maximal_regularity`. It constructs a genuine `TimeLp T (SobolevSpace 1 (2 + q))`, with a.e. restriction equal to the original extended H(q+1) path on the same `timeMeasure T`, and an integrable squared high-order norm. There is no shortened horizon and no replacement solution.

`exists_local_of_memForce` invokes the real `OrdinaryForcedLocal.exists_local` with `C01.forcePath hf` and its proved jet continuity. Its inputs are exactly finite order q >= 6, positive viscosity and ambient horizon, smooth L2 initial field with classical divergence zero, and actual `A02.MemForceR f`. The output retains the true force slice identity, initial values, ordinary lift identity, cylinder divergence constraint, original forced Duhamel equality, angular invariance, and the compatible higher path.

`research/A01/axioms_maxreg166.lean` includes the concrete q=6 consumer `actual_force_order_eight` (H7 path, H8 time-integrable realization) and prints dependencies of the four source declarations and consumer.

`higher_value_ae` also identifies the higher path at the cylinder L2 value level with the lift of the actual ordinary path, almost everywhere in time. No endpoint value of the higher TimeLp representative is asserted.

## Scope

This closes a one-order Bochner-time gain from the actual finite-order mild witness. It does not give a continuous H(q+2) path, a compatible all-order tower, or joint smoothness, and uses no `ClassicalSolutionR`. Importing C01 JetPaths supplies only its solution-independent force slice construction and continuity.

## Elaboration repairs and validation

The author ran no Lean or lake command. Luna high performed compilation and verification; the final log contents were read by the author, and the lead confirmed native exit codes.

- r1: evaluating continuity with the concrete coefficients exhausted the default heartbeat budget; the large local-existence consumer also timed out.
- r2: explicit intermediate continuity types did not prevent concrete coefficient unfolding. A misplaced local `set_option` after a docstring was also rejected by the parser.
- r3: moving the option before the docstring fixed syntax, but the concrete source definition still exhausted a finite 800000 budget during definitional equality and nested-proof abstraction.
- r4: a private `coefficientPath` proves continuity for an abstract `Coefficients` argument; `nonlinearSource` merely supplies the actual coefficients. This avoids expanding their large proof terms. The source builder returned to the default budget; only the large `exists_local_of_memForce` declaration retains a local finite 800000 budget. The mathematical statements did not change.

Final acceptance evidence:

- `tmp/build_166_ForcedMaximalRegularity_r4.log`: build completed successfully, 10200 jobs; native exit 0 confirmed by the lead.
- `tmp/probe_166_axioms_maxreg.log`: all five printed declarations (`nonlinearSource`, `forced_mild_maximal_regularity`, `exists_local_of_memForce`, `actual_force_order_eight`, `higher_value_ae`) depend only on `propext`, `Classical.choice`, and `Quot.sound`; probe exit 0 confirmed by the lead.
- `tmp/lake_test_166_maxreg.log`: 26 contract checks, native exit 0 confirmed by the lead.
- `tmp/mutations_166_maxreg.log`: mutation suite passed, native exit 0 confirmed by the lead. This is infrastructure validation, not an additional PDE theorem.

The accepted result remains at a fixed q on the same T. The higher W is a Bochner L2-time realization and is compatible only almost everywhere; no endpoint value, continuous all-order tower, or joint smoothness is claimed.
