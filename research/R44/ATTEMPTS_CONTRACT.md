# Lane 231 — R44 V1 contract registration attempts

## Target and fidelity check

The registered structure is `research/R44/Spec.lean:169-304` with exactly the
nine fields `c`, `C`, `hc`, `hC`, `radius`, `radiusFormula`, `radiusPos`, `main`,
and `nonDensityBallZero`.  The contract copies the Spec field declarations and
docstrings verbatim apart from the registry-conventional structure name.  It
retains the binder order, the named radius field, the explicit formula only in
`radiusFormula`, the inhomogeneous `forceSobolevENormL2 (-1 / 2)` norm, the zero
initial datum, the strict ENNReal smallness inequality, and the strict
finite-lifespan conclusion.  `Contracts.V1.Data` supplies every required public
definition, so no homogeneous-norm import or local definition is needed.

## Binding route

- The record chooses `c := R44.theta / 20`, `C := 3`, and
  `radius := R44.radius`.  The implementation equalities
  `radiusCoefficient = theta / 20` and `radiusRate = 3` pin the field formula;
  positivity comes from `R44.theta_pos` and `R44.radius_pos`.
- `MemForceR` and `forceSobolevENormL2` are definitionally equal to the A02/R44
  spellings, and the binding records both correspondences as `rfl` theorems.
- `Data.ClassicalSolutionR` and A02's local `ClassicalSolutionR` are distinct
  structures.  The `main` conclusion therefore rewrites with the established
  `Bindings.maximalPartial_maximalLifespanR_eq`.  Breakdown-set membership uses
  the same equality in both directions before applying
  `R44.nonDensityBallZero`; it is not falsely claimed as an `rfl` bridge.
- No implementation estimate, differential package, local-existence input, or
  continuation assumption appears in the public API.

## Attempts and diagnostics

The first focused build used `namespace R44 := ...` as if Lean namespace aliases
had declaration syntax.  Lean parsed those lines as nested namespace commands,
so every abbreviated implementation name was unknown and the final `end` also
reported the unintended nesting.  Replacing the three pseudo-aliases with
`open NSFormalization.Section4` made the intended `R44`, `A02`, and `R41`
qualified names resolve.  The contract, binding, and test then built, and
`TestSupport.checkAxioms` reported only the standard logical axioms.

No Spec field failed to bind, and no weakening, placeholder proposition,
additional axiom, or heartbeat override was needed.
