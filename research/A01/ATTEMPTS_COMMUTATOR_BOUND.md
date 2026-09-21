# Lane 202: cylinder commutator attempts

## Positive results

The actual finite-carrier maps expand into four scalar-product commutator
families. This identity needs neither smooth representatives nor compatibility.
The empty word of each coordinate family is zero on arbitrary finite elements.
Taking the Hilbert family norm and summing coordinates costs exactly four;
it does not cost another word-cardinality factor. Compatibility is retained
in the analytic input, where the two tame terms must be consolidated.

## Remaining analytic input (not proved)

`CylinderCoordinateTame q hq C` means exactly:

```lean
∀ (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)),
  restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v →
  ∀ i : Fin 4, familyNorm (cylinderCoordinateCommutator hq v V i) ≤
    C * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖ * cylinderWordGradient V
```

The definitions of both families and the gradient are literal in the new
module. For the fixed lane-200 API the ONE input is
`CylinderCoordinateTame q hq (4 * A q)`. This includes constant certification.
It is a coordinate commutator estimate, not a proved mixed-product interpolation
lemma. Neither its validity nor the existence of any uniform real C has been
proved here. The conditional existential theorem must not be read as an
unconditional existence result. Zero examples establish only zero-data
conformance, not satisfiability of the universally quantified input.

## Negative routes and scope checks

* `asymmetricTransport_bound` bounds high norm times high norm. The coefficient
  norm is at q+1; restriction gives the opposite inequality to that needed to
  replace it by the order-7 norm uniformly in q. Separate triangle inequalities
  before commutator cancellation also discard the necessary derivative structure.
* `tameProductScalar`, `outerProductTame`, `coordinateProduct_tame` and
  `wordMaximum_product_le` use physical R³ data or `SmoothL2Field Space` and
  `Fin 3` words. Arbitrary cylinder elements can depend on the angle. A smooth
  spatial bump multiplied by a nonconstant periodic angular function illustrates
  data that cannot be identified with an ordinary lift. No such identification
  is assumed in this module.
* `scalarCommutator_recurrence` and `transportCommutator_eq_sum` provide the
  smooth differential identities, but applying them does not provide an L²
  mixed-product tame bound or the finite-carrier passage. The new coordinate
  expansion is not advertised as the full Leibniz expansion into mixed products.
* `externalCommutator_ae` retains n+6 ≤ s. Substituting the requested top word
  n=q+1 at s=q+1 fails arithmetically. Base L² estimates only cover n ≤ 6.
* A signed pairing bound cannot imply a family norm bound: a nonzero vector
  orthogonal to the tested vector has pairing zero and positive norm. The
  conformance file checks the scalar zero-test analogue.
* Both sides of the desired bound are quadratic under simultaneous scaling.
  Replacing the first power of the low norm by a square would instead be cubic
  and cannot serve as a uniform small-amplitude substitute.

Searches covered file names, declarations and comments in Section4 D01/A03/A04/
A01/C01, plus the vendor modules named above. Closest candidates were read at
their definitions; this supports the stated interface mismatch, not a claim
that no cylinder interpolation theorem could be developed from the library.

## Resolved Lean diagnostics

The initial expansion ended with:

```text
error: Tactic `rfl` failed: The left-hand side ...
is not definitionally equal to the right-hand side ...
```

The mismatch was evaluation of a sum in the closed Sobolev subspace versus
sum of evaluated words. `Submodule.coe_sum` did not rewrite that closed-subspace
coercion. Mapping the sum through `(sobolevSubspace ...).toSubmodule.subtype`
and then applying the word evaluation proves the needed equality explicitly.
No unresolved Lean errors remain. No failed analytic proof is replaced by an
opaque constant, new logical assumption declaration, or zero-only theorem.
