# A05 V2 contract registration attempts (lane 181)

## Result

Registered the proved `velocityCriticalL3` theorem as
`A05.gradient_l6_v2`, extending the frozen `A05.gradient_l6` V1 interface.
The new field is the statement at `research/A05/Spec.lean:366-368`, with its
local homogeneous norm replaced only by the already registered, definitionally
equal `Contracts.V1.HomogeneousNorm.dotHomogeneousENorm`.

## Contract shape and constant

The V1 record contains only the unrelated gradient-`L⁶` constant `Csix`.
Reusing that constant for the velocity `L³` estimate would be unsupported: the
two implementation constants are different definitions and no comparison is
proved.  Adding a new record constant would also make the requested one-field
record update impossible and would no longer leave the Spec field text intact.

Instead `GradientL6V2API` takes the Spec's constant family `C : ℝ → ℝ` as
an interface parameter and adds exactly one field.  This keeps
`velocityCriticalL3` token-for-token while ensuring the constant is selected
outside every quantified field.  The checked binding fixes `C` to the constant
family `fun _ => A05.criticalL3Const`; only `C (1/2)` is constrained.  The
implementation theorem `criticalL3Const_pos` is exported as the binding-level
fact `gradientL6V2Constant_pos`, but all-orders `C_pos` is honestly outside this
focused contract.

## Definitional bridges

The following all elaborate by reflexivity:

1. `Contracts.V1.Data.MemHInfty v = A02.MemHInfty v`.  The contract hypothesis
   is not stronger or weaker than the implementation hypothesis; both are the
   same smoothness-plus-integer-datum conjunction.
2. `A05.dotHomogeneousENorm = D01.dotHomogeneousENorm`.  This is the checkpoint
   in `REVIEW_165-A05-critical-l3.md`, section "canonical norm: rfl".
3. `Contracts.V1.HomogeneousNorm.dotHomogeneousENorm =
   D01.dotHomogeneousENorm`, the existing D01 registered bridge.  The V2 binding
   composes its symmetric direction with item 2.
4. `gradientL6V2.toGradientL6API = gradientL6`, so no V1 field changes.

## Diagnostics

An initial sequence of direct `lake env lean` calls elaborated the new contract
source but did not emit its `.olean`, so importing it in the next direct call
failed with `object file .../Contracts/V2/GradientL6.olean ... does not exist`.
Building the three module targets with `lake build` is the correct dependency
aware route; it succeeded and the test reported standard logical axioms only.

No mathematical weakening, extra regularity hypothesis, `sorry`, `admit`,
`axiom`, placeholder proposition, or second copy of the homogeneous norm was
introduced.
