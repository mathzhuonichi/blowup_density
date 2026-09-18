# T24 Uc1 + Ua1 attempts (lane 392)

## Closed declarations

`formalization/NSFormalization/Section3/T24/Conservative.lean` restates
`PeriodicPotentialT` and `conservativeForceT` on the canonical T10/T11 field
types and proves the exact `zero_from_rest` clause from
`NSFormalization.Paper1.ConservativeForce.zero_of_negative_gradient_on_Ico`.
The T10 `IsPeriodicOn` and Paper1 `UnitSpatialPeriodsOn` predicates, and the
T10 residual and Paper1 `Source.residual`, are definitionally identical.  The
only small interval conversion is from `S.divergence` on `Ico` to the reused
theorem's `Ioo` premise.

`formalization/NSFormalization/Section3/T24/AffineBasics.lean` introduces the
whole-space raw-field vocabulary `affineCylinder`, `AffineAdmissible`,
`affineVelocity`, `affinePressure`, `crossAdvection`, `affineForce`, and the
extended-real `affineCkSeminorm`.  It proves the five Ua1 clauses:

- `radius_pos` and `window` return the four parameter hypotheses of
  `affineVariationStatement` in the exact field shapes;
- `zero_initial` uses the raw packet clause `u (0,x)=0`; if `(0,x)` belonged
  to `tsupport b`, support containment would imply `0∈Ioo τ₀ τ₁`, contradicting
  `0<τ₀`, so `b(0,x)=0`;
- `late_agreement` uses the same support argument: `τ₁≤t` contradicts the
  cylinder condition `t<τ₁`, hence `b(t,x)=0`;
- `distinct` is pointwise translation injectivity (`add_right_injective`) for
  the explicit function `u+b`.  Its two admissibility premises in the Spec are
  deliberately unused because injectivity holds for all fields.

The probe `research/T24/probes/uc1_ua1_closes.lean` imports the registered
contracts and bindings.  It converts the contract `ClassicalSolutionT` with
`Bindings.TorusLocalTheory.ofContract`, and checks the affine fields using
`Bindings.packet ν hν`'s raw `velocity` and `zero_initial_velocity` fields.

## Failed elaboration attempts and fixes

1. Applying `zero_of_negative_gradient_on_Ico` directly with tactic bullets
   left the final evaluation arguments misaligned, producing:

   ```text
   unsolved goals ... ⊢ t ∈ Ico 0 T
   ```

   Binding the complete reusable theorem as `have hz := ...` and then using
   `exact hz t ht x` makes the intended argument boundary explicit.

2. A probe cannot `import research.T24.Spec`: `research/` is not a Lake source
   root.  The first attempt failed with:

   ```text
   error: unknown module prefix 'research'
   ```

   As in the existing T15/T16 canonical probes, the probe now copies only the
   three definitionally identical registered-spelling fragments it checks
   (`affineCylinder`, `AffineAdmissible`, and `affineVelocity`), with `rfl`
   bridges to the canonical definitions.  No proof declaration or API
   structure is copied or weakened.

3. The registered and canonical `ClassicalSolutionT` structures are distinct
   inductive types.  Directly passing the contract solution to
   `zero_from_rest` is therefore invalid; the required structure-exception
   conversion is `Bindings.TorusLocalTheory.ofContract`.

## Honesty and axiom audit

No named input, placeholder proposition, `sorry`, `admit`, `axiom`, or
`native_decide` was introduced.  `research/T24/axioms_uc1_ua1.lean` prints
exactly `[propext, Classical.choice, Quot.sound]` for all fifteen new
declarations.
