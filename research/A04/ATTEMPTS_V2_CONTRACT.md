# A04 continuation V2 contract registration attempts

## 1. Registered boundary

`ContinuationV2API` registers exactly the continuation interface proved by
lanes 215 and 217. Its `restart` field is the owner-approved
`RestartFixedForce` shape:

```lean
∀ ν > 0, ∀ f ∈ F_R, ∀ S ≥ 0, ∀ K ≠ ⊤, ∃ δ > 0,
  ∀ t₀ ∈ Icc 0 S, ∀ a' ∈ X_R,
    sobolevENorm 7 a' ≤ K →
      δ ≤ localHorizon' ν a' (timeShift t₀ f)
```

The force and compact restart window precede `∃ δ`; the datum bound is H⁷;
the duration remains uniform over every restart time in `[0,S]`. The remaining
fields are the unchanged Spec `higherOrderBound` and lane 217's unconditional
`restartBeyond`, `extendsBeyond`, and
`lifespanInfiniteOfLocallyFinite` shapes.

This record cannot honestly extend the draft/V1 A04 record. Its `Restart`
field is the paper's stronger H¹/cross-force proposition and has no proof.
Replacing that inherited field silently would change an existing statement.
The V2 record is therefore independent.

## 2. The proposition deliberately not claimed

The manuscript says at `appendix-a-local-theory.tex:147-150` that its H¹ local
existence bounds give a common positive duration while the initial H¹ norms and
force H¹ bounds stay bounded. The corresponding Spec/V1 `Restart` chooses the
duration before the force and uses an H¹ datum bound.

`ManuscriptHorizonLowerBoundH1` copies that statement as a named `def : Prop`
for drift detection and documentation only. It is not a
`ContinuationV2API` field, has no witness, and is open. Lane 215's theorem does
not imply it for two independent reasons recorded in `REPORT_215.md` §3:

1. a theorem uniform on an H⁷ ball does not cover the larger H¹ ball;
2. compactness of the shifted path of one fixed force gives no uniformity over
   all forces.

A proof of the paper/V1 field would need a forced quantitative H¹ local theory
on the mild stack with a horizon controlled uniformly by the displayed H¹
datum and force bounds.

## 3. Contract import and bridge attempts

A direct contract reference to `NSFormalization.Section4.A01.localHorizon'`
was rejected as a design: its defining module
`NSFormalization.Section4.A01.LocalTheoryBundle` is not one of
`experiments/check_contracts.py`'s `CONTRACT_CANONICAL_MODULES`. Adding that
large implementation module to the whitelist would weaken the versioned
contract boundary.

The accepted design parameterizes `ContinuationV2API` and its two named
restart propositions by
`horizon : ℝ → SpatialField → SpaceTimeField → ℝ`. The binding supplies the
actual `A01.localHorizon'`. The contract's `RestartFixedForce` and the
implementation predicate then agree by `rfl`; a second `rfl` bridge records
that the named open H¹ proposition matches A01's named open proposition.

The classes and norms also bridge by `rfl`. `SolvesBelow` and
`IsMaximalSolution` cannot use a structure-level `rfl`, because the contract
and implementation contain distinct `ClassicalSolutionR` inductive types.
The binding instead uses `uniqueness_toA02`, `maximalPartial_ofA02`, and the
established `maximalPartial_maximalLifespanR_eq` bridge.

## 4. Witness and non-vacuity audit

The witness uses:

- `restartFixedForce_of_memForceR` and `higherOrderBound_of_gronwall` from
  lane 215;
- `restartBeyond_of_memForceR'`, `extendsBeyond_of_memForceR'`, and
  `lifespanInfiniteOfLocallyFinite_of_memForceR'` from lane 217.

`research/A04/axioms_v2_contract.lean` constructs two explicit nonzero inputs.
The force is the established smooth compact spacetime bump from the R43 audit.
The datum is the curl of the compactly supported smooth potential
`x ↦ (b(x) x₀) e₂`; its second curl component is `-1` at the origin, so it is
nonzero, divergence free, and in `initialClassR`. Instantiating `restart` at
both witnesses returns an actual real `δ` together with `0 < δ` and the local
horizon lower bound. Thus the registered theorem is not being discharged by
empty input classes or a vacuous duration.

## 5. Fidelity refusals

- The paper/V1 H¹ restart was not inserted as a proved field.
- No placeholder `Prop` field, axiom, `sorry`, `admit`, or `native_decide` was
  introduced.
- V2 was not declared to extend an unproved V1 continuation record.
- The owner-approved quantifier order was not strengthened to cross-force
  uniformity or weakened to a single restart time.
- The H⁷ bound was not relabelled as H¹.
- The three continuation consumers were not recut; their lane-217
  `…_of_memForceR'` statements are registered as proved.
