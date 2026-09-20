# REPORT 212 — A01 local theory V2 contract

## 1. What was registered

Registered `A01.local_theory_v2`, version 2.  Its
`LocalTheory.LocalTheoryAPI` structurally extends the frozen
`A01.regularity_partial` API and supplies a named positive horizon, a
`Data.ClassicalSolutionR` on that horizon, and the full four-field
`ManuscriptLocalRegularity` from `research/A01/Spec.lean:167-230` for that same
selected solution.  The four clauses are all-order Sobolev time smoothness,
pressure recovery including `t=0`, the projected forced equation on the
interior, and the radial-potential pressure gauge.

The quantitative field is exactly the owner-approved V2 statement:

```lean
∀ ν, 0 < ν → ∀ f, MemForceR f → ∀ K : ℝ≥0∞, K ≠ ⊤ →
  ∃ δ > 0, ∀ a, a ∈ initialClassR → sobolevENorm 7 a ≤ K →
    δ ≤ horizon ν a f
```

Thus the force is fixed before `δ` is chosen and the datum is bounded in H⁷.
The field is bound to lane 211's
`horizon_lower_bound_H7_fixedForce`.  Lanes 215/217 separately provide the
uniform restart window over `t₀∈[0,S]` for shifted copies of that one force and
the gluing used by the A04 continuation consumers.

## 2. What is now in Lean

`verification/Contracts/V2/LocalTheory.lean` restates the three local
definitions and `ManuscriptLocalRegularity`, includes docstrings recording the
exact H¹/cross-force versus H⁷/fixed-force difference, and exposes the three
draft accessors.  The stronger statement is retained only as the unregistered
definition `ManuscriptHorizonLowerBoundH1`; it is not a structure field.

`verification/Bindings/LocalTheoryV2.lean` binds `localHorizon'`,
`localCarrier`, `manuscriptLocalRegularity_localCarrier`, and the H⁷ theorem.
Every copied ordinary definition has an `rfl` bridge.  The two
`ClassicalSolutionR` structures cross the contract boundary through the
A02/Data field-wise conversions, with both full round trips proved and the
regularity record transported field by field.  Importing the frozen V1 binding
alongside the newer full regularity assembly produced a duplicate
implementation theorem name, so the inherited fields are filled from the same
implementation results directly; `regularityPartial_of_v2` is the structural
V1 projection.  Frozen V1 files and all existing tests remain unchanged.

`verification/Tests/LocalTheoryV2.lean` checks the binding's axioms, repeats all
public field shapes against the draft spec, checks the H¹ definition by `rfl`,
and checks the V1 projection.  `research/A01/axioms_contract_v2.lean` constructs
a concrete nonzero compact force and a concrete nonzero compactly supported
solenoidal datum, obtains the selected solution and its positive horizon, and
obtains an actual real `δ>0` from the H⁷ field at those same nonzero inputs.
All printed declarations have exactly the standard three logical axioms.

The registry, A01 work item and rendered task views are updated.  The mutation
suite now targets A01 V2 directly for `extra_axiom` and
`weakened_hypothesis`.  `COMPARISON.md` contains the required “Paper vs V2”
table and `ATTEMPTS_CONTRACT_V2.md` records the extension, conversion,
non-vacuity and registry decisions.

## 3. What is not proved

**The Appendix A:147–150 H¹ local-existence sentence is NOT proved.**  In
particular, this lane does not prove the draft statement that chooses one
positive `δ` before both the datum and force for an H¹ datum/`L¹_tH¹_x` force
ball.  It proves neither H¹ control nor cross-force uniformity.  That statement
appears only as the open, unproved predicate
`ManuscriptHorizonLowerBoundH1` and is not registered as a V2 field.

The registered H⁷/fixed-force theorem suffices for the actual downstream
consumers: A04 restarts the same force with Grönwall-bounded H⁷ data and proves
restart-time uniformity separately, while A02's `exists_maximal'` needs only
per-datum local existence.  Proving the manuscript/draft H¹ version would
require a forced quantitative H¹ theory on the mild stack, persistence to the
smooth solution on the same interval, and a horizon selection retaining its
uniform estimate.

The task text expected `registered_contracts: 30`, but the specified base
`origin/erenup/integration` already has 32 entries.  The additions-only result
is therefore honestly 33; no later registered contracts were deleted to force
the stale count.

## 4. Commands and results

Every Lean shell sourced `scripts/lean-env.sh`; every Lake command ran from
`verification/` with `LEAN_NUM_THREADS=6`.

- `lake build Contracts.V2.LocalTheory Bindings.LocalTheoryV2 Tests.LocalTheoryV2`:
  exit 0; `checkedLocalTheoryV2` reported “standard logical axioms only”.
- `lake env lean ../research/A01/axioms_contract_v2.lean`: exit 0; all 16
  printed declarations reported exactly `[propext, Classical.choice,
  Quot.sound]`, and both nonzero-input examples compiled.
- `scripts/gates.sh`: exit 0, ending in `== gates OK`; `make check`, all
  registered Lean tests, and the mutation suite passed.  The A01 V2
  `extra_axiom` and `weakened_hypothesis` mutations were rejected as required.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`:
  exit 0.  Relevant output:

  ```text
  {
    "registered_contracts": 33,
    "base_compatibility_checked": true,
    "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
  }
  ```

- `git diff --stat verification/contracts.json`:

  ```text
   verification/contracts.json | 11 +++++++++++
   1 file changed, 11 insertions(+)
  ```

No proof placeholder, new axiom declaration, `native_decide`, or heartbeat
override was added.  Work remained in this worktree; no push, merge, or rebase
was performed.
