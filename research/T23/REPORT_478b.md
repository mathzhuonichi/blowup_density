# Lane 478 continuation — T23 U7 box uniqueness

## 1. Statements

**Box U7 is closed.** `noSlip_uniqueness_box` has the original viscosity,
initial datum, force, two solution records, common-time interval, and spatial
point binders, with the domain predicate restricted to `IsBoxDomain Ω`.
It has no added analytic hypothesis. Openness and boundedness follow from the
strictly separated box coordinates.

`ibp_box` proves scalar boundary integration by parts on the Spec's open
Euclidean box. The proof transports the closed coordinate-box theorem using
the volume-preserving coordinate equivalence, open/closed box equality almost
everywhere, the derivative chain rule and frontier containment.

`difference_energy_identity` proves, on the open common time interval,

```text
E' = −2ν ∫Ω Σᵢ ‖∂ᵢ(u₁−u₂)‖² − 2 ∫Ω ⟨D u₂ (u₁−u₂), u₁−u₂⟩.
```

Time differentiation comes from compact-domain dominated differentiation and
the original closed-slab smoothness fields. No-slip and divergence cancel
pressure and transport. The convection integral is bounded in absolute value
by `C E`, using the proved compact-subslab spatial derivative bound.
Grönwall from `E(0)=0` gives zero energy on every compact common subinterval;
continuity gives pointwise velocity equality on the open domain. An intermediate
`S` strictly between the queried time and `min T₁ T₂` covers every target time.

`noSlip_uniqueness_of_ibp` proves the full U7 conclusion with the single explicit
hypothesis `IBP Ω`. This is exactly the scalar boundary identity authorized by
the continuation request, not a repackaged energy or uniqueness assumption.
All 40 audited theorem declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

## 2. Files

- `Section3/T23/NoSlipUniqueness.lean`: public import entry point exposing both
  uniqueness theorems and the supporting lemmas.
- `Section3/T23/DomainSolution.lean`: the canonical vocabulary and raw solution
  record, moved unchanged from the previous entry point; the original four
  analytic lemmas, explicit `IBP`, and `ibp_box`. The Spec block is byte-identical.
- `Section3/T23/BoxIntegration.lean`: existing closed coordinate-box proof,
  unchanged in this continuation.
- `Section3/T23/NoSlipEnergy.lean`: scalar/vector boundary IBP consequences,
  transport, pressure and viscous cancellations.
- `Section3/T23/DomainTimeIntegral.lean`: continuity and differentiation of
  bounded-domain integrals from neighborhood smoothness.
- `Section3/T23/DifferenceEnergy.lean`: local difference momentum, energy
  differentiation and identity, convection bound, Grönwall, both uniqueness
  declarations and box geometry.
- `research/T23/probes/noslip_box_closes.lean`: literal box U7 target, `ibp_box`,
  and a translated non-cubic box instance.
- `research/T23/probes/noslip_uniqueness_closes.lean`: literal conditional U7
  target with precisely `IBP Ω`.
- `research/T23/axioms_u7.lean`, `ATTEMPTS_U7.md`, `SPEC_ISSUES.md` G1 and
  `T23_SPLIT.md`: complete theorem audit, failed attempts with exact diagnostics,
  smooth-domain residual/search evidence, and updated U7 status.

Incremental commits: `cfb968ec` (physical box IBP), `4e7ac2e9` (boundary energy
cancellations and integral calculus), `7fe87dc2` (complete box uniqueness and
conditional U7). No push, merge or rebase.

## 3. Gaps and error text

**Only unrestricted smooth-domain U7 remains.** The exact missing analytic
statement is:

```lean
∀ (Ω : Set Space), IsOpen Ω → Bornology.IsBounded Ω →
  IsRegularLevelDomain Ω → IBP Ω
```

`IBP` is fully expanded in `SPEC_ISSUES.md` G1. Mathlib's inspected divergence
suppliers integrate over coordinate boxes/order intervals or products of
intervals; the continuous-linear-equivalence variant still requires an order
interval. No applicable regular-level-domain supplier was found by the recorded
full-tree search. No unrestricted `noSlip_uniqueness` declaration was introduced.
A proof of the displayed residual and the box/smooth case split would close it.
The lead decides whether V1 registers only the proved box branch.

No Lean error remains in delivered modules or probes. Failed intermediate
approaches and their exact diagnostics are preserved in `ATTEMPTS_U7.md`, e.g.:

```text
Unknown identifier `frontier_closure`
maximum recursion depth has been reached
failed to synthesize instance of type class
  AlexandrovDiscrete Space
```

These were fixed with frontier containment, a one-time directional-derivative
rewrite, and finite-intersection openness. Other diagnostics concerned coercion
spelling, unfolding, implicit arguments and the order of continuity arguments.
No admission, new axiom, heartbeat override, connectedness assumption, pressure
equality or modified solution field was used. Source import traversal found no
path to the forbidden BoundaryCorollary module.

## 4. Commands and results

Every Lean command sourced `. scripts/lean-env.sh`, ran from `verification/`,
and used `LEAN_NUM_THREADS=6`.

| Command/check | Result |
|---|---|
| `lake build NSFormalization.Section3.T23.NoSlipUniqueness Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace` | Exit 0; dependency closure first |
| `lake build NSFormalization.Section3.T23.NoSlipUniqueness` after final import layout | Exit 0; 8820 jobs, dependency warnings only |
| `lake env lean` on DomainSolution, NoSlipEnergy, DomainTimeIntegral, DifferenceEnergy, NoSlipUniqueness | All exit 0, zero output |
| `lake env lean ../research/T23/probes/noslip_box_closes.lean` | Exit 0, zero output |
| `lake env lean ../research/T23/probes/noslip_uniqueness_closes.lean` | Exit 0, zero output |
| `lake env lean ../research/T23/probes/box_integration_by_parts_closes.lean` | Exit 0, zero output |
| `lake env lean ../research/T23/axioms_u7.lean` | Exit 0; all 40 theorem lists exactly the standard three |
| `make check` from worktree root | Exit 0; 52 registered contracts, 45 consistent work items |
| `lake test` | Exit 0; registered tests pass |
| `make test-mutations` from worktree root | Exit 0; refactor accepted; all three invalid mutations rejected |
| Byte comparison of canonical vocabulary/record with Spec | Identical |
| New-module admission scan and source import traversal | No proof admissions; no forbidden module path |

The only occurrence of the admission keyword in delivered proof sources is the
unchanged Spec provenance comment. `make check` still reports the pre-existing
repository-wide historical admission/source-manifest discrepancy while exiting
0; this lane adds neither. Tests validate the proved box theorem and the exact
conditional theorem, not unrestricted smooth-domain uniqueness.
