# Lane 318 — physical recovery attempts (partial delivery)

## Scope and search

Read CLAUDE.md, T11_SPLIT.md (§0–§4), RECONCILIATION.md (§0–§3),
IMPLEMENTATION_CANDIDATES.md, EXISTENCE_ROUTE.md, REPORT_317.md, the canonical
API probe, and the first 40 lines of logs/LESSONS.md. FourierCalculus.lean is
present. No existing Lean module or contract was changed. Both local instances
in PhysicalRecovery.lean have explicit names.

The required `grep -rnE` covered all of:

- `formalization/NSFormalization/Paper1/Periodic*.lean`
- `formalization/NSFormalization/Section3/`
- `formalization/NSFormalization/Section4/{A01,A02,A04,D01}`
- `vendor/HeliCorgi/Formal/`

Search terms: `reconstruct|Recovery|recover|representative|Pressure.*(exist|smooth)|pressure.*(exist|smooth)`.
The worktree-local raw result is `tmp/318/search.txt` (untracked).

Relevant inspected declarations:

- T10 `periodic_component_eq_tsum`: inversion of an already continuous field,
  conditional on summability. The new inverse also works on arbitrary H³ data.
- `PeriodicPressureSymbolOperator.laplaceOperator_pressureOperator`: raw
  coefficient Poisson identity; no reconstructed physical pressure.
- `PeriodicPressureRecoveryBridge`: normalizes an already supplied smooth flow.
- `PeriodicH3RepresentativeBridge`: cylinder representative, not a constructor
  on the canonical weighted torus coefficient carrier.
- `PeriodicOrdinaryLocal`: requires an ordinary whole-space representative;
  this route was not used for nonzero periodic data.
- U9b/U9c: actual complete carrier, kernel, convolution CLM and forced Picard
  solution. They supply no all-order persistence theorem for this mild path.

## Successful proof route

1. Remove the exact `W(k)^(3/2)` datum weight. Hölder on two ℓ² sequences,
   with `sum W(k)^(-3) < ∞`, proves absolute summability for every coefficient
   datum, without an assumed physical representative.
2. Define the component series using the unit-period characters. Conjugate
   reflection and the `k ↦ -k` bijection prove the series real. Uniform
   summability proves spatial continuity and the character periods give
   periodicity.
3. Descend the series to the compact torus. Interchange integration and sum
   using **summable integrals of norms**, then integrate individual characters.
   This recovers the original coefficient at every frequency. It proves the
   exact datum predicate, including Haar integrability.
4. Conversely, T10 inversion proves that every continuous field with this datum
   equals the constructed field. Applying the mild initial identity recovers a.
5. Package the scalar-component inverse as a real continuous linear map into
   `C(PeriodicTorus, ℂ)`. Hölder gives its uniform norm bound. Continuous
   evaluation supplies joint continuity in the datum and physical point, hence
   joint spacetime continuity on **Icc 0 T** for the given mild path.
6. Prove exact reweight transport, and time smoothness of the reconstructed
   components when the H³ coefficient path is smooth. These are implications;
   no smoothness or higher-order reweighting of the general mild path is asserted.
7. Non-vacuity: instantiate lane 317's contract and the actual forced Picard
   theorem with nonzero constant datum AND nonzero constant force. Also check
   the explicit affine constant path against the exact mild equation and recover
   a full `ClassicalSolutionT` with all three regularity fields on arbitrary T>0.

## Real compiler errors and repairs

Temporary logs are `tmp/318/direct*.log`; no intentionally broken Lean artifact
is part of the delivery.

- `unexpected token '∞'; expected ')'`: `ℝ≥0∞` needs `open scoped ENNReal`.
  Similarly `ℝ≥0` needs the `NNReal` scope.
- `Invalid field 're': The environment does not contain 'Continuous.re'`:
  use `Complex.continuous_re.comp`.
- `Invalid field 'integrable_of_isCompact': The environment does not contain
  'Continuous.integrable_of_isCompact'`: use the continuous-on-compact theorem
  on `univ`, with the exact function explicitly typed.
- `failed to synthesize instance of type class
  FiniteDimensional ℝ C(UnitAddTorus (Fin 3), ℂ)`:
  `Summable.norm` does not follow from arbitrary Banach-valued summability.
  Supply summability of norms directly from the coefficient bound instead.
- A square exponent was inferred as real in `memℓp_gen`:
  `... has type ... ^ (2 : ℕ) but is expected to have type ... ^ (2 : ℝ)`.
  Bridge with `Real.rpow_two`; do not change the Sobolev weight.
- `typeclass instance problem is stuck HAdd ?m.181 ?m.182 ?m.185`:
  replace underspecified `change` expressions by explicitly typed coefficients.
- `(deterministic) timeout at 'whnf', maximum number of heartbeats (200000)
  has been reached`: explicitly supply the spacetime projection in continuous
  composition. A temporary per-declaration 400000 attempt also failed; the
  final module uses the default budget everywhere, with no heartbeat override.
- Rewriting after unfolding the Picard expression reported:
  `The target expression is not type-correct under the 'implicit' transparency
  level ... has type { r // 0 ≤ r } but is expected to have type ℝ≥0`.
  Use explicit types and `erw` for that semireducible NNReal expression.

## Unresolved analytic work — not a conditional closure

The **general U9d target is not proved**, and the requested fallback of complete
(ii)+(iii) from one all-order input is not proved either. No new named analytic
input was introduced. In particular, this delivery does not rename the target
or bundle smooth physical fields and their PDE equations into an assumed
predicate. All delivered declarations are unconditional (ordinary lemma
premises such as datum representation and reweighting are displayed).

Still needed for arbitrary data on the given T:

1. A compatible all-order coefficient family, smooth in time through t=0, on
   the common horizon; joint spatial/time smoothness of its inverse.
2. Solenoidality propagated by the mild equation and physical divergence zero.
3. Smooth physical pressure from the Leray complement, normalized Haar mean,
   pressure-gradient L², and the physical Poisson identity including t=0.
4. Differentiation of the Duhamel formula and the momentum/projected equations.

The suggested immediate full-order bootstrap needs an additional argument:
convection loses one derivative, so using heat to pass directly from H^m
nonlinearity control in H^(m-1) to H^(m+1) requires two heat derivatives, whose
naive time singularity is (t-s)^(-1). That majorant is not integrable. Fractional
increments, time cancellation or high-order persistence estimates may resolve
this; merely reapplying the available one-derivative integrable kernel does not.
This is an analysis of the proposed route, not a proof that the target is false.
There is no fabricated Lean error for these mathematical obligations.

The exact unchanged target is reproduced in REPORT_318.md and in the probe's
opening comment. The probe checks the delivered sub-results and homogeneous
full-recovery case only. Its successful exit must not be recorded as closure
of general U9d. No later unit discharging a fictitious single input is assigned.
