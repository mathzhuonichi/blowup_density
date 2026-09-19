# Lane 443 report — T18 U9/U10 energy and mixed rates

## 1. Theorems with exact statements

### U9

The canonical records prove the complete analytic triangle and bookkeeping
statement without any added hypothesis:

```lean
theorem energyRate_separateConstants (data : InsertionData) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      energyENormT data.place.T
          (fun z => velocity data ε z - data.reference.velocity z) ≤
        ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * data.energyBound) +
          ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * data.dissipationBound) +
          ENNReal.ofReal
            (data.correction.energyConst * ε ^ ((3 : ℝ) / 2))
```

The proof includes the two component triangles
`energyEssSupT_add_le` and `energyGradientT_add_le`, the full triangle
`energyENormT_add_le`, the exact decomposition
`velocityDifference_eq_correction_add_packet`, and the record identity
`packet_energyENorm_eq`.

At the Spec boundary, `insertionU9U10OfCanonical` closes the exact requested
field:

```lean
energyRate : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
  energyENormT T (fun z => velocity ε z - v z) ≤
    ENNReal.ofReal ((P.energyBound + P.dissipationBound) *
      ε ^ ((1 : ℝ) / 2) + energyConst * ε ^ ((3 : ℝ) / 2))
```

It derives `0 ≤ P.energyBound` from `P.energy_isLUB` and
`0 ≤ P.dissipationBound` from `P.dissipation_eq`.

### U10

All four requested canonical fields close exactly under `InsertionData`
projections:

```lean
def forceDiffMixedConst (data : InsertionData) (p q : ℝ≥0∞) : ℝ :=
  if hp : 1 ≤ p then
    letI : Fact (1 ≤ p) := ⟨hp⟩
    data.correction.mixedConst p q +
      (mixedLebesgueENorm q p data.packetForce).toReal
  else 0

theorem forceDiffMixedConst_nonneg (data : InsertionData) :
    ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q →
      0 ≤ forceDiffMixedConst data p q

theorem forceDifference_mixed_memLp (data : InsertionData) :
    ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
      ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
        MemMixedLebesgueT q p (fun z => force data ε z - data.g z)

theorem forceDifference_mixed_bound (data : InsertionData) :
    ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
      ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
        mixedLebesgueENormT q p (fun z => force data ε z - data.g z) ≤
          ENNReal.ofReal (forceDiffMixedConst data p q *
            (ε ^ (alphaT p q) + ε ^ (alphaT p q + 1)))
```

The correction path follows from finiteness of
`correction.force_mixed_bound`; uniqueness of admissible representatives turns
a finite mixed norm into an honest `MemMixedLebesgueT` path.  The packet path
comes directly from `scaling.mixed_memLp`.

## 2. Files

- `formalization/NSFormalization/Section3/T18/EnergyRate.lean`: U9 energy
  triangles, decomposition, packet identity, and strongest unconditional
  canonical rate.
- `formalization/NSFormalization/Section3/T18/MixedRate.lean`: mixed-path
  uniqueness/addition, mixed triangle, constant, honesty field, and exact rate.
- `research/T18/probes/u9_u10_closes.lean`: fieldwise U1 Spec conversion,
  packet sign lemmas, and exact five-field U9/U10 Spec bundle.
- `research/T18/axioms_u9_u10.lean`: all 23 public canonical declarations.
- `research/T18/ATTEMPTS_U9_U10.md`: successful routes, exact canonical
  residual, and verbatim failed diagnostics.
- `research/T18/T18_SPLIT.md`: U9/U10 lane status.
- `research/T18/REPORT_443.md`: this report.

## 3. Gap and exact residual/error text

The only residual is the exact canonical U9 packaging:

```lean
∀ ε ∈ Set.Ioc (0 : ℝ) (ε₀ data),
  energyENormT data.place.T
      (fun z => velocity data ε z - data.reference.velocity z) ≤
    ENNReal.ofReal
      ((data.energyBound + data.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        data.correction.energyConst * ε ^ ((3 : ℝ) / 2))
```

The exact missing record facts are:

```lean
0 ≤ data.energyBound
0 ≤ data.dissipationBound
```

`InsertionData` stores both constants as unconstrained reals, while
`ScalingAPI.packetEnergyIdentity` and `packetDissipationIdentity` expose them
only beneath separate `ENNReal.ofReal` applications.  Because `ofReal`
truncates negative inputs, those identities do not imply the missing signs and
the separate terms cannot soundly be combined.  No named input or replacement
goal was introduced.  The Spec field has no residual because
`PacketImportAPI.energy_isLUB` and `dissipation_eq` supply exactly these facts.

There is no remaining compiler error.  The failed proof diagnostics, including
the `PiLp.contDiff_toLp` mismatch, unknown `essSup_add_le`, inferred
`autoParam` goal, both 200000/400000 heartbeat failures, explicit mixed-path
witness mismatch, and `ofReal` rewrite mismatch, are recorded verbatim in
`ATTEMPTS_U9_U10.md`.

One command-location diagnostic was encountered and corrected:

```text
make: *** No rule to make target 'check'.  Stop.
```

That invocation was from `verification/`; the repository target is in the
worktree-root `Makefile`, where it passes.

## 4. Commands and results

The environment was sourced from `scripts/lean-env.sh`.  Every Lake command
was run from `verification/`, and the build used `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T18.EnergyRate NSFormalization.Section3.T18.MixedRate` | pass; `Build completed successfully (10021 jobs)` |
| `lake env lean ../formalization/NSFormalization/Section3/T18/EnergyRate.lean` | pass, 0 output |
| `lake env lean ../formalization/NSFormalization/Section3/T18/MixedRate.lean` | pass, 0 output |
| `lake env lean ../research/T18/probes/u9_u10_closes.lean` | pass, 0 output |
| `lake env lean ../research/T18/axioms_u9_u10.lean` | pass; all 23 declarations print exactly `[propext, Classical.choice, Quot.sound]` |
| `make check` from the worktree root | pass; plan check, contract/import policy tests, and 45-item work queue check |

The build replayed pre-existing upstream linter warnings but reported no error.
The final forbidden-declaration scan and `git diff --check` also pass.

## Continuation fix final report (lead ruling)

### 1. Theorems

`Section3/T18/EnergyRate.lean` now contains the canonical theorem required by
the lead ruling:

```lean
theorem energyRate (data : InsertionData)
    (hM : 0 ≤ data.energyBound) (hD : 0 ≤ data.dissipationBound) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      energyENormT data.place.T
          (fun z => velocity data ε z - data.reference.velocity z) ≤
        ENNReal.ofReal ((data.energyBound + data.dissipationBound) *
          ε ^ ((1 : ℝ) / 2) +
          data.correction.energyConst * ε ^ ((3 : ℝ) / 2))
```

Its conclusion is the Spec field verbatim under the `InsertionData`
projections.  The proof derives it from `energyRate_separateConstants`, using
`ENNReal.ofReal_add` twice.  Nonnegativity of the three real summands follows
from `hM`, `hD`, `correction.energyConst_nonneg`, and `ε > 0`.

### 2. Files

- `formalization/NSFormalization/Section3/T18/EnergyRate.lean`: added the
  canonical `energyRate` theorem with the two explicit raw premises;
  `InsertionData` was not changed.
- `research/T18/probes/u9_u10_closes.lean`: removed the probe-local assembly
  lemma and now closes the Spec field directly through canonical `energyRate`,
  discharging its premises from `PacketImportAPI.energy_isLUB` and
  `dissipation_eq`.
- `research/T18/axioms_u9_u10.lean`: added `energyRate` to the public axiom
  audit.
- `research/T18/ATTEMPTS_U9_U10.md`: records the lead ruling and marks the old
  parameter-free residual as superseded.
- `research/T18/T18_SPLIT.md`: marks U9 complete under the explicit-premise
  ruling.
- `research/T18/REPORT_443.md`: appended this four-part continuation report.

### 3. Gaps

There is no remaining U9 proof or Spec-field residual.  The intentional
canonical interface boundary is: **explicit raw premises; U12 discharges them
from the packet clauses; a later MAINT may add them to `InsertionData`**.  The
registered packet clauses used by U12 are `PacketImportAPI.energy_isLUB` for
`0 ≤ energyBound` and `PacketImportAPI.dissipation_eq` for
`0 ≤ dissipationBound`.  This section supersedes the pre-ruling residual in
the original §3 above.

### 4. Commands and results

- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.EnergyRate
  NSFormalization.Section3.T18.MixedRate` — success, 10,021 jobs, zero errors.
- `lake env lean ../formalization/NSFormalization/Section3/T18/EnergyRate.lean`
  — zero output.
- `lake env lean ../formalization/NSFormalization/Section3/T18/MixedRate.lean`
  — zero output.
- `lake env lean ../research/T18/probes/u9_u10_closes.lean` — zero output; the
  Spec `energyRate` field closes through the canonical theorem.
- `lake env lean ../research/T18/axioms_u9_u10.lean` — all 24 public
  declarations print exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` from the worktree root — success; all 13 contract-policy tests
  pass and all 45 work items are consistent.
