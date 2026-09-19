# T18 U9/U10 attempts and outcome

## Successful route

For U9, `energyENormT` was split into its two defining summands.  The
`energyEssSupT` triangle follows from slice-wise `eLpNorm_add_le` and
`ENNReal.essSup_add_le`.  For `energyGradientT`, smoothness gives the exact
spatial-gradient addition formula and measurable time paths; then
`ENNReal.lintegral_Lp_add_le` at exponent `2` is precisely the required
Minkowski inequality.  The threaded correction and scaling slice guards close
the resulting full-energy triangle.  The packet identities and correction
bound give `energyRate_separateConstants` with three separate
`ENNReal.ofReal` terms.  The canonical `energyRate` then combines those terms
under the two explicit raw nonnegativity premises described below.

For U10, admissible mixed-norm paths representing the same physical slices
are equal almost everywhere.  Hence every admissible path realizes the
infimum defining `mixedLebesgueENormT`, finite mixed norm supplies an honest
`MemMixedLebesgueT` witness, and explicit path addition gives the mixed-norm
triangle.  This avoids reconstructing a continuous correction path:
`correction.force_mixed_bound` makes the correction norm finite, while
`scaling.mixed_memLp` supplies the packet path.  The selected constant is

```lean
forceDiffMixedConst data p q =
  data.correction.mixedConst p q +
    (mixedLebesgueENorm q p data.packetForce).toReal
```

on the stated range `1 ≤ p`; the two rate terms are absorbed by elementary
nonnegative real arithmetic.

## Lead ruling resolution

The canonical theorem now follows the same ruling as lane 435's
`velocityDifference_support`: facts available on the registered raw packet but
erased by `InsertionData` are explicit theorem premises.  `InsertionData`
remains unchanged:

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

The proof applies `energyRate_separateConstants` and uses
`ENNReal.ofReal_add` twice.  Its three real summands are nonnegative from
`hM`, `hD`, `data.correction.energyConst_nonneg`, and `ε > 0`.

`probes/u9_u10_closes.lean` models U12 assembly.  It discharges the explicit
raw premises from `PacketImportAPI.energy_isLUB` and
`PacketImportAPI.dissipation_eq`, respectively, and closes the Spec field by a
direct call to `energyRate`.  Thus the ruling is: **explicit raw premises; U12
discharges them from the packet clauses; a later MAINT may add them to
`InsertionData`**.

## Pre-ruling exact canonical U9 residual (superseded)

Before the lead ruling, the exact unresolved canonical statement was

```lean
∀ ε ∈ Set.Ioc (0 : ℝ) (ε₀ data),
  energyENormT data.place.T
      (fun z => velocity data ε z - data.reference.velocity z) ≤
    ENNReal.ofReal
      ((data.energyBound + data.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        data.correction.energyConst * ε ^ ((3 : ℝ) / 2))
```

Canonical `InsertionData` stores `energyBound` and `dissipationBound` as raw
reals, and `ScalingAPI` carries only the two `ENNReal.ofReal` identities.  It
does not carry either

```lean
0 ≤ data.energyBound
0 ≤ data.dissipationBound
```

so the separate `ofReal` terms cannot be combined across real addition.
This is substantive: `ENNReal.ofReal` truncates negative inputs, so an
arbitrary positive and negative pair need not satisfy
`ofReal a + ofReal b ≤ ofReal (a + b)`.  At that stage no named hypothesis was
permitted.  The explicit-premise ruling above supersedes this residual without
changing the underlying interface analysis.

## Failed approaches and exact diagnostics

An initial attempt to obtain slice differentiability through the `Lp` API
used a theorem with the wrong shape:

```text
Function expected at
  PiLp.contDiff_toLp
but this term has type
  ContDiff ?m.116 ?m.125 (WithLp.toLp ?m.123)
```

Searching for a generic essential-supremum triangle under the wrong name gave:

```text
Unknown identifier `essSup_add_le`
```

An early `essSup_mono_ae` application left an inferred boundedness side
condition unresolved:

```text
unsolved goals
case hf
...
⊢ autoParam
    (IsCoboundedUnder ...)
```

Before the energy bookkeeping proof was split into smaller declarations,
elaboration failed at the default heartbeat limit:

```text
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

Increasing the local limit did not repair that proof structure:

```text
(deterministic) timeout at `whnf`, maximum number of heartbeats (400000) has been reached
```

The final split proof needs no heartbeat override.

The first mixed-path addition attempt asked Lean to use the anonymous witness
chosen by an existential instead of the explicit sum path:

```text
Application type mismatch: The argument
  MemLp.aestronglyMeasurable (MemLp.add hFm hGm)
has type
  AEStronglyMeasurable (F + G) forceTimeMeasure
but is expected to have type
  AEStronglyMeasurable (Exists.choose ⋯) forceTimeMeasure
```

Introducing `periodicLebesgueSlicePath_add` fixed the witness spelling.

The first conversion of the finite packet norm back through `ofReal` rewrote
only one side of the desired equality:

```text
⊢ ENNReal.ofReal x * ENNReal.ofReal N.toReal =
    ENNReal.ofReal x * ENNReal.ofReal (ENNReal.ofReal N.toReal).toReal
```

An explicit equality `ENNReal.ofReal N.toReal = N`, followed by a two-step
calculation, fixed the mismatch.

Finally, the first probe version omitted the notation scope needed by its
Spec restatement; expressions containing `ℝ≥0∞` produced parser errors.  The
fix was:

```lean
open scoped ENNReal
```
