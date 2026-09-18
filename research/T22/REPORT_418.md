# Lane 418-T22-UZ1-zero-extension-comparison

## 1. The theorem

`formalization/NSFormalization/Section3/T22/ZeroExtensionComparison.lean`
closes the canonical field in namespace
`NSFormalization.Section3.T22`:

```lean
theorem zeroExtensionComparison :
    ∀ (Ω K : Set Space), IsOpen Ω → IsCompact K → K ⊆ Ω →
      ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ z : SpatialField,
        ContDiffOn ℝ ∞ z Ω → tsupport (zeroExtension Ω z) ⊆ K →
        domainSobolevENorm Ω s (restrictField Ω z) ≤
            sobolevENorm s (zeroExtension Ω z) ∧
          sobolevENorm s (zeroExtension Ω z) ≤
            ENNReal.ofReal C * domainSobolevENorm Ω s (restrictField Ω z)
```

The left conjunct is U-B1.  For the right conjunct, U-B3 chooses a smooth
compactly supported cutoff equal to one near `K`, U-A3 supplies the positive
constant and a cutoff datum for every admissible domain datum, and U-B3b turns
that cutoff datum into a datum of the zero extension.  The final infimum step
uses `ENNReal.mul_iInf`; when the admissible subtype is empty,
`domainSobolevENorm = ⊤` and the result is immediate.

## 2. Files

Added:

- `formalization/NSFormalization/Section3/T22/ZeroExtensionComparison.lean`
- `research/T22/probes/zero_extension_comparison_closes.lean`
- `research/T22/axioms_uz1.lean`
- `research/T22/ATTEMPTS_UZ1.md`
- `research/T22/REPORT_418.md`

Updated the U-Z1 status entry in `research/T22/T22_SPLIT.md`.

The probe contains both the exact field-type match and a nonzero smooth vector
bump on `Ω = ball 0 1`, supported in `K = closedBall 0 (1/2)`.

## 3. Gaps and error text

There is no remaining U-Z1 residual, named input, placeholder, `sorry`,
`admit`, `axiom`, or `native_decide`.  The first local draft briefly produced
the following repaired elaboration errors:

```text
Unknown identifier `RealVectorSobolev`
failed to synthesize instance of type class
  Nonempty { A // restrictDatum Ω s A = restrictField Ω z }
failed to synthesize instance of type class
  IsEmpty { A // restrictDatum Ω s A = restrictField Ω z }
```

They came from an omitted `open NSFormalization.Paper3` and an unnecessary
local norm abbreviation; the final proof opens the canonical type and uses
`have := hne` / `have : IsEmpty ...` directly.  The final module has no direct
Lean output.  The axiom audit prints exactly:

```text
'NSFormalization.Section3.T22.zeroExtensionComparison' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 4. Commands and results

All commands were run after `. scripts/lean-env.sh`; `lake` commands were run
from `verification/` with `LEAN_NUM_THREADS=6` where applicable.

| command | result |
|---|---|
| `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.ZeroExtensionComparison` | exit 0; module built successfully, 0 errors |
| `LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T22/ZeroExtensionComparison.lean` | exit 0; 0 output |
| `LEAN_NUM_THREADS=6 lake env lean ../research/T22/probes/zero_extension_comparison_closes.lean` | exit 0; 0 output |
| `LEAN_NUM_THREADS=6 lake env lean ../research/T22/axioms_uz1.lean` | exit 0; standard three axioms shown above |
| `make check` | exit 0; 13 policy tests OK and 45 work items consistent |
