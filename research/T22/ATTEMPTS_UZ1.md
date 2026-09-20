# T22 U-Z1 attempts and closure

## Closed route

`zeroExtensionComparison` is pure assembly from the registered U-B1, U-B2,
U-B3, and U-A3 results.

1. For `K ⋐ Ω`, `exists_cutoff` supplies `χ` with smoothness, compact support,
   `tsupport χ ⊆ Ω`, and `χ = 1` near `K`.
2. `cutoffMultiplier s χ` supplies one positive constant `C`, chosen before
   the field `z`, and for each whole-space datum `A` a cutoff datum `B` with
   `‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ`.
3. For a field satisfying the comparison hypotheses, every subtype member
   `A` in the definition of `domainSobolevENorm` satisfies
   `restrictDatum Ω s A = restrictField Ω z`.  U-B3b then gives
   `IsSobolevDatum s (zeroExtension Ω z) B`, hence
   `sobolevENorm s (zeroExtension Ω z) ≤ ‖B‖ₑ`.
4. In the nonempty datum-subtype case, `ENNReal.mul_iInf` rewrites
   `ofReal C * ⨅ A, ‖A‖ₑ` as `⨅ A, ofReal C * ‖A‖ₑ`, and the pointwise bound
   closes the right inequality.  In the empty case,
   `domainSobolevENorm = ⊤`, so the right inequality is `≤ ⊤`.
5. The left inequality is exactly U-B1's
   `domainSobolevENorm_le_sobolevENorm`; no separate choice of a zero-extension
   datum is needed in this bookkeeping lemma.

## Failed/obsolete route

An initial draft introduced a local abbreviation `q` before opening
`NSFormalization.Paper3`, producing `Unknown identifier RealVectorSobolev` and
typeclass errors on the empty/nonempty subtype.  Removing the abbreviation and
using the canonical norm expression `‖A.1‖ₑ` fixed the elaboration.  The final
proof uses anonymous local hypotheses (`have := hne` and
`have : IsEmpty ...`) so the module's direct `lake env lean` check is silent.

There is no residual theorem, named input, placeholder, `sorry`, or extra axiom.
