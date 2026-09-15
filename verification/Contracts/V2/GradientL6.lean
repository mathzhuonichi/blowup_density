import Contracts.V1.GradientL6
import Contracts.V1.HomogeneousNorm

/-!
# A05 critical `L³` embedding, version 2

Version two extends the frozen `GradientL6API` with the first derived critical
embedding of Lemma B.1, in exactly the form used by Propositions 4.3 and 4.4:

`‖v‖₃ ≤ C(1/2) ‖v‖_{Ḣ¹⁄²}`.

The constant family `C : ℝ → ℝ` is a parameter of the interface, hence is
chosen before the field `v` and is visible in the checked public type.  Only its
value at `1 / 2` is constrained by this focused extension; version two does not
claim the broader `embeddingPair` field or its all-orders positivity field from
`research/A05/Spec.lean`.

The field below is token-for-token `research/A05/Spec.lean:366-368`, except that
the unqualified `dotHomogeneousENorm` resolves to the already registered
`Contracts.V1.HomogeneousNorm.dotHomogeneousENorm` rather than the Spec file's
local copy.  The definitions have the same infimum body and are definitionally
equal; see `research/A05/REVIEW_165-A05-critical-l3.md`, section "canonical
norm: rfl".  The binding records the composed implementation-to-D01-to-contract
`rfl` bridge explicitly.

No implementation module is imported here.
-/

noncomputable section

namespace BlowupDensity.Contracts.V2

open MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm (dotHomogeneousENorm)
open scoped ENNReal

/-- The frozen gradient-`L⁶` interface, extended by the order-half velocity
embedding.  The parameter is the Spec's universal constant family; this focused
contract constrains only `C (1 / 2)`. -/
structure GradientL6V2API (C : ℝ → ℝ) extends
    BlowupDensity.Contracts.V1.GradientL6API where
  /-- `research/A05/Spec.lean:366-368`, equivalently
  `appendix-b-embeddings.tex:29` and its uses at
  `paper/sections/04-whole-space.tex:93,171`. -/
  velocityCriticalL3 :
    ∀ v : SpatialField, MemHInfty v →
      eLpNorm v 3 volume ≤ ENNReal.ofReal (C (1 / 2)) * dotHomogeneousENorm (1 / 2) v

end BlowupDensity.Contracts.V2
