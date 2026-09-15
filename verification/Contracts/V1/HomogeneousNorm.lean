import Contracts.V1.Data

/-!
# Contract: the datum-form spatial homogeneous norm

This contract closes D01 gap G1, the missing physical-field quantity used by
the R43 and A05 specifications.  It deliberately does not reuse
`Data.dotHHalfENorm` or `Data.dotHThreeHalvesENorm`: those are pointwise Fourier
integrals intended for `L¹ ∩ L²` slices, whereas this definition is the honest
datum infimum and returns `⊤` when no homogeneous datum exists.

The sole import is the frozen data contract.  The implementation-side
restatement and its definitional equality are checked in
`Bindings.HomogeneousNorm`.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.HomogeneousNorm

open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal

/-- `appendix-b-embeddings.tex:26-27` and `04-whole-space.tex:85`,
`‖z‖_{Ḣ^s}` for a physical field: the infimum of the `L²` norms of all
order-`s` homogeneous data realizing it, with `⊤` for the empty infimum.

This is verbatim the definition in `research/A05/Spec.lean:131-132` and
`research/R43/Spec.lean:142-143`. -/
def dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ

end BlowupDensity.Contracts.V1.HomogeneousNorm
