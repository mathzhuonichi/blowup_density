import Contracts.V1.BoundedRepresentative
import NSFormalization.Section4.A03.BoundedRepresentative

/-! The only layer that knows the current implementation's names and paths.

`Contracts.V1.BoundedRepresentative` is self-contained, so this adapter has two
jobs: record by `rfl` that each notion the specification writes out is the
notion the proof modules use, and assemble the proved estimates into the
contract.

Every declaration here carries a `boundedRep`/`boundedRepresentative` prefix.
`BlowupDensity.Bindings` is a flat namespace shared by all adapters, and lane
019's `Bindings/GradientL6.lean` already declares a bridge for the same
identically-spelled jet class; two modules declaring one full name cannot be
imported together.
-/

noncomputable section
namespace BlowupDensity.Bindings

open MeasureTheory
open NavierStokes.ProblemStatement

section Correspondence

variable (v : Contracts.V1.Data.SpatialField) (m : ℕ)

/-- The contract's truncated field class — the hypothesis of both estimates — is
the implementation's `SmoothL2UpTo`. -/
theorem boundedRep_smoothJetsUpTo_eq :
    Contracts.V1.BoundedRep.SmoothJetsUpTo m v
      = NSFormalization.Section4.A03.SmoothL2UpTo m v := rfl

/-- The contract's all-order field class is the implementation's `SmoothL2`,
hence also the vendor's `EulerLpTranslation.SmoothL2Field` field for field. -/
theorem boundedRep_smoothSquareIntegrableJets_eq :
    Contracts.V1.BoundedRep.SmoothSquareIntegrableJets v
      = NSFormalization.Section4.A03.SmoothL2 v := rfl

/-- The contract's jet Sobolev norm is the implementation's `jetENorm`. -/
theorem boundedRep_jetSobolevENorm_eq :
    Contracts.V1.BoundedRep.jetSobolevENorm m v
      = NSFormalization.Section4.A03.jetENorm m v := rfl

end Correspondence

/-- Bind the proved `H² ↪ L^∞` estimates to the stable version-one contract. -/
def boundedRepresentative : Contracts.V1.BoundedRep.BoundedRepresentativeAPI where
  Cinfty := NSFormalization.Section4.A03.boundedRepresentativeConst
  Cinfty_pos := NSFormalization.Section4.A03.boundedRepresentativeConst_pos
  smoothJetsUpTo_of_allOrders := fun m _ hv => NSFormalization.Section4.A03.SmoothL2.upTo hv m
  supNorm_le := fun _ hz x => NSFormalization.Section4.A03.enorm_le_jetENorm hz x
  eLpNormTop_le := fun _ hz => NSFormalization.Section4.A03.eLpNormTop_le_jetENorm hz

end BlowupDensity.Bindings
