import Contracts.V1.TameProduct
import NSFormalization.Section4.A03.OuterTameProduct

/-! The only layer that knows the current implementation's names and paths for
the product clauses of Lemma A.1.

`Contracts.V1.TameProduct` is self-contained — its sole import is another
contract, `Contracts.V1.Data` — so this adapter has two jobs: record by `rfl`
that each notion the specification writes out is the notion the proof modules
use, and assemble the proved estimates into the contract.

Every declaration here carries a `tameProduct_` prefix.  `BlowupDensity.Bindings`
is a flat namespace shared by all adapters, and lane 023's
`Bindings/BoundedRepresentative.lean` already declares bridges for an
identically-spelled jet class.
-/

noncomputable section
namespace BlowupDensity.Bindings

open MeasureTheory
open NavierStokes.ProblemStatement

section Correspondence

variable (s : ℝ) (m j : ℕ) (i : Fin 3) (a : Space → ℝ)
  (u v w : Contracts.V1.Data.SpatialField) (T : Fin 3 → Contracts.V1.Data.SpatialField)

/-- The contract's scalar datum predicate is the implementation's. -/
theorem tameProduct_isScalarSobolevDatum_eq
    (A : NSFormalization.Source.RealSobolev.RealSobolevHilbert s) :
    Contracts.V1.TameProduct.IsScalarSobolevDatum s a A
      = NSFormalization.Section4.A03.IsScalarSobolevDatum s a A := rfl

/-- The contract's scalar Sobolev norm is the implementation's. -/
theorem tameProduct_scalarSobolevENorm_eq :
    Contracts.V1.TameProduct.scalarSobolevENorm s a
      = NSFormalization.Section4.A03.scalarSobolevENorm s a := rfl

/-- The contract's admissible scalar class is the implementation's. -/
theorem tameProduct_memHmScalar_eq :
    Contracts.V1.TameProduct.MemHmScalar m a
      = NSFormalization.Section4.A03.MemHmScalar m a := rfl

/-- The contract's admissible three-vector class is the implementation's; in
particular the contract's `Data.sobolevENorm` is the restatement
`NSFormalization.Section4.D01.sobolevENorm` that the proof modules use. -/
theorem tameProduct_memHmVector_eq :
    Contracts.V1.TameProduct.MemHmVector m w
      = NSFormalization.Section4.A03.MemHmVector m w := rfl

theorem tameProduct_sobolevENorm_eq :
    Contracts.V1.Data.sobolevENorm s w = NSFormalization.Section4.D01.sobolevENorm s w := rfl

/-- The contract's jet class is the implementation's `SmoothL2`, hence also the
vendor's `EulerLpTranslation.SmoothL2Field` field for field. -/
theorem tameProduct_smoothJets_eq :
    Contracts.V1.TameProduct.SmoothJets w = NSFormalization.Section4.A03.SmoothL2 w := rfl

theorem tameProduct_lift_eq :
    Contracts.V1.TameProduct.lift w = NSFormalization.Section4.A03.lift w := rfl

theorem tameProduct_partialDeriv_eq (k : Fin 3) :
    Contracts.V1.TameProduct.partialDeriv k w
      = NSFormalization.Section4.A03.partialDeriv k w := rfl

theorem tameProduct_advectionOf_eq :
    Contracts.V1.TameProduct.advectionOf u v = NSFormalization.Section4.A03.advectionOf u v := rfl

theorem tameProduct_outerColumn_eq (k : Fin 3) :
    Contracts.V1.TameProduct.outerColumn u v k
      = NSFormalization.Section4.A03.outerColumn u v k := rfl

theorem tameProduct_diffField_eq :
    Contracts.V1.TameProduct.diffField u v = NSFormalization.Section4.A03.diffField u v := rfl

theorem tameProduct_columnsSobolevENorm_eq :
    Contracts.V1.TameProduct.columnsSobolevENorm s T
      = NSFormalization.Section4.A03.columnsSobolevENorm s T := rfl

theorem tameProduct_outerSobolevENorm_eq :
    Contracts.V1.TameProduct.outerSobolevENorm s u v
      = NSFormalization.Section4.A03.outerSobolevENorm s u v := rfl

theorem tameProduct_outerDiffSobolevENorm_eq :
    Contracts.V1.TameProduct.outerDiffSobolevENorm s u v
      = NSFormalization.Section4.A03.outerDiffSobolevENorm s u v := rfl

theorem tameProduct_gradientSobolevENorm_eq :
    Contracts.V1.TameProduct.gradientSobolevENorm s w
      = NSFormalization.Section4.A03.gradientSobolevENorm s w := rfl

end Correspondence

/-- Bind the proved product estimates of Lemma A.1 to the stable version-one
contract. -/
def tameProduct : Contracts.V1.TameProduct.TameProductAPI where
  C := NSFormalization.Section4.A03.vectorTameConst
  C_pos := NSFormalization.Section4.A03.vectorTameConst_pos
  Calg := NSFormalization.Section4.A03.algebraConst
  Calg_pos := NSFormalization.Section4.A03.algebraConst_pos
  Ctame := NSFormalization.Section4.A03.outerTameConst
  Ctame_pos := NSFormalization.Section4.A03.outerTameConst_pos
  Cdiff := NSFormalization.Section4.A03.outerDiffConst
  Cdiff_pos := NSFormalization.Section4.A03.outerDiffConst_pos
  Cadv := NSFormalization.Section4.A03.advectionConst
  Cadv_pos := NSFormalization.Section4.A03.advectionConst_pos
  scalarSobolevENorm_component_le := fun s z i =>
    NSFormalization.Section4.A03.scalarSobolevENorm_component_le s z i
  sobolevENorm_le_sum_components := fun s z =>
    NSFormalization.Section4.A03.sobolevENorm_le_sum_components s z
  smoothJets_memHmVector := fun m _ h => NSFormalization.Section4.A03.SmoothL2.memHmVector h m
  smoothJets_memHmScalar := fun m _ h i =>
    NSFormalization.Section4.A03.SmoothL2.memHmScalar h m i
  smoothJets_partialDeriv := fun _ h j => NSFormalization.Section4.A03.SmoothL2.partialDeriv h j
  tameProductScalar := fun m hm _ _ ha hb =>
    NSFormalization.Section4.A03.tameProductScalar_vectorConst m hm ha hb
  tameProductVector := fun m hm _ _ ha hw =>
    NSFormalization.Section4.A03.tameProductVector m hm ha hw
  algebraProductScalar := fun k hk _ _ ha hb =>
    NSFormalization.Section4.A03.algebraProductScalar k (by omega) ha hb
  outerProductTame := fun k hk _ hu =>
    NSFormalization.Section4.A03.outerProductTame k (by omega) hu
  outerProductDifference := fun k hk _ _ hu hv =>
    NSFormalization.Section4.A03.outerProductDifference k (by omega) hu hv
  smoothJets_advectionTame := fun m hm _ _ hu hv =>
    NSFormalization.Section4.A03.advectionTame m hm hu hv

end BlowupDensity.Bindings
