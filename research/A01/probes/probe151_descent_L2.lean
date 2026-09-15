import NSFormalization.Section4.A01.CarrierWords

/-! Lane-151 probe for piece **(d)**: the `L²`-level descent of an angle-invariant lift, which would
remove the 3-order jet loss and cover the top three orders `n ∈ {q−1, q, q+1}` of `hword_jet`.

Statement (from `research/A01/REVIEW_APRIORI_ROWS.md` §2):

    ∀ g : LiftL2 1, (∀ θ, translation 1 (0,θ) g = g) →
      ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g

i.e. every angle-invariant `L²` cylinder field is (the `ordinaryLift` of) a θ-independent ordinary
`L²` field on `ℝ³`, with **no** jet / regularity hypothesis.  This is stated but **not proved** here;
the file records the statement (as a `Prop`) and `#check`s the tree pieces, so the obstruction is
documented against real Lean signatures.  See `research/A01/ATTEMPTS_CARRIER_WORDS.md`. -/

noncomputable section

namespace Probe151DescentL2

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Piece (d), as a proposition (no jet hypothesis). -/
def DescentL2 : Prop :=
  ∀ g : LiftL2 1, (∀ θ : AddCircle (1 : ℝ), translation 1 ((0 : Vector3), θ) g = g) →
    ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g

#check @DescentL2

/-! ### The pieces the tree provides, and where they stop.

`exists_ordinary_value` is the **jet-level** analogue: it descends an angle-invariant *finite-order
Sobolev* field `SobolevSpace 1 q` (needing `3 ≤ q`), by taking the `θ = 0` slice of its **continuous
H³ representative** (`representative 1 v`, a genuine pointwise function).  That θ = 0 slice is exactly
the 3-order jet loss — a raw `LiftL2 1` element has no pointwise `θ = 0` slice (it is defined only up
to a null set of `ℝ³ × S¹`). -/
#check @NSFormalization.Source.OrdinaryCylinderDescent.exists_ordinary_value
#check @EulerMeanOrdinaryLift.ordinaryLift            -- EulerMeanSolenoidal.L2 →ₗᵢ[ℝ] LiftL2 1
#check @EulerMeanOrdinaryLift.ordinaryLift_ae         -- ⇑(ordinaryLift u) =ᵐ ⇑u ∘ Prod.fst
#check @EulerMeanOrdinaryLift.ordinaryProjection_measurePreserving

end Probe151DescentL2
