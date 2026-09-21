import NSFormalization.Paper3.SobolevBoundedRepresentative
import NSFormalization.Paper3.CompleteTameProduct

/-! # Physical identification of the complete scalar Sobolev product

The continuous bilinear extension is multiplication of the actual bounded
continuous representatives. All statements concern the existing scalar
cycles-frequency Sobolev model; no angular or tensor norm conversion is asserted.
-/
noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source.FourierTameProduct
open scoped SchwartzMap

/-- Complete Sobolev multiplication is literal bounded-continuous multiplication. -/
theorem sobolevBoundedRepresentative_product (m : ℕ) (hm : 2 ≤ m)
    (h k : SobolevHilbert m) :
    sobolevBoundedRepresentative m (by exact_mod_cast hm) (sobolevProduct m hm h k) =
      sobolevBoundedRepresentative m (by exact_mod_cast hm) h *
        sobolevBoundedRepresentative m (by exact_mod_cast hm) k := by
  refine (denseRange_weightedFourierLp m).induction_on h
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro φ
  refine (denseRange_weightedFourierLp m).induction_on k
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro ψ
  rw [sobolevProduct_weightedFourierLp]
  simp only [sobolevBoundedRepresentative_weightedFourierLp]
  ext x
  rfl

/-- The physical representative agrees with the pointwise product at every point. -/
theorem sobolevBoundedRepresentative_product_apply (m : ℕ) (hm : 2 ≤ m)
    (h k : SobolevHilbert m) (x : Space) :
    sobolevBoundedRepresentative m (by exact_mod_cast hm) (sobolevProduct m hm h k) x =
      sobolevBoundedRepresentative m (by exact_mod_cast hm) h x *
        sobolevBoundedRepresentative m (by exact_mod_cast hm) k x := by
  rw [sobolevBoundedRepresentative_product]
  rfl

/-- The product pairing is integrable without an L1 premise on either datum. -/
theorem sobolevPhysicalProduct_integrable (m : ℕ) (hm : 2 ≤ m)
    (h k : SobolevHilbert m) (θ : SchwartzMap Space ℂ) :
    Integrable (fun x : Space => θ x *
      (sobolevBoundedRepresentative m (by exact_mod_cast hm) h x *
        sobolevBoundedRepresentative m (by exact_mod_cast hm) k x)) :=
  schwartz_mul_bounded_integrable θ
    (sobolevBoundedRepresentative m (by exact_mod_cast hm) h *
      sobolevBoundedRepresentative m (by exact_mod_cast hm) k)

/-- The completed product realizes precisely the ordinary physical product. -/
theorem sobolevRealization_product (m : ℕ) (hm : 2 ≤ m)
    (h k : SobolevHilbert m) (θ : SchwartzMap Space ℂ) :
    sobolevRealization m (sobolevProduct m hm h k) θ =
      ∫ x : Space, θ x *
        (sobolevBoundedRepresentative m (by exact_mod_cast hm) h x *
          sobolevBoundedRepresentative m (by exact_mod_cast hm) k x) := by
  rw [sobolevRealization_boundedRepresentative m (by exact_mod_cast hm),
    sobolevBoundedRepresentative_product]
  rfl

/-- The exact complete tame estimate and physical identity hold for the same product. -/
theorem sobolevProduct_tame_and_physical (m : ℕ) (hm : 2 ≤ m)
    (h k : SobolevHilbert m) :
    (‖sobolevProduct m hm h k‖ ≤ sobolevTameConstant m *
      (‖sobolevOrderLowering m 2 (by exact_mod_cast hm) k‖ * ‖h‖ +
        ‖sobolevOrderLowering m 2 (by exact_mod_cast hm) h‖ * ‖k‖)) ∧
    (∀ θ : SchwartzMap Space ℂ,
      sobolevRealization m (sobolevProduct m hm h k) θ =
        ∫ x : Space, θ x *
          (sobolevBoundedRepresentative m (by exact_mod_cast hm) h x *
            sobolevBoundedRepresentative m (by exact_mod_cast hm) k x)) :=
  ⟨sobolevProduct_tame_bound m hm h k, sobolevRealization_product m hm h k⟩

end NSFormalization.Paper3
