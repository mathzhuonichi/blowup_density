import Bindings.AffineVariation
open Set
open BlowupDensity
open BlowupDensity.Contracts.V1
open BlowupDensity.Bindings
example {ν : ℝ} (P : PacketAPI ν) (c : Space) {r τ₀ τ₁ : ℝ}
    (hr : 0 < r) (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁) (hτ₁ : τ₁ ≤ 1) :
    AffineVariationAPI P c r τ₀ τ₁ := by
  exact affineVariation P c hr hτ₀ hτ₀τ₁ hτ₁
