import NSFormalization.Section4.A01.MildUniqueness

noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerQuadraticSource EulerVolterraConvolution
open scoped Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Deliberately false-strength mutation: replace the mass on `(0,δ]` by the
mass on the strictly shorter `(0,δ/2]`. Applying the reviewed proof must fail. -/
example {S : ℝ} (hS : 0 ≤ S) (K : ℝ → Y →L[ℝ] X) (k : ℝ → ℝ)
    (hK : ContinuousOn (fun p : ℝ × Y => K p.1 p.2) (Ioi 0 ×ˢ (univ : Set Y)))
    (hk : IntegrableOn k (Ioc 0 S)) (hk0 : ∀ r ∈ Ioc 0 S, 0 ≤ k r)
    (hbound : ∀ r ∈ Ioc 0 S, ∀ y, ‖K r y‖ ≤ k r * ‖y‖)
    (d : C(Icc (0 : ℝ) S, X)) (f : C(Icc (0 : ℝ) S, Y))
    (L : ℝ) (hL : 0 ≤ L) (hf : ∀ t, ‖f t‖ ≤ L * ‖d t‖)
    (hd : d = convolution S hS K k hK hk hk0 hbound f)
    {a b δ : ℝ} (hb : 0 ≤ b) (hbS : b ≤ S) (hδS : δ ≤ S)
    (hbδ : b ≤ a + δ) (hpast : ∀ t : Icc (0 : ℝ) S, t.val ≤ a → d t = 0) :
    ‖d.comp (timeInclusion hbS)‖ ≤
      (kernelMass (δ / 2) k * L) * ‖d.comp (timeInclusion hbS)‖ := by
  exact volterra_window_bound (δ := δ) hS K k hK hk hk0 hbound d f L hL hf hd
    hb hbS hδS hbδ hpast

end NSFormalization.Section4.A01
