import NSFormalization.Section4.A04.RestartWiring
namespace NSFormalization.Section4
open Set MeasureTheory
open scoped ENNReal
example {ν S : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (ha : a ∈ A02.initialClassR) (c : A01.LocalCarrier ν a f S) :
    ∀ m : ℕ, 3 ≤ m → BddAbove
      (range (fun t : Ico (0 : ℝ) S => A04.sobolevNormAt (m : ℝ) c.w.velocity t)) := by
  obtain ⟨u, hU, _hdiv, hu, _hduh⟩ := c.hpairs 6 (by omega)
  have hs : ∀ t : Icc (0 : ℝ) S,
      (fun x => c.w.velocity (↑t, x)) =ᵐ[volume] ⇑(c.U t) := by
    simpa only [c.velocity_eq] using c.hslice
  exact A01.highOrder_bddAbove_all_orders_Ico_full c.hν ha c.hf c.w
    c.regularity.sobolev_smooth c.hS u c.U hu hU (by omega) hs (le_refl ‖u‖)
end NSFormalization.Section4
