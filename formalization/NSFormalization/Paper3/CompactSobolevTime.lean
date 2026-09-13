import NSFormalization.Paper3.SobolevTimeSmooth

/-! Compact smooth spacetime functions as actual Sobolev-valued smooth,
Bochner-integrable trajectories. -/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

/-- The actual weighted Fourier L² time trajectory of a compact smooth input. -/
def compactSobolevTimeSlice (s : ℝ) (F : ℝ × Space → ℂ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    Lp ℂ 2 (volume : Measure Space) :=
  compactFourierLp s (fun x => F (t, x))
    (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t)

/-- Genuine Banach-valued C∞ regularity, for every real Sobolev order. -/
theorem contDiff_compactSobolevTimeSlice (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (compactSobolevTimeSlice s F hF hc) := by
  let K := Prod.snd '' tsupport F
  have hK : IsCompact K := (hc : IsCompact (tsupport F)).image continuous_snd
  have hz : ∀ t x, x ∉ K → F (t, x) = 0 := by
    intro t x hx
    apply image_eq_zero_of_notMem_tsupport (f := F)
    intro htx
    exact hx ⟨(t, x), htx, rfl⟩
  exact contDiff_sobolevTimeSlice s hF hK hz

/-- The genuine Sobolev trajectory has compact time support. -/
theorem hasCompactSupport_compactSobolevTimeSlice (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    HasCompactSupport (compactSobolevTimeSlice s F hF hc) := by
  apply hasCompactSupport_norm_iff.mp
  simpa only [compactSobolevTimeSlice, norm_compactFourierLp] using compact_fourierSobolev_time s hc

/-- Actual Bochner Lq membership of the Sobolev trajectory, rather than merely
membership of a scalar expression declared to represent its norm. -/
theorem memLp_compactSobolevTimeSlice (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) :
    MemLp (compactSobolevTimeSlice s F hF hc) q volume :=
  (contDiff_compactSobolevTimeSlice s hF hc).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_compactSobolevTimeSlice s hF hc)

/-- All manuscript integer-order smoothness and L1/L2 requirements for scalar
forces hold in the concrete Fourier L² Sobolev representation. -/
theorem compact_scalar_force_sobolev_regular {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∀ m : ℕ, ContDiff ℝ ∞ (compactSobolevTimeSlice (m : ℝ) F hF hc) ∧
      MemLp (compactSobolevTimeSlice (m : ℝ) F hF hc) 1 volume ∧
      MemLp (compactSobolevTimeSlice (m : ℝ) F hF hc) 2 volume :=
  fun m => ⟨contDiff_compactSobolevTimeSlice (m : ℝ) hF hc,
    memLp_compactSobolevTimeSlice (m : ℝ) hF hc 1,
    memLp_compactSobolevTimeSlice (m : ℝ) hF hc 2⟩

end NSFormalization.Paper3
