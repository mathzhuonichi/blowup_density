import NSFormalization.Paper3.CompactSobolevTime
import NSFormalization.Source.ForceNormAddition
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Compact smooth vector forces satisfy the smoothness and global L1/L2
requirements in the genuine finite-product Fourier L² Sobolev representation. -/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source
open scoped ContDiff ENNReal

/-- The actual vector Sobolev trajectory is C∞ for every real order. -/
theorem contDiff_compactVectorFourierLp (s : ℝ) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (compactVectorFourierLp s F hF hc) := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact contDiff_compactSobolevTimeSlice s (coordinateForce_smooth hF i) (coordinateForce_compact hc i)

/-- The genuine vector Sobolev trajectory has compact time support. -/
theorem hasCompactSupport_compactVectorFourierLp (s : ℝ) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    HasCompactSupport (compactVectorFourierLp s F hF hc) := by
  apply HasCompactSupport.intro ((hc : IsCompact (tsupport F)).image continuous_fst)
  intro t ht
  have hz (x : Space) : F (t, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := F)
    intro htx
    exact ht ⟨(t, x), htx, rfl⟩
  apply PiLp.ext
  intro i
  change compactFourierLp s (fun x => coordinateForce F i (t, x)) _ _ = 0
  unfold compactFourierLp
  have he : NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => coordinateForce F i (t, x))
      ((coordinateForce_smooth hF i).comp (contDiff_const.prodMk contDiff_id))
      (compact_spatial_slice (coordinateForce_compact hc i) t) = 0 := by
    ext x
    simp [coordinateForce, hz x]
  rw [he, map_zero]

/-- Actual Bochner Lq membership for vector Sobolev trajectories. -/
theorem memLp_compactVectorFourierLp (s : ℝ) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) :
    MemLp (compactVectorFourierLp s F hF hc) q volume :=
  (contDiff_compactVectorFourierLp s hF hc).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_compactVectorFourierLp s hF hc)

/-- Every compact smooth physical vector force satisfies all nonnegative
integer-order Sobolev-valued C∞ and global Bochner L1/L2 conditions. The codomain
is the explicit Hilbert representation, not a postulated family of scalar norms. -/
theorem compact_vector_force_sobolev_regular {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∀ m : ℕ, ContDiff ℝ ∞ (compactVectorFourierLp (m : ℝ) F hF hc) ∧
      MemLp (compactVectorFourierLp (m : ℝ) F hF hc) 1 volume ∧
      MemLp (compactVectorFourierLp (m : ℝ) F hF hc) 2 volume :=
  fun m => ⟨contDiff_compactVectorFourierLp (m : ℝ) hF hc,
    memLp_compactVectorFourierLp (m : ℝ) hF hc 1,
    memLp_compactVectorFourierLp (m : ℝ) hF hc 2⟩

end NSFormalization.Paper3
