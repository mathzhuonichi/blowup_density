import NSFormalization.Section4.D01.ForceClass
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Local-in-time smooth forcing for Proposition 2.1.

The local theory requires smooth Sobolev paths on compact time intervals,
without a global time-integrability condition. A scalar time cutoff embeds
each finite window in the existing density force class and leaves its force
unchanged on that window.
-/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01
open scoped ContDiff ENNReal

/-- Smooth forcing into every integer Sobolev order on the future half-line.
No `L¹` or `L²` condition on the whole time half-line is imposed. -/
def SmoothForceR (f : VelocityField) : Prop :=
  ContDiffOn ℝ ∞ f futureDomain ∧
    ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      IsSobolevPath (m : ℝ) f G ∧ ContDiffOn ℝ ∞ G futureTimes

theorem smoothForceR_of_memForceR {f : VelocityField} (hf : MemForceR f) :
    SmoothForceR f :=
  ⟨hf.1, fun m => by
    obtain ⟨G, hp, hc, _, _⟩ := hf.2 m
    exact ⟨G, hp, hc⟩⟩

/-- A smooth cutoff equal to one throughout a prescribed finite future window. -/
def localTimeCutoff (S : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := |S| + 1
  rOut := |S| + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem localTimeCutoff_eq_one {S t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    localTimeCutoff S t = 1 := by
  apply (localTimeCutoff S).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  change t ≤ |S| + 1
  linarith [le_abs_self S, ht.2]

/-- Real scalar multiplication commutes with the distributional realization. -/
theorem isSobolevDatum_smul_local {s : ℝ} {v : Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s v A) (c : ℝ) :
    IsSobolevDatum s (fun x => c • v x) (c • A) := by
  intro i ψ
  have hc : (((c • A) i : RealSobolevHilbert s) : FourierData) =
      c • (A i : FourierData) := rfl
  rw [hc, ContinuousLinearMap.map_smul_of_tower]
  change c • angularRealization s (A i : FourierData) ψ = _
  rw [hA i ψ, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [PiLp.smul_apply, Complex.real_smul, mul_left_comm]

/-- A cutoff times a path continuous on the future half-line is integrable
at every exponent there. The negative-time extension is used only for this
integrability proof and does not alter the smooth future path. -/
theorem memLp_localTimeCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ → E} (hG : ContinuousOn G (Ici (0 : ℝ))) (S : ℝ) (q : ℝ≥0∞) :
    MemLp (fun t => localTimeCutoff S t • G t) q forceTimeMeasure := by
  let H : ℝ → E := fun t => localTimeCutoff S t • G (max t 0)
  have hc : Continuous H :=
    ((localTimeCutoff S).contDiff (n := ⊤)).continuous.smul
      (hG.comp_continuous (continuous_id.max continuous_const) (fun t => le_max_right t 0))
  have hk : HasCompactSupport H := by
    apply HasCompactSupport.of_support_subset_isCompact (localTimeCutoff S).hasCompactSupport
    intro t ht
    exact subset_tsupport _ (fun hz => ht (by simp only [H, hz, zero_smul]))
  have hm : MemLp H q forceTimeMeasure := hc.memLp_of_hasCompactSupport hk
  apply (memLp_congr_ae ?_).mp hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  simp only [H, max_eq_left ht0.le]

/-- Every finite window of a locally smooth force agrees with a force in the
registered globally integrable class, with no condition near time zero. -/
theorem exists_memForceR_eqOn {f : VelocityField} (hf : SmoothForceR f) (S : ℝ) :
    ∃ g : VelocityField, MemForceR g ∧
      ∀ t ∈ Icc (0 : ℝ) S, ∀ x : Space, g (t, x) = f (t, x) := by
  let g : VelocityField := fun z => localTimeCutoff S z.1 • f z
  refine ⟨g, ⟨?_, ?_⟩, ?_⟩
  · exact ((localTimeCutoff S).contDiff.comp contDiff_fst).contDiffOn.smul hf.1
  · intro m
    obtain ⟨G, hp, hc⟩ := hf.2 m
    refine ⟨fun t => localTimeCutoff S t • G t, ?_,
      (localTimeCutoff S).contDiff.contDiffOn.smul hc,
      memLp_localTimeCutoff hc.continuousOn S 1,
      memLp_localTimeCutoff hc.continuousOn S 2⟩
    intro t ht
    exact isSobolevDatum_smul_local (hp t ht) _
  · intro t ht x
    simp only [g, localTimeCutoff_eq_one ht, one_smul]

end NSFormalization.Section4.A01
