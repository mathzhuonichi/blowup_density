import NSFormalization.Paper3.RealPositiveDensity
import NSFormalization.Source.FiniteHilbertBochner
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Real Euclidean-vector physical approximation in the cycles-frequency
Sobolev Hilbert model. Angular convention transport is a separate obligation. -/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source.RealSobolev
open NSFormalization.Source.FiniteHilbertBochner
open scoped ContDiff ENNReal

abbrev RealVectorSobolev (s : ℝ) := Product (Fin 3) (RealSobolevHilbert s)

/-- Assemble three scalar physical functions in the actual Euclidean space. -/
def physicalVector (F : Fin 3 → ℝ × Space → ℝ) : ℝ × Space → Space :=
  fun z => WithLp.toLp 2 (fun i => F i z)

@[simp] theorem physicalVector_apply (F : Fin 3 → ℝ × Space → ℝ)
    (z : ℝ × Space) (i : Fin 3) : physicalVector F z i = F i z := rfl

theorem physicalVector_smooth (F : Fin 3 → ℝ × Space → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) : ContDiff ℝ ∞ (physicalVector F) :=
  (contDiff_piLp 2).mpr hF

theorem physicalVector_support (F : Fin 3 → ℝ × Space → ℝ)
    (hc : ∀ i, HasCompactSupport (F i)) :
    tsupport (physicalVector F) ⊆ ⋃ i, tsupport (F i) := by
  apply closure_minimal
  · intro z hz
    by_contra hn
    have he : physicalVector F z = 0 := by
      ext i
      change F i z = 0
      exact image_eq_zero_of_notMem_tsupport (fun hi => hn (mem_iUnion.mpr ⟨i, hi⟩))
    exact hz he
  · exact isClosed_iUnion_of_finite (fun i => isClosed_tsupport (F i))

theorem physicalVector_compact (F : Fin 3 → ℝ × Space → ℝ)
    (hc : ∀ i, HasCompactSupport (F i)) : HasCompactSupport (physicalVector F) :=
  (isCompact_iUnion hc).of_isClosed_subset (isClosed_tsupport _) (physicalVector_support F hc)

/-- Actual Euclidean-product trajectory of the three real physical slices. -/
def realVectorSlice (s : ℝ) (F : Fin 3 → ℝ × Space → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hc : ∀ i, HasCompactSupport (F i)) :
    ℝ → RealVectorSobolev s :=
  fun t => WithLp.toLp 2 (fun i => realCompactSobolevTimeSlice s (F i) (hF i) (hc i) t)

theorem memLp_realVectorSlice (s : ℝ) (F : Fin 3 → ℝ × Space → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hc : ∀ i, HasCompactSupport (F i)) (q : ℝ≥0∞) :
    MemLp (realVectorSlice s F hF hc) q positiveTimeMeasure :=
  memLp_piLp_iff.mpr (fun i => memLp_realCompactSobolevTimeSlice s (hF i) (hc i) q)

theorem realVectorSlice_toLp (s : ℝ) (F : Fin 3 → ℝ × Space → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hc : ∀ i, HasCompactSupport (F i))
    (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    (memLp_realVectorSlice s F hF hc q).toLp (realVectorSlice s F hF hc) =
      assemble q positiveTimeMeasure (fun i =>
        (memLp_realCompactSobolevTimeSlice s (hF i) (hc i) q).toLp
          (realCompactSobolevTimeSlice s (F i) (hF i) (hc i))) := by
  let b := (memLp_realVectorSlice s F hF hc q).toLp (realVectorSlice s F hF hc)
  have he (i : Fin 3) : coordinates q positiveTimeMeasure b i =
      (memLp_realCompactSobolevTimeSlice s (hF i) (hc i) q).toLp
        (realCompactSobolevTimeSlice s (F i) (hF i) (hc i)) := by
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (coord i) b,
      (memLp_realVectorSlice s F hF hc q).coeFn_toLp,
      (memLp_realCompactSobolevTimeSlice s (hF i) (hc i) q).coeFn_toLp]
      with t ht hb hi
    exact ht.trans ((congrArg (coord i) hb).trans hi.symm)
  change b = _
  rw [← assemble_coordinates q positiveTimeMeasure b]
  congr 1

/-- Three concrete scalar approximations yield one jointly smooth, compactly
supported Euclidean physical force. The displayed trajectory is exactly its
coordinatewise Sobolev realization. -/
theorem exists_real_vector_positive_physical_approx (s : ℝ) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    (b : Lp (RealVectorSobolev s) q positiveTimeMeasure) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : ℝ × Space → Space), ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ {z | 0 < z.1} ∧
      ∃ (f : Fin 3 → ℝ × Space → ℝ)
        (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hc : ∀ i, HasCompactSupport (f i)),
        (∀ z i, F z i = f i z) ∧
        ‖b - (memLp_realVectorSlice s f hf hc q).toLp (realVectorSlice s f hf hc)‖ < ε := by
  have hex (i : Fin 3) := exists_real_positive_physical_compact_smooth_approx s q hq
    (coordinates q positiveTimeMeasure b i) (show 0 < ε / 3 by positivity)
  choose f hf hc hs he using hex
  refine ⟨physicalVector f, physicalVector_smooth f hf, physicalVector_compact f hc, ?_,
    f, hf, hc, fun _ _ => rfl, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (physicalVector_support f hc hz)
    exact hs i hi
  · rw [realVectorSlice_toLp]
    apply (approximation_bound q positiveTimeMeasure b _).trans_lt
    calc
      _ < ∑ i : Fin 3, ε / 3 := Finset.sum_lt_sum_of_nonempty (by simp) (fun i _ => he i)
      _ = ε := by simp; ring

end NSFormalization.Paper3
