import NSFormalization.Paper3.PositivePhysicalDensity
import NSFormalization.Source.RealSobolev

/-! Positive-time physical density in the real Sobolev Hilbert subspace.
The already proved complex approximation is projected using the source real-part
projection, so no spatial or temporal approximation is repeated. -/
noncomputable section
set_option maxHeartbeats 8000000
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source.RealSobolev
open scoped ContDiff ENNReal

instance realSobolevNormedAddCommGroup (s : ℝ) : NormedAddCommGroup (RealSobolevHilbert s) :=
  inferInstanceAs (NormedAddCommGroup (realSubspace s).toSubmodule)

instance realSobolevNormedSpace (s : ℝ) : NormedSpace ℝ (RealSobolevHilbert s) :=
  inferInstanceAs (NormedSpace ℝ (realSubspace s).toSubmodule)

/-- The existing real-part projection with its actual closed-subspace codomain. -/
def realProjectionTo (s : ℝ) : SobolevHilbert s →L[ℝ] RealSobolevHilbert s :=
  realProjection.codRestrict (realSubspace s).toSubmodule (realProjection_mem s)

def realSobolevInclusion (s : ℝ) : RealSobolevHilbert s →L[ℝ] SobolevHilbert s :=
  (realSubspace s).toSubmodule.subtypeL

 theorem realProjectionTo_inclusion (s : ℝ) (h : RealSobolevHilbert s) :
    realProjectionTo s (realSobolevInclusion s h) = h :=
  Subtype.ext (realProjection_eq_self h.property)

 theorem realProjectionTo_norm_le (s : ℝ) (h : SobolevHilbert s) :
    ‖realProjectionTo s h‖ ≤ ‖h‖ := realProjection_norm_le h

 theorem realProjectionTo_opNorm_le (s : ℝ) : ‖realProjectionTo s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  simpa only [one_mul] using realProjectionTo_norm_le s h

 theorem compactSobolevTimeSlice_realPart (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    realProjection (compactSobolevTimeSlice s F hF hc t) =
      compactSobolevTimeSlice s (fun z => ((F z).re : ℂ))
        (Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hF))
        (by
          show HasCompactSupport ((fun z : ℂ => (z.re : ℂ)) ∘ F)
          exact hc.comp_left (by simp)) t := by
  change realProjection (weightedFourierLp s _) = weightedFourierLp s _
  rw [← weightedFourierLp_realPart]
  congr 1
  ext x
  exact realPartSchwartz_apply _ x

/-- The original real compact physical function as an actual real Sobolev vector. -/
def realCompactSobolevTimeSlice (s : ℝ) (F : ℝ × Space → ℝ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) : RealSobolevHilbert s :=
  realProjectionTo s (compactSobolevTimeSlice s (fun z => (F z : ℂ))
    (by convert Complex.ofRealCLM.contDiff.comp hF using 1 <;> rfl)
      (by
        show HasCompactSupport ((fun z : ℝ => (z : ℂ)) ∘ F)
        exact hc.comp_left (by simp)) t)

 theorem coe_realCompactSobolevTimeSlice (s : ℝ) {F : ℝ × Space → ℝ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    (realCompactSobolevTimeSlice s F hF hc t : SobolevHilbert s) =
      compactSobolevTimeSlice s (fun z => (F z : ℂ))
        (by convert Complex.ofRealCLM.contDiff.comp hF using 1 <;> rfl)
          (by
            show HasCompactSupport ((fun z : ℝ => (z : ℂ)) ∘ F)
            exact hc.comp_left (by simp)) t := by
  change realProjection (compactSobolevTimeSlice s _ _ _ t) = _
  rw [compactSobolevTimeSlice_realPart]
  rfl

 theorem project_compactSobolevTimeSlice (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    realProjectionTo s (compactSobolevTimeSlice s F hF hc t) =
      realCompactSobolevTimeSlice s (fun z => (F z).re)
        (by convert Complex.reCLM.contDiff.comp hF using 1 <;> rfl)
          (by
            show HasCompactSupport ((fun z : ℂ => z.re) ∘ F)
            exact hc.comp_left (by simp)) t := by
  apply Subtype.ext
  rw [coe_realCompactSobolevTimeSlice]
  exact compactSobolevTimeSlice_realPart s hF hc t

 theorem memLp_realCompactSobolevTimeSlice (s : ℝ) {F : ℝ × Space → ℝ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) :
    MemLp (realCompactSobolevTimeSlice s F hF hc) q positiveTimeMeasure :=
  (realProjectionTo s).comp_memLp' ((memLp_compactSobolevTimeSlice s
    (by convert Complex.ofRealCLM.contDiff.comp hF using 1 <;> rfl)
      (by
        show HasCompactSupport ((fun z : ℝ => (z : ℂ)) ∘ F)
        exact hc.comp_left (by simp)) q).restrict (Ioi 0))

 theorem realProjectionTo_compLp_inclusion (s : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : Lp (RealSobolevHilbert s) q positiveTimeMeasure) :
    (realProjectionTo s).compLpL q positiveTimeMeasure
      ((realSobolevInclusion s).compLpL q positiveTimeMeasure f) = f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (realProjectionTo s)
    ((realSobolevInclusion s).compLpL q positiveTimeMeasure f),
    ContinuousLinearMap.coeFn_compLpL (realSobolevInclusion s) f] with t ht hinc
  rw [ht, hinc, realProjectionTo_inclusion]

/-- Original real physical C∞ functions, compactly supported strictly inside
positive time, approximate every real Sobolev-valued Bochner datum. -/
theorem exists_real_positive_physical_compact_smooth_approx (s : ℝ) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (hq : q ≠ ⊤) (f : Lp (RealSobolevHilbert s) q positiveTimeMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : ℝ × Space → ℝ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F),
      tsupport F ⊆ {z | 0 < z.1} ∧
      ‖f - (memLp_realCompactSobolevTimeSlice s hF hc q).toLp
        (realCompactSobolevTimeSlice s F hF hc)‖ < ε := by
  let P := (realProjectionTo s).compLpL q positiveTimeMeasure
  let v := (realSobolevInclusion s).compLpL q positiveTimeMeasure f
  obtain ⟨F, hF, hc, hFs, herr⟩ := exists_positive_physical_compact_smooth_approx s q hq v hε
  let R : ℝ × Space → ℝ := fun z => (F z).re
  have hR : ContDiff ℝ ∞ R := Complex.reCLM.contDiff.comp hF
  have hRc : HasCompactSupport R := by
    show HasCompactSupport ((fun z : ℂ => z.re) ∘ F)
    exact hc.comp_left (by simp)
  have hRs : tsupport R ⊆ tsupport F :=
    tsupport_comp_subset (by exact Complex.reCLM.map_zero) F
  refine ⟨R, hR, hRc, hRs.trans hFs, ?_⟩
  let G := ((memLp_compactSobolevTimeSlice s hF hc q).restrict (s := Ioi 0)).toLp
    (compactSobolevTimeSlice s F hF hc)
  have hPG : P G = (memLp_realCompactSobolevTimeSlice s hR hRc q).toLp
      (realCompactSobolevTimeSlice s R hR hRc) := by
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (realProjectionTo s) G,
      ((memLp_compactSobolevTimeSlice s hF hc q).restrict (s := Ioi 0)).coeFn_toLp,
      (memLp_realCompactSobolevTimeSlice s hR hRc q).coeFn_toLp] with t ht hG hreal
    rw [ht, hG, hreal]
    exact project_compactSobolevTimeSlice s hF hc t
  have hPv : P v = f := realProjectionTo_compLp_inclusion s q f
  have hn : ‖P‖ ≤ 1 := (ContinuousLinearMap.norm_compLpL_le _).trans (realProjectionTo_opNorm_le s)
  have hb : ‖P (v - G)‖ ≤ ‖v - G‖ := (P.le_opNorm _).trans (by nlinarith [norm_nonneg (v - G)])
  rw [map_sub, hPv, hPG] at hb
  exact hb.trans_lt herr

end NSFormalization.Paper3
