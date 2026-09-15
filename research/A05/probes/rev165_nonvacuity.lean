import NSFormalization.Section4.A05.CriticalL3
import NSFormalization.Section4.D01.OrderZeroSymbol

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Homogeneous
open scoped ContDiff ENNReal

namespace Review165

/-- Local transcription of lane 164's canonical definition, used only to test
that lane 165's temporary A05 definition has an `rfl` bridge. -/
def canonicalDotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ

example :
    NSFormalization.Section4.A05.dotHomogeneousENorm =
      canonicalDotHomogeneousENorm := rfl

local notation "zB" =>
  (fun x : Space => (Cut.bump x) • (coordinateVector 0 : Space))

theorem bumpField_smooth : ContDiff ℝ ∞ zB :=
  Cut.bump_smooth.smul contDiff_const

theorem bumpField_compact : HasCompactSupport zB := by
  exact Cut.bump_cs.comp_left
    (g := fun c : ℝ => c • (coordinateVector 0 : Space)) (by simp)

theorem bumpField_ne_zero : zB ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Space)
  have hb : Cut.bump (0 : Space) = 1 := Cut.bump_one (by simp)
  have hc := congrArg (fun v : Space => v 0) h0
  simp [hb, coordinateVector] at hc

theorem bumpField_has_half_datum :
    ∃ G : RealVectorSobolev (1 / 2 : ℝ),
      IsHomogeneousSliceDatum (1 / 2 : ℝ) zB G :=
  (isHomogeneousSliceDatum_compact (s := (1 / 2 : ℝ))
    (by norm_num) bumpField_smooth bumpField_compact).1

theorem bumpField_dotHomogeneousENorm_ne_top :
    NSFormalization.Section4.A05.dotHomogeneousENorm (1 / 2) zB ≠ ⊤ := by
  obtain ⟨G, hG⟩ := bumpField_has_half_datum
  rw [NSFormalization.Section4.A05.u1_dotHomogeneousENorm_eq hG, ← ofReal_norm]
  exact ENNReal.ofReal_ne_top

theorem bumpField_eLpNorm_three_ne_top : eLpNorm zB 3 volume ≠ ⊤ := by
  exact (bumpField_smooth.continuous.memLp_of_hasCompactSupport
    bumpField_compact).eLpNorm_ne_top

/-- The finite smallness threshold used downstream rules out the empty-datum
branch of lane 165's totalized norm. -/
theorem half_datum_exists_of_smallness {z : SpatialField} {forceNorm : ℝ≥0∞} {r : ℝ}
    (hsmall : NSFormalization.Section4.A05.dotHomogeneousENorm (1 / 2) z + forceNorm <
      ENNReal.ofReal r) :
    ∃ G : RealVectorSobolev (1 / 2 : ℝ),
      IsHomogeneousSliceDatum (1 / 2 : ℝ) z G := by
  by_contra hdatum
  have hempty : IsEmpty {G : RealVectorSobolev (1 / 2 : ℝ) //
      IsHomogeneousSliceDatum (1 / 2 : ℝ) z G} :=
    ⟨fun G => hdatum ⟨G.1, G.2⟩⟩
  rw [NSFormalization.Section4.A05.dotHomogeneousENorm,
    iInf_of_isEmpty, sInf_empty] at hsmall
  simp at hsmall

example :
    zB ≠ 0 ∧
      (∃ G : RealVectorSobolev (1 / 2 : ℝ),
        IsHomogeneousSliceDatum (1 / 2 : ℝ) zB G) ∧
      NSFormalization.Section4.A05.dotHomogeneousENorm (1 / 2) zB ≠ ⊤ ∧
      eLpNorm zB 3 volume ≠ ⊤ :=
  ⟨bumpField_ne_zero, bumpField_has_half_datum,
    bumpField_dotHomogeneousENorm_ne_top, bumpField_eLpNorm_three_ne_top⟩

end Review165
