import NSFormalization.Section3.T21.Definitions
import NSFormalization.Section3.T18.ForceClass
import NSFormalization.Section3.T18.SobolevRate

/-!
# T21 N7: relative openness of the critical ball

The triangle inequality is the existing T18 supplier.  Its honest-path
hypotheses are discharged here for every smooth compact periodic force by
lowering a compactly supported integer-order coefficient path to the requested
real order.
-/

noncomputable section

namespace NSFormalization.Section3.T21

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open scoped ContDiff ENNReal

/-- The canonical force class is closed under negation. -/
theorem memForceT_neg {f : SpaceTimeField} (hf : MemForceT f) :
    MemForceT (-f) := by
  rcases hf with ⟨hfs, hfp, K, hK, hKpos, hfK⟩
  refine ⟨hfs.neg, ?_, K, hK, hKpos, ?_⟩
  · intro t ht x j
    simp only [Pi.neg_apply, hfp t ht x j]
  · simpa only [tsupport_neg] using hfK

/-- The canonical force class is closed under subtraction. -/
theorem memForceT_sub {f g : SpaceTimeField} (hf : MemForceT f)
    (hg : MemForceT g) : MemForceT (f - g) := by
  change MemForceT (fun z ↦ f z - g z)
  simpa only [sub_eq_add_neg, Pi.neg_apply] using
    NSFormalization.Section3.T18.memForceT_add hf (memForceT_neg hg)

/-- Every canonical test force has an honest Sobolev path at every real order
and every time exponent. -/
theorem memForceSobolevT_of_memForceT (q : ℝ≥0∞) (s : ℝ)
    {f : SpaceTimeField} (hf : MemForceT f) : MemForceSobolevT q s f := by
  obtain ⟨G, _hdatum, _hcont, _hcompact, _hstrong, hpath, hLp⟩ :=
    force_coefficient_path hf ⌈s⌉₊
  exact NSFormalization.Section3.T18.memForceSobolevT_mono_order
    (Nat.le_ceil s) ⟨G, hpath, hLp q⟩

/-- N7: every point of a critical ball is interior relative to the force
class in the `L¹_t H^s_x` pseudometric. -/
theorem ballRelativelyOpen (c : ℝ) : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    ∀ g ∈ criticalBallT c ν s,
      ∃ r : ℝ≥0∞, 0 < r ∧
        ∀ f ∈ forceClassT, forceSobolevENormT 1 s (f - g) < r →
          f ∈ criticalBallT c ν s := by
  intro ν _hν s g hg
  let R : ℝ≥0∞ := ENNReal.ofReal (c * ν)
  let n : ℝ≥0∞ := forceSobolevENormT 1 s g
  have hgn : n < R := hg.2
  refine ⟨R - n, tsub_pos_iff_lt.mpr hgn, ?_⟩
  intro f hf hdist
  refine ⟨hf, ?_⟩
  have hdiff : MemForceSobolevT 1 s (f - g) :=
    memForceSobolevT_of_memForceT 1 s (memForceT_sub hf hg.1)
  have hgpath : MemForceSobolevT 1 s g :=
    memForceSobolevT_of_memForceT 1 s hg.1
  have htriangle := NSFormalization.Section3.T18.forceSobolevENormT_add_le
    (q := (1 : ℝ≥0∞)) (s := s) (by norm_num) hdiff hgpath
  have hsum : (fun z ↦ (f - g) z + g z) = f := by
    funext z
    simp
  rw [hsum] at htriangle
  have hn_top : n ≠ ⊤ := ne_of_lt (hgn.trans_le le_top)
  have hadd : forceSobolevENormT 1 s (f - g) + n < (R - n) + n :=
    ENNReal.add_lt_add_right hn_top hdist
  exact htriangle.trans_lt (hadd.trans_eq (tsub_add_cancel_of_le hgn.le))

end NSFormalization.Section3.T21
