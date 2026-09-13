import Euler.CompactSmoothTimeField
import Euler.LpSmoothFieldAlgebra
import Euler.MeanCutoffDifferenceBound

/-!
# Continuous physical L2 jets of compact spatial perturbations

Joint smoothness on a compact time set and one common compact spatial support
produce genuine square-integrable spatial derivatives, continuous in time at
every order. No extension beyond the time set is assumed. These are physical
Fréchet jets; no identification with a Fourier Sobolev tower is asserted.
-/
noncomputable section
open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
open scoped ContDiff Topology BoundedContinuousFunction ENNReal

namespace NSFormalization.Source.CompactSlabSobolev

private local instance (n : ℕ) : NormedAddCommGroup (Space [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] Space)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] Space)) := inferInstance

variable {s : Set ℝ} [CompactSpace s]
    {w : ℝ × Space → Space} (hw : ContDiffOn ℝ ∞ w (s ×ˢ univ))
    {L : Set Space} (hL : IsCompact L)
    (hsupp : ∀ t ∈ s, tsupport (fun x => w (t, x)) ⊆ L)

/-- A literal slice with genuine L2 integrability at every derivative order. -/
def compactSlice (t : s) : SmoothL2Field Space where
  field x := w (t, x)
  smooth := (SmoothTimeField.ofContDiffOnCompactSupport s w hw L hL hsupp).smooth t
  integrable n := by
    have hsm := (SmoothTimeField.ofContDiffOnCompactSupport s w hw L hL hsupp).smooth t
    exact (hsm.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
      (hL.of_isClosed_subset (isClosed_tsupport _)
        ((tsupport_iteratedFDeriv_subset n).trans (hsupp t t.property)))

@[simp] theorem compactSlice_field (t : s) (x : Space) :
    (compactSlice hw hL hsupp t).field x = w (t, x) := rfl

/-- The actual L2 jet distance is controlled by its uniform spatial distance
and the square root of the volume of the common support. -/
theorem norm_jetLp_sub_le (n : ℕ) (t r : s) :
    ‖(compactSlice hw hL hsupp t).jetLp n - (compactSlice hw hL hsupp r).jetLp n‖ ≤
      ‖(SmoothTimeField.ofContDiffOnCompactSupport s w hw L hL hsupp).jet n t -
        (SmoothTimeField.ofContDiffOnCompactSupport s w hw L hL hsupp).jet n r‖ *
      (volume L).toReal ^ (1 / (2 : ℝ)) := by
  let A := SmoothTimeField.ofContDiffOnCompactSupport s w hw L hL hsupp
  let ft := iteratedFDeriv ℝ n (fun x => w (t, x))
  let fr := iteratedFDeriv ℝ n (fun x => w (r, x))
  have ht : MemLp ft 2 volume := (compactSlice hw hL hsupp t).integrable n
  have hr : MemLp fr 2 volume := (compactSlice hw hL hsupp r).integrable n
  have hz (q : s) (x : Space) (hx : x ∉ L) :
      iteratedFDeriv ℝ n (fun y => w (q, y)) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh =>
      hx ((tsupport_iteratedFDeriv_subset n).trans (hsupp q q.property) hh))
  have hb (x : Space) : ‖(ft - fr) x‖ ≤ ‖A.jet n t - A.jet n r‖ :=
    (A.jet n t - A.jet n r).norm_coe_le_norm x
  have H := EulerMeanBoundary.lpNorm_le_bound_volume (ft - fr)
    (ht.sub hr).aestronglyMeasurable L hL.measure_ne_top
    ‖A.jet n t - A.jet n r‖ (norm_nonneg _) hb
    (fun x hx => by simp only [Pi.sub_apply, ft, fr, hz t x hx, hz r x hx, sub_self]) 2
  change ‖ht.toLp ft - hr.toLp fr‖ ≤ _
  rw [← MemLp.toLp_sub, Lp.norm_toLp,
    toReal_eLpNorm (ht.sub hr).aestronglyMeasurable]
  simpa using H

/-- Every actual spatial L2 jet varies continuously, including time endpoints. -/
theorem continuous_compactSlice_jetLp (n : ℕ) :
    Continuous (fun t : s => (compactSlice hw hL hsupp t).jetLp n) := by
  let A := SmoothTimeField.ofContDiffOnCompactSupport s w hw L hL hsupp
  rw [continuous_iff_continuousAt]
  intro r
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun t => norm_nonneg _)
    (fun t => norm_jetLp_sub_le hw hL hsupp n t r)
  have H : Continuous (fun t : s => ‖A.jet n t - A.jet n r‖ *
      (volume L).toReal ^ (1 / (2 : ℝ))) :=
    ((A.jet n).continuous.sub continuous_const).norm.mul continuous_const
  simpa using H.continuousAt.tendsto (x := r)

/-- Adding the compact perturbation to an actual reference L2 jet path. -/
def addReference (U : s → SmoothL2Field Space) (t : s) : SmoothL2Field Space :=
  (U t).addField (compactSlice hw hL hsupp t)

@[simp] theorem addReference_field (U : s → SmoothL2Field Space) (t : s) (x : Space) :
    (addReference hw hL hsupp U t).field x = (U t).field x + w (t, x) := rfl

theorem continuous_addReference_jetLp (U : s → SmoothL2Field Space)
    (hU : ∀ n, Continuous (fun t => (U t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (addReference hw hL hsupp U t).jetLp n) :=
  SmoothL2Field.continuous_jetLp_addField U (compactSlice hw hL hsupp) hU
    (continuous_compactSlice_jetLp hw hL hsupp) n

include hw hL hsupp in
/-- A reference realization and a compact difference realize the inserted
physical field, with all of its actual spatial L2 jets continuous in time. -/
theorem exists_inserted_path {v V : ℝ × Space → Space}
    (U : s → SmoothL2Field Space) (hU : ∀ n, Continuous (fun t => (U t).jetLp n))
    (hv : ∀ t : s, ∀ x, (U t).field x = v (t, x))
    (hwV : ∀ t : s, ∀ x, w (t, x) = V (t, x) - v (t, x)) :
    ∃ W : s → SmoothL2Field Space,
      (∀ t : s, ∀ x, (W t).field x = V (t, x)) ∧
      ∀ n, Continuous (fun t => (W t).jetLp n) := by
  refine ⟨addReference hw hL hsupp U, ?_, continuous_addReference_jetLp hw hL hsupp U hU⟩
  intro t x
  simp only [addReference_field, hv, hwV]
  abel

end NSFormalization.Source.CompactSlabSobolev
