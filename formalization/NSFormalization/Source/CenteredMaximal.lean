import NSFormalization.Source.MaximalBallWeak
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Instances.Real.Lemmas

/-! # The centered maximal operator over positive rational radii -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NSFormalization.CenteredMaximal
abbrev Space := NSFormalization.MaximalBallWeak.Space
abbrev PositiveRadius := {q : ℚ // 0 < q}

/-- Actual nonnegative mass of an open ball. -/
def ballMass (H : Space → ℝ≥0∞) (r : ℝ) (x : Space) : ℝ≥0∞ :=
  ∫⁻ y in Metric.ball x r, H y

/-- The ball volume depends only on its radius. -/
def ballVolume (r : ℝ) : ℝ≥0∞ := volume (Metric.ball (0 : Space) r)

theorem ballVolume_eq (r : ℝ) (x : Space) : ballVolume r = volume (Metric.ball x r) := by
  simp [ballVolume, EuclideanSpace.volume_ball_fin_three]

theorem ballVolume_pos {r : ℝ} (hr : 0 < r) : 0 < ballVolume r := by
  simp only [ballVolume, EuclideanSpace.volume_ball_fin_three]
  positivity

theorem ballVolume_ne_top (r : ℝ) : ballVolume r ≠ ⊤ := by
  exact measure_ball_lt_top.ne

/-- Actual centered ball average, with ENNReal division. -/
def ballAverage (H : Space → ℝ≥0∞) (r : ℝ) (x : Space) : ℝ≥0∞ :=
  ballMass H r x / ballVolume r

/-- A countable centered supremum; no uncountable measurability claim is used. -/
def centeredMaximal (H : Space → ℝ≥0∞) (x : Space) : ℝ≥0∞ :=
  ⨆ q : PositiveRadius, ballAverage H (q : ℚ) x

theorem measurable_ballMass {H : Space → ℝ≥0∞} (hH : Measurable H) (r : ℝ) :
    Measurable (ballMass H r) := by
  have hf : Measurable (fun p : Space × Space =>
      {p : Space × Space | dist p.2 p.1 < r}.indicator (fun p => H p.2) p) :=
    (hH.comp measurable_snd).indicator
      (measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const)
  have he : ballMass H r = fun x => ∫⁻ y,
      {p : Space × Space | dist p.2 p.1 < r}.indicator (fun p => H p.2) (x,y) := by
    funext x
    rw [ballMass, ← lintegral_indicator measurableSet_ball]
    apply lintegral_congr
    intro y
    by_cases hy : dist y x < r <;> simp [hy, Metric.mem_ball]
  rw [he]
  exact hf.lintegral_prod_right

theorem measurable_ballAverage {H : Space → ℝ≥0∞} (hH : Measurable H) (r : ℝ) :
    Measurable (ballAverage H r) := (measurable_ballMass hH r).div_const _

theorem measurable_centeredMaximal {H : Space → ℝ≥0∞} (hH : Measurable H) :
    Measurable (centeredMaximal H) :=
  Measurable.iSup (fun q : PositiveRadius => measurable_ballAverage hH (q : ℚ))

/-- Every positive rational ball mass is controlled by the actual maximal value. -/
theorem rational_ballMass_le (H : Space → ℝ≥0∞) (q : PositiveRadius) (x : Space) :
    ballMass H (q : ℚ) x ≤ centeredMaximal H x * ballVolume (q : ℚ) := by
  have hq : (0 : ℝ) < (q : ℚ) := by exact_mod_cast q.property
  exact (ENNReal.div_le_iff (ballVolume_pos hq).ne' (ballVolume_ne_top _)).mp
    (le_iSup (fun q : PositiveRadius => ballAverage H (q : ℚ) x) q)

/-- Points admitting a strict positive-rational witness with radius at most N. -/
def boundedLevel (H : Space → ℝ≥0∞) (ℓ : ℝ) (N : ℕ) : Set Space :=
  {x | ∃ q : PositiveRadius, (q : ℚ) ≤ (N : ℝ) ∧ ENNReal.ofReal ℓ < ballAverage H (q : ℚ) x}

/-- The bounded-radius weak theorem applied to genuine strict average witnesses. -/
theorem boundedLevel_weak (H : Space → ℝ≥0∞) (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) :
    ENNReal.ofReal ℓ * volume (boundedLevel H ℓ N) ≤ 64 * ∫⁻ y, H y := by
  classical
  let s := boundedLevel H ℓ N
  have hw : ∀ x : s, ∃ q : PositiveRadius,
      (q : ℚ) ≤ (N : ℝ) ∧ ENNReal.ofReal ℓ < ballAverage H (q : ℚ) x := fun x => x.property
  choose q hq using hw
  let r : Space → ℝ := fun x => if hx : x ∈ s then (q ⟨x,hx⟩ : ℚ) else 1
  apply NSFormalization.MaximalBallWeak.boundedRadius_weak H s r N ℓ hℓ
  · intro x hx
    simp only [r, dite_eq_left hx]
    exact ⟨by exact_mod_cast (q ⟨x,hx⟩).property, (hq ⟨x,hx⟩).1⟩
  · intro x hx
    simp only [r, dite_eq_left hx]
    have hv : 0 < ballVolume ((q ⟨x,hx⟩ : PositiveRadius) : ℚ) :=
      ballVolume_pos (by exact_mod_cast (q ⟨x,hx⟩).property)
    rw [← ballVolume_eq]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hv.ne') (Or.inl (ballVolume_ne_top _))).mp (hq ⟨x,hx⟩).2.le

/-- The positive-rational centered operator satisfies the full weak estimate. -/
theorem centeredMaximal_weak (H : Space → ℝ≥0∞) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ENNReal.ofReal ℓ * volume {x | ENNReal.ofReal ℓ < centeredMaximal H x} ≤
      64 * ∫⁻ y, H y := by
  have hs : {x | ENNReal.ofReal ℓ < centeredMaximal H x} = ⋃ N : ℕ, boundedLevel H ℓ N := by
    ext x
    simp only [mem_ofPred_eq, centeredMaximal, lt_iSup_iff, mem_iUnion, boundedLevel]
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨N, hN⟩ := exists_nat_ge ((q : ℚ) : ℝ)
      exact ⟨N, q, hN, hq⟩
    · rintro ⟨N, q, _, hq⟩
      exact ⟨q, hq⟩
  have hm : Monotone (boundedLevel H ℓ) := by
    intro N K hNK x hx
    obtain ⟨q, hq, hx⟩ := hx
    exact ⟨q, hq.trans (by exact_mod_cast hNK), hx⟩
  rw [hs, hm.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le (fun N => boundedLevel_weak H ℓ hℓ N)

/-- Ball-volume continuity is explicit and independent of the density. -/
theorem continuous_ballVolume : Continuous ballVolume := by
  have he : ballVolume = fun r : ℝ => ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
    funext r
    exact EuclideanSpace.volume_ball_fin_three _ r
  rw [he]
  exact (ENNReal.continuous_mul_const ENNReal.ofReal_ne_top).comp
    ((ENNReal.continuous_pow 3).comp ENNReal.continuous_ofReal)

/-- Rational radii control every positive real radius, without continuity of mass. -/
theorem ballMass_le (H : Space → ℝ≥0∞) {r : ℝ} (hr : 0 < r) (x : Space) :
    ballMass H r x ≤ centeredMaximal H x * ballVolume r := by
  by_cases htop : centeredMaximal H x = ⊤
  · rw [htop, ENNReal.top_mul (ballVolume_pos hr).ne']
    exact le_top
  obtain ⟨q, _, hqr, hqt⟩ := Real.exists_seq_rat_strictAnti_tendsto r
  have hc : Continuous (fun t : ℝ => centeredMaximal H x * ballVolume t) :=
    (ENNReal.continuous_const_mul htop).comp continuous_ballVolume
  apply ge_of_tendsto' (hc.continuousAt.tendsto.comp hqt)
  intro n
  have hq : 0 < q n := by exact_mod_cast (hr.trans (hqr n))
  calc
    ballMass H r x ≤ ballMass H (q n) x :=
      lintegral_mono_set (Metric.ball_subset_ball (hqr n).le)
    _ ≤ _ := rational_ballMass_le H ⟨q n, hq⟩ x

/-- Every actual positive-radius average is bounded by the rational supremum. -/
theorem ballAverage_le (H : Space → ℝ≥0∞) {r : ℝ} (hr : 0 < r) (x : Space) :
    ballAverage H r x ≤ centeredMaximal H x :=
  (ENNReal.div_le_iff (ballVolume_pos hr).ne' (ballVolume_ne_top r)).mpr (ballMass_le H hr x)

/-- Equality with the all-positive-real-radius supremum, proved after measurability. -/
theorem centeredMaximal_eq_realSup (H : Space → ℝ≥0∞) (x : Space) :
    centeredMaximal H x = ⨆ r : {r : ℝ // 0 < r}, ballAverage H r x := by
  apply le_antisymm
  · apply iSup_le
    intro q
    exact le_iSup_of_le ⟨(q : ℚ), by exact_mod_cast q.property⟩ le_rfl
  · exact iSup_le (fun r => ballAverage_le H r.property x)

end NSFormalization.CenteredMaximal
