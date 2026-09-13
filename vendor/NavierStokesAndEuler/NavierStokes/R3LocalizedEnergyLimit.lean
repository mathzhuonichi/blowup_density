import NavierStokes.ComparatorR3Bridge
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Closing a localized whole-space comparison estimate

The localized differential inequality is an
explicit hypothesis here. This file does not assert that arbitrary smooth
finite-energy Navier--Stokes solutions satisfy that inequality: obtaining it
requires the manuscript's pressure recovery and commutator estimates.

The proof uses interior derivatives, an integrating factor, and dominated
convergence over Euclidean space. Neither periodicity nor compact support of
the comparison velocity is assumed.
-/

noncomputable section

namespace NavierStokes.R3LocalizedEnergyLimit

open Set Filter MeasureTheory ProblemStatement
open scoped Topology

/-- An inhomogeneous Grönwall estimate requiring derivatives only at positive
interior times. This also covers `T = 0` and `K = 0`. -/
theorem gronwall_error {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hc : ContinuousOn E (Icc 0 T)) (hzero : E 0 = 0)
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hb : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, E t ≤ ε * t * Real.exp (K * t) := by
  let G : ℝ → ℝ := fun t => Real.exp (-K * t) * E t - ε * t
  let G' : ℝ → ℝ := fun t =>
    Real.exp (-K * t) * (E' t - K * E t) - ε
  have hGc : ContinuousOn G (Icc 0 T) :=
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hc).sub
      (continuous_const.mul continuous_id).continuousOn)
  have hGd (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt G (G' t) t := by
    convert! ((((hasDerivAt_id t).const_mul (-K)).exp.mul (hd t ht)).sub
      ((hasDerivAt_id t).const_mul ε)) using 1
    dsimp [G, G']
    ring
  have hGb (t : ℝ) (ht : t ∈ Ioo 0 T) : G' t ≤ 0 := by
    have hexp : Real.exp (-K * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    have hmul := mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos (-K * t)).le
    have hsmall := mul_le_mul_of_nonneg_right hexp hε
    dsimp [G']
    nlinarith
  have hmono : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hGc
    · intro t ht
      exact (hGd t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      exact hGb t (by simpa only [interior_Icc] using ht)
  intro t ht
  have hle := hmono ⟨le_rfl, hT⟩ ht ht.1
  have hweight : Real.exp (K * t) * Real.exp (-K * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hmul := mul_le_mul_of_nonneg_left hle (Real.exp_pos (K * t)).le
  dsimp [G] at hmul
  rw [hzero] at hmul
  rw [mul_sub, ← mul_assoc, hweight] at hmul
  nlinarith only [hmul]

/-- The actual weighted kinetic energy over all of `ℝ³`. -/
def localizedEnergy (χ : Space → ℝ) (w : Space → Space) : ℝ :=
  ∫ x : Space, χ x * ‖w x‖ ^ 2

theorem localizedEnergy_nonneg {χ : Space → ℝ} (hχ : ∀ x, 0 ≤ χ x)
    (w : Space → Space) : 0 ≤ localizedEnergy χ w :=
  integral_nonneg (fun x => mul_nonneg (hχ x) (sq_nonneg _))

/-- Exhausting cutoffs recover the global kinetic energy by dominated
convergence. The sole global integrability assumption is the squared speed. -/
theorem localizedEnergy_tendsto {χ : ℕ → Space → ℝ} {w : Space → Space}
    (hc : ∀ n, Continuous (χ n)) (hw : Continuous w)
    (hχ : ∀ n x, χ n x ∈ Icc (0 : ℝ) 1)
    (hexhaust : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hint : Integrable (fun x : Space => ‖w x‖ ^ 2)) :
    Tendsto (fun n => localizedEnergy (χ n) w) atTop (𝓝 (∫ x : Space, ‖w x‖ ^ 2)) := by
  apply tendsto_integral_of_dominated_convergence (fun x : Space => ‖w x‖ ^ 2)
  · intro n
    exact ((hc n).mul (hw.norm.pow 2)).aestronglyMeasurable
  · exact hint
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχ n x).1 (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (hχ n x).2
  · filter_upwards with x
    simpa using (hexhaust x).mul_const (‖w x‖ ^ 2)

/-- If the cutoff energies have a uniform `C / (n + 1)` bound, the entire
continuous velocity difference vanishes. -/
theorem eq_zero_of_localizedEnergy_le {χ : ℕ → Space → ℝ} {w : Space → Space}
    (hc : ∀ n, Continuous (χ n)) (hw : Continuous w)
    (hχ : ∀ n x, χ n x ∈ Icc (0 : ℝ) 1)
    (hexhaust : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hint : Integrable (fun x : Space => ‖w x‖ ^ 2))
    {C : ℝ} (hbound : ∀ n : ℕ, localizedEnergy (χ n) w ≤ C / (n + 1 : ℕ)) :
    ∀ x, w x = 0 := by
  have hlim := localizedEnergy_tendsto hc hw hχ hexhaust hint
  have hlimzero : Tendsto (fun n => localizedEnergy (χ n) w) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => localizedEnergy_nonneg (fun x => (hχ n x).1) w) hbound
    exact (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat C)
  have htotal : (∫ x : Space, ‖w x‖ ^ 2) = 0 := tendsto_nhds_unique hlim hlimzero
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖w x‖) hint).mp htotal
  have heq : (fun x : Space => ‖w x‖ ^ 2) = fun _ => 0 :=
    MeasureTheory.Measure.eq_of_ae_eq hae (hw.norm.pow 2) continuous_const
  intro x
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (congrFun heq x))

/-- The final comparison step of the manuscript, with the pressure-flux
estimate still exposed as the differential-inequality premise `hbound`. -/
theorem comparison_of_localized_differential_inequality
    {χ : ℕ → Space → ℝ} {w : VelocityField} {E' : ℕ → ℝ → ℝ} {T K C : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hχc : ∀ n, Continuous (χ n)) (hχ : ∀ n x, χ n x ∈ Icc (0 : ℝ) 1)
    (hexhaust : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hw : ∀ t ∈ Icc 0 T, Continuous (fun x : Space => w (t, x)))
    (hint : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => ‖w (t, x)‖ ^ 2))
    (hzero : ∀ x, w (0, x) = 0)
    (hcont : ∀ n, ContinuousOn (fun t => localizedEnergy (χ n) (fun x => w (t, x))) (Icc 0 T))
    (hderiv : ∀ n t, t ∈ Ioo 0 T →
      HasDerivAt (fun s => localizedEnergy (χ n) (fun x => w (s, x))) (E' n t) t)
    (hbound : ∀ n t, t ∈ Ioo 0 T →
      E' n t ≤ K * localizedEnergy (χ n) (fun x => w (t, x)) + C / (n + 1 : ℕ)) :
    ∀ t ∈ Icc 0 T, ∀ x, w (t, x) = 0 := by
  intro t ht
  apply eq_zero_of_localizedEnergy_le hχc (hw t ht) hχ hexhaust (hint t ht)
    (C := C * t * Real.exp (K * t))
  intro n
  have hε : 0 ≤ C / (n + 1 : ℕ) := by positivity
  have hEzero : localizedEnergy (χ n) (fun x => w (0, x)) = 0 := by
    simp [localizedEnergy, hzero]
  have hb := gronwall_error hT hK hε (hcont n) hEzero (hderiv n) (hbound n) t ht
  convert! hb using 1
  ring

end NavierStokes.R3LocalizedEnergyLimit
