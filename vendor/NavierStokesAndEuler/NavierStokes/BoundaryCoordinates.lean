import Mathlib.Analysis.Calculus.TangentCone.Prod
import NavierStokes.SimilarityCoordinates
import Mathlib.Data.Real.Sign
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Similarity coordinates at nonsingular boundary points

The parameter `a` is `2h`, so `axialExponent a = 1/2 - h`.
We extend the actual positive-time coordinate to `τ = 0`, away from `z = 0`.
The smooth continuation is obtained from the inverse function theorem for
`(q,z) ↦ (q - z² q^a,z)`; it is not assumed as input.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.BoundaryCoordinates

open SimilarityCoordinates

def axialExponent (a : ℝ) : ℝ := (1 - a) / 2

def boundaryQ (a z : ℝ) : ℝ := |z| ^ (axialExponent a)⁻¹

/-- Values at negative `τ` are merely a totalization. Smoothness is asserted
relative to `domain`; a separate theorem constructs an ambient continuation. -/
def extendedQ (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.1 then coordinateQ a p else boundaryQ a p.2

def extendedEta (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2 / extendedQ a p ^ axialExponent a

def halfPlane : Set (ℝ × ℝ) := Ici 0 ×ˢ univ

def domain : Set (ℝ × ℝ) := halfPlane ∩ {(0, 0)}ᶜ

def positiveDomain : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ

theorem axialExponent_pos {a : ℝ} (ha1 : a < 1) : 0 < axialExponent a :=
  div_pos (sub_pos.mpr ha1) (by norm_num)

theorem boundaryQ_pos {a z : ℝ} (hz : z ≠ 0) : 0 < boundaryQ a z :=
  Real.rpow_pos_of_pos (abs_pos.mpr hz) _

theorem boundaryQ_pow {a z : ℝ} (ha1 : a < 1) :
    boundaryQ a z ^ axialExponent a = |z| := by
  exact Real.rpow_inv_rpow (abs_nonneg z) (axialExponent_pos ha1).ne'

theorem boundaryQ_pow_two {a z : ℝ} (ha1 : a < 1) :
    boundaryQ a z ^ (1 - a) = z ^ 2 := by
  have he : 1 - a = axialExponent a * (2 : ℕ) := by dsimp [axialExponent]; ring
  have hq : 0 ≤ boundaryQ a z := Real.rpow_nonneg (abs_nonneg z) _
  rw [he, Real.rpow_mul_natCast hq,
    boundaryQ_pow ha1, sq_abs]

theorem boundaryQ_forward {a z : ℝ} (ha1 : a < 1) (hz : z ≠ 0) :
    forwardScalar a z (boundaryQ a z) = 0 := by
  rw [forwardScalar_factor (boundaryQ_pos hz), boundaryQ_pow_two ha1, sub_self, mul_zero]

/-- The inverse-function determinant at the boundary is exactly `1 - a`. -/
theorem boundaryQ_slope {a z : ℝ} (ha1 : a < 1) (hz : z ≠ 0) :
    scalarSlope a z (boundaryQ a z) = 1 - a := by
  have hq := boundaryQ_pos (a := a) hz
  have he := boundaryQ_forward ha1 hz
  have hprod : z ^ 2 * boundaryQ a z ^ a = boundaryQ a z := by
    dsimp [forwardScalar] at he
    linarith
  unfold scalarSlope
  rw [Real.rpow_sub_one hq.ne']
  calc
    1 - z ^ 2 * a * (boundaryQ a z ^ a / boundaryQ a z) =
        1 - a * ((z ^ 2 * boundaryQ a z ^ a) / boundaryQ a z) := by ring
    _ = 1 - a := by rw [hprod, div_self hq.ne', mul_one]

theorem positive_zero_solution_unique {a z q : ℝ} (ha1 : a < 1)
    (hz : z ≠ 0) (hq : 0 < q) (he : forwardScalar a z q = 0) :
    q = boundaryQ a z := by
  have hpow : q ^ (1 - a) = z ^ 2 := by
    rw [forwardScalar_factor hq] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left
      (Real.rpow_pos_of_pos hq a).ne')
  apply (Real.rpow_left_inj hq.le (boundaryQ_pos (a := a) hz).le
    (sub_pos.mpr ha1).ne').mp
  rw [hpow, boundaryQ_pow_two ha1]

@[simp] theorem extendedQ_boundary (a z : ℝ) :
    extendedQ a (0, z) = boundaryQ a z := by simp [extendedQ]

theorem extendedQ_positive {a : ℝ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    extendedQ a p = coordinateQ a p := ite_eq_left hp

theorem extendedEta_positive {a : ℝ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    extendedEta a p = coordinateEta a p := by
  rw [extendedEta, extendedQ_positive hp]
  rfl

theorem extendedEta_boundary {a z : ℝ} (ha1 : a < 1) :
    extendedEta a (0, z) = z / |z| := by
  rw [extendedEta, extendedQ_boundary, boundaryQ_pow ha1]

theorem extendedEta_boundary_sign {a z : ℝ} (ha1 : a < 1) :
    extendedEta a (0, z) = Real.sign z := by
  rw [extendedEta_boundary ha1]
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · rw [abs_of_neg hz, Real.sign_of_neg hz, div_neg, div_self hz.ne]
  · simp
  · rw [abs_of_pos hz, Real.sign_of_pos hz, div_self hz.ne']

theorem boundary_mem_domain {z : ℝ} (hz : z ≠ 0) : (0, z) ∈ domain := by
  exact ⟨⟨mem_Ici.mpr le_rfl, mem_univ z⟩, fun he => hz (congrArg Prod.snd he)⟩

theorem uniqueDiffOn_domain : UniqueDiffOn ℝ domain := by
  exact ((uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ).inter isClosed_singleton.isOpen_compl

/-- The inverse branch exists and is smooth on one open neighborhood crossing
the boundary. Its equality with the constructed coordinate on `τ ≥ 0` follows
from positive-root uniqueness, including the separately proved zero-time case. -/
theorem exists_smooth_boundary_q {a z : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hz : z ≠ 0) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, z) ∈ U ∧
      ∃ Q : (ℝ × ℝ) → ℝ,
        ContDiffOn ℝ ∞ Q U ∧
        (∀ p ∈ U, 0 < Q p) ∧
        (∀ p ∈ U, forwardScalar a p.2 (Q p) = p.1) ∧
        EqOn Q (extendedQ a) (U ∩ halfPlane) := by
  let p₀ : ℝ × ℝ := (boundaryQ a z, z)
  have hq : 0 < p₀.1 := boundaryQ_pos hz
  have hm : 0 < scalarSlope a p₀.2 p₀.1 := by
    simpa only [p₀, boundaryQ_slope ha1 hz] using sub_pos.mpr ha1
  have hsm := forwardMap_smooth (a := a) hq.ne'
  have hd := forwardMap_hasFDerivAt (a := a) hq.ne' hm.ne'
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let e := hsm.toOpenPartialHomeomorph (forwardMap a) hd hn
  have hep : p₀ ∈ e.source := hsm.mem_toOpenPartialHomeomorph_source hd hn
  have heval : e p₀ = (0, z) := by
    change (forwardScalar a z (boundaryQ a z), z) = (0, z)
    rw [boundaryQ_forward ha1 hz]
  have het : (0, z) ∈ e.target := heval ▸ e.map_source hep
  have hei : e.symm (0, z) = p₀ := by rw [← heval]; exact e.left_inv hep
  have hc : ContinuousAt e.symm (0, z) := e.continuousAt_symm het
  have hqev : ∀ᶠ p in 𝓝 (0, z), 0 < (e.symm p).1 := by
    apply hc.fst.eventually
    change Ioi 0 ∈ 𝓝 ((e.symm (0, z)).1)
    rw [hei]
    exact Ioi_mem_nhds hq
  have hsc : ContinuousAt (fun p : ℝ × ℝ => scalarSlope a p.2 p.1) p₀ := by
    exact (contDiffAt_const.sub
      (((contDiffAt_snd.pow 2).mul contDiffAt_const).mul
        (contDiffAt_fst.rpow_const_of_ne hq.ne')) :
          ContDiffAt ℝ ∞ _ p₀).continuousAt
  have hmev : ∀ᶠ p in 𝓝 (0, z), 0 < scalarSlope a (e.symm p).2 (e.symm p).1 := by
    have hsc' : ContinuousAt (fun p : ℝ × ℝ => scalarSlope a p.2 p.1)
        (e.symm (0, z)) := by rwa [hei]
    have hc' := hsc'.comp hc
    apply hc'.eventually
    change Ioi 0 ∈ 𝓝 (scalarSlope a (e.symm (0, z)).2 (e.symm (0, z)).1)
    rw [hei]
    exact Ioi_mem_nhds hm
  have htev : ∀ᶠ p in 𝓝 (0, z), p ∈ e.target := e.open_target.mem_nhds het
  obtain ⟨U, hUsub, hUopen, hUbase⟩ := mem_nhds_iff.mp (htev.and (hqev.and hmev))
  refine ⟨U, hUopen, hUbase, fun p => (e.symm p).1, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hps := hUsub hp
    have hs : ContDiffAt ℝ ∞ e.symm p := by
      apply e.contDiffAt_symm hps.1
        (forwardMap_hasFDerivAt hps.2.1.ne' hps.2.2.ne')
      exact forwardMap_smooth hps.2.1.ne'
    exact hs.fst.contDiffWithinAt
  · intro p hp
    exact (hUsub hp).2.1
  · intro p hp
    have hi := e.right_inv (hUsub hp).1
    have hi₂ := congrArg Prod.snd hi
    change (e.symm p).2 = p.2 at hi₂
    have hi₁ := congrArg Prod.fst hi
    change forwardScalar a (e.symm p).2 (e.symm p).1 = p.1 at hi₁
    rwa [hi₂] at hi₁
  · intro p hp
    have hps := hUsub hp.1
    have hi := e.right_inv hps.1
    have hi₂ := congrArg Prod.snd hi
    change (e.symm p).2 = p.2 at hi₂
    have hi₁ := congrArg Prod.fst hi
    change forwardScalar a (e.symm p).2 (e.symm p).1 = p.1 at hi₁
    rw [hi₂] at hi₁
    by_cases ht : 0 < p.1
    · rw [extendedQ_positive ht]
      exact eq_coordinateQ ha ha1 ht hps.2.1 hi₁
    · have ht₀ : p.1 = 0 := le_antisymm (le_of_not_gt ht) hp.2.1
      have hz' : p.2 ≠ 0 := by
        intro hz₀
        have he : forwardScalar a 0 (e.symm p).1 = 0 := by
          simpa only [hz₀, ht₀] using hi₁
        have he' : (e.symm p).1 = 0 := by simpa [forwardScalar] using he
        exact hps.2.1.ne' he'
      rw [extendedQ, ite_eq_right ht]
      exact positive_zero_solution_unique ha1 hz' hps.2.1 (by simpa only [ht₀] using hi₁)

/-- A common smooth ambient continuation of both coordinates. The open set
contains points with both signs of `τ`, while agreement is required only on
the physical half-plane. -/
theorem exists_smooth_boundary_coordinates {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : z ≠ 0) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, z) ∈ U ∧
      ∃ Q E : (ℝ × ℝ) → ℝ,
        ContDiffOn ℝ ∞ Q U ∧ ContDiffOn ℝ ∞ E U ∧
        (∀ p ∈ U, 0 < Q p) ∧
        EqOn Q (extendedQ a) (U ∩ halfPlane) ∧
        EqOn E (extendedEta a) (U ∩ halfPlane) := by
  obtain ⟨U, hUo, hUb, Q, hQs, hQp, _, hQe⟩ := exists_smooth_boundary_q ha ha1 hz
  let E : (ℝ × ℝ) → ℝ := fun p => p.2 / Q p ^ axialExponent a
  refine ⟨U, hUo, hUb, Q, E, hQs, ?_, hQp, hQe, ?_⟩
  · exact contDiffOn_snd.div (hQs.rpow_const_of_ne (fun p hp => (hQp p hp).ne'))
      (fun p hp => (Real.rpow_pos_of_pos (hQp p hp) _).ne')
  · intro p hp
    dsimp [E, extendedEta]
    rw [hQe hp]

theorem extendedQ_germ_positive {a : ℝ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    extendedQ a =ᶠ[𝓝 p] coordinateQ a := by
  filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hp)] with q hq
  exact extendedQ_positive hq

theorem extendedEta_germ_positive {a : ℝ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    extendedEta a =ᶠ[𝓝 p] coordinateEta a := by
  filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hp)] with q hq
  exact extendedEta_positive hq

theorem extendedQ_smooth {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ContDiffOn ℝ ∞ (extendedQ a) domain := by
  intro p hp
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ p.1 from hp.1.1) with ht | ht
  · exact ((coordinateQ_smooth ha ha1 ht).congr_of_eventuallyEq
      (extendedQ_germ_positive ht)).contDiffWithinAt
  · have hp₀ : p = (0, p.2) := by ext <;> simp [← ht]
    have hz : p.2 ≠ 0 := by
      intro hz
      exact hp.2 (by simpa [hz] using hp₀)
    obtain ⟨U, hUo, hUb, Q, hQs, _, _, hQe⟩ := exists_smooth_boundary_q ha ha1 hz
    have hUp : p ∈ U := hp₀.symm ▸ hUb
    have hg : extendedQ a =ᶠ[𝓝[domain] p] Q := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hUp),
        self_mem_nhdsWithin] with y hyU hyd
      exact (hQe ⟨hyU, hyd.1⟩).symm
    exact ((hQs p hUp).contDiffAt (hUo.mem_nhds hUp)).contDiffWithinAt.congr_of_eventuallyEq
      hg (hQe ⟨hUp, hp.1⟩).symm

theorem extendedQ_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : p ∈ domain) : 0 < extendedQ a p := by
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ p.1 from hp.1.1) with ht | ht
  · rw [extendedQ_positive ht]
    exact (coordinateQ_spec ha ha1 ht).1
  · have hz : p.2 ≠ 0 := by
      intro hz
      apply hp.2
      ext <;> simp [hz, ← ht]
    simp only [extendedQ, ← ht, lt_self_iff_false, ↓reduceIte]
    exact boundaryQ_pos hz

theorem extendedEta_smooth {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ContDiffOn ℝ ∞ (extendedEta a) domain := by
  exact contDiffOn_snd.div
    ((extendedQ_smooth ha ha1).rpow_const_of_ne
      (fun _ hp => (extendedQ_pos ha ha1 hp).ne'))
    (fun _ hp => (Real.rpow_pos_of_pos (extendedQ_pos ha ha1 hp) _).ne')

theorem extendedEta_boundary_sq {a z : ℝ} (ha1 : a < 1) (hz : z ≠ 0) :
    extendedEta a (0, z) ^ 2 = 1 := by
  rw [extendedEta_boundary ha1, div_pow, sq_abs, div_self (pow_ne_zero 2 hz)]

/-- The true Jacobian denominator is `L = 1 - a η²`, up to and including
the nonsingular boundary. -/
theorem extended_slope_eq_L {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : p ∈ domain) :
    scalarSlope a p.2 (extendedQ a p) = 1 - a * extendedEta a p ^ 2 := by
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ p.1 from hp.1.1) with ht | ht
  · rw [extendedQ_positive ht, extendedEta_positive ht]
    exact scalarSlope_eq_L ha ha1 ht
  · have hp₀ : p = (0, p.2) := by ext <;> simp [← ht]
    have hz : p.2 ≠ 0 := fun hz => hp.2 (by simpa [hz] using hp₀)
    conv_lhs => rw [hp₀]
    conv_rhs => rw [hp₀]
    rw [extendedQ_boundary, boundaryQ_slope ha1 hz, extendedEta_boundary_sq ha1 hz,
      mul_one]

theorem extended_L_lowerBound {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : p ∈ domain) :
    1 - a ≤ 1 - a * extendedEta a p ^ 2 := by
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ p.1 from hp.1.1) with ht | ht
  · rw [extendedEta_positive ht]
    have hs := coordinateEta_sq_lt_one ha ha1 ht
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hs.le)]
  · have hp₀ : p = (0, p.2) := by ext <;> simp [← ht]
    have hz : p.2 ≠ 0 := fun hz => hp.2 (by simpa [hz] using hp₀)
    rw [hp₀, extendedEta_boundary_sq ha1 hz, mul_one]

theorem extended_L_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {p : ℝ × ℝ} (hp : p ∈ domain) : 0 < 1 - a * extendedEta a p ^ 2 :=
  lt_of_lt_of_le (sub_pos.mpr ha1) (extended_L_lowerBound ha ha1 hp)

theorem positive_mem_domain {p : ℝ × ℝ} (hp : 0 < p.1) : p ∈ domain := by
  refine ⟨⟨hp.le, mem_univ _⟩, ?_⟩
  intro he
  exact hp.ne' (congrArg Prod.fst he)

theorem positiveDomain_subset : positiveDomain ⊆ domain :=
  fun _ hp => positive_mem_domain hp.1

/-- The approach filter in the joint jet limits is nonempty. -/
theorem positive_boundary_filter_neBot (z : ℝ) :
    NeBot (𝓝[positiveDomain] (0, z)) := by
  rw [positiveDomain, nhdsWithin_prod_eq, nhdsWithin_univ]
  infer_instance

private theorem iteratedFDeriv_eq_of_germ {f g : (ℝ × ℝ) → ℝ}
    {p : ℝ × ℝ} (hg : f =ᶠ[𝓝 p] g) (n : ℕ) :
    iteratedFDeriv ℝ n f p = iteratedFDeriv ℝ n g p := by
  have hg' : f =ᶠ[𝓝[univ] p] g := by simpa only [nhdsWithin_univ] using hg
  simpa only [iteratedFDerivWithin_univ] using
    hg'.iteratedFDerivWithin_eq hg.eq_of_nhds n

private theorem nat_order_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)

theorem extendedQ_jet_eq_positive {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (n : ℕ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    iteratedFDerivWithin ℝ n (extendedQ a) domain p =
      iteratedFDeriv ℝ n (coordinateQ a) p := by
  have hs := (coordinateQ_smooth ha ha1 hp).congr_of_eventuallyEq
    (extendedQ_germ_positive hp)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_domain
    (hs.of_le (nat_order_le_infty n)) (positive_mem_domain hp)]
  exact iteratedFDeriv_eq_of_germ (extendedQ_germ_positive hp) n

theorem extendedEta_jet_eq_positive {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (n : ℕ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    iteratedFDerivWithin ℝ n (extendedEta a) domain p =
      iteratedFDeriv ℝ n (coordinateEta a) p := by
  have hs := (coordinateEta_smooth ha ha1 hp).congr_of_eventuallyEq
    (extendedEta_germ_positive hp)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_domain
    (hs.of_le (nat_order_le_infty n)) (positive_mem_domain hp)]
  exact iteratedFDeriv_eq_of_germ (extendedEta_germ_positive hp) n

theorem extendedQ_jets_continuous {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (n : ℕ) : ContinuousOn (iteratedFDerivWithin ℝ n (extendedQ a) domain) domain := by
  intro p hp
  exact ((extendedQ_smooth ha ha1 p hp).iteratedFDerivWithin_right
    (m := 0) uniqueDiffOn_domain (by simp) hp).continuousWithinAt

theorem extendedEta_jets_continuous {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (n : ℕ) : ContinuousOn (iteratedFDerivWithin ℝ n (extendedEta a) domain) domain := by
  intro p hp
  exact ((extendedEta_smooth ha ha1 p hp).iteratedFDerivWithin_right
    (m := 0) uniqueDiffOn_domain (by simp) hp).continuousWithinAt

/-- Every actual full derivative tensor of the constructed positive-time `q`
has a joint one-sided limit. This allows `z` and `τ` to approach together. -/
theorem coordinateQ_jets_tendsto {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : z ≠ 0) (n : ℕ) :
    Tendsto (iteratedFDeriv ℝ n (coordinateQ a)) (𝓝[positiveDomain] (0, z))
      (𝓝 (iteratedFDerivWithin ℝ n (extendedQ a) domain (0, z))) := by
  have hc := (extendedQ_jets_continuous ha ha1 n (0, z) (boundary_mem_domain hz)).mono
    positiveDomain_subset
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact extendedQ_jet_eq_positive ha ha1 n hp.1

/-- The corresponding joint one-sided limits of all actual `η` tensors. -/
theorem coordinateEta_jets_tendsto {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : z ≠ 0) (n : ℕ) :
    Tendsto (iteratedFDeriv ℝ n (coordinateEta a)) (𝓝[positiveDomain] (0, z))
      (𝓝 (iteratedFDerivWithin ℝ n (extendedEta a) domain (0, z))) := by
  have hc := (extendedEta_jets_continuous ha ha1 n (0, z) (boundary_mem_domain hz)).mono
    positiveDomain_subset
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact extendedEta_jet_eq_positive ha ha1 n hp.1

/-- Boundary tensor values vary continuously with the nonsingular axial point. -/
theorem boundaryQ_jets_continuous {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    ContinuousOn (fun z : ℝ => iteratedFDerivWithin ℝ n (extendedQ a) domain (0, z))
      {0}ᶜ := by
  exact (extendedQ_jets_continuous ha ha1 n).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => boundary_mem_domain hz)

theorem boundaryEta_jets_continuous {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    ContinuousOn (fun z : ℝ => iteratedFDerivWithin ℝ n (extendedEta a) domain (0, z))
      {0}ᶜ := by
  exact (extendedEta_jets_continuous ha ha1 n).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => boundary_mem_domain hz)

theorem coordinateQ_tendsto_boundary {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : z ≠ 0) :
    Tendsto (coordinateQ a) (𝓝[positiveDomain] (0, z)) (𝓝 (boundaryQ a z)) := by
  have hc := ((extendedQ_smooth ha ha1).continuousOn (0, z) (boundary_mem_domain hz)).mono
    positiveDomain_subset
  change Tendsto (extendedQ a) _ (𝓝 (extendedQ a (0, z))) at hc
  rw [extendedQ_boundary] at hc
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact extendedQ_positive hp.1

theorem coordinateEta_tendsto_boundary {a z : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hz : z ≠ 0) :
    Tendsto (coordinateEta a) (𝓝[positiveDomain] (0, z)) (𝓝 (Real.sign z)) := by
  have hc := ((extendedEta_smooth ha ha1).continuousOn (0, z) (boundary_mem_domain hz)).mono
    positiveDomain_subset
  change Tendsto (extendedEta a) _ (𝓝 (extendedEta a (0, z))) at hc
  rw [extendedEta_boundary_sign ha1] at hc
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact extendedEta_positive hp.1

/-- The actual derivative tensors converge locally uniformly in `z ≠ 0`.
This follows from the joint limit and continuity of the boundary tensor,
rather than from pointwise convergence alone. -/
theorem coordinateQ_jets_locallyUniform {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    TendstoLocallyUniformlyOn
      (fun τ z => iteratedFDeriv ℝ n (coordinateQ a) (τ, z))
      (fun z => iteratedFDerivWithin ℝ n (extendedQ a) domain (0, z))
      (𝓝[>] 0) {0}ᶜ := by
  apply isClosed_singleton.isOpen_compl.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro z hz
  have hl := coordinateQ_jets_tendsto ha ha1 hz n
  rw [positiveDomain, nhdsWithin_prod_eq, nhdsWithin_univ] at hl
  have hc := ((boundaryQ_jets_continuous ha ha1 n z hz).continuousAt
    (isClosed_singleton.isOpen_compl.mem_nhds hz)).tendsto.comp
      (tendsto_snd : Tendsto (Prod.snd : ℝ × ℝ → ℝ) ((𝓝[>] 0) ×ˢ 𝓝 z) (𝓝 z))
  exact (hc.prodMk_nhds hl).mono_right (nhds_le_uniformity _)

theorem coordinateEta_jets_locallyUniform {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    TendstoLocallyUniformlyOn
      (fun τ z => iteratedFDeriv ℝ n (coordinateEta a) (τ, z))
      (fun z => iteratedFDerivWithin ℝ n (extendedEta a) domain (0, z))
      (𝓝[>] 0) {0}ᶜ := by
  apply isClosed_singleton.isOpen_compl.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro z hz
  have hl := coordinateEta_jets_tendsto ha ha1 hz n
  rw [positiveDomain, nhdsWithin_prod_eq, nhdsWithin_univ] at hl
  have hc := ((boundaryEta_jets_continuous ha ha1 n z hz).continuousAt
    (isClosed_singleton.isOpen_compl.mem_nhds hz)).tendsto.comp
      (tendsto_snd : Tendsto (Prod.snd : ℝ × ℝ → ℝ) ((𝓝[>] 0) ×ˢ 𝓝 z) (𝓝 z))
  exact (hc.prodMk_nhds hl).mono_right (nhds_le_uniformity _)

/-- On this unique-differentiability domain the relative boundary jets are
exactly the ordinary jets of any smooth local extension agreeing there. -/
theorem boundary_jet_eq_ambient {f F : (ℝ × ℝ) → ℝ} {z : ℝ}
    (hz : z ≠ 0) {U : Set (ℝ × ℝ)} (hUo : IsOpen U) (hUb : (0, z) ∈ U)
    (hFs : ContDiffOn ℝ ∞ F U) (hFe : EqOn F f (U ∩ halfPlane)) (n : ℕ) :
    iteratedFDerivWithin ℝ n f domain (0, z) = iteratedFDeriv ℝ n F (0, z) := by
  have hg : f =ᶠ[𝓝[domain] (0, z)] F := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hUb),
      self_mem_nhdsWithin] with p hpU hpd
    exact (hFe ⟨hpU, hpd.1⟩).symm
  rw [hg.iteratedFDerivWithin_eq (hFe ⟨hUb, (boundary_mem_domain hz).1⟩).symm n]
  exact iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_domain
    (((hFs (0, z) hUb).contDiffAt (hUo.mem_nhds hUb)).of_le (nat_order_le_infty n))
    (boundary_mem_domain hz)

/-- The notation used in the manuscript: `a = 2h` and `D = 1/2 - h`. -/
theorem manuscript_boundary_values {h : ℝ} (_hh : 0 < h) (hh1 : h < 1 / 2) (z : ℝ) :
    extendedQ (2 * h) (0, z) = |z| ^ (1 / (1 / 2 - h)) ∧
      extendedEta (2 * h) (0, z) = Real.sign z := by
  constructor
  · rw [extendedQ_boundary, boundaryQ]
    congr 1
    rw [one_div]
    congr 1
    dsimp [axialExponent]
    ring
  · exact extendedEta_boundary_sign (by linarith)

theorem manuscript_coordinates_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (extendedQ (2 * h)) domain ∧
      ContDiffOn ℝ ∞ (extendedEta (2 * h)) domain :=
  ⟨extendedQ_smooth (by linarith) (by linarith),
    extendedEta_smooth (by linarith) (by linarith)⟩

end NavierStokes.BoundaryCoordinates
