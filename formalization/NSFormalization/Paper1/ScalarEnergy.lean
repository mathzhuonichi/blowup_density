import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Regularized division for the packet and critical energy arguments

This is the scalar analytic step in Lemma `lem:packetenergy` and Proposition
`prop:critical`. Unlike a bound which assumes the desired norm estimate, the
input here is a differentiable squared-energy inequality and a forcing primitive.
Derivation of that inequality from the periodic PDE remains separate.
-/
namespace NSFormalization.Paper1
open Set

/-! The generalized endpoint form is the canonical scalar lemma. -/

/-- A squared-energy inequality implies a bound by the forcing primitive when the
initial energy need not vanish.  The endpoint condition is the sharp
`Real.sqrt (E 0) ≤ N 0` comparison; the zero-energy statement below is its
special case. -/
theorem sqrt_energy_le_primitive_general {T : ℝ} {E E' N b : ℝ → ℝ}
    (hT : 0 ≤ T) (hE : ContinuousOn E (Icc 0 T)) (hN : ContinuousOn N (Icc 0 T))
    (hEN0 : Real.sqrt (E 0) ≤ N 0)
    (hEnonneg : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hb : ∀ t ∈ Ioo 0 T, 0 ≤ b t)
    (hdE : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hdN : ∀ t ∈ Ioo 0 T, HasDerivAt N (b t) t)
    (hineq : ∀ t ∈ Ioo 0 T, E' t ≤ 2 * b t * Real.sqrt (E t)) :
    ∀ t ∈ Icc 0 T, Real.sqrt (E t) ≤ N t := by
  intro t ht
  apply le_of_forall_pos_le_add
  intro δ hδ
  let G : ℝ → ℝ := fun x => Real.sqrt (E x + δ ^ 2) - N x
  have hpos (x : ℝ) (hx : x ∈ Icc 0 T) : 0 < E x + δ ^ 2 := by
    nlinarith [hEnonneg x hx]
  have hgcont : ContinuousOn G (Icc 0 T) := ((hE.add continuousOn_const).sqrt).sub hN
  have hderiv (x : ℝ) (hx : x ∈ Ioo 0 T) :
      HasDerivAt G (E' x / (2 * Real.sqrt (E x + δ ^ 2)) - b x) x :=
    (((hdE x hx).add_const (δ ^ 2)).sqrt (ne_of_gt (hpos x ⟨hx.1.le, hx.2.le⟩))).sub (hdN x hx)
  have hG : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hgcont
    · intro x hx
      exact (hderiv x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo 0 T := by simpa only [interior_Icc] using hx
      have hs : 0 < Real.sqrt (E x + δ ^ 2) :=
        Real.sqrt_pos.mpr (hpos x ⟨hx'.1.le, hx'.2.le⟩)
      have hmono : Real.sqrt (E x) ≤ Real.sqrt (E x + δ ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])
      have hdiv : E' x / (2 * Real.sqrt (E x + δ ^ 2)) ≤ b x := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (E x + δ ^ 2))).mpr
        nlinarith [hineq x hx', mul_nonneg (hb x hx') (sub_nonneg.mpr hmono)]
      exact sub_nonpos.mpr hdiv
  have hbound := hG ⟨le_rfl, hT⟩ ht ht.1
  have hE0nn : 0 ≤ E 0 := hEnonneg 0 ⟨le_rfl, hT⟩
  have hN0nn : 0 ≤ N 0 := le_trans (Real.sqrt_nonneg _) hEN0
  have hsq : E 0 ≤ N 0 ^ 2 := by
    nlinarith [Real.sq_sqrt hE0nn, hEN0, Real.sqrt_nonneg (E 0)]
  have hG0 : G 0 ≤ δ := by
    show Real.sqrt (E 0 + δ ^ 2) - N 0 ≤ δ
    have hle : Real.sqrt (E 0 + δ ^ 2) ≤ N 0 + δ := by
      rw [show N 0 + δ = Real.sqrt ((N 0 + δ) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hN0nn hδ.le])
    linarith
  have hGt : G t ≤ δ := le_trans hbound hG0
  have hfinal : Real.sqrt (E t + δ ^ 2) ≤ N t + δ := by
    simp only [G] at hGt; linarith
  exact (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg δ])).trans hfinal

/-- A squared-energy inequality implies a bound by the forcing primitive even
when the energy vanishes. The proof regularizes the square root before division. -/
theorem sqrt_energy_le_primitive {T : ℝ} {E E' N b : ℝ → ℝ}
    (hT : 0 ≤ T) (hE : ContinuousOn E (Icc 0 T))
    (hN : ContinuousOn N (Icc 0 T))
    (hE0 : E 0 = 0) (hN0 : N 0 = 0)
    (hEnonneg : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hb : ∀ t ∈ Ioo 0 T, 0 ≤ b t)
    (hdE : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hdN : ∀ t ∈ Ioo 0 T, HasDerivAt N (b t) t)
    (hineq : ∀ t ∈ Ioo 0 T, E' t ≤ 2 * b t * Real.sqrt (E t)) :
    ∀ t ∈ Icc 0 T, Real.sqrt (E t) ≤ N t := by
  exact sqrt_energy_le_primitive_general hT hE hN (by rw [hE0, Real.sqrt_zero, hN0])
    hEnonneg hb hdE hdN hineq

/-- Absorb nonlinear critical energy when the critical norm stays below ν/(2C).
The derivative variable is the derivative of the *squared* critical norm. -/
theorem critical_energy_absorption {ν C y z b E' : ℝ}
    (hsmall : C * y ≤ ν / 2)
    (henergy : E' / 2 + (ν - C * y) * z ^ 2 ≤ b * y) :
    E' / 2 + (ν / 2) * z ^ 2 ≤ b * y := by
  have h := mul_le_mul_of_nonneg_right hsmall (sq_nonneg z)
  nlinarith

/-- Dropping nonnegative dissipation yields the exact scalar input above. -/
theorem critical_squared_derivative_bound {ν y z b E' : ℝ} (hν : 0 ≤ ν)
    (henergy : E' / 2 + (ν / 2) * z ^ 2 ≤ b * y) :
    E' ≤ 2 * b * y := by
  have h := mul_nonneg hν (sq_nonneg z)
  nlinarith

/-- Close a bootstrap by taking the first level-crossing time. The improvement
hypothesis is required only on intervals on which the bootstrap bound holds;
it can be supplied by `sqrt_energy_le_primitive` after dissipation absorption. -/
theorem continuous_bootstrap {T K ρ : ℝ} {y : ℝ → ℝ}
    (hy : Continuous y) (hy0 : y 0 ≤ ρ) (hρ : ρ < K)
    (improve : ∀ t ∈ Icc 0 T, (∀ x ∈ Icc 0 t, y x ≤ K) → y t ≤ ρ) :
    ∀ t ∈ Icc 0 T, y t ≤ ρ := by
  have no_level : ∀ t ∈ Icc 0 T, y t ≠ K := by
    intro t ht heq
    let S : Set ℝ := Icc 0 T ∩ {x | y x = K}
    have hcompact : IsCompact S :=
      isCompact_Icc.inter_right (isClosed_eq hy continuous_const)
    obtain ⟨τ, hτ⟩ := hcompact.exists_isLeast ⟨t, ht, heq⟩
    have hτmem : τ ∈ Icc 0 T := hτ.1.1
    have hτeq : y τ = K := hτ.1.2
    have hprefix : ∀ x ∈ Icc 0 τ, y x ≤ K := by
      intro x hx
      by_contra hnot
      have hbig : K < y x := lt_of_not_ge hnot
      obtain ⟨z, hz, hzeq⟩ := intermediate_value_Icc hx.1 hy.continuousOn
        (show K ∈ Icc (y 0) (y x) from ⟨le_trans hy0 hρ.le, hbig.le⟩)
      have hτz : τ ≤ z := hτ.2 ⟨⟨hz.1, hz.2.trans (hx.2.trans hτmem.2)⟩, hzeq⟩
      have hxeq : x = τ := le_antisymm hx.2 (hτz.trans hz.2)
      rw [hxeq, hτeq] at hbig
      exact lt_irrefl _ hbig
    have := improve τ hτmem hprefix
    rw [hτeq] at this
    exact (not_le_of_gt hρ) this
  have below : ∀ t ∈ Icc 0 T, y t ≤ K := by
    intro t ht
    by_contra hnot
    have hbig : K < y t := lt_of_not_ge hnot
    obtain ⟨z, hz, hzeq⟩ := intermediate_value_Icc ht.1 hy.continuousOn
      (show K ∈ Icc (y 0) (y t) from ⟨le_trans hy0 hρ.le, hbig.le⟩)
    exact no_level z ⟨hz.1, hz.2.trans ht.2⟩ hzeq
  intro t ht
  exact improve t ht (fun x hx => below x ⟨hx.1, hx.2.trans ht.2⟩)

/-- The complete scalar critical-force bootstrap. The only analytic input is
 the squared critical energy inequality, together with a forcing primitive N
 bounded by the small total forcing ρ. No positive lower bound on y is required. -/
theorem critical_norm_bound {T ν C K ρ : ℝ} {y E' z b N : ℝ → ℝ}
    (hν : 0 ≤ ν) (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρK : ρ < K)
    (hK : C * K ≤ ν / 2) (hy : Continuous y) (hy0 : y 0 = 0)
    (hynonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t)
    (hN : ContinuousOn N (Icc 0 T)) (hN0 : N 0 = 0)
    (hNbound : ∀ t ∈ Icc 0 T, N t ≤ ρ)
    (hb : ∀ t ∈ Ioo 0 T, 0 ≤ b t)
    (hdE : ∀ t ∈ Ioo 0 T, HasDerivAt (fun x => (y x) ^ 2) (E' t) t)
    (hdN : ∀ t ∈ Ioo 0 T, HasDerivAt N (b t) t)
    (henergy : ∀ t ∈ Ioo 0 T,
      E' t / 2 + (ν - C * y t) * (z t) ^ 2 ≤ b t * y t) :
    ∀ t ∈ Icc 0 T, y t ≤ ρ := by
  apply continuous_bootstrap hy (by simpa [hy0] using hρ0) hρK
  intro t ht hprefix
  have hsub : Icc 0 t ⊆ Icc 0 T := fun x hx => ⟨hx.1, hx.2.trans ht.2⟩
  have hsub' : Ioo 0 t ⊆ Ioo 0 T := fun x hx => ⟨hx.1, hx.2.trans_le ht.2⟩
  have hbnd := sqrt_energy_le_primitive ht.1 (hy.pow 2).continuousOn
    (hN.mono hsub) (by simp [hy0]) hN0 (fun x _ => sq_nonneg (y x))
    (fun x hx => hb x (hsub' hx)) (fun x hx => hdE x (hsub' hx))
    (fun x hx => hdN x (hsub' hx))
    (fun x hx => by
      have hsmall : C * y x ≤ ν / 2 :=
        (mul_le_mul_of_nonneg_left (hprefix x ⟨hx.1.le, hx.2.le⟩) hC).trans hK
      have hd := critical_squared_derivative_bound hν
        (critical_energy_absorption hsmall (henergy x (hsub' hx)))
      simpa only [Pi.pow_apply, Real.sqrt_sq (hynonneg x (hsub ⟨hx.1.le, hx.2.le⟩))] using hd)
    t ⟨ht.1, le_rfl⟩
  simp only [Pi.pow_apply, Real.sqrt_sq (hynonneg t ht)] at hbnd
  exact hbnd.trans (hNbound t ht)

/-- Packet energy plus integrated dissipation is bounded by the square of the
forcing primitive. D is the dissipation primitive, so D' is nonnegative.
This is the scalar content of equation `eq:packetenergy`. -/
theorem energy_add_dissipation_le_primitive_sq {T ν : ℝ} {E E' D D' N b : ℝ → ℝ}
    (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (hE : ContinuousOn E (Icc 0 T)) (hD : ContinuousOn D (Icc 0 T))
    (hN : ContinuousOn N (Icc 0 T))
    (hE0 : E 0 = 0) (hD0 : D 0 = 0) (hN0 : N 0 = 0)
    (hEnonneg : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hD' : ∀ t ∈ Ioo 0 T, 0 ≤ D' t)
    (hb : ∀ t ∈ Ioo 0 T, 0 ≤ b t)
    (hdE : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hdD : ∀ t ∈ Ioo 0 T, HasDerivAt D (D' t) t)
    (hdN : ∀ t ∈ Ioo 0 T, HasDerivAt N (b t) t)
    (henergy : ∀ t ∈ Ioo 0 T, E' t + 2 * ν * D' t ≤ 2 * b t * Real.sqrt (E t)) :
    ∀ t ∈ Icc 0 T, E t + 2 * ν * D t ≤ (N t) ^ 2 := by
  have hnorm := sqrt_energy_le_primitive hT hE hN hE0 hN0 hEnonneg hb hdE hdN
    (fun t ht => by
      have hpos := mul_nonneg hν (hD' t ht)
      nlinarith [henergy t ht])
  let G : ℝ → ℝ := fun t => E t + 2 * ν * D t - (N t) ^ 2
  have hgcont : ContinuousOn G (Icc 0 T) :=
    (hE.add (continuousOn_const.mul hD)).sub (hN.pow 2)
  have hgderiv (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt G (E' t + 2 * ν * D' t - 2 * N t * b t) t := by
    convert ((hdE t ht).add ((hdD t ht).const_mul (2 * ν))).sub ((hdN t ht).pow 2) using 1 <;>
      first | rfl | ring
  have hanti : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hgcont
    · intro t ht
      exact (hgderiv t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      have hmul := mul_le_mul_of_nonneg_left (hnorm t ⟨ht'.1.le, ht'.2.le⟩)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hb t ht'))
      nlinarith [henergy t ht']
  intro t ht
  have h := hanti ⟨le_rfl, hT⟩ ht ht.1
  simp only [G, hE0, hD0, hN0, mul_zero, zero_add, zero_pow (by decide : 2 ≠ 0),
    sub_zero] at h
  linarith

/-- The scalar packet inequality with genuine time integrals, obtained by the
fundamental theorem of calculus from continuous forcing and dissipation rates. -/
theorem packet_energy_integral_bound {T ν : ℝ} {E E' d b : ℝ → ℝ}
    (hT : 0 ≤ T) (hν : 0 ≤ ν) (hE : ContinuousOn E (Icc 0 T))
    (hE0 : E 0 = 0) (hEnonneg : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hbcont : Continuous b) (hdcont : Continuous d)
    (hdnonneg : ∀ t ∈ Ioo 0 T, 0 ≤ d t)
    (hbnonneg : ∀ t ∈ Ioo 0 T, 0 ≤ b t)
    (hdE : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (henergy : ∀ t ∈ Ioo 0 T, E' t + 2 * ν * d t ≤ 2 * b t * Real.sqrt (E t)) :
    ∀ t ∈ Icc 0 T,
      E t + 2 * ν * (∫ x in (0 : ℝ)..t, d x) ≤ (∫ x in (0 : ℝ)..t, b x) ^ 2 := by
  have primitive (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
      HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, f x) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  exact energy_add_dissipation_le_primitive_sq hT hν hE
    (intervalIntegral.differentiable_integral_of_continuous hdcont).continuous.continuousOn
    (intervalIntegral.differentiable_integral_of_continuous hbcont).continuous.continuousOn
    hE0 (by simp) (by simp) hEnonneg hdnonneg hbnonneg hdE
    (fun t _ => primitive d hdcont t) (fun t _ => primitive b hbcont t) henergy

end NSFormalization.Paper1
