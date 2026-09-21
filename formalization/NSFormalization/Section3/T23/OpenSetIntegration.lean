import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Order.LeftRightNhds

/-! Integration of a derivative over a bounded open set with zero boundary values. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace NSFormalization.Section3.T23

/-- Zero extension preserves a zero derivative at a zero of the function. -/
lemma hasDerivAt_indicator_zero {s : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf : HasDerivAt f 0 x) (hz : f x = 0) :
    HasDerivAt (s.indicator f) 0 x := by
  classical
  have hi : s.indicator f x = 0 := by by_cases h : x ∈ s <;> simp [h, hz]
  rw [hasDerivAt_iff_isLittleO] at hf ⊢
  simp only [hz, hi, smul_zero, sub_zero] at hf ⊢
  exact (Asymptotics.IsBigO.of_bound' (Filter.Eventually.of_forall
    (fun y => norm_indicator_le_norm_self (s := s) f y))).trans_isLittleO hf

/-- Along a real line, a zero-boundary function has zero integral derivative.
The only exceptional points are a countable set of isolated boundary points. -/
theorem integral_deriv_open_eq_zero {s : Set ℝ} (hs : IsOpen s)
    (hb : Bornology.IsBounded s) (f f' : ℝ → ℝ)
    (hf : ∀ x ∈ closure s, HasDerivAt f (f' x) x)
    (hz : ∀ x ∈ frontier s, f x = 0)
    (hi : IntegrableOn f' s) : (∫ x in s, f' x) = 0 := by
  classical
  let bad := {x ∈ frontier s | 𝓝[frontier s ∩ Ioi x] x = ⊥}
  have hbad : bad.Countable := countable_setOfPred_isolated_right_within
  have hc : Continuous (s.indicator f) := continuous_indicator hz
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
  have hd : ∀ x ∉ bad, HasDerivAt (s.indicator f) (s.indicator f' x) x := by
    intro x hx
    by_cases hxs : x ∈ s
    · rw [indicator_of_mem hxs]
      exact (hf x (subset_closure hxs)).congr_of_eventuallyEq
        (Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hxs, fun y hy => indicator_of_mem hy f⟩)
    by_cases hxc : x ∈ closure s
    · have hfront : x ∈ frontier s := by simpa [frontier, hs.interior_eq] using And.intro hxc hxs
      have hn : (𝓝[frontier s ∩ Ioi x] x).NeBot := ⟨fun h => hx ⟨hfront, h⟩⟩
      have ha : AccPt x (𝓟 (frontier s)) := by
        rw [accPt_principal_iff_clusterPt]
        change (𝓝[frontier s \ {x}] x).NeBot
        exact hn.mono (nhdsWithin_mono _ (by intro y hy; exact ⟨hy.1, ne_of_gt hy.2⟩))
      have hd0 : f' x = 0 := by
        rw [← (hf x hxc).deriv]
        exact deriv_zero_of_frequently_const ((accPt_iff_frequently_nhdsNE.mp ha).mono
          (fun y hy => hz y hy))
      rw [indicator_of_notMem hxs]
      exact hasDerivAt_indicator_zero (hd0 ▸ hf x hxc) (hz x hfront)
    · rw [indicator_of_notMem hxs]
      apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
      exact indicator_of_notMem (fun h => hy (subset_closure h)) f
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  let a := -(max R 0 + 1)
  let b := max R 0 + 1
  have hab : a ≤ b := by dsimp [a,b]; linarith [le_max_right R 0]
  have hsa : a ∉ s := by
    intro h
    have := hR a h
    have hnon : 0 ≤ max R 0 + 1 := by positivity
    simp only [a, norm_neg, Real.norm_eq_abs, abs_of_nonneg hnon] at this
    linarith [le_max_left R 0]
  have hsb : b ∉ s := by
    intro h
    have := hR b h
    have hnon : 0 ≤ max R 0 + 1 := by positivity
    simp only [b, Real.norm_eq_abs, abs_of_nonneg hnon] at this
    linarith [le_max_left R 0]
  have hsub : s ⊆ Ioc a b := by
    intro x hx
    have hh := abs_le.mp (hR x hx)
    dsimp [a,b]
    constructor <;> linarith [le_max_left R 0]
  have hI := integral_eq_of_hasDerivAt_off_countable_of_le (s.indicator f)
    (s.indicator f') hab hbad hc.continuousOn (fun x hx => hd x hx.2)
    (hi.integrable_indicator hs.measurableSet).intervalIntegrable
  rw [indicator_of_notMem hsa, indicator_of_notMem hsb, sub_self,
    intervalIntegral.integral_of_le hab, setIntegral_indicator hs.measurableSet,
    inter_eq_right.mpr hsub] at hI
  exact hI


/-- Fubini reduces zero boundary flux on an arbitrary bounded open set to the
one-dimensional fundamental theorem of calculus. No boundary regularity is needed. -/
theorem integral_partial_open_eq_zero {s : Set (Fin 3 → ℝ)} (hs : IsOpen s)
    (hb : Bornology.IsBounded s) (f : (Fin 3 → ℝ) → ℝ)
    (hf : ∀ x ∈ closure s, ContDiffAt ℝ 1 f x)
    (hz : ∀ x ∈ frontier s, f x = 0) (j : Fin 3) :
    (∫ x in s, fderiv ℝ f x (Pi.single j 1)) = 0 := by
  classical
  let D := fun x => fderiv ℝ f x (Pi.single j 1)
  have hD : ContinuousOn D (closure s) := by
    have hdf : ContinuousOn (fderiv ℝ f) (closure s) := fun x hx =>
      ((hf x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
    exact hdf.clm_apply continuousOn_const
  have hi : IntegrableOn D s :=
    (hD.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  let F := s.indicator D
  have hF : Integrable F := hi.integrable_indicator hs.measurableSet
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j).symm
  have he : MeasurePreserving e (volume.prod volume) volume := by
    simpa only [e, volume_pi] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) j).symm
  have hcomp : Integrable (fun p : ℝ × (Fin 2 → ℝ) => F (j.insertNth p.1 p.2)) (volume.prod volume) := by
    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Function.comp_def] using
      (he.integrable_comp_emb e.measurableEmbedding).mpr hF
  have heq : (∫ x, F x) = ∫ p : ℝ × (Fin 2 → ℝ), F (j.insertNth p.1 p.2) ∂(volume.prod volume) := by
    simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Function.comp_def] using
      (he.integral_comp' F).symm
  rw [← integral_indicator hs.measurableSet, heq, integral_prod_symm _ hcomp]
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro y
  let L : ℝ → (Fin 3 → ℝ) := fun t => j.insertNth t y
  have hL (t : ℝ) : HasDerivAt L (Pi.single j 1) t := by
    convert hasDerivAt_update (j.insertNth 0 y) j t using 1
    ext z
    simp [L, Fin.update_insertNth]
  have hcL : Continuous L := continuous_iff_continuousAt.mpr (fun t => (hL t).continuousAt)
  let u := L ⁻¹' s
  have hu : IsOpen u := hs.preimage hcL
  have hucl : closure u ⊆ L ⁻¹' closure s :=
    closure_minimal (fun t ht => subset_closure ht) (isClosed_closure.preimage hcL)
  have huB : Bornology.IsBounded u := by
    obtain ⟨R, hR⟩ := hb.exists_norm_le
    apply (isBounded_iff_forall_norm_le).mpr
    refine ⟨R, fun t ht => ?_⟩
    calc ‖t‖ = ‖L t j‖ := by simp [L]
         _ ≤ ‖L t‖ := norm_le_pi_norm _ j
         _ ≤ R := hR (L t) ht
  have hzU : ∀ t ∈ frontier u, (f ∘ L) t = 0 := by
    intro t ht
    apply hz
    rw [frontier, hs.interior_eq]
    refine ⟨hucl ht.1, ?_⟩
    exact fun h => ht.2 (by simpa [hu.interior_eq, u] using h)
  have hint : (∫ t in u, D (L t)) = 0 :=
    integral_deriv_open_eq_zero hu huB (f ∘ L) (D ∘ L)
      (fun t ht => ((hf (L t) (hucl ht)).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt t (hL t))
      hzU (((hD.comp hcL.continuousOn hucl).integrableOn_compact
        huB.isCompact_closure).mono_set subset_closure)
  simpa [← integral_indicator hu.measurableSet, F, u, L, Set.indicator, Function.comp_def] using hint

end NSFormalization.Section3.T23
