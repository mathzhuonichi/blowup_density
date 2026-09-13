import NSFormalization.Paper3.ForceObservations
import NavierStokes.R3.CompactTimeIntegral

/-! Differentiation of the actual zero spatial mean closes the temporal part of
Paper 3's cell-force observation mechanism. -/

noncomputable section
namespace NSFormalization.Paper3
open Set Filter MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NavierStokes.R3CompactIntegration
open scoped Topology

/-- The spatial integral of a time derivative is zero for a jointly C¹,
uniformly compact, divergence-free velocity perturbation. -/
theorem integral_timeDerivative_component_eq_zero
    {w : ℝ × Space → Space} {z : Space → Space} {a b t : ℝ} {K : Set Space}
    (hK : IsCompact K) (hw : ContDiffOn ℝ 1 w (Icc a b ×ˢ univ))
    (hsupp : ∀ r ∈ Icc a b, ∀ x ∉ K, w (r, x) = 0)
    (hdiv : ∀ r ∈ Icc a b, ∀ x, Comparator.divergence (fun y => w (r, y)) x = 0)
    (ht : t ∈ Ioo a b)
    (hderiv : ∀ x, HasDerivAt (fun r => w (r, x)) (z x) t) (j : Fin 3) :
    (∫ x : Space, z x j) = 0 := by
  have hF : ContDiffOn ℝ 1 (fun q : ℝ × Space => w q j) (Icc a b ×ˢ univ) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hw
  have h := NavierStokesR3.CompactTimeIntegral.hasDerivAt_integral_of_contDiffOn_of_hasDerivAt
    hK hF (fun r hr x hx => by simp [hsupp r hr x hx]) ht
    (fun x => (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t (hderiv x))
  have heq : (fun r => ∫ x : Space, w (r, x) j) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    have hslice : ContDiff ℝ 1 (fun x => w (r, x)) :=
      hw.comp_contDiff (contDiff_const.prodMk contDiff_id)
        (fun x => ⟨Ioo_subset_Icc_self hr, mem_univ x⟩)
    have hsupport : HasCompactSupport (fun x => w (r, x)) :=
      HasCompactSupport.intro hK (hsupp r (Ioo_subset_Icc_self hr))
    exact integral_component_eq_zero hslice hsupport (hdiv r (Ioo_subset_Icc_self hr)) j
  exact (h.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t (0 : ℝ))

/-- Actual integrated force difference for a time-dependent compact solenoidal
perturbation satisfying a conservative component momentum balance. -/
theorem integral_timeDependent_force_eq_zero
    {w : ℝ × Space → Space} {z : Space → Space} {a b t : ℝ} {K : Set Space}
    {flux : Fin 3 → Space → ℝ} {force : Space → ℝ}
    (hK : IsCompact K) (hw : ContDiffOn ℝ 1 w (Icc a b ×ˢ univ))
    (hsupp : ∀ r ∈ Icc a b, ∀ x ∉ K, w (r, x) = 0)
    (hdiv : ∀ r ∈ Icc a b, ∀ x, Comparator.divergence (fun y => w (r, y)) x = 0)
    (ht : t ∈ Ioo a b)
    (hderiv : ∀ x, HasDerivAt (fun r => w (r, x)) (z x) t)
    (j : Fin 3) (hzint : Integrable (fun x => z x j))
    (hflux : ∀ i, ContDiff ℝ 1 (flux i))
    (hfluxc : ∀ i, HasCompactSupport (flux i))
    (hbalance : ∀ x, force x = z x j + ∑ i, spatialPartial i (flux i) x) :
    (∫ x : Space, force x) = 0 := by
  have hfi (i : Fin 3) : Integrable (spatialPartial i (flux i)) :=
    (partial_continuous (hflux i) i).integrable_of_hasCompactSupport (partial_compact (hfluxc i) i)
  simp_rw [hbalance]
  rw [integral_add hzint (integrable_finsetSum _ (fun i _ => hfi i))]
  rw [integral_timeDerivative_component_eq_zero hK hw hsupp hdiv ht hderiv j]
  rw [integral_finsetSum _ (fun i _ => hfi i)]
  simp [integral_spatialPartial_eq_zero (hflux _) (hfluxc _)]

end NSFormalization.Paper3
