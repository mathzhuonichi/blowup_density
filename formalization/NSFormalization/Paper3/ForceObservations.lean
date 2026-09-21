import NSFormalization.Paper3.CompactObservations

/-!
# Integrated momentum flux

The hypothesis is the pointwise conservative momentum balance with an actual
spatial derivative, not the desired equality of force observations. Compact
fluxes integrate to zero. Applying this lemma to a time-dependent insertion still
requires differentiating its divergence and support properties in time.
-/

noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory NavierStokes NavierStokes.ProblemStatement
open NavierStokes.R3CompactIntegration

/-- Every coordinate derivative of a compact C¹ scalar function has zero integral. -/
theorem integral_spatialPartial_eq_zero {f : Space → ℝ}
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (i : Fin 3) :
    (∫ x : Space, spatialPartial i f x) = 0 := by
  have h := integration_by_parts hf (contDiff_const : ContDiff ℝ 1 (fun _ : Space => (1 : ℝ))) hs i
  simp [spatialPartial] at h
  exact h

/-- Conservative flux form of one component of the force difference integrates
to zero when its temporal velocity term is compact and solenoidal. -/
theorem integral_force_of_compact_momentum_balance
    {z : Space → Space} {flux : Fin 3 → Space → ℝ} {force : Space → ℝ}
    (hz : ContDiff ℝ 1 z) (hzc : HasCompactSupport z)
    (hzd : ∀ x, Comparator.divergence z x = 0)
    (hflux : ∀ i, ContDiff ℝ 1 (flux i))
    (hfluxc : ∀ i, HasCompactSupport (flux i))
    (j : Fin 3)
    (hbalance : ∀ x, force x = z x j + ∑ i, spatialPartial i (flux i) x) :
    (∫ x : Space, force x) = 0 := by
  have hzint : Integrable (fun x => z x j) :=
    (component_contDiff hz j).continuous.integrable_of_hasCompactSupport (component_compact hzc j)
  have hfi (i : Fin 3) : Integrable (spatialPartial i (flux i)) :=
    (partial_continuous (hflux i) i).integrable_of_hasCompactSupport (partial_compact (hfluxc i) i)
  simp_rw [hbalance]
  rw [integral_add hzint (integrable_finsetSum _ (fun i _ => hfi i))]
  rw [integral_component_eq_zero hz hzc hzd j]
  rw [integral_finsetSum _ (fun i _ => hfi i)]
  simp [integral_spatialPartial_eq_zero (hflux _) (hfluxc _)]

end NSFormalization.Paper3
