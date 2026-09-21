import NSFormalization.Section3.T23.NoSlipUniqueness
import NSFormalization.Section3.T23.PressureNormalization

/-!
# Proposition 3.17 on a bounded no-slip domain

`paper/revised/sections/03-torus.tex:539-540`:
"On a bounded domain, let $f=-\nabla\phi$ and impose homogeneous no-slip velocity.
In either case, any smooth solution with zero initial velocity is identically
zero on its classical lifespan."

The potential class is `ContDiff ℝ ∞ φ`, with no periodicity requirement.
The pairing is proved directly by boundary integration by parts. The energy
proof specializes the difference energy identity against the explicit rest
solution: its convection term is zero, so energy is nonincreasing from zero.
-/
noncomputable section
namespace NSFormalization.Section3.T24
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeScalar SpaceTimeField)
open NSFormalization.Section3.T23
open scoped ContDiff RealInnerProductSpace

/-- The negative spatial gradient, without a periodicity restriction. -/
def conservativeForceOmega (φ : SpaceTimeScalar) : SpaceTimeField :=
  fun z ↦ -pressureGradient φ z.1 z.2

/-- The pressure `-φ`, with its domain mean removed, balances the force. -/
def restSolutionOmega (ν : ℝ) (Ω : Set Space)
    (hΩ : IsBoundedBoxOrSmoothDomain Ω) (φ : SpaceTimeScalar)
    (hφ : ContDiff ℝ ∞ φ) (T : ℝ) (hT : 0 < T) :
    ClassicalSolutionOmega ν Ω 0 (conservativeForceOmega φ) T where
  velocity := 0
  pressure := domainNormalizePressure Ω (-φ)
  horizon_pos := hT
  velocity_smooth := ⟨univ, isOpen_univ, subset_univ _, contDiff_const.contDiffOn⟩
  pressure_smooth :=
    (show SmoothOnClosedSlab (Ico 0 T) Ω (-φ) from
      ⟨univ, isOpen_univ, subset_univ _, hφ.neg.contDiffOn⟩).domainNormalizePressure
        hΩ.2.1 hΩ.1.measurableSet
  initial := fun _ _ ↦ rfl
  divergence := by
    intro t ht x hx
    simp [spatialDivergence, spatialDerivative]
  momentum := by
    intro t ht x hx
    rw [residual_domainNormalizePressure]
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual,
      conservativeForceOmega, temporalDerivative, advection, spatialDerivative,
      spatialLaplacian, pressureGradient]
  no_slip := fun _ _ _ _ ↦ rfl
  pressure_gauge := by
    intro t ht
    apply domainNormalizePressure_integral hΩ.1 hΩ.2.1 hΩ.2.2.1
    have hc : ContinuousOn (fun x => (-φ) (t, x)) (closure Ω) :=
      (hφ.neg.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    exact (hc.integrableOn_compact hΩ.2.1.isCompact_closure).mono_set subset_closure

/-- The article's pairing proof, directly from incompressibility and no-slip. -/
theorem potential_pairingOmega
    (ν T : ℝ) (_hT : 0 < T) (Ω : Set Space)
    (hΩ : IsBoundedBoxOrSmoothDomain Ω) (φ : SpaceTimeScalar)
    (hφ : ContDiff ℝ ∞ φ)
    (S : ClassicalSolutionOmega ν Ω 0 (conservativeForceOmega φ) T)
    (t : ℝ) (ht : t ∈ Ico 0 T) :
    (∫ x in Ω, inner ℝ (conservativeForceOmega φ (t, x)) (S.velocity (t, x))) = 0 := by
  have h := (ibp_boundedDomain hΩ).integral_pressure_energy_zero hΩ.2.1
    hΩ.1.measurableSet (fun _ hx => S.velocity_smooth.contDiffAt_slice ht hx)
    (fun x _ => (hφ.comp (contDiff_const.prodMk contDiff_id)).contDiffAt)
    (S.no_slip t ht) (S.divergence t ht)
  simpa only [conservativeForceOmega, inner_neg_left, real_inner_comm,
    integral_neg, neg_eq_zero] using h

/-- Zero initial energy and nonpositive energy derivative force zero velocity. -/
theorem zero_from_restOmega
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (Ω : Set Space)
    (hΩ : IsBoundedBoxOrSmoothDomain Ω) (φ : SpaceTimeScalar)
    (hφ : ContDiff ℝ ∞ φ)
    (u : ClassicalSolutionOmega ν Ω 0 (conservativeForceOmega φ) T)
    (t : ℝ) (ht : t ∈ Ico 0 T) (x : Space) (hx : x ∈ Ω) :
    u.velocity (t, x) = 0 := by
  let v := restSolutionOmega ν Ω hΩ φ hφ T hT
  obtain ⟨b, htb, hb⟩ := exists_between ht.2
  let E := differenceEnergy Ω u.velocity v.velocity
  let D := fun s => ∫ y in Ω, ∑ i : Fin 3,
    ‖spatialDerivative (u.velocity - v.velocity) s y (coordinateVector i)‖ ^ 2
  have hd (s : ℝ) (hs : s ∈ Ioo 0 b) : HasDerivAt E (-2 * ν * D s) s := by
    have h := difference_energy_identity (ibp_boundedDomain hΩ) hΩ.1 hΩ.2.1 u v
      (show s ∈ Ioo 0 (min T T) by simpa using ⟨hs.1, hs.2.trans hb⟩)
    simpa [v, restSolutionOmega, spatialDerivative, E, D] using h
  have hi : E 0 = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    simp [u.initial y hy, v, restSolutionOmega]
  have hz := NavierStokes.PeriodicUniqueness.gronwall_zero (ht.1.trans htb.le)
    (differenceEnergy_continuousOn hΩ.2.1 hΩ.1.measurableSet u v
      (by simpa using hb)) hi
    (fun s _ => integral_nonneg fun y => sq_nonneg _) hd
    (show ∀ s ∈ Ioo 0 b, -2 * ν * D s ≤ 0 * E s from by
      intro s hs
      have hD : 0 ≤ D s := integral_nonneg fun y =>
        Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [mul_nonneg hν.le hD]) t ⟨ht.1, htb.le⟩
  exact eqOn_of_integral_norm_sub_sq_eq_zero hΩ.1
    (fun y hy => (u.velocity_smooth.contDiffAt_slice ht
      (subset_closure hy)).continuousAt.continuousWithinAt)
    continuousOn_const (difference_energy_integrable hΩ.2.1 u v (by simpa using ht)) hz hx

/-- The two bounded-domain clauses of Proposition 3.17. -/
structure ConservativeForcingOmegaAPI : Prop where
  potential_pairing :
    ∀ (ν T : ℝ), 0 < T → ∀ (Ω : Set Space), IsBoundedBoxOrSmoothDomain Ω →
      ∀ φ : SpaceTimeScalar, ContDiff ℝ ∞ φ →
        ∀ S : ClassicalSolutionOmega ν Ω 0 (conservativeForceOmega φ) T,
          ∀ t ∈ Ico 0 T,
            (∫ x in Ω, inner ℝ (conservativeForceOmega φ (t, x)) (S.velocity (t, x))) = 0
  zero_from_rest :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ (Ω : Set Space), IsBoundedBoxOrSmoothDomain Ω →
        ∀ φ : SpaceTimeScalar, ContDiff ℝ ∞ φ →
          ∀ S : ClassicalSolutionOmega ν Ω 0 (conservativeForceOmega φ) T,
            ∀ t ∈ Ico 0 T, ∀ x ∈ Ω, S.velocity (t, x) = 0

/-- Bounded no-slip conservative forcing, with all boundary premises discharged. -/
theorem conservativeForcingOmega : ConservativeForcingOmegaAPI where
  potential_pairing := potential_pairingOmega
  zero_from_rest := zero_from_restOmega
end NSFormalization.Section3.T24
