import NSFormalization.Paper1.PeriodicFourierDerivative

/-!
# Actual periodic Fourier reconstruction

The reconstruction theorem is Mathlib's
`UnitAddTorus.hasSum_mFourier_series_of_summable` and its pointwise corollary,
`Mathlib/Analysis/Fourier/AddCircleMulti.lean`, lines 318--332 in the pinned
checkout. The same theorem is used in the two-dimensional source adapter
`NavierStokes/SmoothFourierData.lean`, lines 457--479. Here it is applied in
three dimensions with the existing Paper 1 coefficient convention.

The canonical measurable representative `torusLift` is proved continuous
for continuous functions with the actual `UnitPeriods` property. Absolute
summability remains an explicit hypothesis; this module does not assert
that smoothness or an H2 energy bound implies it, nor does it prove a
critical Sobolev embedding.
-/

noncomputable section

namespace NSFormalization.Paper1

open Set Filter MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators Topology

/-- Coordinate periods imply invariance under every integer lattice translation. -/
theorem unitPeriods_integer_translate {E : Type*} {f : Space → E}
    (hp : UnitPeriods f) (k : PeriodicFrequency) (x : Space) :
    f (x + toSpace (fun i => (k i : ℝ))) = f x := by
  have hperiod (i : Fin 3) : Function.Periodic f ((k i) • coordinateVector i) :=
    (show Function.Periodic f (coordinateVector i) from fun y => hp y i).zsmul (k i)
  have hsum (S : Finset (Fin 3)) :
      Function.Periodic f (∑ i ∈ S, (k i) • coordinateVector i) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact fun y => by rw [add_zero]
    | @insert i S hi ih =>
        rw [Finset.sum_insert hi]
        exact (hperiod i).add_period ih
  have hvec : (∑ i : Fin 3, (k i) • coordinateVector i) =
      toSpace (fun i => (k i : ℝ)) := by
    ext j
    simp [coordinateVector, Pi.single_apply]
  rw [← hvec]
  exact hsum Finset.univ x

/-- Functions with unit coordinate periods are constant on the quotient fibers. -/
theorem unitPeriods_eq_of_torus_eq {E : Type*} {f : Space → E}
    (hp : UnitPeriods f) {a b : Coords}
    (hab : (fun i => (a i : UnitAddCircle)) = (fun i => (b i : UnitAddCircle))) :
    f (toSpace a) = f (toSpace b) := by
  have hdiff (i : Fin 3) : ∃ n : ℤ, (n : ℝ) = a i - b i := by
    have hzero : ((a i - b i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, congrFun hab i, sub_self]
    simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff 1).mp hzero
  choose k hk using hdiff
  have heq : toSpace a = toSpace b + toSpace (fun i => (k i : ℝ)) := by
    ext i
    simp only [PiLp.add_apply, toSpace_apply, hk i]
    ring
  rw [heq]
  exact unitPeriods_integer_translate hp k (toSpace b)

/-- The canonical torus lift agrees with the field at every physical point,
including the boundaries of the chosen fundamental domain. -/
theorem torusLift_coe_of_unitPeriods {E : Type*} {f : Space → E}
    (hp : UnitPeriods f) (x : Space) :
    torusLift f (fun i => (x i : UnitAddCircle)) = f x := by
  unfold torusLift
  have hz := (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).symm_apply_apply
    (fun i => (x i : UnitAddCircle))
  have h := unitPeriods_eq_of_torus_eq hp hz
  exact h

/-- Continuity descends through the product quotient; the representative map
itself need not be continuous. -/
theorem continuous_torusLift {f : Space → ℂ} (hf : Continuous f)
    (hp : UnitPeriods f) : Continuous (torusLift f) := by
  have hq : IsOpenQuotientMap (fun x : Coords => fun i => (x i : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ : Fin 3 =>
      (show IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) from
        QuotientAddGroup.isOpenQuotientMap_mk))
  apply hq.isQuotientMap.continuous_iff.mpr
  have heq : (torusLift f ∘ (fun x : Coords => fun i => (x i : UnitAddCircle))) =
      f ∘ toSpace := by
    funext x
    exact torusLift_coe_of_unitPeriods hp (toSpace x)
  rw [heq]
  exact hf.comp toSpace.continuous

/-- The actual continuous function on the quotient, in Paper 1 conventions. -/
def continuousTorusLift (f : Space → ℂ) (hf : Continuous f) (hp : UnitPeriods f) :
    C(PeriodicTorus, ℂ) := ⟨torusLift f, continuous_torusLift hf hp⟩

/-- Uniform Fourier reconstruction as convergence in the continuous-map norm. -/
theorem hasSum_periodicFourier_continuous {f : Space → ℂ} (hf : Continuous f)
    (hp : UnitPeriods f) (hc : Summable (periodicFourierCoeff f)) :
    HasSum (fun k : PeriodicFrequency =>
      periodicFourierCoeff f k • UnitAddTorus.mFourier k) (continuousTorusLift f hf hp) := by
  change HasSum (fun k => UnitAddTorus.mFourierCoeff
    (continuousTorusLift f hf hp) k • UnitAddTorus.mFourier k) _
  exact UnitAddTorus.hasSum_mFourier_series_of_summable
    (f := continuousTorusLift f hf hp) hc

/-- Pointwise reconstruction on the torus from the actual physical coefficients. -/
theorem hasSum_periodicFourier_torus {f : Space → ℂ} (hf : Continuous f)
    (hp : UnitPeriods f) (hc : Summable (periodicFourierCoeff f)) (z : PeriodicTorus) :
    HasSum (fun k : PeriodicFrequency =>
      UnitAddTorus.mFourier k z * periodicFourierCoeff f k) (torusLift f z) := by
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (f := continuousTorusLift f hf hp) hc z
  apply h.congr_fun
  intro k
  change UnitAddTorus.mFourier k z * periodicFourierCoeff f k =
    periodicFourierCoeff f k • UnitAddTorus.mFourier k z
  simp only [smul_eq_mul, mul_comm]

/-- Pointwise reconstruction at every point of physical Euclidean space. -/
theorem hasSum_periodicFourier_physical {f : Space → ℂ} (hf : Continuous f)
    (hp : UnitPeriods f) (hc : Summable (periodicFourierCoeff f)) (x : Space) :
    HasSum (fun k : PeriodicFrequency => periodicCharacter k x * periodicFourierCoeff f k)
      (f x) := by
  simpa only [periodicCharacter_eq_mFourier, torusLift_coe_of_unitPeriods hp] using
    hasSum_periodicFourier_torus hf hp hc (fun i => (x i : UnitAddCircle))

/-- The pointwise identity is accompanied by a genuine summability proof. -/
theorem periodicFourier_tsum_eq {f : Space → ℂ} (hf : Continuous f)
    (hp : UnitPeriods f) (hc : Summable (periodicFourierCoeff f)) (x : Space) :
    (∑' k : PeriodicFrequency, periodicCharacter k x * periodicFourierCoeff f k) = f x :=
  (hasSum_periodicFourier_physical hf hp hc x).tsum_eq

/-- Arbitrary finite Fourier partial sums converge at each physical point,
with finite subsets ordered by inclusion. -/
theorem tendsto_periodicFourier_partialSums {f : Space → ℂ} (hf : Continuous f)
    (hp : UnitPeriods f) (hc : Summable (periodicFourierCoeff f)) (x : Space) :
    Tendsto (fun S : Finset PeriodicFrequency =>
      ∑ k ∈ S, periodicCharacter k x * periodicFourierCoeff f k) atTop (𝓝 (f x)) :=
  hasSum_periodicFourier_physical hf hp hc x

/-- Uniform approximation by sufficiently large finite Fourier sums. The same
frequency set works for every physical point of the periodic field. -/
theorem exists_periodicFourier_partialSum_uniform {f : Space → ℂ} (hf : Continuous f)
    (hp : UnitPeriods f) (hc : Summable (periodicFourierCoeff f))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset PeriodicFrequency, ∀ T : Finset PeriodicFrequency, S ⊆ T →
      ∀ x : Space, ‖(∑ k ∈ T, periodicCharacter k x * periodicFourierCoeff f k) - f x‖ < ε := by
  have h := hasSum_periodicFourier_continuous hf hp hc
  have hevent := (Metric.tendsto_nhds.mp h) ε hε
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨S, fun T hT x => ?_⟩
  have hb := (ContinuousMap.norm_coe_le_norm
    ((∑ k ∈ T, periodicFourierCoeff f k • UnitAddTorus.mFourier k) -
      continuousTorusLift f hf hp) (fun i => (x i : UnitAddCircle))).trans_lt
        (show ‖((∑ k ∈ T, periodicFourierCoeff f k • UnitAddTorus.mFourier k) -
          continuousTorusLift f hf hp)‖ < ε from by
            simpa only [dist_eq_norm] using hS T hT)
  simpa only [ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    continuousTorusLift, ContinuousMap.coe_mk, torusLift_coe_of_unitPeriods hp,
    periodicCharacter_eq_mFourier, smul_eq_mul, mul_comm] using hb

/-- The physical field is bounded by the absolutely convergent coefficient sum. -/
theorem norm_le_tsum_periodicFourierCoeff {f : Space → ℂ} (hf : Continuous f)
    (hp : UnitPeriods f) (hc : Summable (periodicFourierCoeff f)) (x : Space) :
    ‖f x‖ ≤ ∑' k : PeriodicFrequency, ‖periodicFourierCoeff f k‖ := by
  rw [← periodicFourier_tsum_eq hf hp hc x]
  have hmode (k : PeriodicFrequency) : ‖periodicCharacter k x‖ = 1 := by
    rw [periodicCharacter_eq_mFourier]
    change ‖∏ i : Fin 3, fourier (k i) (x i : UnitAddCircle)‖ = 1
    simp only [norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]
  have hn : Summable (fun k : PeriodicFrequency =>
      ‖periodicCharacter k x * periodicFourierCoeff f k‖) := by
    simpa only [norm_mul, hmode, one_mul] using hc.norm
  simpa only [norm_mul, hmode, one_mul] using norm_tsum_le_tsum_norm hn

end NSFormalization.Paper1
