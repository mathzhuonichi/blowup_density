import NSFormalization.Section3.T12.CriticalL3
import NSFormalization.Section3.T10.Parseval
import NSFormalization.Section3.T10.DatumBasics
import NSFormalization.Paper1.PeriodicFiniteL3

/-!
# T12 U4b: the verbatim `velocityCriticalL3` by torus Fourier-truncation density

Lane 396 proved the smooth mean-zero form `velocityCriticalL3_smooth`
(`Section3/T12/CriticalL3.lean`).  The API field
(`research/T12/probes/api_on_canonical.lean:148-151`) quantifies over
`MemPeriodicHomogeneous (1/2) v`, which carries **no smoothness**, while both
analytic inputs of the smooth proof (`Cutoff.memHInfty_cutoffMul` and
`CutoffGagliardo.cutoff_gagliardo_half`) require a smooth field.  This module
closes that gap by the density route of `research/T12/T12_SPLIT.md` U4, option
(A) (symmetric Fourier truncation) rather than (B) (mollification):

1. **§1-§2** For a finite frequency set `S` closed under `k ↦ -k`, the physical
   partial Fourier sum `truncField v S` — the real part of
   `Paper1.finitePeriodicFourierSum` taken componentwise — is smooth
   (`contDiff_truncField`), periodic (`isPeriodicSpatial_truncField`) and has
   exactly the restricted Fourier datum
   (`periodicFourierCoeff_truncField`).  Realness of the partial sum uses the
   conjugate symmetry `T10.periodicFourierCoeff_real_neg` of the coefficients of
   a real field together with `S = -S`, so the `.re` is not a truncation of the
   data.
2. **§3** On the symmetric boxes `freqBox N = {k : ∀ i, |k i| ≤ N}` (cofinal in
   the finite subsets of `ℤ³`, `tendsto_freqBox`) the truncation is mean-zero
   (`isMeanZeroT_truncField`; the zero mode of a mean-zero field vanishes), and
   the homogeneous `Ḣ^s(T³)` extended norm does not increase
   (`periodicHomogeneousENorm_truncField_le`): the datum of the truncation is
   the `SpectralGap.reweightDatum` of the datum of `v` by the indicator
   multiplier of `S`, of modulus `≤ 1` and even because `S = -S`.
3. **§4** `truncField v (freqBox N) → v` in `L²(T³)`
   (`tendsto_eLpNorm_truncField_sub`): componentwise this is Mathlib's
   `UnitAddTorus.hasSum_mFourier_series_L2` for the Hilbert basis
   `mFourierBasis`, composed with the cofinality of the boxes; the three
   components are recombined by `eLpNorm_sum_le` and `‖x‖ ≤ ∑ i, |x i|`.
4. **§4b** `memPeriodicHomogeneous_of_smooth` — smooth mean-zero periodic fields
   really do lie in the class the API field quantifies over (so the hypothesis is
   not vacuous).
5. **§5** `L²` convergence gives convergence in measure
   (`tendstoInMeasure_of_tendsto_eLpNorm`), hence a.e. convergence along a
   subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`), and the lower
   semicontinuity `Lp.eLpNorm_lim_le_liminf_eLpNorm` of `eLpNorm · 3` — which
   holds for an arbitrary measure — turns the uniform bound
   `velocityCriticalL3_smooth (truncField v (freqBox N))` into the verbatim
   `velocityCriticalL3`.  The constant is unchanged: `CcriticalHalf`.

No `sorry`, no `axiom`, no `native_decide`, no `maxHeartbeats` override, no named
goal input; every declaration reduces to `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (Coords toSpace)
open NSFormalization.Section3.T10
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Paper1 (periodicCharacter periodicCharacter_eq_mFourier
  periodicCharacter_smooth periodicCharacter_periodic finitePeriodicFourierSum
  finitePeriodicFourierSum_apply)
open scoped ContDiff ENNReal BigOperators Topology ComplexConjugate

/-! ## §1  Finite Fourier sums and their coefficients -/

private theorem integrable_mFourier (k : PeriodicFrequency) :
    Integrable (fun z : PeriodicTorus ↦ UnitAddTorus.mFourier k z) periodicTorusMeasure := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (UnitAddTorus.mFourier k).continuous.aestronglyMeasurable ?_
  filter_upwards with z
  simpa only [UnitAddTorus.mFourier_norm] using
    (UnitAddTorus.mFourier k).norm_coe_le_norm z

/-- The canonical torus lift of a physical finite Fourier sum is the
corresponding finite combination of Mathlib's torus monomials. -/
theorem torusLift_finitePeriodicFourierSum (c : PeriodicFrequency → ℂ)
    (S : Finset PeriodicFrequency) (z : PeriodicTorus) :
    torusLift (finitePeriodicFourierSum c S) z
      = ∑ k ∈ S, UnitAddTorus.mFourier k z * c k := by
  have hz := (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).symm_apply_apply z
  change (fun i ↦ (((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val i) :
    AddCircle (1 : ℝ))) = z at hz
  simp only [NSFormalization.Paper1.torusLift, finitePeriodicFourierSum_apply,
    periodicCharacter_eq_mFourier, NavierStokes.PeriodicIntegration.toSpace_apply, hz]

/-- The Fourier coefficients of a finite Fourier sum are the prescribed
coefficients on the frequency set and zero elsewhere. -/
theorem periodicFourierCoeff_finitePeriodicFourierSum (c : PeriodicFrequency → ℂ)
    (S : Finset PeriodicFrequency) (m : PeriodicFrequency) :
    periodicFourierCoeff (finitePeriodicFourierSum c S) m = if m ∈ S then c m else 0 := by
  change UnitAddTorus.mFourierCoeff (torusLift (finitePeriodicFourierSum c S)) m = _
  unfold UnitAddTorus.mFourierCoeff
  have hfun : ∀ z : PeriodicTorus,
      UnitAddTorus.mFourier (-m) z • torusLift (finitePeriodicFourierSum c S) z
        = ∑ k ∈ S, UnitAddTorus.mFourier (-m + k) z * c k := by
    intro z
    rw [torusLift_finitePeriodicFourierSum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [UnitAddTorus.mFourier_add, mul_assoc]
  rw [integral_congr_ae (Filter.Eventually.of_forall hfun),
    integral_finsetSum S (fun k _ ↦ (integrable_mFourier (-m + k)).mul_const (c k))]
  have hterm : ∀ k : PeriodicFrequency,
      (∫ z : PeriodicTorus, UnitAddTorus.mFourier (-m + k) z * c k ∂periodicTorusMeasure)
        = if k = m then c k else 0 := by
    intro k
    rw [integral_mul_const, integral_mFourier]
    by_cases hk : k = m
    · subst hk; simp
    · have hne : ¬ (-m + k = 0) := fun h ↦ hk (neg_add_eq_zero.mp h).symm
      simp [hne, hk]
  simp only [hterm]
  exact Finset.sum_ite_eq' S m c

/-! ## §2  The symmetric Fourier truncation of a real periodic field -/

/-- The physical character is conjugate-symmetric in the frequency. -/
theorem periodicCharacter_neg (k : PeriodicFrequency) (x : Space) :
    periodicCharacter (-k) x = conj (periodicCharacter k x) := by
  rw [periodicCharacter_eq_mFourier, periodicCharacter_eq_mFourier]
  exact UnitAddTorus.mFourier_neg

/-- A partial Fourier sum of a **real** field over a frequency set closed under
negation is real-valued. -/
theorem conj_finitePeriodicFourierSum_real (f : Space → ℝ)
    (S : Finset PeriodicFrequency) (hS : ∀ k ∈ S, -k ∈ S) (x : Space) :
    conj (finitePeriodicFourierSum
        (fun k ↦ periodicFourierCoeff (fun y ↦ ((f y : ℝ) : ℂ)) k) S x)
      = finitePeriodicFourierSum
        (fun k ↦ periodicFourierCoeff (fun y ↦ ((f y : ℝ) : ℂ)) k) S x := by
  classical
  set c : PeriodicFrequency → ℂ :=
    fun k ↦ periodicFourierCoeff (fun y ↦ ((f y : ℝ) : ℂ)) k with hc
  have himg : S.image (fun k : PeriodicFrequency ↦ -k) = S := by
    apply Finset.Subset.antisymm
    · intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      exact hS j hj
    · intro k hk
      exact Finset.mem_image.mpr ⟨-k, hS k hk, neg_neg k⟩
  have hinj : Set.InjOn (fun k : PeriodicFrequency ↦ -k) (S : Set PeriodicFrequency) := by
    intro a _ b _ h
    simpa using congrArg Neg.neg h
  have hconj : ∀ k : PeriodicFrequency, conj (c k) = c (-k) := by
    intro k
    simpa [hc, Complex.star_def] using
      (NSFormalization.Section3.T10.periodicFourierCoeff_real_neg f k).symm
  simp only [finitePeriodicFourierSum_apply]
  calc conj (∑ k ∈ S, periodicCharacter k x * c k)
      = ∑ k ∈ S, periodicCharacter (-k) x * c (-k) := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun k _ ↦ ?_)
        rw [map_mul, ← periodicCharacter_neg, hconj k]
    _ = ∑ k ∈ S.image (fun k : PeriodicFrequency ↦ -k), periodicCharacter k x * c k :=
        (Finset.sum_image (g := fun k : PeriodicFrequency ↦ -k)
          (f := fun k ↦ periodicCharacter k x * c k) hinj).symm
    _ = ∑ k ∈ S, periodicCharacter k x * c k := by rw [himg]

/-- `01-introduction.tex:105-109`: the symmetric Fourier truncation of a
periodic vector field to the frequency set `S`, taken componentwise. -/
def truncField (v : SpatialField) (S : Finset PeriodicFrequency) : SpatialField :=
  fun x ↦ WithLp.toLp 2 (fun i ↦
    (finitePeriodicFourierSum
      (fun k ↦ periodicFourierCoeff (fun y ↦ ((v y i : ℝ) : ℂ)) k) S x).re)

theorem truncField_apply (v : SpatialField) (S : Finset PeriodicFrequency)
    (x : Space) (i : Fin 3) :
    truncField v S x i =
      (finitePeriodicFourierSum
        (fun k ↦ periodicFourierCoeff (fun y ↦ ((v y i : ℝ) : ℂ)) k) S x).re := rfl

/-- Over a negation-closed frequency set the complexified component of the
truncation is exactly the partial Fourier sum. -/
theorem ofReal_truncField_apply (v : SpatialField) (S : Finset PeriodicFrequency)
    (hS : ∀ k ∈ S, -k ∈ S) (i : Fin 3) (x : Space) :
    ((truncField v S x i : ℝ) : ℂ)
      = finitePeriodicFourierSum
          (fun k ↦ periodicFourierCoeff (fun y ↦ ((v y i : ℝ) : ℂ)) k) S x := by
  rw [truncField_apply]
  exact Complex.conj_eq_iff_re.mp
    (conj_finitePeriodicFourierSum_real (fun y ↦ v y i) S hS x)

/-- The Fourier datum of the truncation is the restriction of the datum of `v`. -/
theorem periodicFourierCoeff_truncField (v : SpatialField) (S : Finset PeriodicFrequency)
    (hS : ∀ k ∈ S, -k ∈ S) (i : Fin 3) (m : PeriodicFrequency) :
    periodicFourierCoeff (fun y ↦ ((truncField v S y i : ℝ) : ℂ)) m
      = if m ∈ S then periodicFourierCoeff (fun y ↦ ((v y i : ℝ) : ℂ)) m else 0 := by
  rw [show (fun y ↦ ((truncField v S y i : ℝ) : ℂ))
      = finitePeriodicFourierSum
          (fun k ↦ periodicFourierCoeff (fun y ↦ ((v y i : ℝ) : ℂ)) k) S
    from funext (fun y ↦ ofReal_truncField_apply v S hS i y)]
  exact periodicFourierCoeff_finitePeriodicFourierSum _ _ _

private theorem finitePeriodicFourierSum_periodic (c : PeriodicFrequency → ℂ)
    (S : Finset PeriodicFrequency) (x : Space) (i : Fin 3) :
    finitePeriodicFourierSum c S (x + coordinateVector i) = finitePeriodicFourierSum c S x := by
  simp only [finitePeriodicFourierSum_apply]
  exact Finset.sum_congr rfl (fun k _ ↦ by rw [periodicCharacter_periodic k x i])

theorem isPeriodicSpatial_truncField (v : SpatialField) (S : Finset PeriodicFrequency) :
    IsPeriodicSpatial (truncField v S) := by
  intro x i
  unfold truncField
  simp only [finitePeriodicFourierSum_periodic]

theorem contDiff_truncField (v : SpatialField) (S : Finset PeriodicFrequency) :
    ContDiff ℝ ∞ (truncField v S) := by
  rw [contDiff_euclidean]
  intro i
  have h : ContDiff ℝ ∞ (fun x : Space ↦
      finitePeriodicFourierSum
        (fun k ↦ periodicFourierCoeff (fun y ↦ ((v y i : ℝ) : ℂ)) k) S x) := by
    simp only [finitePeriodicFourierSum_apply]
    exact ContDiff.sum (fun k _ ↦ (periodicCharacter_smooth k).mul contDiff_const)
  exact Complex.reCLM.contDiff.comp h

theorem smoothPeriodicT_truncField (v : SpatialField) (S : Finset PeriodicFrequency) :
    SmoothPeriodicT (truncField v S) :=
  ⟨contDiff_truncField v S, isPeriodicSpatial_truncField v S⟩

/-! ## §3  The frequency boxes, mean zero, and the homogeneous-norm contraction -/

/-- The symmetric frequency box `{k : ∀ i, |k i| ≤ N}`. -/
def freqBox (N : ℕ) : Finset PeriodicFrequency :=
  Fintype.piFinset (fun _ : Fin 3 ↦ Finset.Icc (-(N : ℤ)) (N : ℤ))

theorem mem_freqBox {N : ℕ} {k : PeriodicFrequency} :
    k ∈ freqBox N ↔ ∀ i : Fin 3, -(N : ℤ) ≤ k i ∧ k i ≤ (N : ℤ) := by
  simp [freqBox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem freqBox_neg_closed (N : ℕ) : ∀ k ∈ freqBox N, -k ∈ freqBox N := by
  intro k hk
  rw [mem_freqBox] at hk ⊢
  intro i
  have h := hk i
  refine ⟨?_, ?_⟩
  · show -(N : ℤ) ≤ -(k i)
    linarith [h.2]
  · show -(k i) ≤ (N : ℤ)
    linarith [h.1]

theorem freqBox_mono {N M : ℕ} (h : N ≤ M) : freqBox N ⊆ freqBox M := by
  intro k hk
  rw [mem_freqBox] at hk ⊢
  intro i
  have hNM : (N : ℤ) ≤ (M : ℤ) := Int.ofNat_le.mpr h
  exact ⟨le_trans (by linarith) (hk i).1, le_trans (hk i).2 hNM⟩

theorem exists_freqBox_superset (S : Finset PeriodicFrequency) :
    ∃ N : ℕ, S ⊆ freqBox N := by
  classical
  refine ⟨S.sup (fun k ↦ Finset.univ.sup (fun i : Fin 3 ↦ (k i).natAbs)), ?_⟩
  intro k hk
  rw [mem_freqBox]
  intro i
  have h1 : (k i).natAbs ≤ Finset.univ.sup (fun j : Fin 3 ↦ (k j).natAbs) :=
    Finset.le_sup (f := fun j : Fin 3 ↦ (k j).natAbs) (Finset.mem_univ i)
  have h2 : Finset.univ.sup (fun j : Fin 3 ↦ (k j).natAbs)
      ≤ S.sup (fun m ↦ Finset.univ.sup (fun j : Fin 3 ↦ (m j).natAbs)) :=
    Finset.le_sup (f := fun m : PeriodicFrequency ↦
      Finset.univ.sup (fun j : Fin 3 ↦ (m j).natAbs)) hk
  have habs : |k i| ≤ ((S.sup (fun m ↦ Finset.univ.sup
      (fun j : Fin 3 ↦ (m j).natAbs)) : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast le_trans h1 h2
  exact ⟨(abs_le.mp habs).1, (abs_le.mp habs).2⟩

theorem tendsto_freqBox : Tendsto freqBox atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro S
  obtain ⟨N, hN⟩ := exists_freqBox_superset S
  exact ⟨N, fun M hM ↦ le_trans hN (freqBox_mono hM)⟩

theorem integrable_torusLift_truncField (v : SpatialField) (S : Finset PeriodicFrequency) :
    Integrable (torusLift (truncField v S)) periodicTorusMeasure :=
  (memLp_torusLift_vector (contDiff_truncField v S).continuous 1).integrable le_rfl

/-- The truncation of a mean-zero field is mean-zero. -/
theorem isMeanZeroT_truncField (v : SpatialField)
    (hL : MemLp (torusLift v) 2 periodicTorusMeasure) (hmean : IsMeanZeroT v)
    (S : Finset PeriodicFrequency) (hS : ∀ k ∈ S, -k ∈ S) :
    IsMeanZeroT (truncField v S) := by
  have hintv : Integrable (torusLift v) periodicTorusMeasure := hL.integrable (by norm_num)
  have hcomp : ∀ i : Fin 3, meanT (truncField v S) i = 0 := by
    intro i
    have hv0 : periodicFourierCoeff (fun y ↦ ((v y i : ℝ) : ℂ)) 0 = 0 := by
      rw [periodicFourierCoeff_zero_eq_mean_component hintv i, hmean]
      simp
    have h0 := periodicFourierCoeff_zero_eq_mean_component
      (integrable_torusLift_truncField v S) i
    rw [periodicFourierCoeff_truncField v S hS i 0, hv0] at h0
    have : ((meanT (truncField v S) i : ℝ) : ℂ) = 0 := by
      rw [← h0]; split_ifs <;> rfl
    exact_mod_cast this
  ext i
  simpa using hcomp i

/-- Truncating to a negation-closed frequency set does not increase the
homogeneous `Ḣ^s(T³)` extended norm. -/
theorem periodicHomogeneousENorm_truncField_le (s : ℝ) (v : SpatialField)
    (hL : MemLp (torusLift v) 2 periodicTorusMeasure) (hmean : IsMeanZeroT v)
    (S : Finset PeriodicFrequency) (hS : ∀ k ∈ S, -k ∈ S) :
    periodicHomogeneousENorm s (truncField v S) ≤ periodicHomogeneousENorm s v := by
  classical
  unfold periodicHomogeneousENorm
  refine le_iInf (fun A ↦ ?_)
  set w : PeriodicFrequency → ℝ := fun k ↦ if k ∈ S then 1 else 0 with hw
  have hbound : ∀ k, |w k| ≤ 1 := by
    intro k
    simp only [hw]
    split_ifs <;> norm_num
  have heven : ∀ k, w (-k) = w k := by
    intro k
    simp only [hw]
    by_cases hk : k ∈ S
    · simp [hk, hS k hk]
    · have hnk : -k ∉ S := fun h ↦ hk (by simpa using hS (-k) h)
      simp [hk, hnk]
  have hmem0 : reweightDatum w 1 zero_le_one hbound A.1.1 ∈ realPeriodicSubmodule :=
    reweightDatum_real w 1 zero_le_one hbound heven A.1
  have hdatum : IsPeriodicHomogeneousDatum s (truncField v S)
      ⟨reweightDatum w 1 zero_le_one hbound A.1.1, hmem0⟩ := by
    refine ⟨isPeriodicSpatial_truncField v S, integrable_torusLift_truncField v S,
      isMeanZeroT_truncField v hL hmean S hS, ?_⟩
    intro i k
    show reweightDatum w 1 zero_le_one hbound A.1.1 i k
        = (homogeneousDatumWeight s k : ℂ) •
          periodicFourierCoeff (fun y ↦ ((truncField v S y i : ℝ) : ℂ)) k
    rw [reweightDatum_apply, A.2.2.2.2 i k, periodicFourierCoeff_truncField v S hS i k]
    by_cases hk : k ∈ S <;> simp [hw, hk]
  refine le_trans
    (iInf_le_of_le ⟨⟨reweightDatum w 1 zero_le_one hbound A.1.1, hmem0⟩, hdatum⟩ le_rfl) ?_
  have hnorm : ‖reweightDatum w 1 zero_le_one hbound A.1.1‖ₑ ≤ ‖A.1.1‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      (by simpa only [one_mul] using reweightDatum_norm_le w 1 zero_le_one hbound A.1.1)
  exact hnorm

/-! ## §4  `L²(T³)` convergence of the truncations -/

private theorem coeFn_finset_smul_mFourierLp (c : PeriodicFrequency → ℂ)
    (S : Finset PeriodicFrequency) :
    ⇑(∑ k ∈ S, c k • UnitAddTorus.mFourierLp (d := Fin 3) 2 k)
      =ᵐ[periodicTorusMeasure] torusLift (finitePeriodicFourierSum c S) := by
  have hrw : (∑ k ∈ S, c k • UnitAddTorus.mFourierLp (d := Fin 3) 2 k)
      = ContinuousMap.toLp (E := ℂ) 2 periodicTorusMeasure ℂ
          (∑ k ∈ S, c k • UnitAddTorus.mFourier k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl
      (fun k _ ↦ (map_smul (ContinuousMap.toLp (E := ℂ) 2 periodicTorusMeasure ℂ)
        (c k) (UnitAddTorus.mFourier k)).symm)
  rw [hrw]
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (𝕜 := ℂ) (μ := periodicTorusMeasure)
    (p := 2) (∑ k ∈ S, c k • UnitAddTorus.mFourier k)] with z hz
  rw [hz, torusLift_finitePeriodicFourierSum]
  simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl (fun k _ ↦ mul_comm _ _)

private theorem tendsto_eLpNorm_component (v : SpatialField)
    (hL : MemLp (torusLift v) 2 periodicTorusMeasure) (i : Fin 3) :
    Tendsto (fun N : ℕ ↦ eLpNorm
        (fun z ↦ ((torusLift (truncField v (freqBox N)) z i : ℝ) : ℂ)
          - ((torusLift v z i : ℝ) : ℂ)) 2 periodicTorusMeasure) atTop (𝓝 0) := by
  classical
  set f : Space → ℂ := fun y ↦ ((v y i : ℝ) : ℂ) with hfdef
  have hfL : MemLp (torusLift f) 2 periodicTorusMeasure := memLp_torusLift_component v hL i
  set c : PeriodicFrequency → ℂ := fun k ↦ periodicFourierCoeff f k with hcdef
  set F : Lp ℂ 2 periodicTorusMeasure := hfL.toLp (torusLift f) with hFdef
  have hcoeff : ∀ k : PeriodicFrequency,
      UnitAddTorus.mFourierCoeff (⇑F) k = c k := by
    intro k
    rw [← UnitAddTorus.mFourierBasis_repr]
    exact fourier_repr_toLp f hfL k
  have hsum : HasSum (fun k ↦ c k • UnitAddTorus.mFourierLp (d := Fin 3) 2 k) F := by
    have h := UnitAddTorus.hasSum_mFourier_series_L2 F
    simpa only [hcoeff] using h
  have htend : Tendsto
      (fun N : ℕ ↦ ∑ k ∈ freqBox N, c k • UnitAddTorus.mFourierLp (d := Fin 3) 2 k)
      atTop (𝓝 F) := hsum.comp tendsto_freqBox
  have heLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun N : ℕ ↦ ∑ k ∈ freqBox N, c k • UnitAddTorus.mFourierLp (d := Fin 3) 2 k) F).mp htend
  refine heLp.congr (fun N ↦ ?_)
  refine eLpNorm_congr_ae ?_
  filter_upwards [coeFn_finset_smul_mFourierLp c (freqBox N), hfL.coeFn_toLp] with z h1 h2
  show (⇑(∑ k ∈ freqBox N, c k • UnitAddTorus.mFourierLp (d := Fin 3) 2 k)) z - (⇑F) z = _
  rw [h1, h2]
  exact congrArg (fun t ↦ t - ((torusLift v z i : ℝ) : ℂ))
    (ofReal_truncField_apply v (freqBox N) (freqBox_neg_closed N) i _).symm

private theorem norm_le_sum_abs (x : Space) : ‖x‖ ≤ ∑ i : Fin 3, |x i| := by
  rw [EuclideanSpace.norm_eq]
  have h1 : ∑ i : Fin 3, ‖x i‖ ^ 2 ≤ (∑ i : Fin 3, |x i|) ^ 2 := by
    simp only [Fin.sum_univ_three, Real.norm_eq_abs]
    nlinarith [abs_nonneg (x 0), abs_nonneg (x 1), abs_nonneg (x 2)]
  calc Real.sqrt (∑ i : Fin 3, ‖x i‖ ^ 2) ≤ Real.sqrt ((∑ i : Fin 3, |x i|) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = ∑ i : Fin 3, |x i| := Real.sqrt_sq (by positivity)

/-- The symmetric Fourier truncations converge to `v` in `L²(T³)`. -/
theorem tendsto_eLpNorm_truncField_sub (v : SpatialField)
    (hL : MemLp (torusLift v) 2 periodicTorusMeasure) :
    Tendsto (fun N : ℕ ↦ eLpNorm
        (fun z ↦ torusLift (truncField v (freqBox N)) z - torusLift v z) 2 periodicTorusMeasure)
      atTop (𝓝 0) := by
  have hmemT : ∀ N : ℕ, MemLp (torusLift (truncField v (freqBox N))) 2 periodicTorusMeasure :=
    fun N ↦ memLp_torusLift_vector (contDiff_truncField v (freqBox N)).continuous 2
  have hmeas : ∀ (N : ℕ) (i : Fin 3), AEStronglyMeasurable
      (fun z : PeriodicTorus ↦ ‖((torusLift (truncField v (freqBox N)) z i : ℝ) : ℂ)
        - ((torusLift v z i : ℝ) : ℂ)‖) periodicTorusMeasure := by
    intro N i
    exact (((memLp_torusLift_component _ (hmemT N) i).aestronglyMeasurable).sub
      ((memLp_torusLift_component v hL i).aestronglyMeasurable)).norm
  have hbound : ∀ N : ℕ,
      eLpNorm (fun z ↦ torusLift (truncField v (freqBox N)) z - torusLift v z) 2
          periodicTorusMeasure
        ≤ ∑ i : Fin 3, eLpNorm
            (fun z ↦ ((torusLift (truncField v (freqBox N)) z i : ℝ) : ℂ)
              - ((torusLift v z i : ℝ) : ℂ)) 2 periodicTorusMeasure := by
    intro N
    have hstep : eLpNorm (fun z ↦ torusLift (truncField v (freqBox N)) z - torusLift v z) 2
        periodicTorusMeasure
          ≤ eLpNorm (∑ i : Fin 3, fun z : PeriodicTorus ↦
              ‖((torusLift (truncField v (freqBox N)) z i : ℝ) : ℂ)
                - ((torusLift v z i : ℝ) : ℂ)‖) 2 periodicTorusMeasure := by
      refine eLpNorm_mono (fun z ↦ ?_)
      have hnn : (0 : ℝ) ≤ ∑ i : Fin 3,
          ‖((torusLift (truncField v (freqBox N)) z i : ℝ) : ℂ)
            - ((torusLift v z i : ℝ) : ℂ)‖ := by positivity
      rw [Finset.sum_apply, Real.norm_eq_abs, abs_of_nonneg hnn]
      refine le_trans (norm_le_sum_abs _) (le_of_eq (Finset.sum_congr rfl (fun i _ ↦ ?_)))
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rfl
    refine hstep.trans ?_
    refine le_trans (eLpNorm_sum_le (fun i _ ↦ hmeas N i) one_le_two) ?_
    exact le_of_eq (Finset.sum_congr rfl (fun i _ ↦ eLpNorm_norm _))
  have hsum : Tendsto (fun N : ℕ ↦ ∑ i : Fin 3, eLpNorm
      (fun z ↦ ((torusLift (truncField v (freqBox N)) z i : ℝ) : ℂ)
        - ((torusLift v z i : ℝ) : ℂ)) 2 periodicTorusMeasure) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin 3))
      (fun i _ ↦ tendsto_eLpNorm_component v hL i)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) hbound

/-! ## §4b  Smooth mean-zero periodic fields lie in the homogeneous class -/

/-- The ratio of the homogeneous to the inhomogeneous Fourier weight. -/
private def weightRatio (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  homogeneousDatumWeight s k / periodicFrequencyWeight k ^ (s / 2)

private theorem periodicFrequencyWeight_rpow_pos (s : ℝ) (k : PeriodicFrequency) :
    0 < periodicFrequencyWeight k ^ (s / 2) :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (one_le_fourierWeight k)) _

private theorem homogeneousDatumWeight_nonneg' (s : ℝ) (k : PeriodicFrequency) :
    0 ≤ homogeneousDatumWeight s k := by
  unfold homogeneousDatumWeight
  split_ifs with h
  · exact le_rfl
  · refine Real.rpow_nonneg ?_ _
    unfold periodicAngularFrequencySq
    positivity

private theorem weightRatio_abs_le_one (s : ℝ) (hs : 0 ≤ s) (k : PeriodicFrequency) :
    |weightRatio s k| ≤ 1 := by
  have hpos := periodicFrequencyWeight_rpow_pos s k
  have hnn : 0 ≤ weightRatio s k :=
    div_nonneg (homogeneousDatumWeight_nonneg' s k) hpos.le
  rw [abs_of_nonneg hnn, weightRatio, div_le_one hpos]
  exact homogeneousDatumWeight_le_periodicFrequencyWeight_rpow s hs k

private theorem weightRatio_neg (s : ℝ) (k : PeriodicFrequency) :
    weightRatio s (-k) = weightRatio s k := by
  have h1 : homogeneousDatumWeight s (-k) = homogeneousDatumWeight s k := by
    simp only [homogeneousDatumWeight, neg_eq_zero, periodicAngularFrequencySq]
    simp
  rw [weightRatio, weightRatio, h1, fourierWeight_neg]

/-- Every smooth mean-zero periodic field has a finite homogeneous datum at each
nonnegative order, hence lies in the class the API field quantifies over.  This
makes the hypothesis of `velocityCriticalL3` satisfiable at nonzero fields. -/
theorem memPeriodicHomogeneous_of_smooth (s : ℝ) (hs : 0 ≤ s) (v : SpatialField)
    (hv : SmoothPeriodicT v) (hmean : IsMeanZeroT v) :
    MemPeriodicHomogeneous s v := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum s hv.1 hv.2
  refine ⟨hv.2, memLp_torusLift_vector hv.1.continuous 2, hmean, ?_⟩
  have hbound := weightRatio_abs_le_one s hs
  have hmem0 : reweightDatum (weightRatio s) 1 zero_le_one hbound A.1
      ∈ realPeriodicSubmodule :=
    reweightDatum_real (weightRatio s) 1 zero_le_one hbound (weightRatio_neg s) A
  have hdatum : IsPeriodicHomogeneousDatum s v
      ⟨reweightDatum (weightRatio s) 1 zero_le_one hbound A.1, hmem0⟩ := by
    refine ⟨hv.2, hA.2.1, hmean, ?_⟩
    intro i k
    show reweightDatum (weightRatio s) 1 zero_le_one hbound A.1 i k
        = (homogeneousDatumWeight s k : ℂ) •
          periodicFourierCoeff (fun y ↦ ((v y i : ℝ) : ℂ)) k
    have hscal : weightRatio s k * periodicFrequencyWeight k ^ (s / 2)
        = homogeneousDatumWeight s k := by
      rw [weightRatio, div_mul_cancel₀ _ (periodicFrequencyWeight_rpow_pos s k).ne']
    rw [reweightDatum_apply, hA.2.2 i k]
    simp only [smul_eq_mul, Complex.real_smul]
    rw [← mul_assoc, ← Complex.ofReal_mul, hscal]
  unfold periodicHomogeneousENorm
  exact ne_top_of_le_ne_top enorm_ne_top
    (iInf_le_of_le
      ⟨⟨reweightDatum (weightRatio s) 1 zero_le_one hbound A.1, hmem0⟩, hdatum⟩ le_rfl)

/-! ## §5  The verbatim `velocityCriticalL3` -/

/-- **T12 U4, `appendix-b-embeddings.tex:20-31`.**  For every mean-zero periodic
field with a finite homogeneous `Ḣ^{1/2}(T³)` datum, the physical `L³(T³)` norm
is bounded by `CcriticalHalf` times the homogeneous norm.  The smooth case is
`velocityCriticalL3_smooth`; the general case follows by symmetric Fourier
truncation, whose homogeneous norm does not increase
(`periodicHomogeneousENorm_truncField_le`), which converges in `L²(T³)`
(`tendsto_eLpNorm_truncField_sub`), hence almost everywhere along a
subsequence, together with the lower semicontinuity of `eLpNorm · 3`. -/
theorem velocityCriticalL3 (v : SpatialField) (hv : MemPeriodicHomogeneous (1 / 2) v) :
    periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v := by
  obtain ⟨-, hL, hmean, -⟩ := hv
  have hmeasT : ∀ N : ℕ, AEStronglyMeasurable
      (torusLift (truncField v (freqBox N))) periodicTorusMeasure := fun N ↦
    (memLp_torusLift_vector (contDiff_truncField v (freqBox N)).continuous 2).aestronglyMeasurable
  have hTM : TendstoInMeasure periodicTorusMeasure
      (fun N ↦ torusLift (truncField v (freqBox N))) atTop (torusLift v) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hmeasT hL.aestronglyMeasurable
      (tendsto_eLpNorm_truncField_sub v hL)
  obtain ⟨ns, -, hae⟩ := hTM.exists_seq_tendsto_ae
  have hfatou : eLpNorm (torusLift v) 3 periodicTorusMeasure
      ≤ atTop.liminf (fun n ↦ eLpNorm
          (torusLift (truncField v (freqBox (ns n)))) 3 periodicTorusMeasure) :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n ↦ hmeasT (ns n)) (torusLift v) hae
  have hle : ∀ n : ℕ,
      eLpNorm (torusLift (truncField v (freqBox (ns n)))) 3 periodicTorusMeasure
        ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v := by
    intro n
    have h1 : periodicLpENorm 3 (truncField v (freqBox (ns n)))
        ≤ ENNReal.ofReal CcriticalHalf *
          periodicHomogeneousENorm (1 / 2) (truncField v (freqBox (ns n))) :=
      velocityCriticalL3_smooth _ (smoothPeriodicT_truncField v _)
        (isMeanZeroT_truncField v hL hmean _ (freqBox_neg_closed (ns n)))
    refine h1.trans ?_
    gcongr
    exact periodicHomogeneousENorm_truncField_le (1 / 2) v hL hmean _
      (freqBox_neg_closed (ns n))
  calc periodicLpENorm 3 v = eLpNorm (torusLift v) 3 periodicTorusMeasure := rfl
    _ ≤ atTop.liminf (fun n ↦ eLpNorm
          (torusLift (truncField v (freqBox (ns n)))) 3 periodicTorusMeasure) := hfatou
    _ ≤ atTop.liminf (fun _ : ℕ ↦
          ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v) :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)
    _ = ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v :=
        Filter.liminf_const _

end NSFormalization.Section3.T12
