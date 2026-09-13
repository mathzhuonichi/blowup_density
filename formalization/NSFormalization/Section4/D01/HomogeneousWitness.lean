import NSFormalization.Paper3.AngularFourierDilation
import NSFormalization.Paper3.RealVectorPositiveDensity
import NSFormalization.Paper3.CompactFourier
import NSFormalization.Paper3.PositiveTemporalDensity
import NSFormalization.Source.FourierConvention
import NSFormalization.Source.RealSobolev
import NavierStokes.R3.WeakFourierUniqueness

/-!
# The first inhabitant of the homogeneous realization (unit D01, homogeneous half)

Before this module every homogeneous name of `verification/Contracts/V1/Data.lean`
had **zero** users (`research/I03/COMPARISON.md:223,284`), so
`Data.lean:338` `homogeneousENorm` and `Data.lean:390` `forceHomogeneousENorm`
were empty infima, i.e. `⊤`, and every statement about them was vacuous.

For `Data.lean:338` this module supplies the witness outright:
`homogeneousENorm s (φ : 𝓢')` is attained and `≠ ⊤`
(`homogeneousENorm_schwartz`, `homogeneousENorm_schwartz_ne_top`).

For `Data.lean:390` `forceHomogeneousENorm` it supplies only **part** of the
witness.  `Data.lean:375` `IsHomogeneousPath` is inhabited
(`isHomogeneousPath_compact`), but that infimum ranges over a subtype which
additionally demands `AEStronglyMeasurable G forceTimeMeasure`, and no such path
is produced here.  So `forceHomogeneousENorm` is **still not known to be `< ⊤`**:
what is proved about it is the unconditional lower bound
`eLpNorm_slice_le_forceHomogeneousENorm` and the conditional equality
`forceHomogeneousENorm_eq_of_aestronglyMeasurable`.  That one missing hypothesis
is exactly I03's U7c blocker; `research/D01/ATTEMPTS_HOMOGENEOUS.md` §4(a)1
records the route.

## What is proved

* `isHomogeneousSliceDatum_schwartz` / `isHomogeneousSliceDatum_compact`: a real
  three-vector field whose complex components are Schwartz — in particular every
  `C_c^∞(R³;R³)` field — has an order-`s` homogeneous slice datum
  (`Data.lean:367`) for every `s > -3/2`, its datum lies in the closed real
  subspace `F(-ξ) = conj (F ξ)` of `02-preliminaries.tex:72`, and *every* datum
  of that slice has `L²` norm equal to `Data.lean:410`
  `homogeneousFourierENorm`.  These are the two clauses of
  `research/B02/Spec.lean:454` `lebesgueHomogeneousDatum` under a Schwartz
  hypothesis in place of `L¹ ∩ L²`.
* `homogeneousDatum_unique` / `isHomogeneousSliceDatum_unique`: the homogeneous
  datum is unique at every real order.  This is `research/D01/RECONCILIATION.md`
  unit **L7**, the "no polynomial ambiguity" of `02-preliminaries.tex:70`, and
  it is what turns the `Data.lean` infima into equalities.
* `isHomogeneousSliceDatum_sub`: `research/B02/Spec.lean:470`
  `homogeneousDatumSub`, with an integrability side condition that the
  unconditional statement needs (see the docstring of `isSliceDistribution_sub`).
* `isHomogeneousPath_compact`, `bochnerDatumENorm_eq_eLpNorm_slice`,
  `eLpNorm_slice_le_forceHomogeneousENorm`: the `F_c` class has a homogeneous
  datum path (`Data.lean:375`), every such path has the same Bochner norm,
  namely the `L^q(0,∞)` norm of the slice quantity, and hence that `L^q_t`
  quantity is a lower bound for `Data.lean:390` `forceHomogeneousENorm`.

## The range of `s`

`-3/2 < s` is the only hypothesis: it is exactly what makes
`∫_{|ξ|<1}|ξ|^{2s}dξ` finite (`04-whole-space.tex:70-72`,
`Paper3.homogeneous_low_frequency_integrable`).  The upper bound `s < 3/2` of
the `Data.lean:324` docstring is *not* needed here: the temperedness estimate it
protects is the Cauchy-Schwarz bound for a general `L²` datum, whereas a Schwartz
profile's datum is `|ξ|^s φ̂` with `φ̂` Schwartz, whose pairing with a Schwartz
test is integrable at every order.  Uniqueness likewise holds at every real `s`:
the local integrability that
`NavierStokesR3.WeakFourierUniqueness.ae_eq_zero_of_integral_schwartz_test_mul_eq_zero`
needs is obtained from the `Integrable` clause of `Data.lean:324` itself, by
testing against a bump equal to `1` on the compact set
(`locallyIntegrable_of_schwartz_mul`), not from the `2s < 3` estimate.

## Conventions

The transform is the manuscript's angular one
`ẑ(ξ) = (2π)^{-3/2}∫e^{-ix·ξ}z(x)dx` (`01-introduction.tex:91`), carried by
`Source.angularFourier` and `Paper3.angularFourierDistribution`, never Mathlib's
cycles-convention `𝓕`.  Reality is `Source.RealSobolev.realSubspace`; the three
components are summed with the Euclidean `PiLp 2` norm of
`01-introduction.tex:103`, i.e. `Paper3.RealVectorSobolev`.

`NSFormalization` is a dependency of the `Contracts` library and cannot import
it, so §5 and §15 restate the `Data.lean` declarations; each is *definitionally*
the contract one (checked by `rfl` against `Contracts.V1.Data` in a scratch
file), and a `verification/Bindings` bridge is owed.
-/

noncomputable section

namespace NSFormalization.Section4.D01.Homogeneous

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source (angularFourier frequencyUnit frequencyUnit_pos)
open NSFormalization.Source.RealSobolev
open scoped ContDiff ENNReal SchwartzMap ComplexConjugate

/-! ## 1. The angular transform of a Schwartz function, as a Schwartz function -/

/-- `angularFourier` of a Schwartz function, packaged as a Schwartz function. -/
def schwartzAngularFourier (φ : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  schwartzAngularDilation (𝓕 φ)

@[simp] theorem schwartzAngularFourier_apply (φ : SchwartzMap Space ℂ) (ξ : Space) :
    schwartzAngularFourier φ ξ = angularFourier (φ : Space → ℂ) ξ := rfl

/-! ## 2. Finiteness of the homogeneous energy of a Schwartz profile -/

/-- `04-whole-space.tex:70-72`: every Schwartz profile has finite homogeneous
energy at every order `s > -3/2`. -/
theorem integrable_homogeneous_schwartz {s : ℝ} (hs : -3 / 2 < s) (ψ : SchwartzMap Space ℂ) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖ψ ξ‖ ^ 2) := by
  rcases le_or_gt s 0 with hs0 | hs0
  · exact schwartz_homogeneous_negative_integrable hs hs0 ψ
  · refine (schwartz_bessel_integrable s ψ).mono'
      (by apply Measurable.aestronglyMeasurable; fun_prop) ?_
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hw : ‖ξ‖ ^ (2 * s) ≤ (1 + ‖ξ‖ ^ 2) ^ s := by
      have h1 : ‖ξ‖ ^ (2 * s) = ((‖ξ‖ ^ 2 : ℝ)) ^ s := by
        rw [← Real.rpow_natCast ‖ξ‖ 2, ← Real.rpow_mul (norm_nonneg ξ)]
        norm_num
      rw [h1]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hs0.le
    have : (0:ℝ) ≤ ‖ψ ξ‖ ^ 2 := by positivity
    unfold besselIntegrand
    nlinarith

/-! ## 3. The homogeneous datum of a Schwartz profile -/

/-- `02-preliminaries.tex:59-63` eq:homogeneous-realization read forwards:
the datum of `h` is `G = |ξ|^{s} ĥ`, in the manuscript's angular convention. -/
def homogeneousProfile (s : ℝ) (f : Space → ℂ) : Space → ℂ :=
  fun ξ => ((‖ξ‖ ^ s : ℝ) : ℂ) * angularFourier f ξ

theorem measurable_homogeneousProfile (s : ℝ) (φ : SchwartzMap Space ℂ) :
    Measurable (homogeneousProfile s (φ : Space → ℂ)) := by
  have hw : Measurable (fun ξ : Space => ((‖ξ‖ ^ s : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_norm.pow_const s)
  have hF : Measurable (fun ξ : Space => angularFourier (φ : Space → ℂ) ξ) :=
    (schwartzAngularFourier φ).continuous.measurable
  exact hw.mul hF

theorem norm_homogeneousProfile_sq (s : ℝ) (f : Space → ℂ) (ξ : Space) :
    ‖homogeneousProfile s f ξ‖ ^ 2 = ‖ξ‖ ^ (2 * s) * ‖angularFourier f ξ‖ ^ 2 := by
  have hnn : (0:ℝ) ≤ ‖ξ‖ ^ s := Real.rpow_nonneg (norm_nonneg ξ) s
  have hsq : (‖ξ‖ ^ s) ^ 2 = ‖ξ‖ ^ (2 * s) := by
    rw [← Real.rpow_natCast (‖ξ‖ ^ s) 2, ← Real.rpow_mul (norm_nonneg ξ)]
    norm_num [mul_comm]
  unfold homogeneousProfile
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn, mul_pow, hsq]

/-- `04-whole-space.tex:70-72`: the homogeneous datum of a Schwartz profile is
square integrable at every order `s > -3/2`. -/
theorem memLp_homogeneousProfile {s : ℝ} (hs : -3 / 2 < s) (φ : SchwartzMap Space ℂ) :
    MemLp (homogeneousProfile s (φ : Space → ℂ)) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm
    (measurable_homogeneousProfile s φ).aestronglyMeasurable).mpr ?_
  refine (integrable_homogeneous_schwartz hs (schwartzAngularFourier φ)).congr ?_
  filter_upwards [] with ξ
  exact (norm_homogeneousProfile_sq s (φ : Space → ℂ) ξ).symm

/-- The `L²` datum `|ξ|^s φ̂` of a Schwartz profile. -/
def homogeneousDatum {s : ℝ} (hs : -3 / 2 < s) (φ : SchwartzMap Space ℂ) : FourierData :=
  (memLp_homogeneousProfile hs φ).toLp _

theorem homogeneousDatum_ae {s : ℝ} (hs : -3 / 2 < s) (φ : SchwartzMap Space ℂ) :
    (homogeneousDatum hs φ : Space → ℂ) =ᵐ[volume] homogeneousProfile s (φ : Space → ℂ) :=
  MemLp.coeFn_toLp _

theorem ae_ne_zero : ∀ᵐ ξ : Space ∂(volume : Measure Space), ξ ≠ 0 := by
  simp [ae_iff]

/-- Removing the homogeneous weight recovers the angular transform, a.e. -/
theorem homogeneousDatum_weight_ae {s : ℝ} (hs : -3 / 2 < s) (φ : SchwartzMap Space ℂ) :
    (fun ξ : Space => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * (homogeneousDatum hs φ : Space → ℂ) ξ)
      =ᵐ[volume] fun ξ : Space => angularFourier (φ : Space → ℂ) ξ := by
  filter_upwards [homogeneousDatum_ae hs φ, ae_ne_zero] with ξ hξ hne
  have hpos : (0:ℝ) < ‖ξ‖ := norm_pos_iff.mpr hne
  have hone : (‖ξ‖ ^ (-s)) * (‖ξ‖ ^ s) = 1 := by
    rw [← Real.rpow_add hpos]
    simp
  rw [hξ]
  unfold homogeneousProfile
  rw [← mul_assoc, ← Complex.ofReal_mul, hone]
  simp

/-! ## 4. Reality: the conjugate-reflection symmetry of `02-preliminaries.tex:72` -/

/-- The angular transform of a real-valued field has the manuscript's
conjugate-reflection symmetry `F(-ξ) = conj (F ξ)`. -/
theorem angularFourier_conj_neg {f : Space → ℂ} (hf : ∀ x, conj (f x) = f x) (ξ : Space) :
    conj (angularFourier f (-ξ)) = angularFourier f ξ := by
  have hfc : (fun x => conj (f x)) = f := funext hf
  have h := NSFormalization.Source.RealSobolev.fourier_conjugate f (frequencyUnit⁻¹ • ξ)
  rw [hfc] at h
  simp only [NSFormalization.Source.angularFourier, smul_neg, Complex.real_smul, map_mul,
    Complex.conj_ofReal]
  rw [← h]

/-- The datum of a real-valued Schwartz profile lies in the closed real
subspace `Source.RealSobolev.realSubspace` of `02-preliminaries.tex:72`. -/
theorem realSymmetry_homogeneousDatum {s : ℝ} (hs : -3 / 2 < s) (φ : SchwartzMap Space ℂ)
    (hφ : ∀ x, conj (φ x) = φ x) :
    realSymmetry (homogeneousDatum hs φ) = homogeneousDatum hs φ := by
  apply Lp.ext
  have hneg := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae
    (homogeneousDatum_ae hs φ)
  filter_upwards [realSymmetry_ae (homogeneousDatum hs φ), homogeneousDatum_ae hs φ, hneg]
    with ξ h1 h2 h3
  rw [h1, h3, h2]
  unfold homogeneousProfile
  rw [map_mul, Complex.conj_ofReal, norm_neg]
  exact congrArg _ (angularFourier_conj_neg hφ ξ)

theorem mem_realSubspace_homogeneousDatum {s : ℝ} (hs : -3 / 2 < s) (φ : SchwartzMap Space ℂ)
    (hφ : ∀ x, conj (φ x) = φ x) : homogeneousDatum hs φ ∈ realSubspace s :=
  (mem_realSubspace_iff s _).mpr (realSymmetry_homogeneousDatum hs φ hφ)

/-! ## 5. The `Contracts.V1.Data` predicates, restated

`NSFormalization` is a dependency of the `Contracts` library and cannot import
it, so the four predicates of `verification/Contracts/V1/Data.lean:298,324,358,367`
and the two norms of `:338,410` are restated verbatim.  Each is *definitionally*
the contract declaration; a `verification/Bindings` `rfl` bridge is owed. -/

/-- `Data.lean:99` `SpatialField`. -/
abbrev SpatialField := Space → Space

/-- `Data.lean:284` `VectorDistribution`. -/
abbrev VectorDistribution := Fin 3 → 𝓢'(Space, ℂ)

/-- `Data.lean:298` `IsSliceDistribution`. -/
def IsSliceDistribution (z : SpatialField) (U : VectorDistribution) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    U i ψ = ∫ x : Space, ψ x * ((z x i : ℝ) : ℂ)

/-- `Data.lean:324` `IsHomogeneousDatum`. -/
def IsHomogeneousDatum (s : ℝ) (G : FourierData) (u : 𝓢'(Space, ℂ)) : Prop :=
  ∀ φ : SchwartzMap Space ℂ,
    Integrable (fun ξ : Space => φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ)) ∧
      angularFourierDistribution u φ =
        ∫ ξ : Space, φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ)

/-- `Data.lean:338` `homogeneousENorm`. -/
def homogeneousENorm (s : ℝ) (u : 𝓢'(Space, ℂ)) : ℝ≥0∞ :=
  ⨅ G : {G : FourierData // IsHomogeneousDatum s G u}, ‖G.1‖ₑ

/-- `Data.lean:358` `IsHomogeneousVectorDatum`. -/
def IsHomogeneousVectorDatum (s : ℝ) (U : VectorDistribution)
    (G : RealVectorSobolev s) : Prop :=
  ∀ i : Fin 3, IsHomogeneousDatum s ((G i : FourierData)) (U i)

/-- `Data.lean:367` `IsHomogeneousSliceDatum`. -/
def IsHomogeneousSliceDatum (s : ℝ) (z : SpatialField)
    (G : RealVectorSobolev s) : Prop :=
  ∃ U : VectorDistribution, IsSliceDistribution z U ∧ IsHomogeneousVectorDatum s U G

/-- `Data.lean:410` `homogeneousFourierENorm`. -/
def homogeneousFourierENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  (∑ i : Fin 3, ∫⁻ ξ : Space,
      ENNReal.ofReal (‖ξ‖ ^ (2 * s) *
        ‖angularFourier (fun x => ((z x i : ℝ) : ℂ)) ξ‖ ^ 2)) ^ ((2 : ℝ)⁻¹)

/-! ## 6. The scalar realization identity -/

/-- A Schwartz test times the angular transform of a Schwartz profile is
integrable; this is the manuscript's temperedness estimate
(`02-preliminaries.tex:67`) in the only case it is used here. -/
theorem integrable_schwartz_mul_angularFourier (φ ψ : SchwartzMap Space ℂ) :
    Integrable (fun ξ : Space => ψ ξ * angularFourier (φ : Space → ℂ) ξ) :=
  ψ.integrable.mul_bdd (c := SchwartzMap.seminorm ℝ 0 0 (schwartzAngularFourier φ))
    (schwartzAngularFourier φ).continuous.aestronglyMeasurable
    (.of_forall (SchwartzMap.norm_le_seminorm ℝ (schwartzAngularFourier φ)))

/-- `02-preliminaries.tex:58-69` eq:homogeneous-realization, the existence half:
the tempered distribution of a Schwartz profile `φ` is realized by the datum
`|ξ|^s φ̂` at every order `s > -3/2`. -/
theorem isHomogeneousDatum_homogeneousDatum {s : ℝ} (hs : -3 / 2 < s)
    (φ : SchwartzMap Space ℂ) :
    IsHomogeneousDatum s (homogeneousDatum hs φ) (φ : 𝓢'(Space, ℂ)) := by
  intro ψ
  have hae : (fun ξ : Space =>
        ψ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * (homogeneousDatum hs φ : Space → ℂ) ξ))
      =ᵐ[volume] fun ξ : Space => ψ ξ * angularFourier (φ : Space → ℂ) ξ := by
    filter_upwards [homogeneousDatum_weight_ae hs φ] with ξ h
    rw [h]
  refine ⟨(integrable_schwartz_mul_angularFourier φ ψ).congr hae.symm, ?_⟩
  rw [angularFourierDistribution_schwartz_apply, integral_congr_ae hae]
  simp only [smul_eq_mul]

/-! ## 7. Uniqueness of the homogeneous datum (unit L7) -/

/-- A function integrable against every Schwartz test is locally integrable.
Take a bump equal to `1` on the compact set. -/
theorem locallyIntegrable_of_schwartz_mul {h : Space → ℂ}
    (hint : ∀ ψ : SchwartzMap Space ℂ, Integrable (fun ξ : Space => ψ ξ * h ξ)) :
    LocallyIntegrable h (volume : Measure Space) := by
  refine locallyIntegrable_iff.mpr ?_
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  set R' : ℝ := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set b : ContDiffBump (0 : Space) := ⟨R', R' + 1, hR'pos, by linarith⟩ with hb
  have hbsmooth : ContDiff ℝ ∞ (fun x : Space => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hbsupp : HasCompactSupport (fun x : Space => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  set ψ : SchwartzMap Space ℂ :=
    NavierStokesR3.CompactSchwartz.ofCompactSupport _ hbsmooth hbsupp with hψ
  have hone : ∀ x ∈ K, ψ x = 1 := by
    intro x hx
    have hxb : x ∈ Metric.closedBall (0 : Space) b.rIn := by
      refine Metric.mem_closedBall.mpr ?_
      exact le_trans (Metric.mem_closedBall.mp (hR hx)) (le_max_left _ _)
    change ((b x : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall hxb]
    norm_num
  refine ((hint ψ).integrableOn (s := K)).congr_fun ?_ hK.measurableSet
  intro x hx
  show ψ x * h x = h x
  rw [hone x hx, one_mul]

/-- `02-preliminaries.tex:70` "no polynomial ambiguity", and the uniqueness
that `Data.lean:338` defers to unit L7: a tempered distribution has at most one
homogeneous datum, at every real order `s`. -/
theorem homogeneousDatum_unique {s : ℝ} {G G' : FourierData} {u : 𝓢'(Space, ℂ)}
    (hG : IsHomogeneousDatum s G u) (hG' : IsHomogeneousDatum s G' u) : G = G' := by
  set h : Space → ℂ := fun ξ =>
    ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * ((G : Space → ℂ) ξ - (G' : Space → ℂ) ξ) with hh
  have hint : ∀ ψ : SchwartzMap Space ℂ, Integrable (fun ξ : Space => ψ ξ * h ξ) := by
    intro ψ
    refine ((hG ψ).1.sub (hG' ψ).1).congr ?_
    filter_upwards [] with ξ
    simp only [hh, Pi.sub_apply]
    ring
  have hzero : ∀ ψ : SchwartzMap Space ℂ, (∫ ξ : Space, h ξ * ψ ξ) = 0 := by
    intro ψ
    have hsub : (∫ ξ : Space, (ψ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * (G : Space → ℂ) ξ) -
        ψ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * (G' : Space → ℂ) ξ))) = 0 := by
      rw [integral_sub (hG ψ).1 (hG' ψ).1, ← (hG ψ).2, ← (hG' ψ).2, sub_self]
    rw [← hsub]
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [hh]
    ring
  have hae := NavierStokesR3.WeakFourierUniqueness.ae_eq_zero_of_integral_schwartz_test_mul_eq_zero
    h (locallyIntegrable_of_schwartz_mul hint) hzero
  apply Lp.ext
  filter_upwards [hae, ae_ne_zero] with ξ hξ hne
  have hpos : (0:ℝ) < ‖ξ‖ := norm_pos_iff.mpr hne
  have hw : ((‖ξ‖ ^ (-s) : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt (Real.rpow_pos_of_pos hpos (-s))
  have : (G : Space → ℂ) ξ - (G' : Space → ℂ) ξ = 0 := by
    have h0 : ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * ((G : Space → ℂ) ξ - (G' : Space → ℂ) ξ) = 0 := hξ
    exact (mul_eq_zero.mp h0).resolve_left hw
  exact sub_eq_zero.mp this

/-! ## 8. The `L²` norm of the datum is the manuscript's Fourier quantity -/

theorem enorm_homogeneousDatum_sq {s : ℝ} (hs : -3 / 2 < s) (φ : SchwartzMap Space ℂ) :
    ‖homogeneousDatum hs φ‖ₑ ^ (2 : ℝ) =
      ∫⁻ ξ : Space,
        ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖angularFourier (φ : Space → ℂ) ξ‖ ^ 2) := by
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [ENNReal.rpow_inv_rpow (by norm_num : (2:ℝ) ≠ 0)]
  apply lintegral_congr_ae
  filter_upwards [homogeneousDatum_ae hs φ] with ξ hξ
  rw [hξ, ← norm_homogeneousProfile_sq s (φ : Space → ℂ) ξ, ← ofReal_norm,
    ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-! ## 9. The vector witness -/

/-- The real three-vector homogeneous datum of a Schwartz family. -/
def homogeneousVectorDatum {s : ℝ} (hs : -3 / 2 < s) (ψ : Fin 3 → SchwartzMap Space ℂ)
    (hre : ∀ (i : Fin 3) (x : Space), conj (ψ i x) = ψ i x) : RealVectorSobolev s :=
  WithLp.toLp 2 fun i => ⟨homogeneousDatum hs (ψ i),
    mem_realSubspace_homogeneousDatum hs (ψ i) (hre i)⟩

@[simp] theorem homogeneousVectorDatum_coe {s : ℝ} (hs : -3 / 2 < s)
    (ψ : Fin 3 → SchwartzMap Space ℂ)
    (hre : ∀ (i : Fin 3) (x : Space), conj (ψ i x) = ψ i x) (i : Fin 3) :
    ((homogeneousVectorDatum hs ψ hre i : RealSobolevHilbert s) : FourierData)
      = homogeneousDatum hs (ψ i) := rfl

/-- `04-whole-space.tex:226` prop:Renergy, the existence half at the spatial
level: a real three-vector field whose complex components are Schwartz has an
order-`s` homogeneous slice datum for every `s > -3/2`.  This is the first
inhabitant of `Data.lean:367` `IsHomogeneousSliceDatum`. -/
theorem isHomogeneousSliceDatum_schwartz {s : ℝ} (hs : -3 / 2 < s)
    (z : SpatialField) (ψ : Fin 3 → SchwartzMap Space ℂ)
    (hz : ∀ (i : Fin 3) (x : Space), ψ i x = ((z x i : ℝ) : ℂ))
    (hre : ∀ (i : Fin 3) (x : Space), conj (ψ i x) = ψ i x) :
    IsHomogeneousSliceDatum s z (homogeneousVectorDatum hs ψ hre) := by
  refine ⟨fun i => ((ψ i : SchwartzMap Space ℂ) : 𝓢'(Space, ℂ)), ?_, ?_⟩
  · intro i χ
    rw [SchwartzMap.coe_apply]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [smul_eq_mul, hz i x]
  · intro i
    rw [homogeneousVectorDatum_coe]
    exact isHomogeneousDatum_homogeneousDatum hs (ψ i)

/-! ## 10. The norm clause -/

/-- `01-introduction.tex:103` "sum the squared component norms", in `ℝ≥0∞`. -/
theorem enorm_sq_piLp {s : ℝ} (A : RealVectorSobolev s) :
    ‖A‖ₑ ^ (2 : ℝ) = ∑ i : Fin 3, ‖A i‖ₑ ^ (2 : ℝ) := by
  have hsq : ‖A‖ ^ 2 = ∑ i : Fin 3, ‖A i‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => RealSobolevHilbert s) A
  rw [← ofReal_norm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _), hsq,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ofReal_norm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- The datum's `L²` norm is the manuscript's literal Fourier quantity
`Data.lean:410` `homogeneousFourierENorm`. -/
theorem enorm_homogeneousVectorDatum {s : ℝ} (hs : -3 / 2 < s) (z : SpatialField)
    (ψ : Fin 3 → SchwartzMap Space ℂ)
    (hz : ∀ (i : Fin 3) (x : Space), ψ i x = ((z x i : ℝ) : ℂ))
    (hre : ∀ (i : Fin 3) (x : Space), conj (ψ i x) = ψ i x) :
    ‖homogeneousVectorDatum hs ψ hre‖ₑ = homogeneousFourierENorm s z := by
  have hcomp : ∀ i : Fin 3, (fun x : Space => ((z x i : ℝ) : ℂ)) = (ψ i : Space → ℂ) :=
    fun i => funext fun x => (hz i x).symm
  have hsq : ‖homogeneousVectorDatum hs ψ hre‖ₑ ^ (2 : ℝ) =
      ∑ i : Fin 3, ∫⁻ ξ : Space,
        ENNReal.ofReal (‖ξ‖ ^ (2 * s) *
          ‖angularFourier (fun x => ((z x i : ℝ) : ℂ)) ξ‖ ^ 2) := by
    rw [enorm_sq_piLp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcomp i]
    exact enorm_homogeneousDatum_sq hs (ψ i)
  rw [homogeneousFourierENorm, ← hsq, ENNReal.rpow_rpow_inv (by norm_num : (2:ℝ) ≠ 0)]

/-! ## 11. Uniqueness at the vector level, and the two `Data.lean` norms -/

theorem isSliceDistribution_unique {z : SpatialField} {U V : VectorDistribution}
    (hU : IsSliceDistribution z U) (hV : IsSliceDistribution z V) : U = V := by
  funext i
  ext ψ
  rw [hU i ψ, hV i ψ]

/-- Unit L7 at the vector level: a physical slice has at most one homogeneous
datum, so the `Data.lean:338` and `Data.lean:390` infima are attained at a unique point. -/
theorem isHomogeneousSliceDatum_unique {s : ℝ} {z : SpatialField} {A B : RealVectorSobolev s}
    (hA : IsHomogeneousSliceDatum s z A) (hB : IsHomogeneousSliceDatum s z B) : A = B := by
  obtain ⟨U, hU, hAU⟩ := hA
  obtain ⟨V, hV, hBV⟩ := hB
  have hUV : U = V := isSliceDistribution_unique hU hV
  subst hUV
  refine WithLp.ofLp_injective 2 (funext fun i => ?_)
  exact Subtype.ext (homogeneousDatum_unique (hAU i) (hBV i))

/-- `02-preliminaries.tex:63` "isometric bijection onto `L²`": the
`Data.lean:338` infimum is the norm of the unique datum. -/
theorem homogeneousENorm_schwartz {s : ℝ} (hs : -3 / 2 < s) (φ : SchwartzMap Space ℂ) :
    homogeneousENorm s (φ : 𝓢'(Space, ℂ)) = ‖homogeneousDatum hs φ‖ₑ := by
  rw [homogeneousENorm]
  refine le_antisymm ?_ (le_iInf fun G => ?_)
  · exact iInf_le_of_le ⟨homogeneousDatum hs φ, isHomogeneousDatum_homogeneousDatum hs φ⟩ le_rfl
  · rw [homogeneousDatum_unique (isHomogeneousDatum_homogeneousDatum hs φ) G.2]

theorem homogeneousENorm_schwartz_ne_top {s : ℝ} (hs : -3 / 2 < s) (φ : SchwartzMap Space ℂ) :
    homogeneousENorm s (φ : 𝓢'(Space, ℂ)) ≠ ⊤ := by
  rw [homogeneousENorm_schwartz hs φ, ← ofReal_norm]
  exact ENNReal.ofReal_ne_top

/-! ## 12. The two clauses of `B02`'s `lebesgueHomogeneousDatum`, for Schwartz data -/

/-- Existence, with the norm of the witness.  `research/B02/Spec.lean:454`
`lebesgueHomogeneousDatum`, first conjunct, under a Schwartz hypothesis in
place of `L¹ ∩ L²`. -/
theorem exists_isHomogeneousSliceDatum {s : ℝ} (hs : -3 / 2 < s) (z : SpatialField)
    (ψ : Fin 3 → SchwartzMap Space ℂ)
    (hz : ∀ (i : Fin 3) (x : Space), ψ i x = ((z x i : ℝ) : ℂ)) :
    ∃ A : RealVectorSobolev s,
      IsHomogeneousSliceDatum s z A ∧ ‖A‖ₑ = homogeneousFourierENorm s z := by
  have hre : ∀ (i : Fin 3) (x : Space), conj (ψ i x) = ψ i x := by
    intro i x
    rw [hz i x, Complex.conj_ofReal]
  exact ⟨homogeneousVectorDatum hs ψ hre, isHomogeneousSliceDatum_schwartz hs z ψ hz hre,
    enorm_homogeneousVectorDatum hs z ψ hz hre⟩

/-- The norm clause: *every* datum of the slice has the Fourier norm.
`research/B02/Spec.lean:454` `lebesgueHomogeneousDatum`, second conjunct. -/
theorem enorm_of_isHomogeneousSliceDatum {s : ℝ} (hs : -3 / 2 < s) (z : SpatialField)
    (ψ : Fin 3 → SchwartzMap Space ℂ)
    (hz : ∀ (i : Fin 3) (x : Space), ψ i x = ((z x i : ℝ) : ℂ))
    (A : RealVectorSobolev s) (hA : IsHomogeneousSliceDatum s z A) :
    ‖A‖ₑ = homogeneousFourierENorm s z := by
  obtain ⟨B, hB, hnorm⟩ := exists_isHomogeneousSliceDatum hs z ψ hz
  rw [isHomogeneousSliceDatum_unique hA hB, hnorm]

/-! ## 13. Smooth compactly supported real vector fields -/

theorem contDiff_component {z : SpatialField} (hz : ContDiff ℝ ∞ z) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x : Space => ((z x i : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp
    (((EuclideanSpace.proj i : Space →L[ℝ] ℝ)).contDiff.comp hz)

theorem hasCompactSupport_component {z : SpatialField} (hc : HasCompactSupport z) (i : Fin 3) :
    HasCompactSupport (fun x : Space => ((z x i : ℝ) : ℂ)) :=
  hc.comp_left (g := fun v : Space => ((v i : ℝ) : ℂ)) (by simp)

/-- The Schwartz components of a `C_c^∞(R³;R³)` real vector field. -/
def compactSchwartzComponents {z : SpatialField} (hzs : ContDiff ℝ ∞ z)
    (hzc : HasCompactSupport z) (i : Fin 3) : SchwartzMap Space ℂ :=
  NavierStokesR3.CompactSchwartz.ofCompactSupport _ (contDiff_component hzs i)
    (hasCompactSupport_component hzc i)

@[simp] theorem compactSchwartzComponents_apply {z : SpatialField} (hzs : ContDiff ℝ ∞ z)
    (hzc : HasCompactSupport z) (i : Fin 3) (x : Space) :
    compactSchwartzComponents hzs hzc i x = ((z x i : ℝ) : ℂ) := rfl

/-- `04-whole-space.tex:249` "compact-smooth density in this realization": the
first inhabitant of `Data.lean:367` `IsHomogeneousSliceDatum`, for a real
`C_c^∞(R³;R³)` field, at every order `-3/2 < s`.  Both clauses of
`research/B02/Spec.lean:454` `lebesgueHomogeneousDatum` hold. -/
theorem isHomogeneousSliceDatum_compact {s : ℝ} (hs : -3 / 2 < s) {z : SpatialField}
    (hzs : ContDiff ℝ ∞ z) (hzc : HasCompactSupport z) :
    (∃ A : RealVectorSobolev s, IsHomogeneousSliceDatum s z A) ∧
      ∀ A : RealVectorSobolev s, IsHomogeneousSliceDatum s z A →
        ‖A‖ₑ = homogeneousFourierENorm s z := by
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hA, _⟩ :=
      exists_isHomogeneousSliceDatum hs z (compactSchwartzComponents hzs hzc) (fun _ _ => rfl)
    exact ⟨A, hA⟩
  · intro A hA
    exact enorm_of_isHomogeneousSliceDatum hs z (compactSchwartzComponents hzs hzc)
      (fun _ _ => rfl) A hA

/-! ## 14. Linearity: the datum of a difference is the difference of the data -/

theorem isHomogeneousDatum_sub {s : ℝ} {G G' : FourierData} {u v : 𝓢'(Space, ℂ)}
    (hG : IsHomogeneousDatum s G u) (hG' : IsHomogeneousDatum s G' v) :
    IsHomogeneousDatum s (G - G') (u - v) := by
  intro φ
  have hae : (fun ξ : Space =>
        φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * ((G - G' : FourierData) : Space → ℂ) ξ))
      =ᵐ[volume] fun ξ : Space =>
        φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * (G : Space → ℂ) ξ) -
          φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * (G' : Space → ℂ) ξ) := by
    filter_upwards [Lp.coeFn_sub G G'] with ξ hξ
    rw [hξ]
    simp only [Pi.sub_apply]
    ring
  refine ⟨((hG φ).1.sub (hG' φ).1).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_sub (hG φ).1 (hG' φ).1, ← (hG φ).2, ← (hG' φ).2]
  simp [map_sub]

theorem isHomogeneousVectorDatum_sub {s : ℝ} {U V : VectorDistribution}
    {Z W : RealVectorSobolev s}
    (hZ : IsHomogeneousVectorDatum s U Z) (hW : IsHomogeneousVectorDatum s V W) :
    IsHomogeneousVectorDatum s (U - V) (Z - W) := by
  intro i
  have h1 : (((Z - W) i : RealSobolevHilbert s) : FourierData) =
      ((Z i : RealSobolevHilbert s) : FourierData) - ((W i : RealSobolevHilbert s) : FourierData) :=
    rfl
  have h2 : (U - V) i = U i - V i := rfl
  rw [h1, h2]
  exact isHomogeneousDatum_sub (hZ i) (hW i)

/-- The physical difference clause needs the integrability that
`Data.lean:298`'s totalized integral leaves implicit; it holds for every field
this module produces data for. -/
theorem isSliceDistribution_sub {z w : SpatialField} {U V : VectorDistribution}
    (hU : IsSliceDistribution z U) (hV : IsSliceDistribution w V)
    (hz : ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      Integrable (fun x : Space => ψ x * ((z x i : ℝ) : ℂ)))
    (hw : ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      Integrable (fun x : Space => ψ x * ((w x i : ℝ) : ℂ))) :
    IsSliceDistribution (z - w) (U - V) := by
  intro i ψ
  have h2 : (U - V) i ψ = U i ψ - V i ψ := rfl
  rw [h2, hU i ψ, hV i ψ, ← integral_sub (hz i ψ) (hw i ψ)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hzw : (z - w) x i = z x i - w x i := rfl
  rw [hzw]
  push_cast
  ring

/-- `research/B02/Spec.lean:470` `homogeneousDatumSub`, with the integrability
side condition made explicit. -/
theorem isHomogeneousSliceDatum_sub {s : ℝ} {z w : SpatialField} {Z W : RealVectorSobolev s}
    (hZ : IsHomogeneousSliceDatum s z Z) (hW : IsHomogeneousSliceDatum s w W)
    (hz : ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      Integrable (fun x : Space => ψ x * ((z x i : ℝ) : ℂ)))
    (hw : ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      Integrable (fun x : Space => ψ x * ((w x i : ℝ) : ℂ))) :
    IsHomogeneousSliceDatum s (z - w) (Z - W) := by
  obtain ⟨U, hU, hZU⟩ := hZ
  obtain ⟨V, hV, hWV⟩ := hW
  exact ⟨U - V, isSliceDistribution_sub hU hV hz hw, isHomogeneousVectorDatum_sub hZU hWV⟩

/-- The integrability side condition for a field with Schwartz components. -/
theorem integrable_schwartz_mul_component {z : SpatialField}
    (ψ : Fin 3 → SchwartzMap Space ℂ)
    (hz : ∀ (i : Fin 3) (x : Space), ψ i x = ((z x i : ℝ) : ℂ))
    (i : Fin 3) (χ : SchwartzMap Space ℂ) :
    Integrable (fun x : Space => χ x * ((z x i : ℝ) : ℂ)) := by
  have hrw : (fun x : Space => χ x * ((z x i : ℝ) : ℂ)) = fun x => χ x * (ψ i) x := by
    funext x; rw [hz i x]
  rw [hrw]
  exact χ.integrable.mul_bdd (c := SchwartzMap.seminorm ℝ 0 0 (ψ i))
    (ψ i).continuous.aestronglyMeasurable (.of_forall (SchwartzMap.norm_le_seminorm ℝ (ψ i)))

/-! ## 15. The path lift and the `L^q_t` form of `forceHomogeneousENorm`

`Data.lean:170,375,382,390`: `SpaceTimeField`, `IsHomogeneousPath`,
`bochnerDatumENorm` and `forceHomogeneousENorm`, restated verbatim. -/

/-- `Data.lean:104` `SpaceTimeField`. -/
abbrev SpaceTimeField := VelocityField

/-- `Data.lean:118` `forceTimeMeasure`. -/
abbrev forceTimeMeasure : Measure ℝ := positiveTimeMeasure

/-- `Data.lean:205` `bochnerDatumENorm`. -/
def bochnerDatumENorm (q : ℝ≥0∞) (s : ℝ) (G : ℝ → RealVectorSobolev s) : ℝ≥0∞ :=
  eLpNorm G q forceTimeMeasure

/-- `Data.lean:375` `IsHomogeneousPath`. -/
def IsHomogeneousPath (s : ℝ) (f : SpaceTimeField)
    (G : ℝ → RealVectorSobolev s) : Prop :=
  ∀ t : ℝ, 0 ≤ t → IsHomogeneousSliceDatum s (fun x => f (t, x)) (G t)

/-- `Data.lean:390` `forceHomogeneousENorm`. -/
def forceHomogeneousENorm (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → RealVectorSobolev s //
      IsHomogeneousPath s f G ∧ AEStronglyMeasurable G forceTimeMeasure},
    bochnerDatumENorm q s G.1

/-- Space-valued spatial slice of a compactly supported spacetime field.  The
proof is `Paper3.compact_spatial_slice` (`Paper3/CompactFourierTime.lean:20`),
which is stated only for `ℂ`-valued fields. -/
theorem compact_spatial_slice' {F : ℝ × Space → Space} (hc : HasCompactSupport F) (t : ℝ) :
    HasCompactSupport (fun x : Space => F (t, x)) := by
  apply HasCompactSupport.intro ((hc : IsCompact (tsupport F)).image continuous_snd)
  intro x hx
  apply image_eq_zero_of_notMem_tsupport (f := F)
  intro htx
  exact hx ⟨(t, x), htx, rfl⟩

/-- The datum path of a smooth compactly supported spacetime force. -/
def compactHomogeneousPath {s : ℝ} (hs : -3 / 2 < s) {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : ℝ → RealVectorSobolev s :=
  fun t =>
    homogeneousVectorDatum hs
      (compactSchwartzComponents (z := fun x => f (t, x))
        (hf.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice' hc t))
      (fun i x => by rw [compactSchwartzComponents_apply, Complex.conj_ofReal])

/-- `Data.lean:375` `IsHomogeneousPath` is inhabited: the class `F_c` of smooth
compactly supported spacetime forces has an order-`s` homogeneous datum path at
every `s > -3/2`, hence `04-whole-space.tex:226` prop:Renergy's homogeneous
clause is not vacuous. -/
theorem isHomogeneousPath_compact {s : ℝ} (hs : -3 / 2 < s) {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    IsHomogeneousPath s f (compactHomogeneousPath hs hf hc) := by
  intro t _
  exact isHomogeneousSliceDatum_schwartz hs _ _ (fun _ _ => rfl) _

/-- U7c, the `L^q_t` form: *every* order-`s` homogeneous datum path of a smooth
compactly supported force has the same Bochner norm, namely the `L^q(0,∞)` norm
of the slice quantity `Data.lean:410` `homogeneousFourierENorm`. -/
theorem bochnerDatumENorm_eq_eLpNorm_slice {q : ℝ≥0∞} {s : ℝ} (hs : -3 / 2 < s)
    {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (G : ℝ → RealVectorSobolev s) (hG : IsHomogeneousPath s f G) :
    bochnerDatumENorm q s G =
      eLpNorm (fun t => homogeneousFourierENorm s (fun x => f (t, x))) q forceTimeMeasure := by
  refine eLpNorm_congr_enorm_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : (0:ℝ) ≤ t := le_of_lt ht
  rw [enorm_eq_self]
  exact enorm_of_isHomogeneousSliceDatum hs _
    (compactSchwartzComponents (z := fun x => f (t, x))
      (hf.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice' hc t))
    (fun _ _ => rfl) (G t) (hG t ht0)

/-- Consequently the `Data.lean:390` infimum is bounded below by that `L^q_t`
quantity, with no measurability hypothesis. -/
theorem eLpNorm_slice_le_forceHomogeneousENorm {q : ℝ≥0∞} {s : ℝ} (hs : -3 / 2 < s)
    {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    eLpNorm (fun t => homogeneousFourierENorm s (fun x => f (t, x))) q forceTimeMeasure ≤
      forceHomogeneousENorm q s f := by
  refine le_iInf fun G => ?_
  rw [← bochnerDatumENorm_eq_eLpNorm_slice hs hf hc G.1 G.2.1]

/-- With one strongly measurable path, `Data.lean:390` `forceHomogeneousENorm`
is exactly the `L^q_t` norm of the slice quantity. -/
theorem forceHomogeneousENorm_eq_of_aestronglyMeasurable {q : ℝ≥0∞} {s : ℝ} (hs : -3 / 2 < s)
    {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hm : AEStronglyMeasurable (compactHomogeneousPath hs hf hc) forceTimeMeasure) :
    forceHomogeneousENorm q s f =
      eLpNorm (fun t => homogeneousFourierENorm s (fun x => f (t, x))) q forceTimeMeasure := by
  refine le_antisymm ?_ (eLpNorm_slice_le_forceHomogeneousENorm hs hf hc)
  rw [← bochnerDatumENorm_eq_eLpNorm_slice hs hf hc _ (isHomogeneousPath_compact hs hf hc)]
  exact iInf_le_of_le ⟨compactHomogeneousPath hs hf hc, isHomogeneousPath_compact hs hf hc, hm⟩
    le_rfl
