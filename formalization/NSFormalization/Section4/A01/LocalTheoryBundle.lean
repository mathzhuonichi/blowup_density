import NSFormalization.Section4.A01.LocalSolution
import NSFormalization.Section4.A01.ManuscriptRegularity
import NSFormalization.Section4.A01.HorizonUniform
import NSFormalization.Section4.A01.CylinderWiring
import NSFormalization.Section4.A01.JointRepresentative
import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A01.PressureRegularity
import NSFormalization.Section4.D01.DatumToJets

/-!
# Carrier-bundled local theory on a uniformly selected horizon

The strict Picard budgets from lane 210 define an antitone horizon. All carrier
witnesses survive solution selection, so manuscript regularity refers to that
same solution. The proved uniformity is fixed-force H⁷; the H¹ manuscript field
remains an unasserted definition. No contract statement is changed here.
-/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

open NSFormalization.Paper3 (RealVectorSobolev)
open D01 (IsSobolevDatum)

/-- The chosen physical solution together with the witnesses used to construct it. -/
structure LocalCarrier (ν : ℝ) (a : A02.SpatialField) (f : A02.SpaceTimeField)
    (S : ℝ) where
  hν : 0 < ν
  hS : 0 < S
  hf : D01.MemForceR f
  datum : SmoothL2Field Space
  datum_eq : datum.field = a
  datum_div : ∀ x, EulerSmoothLimit.divergence datum.field x = 0
  U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)
  hU0 : U ⟨0, le_rfl, hS.le⟩ = datum.toLp
  hpairs : ∀ q (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t,
            sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq
              (sobolevPath (C01.forcePath (S := S) hf)
                (C01.forcePath_jetLp_continuous (S := S) hf) q))
            (ordinarySobolev (q + 1) datum.toLp datum.translation_contDiff) u t
  hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)
  velocity : A02.SpaceTimeField
  hslice : ∀ t : Icc (0 : ℝ) S,
    (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t)
  hc3 : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ (univ : Set Space))
  G : A02.SpaceTimeField
  hG_int : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
    G (t, x) = pressureGradientOfVelocity ν f velocity (t, x)
  hG : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
    ∀ t ∈ Ico (0 : ℝ) S,
      MemLp (fun x : Space => G (t, x)) 2 volume ∧
      RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x))
  w : A02.ClassicalSolutionR ν a f S
  velocity_eq : w.velocity = velocity
  initial_eq : (fun x => velocity (0, x)) = a

theorem localCarrier_of_base {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (f : A02.SpaceTimeField) (hf : D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7))
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath (C01.forcePath (S := S) hf)
        (C01.forcePath_jetLp_continuous (S := S) hf) 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t) :
    Nonempty (LocalCarrier ν a.field f S) := by
  let F := C01.forcePath (S := S) hf
  let hF := C01.forcePath_jetLp_continuous (S := S) hf
  let R := aprioriRadius a F hF ‖u₆‖ E (fun q => tameAssemblyA q^2/(4*ν))
  have hb := hb_of_base'' hν hS.le a ha F hF u₆ le_rfl h₆
  obtain ⟨U, hU0, hpairs, hpaths⟩ := cylinderPair_of_bounds hf hν hS a ha R hb
  obtain ⟨velocity, hslice, hc3⟩ := exists_joint_smooth_representative hS U hpaths
  obtain ⟨G, hG_int, hG_smooth, hG_slices⟩ :=
    pressureSupply_of_pieces (le_refl 6) hν hS f hf a ha U hpairs hpaths velocity hslice hc3
  obtain ⟨u, hU, hdiv, _hinv, _hduh⟩ := hpairs 6 (le_refl 6)
  obtain ⟨w, hw, _hslice⟩ := carrierConstructor_of_localTheory hS u U hU hdiv f
    velocity hslice (hpaths 0) hc3 G hG_int ⟨hG_smooth, hG_slices⟩
  have heq : (fun x => velocity (0, x)) = a.field := by
    apply ((D01.contDiff_slice hc3 ⟨le_rfl, hS⟩).continuous.ae_eq_iff_eq
      volume a.smooth.continuous).mp
    have hs := hslice ⟨0, le_rfl, hS.le⟩
    rw [hU0] at hs
    exact hs.trans a.toLp_ae
  exact ⟨⟨hν, hS, hf, a, rfl, ha, U, hU0, hpairs, hpaths,
    velocity, hslice, hc3, G, hG_int, ⟨hG_smooth, hG_slices⟩,
    transport_initial w heq, hw, heq⟩⟩

/-- Regularity follows from the witnesses retained for this very solution. -/
theorem LocalCarrier.regularity {ν S : ℝ} {a : A02.SpatialField}
    {f : A02.SpaceTimeField} (c : LocalCarrier ν a f S) :
    ManuscriptLocalRegularity ν a f S c.w := by
  apply manuscriptLocalRegularity_of_pipeline c.w c.hf c.U _ c.hpaths
  simpa only [c.velocity_eq] using c.hslice


open EulerSobolevHeat

/-- Admissible times for the two strict Picard budgets used in lane 210. -/
def uniformBudgetSet (ν M L : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ t ≤ 1 ∧
    (t + 2 * parabolicConstant ν * Real.sqrt t) * M < 1 ∧
    (t + 2 * parabolicConstant ν * Real.sqrt t) * L < 1}

/-- Half the supremum selects a time strictly inside the admissible budget. -/
def uniformBudget (ν M L : ℝ) : ℝ := sSup (uniformBudgetSet ν M L) / 2

theorem uniformBudgetSet_nonempty (ν M L : ℝ) :
    (uniformBudgetSet ν M L).Nonempty := by
  refine ⟨0, ?_⟩
  simp [uniformBudgetSet]

theorem uniformBudgetSet_bddAbove (ν M L : ℝ) :
    BddAbove (uniformBudgetSet ν M L) := ⟨1, fun _ ht => ht.2.1⟩

theorem uniformBudget_pos (ν M L : ℝ) : 0 < uniformBudget ν M L := by
  obtain ⟨t, ht, ht1, hM, hL⟩ :=
    exists_positive_time_budget ν M L 1 1 one_pos one_pos
  have hle := le_csSup (uniformBudgetSet_bddAbove ν M L)
    (show t ∈ uniformBudgetSet ν M L from ⟨ht.le, ht1, hM, hL⟩)
  unfold uniformBudget
  linarith

theorem uniformBudget_spec (ν M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    uniformBudget ν M L ∈ uniformBudgetSet ν M L := by
  have hp := uniformBudget_pos ν M L
  have hs : sSup (uniformBudgetSet ν M L) ≤ 1 :=
    csSup_le (uniformBudgetSet_nonempty ν M L) (fun _ ht => ht.2.1)
  have hlt : uniformBudget ν M L < sSup (uniformBudgetSet ν M L) := by
    unfold uniformBudget at *
    linarith
  obtain ⟨t, ht, hδt⟩ := exists_lt_of_lt_csSup (uniformBudgetSet_nonempty ν M L) hlt
  have hmass : uniformBudget ν M L + 2 * parabolicConstant ν *
      Real.sqrt (uniformBudget ν M L) ≤ t + 2 * parabolicConstant ν * Real.sqrt t := by
    have hr := Real.sqrt_le_sqrt hδt.le
    have hc := parabolicConstant_nonneg ν
    nlinarith
  refine ⟨hp.le, ?_, (mul_le_mul_of_nonneg_right hmass hM).trans_lt ht.2.2.1,
    (mul_le_mul_of_nonneg_right hmass hL).trans_lt ht.2.2.2⟩
  unfold uniformBudget
  linarith

theorem uniformBudget_antitone (ν : ℝ) {M L M' L' : ℝ}
    (hM : M ≤ M') (hL : L ≤ L') :
    uniformBudget ν M' L' ≤ uniformBudget ν M L := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply csSup_le_csSup (uniformBudgetSet_bddAbove ν M L)
    (uniformBudgetSet_nonempty ν M' L')
  intro t ht
  obtain ⟨hb, hl⟩ := picard_budget_mono ht.1 hM hL ht.2.2.1 ht.2.2.2
  exact ⟨ht.1, ht.2.1, hb, hl⟩


/-- Zero-force coefficients on the reference compact interval. -/
def referenceCoefficients := coefficients 1 (le_refl 6)
  (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 6))

/-- The uniform sup-force ball budget, with negative inputs clipped to zero. -/
def uniformBallBound (R B : ℝ) : ℝ := by
  let : SeminormedAddCommGroup (SobolevSpace 1 7 →L[ℝ]
    SobolevSpace 1 7 →L[ℝ] SobolevSpace 1 6) := inferInstance
  exact ‖referenceCoefficients.projection‖ *
    (max 0 B + ‖referenceCoefficients.quadratic‖ * (max 0 R + 1)^2)

/-- The uniform Lipschitz budget of the same ball. -/
def uniformLipschitz (R : ℝ) : ℝ :=
  referenceCoefficients.ballLipschitz (max 0 R + 1)

/-- A canonical antitone selection from lane 210's two budget conditions. -/
def uniformHorizon (ν R B : ℝ) : ℝ :=
  uniformBudget ν (uniformBallBound R B) (uniformLipschitz R)

theorem uniformHorizon_pos (ν R B : ℝ) : 0 < uniformHorizon ν R B :=
  uniformBudget_pos _ _ _

theorem uniformHorizon_antitone (ν : ℝ) {R R' B B' : ℝ}
    (hR : R ≤ R') (hB : B ≤ B') :
    uniformHorizon ν R' B' ≤ uniformHorizon ν R B := by
  let : SeminormedAddCommGroup (SobolevSpace 1 7 →L[ℝ]
    SobolevSpace 1 7 →L[ℝ] SobolevSpace 1 6) := inferInstance
  apply uniformBudget_antitone
  · dsimp only [uniformBallBound]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg referenceCoefficients.projection)
    apply add_le_add (max_le_max_left 0 hB)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg referenceCoefficients.quadratic)
    exact pow_le_pow_left₀ (by positivity)
      (by linarith [max_le_max_left 0 hR]) 2
  · exact picard_ballLipschitz_mono referenceCoefficients
      (by linarith [max_le_max_left 0 hR])

theorem uniformHorizon_spec (ν R B : ℝ) :
    uniformHorizon ν R B ∈ uniformBudgetSet ν (uniformBallBound R B)
      (uniformLipschitz R) := by
  let : SeminormedAddCommGroup (SobolevSpace 1 7 →L[ℝ]
    SobolevSpace 1 7 →L[ℝ] SobolevSpace 1 6) := inferInstance
  apply uniformBudget_spec
  · unfold uniformBallBound
    positivity
  · exact referenceCoefficients.ballLipschitz_nonneg _ (by positivity)

/-- Lane 210's Picard argument on the canonically selected budget. -/
theorem uniformHorizon_mild {ν R B : ℝ} (hν : 0 < ν) (hR : 0 ≤ R)
    (hB : 0 ≤ B)
    (F : C(Icc (0 : ℝ) 1, SobolevSpace 1 6)) (hF : ‖F‖ ≤ B)
    (a : SobolevSpace 1 7) (ha : ‖a‖ ≤ R) :
    ∃ u : C(Icc (0 : ℝ) (uniformHorizon ν R B), SobolevSpace 1 7),
      ∀ t, u t = quadraticDuhamel 1 ν hν (uniformHorizon_pos ν R B).le
        (uniformHorizon_spec ν R B).2.1 (coefficients 1 (le_refl 6) F) a u t := by
  let : SeminormedAddCommGroup (SobolevSpace 1 7 →L[ℝ]
    SobolevSpace 1 7 →L[ℝ] SobolevSpace 1 6) := inferInstance
  let : SeminormedAddCommGroup (SobolevSpace 1 7 →L[ℝ] SobolevSpace 1 6) := inferInstance
  let C := coefficients 1 (le_refl 6) F
  let δ := uniformHorizon ν R B
  have hδ := uniformHorizon_pos ν R B
  have hspec := uniformHorizon_spec ν R B
  have hR1 : 0 ≤ R+1 := by linarith
  have hM : C.ballBound (R+1) ≤ uniformBallBound R B := by
    change ‖referenceCoefficients.projection‖ * (‖-F‖ +
      ‖(0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7 →L[ℝ] SobolevSpace 1 6))‖ * (R+1) +
      ‖referenceCoefficients.quadratic‖ * (R+1)^2) ≤ _
    simp only [norm_neg, _root_.norm_zero, zero_mul, add_zero,
      uniformBallBound, max_eq_right hR, max_eq_right hB]
    exact mul_le_mul_of_nonneg_left (add_le_add hF le_rfl) (norm_nonneg referenceCoefficients.projection)
  have hL : C.ballLipschitz (R+1) ≤ uniformLipschitz R := by
    unfold uniformLipschitz
    rw [max_eq_right hR]
    exact le_rfl
  obtain ⟨hb, hl⟩ := picard_budget_mono hδ.le hM hL hspec.2.2.1 hspec.2.2.2
  have hbudget : ‖a‖ + (δ + 2 * parabolicConstant ν * Real.sqrt δ) *
      C.ballBound (R+1) ≤ R+1 := by linarith
  obtain ⟨u, _, hu⟩ := exists_viscous_mild_solution 1 6 ν hν δ hδ.le a
    (C.comp (timeInclusion hspec.2.1)).apply
    (C.comp (timeInclusion hspec.2.1)).continuous (R+1)
    (C.ballBound (R+1)) (C.ballLipschitz (R+1)) hR1
    (C.ballBound_nonneg _ hR1) (C.ballLipschitz_nonneg _ hR1)
    (fun t x hx => C.apply_bound _ hR1 (timeInclusion hspec.2.1 t) x hx)
    (fun t x y hx hy => C.apply_sub_bound _ hR1 (timeInclusion hspec.2.1 t) x y hx hy)
    hbudget hl
  exact ⟨u, hu⟩


/-- The same smooth datum is used in the radius and the constructor. -/
def selectedDatum (a : A02.SpatialField) (ha : a ∈ A02.initialClassR) :
    SmoothL2Field Space := Classical.choose (smoothL2_of_initialClassR ha)

theorem selectedDatum_spec (a : A02.SpatialField) (ha : a ∈ A02.initialClassR) :
    (selectedDatum a ha).field = a ∧
      ∀ x, EulerSmoothLimit.divergence (selectedDatum a ha).field x = 0 :=
  Classical.choose_spec (smoothL2_of_initialClassR ha)

/-- Continuous H⁶ force path on the compact reference interval. -/
def referenceForce (f : A02.SpaceTimeField) (hf : D01.MemForceR f) :
    C(Icc (0 : ℝ) 1, SobolevSpace 1 6) :=
  sobolevPath (C01.forcePath (S := 1) hf)
    (C01.forcePath_jetLp_continuous (S := 1) hf) 6

/-- The compact-interval sup norm is a finite uniform bound on every force slice. -/
theorem referenceForce_bound (f : A02.SpaceTimeField) (hf : D01.MemForceR f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, ‖referenceForce f hf t‖ ≤ B :=
  ⟨‖referenceForce f hf‖, norm_nonneg _, ContinuousMap.norm_coe_le_norm _⟩

/-- Total horizon selected from the uniform budget; inadmissible inputs use one. -/
def localHorizon' (ν : ℝ) (a : A02.SpatialField) (f : A02.SpaceTimeField) : ℝ := by
  classical
  exact if h : 0 < ν ∧ a ∈ A02.initialClassR ∧ D01.MemForceR f then
    uniformHorizon ν
      ‖ordinarySobolev 7 (selectedDatum a h.2.1).toLp
        (selectedDatum a h.2.1).translation_contDiff‖
      ‖referenceForce f h.2.2‖
  else 1

theorem localHorizon'_eq {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (hν : 0 < ν) (ha : a ∈ A02.initialClassR) (hf : D01.MemForceR f) :
    localHorizon' ν a f = uniformHorizon ν
      ‖ordinarySobolev 7 (selectedDatum a ha).toLp (selectedDatum a ha).translation_contDiff‖
      ‖referenceForce f hf‖ := by
  rw [localHorizon', dite_eq_left (show 0 < ν ∧ a ∈ A02.initialClassR ∧ D01.MemForceR f
    from ⟨hν, ha, hf⟩)]

theorem localCarrier_nonempty {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (hν : 0 < ν) (ha : a ∈ A02.initialClassR) (hf : D01.MemForceR f) :
    Nonempty (LocalCarrier ν a f (localHorizon' ν a f)) := by
  rw [localHorizon'_eq hν ha hf]
  let A := selectedDatum a ha
  let R := ‖ordinarySobolev 7 A.toLp A.translation_contDiff‖
  let B := ‖referenceForce f hf‖
  obtain ⟨u, hu⟩ := uniformHorizon_mild hν (norm_nonneg _) (norm_nonneg _)
    (referenceForce f hf) le_rfl (ordinarySobolev 7 A.toLp A.translation_contDiff) le_rfl
  have hc := localCarrier_of_base hν (uniformHorizon_pos ν R B) f hf A
    (selectedDatum_spec a ha).2 u hu
  simpa only [A, (selectedDatum_spec a ha).1] using hc

/-- Chosen solution data retain all the carrier and pressure witnesses. -/
def localCarrier (ν : ℝ) (a : A02.SpatialField) (f : A02.SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ A02.initialClassR) (hf : D01.MemForceR f) :
    LocalCarrier ν a f (localHorizon' ν a f) :=
  Classical.choice (localCarrier_nonempty hν ha hf)

theorem manuscriptLocalRegularity_localCarrier (ν : ℝ) (a : A02.SpatialField)
    (f : A02.SpaceTimeField) (hν : 0 < ν) (ha : a ∈ A02.initialClassR)
    (hf : D01.MemForceR f) :
    ManuscriptLocalRegularity ν a f (localHorizon' ν a f) (localCarrier ν a f hν ha hf).w :=
  (localCarrier ν a f hν ha hf).regularity


/-- Datum-to-jet constants, summed over the eight orders in the H⁷ cylinder norm. -/
def datumRadiusConstant : ℝ := ∑ j ∈ Finset.range 8, D01.jetDatumConst j 7

theorem datumRadiusConstant_nonneg : 0 ≤ datumRadiusConstant :=
  Finset.sum_nonneg (fun j _ => (D01.jetDatumConst_pos j 7).le)

/-- Physical H⁷ bounds control the cylinder datum used by the Picard solver. -/
theorem cylinderDatum_norm_le (A : SmoothL2Field Space)
    (D : RealVectorSobolev (7 : ℝ)) (hD : IsSobolevDatum 7 A.field D) :
    ‖ordinarySobolev 7 A.toLp A.translation_contDiff‖ ≤ datumRadiusConstant * ‖D‖ := by
  apply (EulerOrdinarySobolev.ordinarySobolev_norm_le_tensor A 7).trans
  unfold EulerOrdinarySobolev.tensorNorm datumRadiusConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hj7 : j ≤ 7 := by have := Finset.mem_range.mp hj; omega
  have he : A.jetLp j = D01.jetOfDatum 7 j hj7 D := by
    apply Lp.ext
    exact (A.jetLp_ae j).trans (D01.jetOfDatum_ae hj7 A.smooth hD).symm
  rw [he]
  exact D01.norm_jetOfDatum_le 7 j hj7 D

open scoped ENNReal

/-- Uniform positive lower bound for fixed admissible force and a physical H⁷ ball. -/
theorem horizon_lower_bound_H7_fixedForce :
    ∀ ν, 0 < ν → ∀ f, D01.MemForceR f → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∃ δ > 0, ∀ a, a ∈ A02.initialClassR → D01.sobolevENorm 7 a ≤ K →
        δ ≤ localHorizon' ν a f := by
  intro ν hν f hf K hK
  refine ⟨uniformHorizon ν (datumRadiusConstant * K.toReal) ‖referenceForce f hf‖,
    uniformHorizon_pos _ _ _, ?_⟩
  intro a ha hbound
  rw [localHorizon'_eq hν ha hf]
  apply uniformHorizon_antitone ν _ le_rfl
  obtain ⟨D, hD⟩ := ha.1.2 7
  have hD' : IsSobolevDatum 7 (selectedDatum a ha).field D := by
    rw [(selectedDatum_spec a ha).1]
    exact hD
  have hn : ‖D‖ ≤ K.toReal := by
    have h := ENNReal.toReal_mono hK hbound
    have heq : D01.sobolevENorm 7 a = ‖D‖ₑ := A04.sobolevENorm_eq hD
    rw [heq] at h
    simpa only [toReal_enorm] using h
  exact (cylinderDatum_norm_le (selectedDatum a ha) D hD').trans
    (mul_le_mul_of_nonneg_left hn datumRadiusConstant_nonneg)

open A02 (SpatialField SpaceTimeField initialClassR)
open D01 (MemForceR sobolevENorm)
open A04 (forceSobolevENormL1)

/-- manuscript wording (Tao H¹ theory); not provable from the tree; see
REPORT_210 §3; the owner decides between implementing forced H¹ local theory
and a V2 narrowing. The existing `HorizonLowerBoundH1` name belongs to lane 210;
this specialization repeats its field verbatim after binding the new horizon. -/
def ManuscriptHorizonLowerBoundH1 : Prop :=
  let horizon := localHorizon'
  ∀ (ν : ℝ), 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f : SpaceTimeField),
        a ∈ initialClassR → MemForceR f →
          sobolevENorm 1 a ≤ K → forceSobolevENormL1 1 f ≤ K →
            δ ≤ horizon ν a f

/-- Data ready for V2 registration, subject to the owner's statement decision. -/
structure LocalTheoryDataShape where
  horizon : ℝ → A02.SpatialField → A02.SpaceTimeField → ℝ
  solution : ∀ (ν : ℝ) (a : A02.SpatialField) (f : A02.SpaceTimeField),
    0 < ν → a ∈ A02.initialClassR → D01.MemForceR f →
      A02.ClassicalSolutionR ν a f (horizon ν a f)
  regularity : ∀ (ν : ℝ) (a : A02.SpatialField) (f : A02.SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ A02.initialClassR) (hf : D01.MemForceR f),
      ManuscriptLocalRegularity ν a f (horizon ν a f) (solution ν a f hν ha hf)
  horizon_lower_bound_H7_fixedForce :
    ∀ ν, 0 < ν → ∀ f, D01.MemForceR f → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∃ δ > 0, ∀ a, a ∈ A02.initialClassR → D01.sobolevENorm 7 a ≤ K →
        δ ≤ horizon ν a f

/-- The shared horizon, solution, regularity and fixed-force H⁷ bound. -/
def localTheoryData : LocalTheoryDataShape where
  horizon := localHorizon'
  solution := fun ν a f hν ha hf => (localCarrier ν a f hν ha hf).w
  regularity := manuscriptLocalRegularity_localCarrier
  horizon_lower_bound_H7_fixedForce := horizon_lower_bound_H7_fixedForce

end NSFormalization.Section4.A01
