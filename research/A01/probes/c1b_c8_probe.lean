import NSFormalization.Section4.A01.CarrierBridge

noncomputable section
open MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Paper3
open NavierStokes.ProblemStatement (Space)
open FourierTransform

abbrev H0 := NSFormalization.Source.RealSobolev.RealSobolevHilbert (0:ℝ)

def Ci (i : Fin 3) : Lp Space 2 (volume : Measure Space) →L[ℝ] Lp ℂ 2 (volume : Measure Space) :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).compLpL 2 volume

theorem componentLp_eq (u : Lp Space 2 (volume : Measure Space)) (i : Fin 3) :
    componentLp (Lp.memLp u) i = Ci i u := by
  apply Lp.ext
  filter_upwards [componentLp_ae (Lp.memLp u) i,
    ContinuousLinearMap.coeFn_compLpL (Complex.ofRealCLM.comp (EuclideanSpace.proj i)) u]
    with x h1 h2
  simp only [Ci]
  rw [h1, h2]
  rfl

def orderZeroDatumCLM' : Lp Space 2 (volume : Measure Space) →L[ℝ] RealVectorSobolev (0:ℝ) :=
  (cyclesToAngularRealVector (0:ℝ)).toContinuousLinearMap.comp <|
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => H0)).symm.toContinuousLinearMap.comp <|
      ContinuousLinearMap.pi fun i =>
        (realProjectionTo (0:ℝ)).comp <|
          ((fourierCLM ℂ (Lp ℂ 2 (volume : Measure Space))).restrictScalars ℝ).comp (Ci i)

#check @orderZeroDatumCLM'

theorem orderZeroDatum_eq (u : Lp Space 2 (volume : Measure Space)) :
    orderZeroDatum (Lp.memLp u) = orderZeroDatumCLM' u := by
  have key : (fun i => realProjectionTo (0:ℝ) (𝓕 (componentLp (Lp.memLp u) i)))
      = (fun i => realProjectionTo (0:ℝ) (𝓕 (Ci i u))) := by
    funext i; rw [componentLp_eq u i]
  unfold orderZeroDatum
  rw [key]
  rfl

#check @orderZeroDatum_eq

open NSFormalization.Section4.A01

theorem continuous_orderZeroDatum' {X : Type*} [TopologicalSpace X]
    (U : X → EulerMeanSolenoidal.L2) (hU : Continuous U) :
    Continuous (fun t => orderZeroDatum (Lp.memLp (U t))) := by
  have h : (fun t => orderZeroDatum (Lp.memLp (U t))) = fun t => orderZeroDatumCLM' (U t) := by
    funext t; exact orderZeroDatum_eq (U t)
  rw [h]
  exact orderZeroDatumCLM'.continuous.comp hU

def datumPath' {T : ℝ} (U : C(Set.Icc (0:ℝ) T, EulerMeanSolenoidal.L2)) : ℝ → RealVectorSobolev (0:ℝ) :=
  fun t => if h : t ∈ Set.Icc (0:ℝ) T then orderZeroDatumCLM' (U ⟨t, h⟩) else 0

theorem continuousOn_datumPath' {T : ℝ} (U : C(Set.Icc (0:ℝ) T, EulerMeanSolenoidal.L2)) :
    ContinuousOn (datumPath' U) (Set.Ico (0:ℝ) T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hEq : (Set.Ico (0:ℝ) T).domRestrict (datumPath' U)
      = fun x => orderZeroDatumCLM' (U (Set.inclusion Set.Ico_subset_Icc_self x)) := by
    funext x
    simp only [Set.domRestrict_apply, datumPath', dite_eq_left (Set.Ico_subset_Icc_self x.2)]
  rw [hEq]
  exact orderZeroDatumCLM'.continuous.comp (U.continuous.comp (continuous_inclusion _))

theorem isSobolevDatum_zero_path' {T : ℝ}
    (U : C(Set.Icc (0:ℝ) T, EulerMeanSolenoidal.L2))
    (v : ℝ × Space → Space)
    (hv : ∀ t (ht : t ∈ Set.Ico (0:ℝ) T),
      (fun x => v (t, x)) =ᵐ[volume] ⇑(U ⟨t, Set.Ico_subset_Icc_self ht⟩)) :
    ContinuousOn (datumPath' U) (Set.Ico (0:ℝ) T) ∧
      ∀ t ∈ Set.Ico (0:ℝ) T, IsSobolevDatum 0 (fun x => v (t, x)) (datumPath' U t) := by
  refine ⟨continuousOn_datumPath' U, fun t ht => ?_⟩
  have hmem : t ∈ Set.Icc (0:ℝ) T := Set.Ico_subset_Icc_self ht
  have hdatum : datumPath' U t = orderZeroDatum (Lp.memLp (U ⟨t, hmem⟩)) := by
    simp only [datumPath', dite_eq_left hmem]
    exact (orderZeroDatum_eq (U ⟨t, hmem⟩)).symm
  rw [hdatum]
  exact IsSobolevDatum.congr_field (isSobolevDatum_zero_ordinaryL2 (U ⟨t, hmem⟩)) (hv t ht).symm

#check @continuous_orderZeroDatum'
#check @continuousOn_datumPath'
#check @isSobolevDatum_zero_path'
