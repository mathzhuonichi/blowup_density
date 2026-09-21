import NSFormalization.Section4.A01.L2Descent

/-! Reviewer probe (lane 153), **mutation 3** — the module's proof body run verbatim after DELETING
the `hginv` hypothesis (`autoImplicit false`, so the deleted binder cannot be silently re-bound as an
implicit argument).  Records where the route breaks.  Expected to FAIL. -/

set_option autoImplicit false

noncomputable section
namespace Rev153Mut3

open Set MeasureTheory
open NSFormalization.Section4.D01
open NavierStokes.ProblemStatement (Space coordinateVector)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open EulerLpTranslation
open NSFormalization.Source.OrdinaryCylinderDescent
open scoped ENNReal ContDiff LineDeriv

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

local instance instIsProbAddCircleOne :
    IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
  constructor
  simp [AddCircle.measure_univ]

/-- **Piece (d).**  Every angle-invariant `L²` cylinder field is the `ordinaryLift` of a
`θ`-independent ordinary `L²` field on `ℝ³`, with no jet / regularity hypothesis. -/
theorem exists_ordinaryLift_of_invariant (g : LiftL2 1) :
    ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g := by
  -- A strongly-measurable representative of `g`.
  obtain ⟨g₀, hg₀sm, hg₀ae⟩ :
      ∃ g₀ : LiftDomain 1 → Space, StronglyMeasurable g₀ ∧ (⇑g) =ᵐ[liftMeasure 1] g₀ :=
    ⟨(Lp.aestronglyMeasurable g).mk (⇑g),
      (Lp.aestronglyMeasurable g).stronglyMeasurable_mk,
      (Lp.aestronglyMeasurable g).ae_eq_mk⟩
  -- a.e. angular invariance of the representative
  have hinv0 : ∀ θ : AddCircle (1 : ℝ),
      ∀ᵐ x ∂(liftMeasure 1), g₀ x = g₀ (x + ((0 : Vector3), θ)) := by
    intro θ
    have h1 : (⇑g) =ᵐ[liftMeasure 1] fun x => (⇑g) (x + ((0 : Vector3), θ)) := by
      have h := translation_ae 1 ((0 : Vector3), θ) g
      rw [hginv θ] at h
      exact h
    have h2 : (fun x => (⇑g) (x + ((0 : Vector3), θ)))
        =ᵐ[liftMeasure 1] fun x => g₀ (x + ((0 : Vector3), θ)) :=
      (measurePreserving_translation 1 ((0 : Vector3), θ)).quasiMeasurePreserving.ae hg₀ae
    filter_upwards [hg₀ae, h1, h2] with x hx hx1 hx2
    rw [← hx, hx1, hx2]
  -- swap the a.e. quantifiers via Fubini for null sets
  have hmeas : MeasurableSet {z : AddCircle (1 : ℝ) × LiftDomain 1 |
      g₀ z.2 = g₀ (z.2 + ((0 : Vector3), z.1))} := by
    have hm : Measurable (fun z : AddCircle (1 : ℝ) × LiftDomain 1 =>
        z.2 + ((0 : Vector3), z.1)) :=
      measurable_snd.add (measurable_const.prodMk measurable_fst)
    exact measurableSet_eq_fun (hg₀sm.measurable.comp measurable_snd) (hg₀sm.measurable.comp hm)
  have hswap : ∀ᵐ pt ∂(liftMeasure 1), ∀ᵐ θ ∂(volume : Measure (AddCircle (1 : ℝ))),
      g₀ pt = g₀ (pt + ((0 : Vector3), θ)) :=
    (Measure.ae_ae_comm hmeas).mp (ae_of_all _ hinv0)
  -- the `θ`-average
  set G₀ : Space → Space := fun x => ∫ θ, g₀ (x, θ) ∂(volume : Measure (AddCircle (1 : ℝ)))
    with hG₀def
  -- slice constancy: `g₀ pt = G₀ pt.1` a.e.
  have hgG0 : ∀ᵐ pt ∂(liftMeasure 1), g₀ pt = G₀ pt.1 := by
    filter_upwards [hswap] with pt hpt
    calc g₀ pt
        = ∫ _θ : AddCircle (1 : ℝ), g₀ pt ∂volume := by rw [integral_const]; simp
      _ = ∫ θ, g₀ (pt + ((0 : Vector3), θ)) ∂volume := integral_congr_ae hpt
      _ = ∫ θ, g₀ (pt.1, pt.2 + θ) ∂volume := by
            refine integral_congr_ae (ae_of_all _ (fun θ => ?_))
            show g₀ (pt + ((0 : Vector3), θ)) = g₀ (pt.1, pt.2 + θ)
            rw [show pt + ((0 : Vector3), θ) = (pt.1, pt.2 + θ) from by simp [Prod.add_def]]
      _ = ∫ θ, g₀ (pt.1, θ) ∂volume :=
            integral_add_left_eq_self (fun θ => g₀ (pt.1, θ)) pt.2
      _ = G₀ pt.1 := by simp only [hG₀def]
  have hgfst : (⇑g) =ᵐ[liftMeasure 1] fun pt => G₀ pt.1 := hg₀ae.trans hgG0
  -- `G₀ ∈ L²(volume)`
  have hG₀aesm : AEStronglyMeasurable G₀ volume := by
    rw [hG₀def]
    exact hg₀sm.aestronglyMeasurable.integral_prod_right'
  have hmap : Measure.map (Prod.fst : LiftDomain 1 → Space) (liftMeasure 1) = volume :=
    ordinaryProjection_measurePreserving.map_eq
  have hMemLp : MemLp G₀ 2 volume := by
    have hiff := memLp_map_measure_iff (p := 2) (μ := liftMeasure 1)
      (f := (Prod.fst : LiftDomain 1 → Space)) (g := G₀)
      (by rw [hmap]; exact hG₀aesm) measurable_fst.aemeasurable
    rw [hmap] at hiff
    rw [hiff]
    exact (Lp.memLp g).ae_eq hgfst
  -- assemble
  refine ⟨hMemLp.toLp G₀, ?_⟩
  apply Lp.ext
  have h1 := ordinaryLift_ae (hMemLp.toLp G₀)
  have h2 : (fun x : LiftDomain 1 => (⇑(hMemLp.toLp G₀)) x.1)
      =ᵐ[liftMeasure 1] fun x => G₀ x.1 :=
    ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae (MemLp.coeFn_toLp hMemLp)
  filter_upwards [h1, h2, hgfst] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3]
end Rev153Mut3
