import NSFormalization.Section4.A01.DatumPathContinuity

/-!
# Probe: `orderZeroDatumCLM` is injective (lane 124 review spin-off)

Verbatim copy of the lane-124 reviewer's probe `/tmp/rev124/p6b_concrete.lean`
(review `research/A01/REVIEW_C1B_C8.md` finding 6/7), credited here so the
injectivity argument is preserved outside `/tmp`.  `#print axioms` on all four
theorems = `[propext, Classical.choice, Quot.sound]`.

Content: `orderZeroDatumCLM_injective : Function.Injective orderZeroDatumCLM`
(the natural input for the still-open row `C1b-unique`, and the cheap half of the
missing order-0 Plancherel identity, `D01/OrderZeroDatum.lean:40-53`), plus a
concrete non-constant datum path `t ↦ orderZeroDatum (Lp.memLp (t • u₀))` for
`u₀ = indicatorConstLp (ball 0 1) e₀`.
-/

noncomputable section
open MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev cyclesToAngularRealVector realProjectionTo)
open NSFormalization.Source.RealSobolev
open NavierStokes.ProblemStatement (Space)
open FourierTransform
open scoped ENNReal

theorem componentCLM_eq_zero_of (w : EulerMeanSolenoidal.L2) (h : orderZeroDatumCLM w = 0)
    (i : Fin 3) : componentCLM i w = 0 := by
  have h1 : cyclesToAngularRealVector (0:ℝ)
      (WithLp.toLp 2 (fun j => realProjectionTo (0:ℝ) (𝓕 (componentCLM j w)))) = 0 := h
  have h2 := congrArg (cyclesToAngularRealVector (0:ℝ)).symm h1
  simp only [ContinuousLinearEquiv.symm_apply_apply, map_zero] at h2
  have h3 : realProjectionTo (0:ℝ) (𝓕 (componentCLM i w)) = 0 :=
    congrFun (congrArg (fun v : RealVectorSobolev (0:ℝ) => (v : Fin 3 → _)) h2) i
  -- descend out of the closed subspace
  have h4 : realProjection (𝓕 (componentCLM i w)) = 0 := congrArg Subtype.val h3
  -- the transform of a real component is conjugation-symmetric, so the projection is the identity
  have hmem : 𝓕 (componentCLM i w) ∈ realSubspace (0:ℝ) := by
    have := fourier_componentLp_mem (Lp.memLp w) i
    rwa [componentLp_eq_compLpL w i] at this
  have h5 : 𝓕 (componentCLM i w) = 0 := by
    rw [← realProjection_eq_self hmem, h4]
  -- 𝓕 is injective on L²
  have hfz : 𝓕 (0 : Lp ℂ 2 (volume : Measure Space)) = 0 :=
    map_zero (fourierCLM ℂ (Lp ℂ 2 (volume : Measure Space)))
  have hz : (𝓕⁻ (0 : Lp ℂ 2 (volume : Measure Space)) : Lp ℂ 2 (volume : Measure Space)) = 0 := by
    have hh : (𝓕⁻ (𝓕 (0 : Lp ℂ 2 (volume : Measure Space))) : Lp ℂ 2 (volume : Measure Space))
        = (0 : Lp ℂ 2 (volume : Measure Space)) := fourierInv_fourier_eq _
    rwa [hfz] at hh
  have h6 := congrArg (fun z => (𝓕⁻ z : Lp ℂ 2 (volume : Measure Space))) h5
  simpa only [fourierInv_fourier_eq, hz] using h6


theorem orderZeroDatumCLM_injective : Function.Injective orderZeroDatumCLM := by
  have key : ∀ w : EulerMeanSolenoidal.L2, orderZeroDatumCLM w = 0 → w = 0 := by
    intro w hw
    have hae : ∀ i : Fin 3, ∀ᵐ x : Space,
        (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)) ((w : Space → Space) x) = 0 := by
      intro i
      have h0 := componentCLM_eq_zero_of w hw i
      have hc := ContinuousLinearMap.coeFn_compLpL
        (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)) w
      have hz : (⇑(componentCLM i w) : Space → ℂ) =ᵐ[volume] 0 := by
        rw [h0]; exact Lp.coeFn_zero _ _ _
      have hcc : (⇑(componentCLM i w) : Space → ℂ)
          =ᵐ[volume] fun x => (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i))
            ((w : Space → Space) x) := by
        simpa only [componentCLM] using hc
      filter_upwards [hcc.symm, hz] with x hx hy
      rw [hx, hy]
      rfl
    have hall : ∀ᵐ x : Space, ∀ i : Fin 3,
        (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)) ((w : Space → Space) x) = 0 :=
      (ae_all_iff).mpr hae
    apply Lp.ext
    filter_upwards [hall, Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx hz
    rw [hz]
    ext i
    have := hx i
    simpa using this
  intro u u' h
  have : orderZeroDatumCLM (u - u') = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (key _ this)

/-- Non-vacuity: the order-0 datum of a genuinely moving `L²` path genuinely moves. -/
theorem datum_path_nonconstant (u0 : EulerMeanSolenoidal.L2) (hu0 : u0 ≠ 0) :
    Continuous (fun t : ℝ => orderZeroDatum (Lp.memLp (t • u0))) ∧
      (fun t : ℝ => orderZeroDatum (Lp.memLp (t • u0))) 1
        ≠ (fun t : ℝ => orderZeroDatum (Lp.memLp (t • u0))) 0 := by
  refine ⟨continuous_orderZeroDatum (fun t : ℝ => t • u0) (continuous_id.smul continuous_const), ?_⟩
  simp only [orderZeroDatum_memLp_eq]
  intro hcon
  apply hu0
  have : (1:ℝ) • u0 = (0:ℝ) • u0 := orderZeroDatumCLM_injective hcon
  simpa using this

/-- A concrete nonzero ordinary `L²` field: the indicator of the unit ball times `e₀`. -/
def u0 : EulerMeanSolenoidal.L2 :=
  indicatorConstLp 2 (measurableSet_ball (x := (0 : Space)) (ε := 1))
    (measure_ball_lt_top (x := (0 : Space)) (r := 1)).ne
    (EuclideanSpace.single (0 : Fin 3) (1:ℝ))

theorem u0_ne_zero : u0 ≠ 0 := by
  have hs : (volume : Measure Space) (Metric.ball (0 : Space) 1) ≠ 0 :=
    (Metric.measure_ball_pos (volume : Measure Space) (0 : Space) one_pos).ne'
  have hn : ‖u0‖ = ‖EuclideanSpace.single (0 : Fin 3) (1:ℝ)‖ *
      ((volume : Measure Space) (Metric.ball (0 : Space) 1)).toReal ^ (1 / (2:ℝ≥0∞).toReal) :=
    norm_indicatorConstLp' (by norm_num) hs
  have hc : ‖EuclideanSpace.single (0 : Fin 3) (1:ℝ)‖ = 1 := by simp
  intro h
  rw [h, norm_zero, hc, one_mul] at hn
  have hpos : (0:ℝ) < ((volume : Measure Space) (Metric.ball (0 : Space) 1)).toReal :=
    ENNReal.toReal_pos hs (measure_ball_lt_top (x := (0 : Space)) (r := 1)).ne
  exact absurd hn.symm (by positivity)

/-- The concrete non-vacuity witness the review asked for. -/
theorem concrete_nonconstant :
    Continuous (fun t : ℝ => orderZeroDatum (Lp.memLp (t • u0))) ∧
      (fun t : ℝ => orderZeroDatum (Lp.memLp (t • u0))) 1
        ≠ (fun t : ℝ => orderZeroDatum (Lp.memLp (t • u0))) 0 :=
  datum_path_nonconstant u0 u0_ne_zero

#print axioms componentCLM_eq_zero_of
#print axioms orderZeroDatumCLM_injective
#print axioms datum_path_nonconstant
#print axioms concrete_nonconstant
end
