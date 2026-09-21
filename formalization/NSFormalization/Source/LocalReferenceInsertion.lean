import NSFormalization.Source.InsertionFamily
import NSFormalization.Source.LocalReferenceHelpers

/-! Fixed-profile insertion for a reference regular only on its prescribed time slab. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace NSFormalization.Source.LocalReferenceInsertion
open NavierStokes.ProblemStatement NavierStokesR3.CompactEnergy
open InsertionFamily LocalizedBlowup LocalReferenceHelpers

/-- Keep the original reference and retain exactly the auxiliary perturbation. -/
def restoreReference {E : Type*} [AddGroup E]
    (original auxiliary inserted : SpaceTime → E) : SpaceTime → E :=
  fun z => original z + (inserted z - auxiliary z)

set_option maxHeartbeats 800000 in
/-- Restore the actual reference without changing the perturbation force.
Near T this follows from equality of germs; before the auxiliary history
threshold, the perturbation and its force vanish. -/
theorem restore_insertion_properties {ν r T τ σ d : ℝ} {x₀ : Space}
    {v vhat V g G : VelocityField} {q qhat Q : PressureField}
    (hd : 0 < d) (hτσ : τ ≤ σ) (hσlate : T - d < σ)
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ univ))
    (hq : ContDiffOn ℝ ∞ q (Ico (0 : ℝ) T ×ˢ univ))
    (hvhat : ContDiff ℝ ∞ vhat) (hqhat : ContDiff ℝ ∞ qhat)
    (hvdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hvhatdiv : ∀ t x, spatialDivergence vhat t x = 0)
    (hveq : EqOn vhat v (Icc (T - d) (T + d) ×ˢ (univ : Set Space)))
    (hqeq : EqOn qhat q (Icc (T - d) (T + d) ×ˢ (univ : Set Space)))
    (hvNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t, x))
    (h : InsertionProperties ν vhat qhat (fun z => residual ν vhat qhat z.1 z.2)
      x₀ r T σ V Q G) :
    InsertionProperties ν v q g x₀ r T τ
      (restoreReference v vhat V) (restoreReference q qhat Q) G := by
  obtain ⟨hVs, hQs, hGs, hGc, hGloc, hL, hdiv, hNS, hSpeed, hLocal, hEarly⟩ := h
  have hlocal' : LocalSpeedUnboundedAt T (Metric.closedBall x₀ r) (restoreReference v vhat V) := by
    apply local_speed_congr_near hd hLocal
    intro t ht x _
    have he := hveq (x := (t, x)) ⟨⟨ht.1.le, by linarith [ht.2]⟩, mem_univ _⟩
    simp only [restoreReference, he]
    abel
  refine ⟨hv.add (hVs.sub hvhat.contDiffOn), hq.add (hQs.sub hqhat.contDiffOn), hGs, hGc,
    ?_, ?_, ?_, ?_, local_speed_implies_speed hlocal', hlocal', ?_⟩
  · intro z hz
    have hh := hGloc hz
    exact ⟨hτσ.trans_lt hh.1, hh.2⟩
  · obtain ⟨L, hLc, hLb, hLs⟩ := hL
    refine ⟨L, hLc, hLb, ?_⟩
    intro t ht
    simpa only [restoreReference, add_sub_cancel_left] using hLs t ht
  · intro t ht x
    have hvs := NavierStokes.SpatialCurl.contDiff_spatialSlice hv ht
    have hVs := NavierStokes.SpatialCurl.contDiff_spatialSlice hVs ht
    have hhs : ContDiff ℝ ∞ (fun x : Space => vhat (t, x)) :=
      hvhat.comp (contDiff_const.prodMk contDiff_id)
    change spatialDivergence (fun z => v z + (V - vhat) z) t x = 0
    rw [NavierStokes.ResidualCalculus.spatialDivergence_add _ _ t x
      (hvs.differentiable (by simp) x) ((hVs.sub hhs).differentiable (by simp) x),
      NavierStokes.PeriodicUniqueness.spatialDivergence_sub hVs hhs x,
      hvdiv t ht x, hdiv t ht x, hvhatdiv t x]
    simp
  · intro t ht x
    by_cases hnear : T - d < t
    · have htnear : t ∈ Ioo (T - d) (T + d) := ⟨hnear, by linarith [ht.2]⟩
      have hvgerm := eventuallyEq_of_time_plateau hveq htnear x
      have hqgerm := eventuallyEq_of_time_plateau hqeq htnear x
      have hVgerm : restoreReference v vhat V =ᶠ[𝓝 (t, x)] V := by
        filter_upwards [hvgerm] with z hz
        simp only [restoreReference, hz]
        abel
      have hQgerm : restoreReference q qhat Q =ᶠ[𝓝 (t, x)] Q := by
        filter_upwards [hqgerm] with z hz
        simp only [restoreReference, hz]
        ring
      have hbase : residual ν vhat qhat t x = g (t, x) :=
        (LocalReferenceHelpers.residual_congr ν hvgerm hqgerm).trans (hvNS t ht x)
      calc
        residual ν (restoreReference v vhat V) (restoreReference q qhat Q) t x =
            residual ν V Q t x := LocalReferenceHelpers.residual_congr
              (u := restoreReference v vhat V) (v := V)
              (p := restoreReference q qhat Q) (q := Q) (z := (t, x)) ν hVgerm hQgerm
        _ = residual ν vhat qhat t x + G (t, x) := hNS t ht x
        _ = g (t, x) + G (t, x) := by rw [hbase]
    · have htσ : t < σ := (le_of_not_gt hnear).trans_lt hσlate
      have htime : ∀ᶠ z : SpaceTime in 𝓝 (t, x), z.1 < σ :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds htσ
      have hVgerm : restoreReference v vhat V =ᶠ[𝓝 (t, x)] v := by
        filter_upwards [htime] with z hz
        simp only [restoreReference, (hEarly z.1 hz.le z.2).1, sub_self, add_zero]
      have hQgerm : restoreReference q qhat Q =ᶠ[𝓝 (t, x)] q := by
        filter_upwards [htime] with z hz
        simp only [restoreReference, (hEarly z.1 hz.le z.2).2, sub_self, add_zero]
      have hG0 : G (t, x) = 0 := image_eq_zero_of_notMem_tsupport
        (fun hz => (not_lt_of_ge htσ.le) (hGloc hz).1)
      rw [LocalReferenceHelpers.residual_congr
        (u := restoreReference v vhat V) (v := v)
        (p := restoreReference q qhat Q) (q := q) (z := (t, x)) ν hVgerm hQgerm,
        hvNS t ht x, hG0, add_zero]
  · intro t ht x
    have he := hEarly t (ht.trans hτσ) x
    simp only [restoreReference, he.1, he.2, sub_self, add_zero, and_self]

/-- The field keeps the original reference at every time; only its compact
correction profile is computed using the smooth auxiliary extension. -/
def velocityOn (u v vhat : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (ε : ℝ) : VelocityField := fun z =>
  v z + NSFormalization.Paper1.CorrectionProfile.physicalCorrection vhat x₀ T θ η ε z +
    parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (PacketScaling.zeroPastField u) z

/-- Actual fixed-profile families for a reference smooth only on
[0,T+δ). The auxiliary extension is made strictly inside the positive-time
regularity interval and need not solve the original global background PDE. -/
theorem exists_local_reference_insertion_family {ν δ : ℝ} (hν : 0 < ν) (hδ : 0 < δ)
    {v g : VelocityField} {q : PressureField} {T τ : ℝ}
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) (T + δ) ×ˢ univ))
    (hq : ContDiffOn ℝ ∞ q (Ico (0 : ℝ) (T + δ) ×ˢ univ))
    (hvdiv : ∀ t ∈ Ico (0 : ℝ) (T + δ), ∀ x, spatialDivergence v t x = 0)
    (hτ0 : 0 ≤ τ) (hτT : τ < T)
    (hvNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t, x))
    (x₀ : Space) {r : ℝ} (hr : 0 < r) :
    ∃ vhat : VelocityField, ∃ u : VelocityField, ∃ p : PressureField,
    ∃ f : VelocityField, ∃ K : Set Space, ∃ θ : Space → ℝ, ∃ η : ℝ → ℝ, ∃ ε₀ : ℝ,
      ContDiff ℝ ∞ vhat ∧ (∀ t x, spatialDivergence vhat t x = 0) ∧
      NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K ∧
      IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) ∧
      ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ η ∧
      HasCompactSupport θ ∧ HasCompactSupport η ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        InsertionProperties ν v q g x₀ r T τ
          (velocityOn u v vhat x₀ T θ η ε) (pressure p q x₀ T ε)
          (force ν f vhat x₀ T θ η ε) := by
  have hT : 0 < T := hτ0.trans_lt hτT
  let d := min (T / 4) (δ / 4)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdT : d ≤ T / 4 := min_le_left _ _
  have hdδ : d ≤ δ / 4 := min_le_right _ _
  have hwindow : Ioo (T - 2 * d) (T + 2 * d) ⊆ Ico (0 : ℝ) (T + δ) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨vhat, qhat, hvhat, hqhat, hvhatdiv, hveq, hqeq⟩ :=
    exists_reference_pair_extension T d hd
      (hv.mono (Set.prod_mono hwindow Subset.rfl))
      (hq.mono (Set.prod_mono hwindow Subset.rfl))
      (fun t ht => hvdiv t (hwindow ht))
  let σ := max τ (T - d / 2)
  have hτσ : τ ≤ σ := le_max_left _ _
  have hσ0 : 0 ≤ σ := hτ0.trans hτσ
  have hσT : σ < T := max_lt hτT (by linarith)
  have hσlate : T - d < σ := by have := le_max_right τ (T - d / 2); dsimp [σ]; linarith
  obtain ⟨u, p, f, K, θ, η, ε₀, hc, hD, hθ, hη, hθc, hηc, hε₀, hfamily⟩ :=
    exists_insertion_family hν hvhat hqhat hvhatdiv x₀ hr hσ0 hσT
      (g := fun z => residual ν vhat qhat z.1 z.2) (fun _ _ _ => rfl)
  have hpre : Ico (0 : ℝ) T ⊆ Ico (0 : ℝ) (T + δ) := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  refine ⟨vhat, u, p, f, K, θ, η, ε₀, hvhat, hvhatdiv, hc, hD,
    hθ, hη, hθc, hηc, hε₀, ?_⟩
  intro ε hε
  have hp := restore_insertion_properties hd hτσ hσlate
    (hv.mono (Set.prod_mono hpre Subset.rfl)) (hq.mono (Set.prod_mono hpre Subset.rfl))
    hvhat hqhat (fun t ht => hvdiv t (hpre ht)) hvhatdiv hveq hqeq hvNS (hfamily ε hε)
  have heV : restoreReference v vhat (velocity u vhat x₀ T θ η ε) = velocityOn u v vhat x₀ T θ η ε := by
    funext z
    simp only [restoreReference, velocity, velocityOn]
    abel
  have heQ : restoreReference q qhat (pressure p qhat x₀ T ε) = pressure p q x₀ T ε := by
    funext z
    simp only [restoreReference, pressure]
    ring
  rwa [heV, heQ] at hp

end NSFormalization.Source.LocalReferenceInsertion
