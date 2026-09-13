import NavierStokes.R3SmoothPressure
import NavierStokes.R3TimeLocalization

/-!
# Pressure recovery after compact time localization

A smooth equation on an open time interval is multiplied by a compact time
cutoff. The time derivative of the cutoff is included explicitly in the
momentum equation, and all fields become global smooth space-time fields.
-/

noncomputable section
namespace NavierStokes.R3LocalizedPressure

open Set Filter MeasureTheory TemperedDistribution
open R3SpaceTime R3SpaceTimePressure R3WeakPressure R3TimeLocalization
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal

theorem directional_contDiffOn {s : Set Domain} (hs : IsOpen s) {u : Domain → ℂ}
    (hu : ContDiffOn ℝ ∞ u s) (m : Domain) : ContDiffOn ℝ ∞ (directional m u) s :=
  (hu.fderiv_of_isOpen hs (by simp)).clm_apply contDiffOn_const

theorem directional_localize_of_mem {s : Set ℝ} (hs : IsOpen s) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {u : Domain → ℂ} (hu : ContDiffOn ℝ ∞ u (timeProj ⁻¹' s))
    {z : Domain} (hz : timeProj z ∈ s) (m : Domain) :
    directional m (localize a u) z =
      ((deriv a (timeProj z) * timeProj m : ℝ) : ℂ) * u z +
      (a (timeProj z) : ℂ) * directional m u z := by
  have hud := ((hu z hz).contDiffAt ((hs.preimage timeProj.continuous).mem_nhds hz)).differentiableAt (by simp)
  have had := (ha.differentiable (by simp) (timeProj z)).hasDerivAt
  have hA := Complex.ofRealCLM.hasFDerivAt.comp z (had.comp_hasFDerivAt z timeProj.hasFDerivAt)
  unfold directional localize
  change (fderiv ℝ ((Complex.ofRealCLM ∘ a ∘ timeProj) * u) z) m = _
  rw [(hA.mul hud.hasFDerivAt).fderiv]
  simp
  ring

theorem localize_eventually_zero {a : ℝ → ℝ} {u : Domain → ℂ} {z : Domain}
    (hz : timeProj z ∉ tsupport a) : localize a u =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
  have hzero := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto timeProj.continuous.continuousAt
  filter_upwards [hzero] with y hy
  change a (timeProj y) = 0 at hy
  simp [localize, hy]

theorem directional_localize_space {s : Set ℝ} (hs : IsOpen s) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (has : tsupport a ⊆ s) {u : Domain → ℂ}
    (hu : ContDiffOn ℝ ∞ u (timeProj ⁻¹' s)) (i : Fin 3) :
    directional (spaceDirection i) (localize a u) = localize a (directional (spaceDirection i) u) := by
  funext z
  by_cases hz : timeProj z ∈ tsupport a
  · rw [directional_localize_of_mem hs ha hu (has hz)]
    simp [localize, timeProj, spaceDirection, WithLp.fstL]
  · have hd := (localize_eventually_zero (u := u) hz).fderiv_eq (𝕜 := ℝ)
    have hzero := image_eq_zero_of_notMem_tsupport hz
    simp only [directional, hd, fderiv_const_apply, zero_apply,
      localize, hzero, Complex.ofReal_zero, zero_mul]

theorem directional_localize_time {s : Set ℝ} (hs : IsOpen s) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (has : tsupport a ⊆ s) {u : Domain → ℂ}
    (hu : ContDiffOn ℝ ∞ u (timeProj ⁻¹' s)) :
    directional timeDirection (localize a u) =
      fun z => localize (deriv a) u z + localize a (directional timeDirection u) z := by
  funext z
  by_cases hz : timeProj z ∈ tsupport a
  · rw [directional_localize_of_mem hs ha hu (has hz)]
    simp [localize, timeProj, timeDirection, WithLp.fstL]
  · have hd := (localize_eventually_zero (u := u) hz).fderiv_eq (𝕜 := ℝ)
    have hzero := image_eq_zero_of_notMem_tsupport hz
    have hderiv : deriv a (timeProj z) = 0 := by
      have he := (notMem_tsupport_iff_eventuallyEq.mp hz).deriv_eq
      simpa using he
    simp only [directional, hd, fderiv_const_apply, zero_apply,
      localize, hzero, hderiv, Complex.ofReal_zero, zero_mul, add_zero]

theorem laplacian_localize {s : Set ℝ} (hs : IsOpen s) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (has : tsupport a ⊆ s) {u : Domain → ℂ}
    (hu : ContDiffOn ℝ ∞ u (timeProj ⁻¹' s)) :
    functionLaplacian (localize a u) = localize a (functionLaplacian u) := by
  funext z
  unfold functionLaplacian
  simp only [directional_localize_space hs ha has hu,
    directional_localize_space hs ha has (directional_contDiffOn (hs.preimage timeProj.continuous) hu _),
    localize, Finset.mul_sum]

theorem divergence_localize {s : Set ℝ} (hs : IsOpen s) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (has : tsupport a ⊆ s) {U : Fin 3 → Domain → ℂ}
    (hu : ∀ i, ContDiffOn ℝ ∞ (U i) (timeProj ⁻¹' s)) :
    functionDivergence (fun i => localize a (U i)) = localize a (functionDivergence U) := by
  funext z
  unfold functionDivergence
  simp only [directional_localize_space hs ha has (hu _), localize, Finset.mul_sum]

theorem momentum_localize {s : Set ℝ} (hs : IsOpen s) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (has : tsupport a ⊆ s)
    {U : Fin 3 → Domain → ℂ} {G : Fin 3 → Fin 3 → Domain → ℂ}
    (hu : ∀ i, ContDiffOn ℝ ∞ (U i) (timeProj ⁻¹' s))
    (hg : ∀ i j, ContDiffOn ℝ ∞ (G i j) (timeProj ⁻¹' s)) (i : Fin 3) :
    functionMomentum (fun i => localize a (U i)) (fun i => localize (deriv a) (U i))
      (fun i j => localize a (G i j)) i =
      localize a (functionMomentum U (fun _ _ => 0) G i) := by
  funext z
  have hsum : (∑ j : Fin 3, (a (timeProj z) : ℂ) * directional (spaceDirection j) (G i j) z) =
      (a (timeProj z) : ℂ) * ∑ j : Fin 3, directional (spaceDirection j) (G i j) z :=
    (Finset.mul_sum _ _ _).symm
  simp only [functionMomentum, laplacian_localize hs ha has (hu i),
    directional_localize_time hs ha has (hu i),
    directional_localize_space hs ha has (hg _ _), localize, hsum]
  ring

/-- The compactly localized physical pressure satisfies the canonical
pressure-gradient identity. Uniform spatial norms are the only global
bounds required on the original fields. -/
theorem localized_pressure_gradient {s : Set ℝ} (hs : IsOpen s)
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (has : tsupport a ⊆ s)
    (U : Fin 3 → Domain → ℂ) (G : Fin 3 → Fin 3 → Domain → ℂ) (p : Domain → ℂ)
    (hu : ∀ i, ContDiffOn ℝ ∞ (U i) (timeProj ⁻¹' s))
    (hg : ∀ i j, ContDiffOn ℝ ∞ (G i j) (timeProj ⁻¹' s))
    (hp : ContDiffOn ℝ ∞ p (timeProj ⁻¹' s))
    (U2 : ∀ i t, t ∈ s → MemLp (fun x => U i (pack t x)) 2)
    (G1 : ∀ i j t, t ∈ s → Integrable (fun x => G i j (pack t x)))
    (CU CG : ℝ)
    (boundU : ∀ i t, t ∈ s → (∫ x : ProblemStatement.Space, ‖U i (pack t x)‖ ^ 2) ≤ CU)
    (boundG : ∀ i j t, t ∈ s → (∫ x : ProblemStatement.Space, ‖G i j (pack t x)‖) ≤ CG)
    (divU : ∀ z, timeProj z ∈ s → functionDivergence U z = 0)
    (eqn : ∀ i z, timeProj z ∈ s →
      functionMomentum U (fun _ _ => 0) G i z = directional (spaceDirection i) p z) :
    ∃ gLp : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Domain),
      (∀ i j, gLp i j =ᵐ[volume] localize a (G i j)) ∧
      ∀ i, Represents (∂_{spaceDirection i} (stressPressure gLp))
        (localize a (directional (spaceDirection i) p)) := by
  have had : ContDiff ℝ ∞ (deriv a) := ha.deriv'
  have hadc : HasCompactSupport (deriv a) := hac.deriv
  have hads : tsupport (deriv a) ⊆ s := (tsupport_deriv_subset).trans has
  have smoothU i := localize_contDiff ha hs has (hu i)
  have smoothV i := localize_contDiff had hs hads (hu i)
  have smoothG i j := localize_contDiff ha hs has (hg i j)
  have smoothP := localize_contDiff ha hs has hp
  have in_s {b : ℝ → ℝ} (hbs : tsupport b ⊆ s) {t : ℝ} (ht : b t ≠ 0) : t ∈ s :=
    hbs (subset_tsupport _ ht)
  have hU i : MemLp (localize a (U i)) 2 := localize_memLp_two
    (ha.continuous.memLp_of_hasCompactSupport hac) (smoothU i).continuous.aestronglyMeasurable
    (fun t ht => U2 i t (in_s has ht)) (fun t ht => boundU i t (in_s has ht))
  have hV i : MemLp (localize (deriv a) (U i)) 2 := localize_memLp_two
    (had.continuous.memLp_of_hasCompactSupport hadc) (smoothV i).continuous.aestronglyMeasurable
    (fun t ht => U2 i t (in_s hads ht)) (fun t ht => boundU i t (in_s hads ht))
  have hG i j : MemLp (localize a (G i j)) 1 := memLp_one_iff_integrable.mpr (localize_integrable
    (ha.continuous.integrable_of_hasCompactSupport hac) (smoothG i j).continuous.aestronglyMeasurable
    (fun t ht => G1 i j t (in_s has ht)) (fun t ht => boundG i j t (in_s has ht)))
  refine ⟨fun i j => (hG i j).toLp _, fun i j => (hG i j).coeFn_toLp, ?_⟩
  intro i
  rw [← directional_localize_space hs ha has hp]
  apply smooth_pressure_gradient (fun i => localize a (U i)) (fun i => localize (deriv a) (U i))
    (fun i j => localize a (G i j)) (localize a p) hU hV hG smoothU smoothV smoothG smoothP
  · intro z
    rw [divergence_localize hs ha has hu]
    by_cases hz : a (timeProj z) = 0
    · simp [localize, hz]
    · simp [localize, divU z (in_s has hz)]
  · intro z
    rw [divergence_localize hs had hads hu]
    by_cases hz : deriv a (timeProj z) = 0
    · simp [localize, hz]
    · simp [localize, divU z (in_s hads hz)]
  · intro j z
    rw [momentum_localize hs ha has hu hg, directional_localize_space hs ha has hp]
    by_cases hz : a (timeProj z) = 0
    · simp [localize, hz]
    · simp [localize, eqn j z (in_s has hz)]

end NavierStokes.R3LocalizedPressure
