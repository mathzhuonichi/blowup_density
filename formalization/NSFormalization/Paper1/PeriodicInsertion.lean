import NSFormalization.Paper1.PeriodicBridge
import NSFormalization.Source.InsertionFamily

/-!
# Actual periodic insertion from a compact whole-space perturbation

Only the perturbation is periodized. At and after the singular time its
velocity/pressure are set to zero solely to supply the globally supported
input expected by the existing periodization construction. On the entire
presingular slab the actual inserted fields are unchanged in the local chart.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicInsertion
open NavierStokes NavierStokes.ProblemStatement NavierStokes.PeriodicLocalization
open Source Source.InsertionFamily Source.LocalizedBlowup PeriodicBridge
open Set Filter MeasureTheory
open scoped ContDiff Topology

/-- This is an ordinary indicator, not an asserted continuation at T. -/
def before {E : Type*} [Zero E] (T : ℝ) (f : SpaceTime → E) : SpaceTime → E :=
  (Prod.fst ⁻¹' Iio T).indicator f

theorem before_eq {E : Type*} [Zero E] {T : ℝ} (f : SpaceTime → E)
    {z : SpaceTime} (ht : z.1 < T) : before T f z = f z :=
  indicator_of_mem (s := Prod.fst ⁻¹' Iio T) ht f

theorem before_germ {E : Type*} [Zero E] {T : ℝ} (f : SpaceTime → E)
    {z : SpaceTime} (ht : z.1 < T) : before T f =ᶠ[𝓝 z] f := by
  filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds ht] with y hy
  exact before_eq f hy

theorem before_smoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {f : SpaceTime → E}
    (hf : ContDiffOn ℝ ∞ f (Ico (0 : ℝ) T ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (before T f) (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
  hf.congr (fun _ hz => before_eq f hz.1.2)

theorem coord_abs_le_norm (x : Space) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i

/-- A compact local spatial support on the physical slab and zero earlier
history suffice for the global support condition of periodization. -/
theorem before_supported {E : Type*} [NormedAddCommGroup E] {r T : ℝ}
    {f : SpaceTime → E}
    (hs : ∀ t ∈ Ico (0 : ℝ) T, tsupport (fun x => f (t,x)) ⊆ Metric.ball 0 r)
    (hearly : ∀ t ≤ 0, ∀ x, f (t,x) = 0) : SupportedInCube r (before T f) := by
  intro z hz i
  have ht : z.1 < T := by
    by_contra hnot
    exact hz (indicator_of_notMem (s := Prod.fst ⁻¹' Iio T) hnot f)
  have hne : f z ≠ 0 := by rwa [before_eq f ht] at hz
  have ht0 : 0 ≤ z.1 := by
    by_contra hneg
    exact hne (hearly z.1 (lt_of_not_ge hneg).le z.2)
  have hball := hs z.1 ⟨ht0,ht⟩ (subset_tsupport _ hne)
  have hn : ‖z.2‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hball
  exact (coord_abs_le_norm z.2 i).trans hn.le

def velocity (T : ℝ) (v V : VelocityField) : VelocityField :=
  v + periodize (before T (V-v))

def pressure (T : ℝ) (q Q : PressureField) : PressureField :=
  q + periodize (before T (Q-q))

def force (G : VelocityField) : VelocityField := periodize G

theorem velocity_germ {T r : ℝ} {v V : VelocityField}
    (hW : SupportedInCube r (before T (V-v))) {z : SpaceTime}
    (ht : z.1 < T) (hx : z.2 ∈ innerCube r) : velocity T v V =ᶠ[𝓝 z] V := by
  have he := (periodize_eventuallyEq hW hx).trans (before_germ (V-v) ht)
  filter_upwards [he] with y hy
  change v y + periodize (before T (V-v)) y = V y
  rw [hy]
  simp

theorem pressure_germ {T r : ℝ} {q Q : PressureField}
    (hP : SupportedInCube r (before T (Q-q))) {z : SpaceTime}
    (ht : z.1 < T) (hx : z.2 ∈ innerCube r) : pressure T q Q =ᶠ[𝓝 z] Q := by
  have he := (periodize_eventuallyEq hP hx).trans (before_germ (Q-q) ht)
  filter_upwards [he] with y hy
  change q y + periodize (before T (Q-q)) y = Q y
  rw [hy]
  simp

theorem compact_future_support {G : VelocityField} (hG : HasCompactSupport G) :
    CompactFutureTimeSupport G := by
  obtain ⟨C,hC⟩ := hG.exists_bound_of_continuousOn (continuous_fst.continuousOn :
    ContinuousOn (fun z : SpaceTime => z.1) (tsupport G))
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro t ht x
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  have hb := hC (t,x) hs
  have hh : t ≤ ‖t‖ := le_abs_self t
  have hmax := le_max_left C 0
  linarith

/-- Concrete conclusions needed for periodic singular-force density. -/
structure Properties (ν r T τ : ℝ) (v : VelocityField) (q : PressureField)
    (g U F : VelocityField) (P : PressureField) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ U (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  pressure_smooth : ContDiffOn ℝ ∞ P (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  velocity_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) U
  pressure_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) P
  force_smooth : ContDiff ℝ ∞ F
  force_periodic : UnitSpatialPeriodsOn univ F
  force_future_support : CompactFutureTimeSupport F
  force_zero_before : ∀ t ≤ τ, ∀ x, F (t,x) = 0
  divergence_free : ∀ t ∈ Ico (0 : ℝ) T, ∀ x, spatialDivergence U t x = 0
  equation : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν U P t x = g (t,x)+F (t,x)
  local_speed_unbounded : LocalSpeedUnboundedAt T (Metric.closedBall 0 r) U
  history : ∀ t ≤ τ, ∀ x, U (t,x) = v (t,x) ∧ P (t,x) = q (t,x)
  force_supported_after : tsupport F ⊆ Ioi τ ×ˢ (univ : Set Space)

/-- Every previously constructed compact whole-space insertion yields an
actual periodic insertion, with the same original reference on its slab. -/
theorem of_insertion {ν r T τ : ℝ} {v V g G : VelocityField} {q Q : PressureField}
    (hτ : 0 ≤ τ) (hτT : τ < T) (hr : r < 1/2)
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hq : ContDiffOn ℝ ∞ q (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hvper : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) v)
    (hqper : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) q)
    (href : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t,x))
    (h : InsertionProperties ν v q g 0 r T τ V Q G) :
    Properties ν r T τ v q g (velocity T v V) (force G) (pressure T q Q) := by
  rcases h with ⟨hV,hQ,hGs,hGc,hGloc,⟨K,hK,hKb,hKs⟩,hdiv,hNS,_,hSpeed,hEarly⟩
  have hWs : ∀ t ∈ Ico (0 : ℝ) T, tsupport (fun x => (V-v) (t,x)) ⊆ Metric.ball 0 r :=
    fun t ht => (hKs t ht).1.trans hKb
  have hPs : ∀ t ∈ Ico (0 : ℝ) T, tsupport (fun x => (Q-q) (t,x)) ⊆ Metric.ball 0 r :=
    fun t ht => (hKs t ht).2.trans hKb
  have hWe : ∀ t ≤ 0, ∀ x, (V-v) (t,x) = 0 := by
    intro t ht x
    simp only [Pi.sub_apply,(hEarly t (ht.trans hτ) x).1,sub_self]
  have hPe : ∀ t ≤ 0, ∀ x, (Q-q) (t,x) = 0 := by
    intro t ht x
    simp only [Pi.sub_apply,(hEarly t (ht.trans hτ) x).2,sub_self]
  have hW := before_supported hWs hWe
  have hP := before_supported hPs hPe
  have hGsupport : SupportedInCube r G := by
    intro z hz i
    have hb := (hGloc (subset_tsupport _ hz)).2
    have hn : ‖z.2‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hb
    exact (coord_abs_le_norm z.2 i).trans hn.le
  have hUper : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) (velocity T v V) := by
    intro t ht x i
    exact congrArg₂ (· + ·) (hvper t ht x i)
      (unitSpatialPeriodsOn_periodize _ _ t ht x i)
  have hPper : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) (pressure T q Q) := by
    intro t ht x i
    exact congrArg₂ (· + ·) (hqper t ht x i)
      (unitSpatialPeriodsOn_periodize _ _ t ht x i)
  refine ⟨hv.add (contDiffOn_periodize hW (before_smoothOn (hV.sub hv))),
    hq.add (contDiffOn_periodize hP (before_smoothOn (hQ.sub hq))),
    hUper,hPper,contDiff_periodize hGsupport hGs,unitSpatialPeriodsOn_periodize _ univ,
    compactFutureTimeSupport_periodize (compact_future_support hGc),?_,?_,?_,?_,?_,?_⟩
  · intro t ht x
    apply periodize_eq_zero_of_timeSlice
    intro y
    exact image_eq_zero_of_notMem_tsupport (fun hz => (not_lt_of_ge ht) (hGloc hz).1)
  · have hdper : UnitSpatialPeriodsOn (Ico (0 : ℝ) T)
        (fun z => spatialDivergence (velocity T v V) z.1 z.2) := by
      intro t ht x i
      exact congrArg (fun A : Space →L[ℝ] Space => ∑ j : Fin 3, A (coordinateVector j) j)
        (ResidualRegularity.spatialDerivative_periods hUper t ht x i)
    have heq := periodic_eqOn_of_unitCube hdper
      (f := fun z => spatialDivergence (velocity T v V) z.1 z.2)
      (g := fun _ => (0 : ℝ)) (fun _ _ _ _ => rfl) (by
        intro t ht x hx
        unfold spatialDivergence
        rw [ResidualRegularity.spatialDerivative_congr
          (velocity_germ hW ht.2 (innerCube_of_unitCube hr hx))]
        exact hdiv t ht x)
    intro t ht x
    exact heq (x := (t,x)) ⟨ht,mem_univ x⟩
  · intro t ht x
    have hvI : UnitSpatialPeriodsOn (Ioo (0 : ℝ) T) v :=
      fun t ht x i => hvper t ⟨ht.1.le,ht.2⟩ x i
    have hqI : UnitSpatialPeriodsOn (Ioo (0 : ℝ) T) q :=
      fun t ht x i => hqper t ⟨ht.1.le,ht.2⟩ x i
    apply periodic_reference_pde_on ν isOpen_Ioo hvI hqI hW hP hr ht (href t ht)
    intro y
    have hvEq : v + before T (V-v) =ᶠ[𝓝 (t,y)] V := by
      filter_upwards [before_germ (V-v) ht.2] with z hz
      simp only [Pi.add_apply,hz,Pi.sub_apply]
      abel
    have hpEq : q + before T (Q-q) =ᶠ[𝓝 (t,y)] Q := by
      filter_upwards [before_germ (Q-q) ht.2] with z hz
      simp only [Pi.add_apply,hz,Pi.sub_apply]
      ring
    exact (Source.LocalReferenceHelpers.residual_congr ν hvEq hpEq).trans (hNS t ht y)
  · intro M hM δ hδ
    obtain ⟨t,x,ht,hx,hnear,hlarge⟩ := hSpeed M hM δ hδ
    have hn : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    have hcube : ∀ i : Fin 3, |x i| ≤ 1/2 :=
      fun i => ((coord_abs_le_norm x i).trans hn).trans hr.le
    refine ⟨t,x,ht,hx,hnear,?_⟩
    rwa [(velocity_germ hW ht.2 (innerCube_of_unitCube hr hcube)).self_of_nhds]
  · intro t ht x
    have hWzero : ∀ y, before T (V-v) (t,y) = 0 := by
      intro y
      rw [before_eq (V-v) (ht.trans_lt hτT)]
      simp only [Pi.sub_apply,(hEarly t ht y).1,sub_self]
    have hPzero : ∀ y, before T (Q-q) (t,y) = 0 := by
      intro y
      rw [before_eq (Q-q) (ht.trans_lt hτT)]
      simp only [Pi.sub_apply,(hEarly t ht y).2,sub_self]
    constructor
    · change v (t,x)+periodize (before T (V-v)) (t,x) = v (t,x)
      rw [periodize_eq_zero_of_timeSlice hWzero,add_zero]
    · change q (t,x)+periodize (before T (Q-q)) (t,x) = q (t,x)
      rw [periodize_eq_zero_of_timeSlice hPzero,add_zero]
  · intro z hz
    obtain ⟨y,hy,he⟩ := time_support_periodize hGc hz
    exact ⟨he ▸ (hGloc hy).1,mem_univ _⟩

end NSFormalization.Paper1.PeriodicInsertion
