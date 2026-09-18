import NSFormalization.Section3.T11.Restart
import NSFormalization.Section3.T11.Uniqueness
import NSFormalization.Section4.A04.ShiftedExtension

/-!
# Restart past an unattained torus horizon

This module supplies the `restartBeyond` field of `PeriodicContinuationAPI`
(`research/T11/probes/api_on_canonical.lean`), conditional only on the single
named input `PeriodicQuantitativeLocalInput'` consumed through `restart`.

The route is the periodic-data counterpart of the Section 4 interior overlap
paste (`Section4.A04.ShiftedExtension`).  A classical torus solution is
translated to an interior basepoint `b` (`shiftedSolutionT`), compared with a
restarted solution for the shifted force by the canonical common-interval
uniqueness theorems, and pasted strictly inside the overlap
(`glueClassicalSolutionT`).  Two differences from the `R³` module are
structural: the T10 pressure carries the Haar gauge `∫_{T³} p(t) = 0` as a
structure field, so no auxiliary basepoint normalization is needed and the
overlap pressures agree *exactly*; and the three extra T10 fields (integer
Fourier data, torus pressure gradient, gauge) have to be pasted as well.

The elementary overlap calculus (`overlapPaste`, `contDiffOn_overlap`,
`continuousOn_overlap`, `residual_eq_of_local_slices`) is type-generic and is
reused verbatim from `Section4.A04` rather than restated.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Paper1
open NSFormalization.Paper1.PeriodicLocalLifespan
open NSFormalization.Section4.A04 (overlapPaste overlapPaste_left overlapPaste_right
  contDiffOn_overlap continuousOn_overlap residual_eq_of_local_slices)
open scoped ContDiff ENNReal

/-! ## Slices and restriction of a classical torus solution -/

/-- The velocity slice of a classical torus solution has the time derivative
`∂_t u` at every interior time.  Torus analogue of
`Section4.C01.velocity_hasDerivAt_time`. -/
theorem velocity_hasDerivAt_timeT {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) (x : Space) :
    HasDerivAt (fun ρ : ℝ => w.velocity (ρ, x)) (temporalDerivative w.velocity s x) s := by
  have hmap : ContDiffOn ℝ ∞ (fun r : ℝ => ((r, x) : ℝ × Space)) (Ico (0 : ℝ) T) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hsub : (Ico (0 : ℝ) T) ⊆
      (fun r : ℝ => ((r, x) : ℝ × Space)) ⁻¹' (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    fun r hr => ⟨hr, mem_univ x⟩
  have hcd : ContDiffOn ℝ ∞ (fun r => w.velocity (r, x)) (Ico (0 : ℝ) T) :=
    w.velocity_smooth.comp hmap hsub
  exact ((hcd.differentiableOn (by simp) s (Ioo_subset_Ico_self hs)).differentiableAt
    (Ico_mem_nhds hs.1 hs.2)).hasDerivAt

/-- Every interior velocity slice of a classical torus solution is an
admissible restart datum. -/
theorem velocitySlice_mem_initialClassT {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) {b : ℝ} (hb : b ∈ Ico (0 : ℝ) T) :
    (fun x => w.velocity (b, x)) ∈ initialClassT := by
  refine ⟨?_, ?_, ?_⟩
  · exact w.velocity_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun _ => ⟨⟨hb.1, hb.2⟩, mem_univ _⟩)
  · intro x i
    exact w.velocity_periodic b hb x i
  · exact w.divergence b hb

/-- A classical torus solution restricts to every shorter positive horizon,
with literally the same velocity and pressure. -/
def restrictClassicalSolutionT {ν T T' : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hT' : 0 < T') (hle : T' ≤ T) :
    ClassicalSolutionT ν a f T' where
  velocity := w.velocity
  pressure := w.pressure
  horizon_pos := hT'
  velocity_smooth :=
    w.velocity_smooth.mono (prod_mono (Ico_subset_Ico_right hle) subset_rfl)
  pressure_smooth :=
    w.pressure_smooth.mono (prod_mono (Ico_subset_Ico_right hle) subset_rfl)
  initial := w.initial
  divergence := fun t ht => w.divergence t (Ico_subset_Ico_right hle ht)
  momentum := fun t ht => w.momentum t (Ioo_subset_Ioo_right hle ht)
  sobolev := fun m => by
    obtain ⟨G, hGc, hG⟩ := w.sobolev m
    exact ⟨G, hGc.mono (Ico_subset_Ico_right hle),
      fun t ht => hG t (Ico_subset_Ico_right hle ht)⟩
  pressure_gradient := fun t ht => w.pressure_gradient t (Ico_subset_Ico_right hle ht)
  velocity_periodic := fun t ht => w.velocity_periodic t (Ico_subset_Ico_right hle ht)
  pressure_periodic := fun t ht => w.pressure_periodic t (Ico_subset_Ico_right hle ht)
  pressure_gauge := fun t ht => w.pressure_gauge t (Ico_subset_Ico_right hle ht)

@[simp] theorem restrictClassicalSolutionT_velocity {ν T T' : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) (hT' : 0 < T') (hle : T' ≤ T) :
    (restrictClassicalSolutionT w hT' hle).velocity = w.velocity := rfl

@[simp] theorem restrictClassicalSolutionT_pressure {ν T T' : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) (hT' : 0 < T') (hle : T' ≤ T) :
    (restrictClassicalSolutionT w hT' hle).pressure = w.pressure := rfl

/-- One classical solution solves below its own horizon. -/
theorem solvesBelowT_of_classicalSolutionT {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) :
    SolvesBelowT ν a f T w.velocity w.pressure :=
  fun _ hb0 hbT => ⟨restrictClassicalSolutionT w hb0 hbT.le, rfl, rfl⟩

/-! ## Time translation of a classical torus solution -/

/-- Translating a classical torus solution to an interior basepoint `b` gives a
classical solution of the `b`-shifted problem on `[0, T - b)`.  All three extra
T10 fields translate: the Fourier path is reindexed, and both the torus
pressure gradient and the Haar gauge are slicewise conditions. -/
def shiftedSolutionT {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (b : ℝ) (hb : b ∈ Ico (0 : ℝ) T) :
    ClassicalSolutionT ν (fun x => w.velocity (b, x)) (timeShiftT b f) (T - b) where
  velocity := timeShiftT b w.velocity
  pressure := fun z => w.pressure (z.1 + b, z.2)
  horizon_pos := sub_pos.mpr hb.2
  velocity_smooth := w.velocity_smooth.comp
    ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
    (fun z hz => ⟨⟨by linarith [hz.1.1, hb.1], by linarith [hz.1.2]⟩, mem_univ _⟩)
  pressure_smooth := w.pressure_smooth.comp
    ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
    (fun z hz => ⟨⟨by linarith [hz.1.1, hb.1], by linarith [hz.1.2]⟩, mem_univ _⟩)
  initial := fun x => by simp [timeShiftT, NSFormalization.Section4.A04.timeShift]
  divergence := fun t ht x => w.divergence (t + b)
    ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩ x
  momentum := by
    intro t ht x
    have ht' : t + b ∈ Ioo (0 : ℝ) T :=
      ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩
    have hd := velocity_hasDerivAt_timeT w ht' x
    have hs := hd.scomp t ((hasDerivAt_id t).add_const b)
    have he : temporalDerivative (timeShiftT b w.velocity) t x =
        temporalDerivative w.velocity (t + b) x := by
      simpa [temporalDerivative, timeShiftT, NSFormalization.Section4.A04.timeShift,
        Function.comp_def] using
        congrArg (fun D : ℝ →L[ℝ] Space => D 1) hs.hasFDerivAt.fderiv
    change temporalDerivative (timeShiftT b w.velocity) t x + _ - _ + _ = _
    rw [he]
    simpa only [NavierStokesR3.ProblemStatement.navierStokesResidual, advection,
      spatialLaplacian, spatialDerivative, pressureGradient, timeShiftT,
      NSFormalization.Section4.A04.timeShift] using w.momentum (t + b) ht' x
  sobolev := fun m => by
    obtain ⟨G, hGc, hG⟩ := w.sobolev m
    exact ⟨fun t => G (t + b),
      hGc.comp (continuous_id.add continuous_const).continuousOn
        (fun t ht => ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩),
      fun t ht => hG (t + b) ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩⟩
  pressure_gradient := fun t ht => by
    simpa [pressureGradient] using w.pressure_gradient (t + b)
      ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩
  velocity_periodic := fun t ht x i =>
    w.velocity_periodic (t + b) ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩ x i
  pressure_periodic := fun t ht x i =>
    w.pressure_periodic (t + b) ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩ x i
  pressure_gauge := fun t ht => w.pressure_gauge (t + b)
    ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩

/-- Translate a solution of the `b`-shifted problem back to the original clock:
it satisfies the original residual equation at the original times. -/
theorem restartedResidualT {ν b L : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a (timeShiftT b f) L) {t : ℝ}
    (ht : t - b ∈ Ioo (0 : ℝ) L) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν
      (fun z => w.velocity (z.1 - b, z.2))
      (fun z => w.pressure (z.1 - b, z.2)) t x = f (t, x) := by
  have hd := velocity_hasDerivAt_timeT w ht x
  have hs := hd.scomp t ((hasDerivAt_id t).sub_const b)
  have he : temporalDerivative (fun z => w.velocity (z.1 - b, z.2)) t x =
      temporalDerivative w.velocity (t - b) x := by
    simpa [temporalDerivative, Function.comp_def] using
      congrArg (fun D : ℝ →L[ℝ] Space => D 1) hs.hasFDerivAt.fderiv
  change temporalDerivative (fun z => w.velocity (z.1 - b, z.2)) t x + _ - _ + _ = _
  rw [he]
  simpa only [NavierStokesR3.ProblemStatement.navierStokesResidual, advection,
    spatialLaplacian, spatialDerivative, pressureGradient, timeShiftT,
    NSFormalization.Section4.A04.timeShift, sub_add_cancel] using w.momentum (t - b) ht x

/-! ## Common-interval agreement without the input classes

`velocity_unique` and `pressure_unique` (lane 315) carry the hypotheses
`a ∈ initialClassT` and `f ∈ forceClassT`.  Neither is available for the
*shifted* problem: `timeShiftT b f` has its compact time support translated to
the left and generally leaves `forceClassT`.  Both hypotheses are unused in the
Paper 1 route, so the two agreement statements are restated without them. -/

/-- Common-interval velocity agreement for two solutions of the same periodic
problem, with no hypothesis on the data classes. -/
theorem shifted_velocity_uniqueT {ν : ℝ} (hν : 0 < ν)
    {a : SpatialField} {g : SpaceTimeField}
    {T₁ T₂ : ℝ} (u₁ : ClassicalSolutionT ν a g T₁)
    (u₂ : ClassicalSolutionT ν a g T₂) :
    ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
      u₁.velocity (t, x) = u₂.velocity (t, x) :=
  fun t ht x =>
    NSFormalization.Paper1.PeriodicLocalLifespan.flow_velocity_agree_on_common_interval
      hν (toFlow u₁) (toFlow u₂) t ht x

/-- Common-interval pressure agreement.  Both pressures are gauge-normalized by
the `pressure_gauge` field, so the agreement is exact, with no additive
function of time. -/
theorem shifted_pressure_uniqueT {ν : ℝ} (hν : 0 < ν)
    {a : SpatialField} {g : SpaceTimeField}
    {T₁ T₂ : ℝ} (u₁ : ClassicalSolutionT ν a g T₁)
    (u₂ : ClassicalSolutionT ν a g T₂) :
    ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
      u₁.pressure (t, x) = u₂.pressure (t, x) := by
  intro t ht x
  have hnorm₁ : IsNormalized (toFlow u₁) := by
    intro s hs
    rw [← integral_torusLift]
    exact u₁.pressure_gauge s hs
  have hnorm₂ : IsNormalized (toFlow u₂) := by
    intro s hs
    rw [← integral_torusLift]
    exact u₂.pressure_gauge s hs
  exact (NSFormalization.Paper1.PeriodicLocalLifespan.normalized_flows_agree
    hν (toFlow u₁) (toFlow u₂) hnorm₁ hnorm₂ t ht x).2

/-! ## The exported overlap constructor -/

/-- **Gluing constructor.**  A classical torus solution `w` on `[0, T)` and a
restart `w₂` from its interior slice `u(b, ·)` for the `b`-shifted force paste
into one classical torus solution on `[0, b + L)`, agreeing with `w` on the
whole of `[0, T)`.  The seam is placed at `(b+T)/2`, strictly inside the
overlap `[b, T)`, so no terminal time is crossed. -/
theorem glueClassicalSolutionT {ν T b L : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (w : ClassicalSolutionT ν a f T)
    (hb : b ∈ Ico (0 : ℝ) T)
    (w₂ : ClassicalSolutionT ν (fun x => w.velocity (b, x)) (timeShiftT b f) L)
    (hTL : T < b + L) :
    ∃ v : ClassicalSolutionT ν a f (b + L),
      (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, v.velocity (t, x) = w.velocity (t, x)) ∧
      (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, v.pressure (t, x) = w.pressure (t, x)) := by
  have hbc : b < (b + T) / 2 := by linarith [hb.2]
  have hcT : (b + T) / 2 < T := by linarith [hb.2]
  have hv : ∀ t ∈ Ico b T, (fun x => w.velocity (t, x)) =
      (fun x => w₂.velocity (t - b, x)) := by
    intro t ht
    funext x
    have he := shifted_velocity_uniqueT hν (shiftedSolutionT w b hb) w₂ (t - b)
      ⟨by linarith [ht.1], lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    simpa [shiftedSolutionT, timeShiftT,
      NSFormalization.Section4.A04.timeShift] using he
  have hp : ∀ t ∈ Ico b T, (fun x => w.pressure (t, x)) =
      (fun x => w₂.pressure (t - b, x)) := by
    intro t ht
    funext x
    have he := shifted_pressure_uniqueT hν (shiftedSolutionT w b hb) w₂ (t - b)
      ⟨by linarith [ht.1], lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    simpa [shiftedSolutionT] using he
  let u : SpaceTimeField := fun z =>
    overlapPaste ((b + T) / 2) (fun t x => w.velocity (t, x))
      (fun t x => w₂.velocity (t - b, x)) z.1 z.2
  let p : SpaceTimeScalar := fun z =>
    overlapPaste ((b + T) / 2) (fun t x => w.pressure (t, x))
      (fun t x => w₂.pressure (t - b, x)) z.1 z.2
  have hul : ∀ t ∈ Ico 0 T, (fun x => u (t, x)) = (fun x => w.velocity (t, x)) :=
    fun t ht => overlapPaste_left hbc hv ht
  have hur : ∀ t ∈ Ico b (b + L), (fun x => u (t, x)) =
      (fun x => w₂.velocity (t - b, x)) := fun t ht => overlapPaste_right hcT hv ht
  have hpl : ∀ t ∈ Ico 0 T, (fun x => p (t, x)) = (fun x => w.pressure (t, x)) :=
    fun t ht => overlapPaste_left hbc hp ht
  have hpr : ∀ t ∈ Ico b (b + L), (fun x => p (t, x)) =
      (fun x => w₂.pressure (t - b, x)) := fun t ht => overlapPaste_right hcT hp ht
  have hshift : MapsTo (fun z : SpaceTime => (z.1 - b, z.2))
      (Ico b (b + L) ×ˢ (univ : Set Space)) (Ico 0 L ×ˢ (univ : Set Space)) := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, mem_univ _⟩
  refine ⟨{
    velocity := u
    pressure := p
    horizon_pos := by linarith [w.horizon_pos]
    velocity_smooth := contDiffOn_overlap hb.2
      (w.velocity_smooth.congr (fun z hz => congrFun (hul z.1 hz.1) z.2))
      ((w₂.velocity_smooth.comp
        ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn hshift).congr
          (fun z hz => congrFun (hur z.1 hz.1) z.2))
    pressure_smooth := contDiffOn_overlap hb.2
      (w.pressure_smooth.congr (fun z hz => congrFun (hpl z.1 hz.1) z.2))
      ((w₂.pressure_smooth.comp
        ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn hshift).congr
          (fun z hz => congrFun (hpr z.1 hz.1) z.2))
    initial := fun x => (congrFun (hul 0 ⟨le_rfl, w.horizon_pos⟩) x).trans (w.initial x)
    divergence := by
      intro t ht x
      by_cases h : t < T
      · have he := hul t ⟨ht.1, h⟩
        simpa only [spatialDivergence, spatialDerivative, he] using w.divergence t ⟨ht.1, h⟩ x
      · have hbt : b ≤ t := by linarith [hb.2]
        have he := hur t ⟨hbt, ht.2⟩
        simpa only [spatialDivergence, spatialDerivative, he] using
          w₂.divergence (t - b) ⟨by linarith, by linarith [ht.2]⟩ x
    momentum := by
      intro t ht x
      by_cases h : t < T
      · have he : ∀ᶠ s in 𝓝 t, ∀ y, u (s, y) = w.velocity (s, y) := by
          filter_upwards [Ioo_mem_nhds ht.1 h] with s hs y
          exact congrFun (hul s ⟨hs.1.le, hs.2⟩) y
        rw [residual_eq_of_local_slices he (hpl t ⟨ht.1.le, h⟩) x]
        exact w.momentum t ⟨ht.1, h⟩ x
      · have hbt : b < t := by linarith [hb.2]
        have he : ∀ᶠ s in 𝓝 t, ∀ y, u (s, y) = w₂.velocity (s - b, y) := by
          filter_upwards [Ioo_mem_nhds hbt ht.2] with s hs y
          exact congrFun (hur s ⟨hs.1.le, hs.2⟩) y
        rw [residual_eq_of_local_slices
          (v := fun z => w₂.velocity (z.1 - b, z.2))
          (q := fun z => w₂.pressure (z.1 - b, z.2)) he (hpr t ⟨hbt.le, ht.2⟩) x]
        exact restartedResidualT w₂ ⟨by linarith, by linarith [ht.2]⟩ x
    sobolev := by
      intro m
      obtain ⟨G, hGc, hG⟩ := w.sobolev m
      obtain ⟨F, hFc, hF⟩ := w₂.sobolev m
      have hGF : ∀ t ∈ Ico b T, G t = F (t - b) := by
        intro t ht
        apply datum_unique (m : ℝ) (fun x => w.velocity (t, x)) (G t) (F (t - b))
          (hG t ⟨hb.1.trans ht.1, ht.2⟩)
        rw [hv t ht]
        exact hF (t - b) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      refine ⟨overlapPaste ((b + T) / 2) G (fun t => F (t - b)),
        continuousOn_overlap hb.2
          ((hGc.congr (fun t ht => overlapPaste_left hbc hGF ht)))
          ((hFc.comp (continuous_id.sub continuous_const).continuousOn
            (fun t ht => ⟨by show 0 ≤ t - b; linarith [ht.1],
              by show t - b < L; linarith [ht.2]⟩)).congr
            (fun t ht => overlapPaste_right hcT hGF ht)), ?_⟩
      intro t ht
      by_cases h : t < T
      · rw [overlapPaste_left hbc hGF ⟨ht.1, h⟩, hul t ⟨ht.1, h⟩]
        exact hG t ⟨ht.1, h⟩
      · have hbt : b ≤ t := by linarith [hb.2]
        rw [overlapPaste_right hcT hGF ⟨hbt, ht.2⟩, hur t ⟨hbt, ht.2⟩]
        exact hF (t - b) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    pressure_gradient := by
      intro t ht
      by_cases h : t < T
      · simpa only [pressureGradient, hpl t ⟨ht.1, h⟩] using w.pressure_gradient t ⟨ht.1, h⟩
      · have hbt : b ≤ t := by linarith [hb.2]
        simpa only [pressureGradient, hpr t ⟨hbt, ht.2⟩] using
          w₂.pressure_gradient (t - b) ⟨by linarith, by linarith [ht.2]⟩
    velocity_periodic := by
      intro t ht x i
      by_cases h : t < T
      · have he := hul t ⟨ht.1, h⟩
        calc
          u (t, x + coordinateVector i)
              = w.velocity (t, x + coordinateVector i) := congrFun he _
          _ = w.velocity (t, x) := w.velocity_periodic t ⟨ht.1, h⟩ x i
          _ = u (t, x) := (congrFun he _).symm
      · have hbt : b ≤ t := by linarith [hb.2]
        have he := hur t ⟨hbt, ht.2⟩
        calc
          u (t, x + coordinateVector i)
              = w₂.velocity (t - b, x + coordinateVector i) := congrFun he _
          _ = w₂.velocity (t - b, x) := w₂.velocity_periodic (t - b)
            ⟨by linarith, by linarith [ht.2]⟩ x i
          _ = u (t, x) := (congrFun he _).symm
    pressure_periodic := by
      intro t ht x i
      by_cases h : t < T
      · have he := hpl t ⟨ht.1, h⟩
        calc
          p (t, x + coordinateVector i)
              = w.pressure (t, x + coordinateVector i) := congrFun he _
          _ = w.pressure (t, x) := w.pressure_periodic t ⟨ht.1, h⟩ x i
          _ = p (t, x) := (congrFun he _).symm
      · have hbt : b ≤ t := by linarith [hb.2]
        have he := hpr t ⟨hbt, ht.2⟩
        calc
          p (t, x + coordinateVector i)
              = w₂.pressure (t - b, x + coordinateVector i) := congrFun he _
          _ = w₂.pressure (t - b, x) := w₂.pressure_periodic (t - b)
            ⟨by linarith, by linarith [ht.2]⟩ x i
          _ = p (t, x) := (congrFun he _).symm
    pressure_gauge := by
      intro t ht
      by_cases h : t < T
      · have hm : pressureMeanT p t = pressureMeanT w.pressure t := by
          unfold pressureMeanT
          rw [hpl t ⟨ht.1, h⟩]
        rw [hm]
        exact w.pressure_gauge t ⟨ht.1, h⟩
      · have hbt : b ≤ t := by linarith [hb.2]
        have hm : pressureMeanT p t = pressureMeanT w₂.pressure (t - b) := by
          unfold pressureMeanT
          rw [hpr t ⟨hbt, ht.2⟩]
        rw [hm]
        exact w₂.pressure_gauge (t - b) ⟨by linarith, by linarith [ht.2]⟩ },
    fun t ht x => congrFun (hul t ht) x, fun t ht x => congrFun (hpl t ht) x⟩

/-! ## The `restartBeyond` field of `PeriodicContinuationAPI` -/

/-- The `PeriodicContinuationAPI.restartBeyond` field, verbatim, conditional
only on the named amended quantitative local-existence input consumed through
`restart`.

`δ` is produced by `restart` at the `H¹` ball `K` for the fixed `f` and `S`,
before the datum, so it is uniform over the ball.  The basepoint is
`t₀ = max 0 (S - d/2) ∈ [0, S)`, chosen so that `t₀ + d > S`; the restart from
the slice `u(t₀, ·)` for `timeShiftT t₀ f` reaches `t₀ + d = S + δ`.  The
agreement on `[0, S)` comes from `velocity_unique`/`pressure_unique` between
the glued solution and the `SolvesBelowT` witness on a horizon `c` with
`t < c < S`. -/
theorem restartBeyond (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x)) := by
  intro ν hν f hf S hS K hK
  obtain ⟨d, hd, hloc⟩ := restart H ν hν f hf S hS.le K hK
  obtain ⟨t₀, ht₀0, ht₀S, ht₀d⟩ : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < S ∧ S < t₀ + d :=
    ⟨max 0 (S - d / 2), le_max_left _ _, max_lt hS (by linarith),
      by have := le_max_right 0 (S - d / 2); linarith⟩
  refine ⟨t₀ + d - S, by linarith, ?_⟩
  intro a ha u p hsolve hbound
  obtain ⟨w, hwv, hwp⟩ := hsolve ((t₀ + S) / 2) (by linarith) (by linarith)
  have hbmem : t₀ ∈ Ico (0 : ℝ) ((t₀ + S) / 2) := ⟨ht₀0, by linarith⟩
  have hKa : periodicSobolevENorm 1 (fun x => w.velocity (t₀, x)) ≤ K := by
    rw [hwv]
    exact hbound t₀ ⟨ht₀0, ht₀S⟩
  obtain ⟨w₂, -⟩ := hloc t₀ ⟨ht₀0, ht₀S.le⟩ (fun x => w.velocity (t₀, x))
    (velocitySlice_mem_initialClassT w hbmem) hKa
  obtain ⟨v, -, -⟩ := glueClassicalSolutionT hν w hbmem w₂ (by linarith : (t₀ + S) / 2 < t₀ + d)
  have hrew : S + (t₀ + d - S) = t₀ + d := by ring
  rw [hrew]
  refine ⟨v, ?_, ?_⟩
  · intro t ht x
    obtain ⟨wc, hwcv, -⟩ := hsolve ((t + S) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    have hag := velocity_unique ν hν a ha f hf (t₀ + d) ((t + S) / 2) v wc t
      ⟨ht.1, lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    rw [hag, hwcv]
  · intro t ht x
    obtain ⟨wc, -, hwcp⟩ := hsolve ((t + S) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    have hag := pressure_unique ν hν a ha f hf (t₀ + d) ((t + S) / 2) v wc t
      ⟨ht.1, lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    rw [hag, hwcp]

/-- Non-vacuity of the gluing constructor: the nonzero forced witness of
`LocalExistence` restricts to a shorter horizon, is translated to the interior
basepoint `1/4`, and the two charts glue to a genuine classical solution on
`[0, 1)` whose velocity at the origin is nonzero. -/
example :
    ∃ (a : SpatialField) (g : SpaceTimeField)
      (v : ClassicalSolutionT 1 a g ((1 : ℝ) / 4 + (1 - 1 / 4))),
      v.velocity (0, 0) ≠ 0 := by
  obtain ⟨-, -, a, g, -, -, -, -, -, -, -, w, -, hw0, -⟩ := nonzero_forced_witness'
  have hb : (1 : ℝ) / 4 ∈ Ico (0 : ℝ) (1 / 2) := ⟨by norm_num, by norm_num⟩
  have hb1 : (1 : ℝ) / 4 ∈ Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨v, hvv, -⟩ := glueClassicalSolutionT one_pos
    (restrictClassicalSolutionT w (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 ≤ 1))
    hb (shiftedSolutionT w (1 / 4) hb1) (by norm_num)
  refine ⟨a, g, v, ?_⟩
  rw [hvv 0 ⟨le_rfl, by norm_num⟩ 0]
  exact hw0

end NSFormalization.Section3.T11
