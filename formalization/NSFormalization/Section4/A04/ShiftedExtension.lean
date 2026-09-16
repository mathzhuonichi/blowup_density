import NSFormalization.Section4.A04.RestartFixedForce

/-! Interior restart gluing. Basepoint normalization makes pressure gauges agree
on the overlap; no gauge function is extended across a terminal time. -/
noncomputable section
namespace NSFormalization.Section4.A04
open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
open scoped ContDiff ENNReal

/-- Paste inside an overlap, rather than at either terminal time. -/
def overlapPaste {E : Type*} (c : ℝ) (u v : ℝ → E) (t : ℝ) : E :=
  if t < c then u t else v t

/-- The pasted path agrees with the first chart on its whole interval. -/
theorem overlapPaste_left {E : Type*} {b c T : ℝ} {u v : ℝ → E}
    (hbc : b < c)
    (he : ∀ t ∈ Ico b T, u t = v t) {t : ℝ} (ht : t ∈ Ico 0 T) :
    overlapPaste c u v t = u t := by
  unfold overlapPaste
  split_ifs with h
  · rfl
  · exact (he t ⟨by linarith, ht.2⟩).symm

/-- The pasted path agrees with the second chart on its whole interval. -/
theorem overlapPaste_right {E : Type*} {b c T H : ℝ} {u v : ℝ → E}
    (hcT : c < T) (he : ∀ t ∈ Ico b T, u t = v t)
    {t : ℝ} (ht : t ∈ Ico b H) : overlapPaste c u v t = v t := by
  unfold overlapPaste
  split_ifs with h
  · exact he t ⟨ht.1, h.trans hcT⟩
  · rfl

/-- Smoothness is local on two overlapping time charts, including time zero. -/
theorem contDiffOn_overlap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b T H : ℝ} (hbT : b < T) {g : SpaceTime → E}
    (hl : ContDiffOn ℝ ∞ g (Ico 0 T ×ˢ (univ : Set Space)))
    (hr : ContDiffOn ℝ ∞ g (Ico b H ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ g (Ico 0 H ×ˢ (univ : Set Space)) := by
  intro z hz
  by_cases ht : z.1 < T
  · apply (hl z ⟨⟨hz.1.1, ht⟩, mem_univ _⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (continuous_fst.tendsto z (Iio_mem_nhds ht))] with y hy hyT
    exact ⟨⟨hy.1.1, hyT⟩, mem_univ _⟩
  · have hbt : b < z.1 := hbT.trans_le (le_of_not_gt ht)
    apply (hr z ⟨⟨hbt.le, hz.1.2⟩, mem_univ _⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (continuous_fst.tendsto z (Ioi_mem_nhds hbt))] with y hy hyb
    exact ⟨⟨hyb.le, hy.1.2⟩, mem_univ _⟩

/-- Continuous Sobolev paths use the same overlapping charts. -/
theorem continuousOn_overlap {E : Type*} [TopologicalSpace E]
    {b T H : ℝ} (hbT : b < T) {g : ℝ → E}
    (hl : ContinuousOn g (Ico 0 T)) (hr : ContinuousOn g (Ico b H)) :
    ContinuousOn g (Ico 0 H) := by
  intro t ht
  by_cases h : t < T
  · apply (hl t ⟨ht.1, h⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h)] with s hs hsT
    exact ⟨hs.1, hsT⟩
  · have hbt : b < t := hbT.trans_le (le_of_not_gt h)
    apply (hr t ⟨hbt.le, ht.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hbt)] with s hs hsb
    exact ⟨hsb.le, hs.2⟩

/-- The residual depends on a time neighborhood of spatial slices. -/
theorem residual_eq_of_local_slices {ν t : ℝ} {u v : SpaceTimeField}
    {p q : SpaceTimeScalar}
    (he : ∀ᶠ s in 𝓝 t, ∀ x, u (s, x) = v (s, x))
    (hp : (fun x => p (t, x)) = (fun x => q (t, x))) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν v q t x := by
  have hs : (fun x => u (t, x)) = (fun x => v (t, x)) :=
    funext he.self_of_nhds
  have hd : spatialDerivative u t = spatialDerivative v t := by
    funext y
    simp only [spatialDerivative, hs]
  have hv : u (t, x) = v (t, x) := congrFun hs x
  have htime : temporalDerivative u t x = temporalDerivative v t x := by
    have hev : (fun s => u (s, x)) =ᶠ[𝓝 t] (fun s => v (s, x)) :=
      he.mono (fun s h => h x)
    have h := hev.fderiv_eq (𝕜 := ℝ)
    exact congrArg (fun D : ℝ →L[ℝ] Space => D 1) h
  simp only [NavierStokesR3.ProblemStatement.navierStokesResidual,
    htime, advection, hd, hv, spatialLaplacian, pressureGradient, hp]

/-- Translate the restarted equation back to the original clock. -/
theorem restarted_residual {ν b L : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a (timeShift b f) L) {t : ℝ}
    (ht : t - b ∈ Ioo (0 : ℝ) L) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν
      (fun z => w.velocity (z.1 - b, z.2))
      (fun z => w.pressure (z.1 - b, z.2)) t x = f (t, x) := by
  have hd := C01.velocity_hasDerivAt_time w ht x
  have hs := hd.scomp t ((hasDerivAt_id t).sub_const b)
  have he : temporalDerivative (fun z => w.velocity (z.1 - b, z.2)) t x =
      temporalDerivative w.velocity (t - b) x := by
    simpa [temporalDerivative, Function.comp_def] using
      congrArg (fun D : ℝ →L[ℝ] Space => D 1) hs.hasFDerivAt.fderiv
  change temporalDerivative _ t x + _ - _ + _ = _
  rw [he]
  simpa only [NavierStokesR3.ProblemStatement.navierStokesResidual,
    advection, spatialLaplacian, spatialDerivative, pressureGradient,
    timeShift, sub_add_cancel] using w.momentum (t - b) ht x

/-- Two actual solutions glue on their union. The pressure is normalized in
each chart separately, and the seam lies strictly inside their overlap. -/
theorem exists_shifted_glue {ν T b L : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (w : ClassicalSolutionR ν a f T) (hb : b ∈ Ico (0 : ℝ) T)
    (w₂ : ClassicalSolutionR ν (fun x => w.velocity (b, x)) (timeShift b f) L)
    (hTL : T < b + L) : Nonempty (ClassicalSolutionR ν a f (b + L)) := by
  let c := (b + T) / 2
  have hbc : b < c := by dsimp [c]; linarith [hb.2]
  have hcT : c < T := by dsimp [c]; linarith [hb.2]
  let n := w.normalizePressure (0 : Space)
  let n₂ := w₂.normalizePressure (0 : Space)
  have hv : ∀ t ∈ Ico b T, (fun x => n.velocity (t, x)) =
      (fun x => n₂.velocity (t - b, x)) := by
    intro t ht
    funext x
    have he := velocity_unique_core hν (shiftedSolution w b hb) w₂ (t - b)
      ⟨by linarith [ht.1], lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    simpa only [n, n₂, ClassicalSolutionR.normalizePressure, shiftedSolution,
      timeShift, sub_add_cancel] using he
  have hp : ∀ t ∈ Ico b T, (fun x => n.pressure (t, x)) =
      (fun x => n₂.pressure (t - b, x)) := by
    intro t ht
    funext x
    have he := normalizePressure_gauge_invariant
      (pressure_gauge_core hν (shiftedSolution w b hb) w₂) (0 : Space) (t - b)
      ⟨by linarith [ht.1], lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    simpa only [n, n₂, ClassicalSolutionR.normalizePressure, shiftedSolution,
      sub_add_cancel] using he.symm
  let u : SpaceTimeField := fun z =>
    overlapPaste c (fun t x => n.velocity (t, x)) (fun t x => n₂.velocity (t - b, x)) z.1 z.2
  let p : SpaceTimeScalar := fun z =>
    overlapPaste c (fun t x => n.pressure (t, x)) (fun t x => n₂.pressure (t - b, x)) z.1 z.2
  have hul : ∀ t ∈ Ico 0 T, (fun x => u (t, x)) = (fun x => n.velocity (t, x)) :=
    fun t ht => overlapPaste_left hbc hv ht
  have hur : ∀ t ∈ Ico b (b + L), (fun x => u (t, x)) =
      (fun x => n₂.velocity (t - b, x)) := fun t ht => overlapPaste_right hcT hv ht
  have hpl : ∀ t ∈ Ico 0 T, (fun x => p (t, x)) = (fun x => n.pressure (t, x)) :=
    fun t ht => overlapPaste_left hbc hp ht
  have hpr : ∀ t ∈ Ico b (b + L), (fun x => p (t, x)) =
      (fun x => n₂.pressure (t - b, x)) := fun t ht => overlapPaste_right hcT hp ht
  have hshift : MapsTo (fun z : SpaceTime => (z.1 - b, z.2))
      (Ico b (b + L) ×ˢ (univ : Set Space)) (Ico 0 L ×ˢ (univ : Set Space)) := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, mem_univ _⟩
  refine ⟨{
    velocity := u
    pressure := p
    horizon_pos := by linarith [w.horizon_pos]
    velocity_smooth := contDiffOn_overlap hb.2
      (n.velocity_smooth.congr (fun z hz => congrFun (hul z.1 hz.1) z.2))
      ((n₂.velocity_smooth.comp
        ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn hshift).congr
          (fun z hz => congrFun (hur z.1 hz.1) z.2))
    pressure_smooth := contDiffOn_overlap hb.2
      (n.pressure_smooth.congr (fun z hz => congrFun (hpl z.1 hz.1) z.2))
      ((n₂.pressure_smooth.comp
        ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn hshift).congr
          (fun z hz => congrFun (hpr z.1 hz.1) z.2))
    initial := fun x => (congrFun (hul 0 ⟨le_rfl, w.horizon_pos⟩) x).trans (n.initial x)
    divergence := ?_
    momentum := ?_
    sobolev := ?_
    pressure_gradient := ?_
  }⟩
  · intro t ht x
    by_cases h : t < T
    · have he := hul t ⟨ht.1, h⟩
      simpa only [spatialDivergence, spatialDerivative, he] using n.divergence t ⟨ht.1, h⟩ x
    · have hbt : b ≤ t := by linarith [hb.2]
      have he := hur t ⟨hbt, ht.2⟩
      simpa only [spatialDivergence, spatialDerivative, he] using
        n₂.divergence (t - b) ⟨by linarith, by linarith [ht.2]⟩ x
  · intro t ht x
    by_cases h : t < T
    · have he : ∀ᶠ s in 𝓝 t, ∀ x, u (s, x) = n.velocity (s, x) := by
        filter_upwards [Ioo_mem_nhds ht.1 h] with s hs x
        exact congrFun (hul s ⟨hs.1.le, hs.2⟩) x
      rw [residual_eq_of_local_slices he (hpl t ⟨ht.1.le, h⟩) x]
      exact n.momentum t ⟨ht.1, h⟩ x
    · have hbt : b < t := by linarith [hb.2]
      have he : ∀ᶠ s in 𝓝 t, ∀ x, u (s, x) = n₂.velocity (s - b, x) := by
        filter_upwards [Ioo_mem_nhds hbt ht.2] with s hs x
        exact congrFun (hur s ⟨hs.1.le, hs.2⟩) x
      rw [residual_eq_of_local_slices
        (v := fun z => n₂.velocity (z.1 - b, z.2))
        (q := fun z => n₂.pressure (z.1 - b, z.2)) he (hpr t ⟨hbt.le, ht.2⟩) x]
      exact restarted_residual n₂ ⟨by linarith, by linarith [ht.2]⟩ x
  · intro m
    obtain ⟨G, hGc, hG⟩ := n.sobolev m
    obtain ⟨F, hFc, hF⟩ := n₂.sobolev m
    have hGF : ∀ t ∈ Ico b T, G t = F (t - b) := by
      intro t ht
      apply D01.isSobolevDatum_unique (hG t ⟨hb.1.trans ht.1, ht.2⟩)
      rw [hv t ht]
      exact hF (t - b) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    let P := overlapPaste c G (fun t => F (t - b))
    have hPl : ∀ t ∈ Ico 0 T, P t = G t := fun t ht => overlapPaste_left hbc hGF ht
    have hPr : ∀ t ∈ Ico b (b + L), P t = F (t - b) :=
      fun t ht => overlapPaste_right hcT hGF ht
    refine ⟨P, continuousOn_overlap hb.2 (hGc.congr hPl)
      ((hFc.comp (continuous_id.sub continuous_const).continuousOn
        (fun t ht => ⟨by dsimp; linarith [ht.1], by dsimp; linarith [ht.2]⟩)).congr hPr), ?_⟩
    intro t ht
    by_cases h : t < T
    · rw [hPl t ⟨ht.1, h⟩, hul t ⟨ht.1, h⟩]
      exact hG t ⟨ht.1, h⟩
    · have hbt : b ≤ t := by linarith [hb.2]
      rw [hPr t ⟨hbt, ht.2⟩, hur t ⟨hbt, ht.2⟩]
      exact hF (t - b) ⟨by linarith, by linarith [ht.2]⟩
  · intro t ht
    by_cases h : t < T
    · have he := hpl t ⟨ht.1, h⟩
      simpa only [pressureGradient, he] using n.pressure_gradient t ⟨ht.1, h⟩
    · have hbt : b ≤ t := by linarith [hb.2]
      have he := hpr t ⟨hbt, ht.2⟩
      simpa only [pressureGradient, he] using
        n₂.pressure_gradient (t - b) ⟨by linarith, by linarith [ht.2]⟩

/-- An interior restart extends the lifespan of the original problem. -/
theorem shiftedLocalExtension : ShiftedLocalExtension := by
  intro ν hν a f T w b hb L w₂
  by_cases h : T < b + L
  · exact horizon_le_lifespan (exists_shifted_glue hν w hb w₂ h).some
  · exact (ENNReal.ofReal_le_ofReal (le_of_not_gt h)).trans (horizon_le_lifespan w)

/-- Fixed-force H⁷ restart, with the extension input discharged. -/
theorem restartBeyond_of_memForceR'
    (ν : ℝ) (hν : 0 < ν) (f : SpaceTimeField) (hf : MemForceR f)
    (S : ℝ) (hS : 0 < S) (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
      a ∈ initialClassR → SolvesBelow ν a f S u p →
      (∀ t ∈ Ico (0 : ℝ) S, D01.sobolevENorm 7 (fun x => u (t, x)) ≤ K) →
      ENNReal.ofReal (S + δ) ≤ maximalLifespanR ν a f :=
  restartBeyond_fixed shiftedLocalExtension ν hν f hf S hS
    (restartFixedForce_of_memForceR ν hν f hf S hS.le) K hK

/-- The integral continuation criterion for a force in the manuscript class. -/
theorem extendsBeyond_of_memForceR'
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (S : ℝ) (hS : 0 < S) (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : SolvesBelow ν a f S u p) (hfin : squaredHTwoIntegral S u ≠ ⊤) :
    ENNReal.ofReal S < maximalLifespanR ν a f :=
  extendsBeyond_of_memForceR shiftedLocalExtension ν a f hν ha hf S hS u p hu hfin

/-- Locally finite H² integral implies infinite maximal lifespan. -/
theorem lifespanInfiniteOfLocallyFinite_of_memForceR'
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : IsMaximalSolution ν a f u p)
    (hfin : ∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanR ν a f →
      squaredHTwoIntegral S u ≠ ⊤) : maximalLifespanR ν a f = ⊤ :=
  lifespanInfiniteOfLocallyFinite_of_memForceR shiftedLocalExtension ν a f hν ha hf u p hu hfin

end NSFormalization.Section4.A04
