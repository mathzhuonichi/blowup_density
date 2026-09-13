import NSFormalization.Source.AngularForceNorms
import NSFormalization.Paper3.WeightedFourierLp

/-! The actual vector Fourier norm is a Hilbert-space norm. This gives its
triangle inequality and permits addition of convergent force perturbations. -/
noncomputable section
namespace NSFormalization.Source
open NavierStokes.ProblemStatement MeasureTheory Filter Topology
open scoped ContDiff ENNReal

theorem compactFourierLp_add (s : ℝ) {f g : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Paper3.compactFourierLp s (f + g) (hf.add hg) (hfc.add hgc) =
      Paper3.compactFourierLp s f hf hfc + Paper3.compactFourierLp s g hg hgc := by
  have hφ : NavierStokesR3.CompactSchwartz.ofCompactSupport (f + g) (hf.add hg) (hfc.add hgc) =
      NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hfc +
        NavierStokesR3.CompactSchwartz.ofCompactSupport g hg hgc := by
    ext x
    rfl
  unfold Paper3.compactFourierLp
  rw [hφ, map_add]

def compactVectorFourierLp (s : ℝ) (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    PiLp 2 (fun _ : Fin 3 => Lp ℂ 2 (volume : Measure Space)) :=
  WithLp.toLp 2 (fun i => Paper3.compactFourierLp s (fun x => coordinateForce F i (t, x))
    ((coordinateForce_smooth hF i).comp (contDiff_const.prodMk contDiff_id))
    (Paper3.compact_spatial_slice (coordinateForce_compact hc i) t))

theorem norm_compactVectorFourierLp (s : ℝ) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    ‖compactVectorFourierLp s F hF hc t‖ = vectorFourierSobolevNorm s F t := by
  rw [PiLp.norm_eq_of_L2]
  simp only [compactVectorFourierLp, PiLp.toLp_apply, Paper3.norm_compactFourierLp,
    fourierSobolevNorm, Real.sq_sqrt (fourierSobolevSq_nonneg _ _)]
  rfl

theorem coordinateForce_add (F G : VelocityField) (i : Fin 3) :
    coordinateForce (F + G) i = coordinateForce F i + coordinateForce G i := by
  funext z
  simp [coordinateForce, PiLp.add_apply]

theorem compactVectorFourierLp_add (s : ℝ) {F G : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFc : HasCompactSupport F) (hGc : HasCompactSupport G) (t : ℝ) :
    compactVectorFourierLp s (F + G) (hF.add hG) (hFc.add hGc) t =
      compactVectorFourierLp s F hF hFc t + compactVectorFourierLp s G hG hGc t := by
  apply PiLp.ext
  intro i
  change Paper3.compactFourierLp s (fun x => coordinateForce (F + G) i (t, x)) _ _ = _
  simp_rw [coordinateForce_add, Pi.add_apply]
  exact compactFourierLp_add s _ _ _ _

theorem vectorFourierSobolevNorm_add_le (s : ℝ) {F G : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFc : HasCompactSupport F) (hGc : HasCompactSupport G) (t : ℝ) :
    vectorFourierSobolevNorm s (F + G) t ≤
      vectorFourierSobolevNorm s F t + vectorFourierSobolevNorm s G t := by
  rw [← norm_compactVectorFourierLp s (F := F + G) (hF.add hG) (hFc.add hGc) t,
    compactVectorFourierLp_add, ← norm_compactVectorFourierLp s hF hFc t,
    ← norm_compactVectorFourierLp s hG hGc t]
  exact norm_add_le _ _

theorem stronglyMeasurable_vectorFourierSobolevNorm (s : ℝ) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) : StronglyMeasurable (vectorFourierSobolevNorm s F) := by
  have h (i : Fin 3) := Paper3.stronglyMeasurable_fourierSobolev_time s
    (coordinateForce_smooth hF i).continuous
  have he : vectorFourierSobolevNorm s F = fun t =>
      Real.sqrt (∑ i : Fin 3, (fourierSobolevNorm s (fun x => coordinateForce F i (t, x))) ^ 2) := by
    funext t
    simp only [fourierSobolevNorm, Real.sq_sqrt (fourierSobolevSq_nonneg _ _)]
    rfl
  rw [he]
  exact Real.continuous_sqrt.comp_stronglyMeasurable
    (Finset.stronglyMeasurable_sum Finset.univ (fun i _ => (h i).pow 2))

theorem eLpNorm_vector_add_le (s : ℝ) (q : ℝ≥0∞) (hq : 1 ≤ q) {F G : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFc : HasCompactSupport F) (hGc : HasCompactSupport G) :
    eLpNorm (vectorFourierSobolevNorm s (F + G)) q volume ≤
      eLpNorm (vectorFourierSobolevNorm s F) q volume +
        eLpNorm (vectorFourierSobolevNorm s G) q volume := by
  apply (eLpNorm_mono_real (p := q) (μ := volume)
    (f := vectorFourierSobolevNorm s (F + G))
    (g := fun t => vectorFourierSobolevNorm s F t + vectorFourierSobolevNorm s G t)
    (fun t => ?_)).trans
  · exact eLpNorm_add_le (stronglyMeasurable_vectorFourierSobolevNorm s hF).aestronglyMeasurable
      (stronglyMeasurable_vectorFourierSobolevNorm s hG).aestronglyMeasurable hq
  · rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ vectorFourierSobolevNorm s (F + G) t
      from Real.sqrt_nonneg _)]
    exact vectorFourierSobolevNorm_add_le s hF hG hFc hGc t

theorem vector_family_add_tendsto_zero (s : ℝ) (q : ℝ≥0∞) (hq : 1 ≤ q)
    {F G : ℝ → VelocityField}
    (hF : ∀ ε, ContDiff ℝ ∞ (F ε)) (hG : ∀ ε, ContDiff ℝ ∞ (G ε))
    (hFc : ∀ ε, 0 < ε → HasCompactSupport (F ε))
    (hGc : ∀ ε, 0 < ε → HasCompactSupport (G ε))
    (hFlim : Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s (F ε)) q volume)
      (𝓝[>] 0) (𝓝 0))
    (hGlim : Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s (G ε)) q volume)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s (F ε + G ε)) q volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hlim := hFlim.add hGlim
  simp only [add_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact eLpNorm_vector_add_le s q hq (hF ε) (hG ε) (hFc ε hε) (hGc ε hε)

end NSFormalization.Source
