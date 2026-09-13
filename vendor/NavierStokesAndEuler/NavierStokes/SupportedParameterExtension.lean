import NavierStokes.SpacetimeGluing
import NavierStokes.FinalSlowBase

/-!
# Smooth parameter extension with unchanged spatial support

The raw field is smooth, and its spatial support is prescribed only for
`-1 ≤ eta ≤ 1`.  Two actual Taylor--Borel gluings extend this closed-band
restriction.  Zero endpoint Taylor coefficients preserve every zero spatial
fiber, without a radial buffer or a support assumption on the raw future.
-/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace NavierStokes.SupportedParameterExtension

abbrev Space := ProblemStatement.Space
abbrev Point := ProblemStatement.SpaceTime

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Vanishing on a nondegenerate closed interval forces every genuine
derivative to vanish at its endpoints as well as in its interior. -/
theorem iteratedDeriv_zero_of_band {a b : ℝ} (hab : a < b) {f : ℝ → V}
    (hf : ContDiff ℝ ∞ f) (hz : EqOn f (fun _ => 0) (Icc a b))
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc a b) : iteratedDeriv n f t = 0 := by
  rw [iteratedDeriv_eq_iteratedFDeriv,
    ← iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc hab)
      (hf.of_le (nat_le_infty n)).contDiffAt ht,
    iteratedFDerivWithin_congr hz ht n]
  simp only [iteratedFDerivWithin_fun_zero, Pi.zero_apply,
    _root_.zero_apply]

/-- The one-sided trace used by the gluing theorem is the ordinary time
derivative of the smooth raw field. -/
theorem normalTrace_eq_iteratedDeriv {f : Point → V} (hf : ContDiff ℝ ∞ f)
    (T : ℝ) (n : ℕ) (x : Space) :
    SpacetimeGluing.normalTrace T f n x = iteratedDeriv n (fun t => f (t, x)) T := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => f (t, x)) :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  rw [SpacetimeGluing.normalTrace_eq_time_jet hf.contDiffOn,
    iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Iic T)
      (hs.of_le (nat_le_infty n)).contDiffAt (mem_Iic.mpr le_rfl)]
  rfl

/-- These are actual endpoint Taylor coefficients, derived from the support
on the closed parameter band. -/
theorem normalTrace_zero_of_band {f : Point → V} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) {x : Space}
    (hz : ∀ t ∈ Icc a b, f (t, x) = 0) (n : ℕ) :
    SpacetimeGluing.normalTrace b f n x = 0 := by
  rw [normalTrace_eq_iteratedDeriv hf]
  exact iteratedDeriv_zero_of_band hab (hf.comp (contDiff_id.prodMk contDiff_const))
    hz n ⟨hab.le, le_rfl⟩

variable [CompleteSpace V]

/-- First gluing, at the upper endpoint of the prescribed band. -/
noncomputable def upper (f : Point → V) (hf : ContDiff ℝ ∞ f) : Point → V :=
  SpacetimeGluing.smoothExtension 1 f hf.contDiffOn

theorem upper_contDiff {f : Point → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (upper f hf) :=
  SpacetimeGluing.smoothExtension_contDiff hf.contDiffOn

omit [CompleteSpace V] in
theorem upper_eq {f : Point → V} (hf : ContDiff ℝ ∞ f) {t : ℝ}
    (ht : t ≤ 1) (x : Space) : upper f hf (t, x) = f (t, x) :=
  SpacetimeGluing.smoothExtension_eqOn_past hf.contDiffOn ⟨ht, mem_univ _⟩

omit [CompleteSpace V] in
/-- Zero spatial fibers persist through the upper gluing.  No restriction on
the raw field is used at parameters less than `-1` or greater than `1`. -/
theorem upper_zero_of_band {f : Point → V} (hf : ContDiff ℝ ∞ f) {x : Space}
    (hz : ∀ t ∈ Icc (-1 : ℝ) 1, f (t, x) = 0) {t : ℝ} (ht : -1 ≤ t) :
    upper f hf (t, x) = 0 := by
  by_cases h : t ≤ 1
  · rw [upper_eq hf h]
    exact hz t ⟨ht, h⟩
  · unfold upper SpacetimeGluing.smoothExtension SpacetimeGluing.glue
    simp only [ite_eq_right h, SpatialBorelExtension.rightExtension]
    apply SpatialBorelExtension.extension_zero_of_coefficients_zero
    intro n
    exact normalTrace_zero_of_band hf (by norm_num : (-1 : ℝ) < 1) hz n

noncomputable def reflect (f : Point → V) (z : Point) : V := f (-z.1, z.2)

omit [CompleteSpace V] in
theorem reflect_contDiff {f : Point → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (reflect f) :=
  hf.comp (contDiff_fst.neg.prodMk contDiff_snd)

/-- The second gluing acts on the reflected upper extension, then is
reflected back.  Both glued fields are actual jointly smooth functions. -/
noncomputable def extension (f : Point → V) (hf : ContDiff ℝ ∞ f) : Point → V :=
  reflect (upper (reflect (upper f hf)) (reflect_contDiff (upper_contDiff hf)))

theorem extension_contDiff {f : Point → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (extension f hf) :=
  reflect_contDiff (upper_contDiff (reflect_contDiff (upper_contDiff hf)))

theorem extension_eq {f : Point → V} (hf : ContDiff ℝ ∞ f) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (x : Space) : extension f hf (t, x) = f (t, x) := by
  change upper (reflect (upper f hf)) (reflect_contDiff (upper_contDiff hf))
    (-t, x) = f (t, x)
  rw [upper_eq (reflect_contDiff (upper_contDiff hf)) (show -t ≤ 1 by linarith [ht.1])]
  simp only [reflect, neg_neg]
  exact upper_eq hf ht.2 x

theorem extension_eqOn {f : Point → V} (hf : ContDiff ℝ ∞ f) :
    EqOn (extension f hf) f (Icc (-1 : ℝ) 1 ×ˢ (univ : Set Space)) :=
  fun z hz => extension_eq hf hz.1 z.2

/-- Every spatial zero fiber of the original closed band stays zero for
all parameters. -/
theorem extension_zero_of_band {f : Point → V} (hf : ContDiff ℝ ∞ f) {x : Space}
    (hz : ∀ t ∈ Icc (-1 : ℝ) 1, f (t, x) = 0) (t : ℝ) :
    extension f hf (t, x) = 0 := by
  by_cases ht : -1 ≤ t
  · change upper (reflect (upper f hf)) (reflect_contDiff (upper_contDiff hf)) (-t, x) = 0
    rw [upper_eq (reflect_contDiff (upper_contDiff hf)) (show -t ≤ 1 by linarith)]
    simp only [reflect, neg_neg]
    exact upper_zero_of_band hf hz ht
  · apply upper_zero_of_band (reflect_contDiff (upper_contDiff hf))
    · intro s hs
      exact upper_zero_of_band hf hz (by linarith [hs.2])
    · dsimp
      linarith

/-- The prescribed spatial support set is unchanged.  It need not have an
interior buffer and is not enlarged by either gluing. -/
theorem extension_supported {S : Set Space} {f : Point → V}
    (hf : ContDiff ℝ ∞ f)
    (hs : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x ∉ S, f (t, x) = 0) :
    ∀ t : ℝ, ∀ x ∉ S, extension f hf (t, x) = 0 := by
  intro t x hx
  exact extension_zero_of_band hf (fun s hs' => hs s hs' x hx) t

/-- All full mixed tensors agree on the closed band, including both
boundary parameter hyperplanes. -/
theorem extension_iteratedFDeriv {f : Point → V} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) {z : Point} (hz : z.1 ∈ Icc (-1 : ℝ) 1) :
    iteratedFDeriv ℝ n (extension f hf) z = iteratedFDeriv ℝ n f z := by
  have hs := (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)).prod
    (uniqueDiffOn_univ (𝕜 := ℝ) (E := Space))
  have hmem : z ∈ Icc (-1 : ℝ) 1 ×ˢ (univ : Set Space) := ⟨hz, mem_univ _⟩
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hs
    ((extension_contDiff hf).of_le (nat_le_infty n)).contDiffAt hmem,
    iteratedFDerivWithin_congr (extension_eqOn hf) hmem n,
    iteratedFDerivWithin_eq_iteratedFDeriv hs (hf.of_le (nat_le_infty n)).contDiffAt hmem]

/-- The same construction has a fixed compact parameter support. -/
theorem extension_zero_parameter {f : Point → V} (hf : ContDiff ℝ ∞ f)
    {t : ℝ} (ht : 2 ≤ |t|) (x : Space) : extension f hf (t, x) = 0 := by
  rcases le_abs.mp ht with h | h
  · change upper (reflect (upper f hf)) (reflect_contDiff (upper_contDiff hf)) (-t, x) = 0
    rw [upper_eq (reflect_contDiff (upper_contDiff hf)) (show -t ≤ 1 by linarith)]
    simp only [reflect, neg_neg, upper]
    exact SpacetimeGluing.smoothExtension_zero_from hf.contDiffOn (by linarith) x
  · unfold extension reflect upper
    exact SpacetimeGluing.smoothExtension_zero_from _ (by linarith) x

/-- A closed spatial support set also contains the topological support. -/
theorem extension_tsupport {S : Set Space} (hS : IsClosed S) {f : Point → V}
    (hf : ContDiff ℝ ∞ f)
    (hs : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x ∉ S, f (t, x) = 0) :
    tsupport (extension f hf) ⊆ Icc (-2 : ℝ) 2 ×ˢ S := by
  apply closure_minimal _ (isClosed_Icc.prod hS)
  intro z hz
  constructor
  · by_contra h
    have ha : 2 ≤ |z.1| := by
      by_contra h'
      exact h (abs_le.mp (le_of_lt (lt_of_not_ge h')))
    exact hz (extension_zero_parameter hf ha z.2)
  · by_contra h
    exact hz (extension_supported hf hs z.1 z.2 h)

/-! ## Positive scale parameter and the normalized radial model -/

/-- Model coordinates are `(q, (X, eta))`; the positive scale is unbounded
and never replaced by a compact interval. -/
abbrev Model := ℝ × (ℝ × ℝ)

/-- `q = exp(logq)` removes the only open-domain restriction.  One unused
spatial coordinate allows the existing joint gluing theorem to apply. -/
noncomputable def modelLift (f : Model → V) (z : Point) : V :=
  f (Real.exp (z.2 0), (z.2 1, z.1))

noncomputable def modelEmbedding (y : Model) : Point :=
  (y.2.2, Real.log y.1 • ProblemStatement.coordinateVector 0 +
    y.2.1 • ProblemStatement.coordinateVector 1)

theorem modelEmbedding_log (y : Model) : (modelEmbedding y).2 0 = Real.log y.1 := by
  simp [modelEmbedding, ProblemStatement.coordinateVector]

theorem modelEmbedding_radial (y : Model) : (modelEmbedding y).2 1 = y.2.1 := by
  simp [modelEmbedding, ProblemStatement.coordinateVector]

omit [CompleteSpace V] in
theorem modelLift_contDiff {f : Model → V}
    (hf : ∀ y, 0 < y.1 → ContDiffAt ℝ ∞ f y) : ContDiff ℝ ∞ (modelLift f) := by
  have h0 : ContDiff ℝ ∞ (fun z : Point => z.2 0) :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  have h1 : ContDiff ℝ ∞ (fun z : Point => z.2 1) :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  rw [contDiff_iff_contDiffAt]
  intro z
  exact (hf _ (Real.exp_pos _)).comp z
    (h0.exp.prodMk (h1.prodMk contDiff_fst)).contDiffAt

theorem modelEmbedding_contDiffAt {y : Model} (hy : 0 < y.1) :
    ContDiffAt ℝ ∞ modelEmbedding y := by
  exact contDiffAt_snd.snd.prodMk
    (((contDiffAt_fst.log hy.ne').smul contDiffAt_const).add
      (contDiffAt_snd.fst.smul contDiffAt_const))

/-- The literal positive-scale adapter.  Only the auxiliary parameter is
extended; `q` and the radial coordinate are unchanged on the closed band. -/
noncomputable def positiveExtension (f : Model → V)
    (hf : ∀ y, 0 < y.1 → ContDiffAt ℝ ∞ f y) (y : Model) : V :=
  extension (modelLift f) (modelLift_contDiff hf) (modelEmbedding y)

theorem positiveExtension_contDiffAt {f : Model → V}
    (hf : ∀ y, 0 < y.1 → ContDiffAt ℝ ∞ f y) {y : Model} (hy : 0 < y.1) :
    ContDiffAt ℝ ∞ (positiveExtension f hf) y :=
  (extension_contDiff (modelLift_contDiff hf)).contDiffAt.comp y
    (modelEmbedding_contDiffAt hy)

theorem positiveExtension_eq {f : Model → V}
    (hf : ∀ y, 0 < y.1 → ContDiffAt ℝ ∞ f y) {y : Model}
    (hy : 0 < y.1) (heta : y.2.2 ∈ Icc (-1 : ℝ) 1) :
    positiveExtension f hf y = f y := by
  unfold positiveExtension
  change extension (modelLift f) (modelLift_contDiff hf)
    (y.2.2, (modelEmbedding y).2) = f y
  rw [extension_eq (modelLift_contDiff hf) heta]
  simp only [modelLift, modelEmbedding_log, modelEmbedding_radial, Real.exp_log hy]

/-- The same radial support works for every positive scale and every
auxiliary parameter, including beyond both original endpoints. -/
theorem positiveExtension_supported {S : Set ℝ} {f : Model → V}
    (hf : ∀ y, 0 < y.1 → ContDiffAt ℝ ∞ f y)
    (hs : ∀ q, 0 < q → ∀ X ∉ S, ∀ eta ∈ Icc (-1 : ℝ) 1, f (q, X, eta) = 0)
    {y : Model} (hy : y.2.1 ∉ S) : positiveExtension f hf y = 0 := by
  apply extension_zero_of_band (modelLift_contDiff hf)
  intro t ht
  change f (Real.exp ((modelEmbedding y).2 0), (modelEmbedding y).2 1, t) = 0
  rw [modelEmbedding_radial]
  exact hs _ (Real.exp_pos _) y.2.1 hy t ht

theorem positiveExtension_iteratedFDeriv {f : Model → V}
    (hf : ∀ y, 0 < y.1 → ContDiffAt ℝ ∞ f y) (n : ℕ) {y : Model}
    (hy : 0 < y.1) (heta : y.2.2 ∈ Icc (-1 : ℝ) 1) :
    iteratedFDeriv ℝ n (positiveExtension f hf) y = iteratedFDeriv ℝ n f y := by
  let s : Set Model := Ioi (0 : ℝ) ×ˢ (univ ×ˢ Icc (-1 : ℝ) 1)
  have hs : UniqueDiffOn ℝ s :=
    (uniqueDiffOn_Ioi (0 : ℝ)).prod
      (uniqueDiffOn_univ.prod (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)))
  have hmem : y ∈ s := ⟨hy, mem_univ _, heta⟩
  have heq : EqOn (positiveExtension f hf) f s :=
    fun z hz => positiveExtension_eq hf hz.1 hz.2.2
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hs
    ((positiveExtension_contDiffAt hf hy).of_le (nat_le_infty n)) hmem,
    iteratedFDerivWithin_congr heq hmem n,
    iteratedFDerivWithin_eq_iteratedFDeriv hs ((hf y hy).of_le (nat_le_infty n)) hmem]

theorem positiveExtension_zero_parameter {f : Model → V}
    (hf : ∀ y, 0 < y.1 → ContDiffAt ℝ ∞ f y) {y : Model} (heta : 2 ≤ |y.2.2|) :
    positiveExtension f hf y = 0 :=
  extension_zero_parameter (modelLift_contDiff hf) heta _

/-! ## The actual normalized stress, with the original selected scales -/

section Stress

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld) (upperBound : ℝ) (B : ℕ)

/-- No coefficients, scales, radial endpoints, or modulation choices are
reselected.  This extends the actual already constructed stress. -/
noncomputable def normalizedStress : Model → ℝ × ℝ :=
  positiveExtension (FinalSlowBase.normalizedStress H v upperBound B)
    (fun _ hy => FinalSlowBase.normalizedStress_smoothAt H v upperBound B hy)

theorem normalizedStress_contDiffAt {y : Model} (hy : 0 < y.1) :
    ContDiffAt ℝ ∞ (normalizedStress H v upperBound B) y :=
  positiveExtension_contDiffAt _ hy

theorem normalizedStress_eq {y : Model} (hy : 0 < y.1)
    (heta : y.2.2 ∈ Icc (-1 : ℝ) 1) :
    normalizedStress H v upperBound B y = FinalSlowBase.normalizedStress H v upperBound B y :=
  positiveExtension_eq _ hy heta

theorem normalizedStress_supported {y : Model}
    (hX : y.2.1 ∉ Icc (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)) :
    normalizedStress H v upperBound B y = 0 := by
  apply positiveExtension_supported _ _ hX
  intro q _ X hX eta heta
  exact FinalSlowBase.normalizedStress_zero_outside H v upperBound B q hX heta

theorem normalizedStress_zero_left {y : Model}
    (hX : y.2.1 ≤ NominalConeAssembly.activeLeft W) :
    normalizedStress H v upperBound B y = 0 := by
  apply positiveExtension_supported (S := Ioi (NominalConeAssembly.activeLeft W)) _ _
    (not_lt.mpr hX)
  intro q _ X hX _ _
  exact FinalSlowBase.normalizedStress_zero_left H v upperBound B q (le_of_not_gt hX)

theorem normalizedStress_iteratedFDeriv (n : ℕ) {y : Model} (hy : 0 < y.1)
    (heta : y.2.2 ∈ Icc (-1 : ℝ) 1) :
    iteratedFDeriv ℝ n (normalizedStress H v upperBound B) y =
      iteratedFDeriv ℝ n (FinalSlowBase.normalizedStress H v upperBound B) y :=
  positiveExtension_iteratedFDeriv _ n hy heta

theorem normalizedStress_contDiffOn :
    ContDiffOn ℝ ∞ (normalizedStress H v upperBound B) (Ioi (0 : ℝ) ×ˢ univ) :=
  fun _ hy => (normalizedStress_contDiffAt H v upperBound B hy.1).contDiffWithinAt

theorem normalizedStress_zero_parameter {y : Model} (heta : 2 ≤ |y.2.2|) :
    normalizedStress H v upperBound B y = 0 :=
  positiveExtension_zero_parameter _ heta

end Stress

end NavierStokes.SupportedParameterExtension
