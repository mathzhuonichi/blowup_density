import NSFormalization.Section3.T23.Boundary

/-! Pressure normalization for the canonical bounded-domain insertion. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeScalar)
open scoped ContDiff

/-- A nonempty bounded open domain has finite, strictly positive real volume. -/
theorem domain_volume_pos {Ω : Set Space} (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    0 < (volume Ω).toReal :=
  ENNReal.toReal_pos (ne_of_gt (ho.measure_pos volume hne)) hb.measure_lt_top.ne

/-- Slab smoothness supplies integrability of every pressure slice. -/
theorem SmoothOnClosedSlab.integrableOn_slice {Ω : Set Space}
    (hb : Bornology.IsBounded Ω) {I : Set ℝ} {p : SpaceTimeScalar}
    (hp : SmoothOnClosedSlab I Ω p) {t : ℝ} (ht : t ∈ I) :
    IntegrableOn (fun x => p (t, x)) Ω := by
  have hc : ContinuousOn (fun x => p (t, x)) (closure Ω) := fun x hx =>
    (hp.contDiffAt_slice ht hx).continuousAt.continuousWithinAt
  exact (hc.integrableOn_compact hb.isCompact_closure).mono_set subset_closure

/-- Subtracting the average really fixes the pressure gauge. -/
theorem domainNormalizePressure_integral {Ω : Set Space} (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) {p : SpaceTimeScalar} {t : ℝ}
    (hp : IntegrableOn (fun x => p (t, x)) Ω) :
    (∫ x in Ω, domainNormalizePressure Ω p (t, x)) = 0 := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa using hb.measure_lt_top (μ := volume)⟩
  simp only [domainNormalizePressure]
  rw [integral_sub hp (integrable_const _), integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, domainPressureMean]
  have hv := (domain_volume_pos ho hb hne).ne'
  field_simp
  ring

/-- No regularity hypothesis is needed for invariance under the spatially constant gauge. -/
theorem pressureGradient_domainNormalizePressure (Ω : Set Space)
    (p : SpaceTimeScalar) (t : ℝ) (x : Space) :
    pressureGradient (domainNormalizePressure Ω p) t x = pressureGradient p t x := by
  unfold pressureGradient domainNormalizePressure
  simp only [fderiv_sub_const]

/-- The physical momentum residual is unchanged by domain normalization. -/
theorem residual_domainNormalizePressure (ν : ℝ) (Ω : Set Space)
    (u : VelocityField) (p : SpaceTimeScalar) (t : ℝ) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u
      (domainNormalizePressure Ω p) t x =
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x := by
  simp only [NavierStokesR3.ProblemStatement.navierStokesResidual,
    pressureGradient_domainNormalizePressure]

/-- Smooth domain integrals on an open time interval, at every finite order. -/
theorem domainIntegral_contDiffOn_nat {Ω : Set Space}
    (hb : Bornology.IsBounded Ω) (hm : MeasurableSet Ω) {I : Set ℝ}
    (hI : IsOpen I) (n : ℕ) {p : SpaceTimeScalar}
    (hp : SmoothOnClosedSlab I Ω p) :
    ContDiffOn ℝ n (fun t => ∫ x in Ω, p (t, x)) I := by
  induction n generalizing p with
  | zero =>
    change ContDiffOn ℝ 0 _ _
    rw [contDiffOn_zero]
    exact fun t ht => (hp.hasDerivAt_integral hb hm hI ht).continuousAt.continuousWithinAt
  | succ n ih =>
    let q : SpaceTimeScalar := fun z => fderiv ℝ p z (1, 0)
    have hq : SmoothOnClosedSlab I Ω q := by
      obtain ⟨N, hN, hsub, hs⟩ := hp
      refine ⟨N, hN, hsub, ?_⟩
      exact (hs.fderiv_of_isOpen hN (by simp)).clm_apply contDiffOn_const
    have hd (t : ℝ) (ht : t ∈ I) :
        HasDerivAt (fun s => ∫ x in Ω, p (s, x)) (∫ x in Ω, q (t, x)) t := by
      convert hp.hasDerivAt_integral hb hm hI ht using 1
      apply setIntegral_congr_fun hm
      intro x hx
      exact (((hp.contDiffAt ⟨ht, subset_closure hx⟩).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv.symm
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_deriv_of_isOpen hI]
    refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · exact (ih hq).congr (fun t ht => (hd t ht).deriv)

/-- The integral of a slab-smooth pressure is smooth on an open time neighborhood. -/
theorem SmoothOnClosedSlab.integral_smooth {Ω : Set Space}
    (hb : Bornology.IsBounded Ω) (hm : MeasurableSet Ω) {I : Set ℝ}
    {p : SpaceTimeScalar} (hp : SmoothOnClosedSlab I Ω p) :
    ∃ J : Set ℝ, IsOpen J ∧ I ⊆ J ∧ ContDiffOn ℝ ∞ (fun t => ∫ x in Ω, p (t, x)) J := by
  obtain ⟨N, hN, hsub, hs⟩ := hp
  let J := interior {t : ℝ | ∀ x ∈ closure Ω, (t, x) ∈ N}
  have hIJ : I ⊆ J := by
    intro t ht
    apply mem_interior_iff_mem_nhds.mpr
    exact hb.isCompact_closure.eventually_forall_of_forall_eventually
      (fun x hx => hN.mem_nhds (hsub ⟨ht, hx⟩))
  refine ⟨J, isOpen_interior, hIJ, contDiffOn_infty.mpr fun n => ?_⟩
  apply domainIntegral_contDiffOn_nat hb hm isOpen_interior n
  exact ⟨N, hN, fun z hz => interior_subset hz.1 z.2 hz.2, hs⟩

/-- Pressure normalization preserves the exact open-neighborhood slab convention. -/
theorem SmoothOnClosedSlab.domainNormalizePressure {Ω : Set Space}
    (hb : Bornology.IsBounded Ω) (hm : MeasurableSet Ω) {I : Set ℝ}
    {p : SpaceTimeScalar} (hp : SmoothOnClosedSlab I Ω p) :
    SmoothOnClosedSlab I Ω (domainNormalizePressure Ω p) := by
  obtain ⟨J, hJ, hIJ, hi⟩ := hp.integral_smooth hb hm
  obtain ⟨N, hN, hsub, hs⟩ := hp
  refine ⟨N ∩ (J ×ˢ univ), hN.inter (hJ.prod isOpen_univ),
    fun z hz => ⟨hsub hz, hIJ hz.1, mem_univ _⟩, ?_⟩
  apply (hs.mono inter_subset_left).sub
  exact (hi.div_const _).comp contDiffOn_fst (fun z hz => hz.2.1)
end NSFormalization.Section3.T23
