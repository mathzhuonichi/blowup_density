import NSFormalization.Source.PacketScaling
import NSFormalization.Paper1.LocalCutoff
import NSFormalization.Source.ViscosityPacket

/-!
# Actual localized insertion into a smooth reference solution

The removal field is constructed by the radial-potential/cutoff theorem. The
physical insertion identity then removes the two cross-advection terms exactly.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace NSFormalization.Source.LocalizedInsertion
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy
open PacketScaling

/-- The actual correction force is smooth when reference and removal are smooth. -/
theorem correctionForce_smooth (ν : ℝ) {v w : VelocityField}
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (correctionForce ν v w) := by
  apply contDiffOn_univ.mp
  have htime := NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative isOpen_univ hw.contDiffOn
  have hlap := NavierStokes.ResidualRegularity.contDiffOn_spatialLaplacian isOpen_univ hw.contDiffOn
  have hdv := NavierStokes.ResidualRegularity.contDiffOn_spatialDerivative isOpen_univ hv.contDiffOn
  have hdw := NavierStokes.ResidualRegularity.contDiffOn_spatialDerivative isOpen_univ hw.contDiffOn
  have hadv := NavierStokes.ResidualRegularity.contDiffOn_advection isOpen_univ hw.contDiffOn
  exact (((htime.sub ((contDiffOn_const (c := ν)).smul hlap)).add
    (hdv.clm_apply hw.contDiffOn)).add (hdw.clm_apply hv.contDiffOn)).add hadv

/-- Every correction-force term is local in the removal field, including its
time derivative and both mixed advection terms. -/
theorem correctionForce_eq_zero_outside (ν : ℝ) (v w : VelocityField) {z : SpaceTime}
    (hz : z ∉ tsupport w) : correctionForce ν v w z = 0 := by
  have he : w =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport w).isOpen_compl.mem_nhds hz] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have ht := NavierStokes.ResidualRegularity.temporalDerivative_congr he
  have hl := NavierStokes.ResidualRegularity.spatialLaplacian_congr he
  have hd := NavierStokes.ResidualRegularity.spatialDerivative_congr he
  have ha := NavierStokes.ResidualRegularity.advection_congr he
  simp only [correctionForce, ht, hl, hd, ha, he.self_of_nhds]
  simp [temporalDerivative, spatialDerivative, spatialLaplacian, advection]

theorem correctionForce_support (ν : ℝ) (v w : VelocityField) :
    tsupport (correctionForce ν v w) ⊆ tsupport w := by
  apply closure_minimal _ (isClosed_tsupport w)
  intro z hz
  by_contra hn
  exact hz (correctionForce_eq_zero_outside ν v w hn)

theorem correctionForce_compact (ν : ℝ) (v : VelocityField) {w : VelocityField}
    (hw : HasCompactSupport w) : HasCompactSupport (correctionForce ν v w) :=
  hw.of_isClosed_subset (isClosed_tsupport _) (correctionForce_support ν v w)

/-- Cancellation on the packet support preserves its arbitrarily late speed
witnesses for the complete inserted velocity. -/
theorem inserted_speed {T : ℝ} {b U : VelocityField}
    (hU : SpeedUnboundedAt T U)
    (hb : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ tsupport (fun y => U (t, y)), b (t, x) = 0) :
    SpeedUnboundedAt T (fun z => b z + U z) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hn, hv⟩ := hU M hM δ hδ
  have hnonzero : U (t, x) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hv
    exact (not_lt_of_ge hM.le) hv
  refine ⟨t, x, ht, hn, ?_⟩
  simpa only [hb t ht x (subset_tsupport _ hnonzero), zero_add] using hv

/-- The removal cancels the background on every packet-support slice. Before
the active interval, the packet support is empty and imposes no condition. -/
theorem background_removed_on_packet {u v w : VelocityField} {K O : Set Space}
    {k T : ℝ} (hk : 0 < k) (x₀ : Space)
    (hs : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => u (t, x)) ⊆ K)
    (hK : IsCompact K) (hKO : scaledSupport k x₀ K ⊆ O)
    (hremove : ∀ t ∈ Icc (T - (k ^ 2)⁻¹) (T + (k ^ 2)⁻¹), ∀ x ∈ O,
      ∀ᶠ y in 𝓝 x, v (t, y) + w (t, y) = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      ∀ x ∈ tsupport (fun y => parabolicVelocity k (T - (k ^ 2)⁻¹) x₀ (zeroPastField u) (t, y)),
      ∀ᶠ y in 𝓝 x, v (t, y) + w (t, y) = 0 := by
  intro t ht x hx
  by_cases hbefore : t ≤ T - (k ^ 2)⁻¹
  · have hz : (fun y => parabolicVelocity k (T - (k ^ 2)⁻¹) x₀ (zeroPastField u) (t, y)) =
        fun _ => 0 := by
      funext y
      exact zeroPast_dilate_early u k (k ^ 2) k _ (sq_nonneg k) x₀ hbefore y
    simp [hz] at hx
  · have hs' := delayed_full_support hK hk x₀ hs
      (t₀ := T - (k ^ 2)⁻¹) t (by simpa only [sub_add_cancel] using ⟨ht.1.le, ht.2⟩)
    apply hremove t ⟨(lt_of_not_ge hbefore).le, ?_⟩ x (hKO (hs' hx))
    have hpos : 0 ≤ (k ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg k)
    linarith [ht.2]

/-- The full sum-field equation follows from the constructed local cancellation. -/
theorem inserted_equation {ν T : ℝ} {v w U g F : VelocityField} {p P : PressureField}
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) (hp : ContDiff ℝ ∞ p)
    (hU : ContDiffOn ℝ ∞ U (Ico (0 : ℝ) T ×ˢ univ))
    (hP : ContDiffOn ℝ ∞ P (Ico (0 : ℝ) T ×ˢ univ))
    (hbg : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v p t x = g (t, x))
    (hpkt : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν U P t x = F (t, x))
    (hremove : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ tsupport (fun y => U (t, y)),
      ∀ᶠ y in 𝓝 x, v (t, y) + w (t, y) = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      residual ν (fun z => v z + w z + U z) (fun z => p z + P z) t x =
        g (t, x) + correctionForce ν v w (t, x) + F (t, x) := by
  intro t ht x
  have hvs : ContDiff ℝ ∞ (fun y : Space => v (t, y)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  have hws : ContDiff ℝ ∞ (fun y : Space => w (t, y)) :=
    hw.comp (contDiff_const.prodMk contDiff_id)
  have hps : ContDiff ℝ ∞ (fun y : Space => p (t, y)) :=
    hp.comp (contDiff_const.prodMk contDiff_id)
  have hUs := NavierStokes.SpatialCurl.contDiff_spatialSlice hU ⟨ht.1.le, ht.2⟩
  have hPs : ContDiff ℝ ∞ (fun y : Space => P (t, y)) :=
    hP.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y => ⟨⟨ht.1.le, ht.2⟩, mem_univ y⟩)
  have hvtime := (hv.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t
  have hwtime := (hw.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t
  have hUtime : DifferentiableAt ℝ (fun s => U (s, x)) t := by
    have hAt : ContDiffAt ℝ ∞ U (t, x) := hU.contDiffAt (prod_mem_nhds (Ico_mem_nhds ht.1 ht.2) univ_mem)
    exact (hAt.comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  apply exact_insertion ν (fun z => v z + w z) U p P
    (fun z => g z + correctionForce ν v w z) F t x
    (hvtime.add hwtime) hUtime (hvs.add hws |>.of_le (by simp)) (hUs.of_le (by simp))
    (hps.differentiable (by simp) x) (hPs.differentiable (by simp) x) (hremove t ht)
    _ (hpkt t ht x)
  rw [corrected_background ν v w p t x hvtime hwtime
    (hvs.of_le (by simp)) (hws.of_le (by simp)) (hps.differentiable (by simp) x), hbg t ht x]

/-- Incompressibility of the complete inserted velocity uses the actual
spatial-derivative sum rule. -/
theorem inserted_divergence {T : ℝ} {v w U : VelocityField}
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w)
    (hU : ContDiffOn ℝ ∞ U (Ico (0 : ℝ) T ×ˢ univ))
    (hdv : ∀ t x, spatialDivergence v t x = 0)
    (hdw : ∀ t x, spatialDivergence w t x = 0)
    (hdU : ∀ t ∈ Ico (0 : ℝ) T, ∀ x, spatialDivergence U t x = 0) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x,
      spatialDivergence (fun z => v z + w z + U z) t x = 0 := by
  intro t ht x
  have hvs : ContDiff ℝ ∞ (fun y : Space => v (t, y)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  have hws : ContDiff ℝ ∞ (fun y : Space => w (t, y)) :=
    hw.comp (contDiff_const.prodMk contDiff_id)
  have hUs := NavierStokes.SpatialCurl.contDiff_spatialSlice hU ht
  rw [NavierStokes.ResidualCalculus.spatialDivergence_add _ _ t x
    ((hvs.add hws).differentiable (by simp) x) (hUs.differentiable (by simp) x),
    NavierStokes.ResidualCalculus.spatialDivergence_add _ _ t x
      (hvs.differentiable (by simp) x) (hws.differentiable (by simp) x),
    hdv t x, hdw t x, hdU t ht x]
  simp

/-- A compact spacetime support supplies one compact spatial support for every
slice; the result is a closed topological-support statement. -/
theorem slice_support_projection {w : VelocityField} (hw : HasCompactSupport w) (t : ℝ) :
    tsupport (fun x => w (t, x)) ⊆ Prod.snd '' tsupport w := by
  apply closure_minimal _ (hw.isCompact.image continuous_snd).isClosed
  intro x hx
  exact ⟨(t, x), subset_tsupport w hx, rfl⟩

/-- Existence of actual local insertion from a physical packet. The removal
field is constructed in the proof, not assumed; its temporal scale is k^{-2}.
All conclusions concern the same total fields and the same perturbation force. -/
theorem localized_insertion_from_packet {ν : ℝ} {u f v g : VelocityField}
    {p q : PressureField} {K : Set Space}
    (hc : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    (hD : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε)
    (huQuiet : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, u (t, x) = 0)
    (hpQuiet : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, p (t, x) = 0)
    (hv : ContDiff ℝ ∞ v) (hq : ContDiff ℝ ∞ q) (_hg : ContDiff ℝ ∞ g)
    (hvdiv : ∀ t x, spatialDivergence v t x = 0)
    (x₀ : Space) {r T τ : ℝ} (hr : 0 < r) (hτ0 : 0 ≤ τ) (hτT : τ < T)
    (hvNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t, x)) :
    ∃ k : ℝ, ∃ w : VelocityField, 0 < k ∧
      ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      let U := parabolicVelocity k (T - (k ^ 2)⁻¹) x₀ (zeroPastField u)
      let P := parabolicPressure k (T - (k ^ 2)⁻¹) x₀ (zeroPastField p)
      let F := parabolicForce k (T - (k ^ 2)⁻¹) x₀ f
      let G := fun z => correctionForce ν v w z + F z
      ContDiffOn ℝ ∞ (fun z => v z + w z + U z) (Ico (0 : ℝ) T ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun z => q z + P z) (Ico (0 : ℝ) T ×ˢ univ) ∧
      ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      tsupport G ⊆ Ioi τ ×ˢ Metric.ball x₀ r ∧
      (∃ L : Set Space, IsCompact L ∧ L ⊆ Metric.ball x₀ r ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          tsupport (fun x => w (t, x) + U (t, x)) ⊆ L ∧
          tsupport (fun x => P (t, x)) ⊆ L) ∧
      (∀ t ∈ Ico (0 : ℝ) T, ∀ x,
        spatialDivergence (fun z => v z + w z + U z) t x = 0) ∧
      (∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
        residual ν (fun z => v z + w z + U z) (fun z => q z + P z) t x = g (t, x) + G (t, x)) ∧
      SpeedUnboundedAt T (fun z => v z + w z + U z) ∧
      (∀ t : ℝ, t ≤ τ → ∀ x,
        v (t, x) + w (t, x) + U (t, x) = v (t, x) ∧ q (t, x) + P (t, x) = q (t, x)) := by
  let τm : ℝ := (τ + T) / 2
  have hτm0 : 0 ≤ τm := by dsimp [τm]; linarith
  have hτmT : τm < T := by dsimp [τm]; linarith
  have hττm : τ ≤ τm := by dsimp [τm]; linarith
  obtain ⟨k, hk, hdelay, hballK, hUs, hPs, hFs, hFcompact, hFball,
    hUPball, hUdiv, hUNS, hSpeed, hEnergy, hDiss, hEarly⟩ :=
    concentrate_classical_packet hc hD hε huQuiet hpQuiet x₀ hr hτm0 hτmT
  let δ : ℝ := (k ^ 2)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (sq_pos_of_pos hk)
  have hwstart : τ < T - 2 * δ := by dsimp [τm] at hdelay; dsimp [δ]; linarith
  obtain ⟨w, O, hws, hwc, hwdiv, hwsupport, hO, hKO, hremove⟩ :=
    NSFormalization.Paper1.exists_local_background_removal hv hvdiv
      (scaledSupport_compact hc.support_compact k x₀) hr hballK T δ hδ
  let U := parabolicVelocity k (T - δ) x₀ (zeroPastField u)
  let P := parabolicPressure k (T - δ) x₀ (zeroPastField p)
  let F := parabolicForce k (T - δ) x₀ f
  have hcancel := background_removed_on_packet hk x₀ hc.velocity_support hc.support_compact hKO hremove
  have hwpast : ∀ t : ℝ, t ≤ τ → ∀ x, w (t, x) = 0 := by
    intro t ht x
    apply image_eq_zero_of_notMem_tsupport (f := w)
    intro hz
    have hh := (hwsupport hz).1.1
    linarith
  have hFafter : ∀ z ∈ tsupport F, τ < z.1 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := parabolicForce_support hc.force_support.1 hk (T - δ) x₀ hz
    have hpos : 0 < y.1 / k ^ 2 := div_pos (hc.force_support.2 hy).1 (sq_pos_of_pos hk)
    have hstart : τ < T - δ := hττm.trans_lt hdelay
    dsimp only
    linarith
  refine ⟨k, w, hk, hws, hwc, (hv.contDiffOn.add hws.contDiffOn).add hUs,
    hq.contDiffOn.add hPs, (correctionForce_smooth ν hv hws).add hFs,
    (correctionForce_compact ν v hwc).add hFcompact.1, ?_, ?_,
    inserted_divergence hv hws hUs hvdiv hwdiv hUdiv, ?_, ?_, ?_⟩
  · intro z hz
    have hh := tsupport_binop_subset (fun a b : Space => a + b) (by simp)
      (correctionForce ν v w) F hz
    rcases hh with hh | hh
    · have hh' := hwsupport (correctionForce_support ν v w hh)
      exact ⟨hwstart.trans hh'.1.1, hh'.2⟩
    · exact ⟨hFafter z hh, hFball z hh⟩
  · let Lw : Set Space := Prod.snd '' tsupport w
    have hLw : IsCompact Lw := hwc.isCompact.image continuous_snd
    refine ⟨Lw ∪ scaledSupport k x₀ K, hLw.union (scaledSupport_compact hc.support_compact k x₀), ?_, ?_⟩
    · rintro x (hx | hx)
      · obtain ⟨z, hz, rfl⟩ := hx
        exact (hwsupport hz).2
      · exact hballK hx
    · intro t ht
      constructor
      · intro x hx
        have hh := tsupport_binop_subset (fun a b : Space => a + b) (by simp)
          (fun x => w (t, x)) (fun x => U (t, x)) hx
        rcases hh with hh | hh
        · exact Or.inl (slice_support_projection hwc t hh)
        · exact Or.inr (delayed_full_support hc.support_compact hk x₀ hc.velocity_support
            (t₀ := T - δ) t (by simpa only [δ, sub_add_cancel] using ht) hh)
      · intro x hx
        exact Or.inr (delayed_pressure_support hc.support_compact hk x₀ hc.pressure_support
          (t₀ := T - δ) t (by simpa only [δ, sub_add_cancel] using ht) hx)
  · intro t ht x
    have hh := inserted_equation hv hws hq hUs hPs hvNS hUNS hcancel t ht x
    simpa only [add_assoc] using hh
  · exact inserted_speed hSpeed (fun t ht x hx => (hcancel t ht x hx).self_of_nhds)
  · intro t ht x
    have hqearly := hEarly t (ht.trans hττm) x
    simp [hwpast t ht x, hqearly.1, hqearly.2]

/-- A fully instantiated localized singular insertion at every positive viscosity.
The packet and the removal field are both constructed. The total velocity and
pressure agree with the reference for every time at or before the requested
history threshold. Compact spatial support refers to their perturbations. -/
theorem exists_localized_singular_solution {ν : ℝ} (hν : 0 < ν)
    {v g : VelocityField} {q : PressureField}
    (hv : ContDiff ℝ ∞ v) (hq : ContDiff ℝ ∞ q) (hg : ContDiff ℝ ∞ g)
    (hvdiv : ∀ t x, spatialDivergence v t x = 0)
    (x₀ : Space) {r T τ : ℝ} (hr : 0 < r) (hτ0 : 0 ≤ τ) (hτT : τ < T)
    (hvNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t, x)) :
    ∃ V : VelocityField, ∃ Q : PressureField, ∃ G : VelocityField,
      ContDiffOn ℝ ∞ V (Ico (0 : ℝ) T ×ˢ univ) ∧
      ContDiffOn ℝ ∞ Q (Ico (0 : ℝ) T ×ˢ univ) ∧
      ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      tsupport G ⊆ Ioi τ ×ˢ Metric.ball x₀ r ∧
      (∃ L : Set Space, IsCompact L ∧ L ⊆ Metric.ball x₀ r ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          tsupport (fun x => V (t, x) - v (t, x)) ⊆ L ∧
          tsupport (fun x => Q (t, x) - q (t, x)) ⊆ L) ∧
      (∀ t ∈ Ico (0 : ℝ) T, ∀ x, spatialDivergence V t x = 0) ∧
      (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν V Q t x = g (t, x) + G (t, x)) ∧
      SpeedUnboundedAt T V ∧
      (∀ t : ℝ, t ≤ τ → ∀ x, V (t, x) = v (t, x) ∧ Q (t, x) = q (t, x)) := by
  obtain ⟨u, p, f, K, hc, hD, hquiet⟩ := selected_packet_every_viscosity hν
  have huQuiet : ∀ t ∈ Ioo (0 : ℝ) (3 / 8), ∀ x, u (t, x) = 0 := by
    intro t ht x
    exact (hquiet t (by rw [abs_of_pos ht.1]; exact ht.2.le) x).1
  have hpQuiet : ∀ t ∈ Ioo (0 : ℝ) (3 / 8), ∀ x, p (t, x) = 0 := by
    intro t ht x
    exact (hquiet t (by rw [abs_of_pos ht.1]; exact ht.2.le) x).2
  obtain ⟨k, w, hk, hws, hwc, hVs, hQs, hGs, hGc, hGloc, hL,
    hdiv, hNS, hSpeed, hEarly⟩ := localized_insertion_from_packet hc hD (by norm_num : (0 : ℝ) < 3 / 8)
      huQuiet hpQuiet hv hq hg hvdiv x₀ hr hτ0 hτT hvNS
  refine ⟨_, _, _, hVs, hQs, hGs, hGc, hGloc, ?_, hdiv, hNS, hSpeed, hEarly⟩
  obtain ⟨L, hLc, hLb, hLs⟩ := hL
  refine ⟨L, hLc, hLb, ?_⟩
  intro t ht
  have hvel (a b c : Space) : a + b + c - a = b + c := by abel
  simpa only [hvel, add_sub_cancel_left] using hLs t ht

end NSFormalization.Source.LocalizedInsertion
