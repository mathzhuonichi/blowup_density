import NSFormalization.Source.LocalizedInsertion
import NSFormalization.Section4.I02.Support

/-!
# R42: the reference-slab form of the insertion identities

`paper/sections/04-whole-space.tex:44-55` (proof of Theorem 4.2, `thm:Rinsert`)
assembles `u_eps = v + w_eps + U_eps`, `p_eps = pi + P_eps`,
`g_eps = g + H_eps + F_eps` from the corrected background `b_eps = v + w_eps`
and the rescaled packet.  `NSFormalization.Source.LocalizedInsertion` already
does the PDE algebra, but for a reference that is *globally* smooth on all of
spacetime (`hv : ContDiff ℝ ∞ v`).

Theorem 4.2's reference is a classical solution, smooth only on the slab
`[0, T+delta) x R^3` (`02-preliminaries.tex:28-36`,
`verification/Contracts/V1/Data.lean`, `ClassicalSolutionR.velocity_smooth`).
This file restates the two identities the assembly needs -- the momentum
equation and incompressibility of the inserted velocity -- with the reference
hypothesis weakened to `ContDiffOn` on a slab `[0,Tref) x R^3` containing
`[0,T)`, together with the three pieces of geometry that put the rescaled
fields inside the ball `B`:

* `scaledSupport_subset_ball`: `x0 + eps K` is inside `ball x0 r` when
  `K` is inside `ball 0 R` and `eps R < r` (`03-torus.tex:104-105`);
* `exists_spatial_radius`: a compact spacetime support has a bounded spatial
  projection -- this is the enlargement `K -> K_*` of `03-torus.tex:101-102`,
  which the packet force needs and which `I02`'s cutoff radius does not carry;
* `parabolicForce_ball`: the rescaled packet force `F_eps` is spatially inside
  `ball x0 r`.

Nothing here mentions a versioned contract; `verification/Bindings/InsertionFamily.lean`
supplies the `I01`/`I02`/`I03` fields to these lemmas.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace NSFormalization.Section4.R42

open NavierStokes.ProblemStatement
open NSFormalization.Source NSFormalization.Source.PacketScaling

/-! ## 1. Geometry: the rescaled carriers sit inside the ball -/

/-- `x0 + eps K subset ball x0 r`, the smallness clause `eps R_* < r` of
`paper/sections/03-torus.tex:104-105, 212` (clarification `C2`).  The inverse
length is `k = eps^{-1}`, so `scaledSupport k x0 K` is `x0 + eps K`. -/
theorem scaledSupport_subset_ball {K : Set Space} {R r ε : ℝ} (hε : 0 < ε)
    (hKR : K ⊆ Metric.ball (0 : Space) R) (hεR : ε * R < r) (x₀ : Space) :
    scaledSupport ε⁻¹ x₀ K ⊆ Metric.ball x₀ r := by
  rintro z ⟨y, hy, rfl⟩
  have hyN : ‖y‖ < R := by
    have := hKR hy
    rwa [Metric.mem_ball, dist_zero_right] at this
  have hnorm : ‖x₀ + ((ε⁻¹ : ℝ))⁻¹ • y - x₀‖ = ε * ‖y‖ := by
    rw [add_sub_cancel_left, inv_inv, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  rw [Metric.mem_ball, dist_eq_norm, hnorm]
  exact lt_trans (mul_lt_mul_of_pos_left hyN hε) hεR

/-- A compact spacetime support has a bounded spatial projection: the compact
enlargement `K_*` of `paper/sections/03-torus.tex:101-102` exists for the packet
force `F` of Theorem 1.1, whose only stated localization is
`CompactPositiveTimeSupport`.  This is what replaces the cutoff radius `R_*`
when the rescaled *force* has to be placed inside `B`. -/
theorem exists_spatial_radius {f : VelocityField} (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ tsupport f, z.2 ∈ Metric.ball (0 : Space) R := by
  obtain ⟨B, hB, hb⟩ := (hf.isCompact.image continuous_snd).isBounded.exists_pos_norm_le
  refine ⟨B + 1, by linarith, ?_⟩
  intro z hz
  have hle := hb z.2 ⟨z, hz, rfl⟩
  rw [Metric.mem_ball, dist_zero_right]
  linarith

/-- `supp F_eps` projects into `ball x0 r`: the spatial half of "`g_eps - g` in
`C_c^infinity(B x (0,infinity))`", `paper/sections/04-whole-space.tex:38`, for
the rescaled packet force. -/
theorem parabolicForce_ball {f : VelocityField} (hf : HasCompactSupport f)
    {R r ε : ℝ} (hε : 0 < ε)
    (hfR : ∀ z ∈ tsupport f, z.2 ∈ Metric.ball (0 : Space) R)
    (hεR : ε * R < r) (t₀ : ℝ) (x₀ : Space) :
    ∀ z ∈ tsupport (parabolicForce ε⁻¹ t₀ x₀ f), z.2 ∈ Metric.ball x₀ r := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := parabolicForce_support hf (inv_pos.mpr hε) t₀ x₀ hz
  have hyN : ‖y.2‖ < R := by
    have := hfR y hy
    rwa [Metric.mem_ball, dist_zero_right] at this
  have hnorm : ‖x₀ + ((ε⁻¹ : ℝ))⁻¹ • y.2 - x₀‖ = ε * ‖y.2‖ := by
    rw [add_sub_cancel_left, inv_inv, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  rw [Metric.mem_ball, dist_eq_norm]
  change ‖x₀ + ((ε⁻¹ : ℝ))⁻¹ • y.2 - x₀‖ < r
  rw [hnorm]
  exact lt_trans (mul_lt_mul_of_pos_left hyN hε) hεR

/-! ## 2. Smoothness of the rescaled fields up to the new singular time -/

/-- The parabolic rescaling of a field smooth on `(-infinity,1) x R^3` is smooth
on `(-infinity,T) x R^3`, since `t_eps + eps^2 = T`.  Used for `U_eps`
(`a = eps^{-1}`) and for `P_eps` (`a = eps^{-2}`), `eq:scaling`,
`paper/sections/03-torus.tex:112-118`. -/
theorem dilate_smoothOn_target {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (a : ℝ) {ε : ℝ} (hε : 0 < ε) (T : ℝ) (x₀ : Space)
    (hf : ContDiffOn ℝ ∞ f (Iio (1 : ℝ) ×ˢ univ)) :
    ContDiffOn ℝ ∞ (dilateField a ((ε⁻¹) ^ 2) ε⁻¹ (T - ε ^ 2) x₀ f)
      (Iio T ×ˢ (univ : Set Space)) := by
  have h := dilate_smoothOn (f := f) a (inv_pos.mpr hε) (T - ε ^ 2) x₀ hf
  rwa [I02.inv_sq_inv, sub_add_cancel] at h

/-! ## 3. The insertion identities over a reference slab -/

/-- The momentum equation for `u_eps = v + w_eps + U_eps` and
`p_eps = pi + P_eps`, `paper/sections/04-whole-space.tex:50-51`, with the
reference smooth only on the slab `[0,Tref) x R^3`, `Tref >= T`.

The background hypothesis is the *corrected* one -- `b_eps = v + w_eps` already
solves the equation with the unchanged pressure `pi` and the force `g + H_eps`,
which is `CorrectionAPI.corrected_background`
(`03-torus.tex:321-325`, `04-whole-space.tex:51`) -- so the correction force is
not re-derived here.  `hremove` is `eq:bgzero` in germ form
(`03-torus.tex:190-193`), and it is what kills both cross-advection terms. -/
theorem inserted_equation_slab {ν T Tref : ℝ} {v w U g F : VelocityField}
    {p P : PressureField} (hTS : T ≤ Tref)
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) Tref ×ˢ (univ : Set Space)))
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) Tref ×ˢ (univ : Set Space)))
    (hw : ContDiff ℝ ∞ w)
    (hU : ContDiffOn ℝ ∞ U (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hP : ContDiffOn ℝ ∞ P (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hbg : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν (fun z => v z + w z) p t x = g (t, x))
    (hpkt : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν U P t x = F (t, x))
    (hremove : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ tsupport (fun y => U (t, y)),
      ∀ᶠ y in 𝓝 x, v (t, y) + w (t, y) = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      residual ν (fun z => v z + w z + U z) (fun z => p z + P z) t x =
        g (t, x) + F (t, x) := by
  intro t ht x
  have htS : t ∈ Ico (0 : ℝ) Tref := ⟨ht.1.le, lt_of_lt_of_le ht.2 hTS⟩
  have htT : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hvs : ContDiff ℝ ∞ (fun y : Space => v (t, y)) :=
    NavierStokes.SpatialCurl.contDiff_spatialSlice hv htS
  have hws : ContDiff ℝ ∞ (fun y : Space => w (t, y)) :=
    hw.comp (contDiff_const.prodMk contDiff_id)
  have hps : ContDiff ℝ ∞ (fun y : Space => p (t, y)) :=
    hp.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y => ⟨htS, mem_univ y⟩)
  have hUs : ContDiff ℝ ∞ (fun y : Space => U (t, y)) :=
    NavierStokes.SpatialCurl.contDiff_spatialSlice hU htT
  have hPs : ContDiff ℝ ∞ (fun y : Space => P (t, y)) :=
    hP.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y => ⟨htT, mem_univ y⟩)
  have hvt : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t := by
    have hAt : ContDiffAt ℝ ∞ v (t, x) :=
      hv.contDiffAt (prod_mem_nhds (Ico_mem_nhds ht.1 (lt_of_lt_of_le ht.2 hTS)) univ_mem)
    exact (hAt.comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hwt : DifferentiableAt ℝ (fun s : ℝ => w (s, x)) t :=
    (hw.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t
  have hUt : DifferentiableAt ℝ (fun s : ℝ => U (s, x)) t := by
    have hAt : ContDiffAt ℝ ∞ U (t, x) :=
      hU.contDiffAt (prod_mem_nhds (Ico_mem_nhds ht.1 ht.2) univ_mem)
    exact (hAt.comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  exact exact_insertion ν (fun z => v z + w z) U p P g F t x
    (hvt.add hwt) hUt ((hvs.add hws).of_le (by simp)) (hUs.of_le (by simp))
    (hps.differentiable (by simp) x) (hPs.differentiable (by simp) x)
    (hremove t ht) (hbg t ht x) (hpkt t ht x)

/-- Incompressibility of `u_eps = v + w_eps + U_eps` on `[0,T)`, including
`t = 0`, with the reference smooth only on the slab `[0,Tref) x R^3`.  The
perturbation hypothesis is `CorrectionAPI.perturbation_divergence_free`
(`03-torus.tex:332`, `04-whole-space.tex:37-38`), so the two summands are not
separated here. -/
theorem inserted_divergence_slab {T Tref : ℝ} {v w U : VelocityField} (hTS : T ≤ Tref)
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) Tref ×ˢ (univ : Set Space)))
    (hw : ContDiff ℝ ∞ w)
    (hU : ContDiffOn ℝ ∞ U (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hdv : ∀ t ∈ Ico (0 : ℝ) Tref, ∀ x, spatialDivergence v t x = 0)
    (hdp : ∀ t ∈ Ico (0 : ℝ) T, ∀ x, spatialDivergence (fun z => w z + U z) t x = 0) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x,
      spatialDivergence (fun z => v z + w z + U z) t x = 0 := by
  intro t ht x
  have htS : t ∈ Ico (0 : ℝ) Tref := ⟨ht.1, lt_of_lt_of_le ht.2 hTS⟩
  have hvs : ContDiff ℝ ∞ (fun y : Space => v (t, y)) :=
    NavierStokes.SpatialCurl.contDiff_spatialSlice hv htS
  have hws : ContDiff ℝ ∞ (fun y : Space => w (t, y)) :=
    hw.comp (contDiff_const.prodMk contDiff_id)
  have hUs : ContDiff ℝ ∞ (fun y : Space => U (t, y)) :=
    NavierStokes.SpatialCurl.contDiff_spatialSlice hU ht
  have hassoc : (fun z : SpaceTime => v z + w z + U z) = fun z => v z + (w z + U z) := by
    funext z
    rw [add_assoc]
  rw [hassoc, NavierStokes.ResidualCalculus.spatialDivergence_add v (fun z => w z + U z) t x
      (hvs.differentiable (by simp) x) ((hws.add hUs).differentiable (by simp) x),
    hdv t htS x, hdp t ht x, add_zero]

end NSFormalization.Section4.R42
