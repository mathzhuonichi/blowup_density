import NSFormalization.Section3.T15.Bridges

/-!
# T15 U2 — scaled-support placement (`prop:scaling`, `paper/sections/03-torus.tex:101-120`)

The paper fixes one compact `K_*` covering both the packet carrier `K` and the
spatial projection of `supp F`, a coordinate ball `B` with
`closure B ⊆ interior Q`, and requires `x₀ + εK_* ⊆ B`
(`paper/sections/03-torus.tex:101-106`); it then rescales velocity, pressure and
force (`:113-118`) and concludes a single supported copy inside `B`, with
velocity and pressure used for `t < T` and force globally (`:120`).

This module proves that placement from the **raw `PacketAPI` support clauses**.
The time domains match the immediate U3 consumers: `velocity_singleCopy` /
`pressure_singleCopy` quantify over **every real `t < T`**
(`research/T15/Spec.lean:704-718`, matching `velocity_summable` /
`pressure_summable` at `:671-685`), and `force_singleCopy` over **every real
`t`** (`research/T15/Spec.lean:726-731`).  Accordingly:

* `scaledVelocity_tsupp_subset` / `scaledPressure_tsupp_subset` hold for all
  `t < T`.  For `t ≤ T-ε²` (before activation `t_ε = T-ε²`) the rescaled source
  time is nonpositive, so the zero-past extension makes the slice identically
  zero (`scaled*_slice_eq_zero`, via `Source.PacketScaling.zeroPast_dilate_early`)
  and `tsupport = ∅`.  For `T-ε² < t < T` the source time lies in `(0,1)`, so the
  packet clause applies and `Source.PacketScaling.parabolic_support` /
  `dilate_support` transport the support to `scaledSupport ε⁻¹ x₀ carrier =
  (fun y ↦ x₀+ε•y) '' carrier`; `carrier ⊆ Kstar` lifts it to `K_*`.
* `scaledForce_tsupp_subset` holds for every `t`, from the verbatim packet clause
  `CompactPositiveTimeSupport f` (used through
  `Source.PacketScaling.parabolicForce_support hf.1`) and the placement clause
  `force_projection_subset`.
* `affineImage_subset_ball` (from `eps_space`), `ball_subset_interior_cube` (from
  `chartBall_in_cube`), the composed `*_slice_subset_cube` (strictly inside
  `interior fundamentalCube`), and `*_slice_hasCompactSupport` complete the U2 /
  U3 interface.

Because `PlacementData` (`research/T15/Spec.lean:560-643`) mentions
`Contracts.V1.PacketAPI`, which `formalization/` cannot import, the lemmas are
phrased over the raw fields with the `PacketAPI` clauses as hypotheses verbatim;
`research/T15/probes/placement_closes.lean` exercises them on an explicit
geometric instance at the active time `t = 7/8`.
-/

noncomputable section
namespace NSFormalization.Section3.T15
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Source.PacketScaling
open NSFormalization.Section3.T13

/-- `03-torus.tex:106,113`: with inverse length `ε⁻¹` and activation time
`t_ε = T - ε²`, the active window `t_ε + (ε⁻¹)²⁻¹` is exactly `T`
(`Source.PacketScaling`'s `parabolic_window`, restated inline). -/
theorem scaledActivation_eq (T ε : ℝ) : (T - ε ^ 2) + ((ε⁻¹) ^ 2)⁻¹ = T := by
  rw [inv_pow, inv_inv]; ring

/-- If a spatial slice vanishes identically, its topological support is empty,
hence contained in anything. -/
theorem tsupport_subset_of_slice_zero {V : Type*} [Zero V] {g : Space → V} (S : Set Space)
    (hg : ∀ x : Space, g x = 0) : tsupport g ⊆ S := by
  have hsupp : Function.support g = ∅ := by
    rw [Function.support_eq_empty_iff]; funext x; exact hg x
  rw [tsupport, hsupp, closure_empty]
  exact empty_subset _

/-! ## Affine image of the compact set -/

/-- `03-torus.tex:101-105`: the transported compact set `x₀ + ε • K_*` is compact
(continuous image of the compact `K_*`). -/
theorem affineImage_compact {x₀ : Space} {ε : ℝ} {Kstar : Set Space}
    (hKstar_compact : IsCompact Kstar) :
    IsCompact ((fun y : Space => x₀ + ε • y) '' Kstar) :=
  hKstar_compact.image (by fun_prop)

/-- `03-torus.tex:104-105`: `x₀ + ε • K_* ⊆ B` for every admissible scale, from
the placement clause `eps_space`. -/
theorem affineImage_subset_ball {x₀ chartCenter : Space} {chartRadius ε ε₀ : ℝ}
    {Kstar : Set Space} (hε_mem : ε ∈ Ioc (0 : ℝ) ε₀)
    (heps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
      x₀ + ε • y ∈ Metric.ball chartCenter chartRadius) :
    (fun y : Space => x₀ + ε • y) '' Kstar ⊆ Metric.ball chartCenter chartRadius := by
  rintro z ⟨y, hy, rfl⟩
  exact heps_space ε hε_mem y hy

/-- `03-torus.tex:22-23,102-105`: `B ⊆ interior Q`, from the placement clause
`chartBall_in_cube` (`closure B ⊆ interior Q`) and `B ⊆ closure B`. -/
theorem ball_subset_interior_cube {chartCenter : Space} {chartRadius : ℝ}
    (hchartBall_in_cube :
      closure (Metric.ball chartCenter chartRadius) ⊆ interior fundamentalCube) :
    Metric.ball chartCenter chartRadius ⊆ interior fundamentalCube :=
  subset_closure.trans hchartBall_in_cube

/-! ## Pre-activation vanishing -/

/-- `03-torus.tex:108-113`: before activation (`t ≤ T-ε²`) the rescaled velocity
slice is identically zero, since the source time is nonpositive and the packet's
zero-past extension vanishes there (`Source.PacketScaling.zeroPast_dilate_early`). -/
theorem scaledVelocity_slice_eq_zero {u : VelocityField} {x₀ : Space} {T ε : ℝ}
    {t : ℝ} (ht : t ≤ T - ε ^ 2) (x : Space) :
    scaledVelocity u x₀ T ε (t, x) = 0 := by
  rw [scaledVelocity_eq_parabolicVelocity]
  exact zeroPast_dilate_early u ε⁻¹ ((ε⁻¹) ^ 2) ε⁻¹ (T - ε ^ 2) (sq_nonneg _) x₀ ht x

/-- `03-torus.tex:108-116`: before activation the rescaled pressure slice is
identically zero. -/
theorem scaledPressure_slice_eq_zero {p : PressureField} {x₀ : Space} {T ε : ℝ}
    {t : ℝ} (ht : t ≤ T - ε ^ 2) (x : Space) :
    scaledPressure p x₀ T ε (t, x) = 0 := by
  rw [scaledPressure_eq_parabolicPressure]
  exact zeroPast_dilate_early p ((ε⁻¹) ^ 2) ((ε⁻¹) ^ 2) ε⁻¹ (T - ε ^ 2) (sq_nonneg _) x₀ ht x

/-! ## Slice support transport (all `t < T`) -/

/-- `03-torus.tex:113-120`: for every `t < T`, the rescaled velocity slice is
supported in the affine image `x₀ + ε • K_*`.

Inputs are the packet's `velocity_support`
(`verification/Contracts/V1/Packet.lean:218-220`, source window `Ico 0 1`),
`carrier_compact`, and `PlacementData.carrier_subset`.  The time domain `t < T`
is exactly that of the U3 consumer `velocity_singleCopy`
(`research/T15/Spec.lean:704-710`).  Route: for `t ≤ T-ε²` the slice vanishes
(`scaledVelocity_slice_eq_zero`); for `T-ε² < t < T` the source time is in
`(0,1)`, so `Source.PacketScaling.parabolic_support` applies (the same route as
`Section4/I03/Energy.lean:197`), valued in
`scaledSupport ε⁻¹ x₀ carrier = (fun y ↦ x₀+ε•y) '' carrier`, then `Set.image_mono`
lifts `carrier` to `K_*`. -/
theorem scaledVelocity_tsupp_subset {u : VelocityField} {x₀ : Space} {T ε : ℝ}
    {carrier Kstar : Set Space} (hε : 0 < ε)
    (hcarrier_compact : IsCompact carrier)
    (hvel : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ carrier)
    (hcarrier_subset : carrier ⊆ Kstar) {t : ℝ} (ht : t < T) :
    tsupport (fun x : Space => scaledVelocity u x₀ T ε (t, x)) ⊆
      (fun y : Space => x₀ + ε • y) '' Kstar := by
  rcases le_or_gt t (T - ε ^ 2) with hbefore | hafter
  · exact tsupport_subset_of_slice_zero _ (scaledVelocity_slice_eq_zero hbefore)
  · have hspos : 0 < (ε⁻¹) ^ 2 * (t - (T - ε ^ 2)) :=
      mul_pos (pow_pos (inv_pos.2 hε) 2) (by linarith)
    have hs1 : (ε⁻¹) ^ 2 * (t - (T - ε ^ 2)) < 1 := by
      have hcancel : (ε⁻¹) ^ 2 * ε ^ 2 = 1 := by
        rw [inv_pow]; exact inv_mul_cancel₀ (pow_ne_zero 2 hε.ne')
      calc (ε⁻¹) ^ 2 * (t - (T - ε ^ 2))
          < (ε⁻¹) ^ 2 * ε ^ 2 :=
            mul_lt_mul_of_pos_left (by linarith) (pow_pos (inv_pos.2 hε) 2)
        _ = 1 := hcancel
    have hs' : tsupport (fun y : Space =>
        zeroPastField u ((ε⁻¹) ^ 2 * (t - (T - ε ^ 2)), y)) ⊆ carrier := by
      have heq : (fun y : Space => zeroPastField u ((ε⁻¹) ^ 2 * (t - (T - ε ^ 2)), y))
          = (fun y : Space => u ((ε⁻¹) ^ 2 * (t - (T - ε ^ 2)), y)) := by
        funext y; rw [zeroPastField_of_pos u hspos]
      rw [heq]; exact hvel _ ⟨le_of_lt hspos, hs1⟩
    rw [scaledVelocity_eq_parabolicVelocity]
    refine (parabolic_support (t₀ := T - ε ^ 2) hcarrier_compact (inv_pos.2 hε) x₀ hs').trans ?_
    rw [show scaledSupport ε⁻¹ x₀ carrier = (fun y : Space => x₀ + ε • y) '' carrier from by
      simp only [scaledSupport, inv_inv]]
    exact Set.image_mono hcarrier_subset

/-- `03-torus.tex:113-120`: for every `t < T`, the rescaled pressure slice is
supported in the affine image `x₀ + ε • K_*`, from `pressure_support`
(`verification/Contracts/V1/Packet.lean:222-224`) and `carrier_subset`.  Time
domain `t < T` matches `pressure_singleCopy` (`research/T15/Spec.lean:715-718`).
Route as for velocity, with `Source.PacketScaling.dilate_support` for the scalar
active branch. -/
theorem scaledPressure_tsupp_subset {p : PressureField} {x₀ : Space} {T ε : ℝ}
    {carrier Kstar : Set Space} (hε : 0 < ε)
    (hcarrier_compact : IsCompact carrier)
    (hpre : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ carrier)
    (hcarrier_subset : carrier ⊆ Kstar) {t : ℝ} (ht : t < T) :
    tsupport (fun x : Space => scaledPressure p x₀ T ε (t, x)) ⊆
      (fun y : Space => x₀ + ε • y) '' Kstar := by
  rcases le_or_gt t (T - ε ^ 2) with hbefore | hafter
  · exact tsupport_subset_of_slice_zero _ (scaledPressure_slice_eq_zero hbefore)
  · have hspos : 0 < (ε⁻¹) ^ 2 * (t - (T - ε ^ 2)) :=
      mul_pos (pow_pos (inv_pos.2 hε) 2) (by linarith)
    have hs1 : (ε⁻¹) ^ 2 * (t - (T - ε ^ 2)) < 1 := by
      have hcancel : (ε⁻¹) ^ 2 * ε ^ 2 = 1 := by
        rw [inv_pow]; exact inv_mul_cancel₀ (pow_ne_zero 2 hε.ne')
      calc (ε⁻¹) ^ 2 * (t - (T - ε ^ 2))
          < (ε⁻¹) ^ 2 * ε ^ 2 :=
            mul_lt_mul_of_pos_left (by linarith) (pow_pos (inv_pos.2 hε) 2)
        _ = 1 := hcancel
    have hs' : tsupport (fun y : Space =>
        zeroPastField p ((ε⁻¹) ^ 2 * (t - (T - ε ^ 2)), y)) ⊆ carrier := by
      have heq : (fun y : Space => zeroPastField p ((ε⁻¹) ^ 2 * (t - (T - ε ^ 2)), y))
          = (fun y : Space => p ((ε⁻¹) ^ 2 * (t - (T - ε ^ 2)), y)) := by
        funext y; rw [zeroPastField_of_pos p hspos]
      rw [heq]; exact hpre _ ⟨le_of_lt hspos, hs1⟩
    rw [scaledPressure_eq_parabolicPressure]
    refine (dilate_support (t₀ := T - ε ^ 2) hcarrier_compact ((ε⁻¹) ^ 2) ((ε⁻¹) ^ 2)
      (inv_pos.2 hε) x₀ hs').trans ?_
    rw [show scaledSupport ε⁻¹ x₀ carrier = (fun y : Space => x₀ + ε • y) '' carrier from by
      simp only [scaledSupport, inv_inv]]
    exact Set.image_mono hcarrier_subset

/-- `03-torus.tex:101-102,113-120`: for **every** `t`, the rescaled force slice is
supported in the affine image `x₀ + ε • K_*`.  Time domain `∀ t` matches
`force_singleCopy` (`research/T15/Spec.lean:726-731`).  Inputs are the packet's
verbatim `force_support` clause `CompactPositiveTimeSupport f`
(`verification/Contracts/V1/Packet.lean:210-214`), used through
`Source.PacketScaling.parabolicForce_support hf.1`, and the placement clause
`force_projection_subset` via `hforce_proj`.  The upstream lemma transports the
compact spacetime support of `f` by the inverse affine map; the spatial
coordinate of the source point of any nonzero slice value lies in
`Prod.snd '' tsupport f ⊆ K_*`. -/
theorem scaledForce_tsupp_subset {f : VelocityField} {x₀ : Space} {T ε : ℝ}
    {Kstar : Set Space} (hε : 0 < ε) (hKstar_compact : IsCompact Kstar)
    (hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hforce_proj : ∀ t : ℝ, ∀ x : Space, (t, x) ∈ tsupport f → x ∈ Kstar)
    (t : ℝ) :
    tsupport (fun x : Space => scaledForce f x₀ T ε (t, x)) ⊆
      (fun y : Space => x₀ + ε • y) '' Kstar := by
  apply closure_minimal _ (affineImage_compact hKstar_compact).isClosed
  intro x hx
  have hmem : (t, x) ∈ tsupport (parabolicForce ε⁻¹ (T - ε ^ 2) x₀ f) := by
    apply subset_tsupport
    show parabolicForce ε⁻¹ (T - ε ^ 2) x₀ f (t, x) ≠ 0
    rw [← scaledForce_eq_parabolicForce]
    exact hx
  obtain ⟨z, hz, hzeq⟩ :=
    parabolicForce_support hf.1 (inv_pos.2 hε) (T - ε ^ 2) x₀ hmem
  simp only [Prod.mk.injEq] at hzeq
  refine ⟨z.2, hforce_proj z.1 z.2 hz, ?_⟩
  have h2 := hzeq.2
  rw [inv_inv] at h2
  exact h2

/-! ## Compact support of the slices -/

/-- Each velocity slice with `t < T` has compact support: its `tsupport` is a
closed subset of the compact affine image of `K_*`. -/
theorem scaledVelocity_slice_hasCompactSupport {u : VelocityField} {x₀ : Space}
    {T ε : ℝ} {carrier Kstar : Set Space} (hε : 0 < ε)
    (hcarrier_compact : IsCompact carrier)
    (hvel : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ carrier)
    (hcarrier_subset : carrier ⊆ Kstar) (hKstar_compact : IsCompact Kstar)
    {t : ℝ} (ht : t < T) :
    HasCompactSupport (fun x : Space => scaledVelocity u x₀ T ε (t, x)) :=
  (affineImage_compact hKstar_compact).of_isClosed_subset (isClosed_tsupport _)
    (scaledVelocity_tsupp_subset hε hcarrier_compact hvel hcarrier_subset ht)

/-- Each pressure slice with `t < T` has compact support. -/
theorem scaledPressure_slice_hasCompactSupport {p : PressureField} {x₀ : Space}
    {T ε : ℝ} {carrier Kstar : Set Space} (hε : 0 < ε)
    (hcarrier_compact : IsCompact carrier)
    (hpre : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ carrier)
    (hcarrier_subset : carrier ⊆ Kstar) (hKstar_compact : IsCompact Kstar)
    {t : ℝ} (ht : t < T) :
    HasCompactSupport (fun x : Space => scaledPressure p x₀ T ε (t, x)) :=
  (affineImage_compact hKstar_compact).of_isClosed_subset (isClosed_tsupport _)
    (scaledPressure_tsupp_subset hε hcarrier_compact hpre hcarrier_subset ht)

/-- Each force slice has compact support, at every physical time. -/
theorem scaledForce_slice_hasCompactSupport {f : VelocityField} {x₀ : Space}
    {T ε : ℝ} {Kstar : Set Space} (hε : 0 < ε) (hKstar_compact : IsCompact Kstar)
    (hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hforce_proj : ∀ t : ℝ, ∀ x : Space, (t, x) ∈ tsupport f → x ∈ Kstar)
    (t : ℝ) :
    HasCompactSupport (fun x : Space => scaledForce f x₀ T ε (t, x)) :=
  (affineImage_compact hKstar_compact).of_isClosed_subset (isClosed_tsupport _)
    (scaledForce_tsupp_subset hε hKstar_compact hf hforce_proj t)

/-! ## Slices supported strictly inside the fundamental cube

These are the single-copy hypotheses consumed by U3
(`HaarBridge.eLpNorm_torusLift_periodize`, `periodize_eq_of_mem_cube`). -/

/-- `03-torus.tex:120`: for every `t < T`, the velocity slice is supported
strictly inside `interior fundamentalCube`. -/
theorem scaledVelocity_slice_subset_cube {u : VelocityField}
    {x₀ chartCenter : Space} {T ε ε₀ chartRadius : ℝ} {carrier Kstar : Set Space}
    (hε_mem : ε ∈ Ioc (0 : ℝ) ε₀) (hcarrier_compact : IsCompact carrier)
    (hvel : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ carrier)
    (hcarrier_subset : carrier ⊆ Kstar)
    (heps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
      x₀ + ε • y ∈ Metric.ball chartCenter chartRadius)
    (hchartBall_in_cube :
      closure (Metric.ball chartCenter chartRadius) ⊆ interior fundamentalCube)
    {t : ℝ} (ht : t < T) :
    tsupport (fun x : Space => scaledVelocity u x₀ T ε (t, x)) ⊆
      interior fundamentalCube :=
  (scaledVelocity_tsupp_subset hε_mem.1 hcarrier_compact hvel hcarrier_subset ht).trans
    ((affineImage_subset_ball hε_mem heps_space).trans
      (ball_subset_interior_cube hchartBall_in_cube))

/-- `03-torus.tex:120`: for every `t < T`, the pressure slice is supported
strictly inside `interior fundamentalCube`. -/
theorem scaledPressure_slice_subset_cube {p : PressureField}
    {x₀ chartCenter : Space} {T ε ε₀ chartRadius : ℝ} {carrier Kstar : Set Space}
    (hε_mem : ε ∈ Ioc (0 : ℝ) ε₀) (hcarrier_compact : IsCompact carrier)
    (hpre : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ carrier)
    (hcarrier_subset : carrier ⊆ Kstar)
    (heps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
      x₀ + ε • y ∈ Metric.ball chartCenter chartRadius)
    (hchartBall_in_cube :
      closure (Metric.ball chartCenter chartRadius) ⊆ interior fundamentalCube)
    {t : ℝ} (ht : t < T) :
    tsupport (fun x : Space => scaledPressure p x₀ T ε (t, x)) ⊆
      interior fundamentalCube :=
  (scaledPressure_tsupp_subset hε_mem.1 hcarrier_compact hpre hcarrier_subset ht).trans
    ((affineImage_subset_ball hε_mem heps_space).trans
      (ball_subset_interior_cube hchartBall_in_cube))

/-- `03-torus.tex:120`: for every `t`, the force slice is supported strictly
inside `interior fundamentalCube`. -/
theorem scaledForce_slice_subset_cube {f : VelocityField}
    {x₀ chartCenter : Space} {T ε ε₀ chartRadius : ℝ} {Kstar : Set Space}
    (hε_mem : ε ∈ Ioc (0 : ℝ) ε₀) (hKstar_compact : IsCompact Kstar)
    (hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hforce_proj : ∀ t : ℝ, ∀ x : Space, (t, x) ∈ tsupport f → x ∈ Kstar)
    (heps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
      x₀ + ε • y ∈ Metric.ball chartCenter chartRadius)
    (hchartBall_in_cube :
      closure (Metric.ball chartCenter chartRadius) ⊆ interior fundamentalCube)
    (t : ℝ) :
    tsupport (fun x : Space => scaledForce f x₀ T ε (t, x)) ⊆
      interior fundamentalCube :=
  (scaledForce_tsupp_subset hε_mem.1 hKstar_compact hf hforce_proj t).trans
    ((affineImage_subset_ball hε_mem heps_space).trans
      (ball_subset_interior_cube hchartBall_in_cube))

end NSFormalization.Section3.T15
