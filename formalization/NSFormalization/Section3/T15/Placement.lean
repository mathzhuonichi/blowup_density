import NSFormalization.Section3.T15.Bridges

/-!
# T15 U2 — scaled-support placement (`prop:scaling`, `paper/sections/03-torus.tex:101-120`)

The paper first fixes one compact `K_*` covering both the packet carrier `K` and
the spatial projection of `supp F`, together with a coordinate ball `B` whose
closure sits inside the fundamental cube, and requires `x₀ + εK_* ⊆ B`
(`paper/sections/03-torus.tex:101-106`).  It then rescales velocity, pressure and
force (`:113-118`) and concludes that on each slice there is a single supported
copy inside `B` (`:120`).

This module discharges exactly that placement, from the **raw packet support
clauses** rather than an assumed transported inclusion:

* velocity/pressure slice transport (`scaledVelocity_tsupp_subset`,
  `scaledPressure_tsupp_subset`) reuse the ℝ³ support-invariance lemmas
  `Source.PacketScaling.delayed_full_support` / `delayed_pressure_support`
  (`formalization/NSFormalization/Source/PacketScaling.lean:335,409`) — the same
  route as `Section4/I03/Energy.lean:197 scaled_slice_hasCompactSupport` — over
  the **honest presingular window** `t ∈ Ico 0 T` (the transported image of the
  packet's `Ico 0 1` support window under `parabolic_window`);
* force slice transport (`scaledForce_tsupp_subset`) is global in time and comes
  directly from `PacketAPI.force_support` (`HasCompactSupport`) and the placement
  clause `force_projection_subset`, mirroring
  `Source.PacketScaling.parabolicForce_support`
  (`formalization/NSFormalization/Source/PacketScaling.lean:534`);
* the affine image lies in the chart ball (`affineImage_subset_ball`, from
  `place.eps_space`) and the ball lies in `interior fundamentalCube`
  (`ball_subset_interior_cube`, from `place.chartBall_in_cube`);
* each slice has compact support (`*_slice_hasCompactSupport`), since its
  `tsupport` is a closed subset of the compact affine image of `K_*`.

The `PlacementData` fields consumed here are stated in `research/T15/Spec.lean:560-643`
(`Kstar_compact`, `carrier_subset`, `force_projection_subset`, `eps_space`,
`chartBall_in_cube`).  Because `PlacementData` mentions `Contracts.V1.PacketAPI`,
which `formalization/` cannot import, the lemmas are phrased over the raw fields
`u p f : Velocity/PressureField` with the `PacketAPI` support clauses as
hypotheses verbatim; the probe `research/T15/probes/placement_closes.lean`
instantiates them from a `PlacementData`-shaped consumer on `Bindings.packet ν hν`.
-/

noncomputable section
namespace NSFormalization.Section3.T15
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Source.PacketScaling
open NSFormalization.Section3.T13

/-- `03-torus.tex:106,113`: with inverse length `ε⁻¹` and activation time
`t_ε = T - ε²`, the active window `t_ε + (ε⁻¹)²⁻¹` is exactly `T`.  This is
`Source.PacketScaling`'s `parabolic_window` specialised inline (that lemma lives
in `Section4/I03/Energy.lean`, which this module does not import). -/
theorem scaledActivation_eq (T ε : ℝ) : (T - ε ^ 2) + ((ε⁻¹) ^ 2)⁻¹ = T := by
  rw [inv_pow, inv_inv]; ring

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

/-! ## Slice support transport -/

/-- `03-torus.tex:113-120`: each presingular spatial slice of the rescaled
velocity is supported in the affine image `x₀ + ε • K_*`.

The support hypothesis `hvel` is the packet's `PacketAPI.velocity_support`
(`verification/Contracts/V1/Packet.lean:218-220`) over its source window
`Ico 0 1`; `hcarrier_subset` is `PlacementData.carrier_subset`.  The conclusion
holds on the transported window `t ∈ Ico 0 T`, exactly the paper's `t < T`
restriction for velocity (`:120`).  Route: the rescaling is definitionally the
upstream `parabolicVelocity ε⁻¹ (T-ε²) x₀ (zeroPastField u)` (Bridges'
`scaledVelocity_eq_parabolicVelocity`), whose slice support is
`Source.PacketScaling.delayed_full_support`, valued in
`scaledSupport ε⁻¹ x₀ carrier = (fun y ↦ x₀ + ε • y) '' carrier`; monotonicity in
the carrier lifts it to `K_*`. -/
theorem scaledVelocity_tsupp_subset {u : VelocityField} {x₀ : Space} {T ε : ℝ}
    {carrier Kstar : Set Space} (hε : 0 < ε)
    (hcarrier_compact : IsCompact carrier)
    (hvel : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ carrier)
    (hcarrier_subset : carrier ⊆ Kstar) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    tsupport (fun x : Space => scaledVelocity u x₀ T ε (t, x)) ⊆
      (fun y : Space => x₀ + ε • y) '' Kstar := by
  rw [scaledVelocity_eq_parabolicVelocity]
  have h := delayed_full_support (K := carrier) (t₀ := T - ε ^ 2)
    hcarrier_compact (inv_pos.2 hε) x₀ hvel t (by rw [scaledActivation_eq]; exact ht)
  refine h.trans ?_
  rw [show scaledSupport ε⁻¹ x₀ carrier = (fun y : Space => x₀ + ε • y) '' carrier from by
    simp only [scaledSupport, inv_inv]]
  exact Set.image_mono hcarrier_subset

/-- `03-torus.tex:113-120`: each presingular spatial slice of the rescaled
pressure is supported in the affine image `x₀ + ε • K_*`, from
`PacketAPI.pressure_support` (`verification/Contracts/V1/Packet.lean:222-224`)
and `PlacementData.carrier_subset`, on the transported window `t ∈ Ico 0 T`.
Route: `Source.PacketScaling.delayed_pressure_support`, via
`scaledPressure_eq_parabolicPressure`. -/
theorem scaledPressure_tsupp_subset {p : PressureField} {x₀ : Space} {T ε : ℝ}
    {carrier Kstar : Set Space} (hε : 0 < ε)
    (hcarrier_compact : IsCompact carrier)
    (hpre : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ carrier)
    (hcarrier_subset : carrier ⊆ Kstar) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    tsupport (fun x : Space => scaledPressure p x₀ T ε (t, x)) ⊆
      (fun y : Space => x₀ + ε • y) '' Kstar := by
  rw [scaledPressure_eq_parabolicPressure]
  have h := delayed_pressure_support (K := carrier) (t₀ := T - ε ^ 2)
    hcarrier_compact (inv_pos.2 hε) x₀ hpre t (by rw [scaledActivation_eq]; exact ht)
  refine h.trans ?_
  rw [show scaledSupport ε⁻¹ x₀ carrier = (fun y : Space => x₀ + ε • y) '' carrier from by
    simp only [scaledSupport, inv_inv]]
  exact Set.image_mono hcarrier_subset

/-- `03-torus.tex:101-102,113-120`: each spatial slice of the rescaled force is
supported in the affine image `x₀ + ε • K_*`, for **every** physical time (the
force is global, `:120`).  Inputs are the packet's `force_support`
(`HasCompactSupport`, `verification/Contracts/V1/Packet.lean:213`) via `_hf`
(kept for interface parity with `PacketAPI`: the compact superset the inclusion
needs is already supplied by `Kstar_compact`, which by `force_projection_subset`
covers the force projection) and the placement clause `force_projection_subset`
via `hforce_proj`.  A slice is
nonzero only where the source point `((ε⁻¹)²(t-t_ε), ε⁻¹•(x-x₀))` lies in
`tsupport f`, whose spatial coordinate `ε⁻¹•(x-x₀) ∈ K_*`; then
`x = x₀ + ε • (ε⁻¹•(x-x₀))`.  This mirrors
`Source.PacketScaling.parabolicForce_support`. -/
theorem scaledForce_tsupp_subset {f : VelocityField} {x₀ : Space} {T ε : ℝ}
    {Kstar : Set Space} (hε : 0 < ε) (hKstar_compact : IsCompact Kstar)
    (_hf : HasCompactSupport f)
    (hforce_proj : ∀ t : ℝ, ∀ x : Space, (t, x) ∈ tsupport f → x ∈ Kstar)
    (t : ℝ) :
    tsupport (fun x : Space => scaledForce f x₀ T ε (t, x)) ⊆
      (fun y : Space => x₀ + ε • y) '' Kstar := by
  apply closure_minimal _ (affineImage_compact hKstar_compact).isClosed
  intro x hx
  have hfne : f (scaledSourcePoint x₀ T ε (t, x)) ≠ 0 := by
    intro hz
    exact hx (by simp [scaledForce, hz])
  have hmem : scaledSourcePoint x₀ T ε (t, x) ∈ tsupport f := subset_tsupport _ hfne
  refine ⟨ε⁻¹ • (x - x₀), hforce_proj _ _ hmem, ?_⟩
  show x₀ + ε • (ε⁻¹ • (x - x₀)) = x
  rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  abel

/-! ## Compact support of the slices -/

/-- Each presingular velocity slice has compact support: its `tsupport` is a
closed subset of the compact affine image of `K_*`. -/
theorem scaledVelocity_slice_hasCompactSupport {u : VelocityField} {x₀ : Space}
    {T ε : ℝ} {carrier Kstar : Set Space} (hε : 0 < ε)
    (hcarrier_compact : IsCompact carrier)
    (hvel : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ carrier)
    (hcarrier_subset : carrier ⊆ Kstar) (hKstar_compact : IsCompact Kstar)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasCompactSupport (fun x : Space => scaledVelocity u x₀ T ε (t, x)) :=
  (affineImage_compact hKstar_compact).of_isClosed_subset (isClosed_tsupport _)
    (scaledVelocity_tsupp_subset hε hcarrier_compact hvel hcarrier_subset ht)

/-- Each presingular pressure slice has compact support. -/
theorem scaledPressure_slice_hasCompactSupport {p : PressureField} {x₀ : Space}
    {T ε : ℝ} {carrier Kstar : Set Space} (hε : 0 < ε)
    (hcarrier_compact : IsCompact carrier)
    (hpre : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => p (t, x)) ⊆ carrier)
    (hcarrier_subset : carrier ⊆ Kstar) (hKstar_compact : IsCompact Kstar)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasCompactSupport (fun x : Space => scaledPressure p x₀ T ε (t, x)) :=
  (affineImage_compact hKstar_compact).of_isClosed_subset (isClosed_tsupport _)
    (scaledPressure_tsupp_subset hε hcarrier_compact hpre hcarrier_subset ht)

/-- Each force slice has compact support, at every physical time. -/
theorem scaledForce_slice_hasCompactSupport {f : VelocityField} {x₀ : Space}
    {T ε : ℝ} {Kstar : Set Space} (hε : 0 < ε) (hKstar_compact : IsCompact Kstar)
    (hf : HasCompactSupport f)
    (hforce_proj : ∀ t : ℝ, ∀ x : Space, (t, x) ∈ tsupport f → x ∈ Kstar)
    (t : ℝ) :
    HasCompactSupport (fun x : Space => scaledForce f x₀ T ε (t, x)) :=
  (affineImage_compact hKstar_compact).of_isClosed_subset (isClosed_tsupport _)
    (scaledForce_tsupp_subset hε hKstar_compact hf hforce_proj t)

/-! ## Slices supported strictly inside the fundamental cube

These are the single-copy hypotheses consumed by U3
(`HaarBridge.eLpNorm_torusLift_periodize`, `periodize_eq_of_mem_cube`). -/

/-- `03-torus.tex:120`: each presingular velocity slice is supported strictly
inside `interior fundamentalCube`. -/
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
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    tsupport (fun x : Space => scaledVelocity u x₀ T ε (t, x)) ⊆
      interior fundamentalCube :=
  (scaledVelocity_tsupp_subset hε_mem.1 hcarrier_compact hvel hcarrier_subset ht).trans
    ((affineImage_subset_ball hε_mem heps_space).trans
      (ball_subset_interior_cube hchartBall_in_cube))

/-- `03-torus.tex:120`: each presingular pressure slice is supported strictly
inside `interior fundamentalCube`. -/
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
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    tsupport (fun x : Space => scaledPressure p x₀ T ε (t, x)) ⊆
      interior fundamentalCube :=
  (scaledPressure_tsupp_subset hε_mem.1 hcarrier_compact hpre hcarrier_subset ht).trans
    ((affineImage_subset_ball hε_mem heps_space).trans
      (ball_subset_interior_cube hchartBall_in_cube))

/-- `03-torus.tex:120`: each force slice is supported strictly inside
`interior fundamentalCube`, at every physical time. -/
theorem scaledForce_slice_subset_cube {f : VelocityField}
    {x₀ chartCenter : Space} {T ε ε₀ chartRadius : ℝ} {Kstar : Set Space}
    (hε_mem : ε ∈ Ioc (0 : ℝ) ε₀) (hKstar_compact : IsCompact Kstar)
    (hf : HasCompactSupport f)
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
