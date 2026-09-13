import Contracts.V1.Data
import Contracts.V1.Packet

/-! Stable specification for the local vector potential, the solenoidal
background correction and the correction force used by Section 4.

Task `collaboration/tasks/I02.md`, graph node `I02`.  Version 1 fixes the
Euclidean (`R^3`) content of

* Lemma 3.4, "A local divergence-free cutoff" (`lem:potential`),
  `paper/sections/03-torus.tex:176-216`, displays `eq:potential` (`:178-180`),
  `eq:cutoff` (`:183-187`) and `eq:bgzero` (`:190-193`), and
* Lemma 3.5, "Bounds for the background correction" (`lem:correction`),
  `paper/sections/03-torus.tex:218-285`, displays `eq:H` (`:220-224`),
  `eq:derivativebounds` (`:226-231`), `eq:wE` (`:234`) and `eq:Hmixed`
  (`:235-237`),

exactly as Theorem 4.2 (`thm:Rinsert`) reuses them.  Section 4 states the reuse
explicitly: "The vector potential in Lemma~\ref{lem:potential} is local, so its
proof applies in any Euclidean ball.  In Lemma~\ref{lem:correction}, the
support, derivative, energy, and mixed Lebesgue bounds are also local; only the
final transfer of fractional norms to the torus is unnecessary.  Thus the same
`w_eps` and `H_eps` are available on `R^3`, with the same uniform bounds."
(`paper/sections/04-whole-space.tex:23-29`).

Deliberately **out of scope**, and left to `I03`: the fractional bound
`eq:HHs` (`03-torus.tex:238-240`), the positive- and negative-order Sobolev
scaling `eq:RpositiveScale`/`eq:RnegativeScale`
(`04-whole-space.tex:63-78`), and every statement about the rescaled packet
`U_eps, P_eps, F_eps` other than the support facts that `eq:bgzero` needs.
Also out of scope: Theorem 4.2's lifespan and blow-up conclusions, which need
the `D01` solution class.  The reference `(v, pi, g)` is taken here as a plain
smooth divergence-free field satisfying the momentum equation pointwise on the
open slab `(0,T+delta) x R^3`.

## Conventions

* Time is the first spacetime coordinate, as in `Contracts.V1.Packet`.
* All measures are the ordinary Lebesgue `volume` on `R^3` and on `R`.  Nothing
  here is periodic.
* `supp` of the manuscript is `tsupport`, the closure of the nonvanishing set.
* The two norms of `eq:wE` and `eq:Hmixed` are the canonical Section 4 norms
  `Data.energyENorm` (`E_T`, `01-introduction.tex:143` eq:Enorm) and
  `Data.mixedLebesgueENorm` (`L^q(0,infinity;L^p)`,
  `01-introduction.tex:134`), not the ad hoc real-valued norms of the
  implementation.  Both are `ENNReal`-valued, so neither bound can be met
  vacuously by an infinite quantity.
* The manuscript's "for all sufficiently small `eps`" is the single threshold
  `eps0` together with the smallness clauses `eps_time` and `eps_space`, which
  transcribe `2 eps^2 < min(T,delta)` and `x0 + eps K subset B`
  (`03-torus.tex:104-105, 212`).  One `eps`-family carries every conclusion.

## Self-containedness

A registered specification may depend only on Mathlib, on the seven canonical
definition modules listed in `experiments/check_contracts.py`, and on other
contracts.  This module therefore imports only `Contracts.V1.Data` (the
Section 4 norms and field types) and `Contracts.V1.Packet` (the packet API and
the Navier-Stokes operators), and writes out every remaining notion --
`derivativeEntry`, `curlLinear`, `curl`, `cross`, `scaledSpatialCutoff`,
`scaledTemporalCutoff`, `dilateField`, `parabolicVelocity`, `scaledPacket`
-- verbatim as upstream -- together with `alpha`, which has no single upstream
counterpart.  `verification/Bindings/Correction.lean` carries one `rfl` bridge
theorem per copied notion, plus `alpha_add_one` for `alpha`, `spatialGradient_eq`
and `energyENorm_eq` for the two `Contracts.V1.Data` norms used in the two
bounds; each stops compiling the moment the two sides drift apart.

Cross references for the copied notions: `derivativeEntry`, `curlLinear`,
`curl` are `vendor/NavierStokesAndEuler/NavierStokes/SpatialCurl.lean:26-52`;
`cross` is `formalization/NSFormalization/Paper1/RadialPotential.lean:16-19`;
`scaledSpatialCutoff` and `scaledTemporalCutoff` are
`formalization/NSFormalization/Paper1/CorrectionProfile.lean:135-139`;
`dilateField` and `parabolicVelocity` are
`formalization/NSFormalization/Source/ParabolicScaling.lean:21-23,92-93`;
`zeroPastField` (reused from `Contracts.V1.Packet`) is
`formalization/NSFormalization/Source/PacketScaling.lean:243-244`.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1

open Set MeasureTheory
open scoped ContDiff ENNReal Topology

/-! ## 1. Notions copied from the implementation, guarded by `rfl` bridges -/

/-- The `(j,i)` entry of a spatial derivative;
`vendor/NavierStokesAndEuler/NavierStokes/SpatialCurl.lean:26-27`. -/
def derivativeEntry (i j : Fin 3) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (ContinuousLinearMap.apply ℝ Space (coordinateVector i))

/-- The antisymmetric part of a Jacobian, identified with a vector;
`vendor/NavierStokesAndEuler/NavierStokes/SpatialCurl.lean:34-37`. -/
def curlLinear : (Space →L[ℝ] Space) →L[ℝ] Space :=
  (derivativeEntry 1 2 - derivativeEntry 2 1).smulRight (coordinateVector 0) +
  (derivativeEntry 2 0 - derivativeEntry 0 2).smulRight (coordinateVector 1) +
  (derivativeEntry 0 1 - derivativeEntry 1 0).smulRight (coordinateVector 2)

/-- The physical Euclidean curl of a spatial field, the manuscript's
`nabla times`; `vendor/NavierStokesAndEuler/NavierStokes/SpatialCurl.lean:52`. -/
def curl (A : Space → Space) (x : Space) : Space := curlLinear (fderiv ℝ A x)

/-- The coordinate cross product `a x b`;
`formalization/NSFormalization/Paper1/RadialPotential.lean:16-19`. -/
def cross (a b : Space) : Space :=
  (a 1 * b 2 - a 2 * b 1) • coordinateVector 0 +
  (a 2 * b 0 - a 0 * b 2) • coordinateVector 1 +
  (a 0 * b 1 - a 1 * b 0) • coordinateVector 2

/-- `theta_eps(x) = theta((x - x0)/eps)`, the first display of `eq:cutoff`,
`paper/sections/03-torus.tex:184`;
`formalization/NSFormalization/Paper1/CorrectionProfile.lean:135-136`. -/
def scaledSpatialCutoff (θ : Space → ℝ) (x₀ : Space) (ε : ℝ) : Space → ℝ :=
  fun x => θ (ε⁻¹ • (x - x₀))

/-- `eta_eps(t) = eta((t - T)/eps^2)`, the second display of `eq:cutoff`,
`paper/sections/03-torus.tex:185`;
`formalization/NSFormalization/Paper1/CorrectionProfile.lean:138-139`. -/
def scaledTemporalCutoff (η : ℝ → ℝ) (T ε : ℝ) : ℝ → ℝ :=
  fun t => η ((ε ^ 2)⁻¹ * (t - T))

/-- The affine amplitude-and-coordinate dilation of a spacetime field;
`formalization/NSFormalization/Source/ParabolicScaling.lean:21-23`. -/
def dilateField {V : Type*} [SMul ℝ V] (a c d t₀ : ℝ) (x₀ : Space)
    (f : SpaceTime → V) : SpaceTime → V :=
  fun z => a • f (c * (z.1 - t₀), d • (z.2 - x₀))

/-- The parabolic velocity rescaling at inverse length `k`;
`formalization/NSFormalization/Source/ParabolicScaling.lean:92-93`. -/
def parabolicVelocity (k t₀ : ℝ) (x₀ : Space) (u : VelocityField) : VelocityField :=
  dilateField k (k ^ 2) k t₀ x₀ u

/-- `U_eps(x,t) = eps^{-1} U((x-x0)/eps, (t-t_eps)/eps^2)` with
`t_eps = T - eps^2`, the first display of `eq:scaling`
(`paper/sections/03-torus.tex:112-113`), applied to the zero extension of the
packet velocity to nonpositive source time (clarification `C1`,
`03-torus.tex:108-111`).  Only its *support* enters `I02`.  This is the third
summand of `NSFormalization.Source.InsertionFamily.velocity`. -/
def scaledPacket (U : VelocityField) (x₀ : Space) (T ε : ℝ) : VelocityField :=
  parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)

/-- `alpha(p,q) = -3 + 3/p + 2/q`, the packet force exponent of
`eq:packetFscale` (`paper/sections/03-torus.tex:130-131`).  The correction force
gains exactly one extra power, `eq:Hmixed` (`03-torus.tex:235-237`).  The
endpoints `p = infinity` and `q = infinity` use the convention `1/infinity = 0`,
which `ENNReal.toReal` realizes as `3 / (top : ENNReal).toReal = 3 / 0 = 0`. -/
def alpha (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal

/-! ## 2. The contract -/

/-- Every obligation that the Euclidean halves of Lemma 3.4 and Lemma 3.5 place
on the local vector potential `A`, the cutoffs `theta, eta`, the solenoidal
correction `w_eps` and the correction force `H_eps`, in exactly the form
Theorem 4.2 (`thm:Rinsert`, `paper/sections/04-whole-space.tex:31-79`) consumes.

The packet is not restated: it is the already registered `PacketAPI nu` of
`I01.packet`, and only the five facts `velocity`, `carrier`, `carrier_compact`,
`velocity_support`, `divergence_free` (plus `velocity_smooth`, `quietTime`,
`quiet_pos`, `velocity_quiet` for the zero extension) are used.

Layout of the fields.

* `T ... reference_equation`: the ambient data -- the singular time, the
  regularity margin, and the reference `(v, pi, g)`.
* `x0 ... eps_space`: the geometry `B = ball x0 r`, the cutoffs and the
  smallness threshold `eps0`.
* `potential_smooth`, `potential_formula`, `potential_curl`: Lemma 3.4's vector
  potential, `eq:potential`.
* `correction_formula ... correction_derivative_bound`: the rest of Lemma 3.4
  and the first bound of `eq:derivativebounds`.
* `force_formula ... force_derivative_bound`: Lemma 3.5's force, its support
  measures and the second bound of `eq:derivativebounds`.
* `correction_energy_bound`, `force_mixed_bound`: `eq:wE` and `eq:Hmixed`,
  against the canonical Section 4 norms of `Contracts.V1.Data`.
* `corrected_background`, `perturbation_divergence_free`: the two extra
  conclusions Theorem 4.2's proof extracts, which
  `research/section4/REVIEW.md:77-88` requires `R42` to re-export.

No field is a hypothesis about an unspecified proposition, and no field is
`True`, `exists x, True` or any similar placeholder. -/
structure CorrectionAPI (ν : ℝ) (P : PacketAPI ν) where
  -- ### Ambient data: times and reference solution
  /-- The prescribed singular time `T`, `paper/sections/04-whole-space.tex:8`. -/
  T : ℝ
  /-- `T > 0`, `paper/sections/04-whole-space.tex:8`. -/
  time_pos : 0 < T
  /-- The regularity margin `delta`: the reference is regular through
  `T + delta`, `paper/sections/04-whole-space.tex:32`; `03-torus.tex:164-165`. -/
  δ : ℝ
  /-- `delta > 0`, `paper/sections/04-whole-space.tex:32`. -/
  margin_pos : 0 < δ
  /-- The reference velocity `v`, `paper/sections/03-torus.tex:164`.  Only its
  restriction to a fixed compact neighbourhood of `B` and of time `T` is used,
  `paper/sections/04-whole-space.tex:45`. -/
  v : VelocityField
  /-- The reference pressure `pi`, `paper/sections/03-torus.tex:164`. -/
  π : PressureField
  /-- The reference force `g`, `paper/sections/03-torus.tex:164`. -/
  g : VelocityField
  /-- `v` is smooth on the open slab `(0, T+delta) x R^3`.  This is the
  Euclidean content of "smooth on `[0,T+delta]`" (`03-torus.tex:164`) that
  Lemmas 3.4 and 3.5 actually use; no membership in a solution class is
  assumed, so this is a *weaker* hypothesis and a stronger contract. -/
  reference_smooth : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space))
  /-- `pi` is smooth on the open slab.  The manuscript fixes a reference
  *solution* `(v, pi, g)` smooth on `[0,T+delta]`,
  `paper/sections/03-torus.tex:164`; only the differentiability of the spatial
  slices of `pi` is used, and only through `corrected_background`. -/
  reference_pressure_smooth :
    ContDiffOn ℝ ∞ π (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space))
  /-- `div v = 0` on the slab: the hypothesis "let `v` be smooth and divergence
  free in a spatial ball centered at `x0`", `paper/sections/03-torus.tex:177`,
  in its global-in-space form. -/
  reference_divergence_free : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space,
    spatialDivergence v t x = 0
  /-- `d_t v + (v.grad)v - nu Laplacian v + grad pi = g` on the slab: the
  reference solves the momentum equation.  Used only to state
  `corrected_background`, `paper/sections/03-torus.tex:321-325`,
  `04-whole-space.tex:51`. -/
  reference_equation : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space,
    navierStokesResidual ν v π t x = g (t, x)

  -- ### Geometry, cutoffs and the scale threshold
  /-- The centre `x0` of the coordinate ball, `paper/sections/03-torus.tex:103`. -/
  x₀ : Space
  /-- The radius of the ball `B = ball x0 r` in which every perturbation lives,
  `paper/sections/04-whole-space.tex:32` ("fix any nonempty open ball
  `B` in `R^3`").  A general nonempty open ball contains such a ball around the
  chosen `x0`, which is clarification `C2` of
  `research/section4/STATEMENTS.md:342-344`. -/
  r : ℝ
  /-- `r > 0`: `B` is nonempty, `paper/sections/04-whole-space.tex:32`. -/
  radius_pos : 0 < r
  /-- `theta` in `C_c^infinity(R^3)`, `paper/sections/03-torus.tex:181`. -/
  θ : Space → ℝ
  /-- `theta` is smooth, `paper/sections/03-torus.tex:181`. -/
  theta_smooth : ContDiff ℝ ∞ θ
  /-- `theta` has compact support, `paper/sections/03-torus.tex:181`. -/
  theta_compactSupport : HasCompactSupport θ
  /-- The open plateau of `theta`: `theta` equals one on a *neighbourhood* of
  the packet carrier, `paper/sections/03-torus.tex:181`.  The Urysohn
  construction is `03-torus.tex:167-174`. -/
  plateau : Set Space
  /-- The plateau is open, `paper/sections/03-torus.tex:181-182`. -/
  plateau_open : IsOpen plateau
  /-- The packet carrier is inside the plateau,
  `paper/sections/03-torus.tex:181`. -/
  carrier_subset_plateau : P.carrier ⊆ plateau
  /-- `theta = 1` on the plateau, `paper/sections/03-torus.tex:181`. -/
  theta_one : EqOn θ (fun _ => 1) plateau
  /-- A radius containing `supp theta`; it fixes the constant in "supported
  inside the coordinate ball", `paper/sections/03-torus.tex:188, 212`.  It is
  the `R_*` of `research/section4/STATEMENTS.md:250`. -/
  θRadius : ℝ
  /-- `R_* > 0`. -/
  theta_radius_pos : 0 < θRadius
  /-- `supp theta` is inside `ball 0 R_*`, `paper/sections/03-torus.tex:212`. -/
  theta_support : tsupport θ ⊆ Metric.ball (0 : Space) θRadius
  /-- `eta` in `C_c^infinity((-2,2))` equal to one on `[-1,1]`,
  `paper/sections/03-torus.tex:181-182`. -/
  η : ℝ → ℝ
  /-- `eta` is smooth, `paper/sections/03-torus.tex:182`. -/
  eta_smooth : ContDiff ℝ ∞ η
  /-- `eta` has compact support, `paper/sections/03-torus.tex:182`. -/
  eta_compactSupport : HasCompactSupport η
  /-- `eta = 1` on `[-1,1]`, `paper/sections/03-torus.tex:182`.  This makes
  `eta_eps = 1` throughout the active packet interval `[T-eps^2, T)`,
  `03-torus.tex:214-215`. -/
  eta_one : EqOn η (fun _ => 1) (Icc (-1 : ℝ) 1)
  /-- `supp eta` is inside `(-2,2)`, `paper/sections/03-torus.tex:182`. -/
  eta_support : tsupport η ⊆ Ioo (-2 : ℝ) 2
  /-- The scale threshold of "for all sufficiently small `eps > 0`",
  `paper/sections/03-torus.tex:188`, `04-whole-space.tex:32`. -/
  ε₀ : ℝ
  /-- `eps0 > 0`. -/
  eps_pos : 0 < ε₀
  /-- `eps0 <= 1`, the normalization under which all constants below are
  uniform, `paper/sections/03-torus.tex:242`. -/
  eps_le_one : ε₀ ≤ 1
  /-- `2 eps^2 < min(T, delta)`, `paper/sections/03-torus.tex:212` and
  `03-torus.tex:104`.  It puts the whole cutoff window inside `(0, T+delta)`,
  where the reference is regular. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ
  /-- `eps R_* < r`, i.e. the scaled support of `theta` is strictly inside the
  coordinate ball and `x0 + eps K` is inside `B`,
  `paper/sections/03-torus.tex:104-105, 212`; clarification `C2`. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θRadius < r

  -- ### Lemma 3.4, `eq:potential`: the local vector potential
  /-- `A`, the radial vector potential of `eq:potential`,
  `paper/sections/03-torus.tex:178-180`. -/
  potential : VelocityField
  /-- `A` is smooth wherever the reference is,
  `paper/sections/03-torus.tex:177-180`. -/
  potential_smooth : ContDiffOn ℝ ∞ potential (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space))
  /-- `A(x,t) = int_0^1 r v(x0 + r y, t) x y dr` with `y = x - x0`: the display
  `eq:potential`, `paper/sections/03-torus.tex:179`. -/
  potential_formula : ∀ t : ℝ, ∀ x : Space,
    potential (t, x) = ∫ ρ in (0 : ℝ)..1, ρ • cross (v (t, x₀ + ρ • (x - x₀))) (x - x₀)
  /-- `curl A = v`, `paper/sections/03-torus.tex:181`, proved at
  `03-torus.tex:196-210`.  The curl is spatial, with the physical time
  frozen. -/
  potential_curl : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space,
    curl (fun y : Space => potential (t, y)) x = v (t, x)

  -- ### Lemma 3.4, `eq:cutoff` and `eq:bgzero`: the solenoidal correction
  /-- The family `eps |-> w_eps`.  One family carries every conclusion below, as
  `research/section4/STATEMENTS.md:190-192` demands. -/
  correction : ℝ → VelocityField
  /-- `w_eps = -curl(eta_eps theta_eps A)`, the third display of `eq:cutoff`,
  `paper/sections/03-torus.tex:186`. -/
  correction_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    correction ε z =
      -curl (fun y : Space =>
          (scaledTemporalCutoff η T ε z.1 * scaledSpatialCutoff θ x₀ ε y) •
            potential (z.1, y)) z.2
  /-- `w_eps` is a smooth field, `paper/sections/03-torus.tex:188`.  Smooth on
  all of spacetime: outside the cutoff support it is identically zero,
  `03-torus.tex:212`. -/
  correction_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (correction ε)
  /-- `w_eps` is divergence free, `paper/sections/03-torus.tex:188`; "its
  divergence vanishes because it is a curl", `03-torus.tex:212`. -/
  correction_divergence_free : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, ∀ x : Space,
    spatialDivergence (correction ε) t x = 0
  /-- `w_eps` has compact spacetime support,
  `paper/sections/03-torus.tex:188`. -/
  correction_compactSupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀, HasCompactSupport (correction ε)
  /-- `supp w_eps` is inside `(T-2eps^2, T+2eps^2) x ball x0 (eps R_*)`:
  "supported inside the coordinate ball and in `(T-2eps^2, T+2eps^2)`",
  `paper/sections/03-torus.tex:188-189`.  This is the `O(eps)` spatial ball and
  the `O(eps^2)` duration. -/
  correction_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    tsupport (correction ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ Metric.ball x₀ (ε * θRadius)
  /-- `supp w_eps` is inside `B` at every time: the velocity perturbation stays
  inside the prescribed ball, `paper/sections/04-whole-space.tex:37-38`. -/
  correction_support_ball : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ,
    tsupport (fun x : Space => correction ε (t, x)) ⊆ Metric.ball x₀ r
  /-- `w_eps = 0` for `t <= T - 2 eps^2`: the earlier history and the initial
  value are untouched, `paper/sections/03-torus.tex:333-335`,
  `04-whole-space.tex:36`. -/
  correction_vanishes_before : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, t ≤ T - 2 * ε ^ 2 →
    ∀ x : Space, correction ε (t, x) = 0
  /-- `eq:bgzero`, literal form: for each presingular time there is an *open
  neighbourhood* of `supp U_eps(t)` on which `v + w_eps = 0`,
  `paper/sections/03-torus.tex:190-193`.  Before `t_eps = T - eps^2` the packet
  slice is empty and the empty set is such a neighbourhood. -/
  correction_cancels : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) T,
    ∃ O : Set Space, IsOpen O ∧
      tsupport (fun y : Space => scaledPacket P.velocity x₀ T ε (t, y)) ⊆ O ∧
      ∀ x ∈ O, v (t, x) + correction ε (t, x) = 0
  /-- `eq:bgzero`, germ form.  This is what the cross-advection cancellation
  consumes -- "`b_eps = 0`, *including its derivatives*",
  `paper/sections/03-torus.tex:330`, `04-whole-space.tex:51` -- and it is the
  hypothesis shape of `NSFormalization.Source.cross_advection_eq_zero`.  It
  follows from `correction_cancels` because an open set is a neighbourhood of
  each of its points. -/
  correction_cancels_germ : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) T,
    ∀ x ∈ tsupport (fun y : Space => scaledPacket P.velocity x₀ T ε (t, y)),
      ∀ᶠ y in 𝓝 x, v (t, y) + correction ε (t, y) = 0
  /-- The constants of `|d_t^j d_x^beta w_eps| <= C_{beta,j} eps^{-2j-|beta|}`,
  the first bound of `eq:derivativebounds`,
  `paper/sections/03-torus.tex:227-228`.  The constant depends only on the two
  derivative orders (`j` time directions, `m` spatial directions), never on
  `eps`, `03-torus.tex:242`. -/
  correctionDerivConst : ℕ → ℕ → ℝ
  /-- Nonnegativity of the derivative constants. -/
  correctionDerivConst_nonneg : ∀ j m : ℕ, 0 ≤ correctionDerivConst j m
  /-- The mixed derivative bound itself, with `j` unit time directions followed
  by `m` spatial directions of norm at most one,
  `paper/sections/03-torus.tex:227-228`.  The manuscript's `d_x^beta` is the
  case `u i = coordinateVector (beta i)`. -/
  correction_derivative_bound : ∀ j m : ℕ, ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z : SpaceTime,
    ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ (j + m) (correction ε) z
          (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
            (fun i => ((0 : ℝ), u i)))‖
        ≤ correctionDerivConst j m * (ε⁻¹) ^ (2 * j + m)

  -- ### Lemma 3.5, `eq:H`: the correction force
  /-- The family `eps |-> H_eps`, the same family as `eps |-> w_eps`. -/
  forceCorrection : ℝ → VelocityField
  /-- `H_eps = d_t w_eps - nu Laplacian w_eps + (v.grad)w_eps + (w_eps.grad)v +
  (w_eps.grad)w_eps`, the display `eq:H`,
  `paper/sections/03-torus.tex:220-223`.  In Frechet form `(w.grad)v = Dv(w)`
  and `(v.grad)w = Dw(v)`; the third summand below is `(w.grad)v` and the
  fourth is `(v.grad)w`. -/
  force_formula : ∀ ε : ℝ, ∀ t : ℝ, ∀ x : Space,
    forceCorrection ε (t, x) =
      temporalDerivative (correction ε) t x -
        ν • spatialLaplacian (correction ε) t x +
        spatialDerivative v t x (correction ε (t, x)) +
        spatialDerivative (correction ε) t x (v (t, x)) +
        advection (correction ε) t x
  /-- "`H_eps` is smooth across `T` and extends by zero to all times outside
  its cutoff support", `paper/sections/03-torus.tex:225`; "globally smooth ...
  including across `T`", `04-whole-space.tex:51`.  Global `ContDiff` on all of
  spacetime is exactly that statement: there is no seam at `T`. -/
  force_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (forceCorrection ε)
  /-- `H_eps` has compact spacetime support, `paper/sections/03-torus.tex:225`;
  "spacetime compact", `04-whole-space.tex:51`. -/
  force_compactSupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀, HasCompactSupport (forceCorrection ε)
  /-- `supp H_eps` is inside `supp w_eps`, hence inside
  `(T-2eps^2, T+2eps^2) x ball x0 (eps R_*)`,
  `paper/sections/03-torus.tex:225`. -/
  force_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    tsupport (forceCorrection ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ Metric.ball x₀ (ε * θRadius)
  /-- The temporal support of `H_eps` is a compact subset of `(0,infinity)`, so
  the zero extension to nonpositive times is smooth and `g + H_eps` stays in the
  force class, `paper/sections/03-torus.tex:339`,
  `04-whole-space.tex:51`. -/
  force_positive_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z ∈ tsupport (forceCorrection ε),
    0 < z.1
  /-- `g_eps - g` is spatially supported in `B`,
  `paper/sections/04-whole-space.tex:38`. -/
  force_support_ball : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z ∈ tsupport (forceCorrection ε),
    z.2 ∈ Metric.ball x₀ r
  /-- The constant in "its spatial support has volume `O(eps^3)`",
  `paper/sections/03-torus.tex:225`. -/
  spatialVolumeConst : ℝ
  /-- "Its spatial support has volume `O(eps^3)`",
  `paper/sections/03-torus.tex:225`.  The spatial support is the projection of
  the compact spacetime support. -/
  force_spatial_volume : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    volume (Prod.snd '' tsupport (forceCorrection ε)) ≤
      ENNReal.ofReal (spatialVolumeConst * ε ^ 3)
  /-- "Its temporal support has length `O(eps^2)`",
  `paper/sections/03-torus.tex:225`: the projection is contained in an interval
  of length `4 eps^2`. -/
  force_time_length : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    volume (Prod.fst '' tsupport (forceCorrection ε)) ≤ ENNReal.ofReal (4 * ε ^ 2)
  /-- The constants of `|d_x^beta H_eps| <= C_beta eps^{-2-|beta|}`, the second
  bound of `eq:derivativebounds`, `paper/sections/03-torus.tex:229-230`.  The
  constant depends only on `|beta| = m`. -/
  forceDerivConst : ℕ → ℝ
  /-- Nonnegativity of the force derivative constants. -/
  forceDerivConst_nonneg : ∀ m : ℕ, 0 ≤ forceDerivConst m
  /-- The spatial derivative bound itself, over `m` spatial directions of norm
  at most one; `m = 0` is the amplitude bound `|H_eps| <= C eps^{-2}` used at
  `paper/sections/03-torus.tex:281-282` and `04-whole-space.tex:68`. -/
  force_derivative_bound : ∀ m : ℕ, ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z : SpaceTime,
    ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (forceCorrection ε) z (fun i => ((0 : ℝ), u i))‖
        ≤ forceDerivConst m * (ε⁻¹) ^ (2 + m)

  -- ### Lemma 3.5, `eq:wE` and `eq:Hmixed`: the two norm bounds
  /-- The constant `C` of `eq:wE`, `paper/sections/03-torus.tex:234`.  It
  depends on `v` near `(x0,T)`, on `theta, eta` and on `nu`, but not on `eps`
  (`03-torus.tex:242`). -/
  energyConst : ℝ
  /-- Each spatial slice of `w_eps` really lies in `L^2`, so the inner norm of
  `Data.energyEssSup` is the honest Lebesgue norm and not a lower integral.
  Implicit in `eq:Enorm`, `01-introduction.tex:143`. -/
  correction_slice_memLp : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ,
    MemLp (fun x : Space => correction ε (t, x)) 2 volume
  /-- Each spatial slice of the gradient of `w_eps` lies in `L^2`, the same
  statement for the second summand of `eq:Enorm`,
  `01-introduction.tex:145`. -/
  correction_gradient_memLp : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ,
    MemLp (fun x : Space => Data.spatialGradient (correction ε) t x) 2 volume
  /-- `‖w_eps‖_{E_T} <= C eps^{3/2}`, the display `eq:wE`,
  `paper/sections/03-torus.tex:234`, in the canonical `ENNReal`-valued energy
  norm of `Contracts.V1.Data`.  Consumed by `eq:REclose`,
  `04-whole-space.tex:39-41`. -/
  correction_energy_bound : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.energyENorm T (correction ε) ≤ ENNReal.ofReal (energyConst * ε ^ ((3 : ℝ) / 2))
  /-- The constants `C_{p,q}` of `eq:Hmixed`,
  `paper/sections/03-torus.tex:236`. -/
  mixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ
  /-- Each spatial slice of `H_eps` really lies in `L^p`, for every `p`,
  so the inner norm of `Data.mixedLebesgueENorm` is attained by an honest
  `L^p` element. -/
  force_spatial_memLp : ∀ p : ℝ≥0∞, ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ,
    MemLp (fun x : Space => forceCorrection ε (t, x)) p volume
  /-- `‖H_eps‖_{L^q(0,infinity;L^p)} <= C_{p,q} eps^{alpha(p,q)+1}`, the display
  `eq:Hmixed`, `paper/sections/03-torus.tex:235-237`, including both
  essential-supremum endpoints, in the canonical `ENNReal`-valued mixed norm of
  `Contracts.V1.Data`, whose time interval is the manuscript's `(0,infinity)`
  (`01-introduction.tex:140`). -/
  force_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.mixedLebesgueENorm q p (forceCorrection ε) ≤
      ENNReal.ofReal (mixedConst p q * ε ^ (alpha p q + 1))

  -- ### The two extra exports that Theorem 4.2's proof extracts
  /-- `d_t b_eps + (b_eps.grad)b_eps - nu Laplacian b_eps + grad pi = g + H_eps`
  for `b_eps = v + w_eps`, the first display of the insertion proof,
  `paper/sections/03-torus.tex:321-325`, reused at
  `04-whole-space.tex:51`.  Note the pressure: it is the *unchanged* reference
  pressure `pi`.  This is precisely why the pressure difference `p_eps - pi` may
  be taken to be the compact packet representative `P_eps`
  (`04-whole-space.tex:51`, `research/section4/REVIEW.md:77-88`): the background
  correction contributes no pressure at all. -/
  corrected_background : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) (T + δ),
    ∀ x : Space,
      navierStokesResidual ν (fun z => v z + correction ε z) π t x =
        g (t, x) + forceCorrection ε (t, x)
  /-- `u_eps - v = w_eps + U_eps` is divergence free at every presingular time,
  including `t = 0`: `paper/sections/03-torus.tex:332` ("each summand of the
  velocity is divergence free"), `04-whole-space.tex:37-38`.  Theorem 4.7
  consumes this, and `research/section4/REVIEW.md:77-88` records that `R42` must
  export it. -/
  perturbation_divergence_free : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (0 : ℝ) T,
    ∀ x : Space,
      spatialDivergence
        (fun z => correction ε z + scaledPacket P.velocity x₀ T ε z) t x = 0

/-- What `I03` and `R42` receive from `I02`: given a packet, the ambient data of
Theorem 4.2 -- a singular time, a regularity margin, a smooth divergence-free
reference solving the momentum equation on `(0,T+delta) x R^3`, and a nonempty
ball -- the potential, the cutoffs, the correction and the correction force
exist with all the properties above, for the given reference itself and not
merely for some extension of it.  Introducing this definition asserts
nothing. -/
def correctionStatement : Prop :=
  ∀ (ν : ℝ) (P : PacketAPI ν) (T δ r : ℝ) (v : VelocityField) (π : PressureField)
    (g : VelocityField) (x₀ : Space),
    0 < T → 0 < δ → 0 < r →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space)) →
    ContDiffOn ℝ ∞ π (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space)) →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space, spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space,
      navierStokesResidual ν v π t x = g (t, x)) →
    ∃ A : CorrectionAPI ν P,
      A.T = T ∧ A.δ = δ ∧ A.v = v ∧ A.π = π ∧ A.g = g ∧ A.x₀ = x₀ ∧ A.r = r

end BlowupDensity.Contracts.V1
