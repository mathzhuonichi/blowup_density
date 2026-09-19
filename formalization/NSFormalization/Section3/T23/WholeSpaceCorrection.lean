import NSFormalization.Section3.T23.LocalCorrection
import NSFormalization.Section4.D01.SmoothDatum
import NSFormalization.Section3.T24.AffineEnergy
import NSFormalization.Section3.T15.Scaling

/-! Raw-field adapter for the full registered I02 CorrectionAPI.
The registration-side field conversions live in the canonical boundary probe. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement NavierStokes.SpatialCurl
open NavierStokesR3.ProblemStatement (navierStokesResidual)
open NSFormalization.Paper1.RadialPotential (cross)
open NSFormalization.Section3.T15 (alphaT)
open scoped ContDiff ENNReal Topology
structure WholeSpaceCorrectionAPI (ν : ℝ) (u : VelocityField) (K : Set Space) where
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
  `paper/sections/03-torus.tex:181`.

  *Narrowing to record.*  The set the manuscript puts inside the plateau there is
  `K_*` (`03-torus.tex:101-102`), the compact enlargement containing the packet
  carrier `K` **and** the spatial projection of `supp F`.  The set used here is
  `K`, the packet's own `K` (`01-introduction.tex:17-18, 24-25`;
  `I01.packet`).  Nothing in this contract mentions the packet force, and the
  only consumer of the plateau below is `eq:bgzero`, which needs the plateau to
  dominate `supp U_eps(t)` alone -- so `K` is exactly what Lemmas 3.4 and 3.5 use
  here, and this field is correspondingly the weaker hypothesis.  `I03` and `R42`
  must supply the enlargement to `K_*` themselves before they may use the cutoffs
  against `supp F`; `Source/InsertionFamily.lean:218-234` builds it inline. -/
  carrier_subset_plateau : K ⊆ plateau
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
  `03-torus.tex:105`.  It puts the whole cutoff window inside `(0, T+delta)`,
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
          (NSFormalization.Paper1.CorrectionProfile.temporalCutoff η T ε z.1 * NSFormalization.Paper1.CorrectionProfile.spatialCutoff θ x₀ ε y) •
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
      tsupport (fun y : Space => NSFormalization.Section3.T15.scaledVelocity u x₀ T ε (t, y)) ⊆ O ∧
      ∀ x ∈ O, v (t, x) + correction ε (t, x) = 0
  /-- `eq:bgzero`, germ form.  This is what the cross-advection cancellation
  consumes -- "`b_eps = 0`, *including its derivatives*",
  `paper/sections/03-torus.tex:330`, `04-whole-space.tex:51` -- and it is the
  hypothesis shape of `NSFormalization.Source.cross_advection_eq_zero`.  It
  follows from `correction_cancels` because an open set is a neighbourhood of
  each of its points. -/
  correction_cancels_germ : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) T,
    ∀ x ∈ tsupport (fun y : Space => NSFormalization.Section3.T15.scaledVelocity u x₀ T ε (t, y)),
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
    MemLp (fun x : Space => NSFormalization.Section4.I02.spatialGradient (correction ε) t x) 2 volume
  /-- `‖w_eps‖_{E_T} <= C eps^{3/2}`, the display `eq:wE`,
  `paper/sections/03-torus.tex:234`, in the canonical `ENNReal`-valued energy
  norm of `Contracts.V1.Data`.  Consumed by `eq:REclose`,
  `04-whole-space.tex:39-41`. -/
  correction_energy_bound : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    NSFormalization.Section3.T24.energyENorm T (correction ε) ≤ ENNReal.ofReal (energyConst * ε ^ ((3 : ℝ) / 2))
  /-- The constants `C_{p,q}` of `eq:Hmixed`,
  `paper/sections/03-torus.tex:236`. -/
  mixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ
  /-- Each spatial slice of `H_eps` really lies in `L^p`, for every `p`,
  so the inner norm of `NSFormalization.Section3.T15.mixedLebesgueENorm` is attained by an honest
  `L^p` element. -/
  force_spatial_memLp : ∀ p : ℝ≥0∞, ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ,
    MemLp (fun x : Space => forceCorrection ε (t, x)) p volume
  /-- `‖H_eps‖_{L^q(0,infinity;L^p)} <= C_{p,q} eps^{alphaT(p,q)+1}`, the display
  `eq:Hmixed`, `paper/sections/03-torus.tex:235-237`, including both
  essential-supremum endpoints, in the canonical `ENNReal`-valued mixed norm of
  `Contracts.V1.Data`, whose time interval is the manuscript's `(0,infinity)`
  (`01-introduction.tex:140`). -/
  force_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    NSFormalization.Section3.T15.mixedLebesgueENorm q p (forceCorrection ε) ≤
      ENNReal.ofReal (mixedConst p q * ε ^ (alphaT p q + 1))

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
        (fun z => correction ε z + NSFormalization.Section3.T15.scaledVelocity u x₀ T ε z) t x = 0


end NSFormalization.Section3.T23
