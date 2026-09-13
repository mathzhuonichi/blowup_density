/-
# D01 draft A: exact manuscript data, force, norms and pressure (whole space)

Definitions only.  Every declaration below transcribes one displayed object of
the manuscript; the comment above it names the source file and the LaTeX label
or equation number it encodes.  There are no theorems with mathematical
content, no `sorry`, no `axiom`, and no placeholder `Prop` fields.

Conventions fixed once, following `paper/sections/01-introduction.tex`:

* Fourier normalization on `R^3` is the *angular unitary* one,
  `hat z (xi) = (2 pi)^{-3/2} \int e^{-i x . xi} z(x) dx`.
  This is exactly `NSFormalization.Source.angularFourier`, whose integral form
  is proved in `NSFormalization.Source.angularFourier_eq_integral`
  (`formalization/NSFormalization/Source/FourierConvention.lean:27`).
  Mathlib's `𝓕` is the *cycles* transform `e^{-2 pi i x . xi}`; the two differ
  by the dilation `xi \mapsto (2 pi)^{-1} xi` together with the unitary
  amplitude `(2 pi)^{-3/2}`, which is precisely the content of
  `NSFormalization.Paper3.angularFourierDistribution`.  We therefore realize
  every Sobolev datum through `NSFormalization.Paper3.angularRealization`,
  never through the cycles realization, so the weights
  `(1 + |xi|^2)^s` are the manuscript's weights and not rescaled ones.
* All fields are real Euclidean three-vectors.  Reality of a frequency datum is
  the conjugate-reflection symmetry `F(-xi) = conj (F xi)` of
  `paper/sections/02-preliminaries.tex` (paragraph after
  `eq:homogeneous-realization`), which is `NSFormalization.Source.RealSobolev.realSubspace`.
  Vector data carry the Euclidean (`PiLp 2`) norm, matching
  "for vectors and tensors we sum the squared component norms"
  (`paper/sections/01-introduction.tex`).
* Force time norms run over `(0, infinity)`; velocity norms before blowup run
  over `(0, T)` (`paper/sections/01-introduction.tex`, paragraph before
  `eq:Enorm`).
-/
import NSFormalization.Paper3.AngularRealVectorBochner
import NSFormalization.Source.FourierConvention
import NavierStokes.R3.ProblemStatement

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source NSFormalization.Source.RealSobolev
open scoped ContDiff ENNReal SchwartzMap

namespace BlowupDensity.D01.DraftA

/-! ## 1. Field types -/

/-- `paper/sections/01-introduction.tex`, `eq:NS`: the spatial domain is
`D = R^3` with its Euclidean metric.  Reused verbatim as
`NavierStokes.ProblemStatement.Space`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:30`).
A time-independent real vector field on `R^3`, such as the initial velocity
`a` of `eq:NS`. -/
abbrev SpatialField := Space → Space

/-- `paper/sections/01-introduction.tex`, `eq:NS`: a real vector field on
spacetime, time first.  Reused verbatim as
`NavierStokes.ProblemStatement.VelocityField`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:35`);
velocities `u`, forces `f` and their differences all have this type. -/
abbrev SpaceTimeField := VelocityField

/-- `paper/sections/01-introduction.tex`, `eq:NS`: the scalar pressure `p`.
Reused verbatim as `NavierStokes.ProblemStatement.PressureField`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:36`). -/
abbrev SpaceTimeScalar := PressureField

/-- `paper/sections/02-preliminaries.tex`, text after `eq:Rclasses`:
smoothness into `H^\infty` uses *one-sided* time derivatives at zero, so the
time domain of the data classes is the closed half line `[0, infinity)`. -/
abbrev forceTimeDomain : Set ℝ := Ici (0 : ℝ)

/-- `paper/sections/01-introduction.tex`, before `eq:time-norms`:
"Unless an interval is displayed, force norms use `(0, infinity)`."
The Lebesgue measure of that interval is
`NSFormalization.Paper3.positiveTimeMeasure`
(`formalization/NSFormalization/Paper3/PositiveTemporalDensity.lean:11`). -/
abbrev forceTimeMeasure : Measure ℝ := positiveTimeMeasure

/-! ## 2. Angular Sobolev data and their physical pairing

The manuscript identifies an element of `H^s(R^3)` with the `L^2` function
`(1 + |xi|^2)^{s/2} hat z`.  In Lean that datum space is
`NSFormalization.Paper3.SobolevHilbert s = Lp ℂ 2 volume`, its real subspace is
`NSFormalization.Source.RealSobolev.RealSobolevHilbert s`, and the Euclidean
three-vector version is `NSFormalization.Paper3.RealVectorSobolev s`
(`formalization/NSFormalization/Paper3/RealVectorPositiveDensity.lean:15`).
`angularRealization s` turns such a datum into the tempered distribution it
represents, in the manuscript's angular normalization. -/

/-- `paper/sections/01-introduction.tex`, displayed definition of `H^s(R^3)`,
together with `paper/sections/02-preliminaries.tex`, `eq:Rinitial`:
`A` is *the* order-`s` angular Sobolev datum of the real physical vector field
`z`, in the sense that its realization pairs with every Schwartz test exactly
as `z` does.  This is the pairing used by
`NSFormalization.Paper3.angularRealVectorSlice_pairing`
(`formalization/NSFormalization/Paper3/AngularRealVectorBochner.lean:54`). -/
def IsAngularDatum (s : ℝ) (z : SpatialField) (A : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s (A i : FourierData) ψ = ∫ x : Space, ψ x * (z x i : ℂ)

/-- `paper/sections/02-preliminaries.tex`, `eq:Rclasses`, and
`paper/sections/01-introduction.tex`, displayed definition of `H^s(R^3)`:
`G` is the order-`s` angular Sobolev trajectory of the space-time field `f`,
recorded on the closed half line `[0, infinity)` of `eq:Rclasses`. -/
def IsAngularPath (s : ℝ) (f : SpaceTimeField) (G : ℝ → RealVectorSobolev s) : Prop :=
  ∀ t : ℝ, 0 ≤ t → IsAngularDatum s (fun x => f (t, x)) (G t)

/-! ## 3. The datum class `X_R` -/

/-- `paper/sections/02-preliminaries.tex`, `eq:Rinitial`:
`X_R = H^\infty(R^3; R^3) \cap L^2_\sigma(R^3)`.

* `smooth` and `sobolev` express `a \in H^\infty = \bigcap_m H^m`: for every
  integer order `m` there is a real Euclidean-vector angular Sobolev datum
  representing `a`.  Membership in `L^2` is the case `m = 0`.
* `divergence_free` is the solenoidal condition of `L^2_\sigma`; for the smooth
  fields of this class it is the pointwise Euclidean divergence, written
  exactly as in `NSFormalization.Paper1.PeriodicInitialData.IsAdmissibleInitialData`
  (`formalization/NSFormalization/Paper1/PeriodicInitialData.lean:21`).

No Frechet topology is attached here; `eq:Rinitial` only fixes the set. -/
structure MemDatumR (a : SpatialField) : Prop where
  smooth : ContDiff ℝ ∞ a
  sobolev : ∀ m : ℕ, ∃ A : RealVectorSobolev (m : ℝ), IsAngularDatum (m : ℝ) a A
  divergence_free : ∀ x : Space, (∑ i : Fin 3, (fderiv ℝ a x (coordinateVector i)) i) = 0

/-- `paper/sections/02-preliminaries.tex`, `eq:Rinitial`: the set `X_R` itself. -/
def datumClassR : Set SpatialField := {a | MemDatumR a}

/-! ## 4. The force class `F_R` -/

/-- `paper/sections/02-preliminaries.tex`, `eq:Rclasses`:
`F_R = \{ f \in C^\infty([0,\infty); H^\infty) :
  \|f\|_{L^1_t H^m_x} + \|f\|_{L^2_t H^m_x} < \infty` for every integer
`m \ge 0 \}`.

For each integer order `m` the field `f` has an angular Sobolev trajectory `G`
which is

* `path`: the order-`m` trajectory of `f` on `[0, infinity)`;
* `smooth`: `C^\infty` into `H^m` with one-sided derivatives at `t = 0`
  (`ContDiffOn ... (Ici 0)`), which is the manuscript's reading of
  "smoothness into `H^\infty` means smoothness into each `H^m`, with one-sided
  time derivatives at zero";
* `l1`, `l2`: finiteness of `\|f\|_{L^1_t H^m_x}` and `\|f\|_{L^2_t H^m_x}`
  over the whole time axis `(0, infinity)`.

Reality of the frequency data is automatic, because `RealVectorSobolev` is the
conjugate-reflection-symmetric subspace.  This is the manuscript-faithful
counterpart of `NSFormalization.Paper3.RealAdmissibleForce`
(`formalization/NSFormalization/Paper3/RealAdmissibleForce.lean:15`), with the
supremum `Pi` norm replaced by the Euclidean `PiLp 2` norm, the cycles
realization replaced by the angular one, and the abstract distribution target
replaced by the physical field. -/
def MemForceR (f : SpaceTimeField) : Prop :=
  ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    IsAngularPath (m : ℝ) f G ∧
    ContDiffOn ℝ ∞ G (Ici (0 : ℝ)) ∧
    MemLp G 1 forceTimeMeasure ∧
    MemLp G 2 forceTimeMeasure

/-- `paper/sections/02-preliminaries.tex`, `eq:Rclasses`: the set `F_R`. -/
def forceClassR : Set SpaceTimeField := {f | MemForceR f}

/-- `paper/sections/04-whole-space.tex`, Section 4.5, definition of
`F_c = C_c^\infty(R^3 \times (0,\infty); R^3)`: smooth space-time fields whose
support is compact and contained in strictly positive time.  This is the class
in which the insertion correction `g_\eps - g` of Theorem `thm:Rinsert` lives.
The support predicate is `NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport`
(`vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:66`). -/
def MemForceCompactR (f : SpaceTimeField) : Prop :=
  ContDiff ℝ ∞ f ∧ NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f

/-! ## 5. Norms -/

/-- `paper/sections/01-introduction.tex`, displayed formula for
`\|z\|_{H^s(R^3)}^2 = \int (1+|xi|^2)^s |hat z(xi)|^2 d xi`, in the angular
normalization, summed over the three real components
("for vectors and tensors we sum the squared component norms").
The scalar summand is `NSFormalization.Source.angularSobolevSq`
(`formalization/NSFormalization/Source/FourierConvention.lean:44`). -/
def angularVectorSobolevSq (s : ℝ) (z : SpatialField) : ℝ :=
  ∑ i : Fin 3, angularSobolevSq s (fun x => (z x i : ℂ))

/-- `paper/sections/01-introduction.tex`, displayed formula for
`\|z\|_{H^s(R^3)}`: the square root of `angularVectorSobolevSq`. -/
def angularVectorSobolevNorm (s : ℝ) (z : SpatialField) : ℝ :=
  Real.sqrt (angularVectorSobolevSq s z)

/-- `paper/sections/01-introduction.tex`, `eq:time-norms` with `I = (0,\infty)`
and `X = H^s(R^3)`, written directly on the physical field:
`\|f\|_{L^q_t H^s_x} = (\int_0^\infty \|f(t)\|_{H^s}^q dt)^{1/q}`.
This is the form in which the scaling estimates `eq:RpositiveScale` and
`eq:RnegativeScale` of `paper/sections/04-whole-space.tex` are stated.  The
Lebesgue integral is taken in `[0, \infty]` so that no integrability side
condition is built into the definition. -/
def forcePhysicalTimeNorm (q s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (angularVectorSobolevNorm s (fun x => f (t, x)) ^ q)) ^ (1 / q)

/-- `paper/sections/01-introduction.tex`, `eq:time-norms` together with the
Bochner-space footnote (Hunter, Definitions 6.14 and 6.27):
`L^q(0,\infty; H^s(R^3))` is the space of strongly measurable Sobolev-valued
time paths with finite norm.  On the angular Sobolev data this is exactly
Mathlib's `eLpNorm` for the measure `positiveTimeMeasure`, which is the norm
already used by
`NSFormalization.Paper3.exists_angular_real_vector_positive_physical_approx`
(`formalization/NSFormalization/Paper3/AngularRealVectorBochner.lean:120`).
`q = 1` and `q = 2` are the two cases of Theorem `thm:Rmain`. -/
def forceBochnerNorm (q : ℝ≥0∞) (s : ℝ) (G : ℝ → RealVectorSobolev s) : ℝ≥0∞ :=
  eLpNorm G q forceTimeMeasure

/-- `paper/sections/01-introduction.tex`, `L^1_t H^s_x`: the `q = 1` case. -/
def forceBochnerNormL1 (s : ℝ) (G : ℝ → RealVectorSobolev s) : ℝ≥0∞ :=
  forceBochnerNorm 1 s G

/-- `paper/sections/01-introduction.tex`, `L^2_t H^s_x`: the `q = 2` case. -/
def forceBochnerNormL2 (s : ℝ) (G : ℝ → RealVectorSobolev s) : ℝ≥0∞ :=
  forceBochnerNorm 2 s G

/-- `paper/sections/04-whole-space.tex`, Theorem `thm:Rmain`:
`s_q = 2/q - 3/2`, the Sobolev threshold for the time exponent `q`.
The already registered `NSFormalization.Paper3.forceExponent`
(`formalization/NSFormalization/Paper3/Thresholds.lean:12`) is
`beta(q,s) = criticalOrder q - s`. -/
def criticalOrder (q : ℝ) : ℝ := 2 / q - 3 / 2

/-! ### Homogeneous realizations -/

/-- `paper/sections/01-introduction.tex`, definition of the homogeneous norm
("the homogeneous norm `\dot H^s` replaces the weights above by `|xi|^{2s}`"),
in the angular normalization and summed over the three real components. -/
def angularVectorHomogeneousSq (s : ℝ) (z : SpatialField) : ℝ :=
  ∑ i : Fin 3, ∫ ξ : Space, ‖ξ‖ ^ (2 * s) * ‖angularFourier (fun x => (z x i : ℂ)) ξ‖ ^ 2

/-- `paper/sections/01-introduction.tex`, definition of `\|z\|_{\dot H^s}`.
Compare `NSFormalization.Source.homogeneousFourierNorm`
(`formalization/NSFormalization/Source/TimeNormScaling.lean:68`), which is the
same quantity in Mathlib's cycles normalization. -/
def angularVectorHomogeneousNorm (s : ℝ) (z : SpatialField) : ℝ :=
  Real.sqrt (angularVectorHomogeneousSq s z)

/-- `paper/sections/02-preliminaries.tex`, `eq:homogeneous-realization`:
`\dot H^{-1}(R^3) = \{ h \in S' : hat h = F` is a measurable function and
`|xi|^{-1} F \in L^2 \}`, together with the sentence "its inverse sends `G` to
the inverse transform of `|xi| G`, which is tempered because
`|\int |xi| G phi| \le \|G\|_2 \||xi| phi\|_2`".

`G` is the `L^2` datum `|xi|^{-1} hat h`; the pairing below is exactly the
displayed temperedness estimate, evaluated on the angular Fourier transform of
`h`.  It is a genuine Bochner integral: `psi` is Schwartz, so `xi \mapsto
|xi| psi(xi)` is in `L^2`, and the product with `G \in L^2` is integrable. -/
def IsHomogeneousNegOneDatum (G : FourierData) (U : 𝓢'(Space, ℂ)) : Prop :=
  ∀ ψ : SchwartzMap Space ℂ,
    angularFourierDistribution U ψ = ∫ ξ : Space, ψ ξ * ((‖ξ‖ : ℝ) : ℂ) * G ξ

/-- `paper/sections/02-preliminaries.tex`, `eq:homogeneous-realization`:
membership in the fixed realization of `\dot H^{-1}(R^3)`. -/
def MemHomogeneousNegOne (U : 𝓢'(Space, ℂ)) : Prop :=
  ∃ G : FourierData, IsHomogeneousNegOneDatum G U

/-- `paper/sections/02-preliminaries.tex`, after `eq:homogeneous-realization`:
"The map `h \mapsto |xi|^{-1} hat h` is an isometric bijection onto `L^2`", so
the `\dot H^{-1}` norm of `h` is the `L^2` norm of its datum. -/
def homogeneousNegOneNorm (G : FourierData) : ℝ := ‖G‖

/-- `paper/sections/02-preliminaries.tex`, last paragraph:
"Real vector fields correspond to the closed subspace with
`F(-xi) = \overline{F(xi)}`."  This is
`NSFormalization.Source.RealSobolev.realSubspace`
(`formalization/NSFormalization/Source/RealSobolev.lean:118`), whose membership
is the conjugate-reflection identity `realSymmetry G = G`. -/
def IsRealFrequencyDatum (G : FourierData) : Prop := realSymmetry G = G

/-! ### The energy norm `E_T` -/

/-- `paper/sections/01-introduction.tex`, `eq:Enorm`, first summand:
`\|z\|_{L^\infty(0,T;L^2(R^3))}`. -/
def energyEssSup (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  essSup (fun t => eLpNorm (fun x => z (t, x)) 2 volume) (volume.restrict (Ioo (0 : ℝ) T))

/-- `paper/sections/01-introduction.tex`, `eq:Enorm`: the spatial gradient of a
space-time field at a fixed time, assembled as the Euclidean vector of its
three coordinate derivatives, so that its norm is
`(\sum_i |\partial_i z|^2)^{1/2}` and `\|\nabla z\|_2` is the manuscript's
Hilbert-Schmidt gradient norm rather than an operator norm.
`spatialDerivative` and `coordinateVector` are reused from
`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:59,39`. -/
def spatialGradient (z : SpaceTimeField) (t : ℝ) (x : Space) : WithLp 2 (Fin 3 → Space) :=
  WithLp.toLp 2 (fun i => spatialDerivative z t x (coordinateVector i))

/-- `paper/sections/01-introduction.tex`, `eq:Enorm`, second summand:
`\|\nabla z\|_{L^2(0,T;L^2(R^3))}`. -/
def energyGradient (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T, (eLpNorm (fun x => spatialGradient z t x) 2 volume) ^ (2 : ℝ))
    ^ (1 / 2 : ℝ)

/-- `paper/sections/01-introduction.tex`, `eq:Enorm`:
`\|z\|_{E_T} = \|z\|_{L^\infty(0,T;L^2)} + \|\nabla z\|_{L^2(0,T;L^2)}`.
It imposes no endpoint value at `T`. -/
def energyNorm (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  energyEssSup T z + energyGradient T z

/-! ## 6. Classical solutions and pressure -/

/-- `paper/sections/02-preliminaries.tex`, Section 2.3, after `eq:Rpressure`:
"the scalar pressure is determined up to a function of time".  Two pressure
fields are the same solution datum on `[0,T)` when they differ by a function of
time alone. -/
def PressureGaugeEquiv (T : ℝ) (p q : SpaceTimeScalar) : Prop :=
  ∃ c : ℝ → ℝ, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, q (t, x) = p (t, x) + c t

/-- `paper/sections/02-preliminaries.tex`, Section 2.3, displayed potential
`p(x,t) = \int_0^1 G(rx,t) \cdot x \, dr` for the prescribed pressure gradient
`G` of `eq:Rpressure`.  This is the manuscript's explicit choice of
representative inside a `PressureGaugeEquiv` class. -/
def radialPressurePotential (G : SpaceTimeField) : SpaceTimeScalar :=
  fun z => ∫ r in (0 : ℝ)..1, (inner ℝ (G (z.1, r • z.2)) z.2 : ℝ)

/-- `paper/sections/02-preliminaries.tex`, Section 2.1 (whole-space classical
solution) together with Proposition `prop:local` and
`paper/sections/04-whole-space.tex`, Theorem `thm:Rinsert`.

A classical solution `(u,p)` on `[0,T)` for viscosity `nu`, initial velocity
`a` and force `f`:

* `velocity_smooth`, `pressure_smooth`: smooth on the closed-at-zero slab
  `[0,T) x R^3`, so all time derivatives at `t = 0` are one-sided.  No
  extension to negative time is differentiated.
* `initial`: `u(\cdot,0) = a` of `eq:NS`.
* `divergence`: `\nabla \cdot u = 0` on `[0,T)`.
* `equation`: the momentum equation of `eq:NS` at interior times, using
  `NavierStokesR3.ProblemStatement.navierStokesResidual`
  (`vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:57`),
  in which the viscosity multiplies only the spatial Laplacian.
* `sobolev`: "a classical velocity belongs to `C([0,S];H^m)` for every integer
  `m \ge 0` on each compact interval of its lifespan"
  (`paper/sections/02-preliminaries.tex`, Section 2.1).
* `pressure_gradient`: `eq:Rpressure` fixes `\nabla p` and the following
  paragraph states "There is no requirement that `p \in L^2(R^3)`.  Its
  gradient belongs to `L^2`, so a nonzero constant pressure gradient is
  excluded."  Only the gradient is constrained, so the scalar pressure is
  determined exactly up to `PressureGaugeEquiv`.

Compare `NSFormalization.Source.SmoothLifespan.Flow`
(`formalization/NSFormalization/Source/SmoothLifespan.lean:23`), which uses
uniform pointwise velocity and derivative bounds and a finite-energy predicate
instead of the all-order Sobolev path and the `L^2` pressure gradient. -/
structure ClassicalSolutionR (ν T : ℝ) (a : SpatialField) (f : SpaceTimeField) where
  velocity : SpaceTimeField
  pressure : SpaceTimeScalar
  horizon_pos : 0 < T
  velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  pressure_smooth : ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  initial : ∀ x : Space, velocity (0, x) = a x
  divergence : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 0
  equation : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)
  sobolev : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    ContinuousOn G (Ico (0 : ℝ) T) ∧
      ∀ t ∈ Ico (0 : ℝ) T, IsAngularDatum (m : ℝ) (fun x => velocity (t, x)) (G t)
  pressure_gradient : ∀ t ∈ Ico (0 : ℝ) T,
    MemLp (fun x : Space => pressureGradient pressure t x) 2 volume

/-! ## 7. Maximal lifespan, breakdown sets, density -/

/-- `paper/sections/02-preliminaries.tex`, Section 2.1: "local uniqueness
defines a maximal classical lifespan, denoted by `T^\nu_{\max,R}(a,f)` on the
whole space"; it is used in `paper/sections/04-whole-space.tex`,
Theorems `thm:Rmain` and `thm:Rinsert` and Propositions `prop:Rcritical1`,
`prop:Rcritical2`.  Following
`NSFormalization.Source.SmoothLifespan.lifespan`
(`formalization/NSFormalization/Source/SmoothLifespan.lean:41`), it is the
supremum of the horizons carrying a classical solution, valued in `[0, \infty]`
so that global regularity is `\infty`.  The empty supremum is zero. -/
def maximalLifespanR (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨆ T : ℝ, ⨆ _ : Nonempty (ClassicalSolutionR ν T a f), ENNReal.ofReal T

/-- `paper/sections/02-preliminaries.tex`, Section 2.1: a reference solution is
*regular through* `T` if it extends smoothly to `[0, T+\delta]` for some
`\delta > 0`.  This is the hypothesis of `paper/sections/04-whole-space.tex`,
Theorem `thm:Rinsert`. -/
def RegularThrough (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionR ν (T + δ) a f)

/-- `paper/sections/02-preliminaries.tex`, `eq:Rsingularforces`:
`B^R_{\nu,a,T} = \{ f \in F_R : T^\nu_{\max,R}(a,f) \le T \}`, the forces
producing classical breakdown by `T`. -/
def breakdownSetR (ν : ℝ) (a : SpatialField) (T : ℝ) : Set SpaceTimeField :=
  {f | MemForceR f ∧ maximalLifespanR ν a f ≤ ENNReal.ofReal T}

/-- `paper/sections/02-preliminaries.tex`, `eq:Rsingularforces`:
`B^{R,0}_{\nu,T} = B^R_{\nu,0,T}`, breakdown from rest, used in
`paper/sections/04-whole-space.tex`, Theorem `thm:Rmain` (ii). -/
def breakdownSetRZero (ν T : ℝ) : Set SpaceTimeField :=
  breakdownSetR ν (fun _ => 0) T

/-- `paper/sections/04-whole-space.tex`, Theorem `thm:Rmain`, clauses (i) and
(ii): density "in the relative `L^q(0,\infty;H^s(R^3))` topology on `F_R`".
Membership in the relative topology means: every member `g` of `F_R` and every
positive radius admit a member `f` of `B` whose difference from `g` has
`L^q_t H^s_x` norm below that radius.  This is exactly how the proof of
`thm:Rmain` begins ("Fix `a,g` and a positive radius in the indicated force
norm").  The difference `f - g` is required to have an order-`s` angular
Sobolev trajectory, which is the sense in which its Bochner norm is measured;
that trajectory is unique when it exists, since `angularRealization` is
injective. -/
def RelativelyDenseInForceR (q : ℝ≥0∞) (s : ℝ) (B : Set SpaceTimeField) : Prop :=
  ∀ g : SpaceTimeField, MemForceR g → ∀ r : ℝ≥0∞, 0 < r →
    ∃ f ∈ B, ∃ D : ℝ → RealVectorSobolev s,
      IsAngularPath s (f - g) D ∧ forceBochnerNorm q s D < r

/-- `paper/sections/04-whole-space.tex`, Theorem `thm:Rmain`, clause (i),
instantiated at the breakdown set: the exact predicate asserted for every
`a \in X_R` when `s < s_q`. -/
def BreakdownDenseR (ν : ℝ) (a : SpatialField) (T : ℝ) (q : ℝ≥0∞) (s : ℝ) : Prop :=
  RelativelyDenseInForceR q s (breakdownSetR ν a T)

end BlowupDensity.D01.DraftA
