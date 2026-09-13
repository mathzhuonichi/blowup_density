import NSFormalization.Paper3.AngularRealVectorBochner
import NSFormalization.Paper3.RealAdmissibleForce
import NSFormalization.Paper3.HomogeneousRealization
import NSFormalization.Paper3.GridGeometry
import NSFormalization.Source.AngularForceNorms
import NavierStokes.R3.CompactEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# D01 draft B: exact manuscript data, force, norms and pressure on `R³`

Definitions only.  Every declaration carries the manuscript location it
encodes.  No theorem with mathematical content, no `sorry`, no `axiom`, and no
placeholder `Prop` field occurs in this file.

## Fourier normalization

`01-introduction.tex` fixes, on the whole space,

  `ẑ(ξ) = (2π)^(-3/2) ∫ exp(-i x·ξ) z(x) dx`,
  `‖z‖²_{H^s(R³)} = ∫ (1 + |ξ|²)^s |ẑ(ξ)|² dξ`,

the *unitary angular-frequency* convention.  Mathlib's `𝓕` is the
cycles-per-unit-length transform `∫ exp(-2πi x·ξ) z(x) dx`, so the two differ
by the dilation `ξ ↦ ξ/(2π)` together with the amplitude `(2π)^{-3/2}`.  That
exact change of normalization is already formalized:
`NSFormalization.Source.angularFourier`
(`formalization/NSFormalization/Source/FourierConvention.lean:23`) is literally
the displayed integral, and
`NSFormalization.Paper3.angularFourierDistribution`
(`formalization/NSFormalization/Paper3/AngularFourierDilation.lean:172`)
is its tempered-distribution extension.  Consequently
`NSFormalization.Paper3.angularRealization s : L²(R³;ℂ) → 𝓢'(R³;ℂ)` realizes an
`L²` *datum* `l` as the distribution whose weighted angular transform is `l`,
and `‖l‖_{L²}` is exactly the manuscript `H^s` norm
(`norm_angularDatum`, `AngularFourierDilation.lean:228`).  Every Sobolev
quantity below is expressed through `angularRealization`, hence in the
manuscript's normalization and *not* in Mathlib's.

Reality is the conjugate-reflection symmetry `F(-ξ) = conj (F ξ)` of the datum
(`02-preliminaries.tex`, end of §2.2), i.e. membership in
`NSFormalization.Source.RealSobolev.realSubspace`.  Vector fields use the
Euclidean sum of squared component norms (`01-introduction.tex`, "For vectors
and tensors we sum the squared component norms"), i.e. the `PiLp 2` product
`NSFormalization.Paper3.RealVectorSobolev`.
-/

noncomputable section

namespace BlowupDensity.D01.DraftB

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev (FourierData RealSobolevHilbert realSubspace)
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. Field types

`01-introduction.tex`, equation `eq:NS`: the fields are real and
three-dimensional, on `D = R³`, with time first in spacetime. -/

/-- `01-introduction.tex` eq:NS. A time-independent real 3-vector field on `R³`
(initial velocities, spatial slices).  Reuses `ProblemStatement.Space`. -/
abbrev SpatialField := Space → Space

/-- `01-introduction.tex` eq:NS. A real 3-vector field on `R³ × ℝ`, time first.
Reuses `ProblemStatement.VelocityField`; velocities, forces and corrections all
live here. -/
abbrev SpaceTimeField := VelocityField

/-- `01-introduction.tex` eq:NS. A real scalar spacetime field (pressure).
Reuses `ProblemStatement.PressureField`. -/
abbrev SpaceTimeScalar := PressureField

/-! ## 2. Sobolev data in the manuscript's angular normalization -/

/-- `01-introduction.tex`, definition of `H^s(R³)`.  The manuscript's *datum*
at order `s` is the weighted angular Fourier transform `(1+|ξ|²)^{s/2} ẑ`, an
element of `L²(R³;ℂ)`; the physical distribution is `angularRealization s`. -/
abbrev AngularDatum (_s : ℝ) := FourierData

/-- `02-preliminaries.tex` §2.2, "Real vector fields correspond to the closed
subspace with `F(-ξ) = conj (F ξ)`". -/
abbrev RealAngularDatum (s : ℝ) := RealSobolevHilbert s

/-- `01-introduction.tex`, "For vectors and tensors we sum the squared
component norms": the Euclidean (`PiLp 2`) product of three real scalar data. -/
abbrev RealVectorAngularDatum (s : ℝ) := RealVectorSobolev s

/-- `01-introduction.tex`, `H^s(R³)`: the physical tempered-distribution
components realized by a real Euclidean vector datum of order `s`. -/
def angularVectorRealization (s : ℝ) (G : RealVectorSobolev s) : ForceDistribution :=
  fun i => angularRealization s ((G i : FourierData))

/-! ## 3. The norms `‖·‖_{H^s(R³)}` and `‖·‖_{L^q(0,∞;H^s(R³))}` -/

/-- `01-introduction.tex`, `‖z‖²_{H^s(R³)} = ∫ (1+|ξ|²)^s |ẑ(ξ)|² dξ`, in the
angular normalization.  Total: the value is `⊤` exactly when the tempered
distribution `u` does not lie in `H^s`, and otherwise the norm of its unique
angular datum (uniqueness is `MemAngularSobolev.exists_unique_datum`). -/
def sobolevENorm (s : ℝ) (u : 𝓢'(Space, ℂ)) : ℝ≥0∞ :=
  ⨅ l : {l : FourierData // angularRealization s l = u}, ‖l.1‖ₑ

/-- `01-introduction.tex`, "For vectors and tensors we sum the squared component
norms". -/
def vectorSobolevENorm (s : ℝ) (U : ForceDistribution) : ℝ≥0∞ :=
  (∑ i : Fin 3, sobolevENorm s (U i) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `01-introduction.tex` eq:time-norms with `I = (0,∞)` (the manuscript's
default force interval): `‖f‖_{L^q(0,∞;H^s(R³))}`.  The time measure is the
already available `positiveTimeMeasure = volume.restrict (Ioi 0)`. -/
def bochnerSobolevENorm (q s : ℝ) (g : ℝ → ForceDistribution) : ℝ≥0∞ :=
  (∫⁻ t, vectorSobolevENorm s (g t) ^ q ∂positiveTimeMeasure) ^ q⁻¹

/-- `01-introduction.tex`, `L¹_t H^s_x`; the `q = 1` threshold case of
`thm:Rmain`. -/
abbrev l1SobolevENorm (s : ℝ) (g : ℝ → ForceDistribution) : ℝ≥0∞ :=
  bochnerSobolevENorm 1 s g

/-- `01-introduction.tex`, `L²_t H^s_x`; the `q = 2` threshold case of
`thm:Rmain`. -/
abbrev l2SobolevENorm (s : ℝ) (g : ℝ → ForceDistribution) : ℝ≥0∞ :=
  bochnerSobolevENorm 2 s g

/-- `01-introduction.tex`, `‖·‖_{H^s(R³)}` evaluated slicewise on a *physical*
real vector field, reusing `Source.vectorAngularSobolevNorm`.  This is the form
in which the insertion estimates `eq:RpositiveScale`, `eq:RnegativeScale` are
already proved for compactly supported smooth profiles. -/
abbrev physicalSobolevNorm (s : ℝ) (F : VelocityField) (t : ℝ) : ℝ :=
  NSFormalization.Source.vectorAngularSobolevNorm s F t

/-- `01-introduction.tex` eq:time-norms on `(0,∞)`, physical slicewise form. -/
def physicalBochnerENorm (q : ℝ≥0∞) (s : ℝ) (F : VelocityField) : ℝ≥0∞ :=
  eLpNorm (physicalSobolevNorm s F) q positiveTimeMeasure

/-! ## 4. The homogeneous realization -/

/-- `02-preliminaries.tex` eq:homogeneous-realization, and its
`appendix-b-embeddings.tex` counterpart at positive orders: `u ∈ Ḣ^s` iff the
angular Fourier transform of `u` is the measurable function `|ξ|^{-s} G` for
some `G ∈ L²`.  At `s = -1` this is literally the displayed set
`{h ∈ 𝓢' : ĥ = F measurable and |ξ|^{-1} F ∈ L²}`; at `s = a ∈ (0,3/2)` it is
the completion realization `v̂ = |ξ|^{-a} G` of Appendix B. -/
def MemHomogeneous (s : ℝ) (u : 𝓢'(Space, ℂ)) : Prop :=
  ∃ G : FourierData, ∀ φ : SchwartzMap Space ℂ,
    angularFourierDistribution u φ = ∫ ξ : Space, φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ)

/-- `02-preliminaries.tex` eq:homogeneous-realization: `h ↦ |ξ|^{-s} ĥ` is an
isometric bijection onto `L²`, so `‖h‖_{Ḣ^s} = ‖G‖_{L²}`.  Total: `⊤` off the
space. -/
def homogeneousENorm (s : ℝ) (u : 𝓢'(Space, ℂ)) : ℝ≥0∞ :=
  ⨅ G : {G : FourierData // ∀ φ : SchwartzMap Space ℂ,
      angularFourierDistribution u φ =
        ∫ ξ : Space, φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ)}, ‖G.1‖ₑ

/-- `02-preliminaries.tex` eq:homogeneous-realization: the completed
energy-force space `Ḣ^{-1}(R³)`. -/
abbrev MemDotHNegOne (u : 𝓢'(Space, ℂ)) : Prop := MemHomogeneous (-1) u

/-- `02-preliminaries.tex` eq:homogeneous-realization, vector form (Euclidean
sum of squared component norms). -/
def vectorHomogeneousENorm (s : ℝ) (U : ForceDistribution) : ℝ≥0∞ :=
  (∑ i : Fin 3, homogeneousENorm s (U i) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `04-whole-space.tex` prop:Renergy: the space `L²(0,∞;Ḣ^{-1}(R³))` and, more
generally, `L^q_t Ḣ^s_x`. -/
def bochnerHomogeneousENorm (q s : ℝ) (g : ℝ → ForceDistribution) : ℝ≥0∞ :=
  (∫⁻ t, vectorHomogeneousENorm s (g t) ^ q ∂positiveTimeMeasure) ^ q⁻¹

/-! ## 5. The initial-velocity class `X_R` -/

/-- `02-preliminaries.tex` eq:Rinitial, the factor `H^∞(R³;R³) = ⋂_m H^m`.
Membership in every integer-order `H^m` for a field that is (equivalently, by
Sobolev embedding) smooth is exactly square integrability of every iterated
Fréchet derivative.  These are field-for-field the hypotheses of
`EulerLpTranslation.SmoothL2Field Space`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31`). -/
def MemHInfty (a : Space → Space) : Prop :=
  ContDiff ℝ ∞ a ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n a) 2 volume

/-- `02-preliminaries.tex` eq:Rinitial, the factor `L²_σ(R³)`: the classical
divergence vanishes identically.  Reuses `ProblemStatement.spatialDivergence`
on the time-independent lift of `a`. -/
def IsSolenoidal (a : Space → Space) : Prop :=
  ∀ x : Space, spatialDivergence (fun z : SpaceTime => a z.2) 0 x = 0

/-- `02-preliminaries.tex` eq:Rinitial:
`X_R = H^∞(R³;R³) ∩ L²_σ(R³)`. -/
def XR : Set (Space → Space) := {a | MemHInfty a ∧ IsSolenoidal a}

/-- `04-whole-space.tex` §4.6: `S_σ = 𝓢(R³;R³) ∩ L²_σ`, the initial class of
the rapid-decay formulation used by `cor:Rclasses`. -/
def SchwartzSolenoidal : Set (Space → Space) :=
  {a | (∃ φ : SchwartzMap Space Space, ⇑φ = a) ∧ IsSolenoidal a}

/-! ## 6. The force class `F_R` -/

/-- The angular Euclidean real-vector datum `G` of order `s` represents the
physical real field `F`.  The pairing is the one already proved for compact
smooth slices in `angularRealVectorSlice_pairing`
(`formalization/NSFormalization/Paper3/AngularRealVectorBochner.lean:54`). -/
def RepresentsSlice (s : ℝ) (G : RealVectorSobolev s) (F : Space → Space) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((G i : FourierData)) ψ = ∫ x : Space, ψ x * ((F x i : ℝ) : ℂ)

/-- `02-preliminaries.tex` eq:Rclasses,
`F_R = {f ∈ C^∞([0,∞);H^∞) : ‖f‖_{L¹_t H^m_x} + ‖f‖_{L²_t H^m_x} < ∞ for every
integer m ≥ 0}`, in physical form together with its exact angular Euclidean
real-vector data at every integer order.  `ContDiffOn ℝ ∞ (datum m) (Ici 0)` is
the manuscript's "smoothness into each `H^m`, with one-sided time derivatives at
zero"; `MemLp _ 1` and `MemLp _ 2` over `positiveTimeMeasure` are the two
finiteness requirements on `(0,∞)`.  No compact support and no vanishing near
`t = 0` is imposed, as the manuscript stresses for the whole-space class. -/
structure ForceR where
  /-- The physical force `f : R³ × [0,∞) → R³` (zero-extended in `t`). -/
  field : VelocityField
  /-- Joint smoothness on the closed half-space `[0,∞) × R³`. -/
  smooth : ContDiffOn ℝ ∞ field futureDomain
  /-- The angular Euclidean real-vector `H^m` datum at each integer order. -/
  datum : (m : ℕ) → ℝ → RealVectorSobolev (m : ℝ)
  /-- The datum realizes the physical field at every nonnegative time. -/
  datum_represents : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
    RepresentsSlice (m : ℝ) (datum m t) (fun x => field (t, x))
  /-- `C^∞([0,∞);H^m)`, one-sided at `t = 0`. -/
  datum_contDiffOn : ∀ m : ℕ, ContDiffOn ℝ ∞ (datum m) (Ici 0)
  /-- `‖f‖_{L¹(0,∞;H^m)} < ∞`. -/
  datum_memL1 : ∀ m : ℕ, MemLp (datum m) 1 positiveTimeMeasure
  /-- `‖f‖_{L²(0,∞;H^m)} < ∞`. -/
  datum_memL2 : ∀ m : ℕ, MemLp (datum m) 2 positiveTimeMeasure

/-- `02-preliminaries.tex` eq:Rclasses, purely distributional form: the same
class stated for a time path of tempered-distribution triples, with reality
built into `RealVectorSobolev` and the manuscript's angular normalization built
into `angularVectorRealization`. -/
def MemForceR (g : ℝ → ForceDistribution) : Prop :=
  ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    (∀ t : ℝ, 0 ≤ t → angularVectorRealization (m : ℝ) (G t) = g t) ∧
    ContDiffOn ℝ ∞ G (Ici 0) ∧
    MemLp G 1 positiveTimeMeasure ∧ MemLp G 2 positiveTimeMeasure

/-- The tempered-distribution time path of a member of `F_R`; the realization
is order-independent, so order `0` is a canonical choice. -/
def ForceR.toDistribution (f : ForceR) : ℝ → ForceDistribution :=
  fun t => angularVectorRealization ((0 : ℕ) : ℝ) (f.datum 0 t)

/-- `04-whole-space.tex` §4.6: `F_c = C_c^∞(R³ × (0,∞);R³)`.  Reuses
`NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport`. -/
def MemFc (f : VelocityField) : Prop :=
  ContDiff ℝ ∞ f ∧ NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f

/-- `04-whole-space.tex` §4.6: `F_rd`, the rapidly decaying class.  All mixed
`∂_x^α ∂_t^j` seminorms of order `k = |α| + j` are collected in the joint
iterated derivative on `futureDomain = [0,∞) × R³`; no common numerical bound
on the seminorms is imposed. -/
def MemFrd (f : VelocityField) : Prop :=
  ContDiffOn ℝ ∞ f futureDomain ∧
    ∀ N k : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      (1 + ‖x‖ + t) ^ N * ‖iteratedFDerivWithin ℝ k f futureDomain (t, x)‖ ≤ C

/-! ## 7. The energy norm `E_T` -/

/-- `01-introduction.tex` eq:Enorm,
`‖z‖_{E_T} = ‖z‖_{L^∞(0,T;L²)} + ‖∇z‖_{L²(0,T;L²)}`, on the open interval
`(0,T)` only, imposing no endpoint value at `T`.  Same shape as
`NSFormalization.Paper1.InsertionEnergy.energyNorm`
(`formalization/NSFormalization/Paper1/InsertionEnergy.lean:30`), built from
the same two reused primitives `NavierStokesR3.CompactEnergy.l2Sq` and
`NavierStokesR3.CompactEnergy.dissipation`. -/
def energyNormET (T : ℝ) (F : VelocityField) : ℝ :=
  (eLpNorm (fun t => Real.sqrt (NavierStokesR3.CompactEnergy.l2Sq F t)) (⊤ : ℝ≥0∞)
      (volume.restrict (Ioo (0 : ℝ) T))).toReal +
    Real.sqrt (∫ t in Ioo (0 : ℝ) T, NavierStokesR3.CompactEnergy.dissipation F t)

/-! ## 8. Classical solutions and the pressure convention -/

/-- `02-preliminaries.tex` §2.1 and §2.3: on `R³` the scalar pressure is
determined only up to a function of time. -/
def PressureGaugeEquiv (p q : PressureField) : Prop :=
  ∃ c : ℝ → ℝ, ∀ (t : ℝ) (x : Space), q (t, x) = p (t, x) + c t

/-- `02-preliminaries.tex` §2.3, the explicit potential
`p(x,t) = ∫₀¹ G(rx,t)·x dr` of the curl-free field `G` of eq:Rpressure. -/
def pressurePotential (G : VelocityField) : PressureField :=
  fun z => ∫ r in (0 : ℝ)..1, (inner ℝ (G (z.1, r • z.2)) z.2 : ℝ)

/-- `02-preliminaries.tex` §2.1, §2.3, `prop:local`, and
`appendix-a-local-theory.tex`: a classical whole-space solution of eq:NS on
`[0,T)`.

* one-sided regularity at `t = 0` is `ContDiffOn` on `Ico 0 T ×ˢ univ` and, at
  the Sobolev level, `ContinuousOn _ (Ico 0 T)` of the `H^m` paths;
* `sobolev` + `sobolev_path_*` encode "a classical velocity belongs to
  `C([0,S];H^m)` for every integer `m ≥ 0` on each compact interval of its
  lifespan";
* the pressure enters only through `momentum`, i.e. through its gradient;
  no scalar `L²` requirement is imposed, matching "There is no requirement that
  `p ∈ L²(R³)`";
* `pressure_gradient_memLp` is the manuscript's `∇p ∈ L²`, which excludes a
  nonzero constant pressure gradient and is invariant under
  `PressureGaugeEquiv`;
* eq:Rpressure `∇p = (I-P)(f - ∇·(u⊗u))` follows from `momentum` together with
  `divergence`, and conversely; it is not a separate field. -/
structure ClassicalSolutionR (ν : ℝ) (a : Space → Space) (f : VelocityField) (T : ℝ) where
  /-- The velocity field. -/
  velocity : VelocityField
  /-- The pressure field, fixed only up to `PressureGaugeEquiv`. -/
  pressure : PressureField
  /-- The horizon is a genuine interval. -/
  horizon_pos : 0 < T
  /-- Smoothness on `[0,T) × R³`, one-sided at `t = 0`. -/
  velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- Smoothness of the pressure on `[0,T) × R³`. -/
  pressure_smooth : ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- `u(·,0) = a`. -/
  initial : ∀ x : Space, velocity (0, x) = a x
  /-- `∇·u = 0` on `[0,T)`. -/
  divergence : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 0
  /-- eq:NS at viscosity `ν`, at interior times. -/
  momentum : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)
  /-- Every spatial slice lies in `H^∞`. -/
  sobolev : ∀ t ∈ Ico (0 : ℝ) T, MemHInfty (fun x => velocity (t, x))
  /-- The `L²` jet paths witnessing `u ∈ C([0,S];H^m)` for every `m`. -/
  sobolev_path : (n : ℕ) → ℝ → Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space)
  /-- Each jet path is the actual iterated derivative of the slice. -/
  sobolev_path_ae : ∀ (n : ℕ) (t : ℝ), t ∈ Ico (0 : ℝ) T →
    (sobolev_path n t : Space → (Space [×n]→L[ℝ] Space)) =ᵐ[volume]
      iteratedFDeriv ℝ n (fun x => velocity (t, x))
  /-- Continuity in time of every `H^m` path. -/
  sobolev_path_continuous : ∀ n : ℕ, ContinuousOn (sobolev_path n) (Ico (0 : ℝ) T)
  /-- `∇p ∈ L²`; excludes a nonzero constant pressure gradient. -/
  pressure_gradient_memLp : ∀ t ∈ Ico (0 : ℝ) T,
    MemLp (fun x : Space => pressureGradient pressure t x) 2 volume

/-! ## 9. Maximal lifespan, breakdown set, regular reference -/

/-- `02-preliminaries.tex` §2.1: `T^ν_{max,R}(a,f)`, the maximal classical
lifespan.  Same supremum-of-horizons shape as
`NSFormalization.Source.SmoothLifespan.lifespan`
(`formalization/NSFormalization/Source/SmoothLifespan.lean:41`), taken over the
manuscript's `H^∞` solution class instead of the finite-energy `Flow` class. -/
def maximalLifespanR (ν : ℝ) (a : Space → Space) (f : VelocityField) : ℝ≥0∞ :=
  ⨆ S : ℝ, ⨆ (_ : Nonempty (ClassicalSolutionR ν a f S)), ENNReal.ofReal S

/-- `02-preliminaries.tex` §2.1: a reference solution is *regular through `T`*
if it extends smoothly to `[0,T+δ]` for some `δ > 0`.  This is the hypothesis of
`thm:Rinsert` and of the second case in the proof of `thm:Rmain`. -/
def RegularThrough (ν : ℝ) (a : Space → Space) (f : VelocityField) (T : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionR ν a f (T + δ))

/-- `02-preliminaries.tex` eq:Rsingularforces:
`B^R_{ν,a,T} = {f ∈ F_R : T^ν_{max,R}(a,f) ≤ T}`. -/
def breakdownSetR (ν : ℝ) (a : Space → Space) (T : ℝ) : Set ForceR :=
  {f | maximalLifespanR ν a f.field ≤ ENNReal.ofReal T}

/-- `02-preliminaries.tex` eq:Rsingularforces: `B^R_{ν,0,T}`, the zero-datum
case for which `thm:Rmain` (ii) is an if-and-only-if. -/
abbrev breakdownSetRZero (ν T : ℝ) : Set ForceR := breakdownSetR ν (fun _ => 0) T

/-! ## 10. The relative force topology and the density predicate -/

/-- `01-introduction.tex` ("We give each smooth force class the relative
topology induced by the stated norm") and `thm:Rmain`: the
`L^q(0,∞;H^s(R³))` distance between two members of `F_R`. -/
def forceRelativeDistance (q s : ℝ) (f g : ForceR) : ℝ≥0∞ :=
  bochnerSobolevENorm q s (fun t => f.toDistribution t - g.toDistribution t)

/-- `04-whole-space.tex` prop:Renergy: the `L^q(0,∞;Ḣ^s(R³))` distance, used at
`q = 2`, `s = -1`. -/
def forceHomogeneousDistance (q s : ℝ) (f g : ForceR) : ℝ≥0∞ :=
  bochnerHomogeneousENorm q s (fun t => f.toDistribution t - g.toDistribution t)

/-- `04-whole-space.tex` thm:Rmain (i)/(ii): density of `S ⊆ F_R` in the
relative `L^q(0,∞;H^s(R³))` topology on `F_R`.  For a topology induced by a
pseudometric this `ε`-approximation form is the definition of density; the
periodic analogue of that equivalence is
`NSFormalization.Paper1.ManuscriptTopology.denseAt_iff_approximation`
(`formalization/NSFormalization/Paper1/ManuscriptTopology.lean:176`). -/
def RelativelyDense (q s : ℝ) (S : Set ForceR) : Prop :=
  ∀ g : ForceR, ∀ ε : ℝ≥0∞, 0 < ε → ∃ f ∈ S, forceRelativeDistance q s f g < ε

/-- `04-whole-space.tex` prop:Renergy: density in the *completed* Bochner space,
stated against an arbitrary element of the completion rather than against a
smooth force. -/
def CompletedDense (q s : ℝ) (S : Set ForceR) : Prop :=
  ∀ b : ℝ → ForceDistribution, ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ f ∈ S, bochnerSobolevENorm q s (fun t => f.toDistribution t - b t) < ε

/-- `04-whole-space.tex` thm:Rmain: the threshold `s_q = 2/q - 3/2`. -/
def criticalOrder (q : ℝ) : ℝ := 2 / q - 3 / 2

/-- `04-whole-space.tex`, proof of thm:Rinsert: `β(q,s) = 2/q - 3/2 - s`. -/
def scalingExponent (q s : ℝ) : ℝ := 2 / q - 3 / 2 - s

/-- `04-whole-space.tex` thm:Rmain: the `L¹_t H^s_x` threshold is `1/2`. -/
example : criticalOrder 1 = 1 / 2 := by norm_num [criticalOrder]

/-- `04-whole-space.tex` thm:Rmain: the `L²_t H^s_x` threshold is `-1/2`. -/
example : criticalOrder 2 = -(1 / 2) := by norm_num [criticalOrder]

/-! ## 11. Cell observations (`thm:Rgrid`) -/

/-- `04-whole-space.tex` §4.8: `(A_h z)_C = |C|⁻¹ ∫_C z dx`. -/
def cellAverage (C : Set Space) (z : Space → Space) : Space :=
  ((volume C).toReal)⁻¹ • ∫ x in C, z x

/-- `04-whole-space.tex` §4.8: the cell-observation map `A_h` of a complete
uniform Cartesian grid, reusing `NSFormalization.Paper3.CartesianGrid`. -/
def gridObservation (grid : CartesianGrid) (z : Space → Space) : (Fin 3 → ℤ) → Space :=
  fun k => cellAverage (grid.cell k) z

end BlowupDensity.D01.DraftB
