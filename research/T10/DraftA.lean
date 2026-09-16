import Mathlib

/-!
# Draft A: the periodic data layer for Section 3

This is a statements-only candidate for `Contracts/V1/TorusData.lean`.  The
physical layer consists of unit-periodic fields on `R^3`; Sobolev regularity,
force norms, the mean-zero splitting, and Leray projection are all expressed
through weighted `l^2 (Z^3)` data.  Only Mathlib is imported, as required for a
future contract module.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.TorusDataDraftA

open Set MeasureTheory
open scoped ContDiff ENNReal

/-! ## Physical and Fourier carriers -/

/-- `01-introduction.tex:9-11`: physical space for the unit torus lift. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- `01-introduction.tex:8-11`: a physical, real, time-independent vector field. -/
abbrev SpatialField := Space → Space

/-- `01-introduction.tex:5-11`: spacetime, with time as the first coordinate. -/
abbrev SpaceTime := ℝ × Space

/-- `01-introduction.tex:5-11`: a physical, real velocity or force field. -/
abbrev SpaceTimeField := SpaceTime → Space

/-- `01-introduction.tex:5-11`: a physical, real pressure field. -/
abbrev SpaceTimeScalar := SpaceTime → ℝ

/-- `01-introduction.tex:10`: the unit torus `R^3 / Z^3`. -/
abbrev PeriodicTorus := UnitAddTorus (Fin 3)

/-- `01-introduction.tex:83-90`: the Fourier lattice `Z^3`. -/
abbrev PeriodicFrequency := Fin 3 → ℤ

/-- `01-introduction.tex:103`: the complex Euclidean three-vector used for the
three Fourier coefficients of a real physical vector field. -/
abbrev FourierVector := EuclideanSpace ℂ (Fin 3)

/-- `03-torus.tex:1-4` and `01-introduction.tex:83-90`: the complete coefficient carrier.  The order
`s` is a phantom index: its Bessel weight is stored in the datum rather than in
the underlying complete `l^2` space. -/
abbrev PeriodicSobolev (_s : ℝ) := lp (fun _ : PeriodicFrequency => FourierVector) 2

/-- `03-torus.tex:1-7` and `01-introduction.tex:83-90,103`: the real norm of a weighted, vector-valued
periodic Sobolev datum. -/
def periodicSobolevNorm (s : ℝ) (A : PeriodicSobolev s) : ℝ := ‖A‖

/-- `03-torus.tex:1-7` and `01-introduction.tex:83-90,103`: the extended norm of a weighted,
vector-valued periodic Sobolev datum. -/
def periodicSobolevDataENorm (s : ℝ) (A : PeriodicSobolev s) : ℝ≥0∞ := ‖A‖ₑ

/-- `01-introduction.tex:10,89`: embed a lattice translation in physical
Euclidean space. -/
def latticePoint (k : PeriodicFrequency) : Space :=
  WithLp.toLp 2 (fun i => (k i : ℝ))

/-- `02-preliminaries.tex:28`: unit periodicity of a physical spatial field. -/
def IsPeriodicSpatial {E : Type*} (z : Space → E) : Prop :=
  ∀ x : Space, ∀ k : PeriodicFrequency, z (x + latticePoint k) = z x

/-- `02-preliminaries.tex:28`: unit spatial periodicity of a spacetime field. -/
def IsPeriodicSpaceTimeOn {E : Type*} (I : Set ℝ) (z : SpaceTime → E) : Prop :=
  ∀ t : ℝ, t ∈ I → ∀ x : Space, ∀ k : PeriodicFrequency,
    z (t, x + latticePoint k) = z (t, x)

/-- `02-preliminaries.tex:28`: unit spatial periodicity at every time. -/
def IsPeriodicSpaceTime {E : Type*} (z : SpaceTime → E) : Prop :=
  IsPeriodicSpaceTimeOn univ z

/-- `01-introduction.tex:10,89`: canonical representative in the half-open
unit cube, rewritten verbatim from the representative used by
`NSFormalization.Paper1.TorusCube.torusLift`. -/
def torusRepresentative (z : PeriodicTorus) : Space :=
  WithLp.toLp 2 ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ) z).val)

/-- `01-introduction.tex:10,89`: canonical measurable realization on the unit
torus.  This is `NSFormalization.Paper1.TorusCube.torusLift` with its local
`toSpace` coercion expanded. -/
def torusLift {E : Type*} (f : Space → E) (z : PeriodicTorus) : E :=
  f (torusRepresentative z)

/-- `01-introduction.tex:83-90`: the unit-period angular Bessel weight
`1 + 4*pi^2*|k|^2`. -/
def periodicFrequencyWeight (k : PeriodicFrequency) : ℝ :=
  1 + 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2

/-- `01-introduction.tex:83-90`: the multiplier
`(1 + 4*pi^2*|k|^2)^(s/2)`. -/
def periodicSobolevWeight (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  Real.rpow (periodicFrequencyWeight k) (s / 2)

/-- `01-introduction.tex:89`: Fourier coefficients in the exact unit-period
angular convention.  Componentwise this is verbatim
`NSFormalization.Paper1.TorusCube.periodicFourierCoeff`, namely
`UnitAddTorus.mFourierCoeff (torusLift f) k`. -/
def periodicFourierCoeffT (z : SpatialField) (k : PeriodicFrequency) : FourierVector :=
  WithLp.toLp 2 (fun i =>
    UnitAddTorus.mFourierCoeff
      (torusLift (fun x => ((z x i : ℝ) : ℂ))) k)

/-- `03-torus.tex:1-4` and `01-introduction.tex:83-103`: `A(k)` is exactly
`(1+4*pi^2*|k|^2)^(s/2) * zhat(k)`.  Integrability prevents Mathlib's
totalized integral from assigning a spurious zero coefficient to a
non-integrable physical field.  The last clause records the conjugate-reflection
symmetry of the complex coefficients of a real vector field. -/
def IsPeriodicDatum (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s) : Prop :=
  IsPeriodicSpatial z ∧
    (∀ i : Fin 3, Integrable (torusLift (fun x => ((z x i : ℝ) : ℂ)))) ∧
    (∀ k : PeriodicFrequency,
      A k = (periodicSobolevWeight s k : ℂ) • periodicFourierCoeffT z k) ∧
    ∀ k : PeriodicFrequency, ∀ i : Fin 3, A (-k) i = star (A k i)

/-- `03-torus.tex:1-7` and `01-introduction.tex:83-103`: the totalized physical `H^s(T^3)` norm,
defined as the infimum over weighted coefficient data.  It is `top` when no
datum exists. -/
def periodicSobolevENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev s // IsPeriodicDatum s z A}, ‖A.1‖ₑ

/-! ## Mean, mean-zero coefficients, and Leray projection -/

/-- `03-torus.tex:395-404`: the spatial mean on the volume-one unit torus. -/
def meanT (z : SpatialField) : Space :=
  WithLp.toLp 2 (fun i => ∫ y : PeriodicTorus, torusLift (fun x => z x i) y)

/-- `03-torus.tex:395-411`: the constant part of the mean decomposition. -/
def meanPartT (z : SpatialField) : SpatialField := fun _ => meanT z

/-- `03-torus.tex:395-411`: the mean-zero part `z - mean(z)`. -/
def meanZeroPartT (z : SpatialField) : SpatialField := fun x => z x - meanT z

/-- `01-introduction.tex:105-109` and `03-torus.tex:407-414`: the coefficient
subspace with vanishing zero Fourier mode. -/
def PeriodicMeanZero (s : ℝ) : Submodule ℂ (PeriodicSobolev s) where
  carrier := {A | A (0 : PeriodicFrequency) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change A 0 = 0 at hA
    change B 0 = 0 at hB
    change (A + B) 0 = 0
    simp [hA, hB]
  smul_mem' := by
    intro c A hA
    change A 0 = 0 at hA
    change (c • A) 0 = 0
    simp [hA]

/-- `03-torus.tex:395-411`: the zero-frequency part of a coefficient datum. -/
def periodicMeanMode (s : ℝ) (A : PeriodicSobolev s) : PeriodicSobolev s :=
  lp.single 2 (0 : PeriodicFrequency) (A 0)

/-- `03-torus.tex:395-411`: the coefficient-side mean-zero part. -/
def periodicMeanZeroPart (s : ℝ) (A : PeriodicSobolev s) : PeriodicSobolev s :=
  A - periodicMeanMode s A

/-- `03-torus.tex:395-411`: the ordered pair `(constant mode, mean-zero part)`
of the coefficient decomposition. -/
def periodicMeanDecomposition (s : ℝ) (A : PeriodicSobolev s) :
    PeriodicSobolev s × PeriodicSobolev s :=
  (periodicMeanMode s A, periodicMeanZeroPart s A)

/-- `02-preliminaries.tex:76-80`: the complex frequency vector `k`. -/
def complexFrequencyVector (k : PeriodicFrequency) : FourierVector :=
  WithLp.toLp 2 (fun i => ((k i : ℝ) : ℂ))

/-- `02-preliminaries.tex:76-80`: the fiber perpendicular to `k`. -/
def solenoidalFiber (k : PeriodicFrequency) : Submodule ℂ FourierVector :=
  (Submodule.span ℂ {complexFrequencyVector k})ᗮ

/-- `02-preliminaries.tex:76-80`: the periodic Leray symbol.  It is the
identity at `k=0`; at `k != 0` orthogonal projection onto `k^perp` is exactly
`I - k tensor k / |k|^2`. -/
def periodicLeraySymbol (k : PeriodicFrequency) (v : FourierVector) : FourierVector :=
  ((solenoidalFiber k).orthogonalProjectionOnto v : FourierVector)

/-- `02-preliminaries.tex:76-80`: the periodic Leray projector on every
weighted coefficient space. -/
def periodicLerayProjector (s : ℝ) (A : PeriodicSobolev s) : PeriodicSobolev s :=
  ⟨fun k => periodicLeraySymbol k (A k),
    (lp.memℓp A).mono' fun k => by
      change ‖(solenoidalFiber k).orthogonalProjectionOnto (A k)‖ ≤ ‖A k‖
      exact (solenoidalFiber k).norm_orthogonalProjectionOnto_apply_le (A k)⟩

/-- `02-preliminaries.tex:76-83`: coefficient-side solenoidality
`k dot A(k) = 0`, including the vacuous zero-mode condition. -/
def IsSolenoidalDatum {s : ℝ} (A : PeriodicSobolev s) : Prop :=
  ∀ k : PeriodicFrequency, ∑ i : Fin 3, ((k i : ℤ) : ℂ) * A k i = 0

/-! ## Pressure gauge and differential operators -/

/-- `02-preliminaries.tex:28` and `:84-88`: the spatial pressure mean. -/
def pressureMeanT (p : SpaceTimeScalar) (t : ℝ) : ℝ :=
  ∫ y : PeriodicTorus, torusLift (fun x => p (t, x)) y

/-- `02-preliminaries.tex:28,84-88`: the pressure gauge `integral p = 0`, on
an explicitly supplied time set and with integrability made non-vacuous. -/
def HasZeroPressureMeanT (I : Set ℝ) (p : SpaceTimeScalar) : Prop :=
  ∀ t ∈ I, Integrable (torusLift (fun x => p (t, x))) ∧ pressureMeanT p t = 0

/-- `01-introduction.tex:5-6`: the `i`th Euclidean coordinate vector. -/
def coordinateVector (i : Fin 3) : Space :=
  WithLp.toLp 2 (Pi.single i (1 : ℝ))

/-- `01-introduction.tex:5-6`: the spatial derivative of a spacetime vector
field, with time frozen. -/
def spatialDerivative (u : SpaceTimeField) (t : ℝ) (x h : Space) : Space :=
  fderiv ℝ (fun y => u (t, y)) x h

/-- `01-introduction.tex:5-6`: the spatial divergence. -/
def spatialDivergence (u : SpaceTimeField) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, spatialDerivative u t x (coordinateVector i) i

/-- `01-introduction.tex:5-6`: the time derivative. -/
def temporalDerivative (u : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  fderiv ℝ (fun r => u (r, x)) t 1

/-- `01-introduction.tex:5-6`: the spatial Laplacian. -/
def spatialLaplacian (u : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3,
    fderiv ℝ (fun y => spatialDerivative u t y (coordinateVector i)) x
      (coordinateVector i)

/-- `01-introduction.tex:5-6`: the pressure gradient. -/
def pressureGradient (p : SpaceTimeScalar) (t : ℝ) (x : Space) : Space :=
  WithLp.toLp 2 (fun i => fderiv ℝ (fun y => p (t, y)) x (coordinateVector i))

/-- `01-introduction.tex:4-7` eq:NS: the left side of the periodic momentum
equation. -/
def navierStokesResidualT (ν : ℝ) (u : SpaceTimeField) (p : SpaceTimeScalar)
    (t : ℝ) (x : Space) : Space :=
  temporalDerivative u t x + spatialDerivative u t x (u (t, x)) -
    ν • spatialLaplacian u t x + pressureGradient p t x

/-! ## Time norms and the smooth input classes -/

/-- `01-introduction.tex:118-140`: force time measure on `(0,infinity)`. -/
abbrev forceTimeMeasureT : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

/-- `01-introduction.tex:118-140`: `G(t)` is the order-`s` weighted datum of
the physical force slice for every nonnegative time. -/
def IsPeriodicSobolevPath (s : ℝ) (f : SpaceTimeField)
    (G : ℝ → PeriodicSobolev s) : Prop :=
  ∀ t : ℝ, 0 ≤ t → IsPeriodicDatum s (fun x => f (t, x)) (G t)

/-- `01-introduction.tex:118-140`: the Bochner `L^q_t H^s_x` norm of a
coefficient path. -/
def periodicBochnerDatumENorm (q : ℝ≥0∞) (s : ℝ)
    (G : ℝ → PeriodicSobolev s) : ℝ≥0∞ :=
  eLpNorm G q forceTimeMeasureT

/-- `03-torus.tex:6-14` and `01-introduction.tex:118-140`: the physical force norm
`L^q(0,infinity;H^s(T^3))`, totalized to `top` if no strongly measurable
coefficient path represents all nonnegative-time slices. -/
def forceSobolevENormT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → PeriodicSobolev s //
      IsPeriodicSobolevPath s f G ∧ AEStronglyMeasurable G forceTimeMeasureT},
    periodicBochnerDatumENorm q s G.1

/-- `02-preliminaries.tex:9-10,23-26`: compact temporal support contained in
the open positive half-line.  Spatial compactness is intentionally absent for
the periodic Euclidean lift. -/
def HasCompactPositiveTimeSupportT (f : SpaceTimeField) : Prop :=
  ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioi (0 : ℝ) ∧
    ∀ t : ℝ, t ∉ K → ∀ x : Space, f (t, x) = 0

/-- `02-preliminaries.tex:9-10` eq:inputspaces:
`X_T = C^infinity_div(T^3;R^3)`. -/
def initialClassT : Set SpatialField :=
  {a | ContDiff ℝ ∞ a ∧ IsPeriodicSpatial a ∧
    ∀ x : Space, spatialDivergence (fun z : SpaceTime => a z.2) 0 x = 0}

/-- `02-preliminaries.tex:9-10,23-26` eq:inputspaces:
`F_T = C_c^infinity(T^3 times (0,infinity);R^3)`. -/
def forceClassT : Set SpaceTimeField :=
  {f | ContDiff ℝ ∞ f ∧ IsPeriodicSpaceTime f ∧ HasCompactPositiveTimeSupportT f}

/-! ## Classical solutions, lifespan, breakdown, and relative density -/

/-- `02-preliminaries.tex:28-36,105-114` prop:local: a classical periodic
solution on `[0,T)`, with periodic velocity and pressure and the pressure
normalized to spatial mean zero at every time in the lifespan. -/
structure ClassicalSolutionT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) where
  /-- The velocity field. -/
  velocity : SpaceTimeField
  /-- The pressure field. -/
  pressure : SpaceTimeScalar
  /-- The horizon is a genuine positive interval. -/
  horizon_pos : 0 < T
  /-- Velocity smoothness on the closed-at-zero, open-at-`T` slab. -/
  velocity_smooth :
    ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- Pressure smoothness on the same slab. -/
  pressure_smooth :
    ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- Unit spatial periodicity of velocity throughout the lifespan. -/
  velocity_periodic : IsPeriodicSpaceTimeOn (Ico (0 : ℝ) T) velocity
  /-- Unit spatial periodicity of pressure throughout the lifespan. -/
  pressure_periodic : IsPeriodicSpaceTimeOn (Ico (0 : ℝ) T) pressure
  /-- The gauge `integral_T3 p(t) = 0` for every `0 <= t < T`. -/
  pressure_gauge : HasZeroPressureMeanT (Ico (0 : ℝ) T) pressure
  /-- Initial condition `u(0)=a`. -/
  initial : ∀ x : Space, velocity (0, x) = a x
  /-- Pointwise incompressibility on `[0,T)`. -/
  divergence :
    ∀ t : ℝ, t ∈ Ico (0 : ℝ) T → ∀ x : Space,
      spatialDivergence velocity t x = 0
  /-- The momentum equation at every interior time. -/
  momentum :
    ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T → ∀ x : Space,
      navierStokesResidualT ν velocity pressure t x = f (t, x)
  /-- On each compact subinterval, every integer Sobolev order has a
  continuous weighted coefficient path representing the velocity slices. -/
  sobolev :
    ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) T) ∧
        ∀ t : ℝ, t ∈ Ico (0 : ℝ) T →
          IsPeriodicDatum (m : ℝ) (fun x => velocity (t, x)) (G t)

/-- `02-preliminaries.tex:32-36`: the maximal classical periodic lifespan,
the supremum of all horizons carrying a classical solution. -/
def maximalLifespanT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨆ S : ℝ, ⨆ _ : Nonempty (ClassicalSolutionT ν a f S), ENNReal.ofReal S

/-- `02-preliminaries.tex:34-36`: a reference solution is regular through `T`
when it has a classical extension to some strictly later horizon. -/
def RegularThroughT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionT ν a f (T + δ))

/-- `02-preliminaries.tex:38-46` eq:singularforces:
`B_{nu,a,T} = {f in F_T : T_max^nu(a,f) <= T}`. -/
def breakdownSetT (ν : ℝ) (a : SpatialField) (T : ℝ) : Set SpaceTimeField :=
  {f | f ∈ forceClassT ∧ maximalLifespanT ν a f ≤ ENNReal.ofReal T}

/-- `02-preliminaries.tex:40-41`: the zero-initial-data breakdown set. -/
def breakdownSetTZero (ν T : ℝ) : Set SpaceTimeField :=
  breakdownSetT ν (fun _ => 0) T

/-- `01-introduction.tex:118-140` and `03-torus.tex:6-14`: density of `S` in
the ambient smooth force class `Y` for the relative `L^q_t H^s_x` topology,
with quantifiers in the approximation order `g`, membership, radius, witness. -/
def RelativelyDenseT (q : ℝ≥0∞) (s : ℝ)
    (Y S : Set SpaceTimeField) : Prop :=
  ∀ g : SpaceTimeField, g ∈ Y → ∀ r : ℝ≥0∞, 0 < r →
    ∃ f : SpaceTimeField, f ∈ S ∧ forceSobolevENormT q s (f - g) < r

/-! ## The periodic energy norm -/

/-- `03-torus.tex:542-561` and `01-introduction.tex:83-90,143-150`: the coefficient-side homogeneous
first-derivative norm of an unweighted (`s=0`) datum. -/
def periodicGradientDatumENorm (A : PeriodicSobolev 0) : ℝ≥0∞ :=
  ENNReal.rpow
    (∑' k : PeriodicFrequency,
      ENNReal.ofReal
        ((4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖A k‖ ^ 2))
    (1 / 2 : ℝ)

/-- `03-torus.tex:542-561` and `01-introduction.tex:143-150`: the physical slice gradient norm, as the
infimum of the homogeneous coefficient norm over its order-zero data. -/
def periodicGradientENorm (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev 0 // IsPeriodicDatum 0 z A},
    periodicGradientDatumENorm A.1

/-- `03-torus.tex:299,542-561` and `01-introduction.tex:143-150` eq:Enorm, first summand
`L^infinity(0,T;L^2(T^3))`. -/
def energyEssSupT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  essSup (fun t => periodicSobolevENorm 0 (fun x => z (t, x)))
    (volume.restrict (Ioo (0 : ℝ) T))

/-- `03-torus.tex:299,542-561` and `01-introduction.tex:143-150` eq:Enorm, second summand
`L^2(0,T;dot H^1(T^3))`. -/
def energyGradientT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  ENNReal.rpow
    (∫⁻ t in Ioo (0 : ℝ) T,
      (periodicGradientENorm (fun x => z (t, x))) ^ (2 : ℝ))
    (1 / 2 : ℝ)

/-- `03-torus.tex:299,542-561` and `01-introduction.tex:143-150` eq:Enorm:
`E_T = L^infinity_t L^2_x + L^2_t dot H^1_x`, on `(0,T)` with no endpoint
value at `T`. -/
def energyENormT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  energyEssSupT T z + energyGradientT T z

end BlowupDensity.Contracts.V1.TorusDataDraftA
