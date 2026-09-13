import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Independent CMI periodic Navier–Stokes definitions.
`Point` is coordinate R³. The Pi norm is used only for topology and calculus;
physical kinetic density is separately defined as the sum of component squares.
Time is restricted to [0,∞); the momentum equation uses an actual right derivative.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff
open Set

namespace ClayNS

abbrev Point := Fin 3 → ℝ
abbrev Velocity := ℝ → Point → Point
abbrev Pressure := ℝ → Point → ℝ

def spatialDeriv (j : Fin 3) (g : Point → ℝ) (x : Point) : ℝ :=
  deriv (fun s => g (Function.update x j s)) (x j)

def divergence (v : Point → Point) (x : Point) : ℝ :=
  ∑ j : Fin 3, spatialDeriv j (fun y => v y j) x

def laplacian (g : Point → ℝ) (x : Point) : ℝ :=
  ∑ j : Fin 3, spatialDeriv j (spatialDeriv j g) x

def convection (u : Velocity) (t : ℝ) (x : Point) (i : Fin 3) : ℝ :=
  ∑ j : Fin 3, u t x j * spatialDeriv j (fun y => u t y i) x

def PeriodicSpatial {V : Type*} (g : Point → V) : Prop :=
  ∀ x (j : Fin 3), g (x + Pi.single j 1) = g x

def SmoothVelocity (u : Velocity) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Point => u z.1 z.2) (Ici 0 ×ˢ univ)

def SmoothPressure (p : Pressure) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Point => p z.1 z.2) (Ici 0 ×ˢ univ)

def Momentum (ν : ℝ) (u : Velocity) (p : Pressure) (f : Velocity) : Prop :=
  ∀ t, 0 ≤ t → ∀ x (i : Fin 3),
    HasDerivWithinAt (fun s => u s x i)
      (ν * laplacian (fun y => u t y i) x - convection u t x i - spatialDeriv i (p t) x
        + f t x i) (Ici 0) t

structure AdmissiblePeriodicDatum (u₀ : Point → Point) : Prop where
  smooth : ContDiff ℝ ∞ u₀
  periodic : PeriodicSpatial u₀
  solenoidal : ∀ x, divergence u₀ x = 0

structure GlobalPeriodicSolution (ν : ℝ) (u₀ : Point → Point)
    (u : Velocity) (p : Pressure) : Prop where
  smooth_velocity : SmoothVelocity u
  smooth_pressure : SmoothPressure p
  periodic_velocity : ∀ t, 0 ≤ t → PeriodicSpatial (u t)
  periodic_pressure : ∀ t, 0 ≤ t → PeriodicSpatial (p t)
  momentum : Momentum ν u p (fun _ _ _ => 0)
  incompressible : ∀ t, 0 ≤ t → ∀ x, divergence (u t) x = 0
  initial : ∀ x, u 0 x = u₀ x

/-- The full periodic unforced CMI alternative B, not asserted as a theorem. -/
def ClayB : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : Point → Point, AdmissiblePeriodicDatum u₀ →
    ∃ u : Velocity, ∃ p : Pressure, GlobalPeriodicSolution ν u₀ u p

def kineticDensity (v : Point) : ℝ := ∑ i : Fin 3, (v i) ^ 2

@[simp] theorem partial_const (j : Fin 3) (c : ℝ) (x : Point) :
    spatialDeriv j (fun _ => c) x = 0 := by
  simp [spatialDeriv]

@[simp] theorem divergence_zero (x : Point) :
    divergence (fun _ _ => 0) x = 0 := by
  simp [divergence]

theorem zero_datum_admissible : AdmissiblePeriodicDatum (fun _ _ => 0) := by
  refine ⟨contDiff_const, ?_, divergence_zero⟩
  intro x j
  rfl

theorem zero_global_periodic (ν : ℝ) :
    GlobalPeriodicSolution ν (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0) := by
  constructor
  · exact contDiff_const.contDiffOn
  · exact contDiff_const.contDiffOn
  · intro t ht x j
    rfl
  · intro t ht x j
    rfl
  · intro t ht x i
    simpa [laplacian, convection, spatialDeriv] using
      (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt (s := Ici 0)
  · intro t ht x
    exact divergence_zero x
  · intro x
    rfl

theorem clayB_zero_specialization (ν : ℝ) (_hν : 0 < ν) :
    AdmissiblePeriodicDatum (fun _ _ => 0) ∧
    ∃ u : Velocity, ∃ p : Pressure,
      GlobalPeriodicSolution ν (fun _ _ => 0) u p := by
  exact ⟨zero_datum_admissible, _, _, zero_global_periodic ν⟩

#print axioms clayB_zero_specialization

end ClayNS
