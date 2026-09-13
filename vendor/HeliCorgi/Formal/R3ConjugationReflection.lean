import Formal.R3StokesL2Operator

/-!
# Conjugation and frequency reflection on the `R³` `L²` velocity carrier

This file builds the minimal reality layer demanded by the physical
real-valued/conjugate-symmetric restriction gate.

It defines:

* `r3CConj` — coordinatewise complex conjugation on the fiber `R3C = ℂ³`, as an `ℝ`-linear
  isometry equivalence, with its fixed-point characterization (componentwise-real vectors);
* `r3L2Conj` — pointwise conjugation on the carrier `R3L2Velocity`, as a norm-preserving real
  continuous linear involution;
* `r3L2Reflect` — composition with the reflection `x ↦ -x`, as a norm-preserving complex
  continuous linear involution (the measure is negation-invariant);
* `IsR3RealVelocity` — the physical realness predicate `r3L2Conj g = g`;
* `IsR3ConjugateSymmetricVelocity` — the frequency-side conjugate-symmetry predicate
  `r3L2Reflect (r3L2Conj g) = g`, i.e. exact `L²` form of `û (-ξ) = conj (û ξ)`.

Both predicates are preserved by addition, real scalar multiplication, negation, subtraction,
and reflection, and both cut out closed subsets of the carrier.

Since `R3HsVelocity s` is by definition the same `L²` coordinate carrier for every order `s`,
these predicates apply verbatim to all Bessel-coordinate spaces used by the mild theory.

What this file deliberately does **not** prove: the Plancherel bridge stating that a coordinate
is physically real if and only if its Fourier transform is conjugate-symmetric, and the
realness-preservation of the concrete Stokes/Leray/convection operators. Those are the next
gates; no realness claim about the mild solutions is made here.
-/

namespace MNS2

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

/-! ## Fiber conjugation on `ℂ³` -/

/-- Coordinatewise complex conjugation on the fiber `R3C = ℂ³`, as an `ℝ`-linear isometry
equivalence. -/
def r3CConj : R3C ≃ₗᵢ[ℝ] R3C :=
  LinearIsometryEquiv.piLpCongrRight 2 fun _ : Fin 3 => Complex.conjLIE

@[simp]
theorem r3CConj_apply (v : R3C) (i : Fin 3) : r3CConj v i = conj (v i) :=
  rfl

@[simp]
theorem r3CConj_r3CConj (v : R3C) : r3CConj (r3CConj v) = v := by
  ext i
  simp

/-- The fixed points of the fiber conjugation are exactly the componentwise-real vectors. -/
theorem r3CConj_eq_self_iff (v : R3C) : r3CConj v = v ↔ ∀ i, (v i).im = 0 := by
  constructor
  · intro h i
    have hi := congrArg (fun w : R3C => w i) h
    simpa [Complex.conj_eq_iff_im] using hi
  · intro h
    ext i
    simpa [Complex.conj_eq_iff_im] using h i

/-- Fiber conjugation as a real continuous linear map. -/
def r3CConjCLM : R3C →L[ℝ] R3C :=
  r3CConj.toLinearIsometry.toContinuousLinearMap

@[simp]
theorem r3CConjCLM_apply (v : R3C) : r3CConjCLM v = r3CConj v :=
  rfl

theorem norm_r3CConjCLM_le_one : ‖r3CConjCLM‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [r3CConjCLM_apply, r3CConj.norm_map, one_mul]

/-! ## Conjugation on the carrier -/

/-- Pointwise complex conjugation on the `L²` velocity carrier, as a real continuous linear
map. -/
def r3L2Conj : R3L2Velocity →L[ℝ] R3L2Velocity :=
  r3CConjCLM.compLpL 2 volume

theorem coeFn_r3L2Conj (g : R3L2Velocity) :
    r3L2Conj g =ᵐ[volume] fun x => r3CConj (g x) :=
  r3CConjCLM.coeFn_compLpL g

@[simp]
theorem r3L2Conj_r3L2Conj (g : R3L2Velocity) : r3L2Conj (r3L2Conj g) = g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_r3L2Conj (r3L2Conj g), coeFn_r3L2Conj g] with x h1 h2
  rw [h1, h2, r3CConj_r3CConj]

theorem norm_r3L2Conj_le (g : R3L2Velocity) : ‖r3L2Conj g‖ ≤ ‖g‖ := by
  have h2 : ‖r3L2Conj‖ ≤ 1 :=
    le_trans (ContinuousLinearMap.norm_compLpL_le r3CConjCLM) norm_r3CConjCLM_le_one
  calc
    ‖r3L2Conj g‖ ≤ ‖r3L2Conj‖ * ‖g‖ := r3L2Conj.le_opNorm g
    _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg g)
    _ = ‖g‖ := one_mul _

/-- Carrier conjugation is norm-preserving. -/
@[simp]
theorem norm_r3L2Conj (g : R3L2Velocity) : ‖r3L2Conj g‖ = ‖g‖ := by
  refine le_antisymm (norm_r3L2Conj_le g) ?_
  calc
    ‖g‖ = ‖r3L2Conj (r3L2Conj g)‖ := by rw [r3L2Conj_r3L2Conj]
    _ ≤ ‖r3L2Conj g‖ := norm_r3L2Conj_le _

/-! ## Frequency reflection on the carrier -/

/-- The reflection `x ↦ -x` preserves the volume measure on `R3`. -/
theorem r3MeasurePreserving_neg :
    MeasurePreserving (fun x : R3 => -x) (volume : Measure R3) (volume : Measure R3) :=
  Measure.measurePreserving_neg _

/-- Reflection on the `L²` velocity carrier, as a complex linear map. -/
def r3L2ReflectLM : R3L2Velocity →ₗ[ℂ] R3L2Velocity where
  toFun g := Lp.compMeasurePreserving _ r3MeasurePreserving_neg g
  map_add' g h := map_add _ g h
  map_smul' c g := by
    refine Lp.ext ?_
    have h1 := Lp.coeFn_compMeasurePreserving (c • g) r3MeasurePreserving_neg
    have h2 := Lp.coeFn_compMeasurePreserving g r3MeasurePreserving_neg
    have h3 : ∀ᵐ x : R3 ∂(volume : Measure R3),
        (c • g : R3L2Velocity) (-x) = (c • (g : R3 → R3C)) (-x) :=
      r3MeasurePreserving_neg.quasiMeasurePreserving.ae (Lp.coeFn_smul c g)
    have h4 := Lp.coeFn_smul c (Lp.compMeasurePreserving _ r3MeasurePreserving_neg g)
    filter_upwards [h1, h2, h3, h4] with x e1 e2 e3 e4
    simp only [Function.comp_apply] at e1 e2
    simp only [Pi.smul_apply] at e3 e4
    rw [RingHom.id_apply, e1, e3, e4, e2]

/-- Reflection on the `L²` velocity carrier, as a complex continuous linear map. -/
def r3L2Reflect : R3L2Velocity →L[ℂ] R3L2Velocity :=
  LinearMap.mkContinuous r3L2ReflectLM 1 fun g => by
    rw [one_mul]
    exact le_of_eq (Lp.norm_compMeasurePreserving g r3MeasurePreserving_neg)

theorem coeFn_r3L2Reflect (g : R3L2Velocity) :
    r3L2Reflect g =ᵐ[volume] fun x => g (-x) :=
  Lp.coeFn_compMeasurePreserving g r3MeasurePreserving_neg

/-- Carrier reflection is norm-preserving. -/
@[simp]
theorem norm_r3L2Reflect (g : R3L2Velocity) : ‖r3L2Reflect g‖ = ‖g‖ :=
  Lp.norm_compMeasurePreserving g r3MeasurePreserving_neg

@[simp]
theorem r3L2Reflect_r3L2Reflect (g : R3L2Velocity) :
    r3L2Reflect (r3L2Reflect g) = g := by
  refine Lp.ext ?_
  have h2 : ∀ᵐ x : R3 ∂(volume : Measure R3),
      (r3L2Reflect g) (-x) = g (- -x) :=
    r3MeasurePreserving_neg.quasiMeasurePreserving.ae (coeFn_r3L2Reflect g)
  filter_upwards [coeFn_r3L2Reflect (r3L2Reflect g), h2] with x e1 e2
  rw [e1, e2, neg_neg]

/-- Conjugation and reflection commute on the carrier. -/
theorem r3L2Reflect_r3L2Conj (g : R3L2Velocity) :
    r3L2Reflect (r3L2Conj g) = r3L2Conj (r3L2Reflect g) := by
  refine Lp.ext ?_
  have h2 : ∀ᵐ x : R3 ∂(volume : Measure R3),
      (r3L2Conj g) (-x) = r3CConj (g (-x)) :=
    r3MeasurePreserving_neg.quasiMeasurePreserving.ae (coeFn_r3L2Conj g)
  filter_upwards [coeFn_r3L2Reflect (r3L2Conj g), h2,
    coeFn_r3L2Conj (r3L2Reflect g), coeFn_r3L2Reflect g] with x e1 e2 e3 e4
  rw [e1, e2, e3, e4]

/-! ## Reality predicates -/

/-- Physical realness of a stored `L²` Bessel coordinate: the coordinate is fixed by pointwise
complex conjugation. -/
def IsR3RealVelocity (g : R3L2Velocity) : Prop :=
  r3L2Conj g = g

/-- Frequency-side conjugate symmetry of a stored `L²` coordinate: the exact `L²` form of
`û (-ξ) = conj (û ξ)`. -/
def IsR3ConjugateSymmetricVelocity (g : R3L2Velocity) : Prop :=
  r3L2Reflect (r3L2Conj g) = g

theorem isR3RealVelocity_zero : IsR3RealVelocity 0 :=
  map_zero r3L2Conj

theorem isR3ConjugateSymmetricVelocity_zero : IsR3ConjugateSymmetricVelocity 0 := by
  unfold IsR3ConjugateSymmetricVelocity
  rw [map_zero, map_zero]

theorem IsR3RealVelocity.add {g h : R3L2Velocity}
    (hg : IsR3RealVelocity g) (hh : IsR3RealVelocity h) : IsR3RealVelocity (g + h) := by
  unfold IsR3RealVelocity at *
  rw [map_add, hg, hh]

theorem IsR3ConjugateSymmetricVelocity.add {g h : R3L2Velocity}
    (hg : IsR3ConjugateSymmetricVelocity g) (hh : IsR3ConjugateSymmetricVelocity h) :
    IsR3ConjugateSymmetricVelocity (g + h) := by
  unfold IsR3ConjugateSymmetricVelocity at *
  rw [map_add, map_add, hg, hh]

theorem IsR3RealVelocity.neg {g : R3L2Velocity} (hg : IsR3RealVelocity g) :
    IsR3RealVelocity (-g) := by
  unfold IsR3RealVelocity at *
  rw [map_neg, hg]

theorem IsR3ConjugateSymmetricVelocity.neg {g : R3L2Velocity}
    (hg : IsR3ConjugateSymmetricVelocity g) : IsR3ConjugateSymmetricVelocity (-g) := by
  unfold IsR3ConjugateSymmetricVelocity at *
  rw [map_neg, map_neg, hg]

theorem IsR3RealVelocity.sub {g h : R3L2Velocity}
    (hg : IsR3RealVelocity g) (hh : IsR3RealVelocity h) : IsR3RealVelocity (g - h) := by
  rw [sub_eq_add_neg]
  exact hg.add hh.neg

theorem IsR3ConjugateSymmetricVelocity.sub {g h : R3L2Velocity}
    (hg : IsR3ConjugateSymmetricVelocity g) (hh : IsR3ConjugateSymmetricVelocity h) :
    IsR3ConjugateSymmetricVelocity (g - h) := by
  rw [sub_eq_add_neg]
  exact hg.add hh.neg

theorem IsR3RealVelocity.real_smul {g : R3L2Velocity} (c : ℝ)
    (hg : IsR3RealVelocity g) : IsR3RealVelocity (c • g) := by
  unfold IsR3RealVelocity at *
  rw [map_smul, hg]

theorem IsR3ConjugateSymmetricVelocity.real_smul {g : R3L2Velocity} (c : ℝ)
    (hg : IsR3ConjugateSymmetricVelocity g) : IsR3ConjugateSymmetricVelocity (c • g) := by
  unfold IsR3ConjugateSymmetricVelocity at *
  rw [map_smul, ContinuousLinearMap.map_smul_of_tower, hg]

theorem IsR3RealVelocity.reflect {g : R3L2Velocity} (hg : IsR3RealVelocity g) :
    IsR3RealVelocity (r3L2Reflect g) := by
  unfold IsR3RealVelocity at *
  rw [← r3L2Reflect_r3L2Conj, hg]

/-- The physically real coordinates form a closed subset of the carrier. -/
theorem isClosed_setOf_isR3RealVelocity :
    IsClosed {g : R3L2Velocity | IsR3RealVelocity g} :=
  isClosed_eq r3L2Conj.continuous continuous_id

/-- The conjugate-symmetric coordinates form a closed subset of the carrier. -/
theorem isClosed_setOf_isR3ConjugateSymmetricVelocity :
    IsClosed {g : R3L2Velocity | IsR3ConjugateSymmetricVelocity g} :=
  isClosed_eq (r3L2Reflect.continuous.comp r3L2Conj.continuous) continuous_id

/-- Conjugate symmetry restated: reflection acts as conjugation. -/
theorem isR3ConjugateSymmetricVelocity_iff_reflect_eq_conj (g : R3L2Velocity) :
    IsR3ConjugateSymmetricVelocity g ↔ r3L2Reflect g = r3L2Conj g := by
  unfold IsR3ConjugateSymmetricVelocity
  constructor
  · intro h
    calc
      r3L2Reflect g = r3L2Reflect (r3L2Reflect (r3L2Conj g)) := by rw [h]
      _ = r3L2Conj g := r3L2Reflect_r3L2Reflect _
  · intro h
    rw [← h, r3L2Reflect_r3L2Reflect]

/-- Almost-everywhere characterization of physical realness. -/
theorem isR3RealVelocity_iff_ae (g : R3L2Velocity) :
    IsR3RealVelocity g ↔ (fun x => r3CConj (g x)) =ᵐ[volume] g := by
  constructor
  · intro h
    have hc := coeFn_r3L2Conj g
    rw [show r3L2Conj g = g from h] at hc
    exact hc.symm
  · intro h
    exact Lp.ext ((coeFn_r3L2Conj g).trans h)

/-- Physical realness is exactly a.e. vanishing of all componentwise imaginary parts. -/
theorem isR3RealVelocity_iff_im_ae (g : R3L2Velocity) :
    IsR3RealVelocity g ↔ ∀ᵐ x ∂(volume : Measure R3), ∀ i, (g x i).im = 0 := by
  rw [isR3RealVelocity_iff_ae]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact (r3CConj_eq_self_iff (g x)).1 hx
  · intro h
    filter_upwards [h] with x hx
    exact (r3CConj_eq_self_iff (g x)).2 hx

end

end MNS2
