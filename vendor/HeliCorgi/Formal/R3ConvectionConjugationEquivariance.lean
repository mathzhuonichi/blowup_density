import Formal.R3LerayConjugationEquivariance
import Formal.R3ProjectedSobolevConvection

/-!
# Conjugation equivariance of the projected convection

Final slice of the operator-realness gate. The completed convection map
`r3ConvectionH3ToH2` is the unique bounded bilinear extension of the Schwartz convection
term, which is a real bilinear differential expression; hence it commutes with pointwise
conjugation, and so does the projected convection (the Leray factor being already
equivariant).

Because the carrier conjugation `r3L2Conj` is only `ℝ`-linear, the statement is packaged
through the *triple-conjugated* map

`B̃ u v := r3L2Conj (B (r3L2Conj u) (r3L2Conj v))`,

which is again `ℂ`-bilinear (three conjugations), agrees with the Schwartz convection on the
dense core, and therefore equals `B` by `r3ConvectionH3ToH2_unique`.

The chain of core lemmas: the carrier conjugation is `ℂ`-antilinear (`r3L2Conj_smul`); the
Bessel coordinate map intertwines carrier and Schwartz conjugation
(`r3L2Conj_r3SchwartzToHsCLM`, via conjugation equivariance of real even Schwartz Fourier
multipliers); the Schwartz convection term is conjugation-equivariant
(`r3SchwartzConvection_conj`, via `fderiv` commuting with the real-linear fiber
conjugation).

Consequences: `r3L2Conj_r3ProjectedConvectionH3ToH2` and
`IsR3RealVelocity.projectedConvection` — with these, every building block of the Picard map
is realness-preserving.
-/

namespace MNS2

open MeasureTheory SchwartzMap FourierTransform
open scoped ENNReal NNReal ComplexConjugate FourierTransform

noncomputable section

/-! ## Carrier antilinearity and Schwartz involution -/

/-- The carrier conjugation is `ℂ`-antilinear. -/
theorem r3L2Conj_smul (c : ℂ) (g : R3L2Velocity) :
    r3L2Conj (c • g) = conj c • r3L2Conj g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_r3L2Conj (c • g), Lp.coeFn_smul c g,
    Lp.coeFn_smul (conj c) (r3L2Conj g), coeFn_r3L2Conj g] with x e1 e2 e3 e4
  simp only [Pi.smul_apply] at e2 e3
  rw [e1, e2, r3CConj_smul, e3, e4]

/-- The Schwartz conjugation is an involution. -/
theorem r3SchwartzConjCLM_r3SchwartzConjCLM (φ : R3SchwartzVelocity) :
    r3SchwartzConjCLM (r3SchwartzConjCLM φ) = φ :=
  SchwartzMap.ext fun x => r3CConj_r3CConj (φ x)

/-! ## Conjugation equivariance of real even Schwartz Fourier multipliers -/

/-- Conjugation moves through the inverse Schwartz Fourier transform against a reflection. -/
theorem r3SchwartzConjCLM_fourierInv (χ : R3SchwartzVelocity) :
    r3SchwartzConjCLM (𝓕⁻ χ) =
      𝓕⁻ (r3SchwartzReflectCLM (r3SchwartzConjCLM χ)) := by
  have h := fourier_r3SchwartzConjCLM (𝓕⁻ χ)
  rw [fourier_fourierInv_eq] at h
  calc
    r3SchwartzConjCLM (𝓕⁻ χ)
        = 𝓕⁻ (𝓕 (r3SchwartzConjCLM (𝓕⁻ χ))) := (fourierInv_fourier_eq _).symm
    _ = 𝓕⁻ (r3SchwartzReflectCLM (r3SchwartzConjCLM χ)) := by rw [h]

/-- Reflected conjugation commutes with multiplication by a real, even symbol. -/
theorem reflect_conj_smulLeft {W : R3 → ℂ} (hW : W.HasTemperateGrowth)
    (hreal : ∀ ξ : R3, conj (W ξ) = W ξ) (heven : ∀ ξ : R3, W (-ξ) = W ξ)
    (χ : R3SchwartzVelocity) :
    r3SchwartzReflectCLM (r3SchwartzConjCLM (smulLeftCLM R3C W χ)) =
      smulLeftCLM R3C W (r3SchwartzReflectCLM (r3SchwartzConjCLM χ)) := by
  refine SchwartzMap.ext fun ξ => ?_
  rw [r3SchwartzReflectCLM_apply, r3SchwartzConjCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply hW, SchwartzMap.smulLeftCLM_apply_apply hW,
    r3CConj_smul, hreal, heven, r3SchwartzReflectCLM_apply, r3SchwartzConjCLM_apply]

/-- Conjugation equivariance of Schwartz Fourier multipliers with real, even symbols. -/
theorem r3SchwartzConjCLM_fourierMultiplier {W : R3 → ℂ} (hW : W.HasTemperateGrowth)
    (hreal : ∀ ξ : R3, conj (W ξ) = W ξ) (heven : ∀ ξ : R3, W (-ξ) = W ξ)
    (φ : R3SchwartzVelocity) :
    r3SchwartzConjCLM (fourierMultiplierCLM R3C W φ) =
      fourierMultiplierCLM R3C W (r3SchwartzConjCLM φ) := by
  rw [fourierMultiplierCLM_apply, fourierMultiplierCLM_apply,
    r3SchwartzConjCLM_fourierInv, reflect_conj_smulLeft hW hreal heven,
    ← fourier_r3SchwartzConjCLM]

/-- The Bessel coordinate map intertwines carrier and Schwartz conjugation. -/
theorem r3L2Conj_r3SchwartzToHsCLM (s : ℝ) (φ : R3SchwartzVelocity) :
    r3L2Conj (r3SchwartzToHsCLM s φ) = r3SchwartzToHsCLM s (r3SchwartzConjCLM φ) := by
  rw [r3SchwartzToHsCLM_apply, r3SchwartzToHsCLM_apply, r3L2Conj_toLp]
  congr 1
  exact r3SchwartzConjCLM_fourierMultiplier
    (r3SobolevWeightComplex_hasTemperateGrowth s)
    (r3SobolevWeightComplex_conj s) (r3SobolevWeightComplex_neg s) φ

/-! ## Conjugation equivariance of the Schwartz convection -/

/-- The coordinate derivative commutes with the Schwartz conjugation. -/
theorem r3SchwartzCoordinateDerivative_conj (i : Fin 3) (v : R3SchwartzVelocity) :
    r3SchwartzCoordinateDerivative i (r3SchwartzConjCLM v) =
      r3SchwartzConjCLM (r3SchwartzCoordinateDerivative i v) := by
  refine SchwartzMap.ext fun x => ?_
  have hv : DifferentiableAt ℝ (⇑v) x :=
    ((v.smooth ⊤).differentiable (by simp)).differentiableAt
  have hcomp : (⇑(r3SchwartzConjCLM v) : R3 → R3C) = ⇑r3CConjCLM ∘ ⇑v := rfl
  calc
    r3SchwartzCoordinateDerivative i (r3SchwartzConjCLM v) x
        = fderiv ℝ (⇑(r3SchwartzConjCLM v)) x (r3CoordinateDirection i) := by
          simp only [r3SchwartzCoordinateDerivative, LineDeriv.lineDerivOpCLM_apply,
            lineDerivOp_apply_eq_fderiv]
    _ = r3CConj (fderiv ℝ (⇑v) x (r3CoordinateDirection i)) := by
          rw [hcomp, fderiv_comp x r3CConjCLM.differentiableAt hv,
            ContinuousLinearMap.fderiv]
          rfl
    _ = r3CConj (r3SchwartzCoordinateDerivative i v x) := by
          simp only [r3SchwartzCoordinateDerivative, LineDeriv.lineDerivOpCLM_apply,
            lineDerivOp_apply_eq_fderiv]
    _ = r3SchwartzConjCLM (r3SchwartzCoordinateDerivative i v) x := rfl

/-- One convection coordinate term is conjugation-equivariant. -/
theorem r3SchwartzConvectionTerm_conj (i : Fin 3) (u v : R3SchwartzVelocity) :
    r3SchwartzConvectionTerm i (r3SchwartzConjCLM u) (r3SchwartzConjCLM v) =
      r3SchwartzConjCLM (r3SchwartzConvectionTerm i u v) := by
  refine SchwartzMap.ext fun x => ?_
  show r3SchwartzConvectionTerm i (r3SchwartzConjCLM u) (r3SchwartzConjCLM v) x =
    r3CConj (r3SchwartzConvectionTerm i u v x)
  rw [r3SchwartzConvectionTerm_apply, r3SchwartzConvectionTerm_apply,
    r3SchwartzCoordinateDerivative_conj, r3CConj_smul]
  congr 1

/-- The Schwartz convection is conjugation-equivariant. -/
theorem r3SchwartzConvection_conj (u v : R3SchwartzVelocity) :
    r3SchwartzConvection (r3SchwartzConjCLM u) (r3SchwartzConjCLM v) =
      r3SchwartzConjCLM (r3SchwartzConvection u v) := by
  rw [r3SchwartzConvection, r3SchwartzConvection, sum_apply, sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => r3SchwartzConvectionTerm_conj i u v

/-! ## The triple-conjugated bilinear map -/

set_option maxHeartbeats 1000000 in
/--
The triple-conjugated convection `B̃ u v = conj (B (conj u) (conj v))`.  Three conjugations
make it `ℂ`-bilinear again, so it can be packaged as a genuine continuous bilinear map.
-/
def r3ConjugatedConvectionH3ToH2 :
    R3HsVelocity 3 →L[ℂ] R3HsVelocity 3 →L[ℂ] R3HsVelocity 2 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ
      (fun u v => r3L2Conj (r3ConvectionH3ToH2 (r3L2Conj u) (r3L2Conj v)))
      (fun u u' v => by
        rw [map_add r3L2Conj u u',
          map_add r3ConvectionH3ToH2 (r3L2Conj u) (r3L2Conj u'), add_apply,
          map_add r3L2Conj])
      (fun c u v => by
        rw [r3L2Conj_smul c u, map_smul r3ConvectionH3ToH2,
          smul_apply, r3L2Conj_smul, Complex.conj_conj])
      (fun u v v' => by
        rw [map_add r3L2Conj v v',
          map_add (r3ConvectionH3ToH2 (r3L2Conj u)) (r3L2Conj v) (r3L2Conj v'),
          map_add r3L2Conj])
      (fun c u v => by
        rw [r3L2Conj_smul c v, map_smul (r3ConvectionH3ToH2 (r3L2Conj u)),
          r3L2Conj_smul, Complex.conj_conj]))
    ‖r3ConvectionH3ToH2‖
    (fun u v => by
      calc
        ‖r3L2Conj (r3ConvectionH3ToH2 (r3L2Conj u) (r3L2Conj v))‖
            = ‖r3ConvectionH3ToH2 (r3L2Conj u) (r3L2Conj v)‖ := norm_r3L2Conj _
        _ ≤ ‖r3ConvectionH3ToH2 (r3L2Conj u)‖ * ‖r3L2Conj v‖ :=
            (r3ConvectionH3ToH2 (r3L2Conj u)).le_opNorm _
        _ ≤ ‖r3ConvectionH3ToH2‖ * ‖r3L2Conj u‖ * ‖r3L2Conj v‖ :=
            mul_le_mul_of_nonneg_right (r3ConvectionH3ToH2.le_opNorm _) (norm_nonneg _)
        _ = ‖r3ConvectionH3ToH2‖ * ‖u‖ * ‖v‖ := by
            rw [norm_r3L2Conj, norm_r3L2Conj])

@[simp]
theorem r3ConjugatedConvectionH3ToH2_apply (u v : R3HsVelocity 3) :
    r3ConjugatedConvectionH3ToH2 u v =
      r3L2Conj (r3ConvectionH3ToH2 (r3L2Conj u) (r3L2Conj v)) :=
  rfl

/-- The triple-conjugated convection agrees with the convection on the Schwartz core, hence
everywhere. -/
theorem r3ConjugatedConvectionH3ToH2_eq :
    r3ConjugatedConvectionH3ToH2 = r3ConvectionH3ToH2 := by
  apply r3ConvectionH3ToH2_unique
  intro u v
  rw [r3ConjugatedConvectionH3ToH2_apply, r3L2Conj_r3SchwartzToHsCLM,
    r3L2Conj_r3SchwartzToHsCLM, r3ConvectionH3ToH2_apply_schwartz,
    r3L2Conj_r3SchwartzToHsCLM, r3SchwartzConvection_conj,
    r3SchwartzConjCLM_r3SchwartzConjCLM]

/-! ## Main equivariance and realness preservation -/

/-- The completed convection commutes with pointwise conjugation. -/
theorem r3L2Conj_r3ConvectionH3ToH2 (u v : R3HsVelocity 3) :
    r3L2Conj (r3ConvectionH3ToH2 u v) =
      r3ConvectionH3ToH2 (r3L2Conj u) (r3L2Conj v) := by
  have happ := congrArg
    (fun T : R3HsVelocity 3 →L[ℂ] R3HsVelocity 3 →L[ℂ] R3HsVelocity 2 => T u v)
    r3ConjugatedConvectionH3ToH2_eq
  simp only [r3ConjugatedConvectionH3ToH2_apply] at happ
  rw [← happ, r3L2Conj_r3L2Conj]

/-- The projected convection commutes with pointwise conjugation. -/
theorem r3L2Conj_r3ProjectedConvectionH3ToH2 (u v : R3HsVelocity 3) :
    r3L2Conj (r3ProjectedConvectionH3ToH2 u v) =
      r3ProjectedConvectionH3ToH2 (r3L2Conj u) (r3L2Conj v) := by
  rw [r3ProjectedConvectionH3ToH2_apply, r3ProjectedConvectionH3ToH2_apply,
    r3L2Conj_r3LerayH2Operator, r3L2Conj_r3ConvectionH3ToH2]

/-- The projected convection of physically real coordinates is physically real. -/
theorem IsR3RealVelocity.projectedConvection {u v : R3HsVelocity 3}
    (hu : IsR3RealVelocity u) (hv : IsR3RealVelocity v) :
    IsR3RealVelocity (r3ProjectedConvectionH3ToH2 u v) := by
  unfold IsR3RealVelocity at *
  rw [r3L2Conj_r3ProjectedConvectionH3ToH2, hu, hv]

end

end MNS2
