import NSFormalization.Section4.D01.FiniteOrderNorm

/-!
# The inhomogeneous `J = (I - Δ)^{1/2}` weight identity

This is row S1a of `research/R44/R44_SPLIT.md`.  The repository's
`RealVectorSobolev s` carrier stores the **weighted** Fourier datum
`(1 + |ξ|²)^{s/2} û`, rather than the unweighted transform `û`.  Consequently
physical `J : H^s → H^{s-1}` is the identity on the stored `L²` datum, with
only its Sobolev order reindexed.  `Jmul_symbol` states the usual
`(1 + |ξ|²)^{1/2}` multiplier after the stored datum is converted back to its
unweighted Fourier profile; `Jmul_weighted_symbol` records the carrier-level
identity.  This convention is forced by, and explains, the exact isometry
`Jmul_norm`.

The single structure `JWeightDatum` is the datum-level restriction consumed by
all three estimates below.  Its fields are only standard realization facts for
`u`, its three weak coordinate derivatives, and `f`, plus the standard weak
derivative pairing.  Compactly supported smooth nonzero fields satisfy it (see
`research/R44/axioms_s1a.lean`).
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open scoped ENNReal LineDeriv RealInnerProductSpace SchwartzMap

namespace NSFormalization.Section4.R44

open NSFormalization.Section4.A03 (partialDeriv)
open NSFormalization.Section4.D01

/-! ## 1. `J` on the weighted datum carrier -/

/-- Physical `J = (I-Δ)^{1/2} : H^s → H^{s-1}` on weighted Fourier data.

Because an order-`s` datum is already `(1+|ξ|²)^{s/2} û`, the order-`s-1`
datum of `Ju` is the same `L²` function.  The order parameter of
`RealSobolevHilbert` is phantom at the carrier level, so this is a genuine
total isometry, including at negative orders. -/
def Jmul {s : ℝ} (v : RealVectorSobolev s) : RealVectorSobolev (s - 1) := v

/-- On the stored weighted datum, `Jmul` is order reindexing. -/
theorem Jmul_weighted_symbol {s : ℝ} (v : RealVectorSobolev s) (i : Fin 3) :
    ((((Jmul v) i : RealSobolevHilbert (s - 1)) : FourierData) : Space → ℂ)
      =ᵐ[volume]
        fun ξ => (((v i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ :=
  Filter.Eventually.of_forall fun _ => rfl

/-- The usual Fourier symbol of physical `J`.

Multiplication by `sobolevBesselWeight (-s)` removes the order-`s` weight from
the stored datum.  After that conversion, `Jmul` multiplies the unweighted
Fourier profile by `sobolevBesselWeight 1 = (1+|ξ|²)^{1/2}`. -/
theorem Jmul_symbol {s : ℝ} (v : RealVectorSobolev s) (i : Fin 3) :
    (fun ξ : Space => sobolevBesselWeight (-(s - 1)) ξ *
        ((((Jmul v) i : RealSobolevHilbert (s - 1)) : FourierData) : Space → ℂ) ξ)
      =ᵐ[volume]
        fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (sobolevBesselWeight (-s) ξ *
            ((((v i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ)) := by
  filter_upwards [Jmul_weighted_symbol v i] with ξ hξ
  rw [hξ]
  have hweight := congrFun (sobolevBesselWeight_mul 1 (-s)) ξ
  simp only [Pi.mul_apply] at hweight
  calc
    sobolevBesselWeight (-(s - 1)) ξ *
        ((((v i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ) =
      sobolevBesselWeight (1 + -s) ξ *
        ((((v i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ) := by
          congr 2
          ring
    _ = (sobolevBesselWeight 1 ξ * sobolevBesselWeight (-s) ξ) *
        ((((v i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ) := by
          rw [hweight]
    _ = _ := by
      change (sobolevBesselWeight 1 ξ * sobolevBesselWeight (-s) ξ) *
          ((((v i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ) =
        (((1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (sobolevBesselWeight (-s) ξ *
            ((((v i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ))
      rw [show sobolevBesselWeight 1 ξ =
        (((1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) by
          simp [sobolevBesselWeight]]
      ring

/-- `J : H^s → H^{s-1}` is an exact isometry. -/
theorem Jmul_norm {s : ℝ} (v : RealVectorSobolev s) : ‖Jmul v‖ = ‖v‖ := rfl

/-- The extended-norm version of `Jmul_norm`. -/
theorem Jmul_enorm {s : ℝ} (v : RealVectorSobolev s) : ‖Jmul v‖ₑ = ‖v‖ₑ := rfl

/-! ## 2. The one satisfiable datum restriction used by S1a -/

/-- Datum package for the `J`-weighted identity and force duality.

`partialDeriv j u` is the weak coordinate derivative of `u`, as pinned by
`gradient_pairing`.  Thus every named input is a restriction of the standard
Sobolev-datum / weak-derivative properties, and the package is satisfied by
nonzero compact-smooth data. -/
structure JWeightDatum (u f : Space → Space) where
  velocityHalf : RealVectorSobolev (1 / 2)
  velocityThreeHalf : RealVectorSobolev (3 / 2)
  gradientHalf : Fin 3 → RealVectorSobolev (1 / 2)
  forceNegHalf : RealVectorSobolev (-1 / 2)
  velocityHalf_isDatum : IsSobolevDatum (1 / 2) u velocityHalf
  velocityThreeHalf_isDatum : IsSobolevDatum (3 / 2) u velocityThreeHalf
  gradientHalf_isDatum : ∀ j,
    IsSobolevDatum (1 / 2) (partialDeriv j u) (gradientHalf j)
  forceNegHalf_isDatum : IsSobolevDatum (-1 / 2) f forceNegHalf
  gradient_pairing : ∀ (j i : Fin 3) (ψ : SchwartzMap Space ℂ),
    ∫ x, ψ x * ((partialDeriv j u x i : ℝ) : ℂ) =
      ∫ x, (-∂_{coordinateVector j} ψ) x * ((u x i : ℝ) : ℂ)

/-! The paper's scalar spellings.  They are real because `R44.Pieces` consumes
real-valued paths. -/

/-- `Y = ‖u‖_{H^{1/2}}`. -/
def Y (u : Space → Space) : ℝ := (sobolevENorm (1 / 2) u).toReal

/-- `Z = ‖∇u‖_{H^{1/2}}`, using A03's one-vector gradient norm. -/
def Z (u : Space → Space) : ℝ :=
  (NSFormalization.Section4.A03.gradientSobolevENorm (1 / 2) u).toReal

/-- `B = ‖f‖_{H^{-1/2}}`.  Negative-order data are already supported by
`RealVectorSobolev (-1/2)`; no fallback norm is needed. -/
def B (f : Space → Space) : ℝ := (sobolevENorm (-1 / 2) f).toReal

/-- The real datum pairing representing `⟪f, Ju⟫`.  The force's order-`-1/2`
datum and `Ju`'s order-`1/2` datum live in the shared weighted `L²` carrier. -/
def forceJPairing {u f : Space → Space} (h : JWeightDatum u f) : ℝ :=
  ⟪h.forceNegHalf, Jmul h.velocityThreeHalf⟫

/-! ## 3. Attainment and the exact Bessel-weight identity -/

/-- Whenever a Sobolev datum is supplied, the datum-infimum norm is attained
at it.  This uses uniqueness of the inhomogeneous realization. -/
theorem sobolevENorm_eq_of_isSobolevDatum {s : ℝ} {z : Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) :
    sobolevENorm s z = ‖A‖ₑ := by
  rw [sobolevENorm]
  refine le_antisymm ?_ (le_iInf fun C => ?_)
  · exact iInf_le_of_le ⟨A, hA⟩ le_rfl
  · rw [isSobolevDatum_unique C.2 hA]

/-- Datum form of `Y`. -/
theorem Y_eq_norm {u f : Space → Space} (h : JWeightDatum u f) :
    Y u = ‖h.velocityHalf‖ := by
  rw [Y, sobolevENorm_eq_of_isSobolevDatum h.velocityHalf_isDatum, toReal_enorm]

/-- Datum form of `Z²`, including the equality between the vector-gradient
spelling and the sum of the three component Sobolev norms. -/
theorem Z_sq_eq_sum_norm {u f : Space → Space} (h : JWeightDatum u f) :
    Z u ^ 2 = ∑ j : Fin 3, ‖h.gradientHalf j‖ ^ 2 := by
  have hfin : ∀ j : Fin 3, sobolevENorm (1 / 2) (partialDeriv j u) ≠ ⊤ := by
    intro j
    rw [sobolevENorm_eq_of_isSobolevDatum (h.gradientHalf_isDatum j)]
    exact enorm_ne_top
  rw [Z, NSFormalization.Section4.A03.gradientSobolevENorm,
    NSFormalization.Section4.A03.columnsSobolevENorm_toReal_sq_eq_sum hfin]
  apply Finset.sum_congr rfl
  intro j _
  rw [sobolevENorm_eq_of_isSobolevDatum (h.gradientHalf_isDatum j), toReal_enorm]

/-- Datum form of `B`. -/
theorem B_eq_norm {u f : Space → Space} (h : JWeightDatum u f) :
    B f = ‖h.forceNegHalf‖ := by
  rw [B, sobolevENorm_eq_of_isSobolevDatum h.forceNegHalf_isDatum, toReal_enorm]

/-- **R44 S1a, exact weight identity.**

`‖u‖²_{H^{3/2}} = Y² + Z²`, where `Z²` is exactly the sum of the
three `H^{1/2}` derivative norms.  The analytic equality is the sharp raising
identity from D01: pointwise
`1 + |ξ|² = 1 + ∑ⱼ |ξⱼ|²` under the `L²` integral. -/
theorem weight_identity {u f : Space → Space} (h : JWeightDatum u f) :
    (sobolevENorm (3 / 2) u).toReal ^ 2 = Y u ^ 2 + Z u ^ 2 := by
  let hg : ∀ i : Fin 3, RaisableWitness
      ((h.velocityHalf i : RealSobolevHilbert (1 / 2)) : FourierData) :=
    fun i => raisableWitness_of_memLp_smul _ fun j =>
      memLp_coord_smul_datum h.velocityHalf_isDatum h.gradientHalf_isDatum
        h.gradient_pairing i j
  let raised : RealVectorSobolev ((1 / 2 : ℝ) + 1) :=
    WithLp.toLp 2 (fun i => raiseHilbert (h.velocityHalf i) (hg i))
  have hraised : IsSobolevDatum ((1 / 2 : ℝ) + 1) u raised :=
    isSobolevDatum_raise h.velocityHalf_isDatum hg
  have heq : raised = h.velocityThreeHalf := by
    apply isSobolevDatum_unique hraised
    rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
    exact h.velocityThreeHalf_isDatum
  have hsharp := norm_raise_sq_eq h.velocityHalf_isDatum h.gradientHalf_isDatum
    h.gradient_pairing hg
  rw [sobolevENorm_eq_of_isSobolevDatum h.velocityThreeHalf_isDatum, toReal_enorm,
    ← heq, Y_eq_norm h, Z_sq_eq_sum_norm h]
  exact hsharp

/-! ## 4. Negative-order force duality -/

/-- **R44 S1a, Fourier Cauchy--Schwarz.**

`abs ⟪f, Ju⟫ ≤ B * sqrt (Y² + Z²)`.  The weights
`(1+|ξ|²)^{-1/4}` and `(1+|ξ|²)^{1/4}` are already absorbed into
`forceNegHalf` and `Jmul velocityThreeHalf`, so this is Hilbert-space
Cauchy--Schwarz followed by `weight_identity`. -/
theorem force_pairing_le {u f : Space → Space} (h : JWeightDatum u f) :
    |forceJPairing h| ≤ B f * Real.sqrt (Y u ^ 2 + Z u ^ 2) := by
  calc
    |forceJPairing h| ≤ ‖h.forceNegHalf‖ * ‖Jmul h.velocityThreeHalf‖ := by
      exact abs_real_inner_le_norm _ _
    _ = B f * ‖h.velocityThreeHalf‖ := by rw [Jmul_norm, B_eq_norm h]
    _ = B f * Real.sqrt (Y u ^ 2 + Z u ^ 2) := by
      rw [← weight_identity h,
        sobolevENorm_eq_of_isSobolevDatum h.velocityThreeHalf_isDatum,
        toReal_enorm, Real.sqrt_sq (norm_nonneg _)]

/-- Paper's second force form: `abs ⟪f, Ju⟫ ≤ B * (Y + Z)`. -/
theorem force_pairing_le' {u f : Space → Space} (h : JWeightDatum u f) :
    |forceJPairing h| ≤ B f * (Y u + Z u) := by
  have hY : 0 ≤ Y u := ENNReal.toReal_nonneg
  have hZ : 0 ≤ Z u := ENNReal.toReal_nonneg
  have hsqrt : Real.sqrt (Y u ^ 2 + Z u ^ 2) ≤ Y u + Z u := by
    have hsquare := Real.sq_sqrt (add_nonneg (sq_nonneg (Y u)) (sq_nonneg (Z u)))
    nlinarith [sq_nonneg (Y u - Z u)]
  exact (force_pairing_le h).trans
    (mul_le_mul_of_nonneg_left hsqrt ENNReal.toReal_nonneg)

end NSFormalization.Section4.R44
