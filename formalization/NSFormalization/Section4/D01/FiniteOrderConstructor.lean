import NSFormalization.Section4.D01.FiniteOrderDatum
import NSFormalization.Section4.D01.OrderZeroDatum

/-!
# Closing the finite-order angular Sobolev datum constructor (unit D01 · C1b-m-D)

`research/A01/C1B_SPLIT.md` row **C1b-m-D** is the carrier bridge's real blocker: D01 has an
order-`0` datum constructor from a bare `MemLp` field (`OrderZeroDatum.orderZeroDatum`) and an
**all-orders** constructor from a `SmoothL2Field` (`SmoothDatum.smoothAngularDatum`), but *nothing
in between* — no constructor taking a field of finite regularity to an order-`m` datum.
`FiniteOrderDatum.lean` supplied the order-**raising step** (`isSobolevDatum_raise`) once the `L²`
raising witness is given, and reduced that witness (`raisableWitness_of_memLp_smul`) to the square
integrability of each coordinate multiple `ξ ↦ (ξ j)·(A i)(ξ)`.  This module discharges that
coordinate `L²` obligation from the weak derivatives of the field, and assembles the whole
constructor by induction on the order.

## What is proved here

* `isSobolevDatum_partialDeriv_weak`, `db_cycles_full` (rows D-b0 / D-b) — **promoted verbatim from
  the lane-125 reviewer probes** (`research/D01/probes/rev125_partialderiv_weak.lean`,
  `rev125_db_cycles.lean`; credit: lane-125 review).  `db_cycles_full` is the raw-frequency Fourier
  identity `2πi·ξⱼ·((cyclesToAngular s).symm (A i)) =ᵐ (cyclesToAngular s).symm (C i)` in the
  pre-dilation (cycles) variable, `C` an order-`s` datum of the weak `∂ⱼz`, with **no smoothness**.

* `memLp_coord_smul_datum` (**row D-b-transport, the only genuinely new work**).  Transports
  `db_cycles_full` from the cycles variable to the raw *angular* variable.  Because the angular
  datum is `angularFrequencyDilation ∘ angularWeightEquiv` of its cycles form, and `A i` and `C j i`
  carry the *same* dilation and weight factors, the transport collapses to a clean a.e. identity
  `(ξ j)·(A i) =ᵐ (frequencyUnit / (2πi))·(C j i)` in the angular variable — the dilation Jacobian
  `frequencyUnit` and the constant `2πi` are the only survivors; the Bessel weight cancels.  Since
  `C j i` is in `L²`, the coordinate multiple is in `L²`.  This is the shape
  `raisableWitness_of_memLp_smul` consumes.

* `exists_isSobolevDatum_of_memLp_derivs` (**row D-close, C1b-m-D itself**).  By induction on `m`:
  the order-`0` seed is `orderZeroDatum`; the step applies the induction hypothesis to `z` and to
  each weak derivative `∂ⱼz`, feeds the resulting data through `memLp_coord_smul_datum`,
  `raisableWitness_of_memLp_smul` and `isSobolevDatum_raise`.  The hypothesis is packaged as the
  predicate `HasWeakDerivsL2 z m`: `MemLp z 2` plus, recursively, an `L²` weak `j`-th derivative
  with its Schwartz pairing, up to order `m`.

## The hypothesis `HasWeakDerivsL2` and the Euler side

`HasWeakDerivsL2 z m` is the iterated form of the Schwartz-pairing weak-derivative hypothesis of
`db_cycles_full`.  This is exactly what the Euler side can deliver (`C1B_SPLIT.md` rows
C1b-m-E / D-euler-pairing): C1b-m-E's `word_hasDerivAt` gives strong `L²` translation derivatives of
each descended word, from which the Schwartz pairing `∫ψ·(∂ⱼz)ᵢ = ∫(−∂ⱼψ)·zᵢ` (row D-euler-pairing)
follows by integration by parts, and the recursion bottoms out at `MemLp z 2`.  Non-vacuity is
checked below: every `SmoothL2Field` satisfies `HasWeakDerivsL2 z m` for all `m`
(`weakDerivs_smooth`), and the constructed datum then agrees with `smoothAngularDatum` by uniqueness.

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_finite_order_close.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.D01

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01.Leray (isSobolevDatum_lower)
open NSFormalization.Section4.A03 (lowerDatum coe_lowerDatum)
open scoped ENNReal ComplexConjugate LineDeriv SchwartzMap

/-! ## 0. The cycles-variable Fourier identity (rows D-b0 / D-b)

Both lemmas were proved by the lane-125 reviewer and preserved as
`research/D01/probes/rev125_{partialderiv_weak,db_cycles}.lean`; they are promoted here verbatim
(credit: lane-125 review of `FiniteOrderDatum.lean`) so that a registered module carries them. -/

/-- **The Schwartz-duality route, smoothness-free** (row D-b0).  If `A` is an order-`s` datum of `z`
and `w` is the `j`-th weak derivative of `z` in the Schwartz-pairing sense, then the angular
directional derivative of `A` is an order-`(s-1)` datum of `w`.  No `SmoothL2Field`, no `ContDiff`.
Promoted from `research/D01/probes/rev125_partialderiv_weak.lean` (lane-125 review). -/
theorem isSobolevDatum_partialDeriv_weak {s : ℝ} {z w : Space → Space} (j : Fin 3)
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A)
    (hw : ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ)) :
    IsSobolevDatum (s - 1) w
      (WithLp.toLp 2 fun i => angularDirectionalDerivativeReal s (coordinateVector j) (A i)) := by
  intro i ψ
  have hcoe : (((WithLp.toLp 2 fun k =>
        angularDirectionalDerivativeReal s (coordinateVector j) (A k)) i :
          RealSobolevHilbert (s - 1)) : FourierData)
      = angularDirectionalDerivative s (coordinateVector j) ((A i : FourierData)) :=
    angularDirectionalDerivativeReal_coe s (coordinateVector j) (A i)
  rw [hcoe, angularRealization_directionalDerivative s (coordinateVector j) ((A i : FourierData)),
    TemperedDistribution.lineDerivOp_apply_apply, hA i (-∂_{coordinateVector j} ψ), hw i ψ]

/-- **Row D-b, in the cycles variable, with no smoothness anywhere.**  If `A` is an order-`s` datum
of `z`, `C` an order-`s` datum of the weak `j`-th derivative `w` of `z`, then in the pre-dilation
(cycles) frequency variable `2πi·ξⱼ·k_A = k_C` a.e.  Promoted from
`research/D01/probes/rev125_db_cycles.lean` (lane-125 review). -/
theorem db_cycles_full {s : ℝ} (j : Fin 3) {z w : Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A)
    {C : RealVectorSobolev s} (hC : IsSobolevDatum s w C)
    (hw : ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ))
    (i : Fin 3) :
    ∀ᵐ ξ ∂(volume : Measure Space),
      (2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ) *
          (((cyclesToAngular s).symm ((A i : RealSobolevHilbert s) : FourierData)) : Space → ℂ) ξ
        = (((cyclesToAngular s).symm ((C i : RealSobolevHilbert s) : FourierData)) : Space → ℂ) ξ := by
  have hle : s - 1 ≤ s := by linarith
  have hB := isSobolevDatum_partialDeriv_weak j hA hw
  have hlow := isSobolevDatum_lower hle hC
  have heq := isSobolevDatum_unique hB hlow
  have hcomp : angularDirectionalDerivative s (coordinateVector j) ((A i : FourierData))
      = angularOrderLowering s (s - 1) hle ((C i : FourierData)) := by
    have h := congrArg
      (fun B : RealVectorSobolev (s - 1) => ((B i : RealSobolevHilbert (s - 1)) : FourierData)) heq
    simpa [angularDirectionalDerivativeReal_coe, lowerVectorL_apply, coe_lowerDatum] using h
  have hcyc : sobolevDirectionalDerivative s (coordinateVector j)
        ((cyclesToAngular s).symm ((A i : FourierData)))
      = sobolevOrderLowering s (s - 1) hle ((cyclesToAngular s).symm ((C i : FourierData))) := by
    have h1 : (cyclesToAngular (s - 1)).symm
          (angularDirectionalDerivative s (coordinateVector j) ((A i : FourierData)))
        = sobolevDirectionalDerivative s (coordinateVector j)
          ((cyclesToAngular s).symm ((A i : FourierData))) :=
      (cyclesToAngular (s - 1)).symm_apply_apply _
    rw [← h1, hcomp, cyclesToAngular_symm_orderLowering]
  have hsigma : ∀ ξ : Space, sobolevDirectionalSymbol (coordinateVector j) ξ
      = (2 * (Real.pi : ℂ) * Complex.I) * (((ξ j : ℝ) : ℂ) * sobolevBesselWeight (-1) ξ) := by
    intro ξ
    rw [sobolevDirectionalSymbol]
    congr 3
    rw [coordinateVector, EuclideanSpace.inner_single_right]; simp
  have hae : (fun ξ => sobolevDirectionalSymbol (coordinateVector j) ξ *
      (((cyclesToAngular s).symm ((A i : FourierData))) : Space → ℂ) ξ)
        =ᵐ[volume] ((sobolevOrderLowering s (s - 1) hle
          ((cyclesToAngular s).symm ((C i : FourierData)))) : Space → ℂ) := by
    refine (sobolevDirectionalDerivative_coeFn s (coordinateVector j)
      ((cyclesToAngular s).symm ((A i : FourierData)))).symm.trans ?_
    rw [hcyc]
  filter_upwards [hae, sobolevOrderLowering_coeFn s (s - 1) hle
      ((cyclesToAngular s).symm ((C i : FourierData)))] with ξ e e2
  have hW : sobolevBesselWeight (-1) ξ ≠ 0 := by
    simp only [sobolevBesselWeight]; rw [Complex.ofReal_ne_zero]; positivity
  rw [e2, show s - 1 - s = (-1 : ℝ) by ring, hsigma ξ] at e
  refine mul_right_cancel₀ hW ?_
  linear_combination e

/-! ## 1. Transport to the raw angular variable (row D-b-transport, the new work)

The angular datum is `cyclesToAngular s = angularFrequencyDilation ∘ angularWeightEquiv s` of its
cycles form.  The two identical factors (the normalized dilation `f ↦ frequencyUnit^{-3/2} f(c⁻¹·)`
and the Bessel weight `angularWeightSymbol s`) appear on both the `A i` and `C j i` sides, so after
substituting the cycles identity `db_cycles_full` they cancel, leaving the angular a.e. identity
`(ξ j)·(A i) =ᵐ (frequencyUnit / 2πi)·(C j i)`.  Since `C j i` is `L²`, the coordinate multiple is
`L²`. -/

/-- **Row D-b-transport.**  Given an order-`s` datum `A` of `z` and, for each `j`, an order-`s`
datum `C j` of the weak `j`-th derivative `w j` of `z` (Schwartz pairing `hw`), every
coordinate-multiplied component `ξ ↦ (ξ j)·(A i)(ξ)` of `A` is square integrable — the shape
`raisableWitness_of_memLp_smul` consumes.  The proof carries `db_cycles_full` from the pre-dilation
cycles variable to the raw angular variable; the Bessel weight and dilation cancel between the two
sides, and only the dilation Jacobian `frequencyUnit` and the constant `2πi` survive as the
a.e. identity `(ξ j)·(A i) =ᵐ (frequencyUnit / 2πi)·(C j i)`. -/
theorem memLp_coord_smul_datum {s : ℝ} {z : Space → Space} {w : Fin 3 → Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A)
    {C : Fin 3 → RealVectorSobolev s} (hC : ∀ j, IsSobolevDatum s (w j) (C j))
    (hw : ∀ (j i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w j x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ)) :
    ∀ (i j : Fin 3),
      MemLp (fun ξ => (ξ j : ℂ) • (((A i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ)
        2 volume := by
  intro i j
  have hc0 : (0 : ℝ) < frequencyUnit := frequencyUnit_pos
  set c := frequencyUnit with hc
  have hdb := db_cycles_full j hA (hC j) (hw j) i
  set f : FourierData := (cyclesToAngular s).symm ((A i : RealSobolevHilbert s) : FourierData)
    with hfdef
  set g : FourierData := (cyclesToAngular s).symm ((C j i : RealSobolevHilbert s) : FourierData)
    with hgdef
  set κm : ℝ≥0∞ := ENNReal.ofReal (|(c⁻¹ ^ (Module.finrank ℝ Space))⁻¹|) with hκm
  have hMP : MeasurePreserving (fun ξ : Space => c⁻¹ • ξ) volume (κm • volume) :=
    ⟨(continuous_const_smul _).measurable, Measure.map_addHaar_smul volume (inv_ne_zero hc0.ne')⟩
  -- Identify `A i` and `C j i` with the dilation of their weighted cycles forms.
  have hAeq : angularFrequencyDilation (angularWeightEquiv s f)
      = ((A i : RealSobolevHilbert s) : FourierData) := by
    have h : cyclesToAngular s f = angularFrequencyDilation (angularWeightEquiv s f) := rfl
    rw [← h, hfdef]; exact (cyclesToAngular s).apply_symm_apply _
  have hCeq : angularFrequencyDilation (angularWeightEquiv s g)
      = ((C j i : RealSobolevHilbert s) : FourierData) := by
    have h : cyclesToAngular s g = angularFrequencyDilation (angularWeightEquiv s g) := rfl
    rw [← h, hgdef]; exact (cyclesToAngular s).apply_symm_apply _
  have hcoeA := angularFrequencyDilation_coeFn (angularWeightEquiv s f)
  have hcoeC := angularFrequencyDilation_coeFn (angularWeightEquiv s g)
  rw [hAeq] at hcoeA
  rw [hCeq] at hcoeC
  have hwA : ∀ᵐ ξ : Space ∂volume,
      ((angularWeightEquiv s f : FourierData) : Space → ℂ) (c⁻¹ • ξ)
        = angularWeightSymbol s (c⁻¹ • ξ) * (f (c⁻¹ • ξ)) :=
    hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure (angularWeightEquiv_coeFn s f) κm)
  have hwC : ∀ᵐ ξ : Space ∂volume,
      ((angularWeightEquiv s g : FourierData) : Space → ℂ) (c⁻¹ • ξ)
        = angularWeightSymbol s (c⁻¹ • ξ) * (g (c⁻¹ • ξ)) :=
    hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure (angularWeightEquiv_coeFn s g) κm)
  have hI : ∀ᵐ ξ : Space ∂volume,
      (2 * (Real.pi : ℂ) * Complex.I) * (((c⁻¹ • ξ) j : ℝ) : ℂ) * (f (c⁻¹ • ξ))
        = g (c⁻¹ • ξ) := hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure hdb κm)
  -- The angular a.e. identity, division-free: `(2πi)·(ξ j • A i) = c·(C j i)`.
  have heq : (fun ξ => (2 * (Real.pi : ℂ) * Complex.I) *
        ((ξ j : ℂ) • (((A i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ)) =ᵐ[volume]
      fun ξ => ((c : ℝ) : ℂ) * (((C j i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ := by
    filter_upwards [hcoeA, hcoeC, hwA, hwC, hI] with ξ eA eC ewA ewC eI
    rw [eA, ewA, eC, ewC]
    have hcoord : (((c⁻¹ • ξ) j : ℝ) : ℂ) = ((c⁻¹ : ℝ) : ℂ) * ((ξ j : ℝ) : ℂ) := by
      rw [show ((c⁻¹ • ξ) j : ℝ) = c⁻¹ * ξ j from rfl, Complex.ofReal_mul]
    rw [hcoord] at eI
    have hcc : ((c⁻¹ : ℝ) : ℂ) * ((c : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hc0.ne', Complex.ofReal_one]
    simp only [Complex.real_smul, smul_eq_mul]
    linear_combination
        (((c : ℝ) : ℂ) * ((c ^ (-3/2 : ℝ) : ℝ) : ℂ) * angularWeightSymbol s (c⁻¹ • ξ)) * eI
      - ((2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ) * ((c ^ (-3/2 : ℝ) : ℝ) : ℂ)
          * angularWeightSymbol s (c⁻¹ • ξ) * (f (c⁻¹ • ξ))) * hcc
  have h2ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have hRmem : MemLp (fun ξ => ((c : ℝ) : ℂ) *
      (((C j i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ) 2 volume := by
    have h := (Lp.memLp ((C j i : RealSobolevHilbert s) : FourierData)).const_smul ((c : ℝ) : ℂ)
    refine (memLp_congr_ae ?_).mp h
    filter_upwards with ξ; rw [Pi.smul_apply, smul_eq_mul]
  have hLmem : MemLp (fun ξ => (2 * (Real.pi : ℂ) * Complex.I) *
      ((ξ j : ℂ) • (((A i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ)) 2 volume :=
    (memLp_congr_ae heq).mpr hRmem
  have hfin := hLmem.const_smul (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  refine (memLp_congr_ae ?_).mp hfin
  filter_upwards with ξ
  rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h2ne, one_mul]

/-! ## 2. The finite-order constructor (row D-close, C1b-m-D)

The hypothesis exposed to the Euler side is the iterated Schwartz-pairing weak-derivative predicate
`HasWeakDerivsL2`; the constructor is proved by induction on the order. -/

/-- **The Euler-facing hypothesis.**  `HasWeakDerivsL2 z m` says `z ∈ L²` and, if `m = k+1`, for
each coordinate `j` there is an `L²` field `w` that is the weak `j`-th derivative of `z` (in the
Schwartz-pairing sense `∫ψ·wᵢ = ∫(−∂ⱼψ)·zᵢ`) and itself has weak `L²` derivatives up to order `k`.
This is the iterated form of the pairing hypothesis of `db_cycles_full`; it is what the Euler side
delivers (`research/A01/C1B_SPLIT.md` rows C1b-m-E / D-euler-pairing: `word_hasDerivAt` gives the
strong `L²` translation derivative of each descended word, whence the Schwartz pairing by parts). -/
def HasWeakDerivsL2 (z : Space → Space) : ℕ → Prop
  | 0 => MemLp z 2 volume
  | (m + 1) => MemLp z 2 volume ∧ ∀ j : Fin 3, ∃ w : Space → Space,
      HasWeakDerivsL2 w m ∧
      (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
        ∫ x, ψ x * ((w x i : ℝ) : ℂ)
          = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ))

/-- `HasWeakDerivsL2` is monotone in the order: one fewer order of regularity still holds. -/
theorem weakDerivs_mono : ∀ (m : ℕ) (z : Space → Space),
    HasWeakDerivsL2 z (m + 1) → HasWeakDerivsL2 z m
  | 0, _, h => h.1
  | (m + 1), z, h => ⟨h.1, fun j => by
      obtain ⟨w, hw, hp⟩ := h.2 j
      exact ⟨w, weakDerivs_mono m w hw, hp⟩⟩

/-- **C1b-m-D, the finite-order angular Sobolev datum constructor.**  A field `z` with `L²` weak
derivatives up to order `m` (`HasWeakDerivsL2 z m`) has an order-`m` angular real-vector Sobolev
datum.  By induction on `m`: the order-`0` seed is `orderZeroDatum`; the step applies the induction
hypothesis to `z` and to each weak derivative `∂ⱼz`, transports the resulting cycles identity to the
raw angular variable (`memLp_coord_smul_datum`), assembles the raising witness
(`raisableWitness_of_memLp_smul`) and raises (`isSobolevDatum_raise`). -/
theorem exists_isSobolevDatum_of_memLp_derivs :
    ∀ (m : ℕ) (z : Space → Space), HasWeakDerivsL2 z m →
      ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) z A
  | 0, z, hz => by
      have hz0 : MemLp z 2 volume := hz
      rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) from Nat.cast_zero]
      exact ⟨orderZeroDatum hz0, isSobolevDatum_orderZeroDatum hz0⟩
  | (m + 1), z, hz => by
      have hzm : HasWeakDerivsL2 z m := weakDerivs_mono m z hz
      obtain ⟨-, hstep⟩ := hz
      obtain ⟨A, hA⟩ := exists_isSobolevDatum_of_memLp_derivs m z hzm
      choose w hwwd hwpair using hstep
      have hCex : ∀ j, ∃ Cj : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) (w j) Cj :=
        fun j => exists_isSobolevDatum_of_memLp_derivs m (w j) (hwwd j)
      choose C hCd using hCex
      have hcoord := memLp_coord_smul_datum hA hCd hwpair
      have hg : ∀ i, RaisableWitness ((A i : RealSobolevHilbert (m : ℝ)) : FourierData) :=
        fun i => raisableWitness_of_memLp_smul _ (fun j => hcoord i j)
      rw [show (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 from by push_cast; ring]
      exact ⟨_, isSobolevDatum_raise hA hg⟩

/-! ## 3. Non-vacuity and consistency

Every `SmoothL2Field` satisfies `HasWeakDerivsL2 z m` for all `m`, and the datum
`exists_isSobolevDatum_of_memLp_derivs` produces then agrees with `smoothAngularDatum` by
uniqueness of the datum. -/

section NonVacuity

open EulerLpTranslation
open NSFormalization.Source.PhysicalSobolevDistribution
open NSFormalization.Source.PhysicalIntegerSobolev

/-- The Schwartz-pairing weak-derivative identity for a smooth `L²` field: integration by parts
against a test function, packaged for `HasWeakDerivsL2`.  This is the reversal of the realization
chain of `DerivativeDatum.isSobolevDatum_partialDeriv`, using
`Source.PhysicalSobolevDistribution.physicalDistribution_directionalField`. -/
theorem smoothField_weakDeriv_pairing (Z : SmoothL2Field Space) (j i : Fin 3)
    (ψ : SchwartzMap Space ℂ) :
    ∫ x, ψ x * (((Z.directionalField (coordinateVector j)).field x i : ℝ) : ℂ)
      = ∫ x, (-∂_{coordinateVector j} ψ) x * ((Z.field x i : ℝ) : ℂ) := by
  have hlhs : physicalDistribution ((componentField i Z).directionalField (coordinateVector j)) ψ
      = ∫ x, ψ x * (((Z.directionalField (coordinateVector j)).field x i : ℝ) : ℂ) := by
    rw [physicalDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [← componentField_directionalField, componentField_field, smul_eq_mul]
  have hrhs : physicalDistribution (componentField i Z) (-∂_{coordinateVector j} ψ)
      = ∫ x, (-∂_{coordinateVector j} ψ) x * ((Z.field x i : ℝ) : ℂ) := by
    rw [physicalDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [componentField_field, smul_eq_mul]
  rw [← hlhs, ← hrhs, physicalDistribution_directionalField,
    TemperedDistribution.lineDerivOp_apply_apply]

/-- **Non-vacuity.**  Every `SmoothL2Field` satisfies the Euler-facing hypothesis to all orders. -/
theorem weakDerivs_smooth : ∀ (m : ℕ) (Z : SmoothL2Field Space),
    HasWeakDerivsL2 Z.field m
  | 0, Z => Z.memLp
  | (m + 1), Z =>
      ⟨Z.memLp, fun j => ⟨(Z.directionalField (coordinateVector j)).field,
        weakDerivs_smooth m (Z.directionalField (coordinateVector j)),
        fun i ψ => smoothField_weakDeriv_pairing Z j i ψ⟩⟩

/-- **Consistency.**  On a `SmoothL2Field`, the finite-order constructor produces a datum, and by
uniqueness it is exactly the all-orders `smoothAngularDatum` at that order. -/
example (Z : SmoothL2Field Space) (m : ℕ) :
    ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) Z.field A ∧
      A = smoothAngularDatum m (m : ℝ) le_rfl Z := by
  obtain ⟨A, hA⟩ := exists_isSobolevDatum_of_memLp_derivs m Z.field (weakDerivs_smooth m Z)
  exact ⟨A, hA, isSobolevDatum_unique hA (smoothAngularDatum_isSobolevDatum m (m : ℝ) le_rfl Z)⟩

/-- Non-vacuity, stated directly: the hypothesis class is inhabited at every order. -/
example (Z : SmoothL2Field Space) (m : ℕ) : HasWeakDerivsL2 Z.field m := weakDerivs_smooth m Z

end NonVacuity

end NSFormalization.Section4.D01
