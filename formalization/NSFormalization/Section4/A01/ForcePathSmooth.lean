import NSFormalization.Section4.A01.ForceBridge

/-!
# Smoothness in time of the canonical cylinder force path

`D01.MemForceR f` supplies, at every integer order `q`, a datum path which is smooth in
time on `Ici 0`.  This module packages the fixed bounded-linear reconstruction from such an
order-`q` datum to the vendor's unit-cylinder `SobolevSpace 1 q`.  On a datum which represents a
smooth physical field, the reconstruction is exactly `ordinarySobolev q` of that field.  Applying
it to the datum path supplied by `MemForceR` proves the `ContDiffOn` hypothesis consumed by the
A01 time-regularity ladder.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.D01
open NSFormalization.Source.RealSobolev
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerLpDerivative
open EulerMeanSolenoidal EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerVolterraConvolution EulerSmoothFieldSobolevTime
open scoped ContDiff Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {f : A02.SpaceTimeField} {S : ℝ}

/-! ## 1. Bounded-linear reconstruction of the cylinder Sobolev array -/

/-- The datum-to-physical-jet operation, bundled as a continuous linear map. -/
def jetOfDatumCLM (m j : ℕ) (hj : j ≤ m) :
    RealVectorSobolev (m : ℝ) →L[ℝ]
      Lp (Space [×j]→L[ℝ] Space) 2 (volume : Measure Space) :=
  LinearMap.mkContinuous
    { toFun := D01.jetOfDatum m j hj
      map_add' := by
        intro A B
        simp only [D01.jetOfDatum, D01.loweredComponent, D01.cyclesComponentOfAngular]
        simp only [PiLp.add_apply, AddMemClass.coe_add, map_add]
        rw [← map_add]
        congr 1
      map_smul' := by
        intro c A
        simp only [D01.jetOfDatum, D01.loweredComponent, D01.cyclesComponentOfAngular]
        simp only [PiLp.smul_apply, SetLike.val_smul, RingHom.id_apply]
        rw [← map_smul]
        congr 1
        funext i
        change (sobolevOrderLowering (m : ℝ) (j : ℝ) _)
            ((cyclesToAngular (m : ℝ)).symm (c • (A i : FourierData))) =
          c • (sobolevOrderLowering (m : ℝ) (j : ℝ) _)
            ((cyclesToAngular (m : ℝ)).symm (A i : FourierData))
        calc
          _ = (sobolevOrderLowering (m : ℝ) (j : ℝ) _)
              (c • (cyclesToAngular (m : ℝ)).symm (A i : FourierData)) := by
                congr 1
                exact (cyclesToAngular (m : ℝ)).symm.toContinuousLinearMap.map_smul_of_tower
                  c (A i : FourierData)
          _ = _ := (sobolevOrderLowering (m : ℝ) (j : ℝ) _).map_smul_of_tower
            c ((cyclesToAngular (m : ℝ)).symm (A i : FourierData)) }
    (D01.jetDatumConst j m) (D01.norm_jetOfDatum_le m j hj)

@[simp] theorem jetOfDatumCLM_apply (m j : ℕ) (hj : j ≤ m)
    (A : RealVectorSobolev (m : ℝ)) :
    jetOfDatumCLM m j hj A = D01.jetOfDatum m j hj A := rfl

/-- One cylinder derivative word reconstructed from an order-`q` datum.  The physical tensor is
first bundled as an `L²`-valued multilinear map, evaluated on the spatial parts of the four
cylinder coordinate directions, and finally lifted isometrically to the unit cylinder.  Thus an
angular direction (whose spatial part is zero) automatically gives zero. -/
def datumWordCLM (q : ℕ) (w : SobolevWord q) :
    RealVectorSobolev (q : ℝ) →L[ℝ] LiftL2 1 :=
  ordinaryLift.toContinuousLinearMap.comp <|
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.1.val => Space)
      (EulerMeanSolenoidal.L2) (coordinateTuple w.2)).comp <|
      (multilinearBundling (P := Space) (V := Space) volume w.1.val).comp <|
        jetOfDatumCLM q w.1.val (Nat.le_of_lt_succ w.1.isLt)

/-- The ambient finite cylinder derivative array reconstructed continuously and linearly from an
order-`q` datum. -/
def datumArrayCLM (q : ℕ) :
    RealVectorSobolev (q : ℝ) →L[ℝ] (SobolevWord q → LiftL2 1) :=
  ContinuousLinearMap.pi (datumWordCLM q)

/-- The ambient datum reconstruction agrees word-by-word with `ordinarySobolev` whenever the
datum represents the smooth field. -/
theorem datumArrayCLM_eq_ordinarySobolev (q : ℕ) (A : SmoothL2Field Space)
    (G : RealVectorSobolev (q : ℝ)) (hG : IsSobolevDatum (q : ℝ) A.field G) :
    datumArrayCLM q G = (ordinarySobolev q A.toLp A.translation_contDiff).1 := by
  funext w
  change datumArrayCLM q G w =
    (ordinarySobolev q A.toLp
      (show SmoothOrbit A.toLp from A.translation_contDiff)).val w
  rw [ordinarySobolev_coordinate]
  have hjet : D01.jetOfDatum q w.1.val (Nat.le_of_lt_succ w.1.isLt) G = A.jetLp w.1.val := by
    apply Lp.ext
    exact (D01.jetOfDatum_ae (Nat.le_of_lt_succ w.1.isLt) A.smooth hG).trans
      (A.jetLp_ae w.1.val).symm
  simp only [datumArrayCLM, datumWordCLM, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, jetOfDatumCLM_apply, hjet]
  have htrans := A.iteratedFDeriv_translation_eq w.1.val 0
  change iteratedFDeriv ℝ w.1.val
      (fun b : Space => EulerMeanSolenoidal.translation b A.toLp) 0 =
    multilinearBundling volume w.1.val
      (EulerLpTranslation.translation 0 (A.jetLp w.1.val)) at htrans
  rw [htrans]
  simp only [EulerLpTranslation.translation_zero]
  rfl

/-! ### Compatibility for arbitrary finite-order data

The preceding identity proves compatibility on smooth physical data.  Such data are dense in the
complete Fourier datum carrier.  Since the cylinder Sobolev space is a closed submodule and
`datumArrayCLM` is continuous, compatibility extends to every datum. -/

/-- A dense family of angular real-vector data obtained by applying the real projection to three
Schwartz functions in the cycles convention and then changing to the manuscript convention. -/
def schwartzDatum (q : ℕ) (φ : Fin 3 → SchwartzMap Space ℂ) :
    RealVectorSobolev (q : ℝ) :=
  cyclesToAngularRealVector (q : ℝ) <|
    WithLp.toLp 2 fun i => realProjectionTo (q : ℝ) (weightedFourierLp (q : ℝ) (φ i))

theorem denseRange_schwartzDatum (q : ℕ) : DenseRange (schwartzDatum q) := by
  let e : SchwartzMap Space ℂ → RealSobolevHilbert (q : ℝ) :=
    fun φ => realProjectionTo (q : ℝ) (weightedFourierLp (q : ℝ) φ)
  have hr : Function.Surjective (realProjectionTo (q : ℝ)) := by
    intro h
    exact ⟨realSobolevInclusion (q : ℝ) h, realProjectionTo_inclusion (q : ℝ) h⟩
  have he : DenseRange e :=
    hr.denseRange.comp (denseRange_weightedFourierLp (q : ℝ))
      (realProjectionTo (q : ℝ)).continuous
  have hp : DenseRange (Pi.map fun _ : Fin 3 => e) :=
    DenseRange.piMap fun _ => he
  have hpi : DenseRange
      (fun φ : Fin 3 → SchwartzMap Space ℂ =>
        WithLp.toLp 2 fun i => e (φ i)) := by
    have h := (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin 3 => RealSobolevHilbert (q : ℝ))).symm.surjective.denseRange.comp hp
          (PiLp.continuousLinearEquiv 2 ℝ
            (fun _ : Fin 3 => RealSobolevHilbert (q : ℝ))).symm.continuous
    rw [PiLp.coe_symm_continuousLinearEquiv] at h
    rw [show (fun φ : Fin 3 → SchwartzMap Space ℂ => WithLp.toLp 2 fun i => e (φ i)) =
      WithLp.toLp 2 ∘ Pi.map (fun _ : Fin 3 => e) by
        funext φ
        rfl]
    exact h
  have h := (cyclesToAngularRealVector (q : ℝ)).surjective.denseRange.comp hpi
    (cyclesToAngularRealVector (q : ℝ)).continuous
  change DenseRange (fun φ : Fin 3 → SchwartzMap Space ℂ =>
    cyclesToAngularRealVector (q : ℝ)
      (WithLp.toLp 2 fun i => e (φ i)))
  rw [show (fun φ : Fin 3 → SchwartzMap Space ℂ =>
      cyclesToAngularRealVector (q : ℝ) (WithLp.toLp 2 fun i => e (φ i))) =
    (cyclesToAngularRealVector (q : ℝ)) ∘
      (fun φ : Fin 3 → SchwartzMap Space ℂ => WithLp.toLp 2 fun i => e (φ i)) by rfl]
  exact h

/-- The real vector field underlying a triple of complex Schwartz functions. -/
def schwartzRealField (φ : Fin 3 → SchwartzMap Space ℂ) : Space → Space :=
  fun x => WithLp.toLp 2 fun i => (φ i x).re

theorem schwartzRealField_smooth (φ : Fin 3 → SchwartzMap Space ℂ) :
    ContDiff ℝ ∞ (schwartzRealField φ) := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact Complex.reCLM.contDiff.comp ((φ i).smooth (⊤ : ℕ∞))

/-- Every derivative order of a Schwartz triple is represented by its weighted Fourier datum. -/
def schwartzSmoothField (φ : Fin 3 → SchwartzMap Space ℂ) : SmoothL2Field Space :=
  NSFormalization.Source.FourierPhysicalJets.smoothL2FieldOfFourier
    (schwartzRealField φ) (schwartzRealField_smooth φ)
    (fun n i => weightedFourierLp (n : ℝ) (realPartSchwartz (φ i))) (by
      intro n i ψ _hψ
      rw [sobolevRealization_weightedFourierLp]
      simp only [SchwartzMap.coe_apply, schwartzRealField, realPartSchwartz_apply,
        PiLp.toLp_apply, smul_eq_mul])

@[simp] theorem schwartzSmoothField_field (φ : Fin 3 → SchwartzMap Space ℂ) :
    (schwartzSmoothField φ).field = schwartzRealField φ := rfl

/-- The dense Schwartz datum represents the dense Schwartz physical field. -/
theorem schwartzDatum_isSobolevDatum (q : ℕ) (φ : Fin 3 → SchwartzMap Space ℂ) :
    IsSobolevDatum (q : ℝ) (schwartzSmoothField φ).field (schwartzDatum q φ) := by
  intro i ψ
  change angularRealization (q : ℝ)
      ((cyclesToAngularReal (q : ℝ)
        (realProjectionTo (q : ℝ) (weightedFourierLp (q : ℝ) (φ i))) :
          RealSobolevHilbert (q : ℝ)) : FourierData) ψ = _
  rw [angularRealization_cyclesToAngularReal]
  change sobolevRealization (q : ℝ)
      (realProjection (weightedFourierLp (q : ℝ) (φ i))) ψ = _
  rw [← weightedFourierLp_realPart, sobolevRealization_weightedFourierLp]
  simp only [SchwartzMap.coe_apply, schwartzSmoothField_field, schwartzRealField,
    realPartSchwartz_apply, PiLp.toLp_apply, smul_eq_mul]

/-- The ambient array reconstructed from every datum satisfies all closed derivative-graph
constraints defining `SobolevSpace 1 q`. -/
theorem datumArrayCLM_mem_sobolevSubspace (q : ℕ) (G : RealVectorSobolev (q : ℝ)) :
    datumArrayCLM q G ∈ sobolevSubspace 1 q := by
  refine (denseRange_schwartzDatum q).induction_on G
    ((sobolevSubspace 1 q).isClosed.preimage (datumArrayCLM q).continuous) ?_
  intro φ
  rw [datumArrayCLM_eq_ordinarySobolev q (schwartzSmoothField φ) (schwartzDatum q φ)
    (schwartzDatum_isSobolevDatum q φ)]
  exact (ordinarySobolev q (schwartzSmoothField φ).toLp
    (schwartzSmoothField φ).translation_contDiff).property

/-- The order-`q` datum-to-cylinder reconstruction as a fixed continuous linear map. -/
def datumSobolevCLM (q : ℕ) :
    RealVectorSobolev (q : ℝ) →L[ℝ] SobolevSpace 1 q :=
  (datumArrayCLM q).codRestrict (sobolevSubspace 1 q).toSubmodule
    (datumArrayCLM_mem_sobolevSubspace q)

/-- The fixed bounded-linear reconstruction is exactly the vendor's `ordinarySobolev` carrier for
every smooth field represented by the datum. -/
theorem datumSobolevCLM_eq_ordinarySobolev (q : ℕ) (A : SmoothL2Field Space)
    (G : RealVectorSobolev (q : ℝ)) (hG : IsSobolevDatum (q : ℝ) A.field G) :
    datumSobolevCLM q G = ordinarySobolev q A.toLp A.translation_contDiff := by
  apply Subtype.ext
  exact datumArrayCLM_eq_ordinarySobolev q A G hG

/-! ## 2. Smoothness of the force path -/

/-- The canonical cylinder Sobolev force path is `C^∞` in time on its closed horizon.  No lower
bound on `q` is needed: the order-`q` datum path from `MemForceR` is composed with the fixed
continuous linear reconstruction `datumSobolevCLM q`.  On `Icc 0 S`, clamping by `extendPath` is
the identity. -/
theorem forcePath_sobolevPath_contDiffOn (hf : D01.MemForceR f) (hS : 0 < S) (q : ℕ) :
    ContDiffOn ℝ ∞
      (extendPath S hS.le
        (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q))
      (Icc (0 : ℝ) S) := by
  obtain ⟨G, hpath, hGc, _, _⟩ := hf.2 q
  have hcomp : ContDiffOn ℝ ∞ (datumSobolevCLM q ∘ G) (Icc (0 : ℝ) S) :=
    (datumSobolevCLM q).contDiff.comp_contDiffOn hGc |>.mono fun _ ht => ht.1
  apply hcomp.congr
  intro t ht
  simp only [extendPath, projIcc_of_mem hS.le ht, sobolevPath, ContinuousMap.coe_mk,
    Function.comp_apply]
  exact (datumSobolevCLM_eq_ordinarySobolev q (C01.forcePath hf ⟨t, ht⟩) (G t)
    (hpath t ht.1)).symm

/-- Lane 167's force package, extended by the smooth Sobolev-path clause needed by the B1 ladder.
The proof argument `hF` is quantified in the last clause because an ordinary conjunction cannot
make the proof in its second conjunct available as an argument of `sobolevPath` in a later
conjunct.  Proof irrelevance makes the conclusion independent of which proof of jet continuity is
supplied. -/
theorem forcePath_of_memForceR_smooth (hf : D01.MemForceR f) (hS : 0 < S) :
    ∃ F : Icc (0 : ℝ) S → SmoothL2Field Space,
      F = C01.forcePath hf ∧
      (∀ n, Continuous fun t => (F t).jetLp n) ∧
      A04.MemL1Hm f ∧
      ∀ q (_hq : 6 ≤ q),
        ∀ hF : ∀ n, Continuous fun t => (F t).jetLp n,
        ContDiffOn ℝ ∞
          (extendPath S hS.le
            (sobolevPath F hF q))
          (Icc (0 : ℝ) S) := by
  refine ⟨C01.forcePath hf, rfl, C01.forcePath_jetLp_continuous hf,
    A04.memL1Hm_of_memForceR hf, ?_⟩
  intro q _hq _hF
  exact forcePath_sobolevPath_contDiffOn hf hS q

end NSFormalization.Section4.A01
