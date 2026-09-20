import NSFormalization.Section4.R44.JWeight
import NSFormalization.Section4.A04.RestartFixedForce
import NSFormalization.Section4.A04.NonlinearPairing
import NSFormalization.Section4.R43.CriticalDatumPath
import NSFormalization.Section4.A04.PressureDrop
import NSFormalization.Section4.A04.ZeroSolution

/-! # Inhomogeneous half-order energy along a classical solution

All realization assertions are restricted to the classical lifespan. The total
chosen datum is zero only when no datum exists; its values outside the lifespan
are never used in a differentiation argument.
-/
noncomputable section
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open scoped ContDiff RealInnerProductSpace LineDeriv SchwartzMap
namespace NSFormalization.Section4.R44
open A02 (SpatialField SpaceTimeField ClassicalSolutionR)
open D01
open A03 (partialDeriv)

/-- Unique Sobolev realization, with a total default outside its domain. -/
def energyDatum (s : ℝ) (z : SpatialField) : RealVectorSobolev s := by
  classical
  exact if h : ∃ A, IsSobolevDatum s z A then h.choose else 0

theorem energyDatum_eq {s : ℝ} {z : SpatialField} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A) : energyDatum s z = A := by
  classical
  rw [energyDatum, dite_eq_left ⟨A, hA⟩]
  exact isSobolevDatum_unique (Exists.choose_spec (show ∃ A, IsSobolevDatum s z A from ⟨A, hA⟩)) hA

theorem energyDatum_isDatum {s : ℝ} {z : SpatialField}
    (hz : A05.SmoothL2 z) : IsSobolevDatum s z (energyDatum s z) := by
  obtain ⟨A, hA⟩ := exists_isSobolevDatum_of_contDiff_memLp hz.1 hz.2 s
  rw [energyDatum_eq hA]
  exact hA

theorem energyDatum_eq_lower {s r : ℝ} (hrs : r ≤ s) {z : SpatialField}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) :
    energyDatum r z = lowerVectorL s r hrs A :=
  energyDatum_eq (Leray.isSobolevDatum_lower hrs hA)

/-- Canonical inhomogeneous velocity path. -/
def energyVelocity {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (s t : ℝ) : RealVectorSobolev s :=
  energyDatum s (fun x => w.velocity (t, x))

theorem energyVelocity_isDatum {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (s : ℝ) {t : ℝ} (ht : t ∈ Ico 0 T) :
    IsSobolevDatum s (fun x => w.velocity (t, x)) (energyVelocity w s t) :=
  energyDatum_isDatum (C01.velocity_slice_smoothL2 w ht)

theorem energyVelocity_smooth {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T)
    {s : ℝ} (hs : s ≤ 2) :
    ContDiffOn ℝ ∞ (energyVelocity w s) (Ico 0 T) := by
  obtain ⟨G, hG, hGc⟩ := A04.classical_hasSmoothSobolevPath hν hf w 2
  exact ((lowerVectorL 2 s hs).contDiff.comp_contDiffOn hGc).congr
    (fun t ht => energyDatum_eq_lower hs (hG t ht))

/-- The S1a datum package on each valid slice. -/
def jWeightDatumPath {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (hf : A02.MemForceR f)
    (t : ℝ) (ht : t ∈ Ico 0 T) :
    JWeightDatum (fun x => w.velocity (t, x)) (fun x => f (t, x)) := by
  let U : EulerLpTranslation.SmoothL2Field Space :=
    ⟨_, (C01.velocity_slice_smoothL2 w ht).1, (C01.velocity_slice_smoothL2 w ht).2⟩
  refine ⟨energyVelocity w (1/2) t, energyVelocity w (3/2) t,
    (fun j => energyDatum (1/2) (partialDeriv j U.field)),
    energyDatum (-1/2) (fun x => f (t,x)),
    energyVelocity_isDatum w _ ht, energyVelocity_isDatum w _ ht, ?_,
    energyDatum_isDatum (forceSlice_smoothL2_of_memForceR hf ht.1), ?_⟩
  · intro j
    apply energyDatum_isDatum
    exact ⟨(U.directionalField (coordinateVector j)).smooth,
      (U.directionalField (coordinateVector j)).integrable⟩
  · intro j i ψ
    rw [A03.partialDeriv_eq_dirDeriv]
    exact smoothField_weakDeriv_pairing U j i ψ

/-- The selected force datum is exactly the lowering of the order-six force
path supplied by `MemForceR`, by uniqueness of Sobolev realization. -/
theorem jWeightDatumPath_force_eq_lower {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (hf : A02.MemForceR f)
    {t : ℝ} (ht : t ∈ Ico 0 T) {F : RealVectorSobolev 6}
    (hF : IsSobolevDatum 6 (fun x => f (t,x)) F) :
    (jWeightDatumPath w hf t ht).forceNegHalf = lowerVectorL 6 (-1/2) (by norm_num) F :=
  energyDatum_eq_lower (by norm_num) hF

/-- Differentiation of the paper's actual norm, rather than a replacement norm. -/
theorem hasDerivAt_Y_sq {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => Y (fun x => w.velocity (r,x)) ^ 2)
      (2 * ⟪energyVelocity w (1/2) t, deriv (energyVelocity w (1/2)) t⟫) t := by
  refine (A04.hasDerivAt_datumNormSq_of_contDiffOn
    (energyVelocity_smooth hν hf w (by norm_num : (1/2 : ℝ) ≤ 2)) ht).congr_of_eventuallyEq ?_
  filter_upwards [Ico_mem_nhds ht.1 ht.2] with r hr
  rw [Y_eq_norm (jWeightDatumPath w hf r hr)]
  rfl

/-- Transport of the exact order-two momentum equation. -/
theorem energyVelocity_momentum {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    {L N P F : RealVectorSobolev 2}
    (hL : IsSobolevDatum 2 (fun x => spatialLaplacian w.velocity t x) L)
    (hN : IsSobolevDatum 2 (fun x => advection w.velocity t x) N)
    (hP : IsSobolevDatum 2 (fun x => pressureGradient w.pressure t x) P)
    (hF : IsSobolevDatum 2 (fun x => f (t,x)) F) :
    deriv (energyVelocity w (1/2)) t =
      lowerVectorL 2 (1/2) (by norm_num) (ν • L - N - P + F) := by
  obtain ⟨G, hG, hGc⟩ := A04.classical_hasSmoothSobolevPath hν hf w 2
  have hm := A04.momentum_datum w hf (m := 2) (by norm_num) hG hGc ht hL hN hP hF
  have hd := (lowerVectorL 2 (1/2) (by norm_num)).hasFDerivAt.comp_hasDerivAt t
    (A04.hasDerivAt_datumPath hGc ht)
  have heq : energyVelocity w (1/2) =ᶠ[nhds t]
      (fun r => lowerVectorL 2 (1/2) (by norm_num) (G r)) := by
    filter_upwards [Ico_mem_nhds ht.1 ht.2] with r hr
    exact energyDatum_eq_lower (by norm_num) (hG r hr)
  rw [(hd.congr_of_eventuallyEq heq).deriv, hm]

/-- Redistribution of Bessel weights between the two slots. -/
theorem inner_eq_jPairing (U V : RealVectorSobolev 2) :
    ⟪lowerVectorL 2 (1/2) (by norm_num) U,
      lowerVectorL 2 (1/2) (by norm_num) V⟫ =
    ⟪lowerVectorL 2 (-1/2) (by norm_num) V,
      Jmul (lowerVectorL 2 (3/2) (by norm_num) U)⟫ := by
  rw [real_inner_comm]
  simp only [PiLp.inner_apply, Jmul, realSobolev_inner_eq_ambient, A04.coe_lowerVectorL]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_lowering_transfer 2 2 (1/2) (1/2) (-1/2) (3/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _

/-- Half-order dissipation reconciliation on one scalar component. -/
theorem half_laplacian_component (A : FourierData) (e : Space) :
    ⟪angularOrderLowering 4 (1/2) (by norm_num) A,
      angularOrderLowering 2 (1/2) (by norm_num)
        (angularDirectionalDerivative 3 e (angularDirectionalDerivative 4 e A))⟫ =
      -‖angularOrderLowering 3 (1/2) (by norm_num)
        (angularDirectionalDerivative 4 e A)‖ ^ 2 := by
  rw [real_inner_lowering_transfer 4 2 (1/2) (1/2) (-1) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    angularOrderLowering_self, real_inner_angularDirectionalDerivative,
    A04.directionalDerivative_orderLowering_comm 3 4 4 (-1) e
      (by norm_num) (by norm_num)]
  congr 1
  have h := real_inner_lowering_pairing 3 (-2) 3
    (by norm_num) (by norm_num) (by norm_num) (angularDirectionalDerivative 4 e A)
  norm_num only at h
  simpa only [angularOrderLowering_self, show (4 - 1 : ℝ) = 3 by norm_num,
    show (-1 - 1 : ℝ) = -2 by norm_num] using h

-- The nested order-four jet coercions require more than the default budget.
set_option maxHeartbeats 400000 in
/-- Exact half-order Laplacian pairing, obtained by lowering order-four jets. -/
theorem laplacian_jPairing {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (hf : A02.MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo 0 T) {L : RealVectorSobolev 2}
    (hL : IsSobolevDatum 2 (fun x => spatialLaplacian w.velocity t x) L) :
    ⟪lowerVectorL 2 (-1/2) (by norm_num) L,
      Jmul (energyVelocity w (3/2) t)⟫ = - Z (fun x => w.velocity (t,x)) ^ 2 := by
  let U : EulerLpTranslation.SmoothL2Field Space :=
    ⟨_, (C01.velocity_slice_smoothL2 w ⟨ht.1.le, ht.2⟩).1,
      (C01.velocity_slice_smoothL2 w ⟨ht.1.le, ht.2⟩).2⟩
  let A := energyVelocity w 4 t
  have hA : IsSobolevDatum 4 U.field A := energyVelocity_isDatum w 4 ⟨ht.1.le, ht.2⟩
  have hL' : L = A04.laplacianDatum 2 A :=
    isSobolevDatum_unique hL (A04.isSobolevDatum_laplacian (Z := U) 2
      (by
        erw [show ((2 : ℕ) + 2 : ℝ) = 4 by norm_num]
        exact hA))
  have hgrad : ∀ j, (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩).gradientHalf j =
      lowerVectorL 3 (1/2) (by norm_num) (A04.derivDatumStep 3 j A) := by
    intro j
    exact energyDatum_eq_lower (by norm_num) (isSobolevDatum_partialDeriv (Z := U) j 3
      (by
        erw [show ((3 : ℕ) + 1 : ℝ) = 4 by norm_num]
        exact hA))
  rw [show energyVelocity w (3/2) t = lowerVectorL 2 (3/2) (by norm_num)
      (energyVelocity w 2 t) from energyDatum_eq_lower (by norm_num)
        (energyVelocity_isDatum w 2 ⟨ht.1.le, ht.2⟩), ← inner_eq_jPairing,
    show lowerVectorL 2 (1/2) (by norm_num) (energyVelocity w 2 t) =
      lowerVectorL 4 (1/2) (by norm_num) A from
        (energyDatum_eq_lower (by norm_num) (energyVelocity_isDatum w 2 ⟨ht.1.le, ht.2⟩)).symm.trans
          (energyDatum_eq_lower (by norm_num) hA),
    hL', Z_sq_eq_sum_norm (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)]
  simp only [hgrad, A04.laplacianDatum, map_sum, inner_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ _ _ = -‖((lowerVectorL 3 (1/2) (by norm_num)
    (A04.derivDatumStep 3 j A)) i : FourierData)‖ ^ 2
  simp only [realSobolev_inner_eq_ambient, A04.coe_lowerVectorL,
    A04.coe_derivDatumStep, A04.castOrder_coe]
  convert half_laplacian_component (A i : FourierData) (coordinateVector j) using 1 <;> norm_num
  · erw [A04.castOrder_coe]
  · erw [A04.coe_derivDatumStep]
    norm_num

/-- The pressure datum pairs to zero after redistribution of the weights. -/
theorem pressure_jPairing_zero {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (hf : A02.MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo 0 T) {P : RealVectorSobolev 2}
    (hP : IsSobolevDatum 2 (fun x => pressureGradient w.pressure t x) P) :
    ⟪lowerVectorL 2 (-1/2) (by norm_num) P,
      Jmul (energyVelocity w (3/2) t)⟫ = 0 := by
  obtain ⟨_, hjets⟩ := memHInfty_iff_smoothSquareIntegrableJets.mpr
    (smoothL2_momentumResidual_slice w hf ht)
  obtain ⟨A, hA⟩ := hjets 2
  have hp := pin_pressureGradient_datum w hf ht hA hP
  have hu := A04.velocity_datum_lerayComplement_eq_zero w ht
    (energyVelocity_isDatum w 2 ⟨ht.1.le, ht.2⟩)
  change P = Leray.lerayComplement 2 A at hp
  change Leray.lerayComplement 2 (energyVelocity w 2 t) = 0 at hu
  have hul : Leray.lerayComplement (3/2) (energyVelocity w (3/2) t) = 0 := by
    rw [show energyVelocity w (3/2) t = lowerVectorL 2 (3/2) (by norm_num)
      (energyVelocity w 2 t) from energyDatum_eq_lower (by norm_num)
        (energyVelocity_isDatum w 2 ⟨ht.1.le, ht.2⟩),
      Leray.lerayComplement_lowerVectorL, hu, map_zero]
  change Leray.lerayComplement (-1/2) (Jmul (energyVelocity w (3/2) t)) = 0 at hul
  change inner ℝ (lowerVectorL 2 (-1/2) (by norm_num) P)
    (energyVelocity w (3/2) t) = 0
  have hpLow := Leray.lerayComplement_lowerVectorL 2 (-1/2) (by norm_num) A
  rw [hp]
  rw [← hpLow]
  exact (real_inner_comm _ _).trans
    (A04.inner_lerayComplement_eq_zero_of_eq_zero (-1/2) _ _ hul)

/-- Advection paired with physical `Ju`, in the same dual carrier as the force. -/
def energyAdvectionJPairing {u f : SpatialField} (h : JWeightDatum u f)
    (N : RealVectorSobolev (-1/2)) : ℝ := ⟪N, Jmul h.velocityThreeHalf⟫

-- Momentum expansion and the shared phantom-order carrier need additional elaboration.
set_option maxHeartbeats 400000 in
/-- Datum-level energy identity with explicit order-two momentum data. -/
theorem energy_identity_of_data {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Ioo 0 T) {L N P F : RealVectorSobolev 2}
    (hL : IsSobolevDatum 2 (fun x => spatialLaplacian w.velocity t x) L)
    (hN : IsSobolevDatum 2 (fun x => advection w.velocity t x) N)
    (hP : IsSobolevDatum 2 (fun x => pressureGradient w.pressure t x) P)
    (hF : IsSobolevDatum 2 (fun x => f (t,x)) F) :
    HasDerivAt (fun r => Y (fun x => w.velocity (r,x)) ^ 2)
      (-2 * ν * Z (fun x => w.velocity (t,x)) ^ 2 -
        2 * energyAdvectionJPairing (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)
          (lowerVectorL 2 (-1/2) (by norm_num) N) +
        2 * forceJPairing (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)) t := by
  have hd := hasDerivAt_Y_sq hν hf w ht
  rw [energyVelocity_momentum hν hf w ht hL hN hP hF,
    show energyVelocity w (1/2) t = lowerVectorL 2 (1/2) (by norm_num)
      (energyVelocity w 2 t) from energyDatum_eq_lower (by norm_num)
        (energyVelocity_isDatum w 2 ⟨ht.1.le, ht.2⟩), inner_eq_jPairing] at hd
  have hu : lowerVectorL 2 (3/2) (by norm_num) (energyVelocity w 2 t) =
      energyVelocity w (3/2) t :=
    (energyDatum_eq_lower (by norm_num) (energyVelocity_isDatum w 2 ⟨ht.1.le, ht.2⟩)).symm
  rw [hu, map_add, map_sub, map_sub, map_smul] at hd
  let V : RealVectorSobolev (-1/2) := Jmul (energyVelocity w (3/2) t)
  change HasDerivAt _ (2 * inner ℝ
    (ν • lowerVectorL 2 (-1/2) (by norm_num) L -
      lowerVectorL 2 (-1/2) (by norm_num) N -
      lowerVectorL 2 (-1/2) (by norm_num) P +
      lowerVectorL 2 (-1/2) (by norm_num) F) V) t at hd
  rw [inner_add_left, inner_sub_left, inner_sub_left, real_inner_smul_left] at hd
  have hl : inner ℝ (lowerVectorL 2 (-1/2) (by norm_num) L) V =
      -Z (fun x => w.velocity (t,x)) ^ 2 := laplacian_jPairing w hf ht hL
  have hp : inner ℝ (lowerVectorL 2 (-1/2) (by norm_num) P) V = 0 :=
    pressure_jPairing_zero w hf ht hP
  simp only [hl, hp] at hd
  have hforce : lowerVectorL 2 (-1/2) (by norm_num) F =
      (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩).forceNegHalf :=
    (energyDatum_eq_lower (by norm_num) hF).symm
  rw [hforce] at hd
  convert hd using 1
  simp only [energyAdvectionJPairing, forceJPairing, jWeightDatumPath]
  ring

/-- The exact `Ju` energy identity on the classical lifespan, without additional
analytic hypotheses. The nonlinear term is the same real pairing as lane 220's
`advectionJPairing h ha`, with `ha.advectionNegHalf` chosen canonically here. -/
theorem energy_identity {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => Y (fun x => w.velocity (r,x)) ^ 2)
      (-2 * ν * Z (fun x => w.velocity (t,x)) ^ 2 -
        2 * energyAdvectionJPairing (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)
          (energyDatum (-1/2) (fun x => advection w.velocity t x)) +
        2 * forceJPairing (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)) t := by
  obtain ⟨P, hP⟩ := exists_isSobolevDatum_pressureGradient_slice w hf ht 2
  have hL := energyDatum_isDatum (s := 2) (laplacian_slice_smoothL2 w ht)
  have hN := energyDatum_isDatum (s := 2) (advection_slice_smoothL2 w ht)
  have hF := energyDatum_isDatum (s := 2) (forceSlice_smoothL2_of_memForceR hf ht.1.le)
  rw [energyDatum_eq_lower (by norm_num : (-1/2 : ℝ) ≤ 2) hN]
  exact energy_identity_of_data hν hf w ht hL hN hP hF

/-- The canonical datum of the zero field is zero at every order. -/
theorem energyDatum_zero (s : ℝ) : energyDatum s (0 : SpatialField) = 0 :=
  energyDatum_eq (isSobolevDatum_zero s)

/-- All four terms of the zero solution's energy identity vanish. -/
theorem zero_energy_terms (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    Y (fun x => (A04.zeroSol ν T hν hT).velocity (t,x)) = 0 ∧
    Z (fun x => (A04.zeroSol ν T hν hT).velocity (t,x)) = 0 ∧
    energyAdvectionJPairing
      (jWeightDatumPath (A04.zeroSol ν T hν hT) A04.memForceR_zero t ht)
      (energyDatum (-1/2) (fun x => advection (A04.zeroSol ν T hν hT).velocity t x)) = 0 ∧
    forceJPairing (jWeightDatumPath (A04.zeroSol ν T hν hT)
      A04.memForceR_zero t ht) = 0 := by
  have hu : energyVelocity (A04.zeroSol ν T hν hT) (3/2) t = 0 := energyDatum_zero _
  have hy : Y (0 : SpatialField) = 0 := by
    erw [Y, sobolevENorm_eq_of_isSobolevDatum (isSobolevDatum_zero (1/2))]
    simp
  have hz : Z (0 : SpatialField) = 0 := by
    have hh := weight_identity (jWeightDatumPath (A04.zeroSol ν T hν hT)
      A04.memForceR_zero t ht)
    change (sobolevENorm (3/2) (0 : SpatialField)).toReal ^ 2 =
      Y (0 : SpatialField) ^ 2 + Z (0 : SpatialField) ^ 2 at hh
    erw [sobolevENorm_eq_of_isSobolevDatum (isSobolevDatum_zero (3/2)), hy] at hh
    simpa using hh.symm
  refine ⟨hy, hz, ?_, ?_⟩
  · change inner ℝ _ (Jmul (energyVelocity (A04.zeroSol ν T hν hT) (3/2) t)) = 0
    rw [hu]
    exact inner_zero_right _
  · change inner ℝ _ (Jmul (energyVelocity (A04.zeroSol ν T hν hT) (3/2) t)) = 0
    rw [hu]
    exact inner_zero_right _

end NSFormalization.Section4.R44
