import NavierStokes.MeanStageContinuation
import NavierStokes.LabelSupportPreservation
import NavierStokes.NativeBandExtension

/-!
# Supported continuation of actual wave stages

The native geometry, entry and exit clocks, and cutoff are retained.
Only primitive coefficient and forcing fields are continued.  Agreement
is on whole positive slow fibers, as needed by the Volterra solve.
-/

noncomputable section

namespace NavierStokes.WaveStageContinuation

open Set Function Filter
open HarmonicCalculus CommonCoverSolve TorusInverse WeightedClasses
open scoped Topology ContDiff BigOperators ComplexConjugate

abbrev Slow := TorusInverse.Plane
abbrev Point := LocalSignedRequest.Point
abbrev Parameter := ℝ × Slow
abbrev Chart := Parameter × Plane

noncomputable def toChart (x : Point) : Chart := ((x.1, x.2.1), x.2.2)
noncomputable def ofChart (x : Chart) : Point := (x.1.1, (x.1.2, x.2))

theorem toChart_smooth : ContDiff ℝ ∞ toChart :=
  (contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd

theorem ofChart_smooth : ContDiff ℝ ∞ ofChart :=
  contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)

def RadialSupport {E : Type*} [Zero E] (a b : ℝ) (ell : Slow → ℝ)
    (U : Set Slow) (f : Point → E) : Prop :=
  ∀ x, x.2.1 ∈ U → f x ≠ 0 → x.1 ∈ Icc (ell x.2.1 * a) (ell x.2.1 * b)

structure FieldContinuation {coord a b : ℝ}
    (W : OffplaneCorrectionExtensions.Window coord a b)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Point → E) where
  value : Point → E
  smooth : ContDiffOn ℝ ∞ value (PhysicalMeanDomain.slowDomain W.carrier)
  supported : RadialSupport a b (OffplaneCorrectionExtensions.stableLength coord) W.carrier value
  agrees : OffplaneCorrectionExtensions.FiberAgreement W.carrier value f

namespace FieldContinuation

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Point → E}

noncomputable def map (e : FieldContinuation W f) (L : E →L[ℝ] F) :
    FieldContinuation W (fun x => L (f x)) where
  value x := L (e.value x)
  smooth := L.contDiff.comp_contDiffOn e.smooth
  supported := fun x hx hn => e.supported x hx (fun hz => hn (by simp [hz]))
  agrees := fun _ hx => congrArg L (e.agrees hx)

noncomputable def scalar (e : FieldContinuation W f) (L : E →L[ℝ] ℝ) :
    OffplaneCorrectionExtensions.SupportedContinuation W (fun x => L (f x)) where
  value := (e.map L).value
  smooth := (e.map L).smooth
  supported := (e.map L).supported
  agrees := (e.map L).agrees

theorem zero_below (e : FieldContinuation W f) {x : Point}
    (hx : x.2.1 ∈ W.carrier) (hr : x.1 < W.lower) : e.value x = 0 := by
  by_contra hn
  exact (not_lt_of_ge ((W.left _ hx).trans (e.supported x hx hn).1)) hr

end FieldContinuation

section ReferenceSolve

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Fiber equality is enough for the exact anchored solution.  No
agreement of the data at unrelated slow points is required. -/
theorem copySolve_eq_of_fiber (d e : LinearData Parameter V E) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) (k : Frequency) (p : Parameter) (Y : Plane)
    (hA : ∀ Z, d.coefficient (p, Z) = e.coefficient (p, Z))
    (hB : ∀ Z, d.forcingMap (p, Z) = e.forcingMap (p, Z))
    (hf : ∀ Z, d.source (p, Z) = e.source (p, Z)) :
    d.copySolve g hle k (p, Y) = e.copySolve g hle k (p, Y) := by
  have hcoef : d.coefficientPath (a := entry) (b := exit) g k (p, Y) =
      e.coefficientPath g k (p, Y) := by
    apply pathFamily_congr_slice
    intro s
    exact hA _
  have hforce : d.forcingPath (a := entry) (b := exit) g k (p, Y) =
      e.forcingPath g k (p, Y) := by
    apply pathFamily_congr_slice
    intro s
    simp only [LinearData.forcingAlong, hB, hf]
  simp only [LinearData.copySolve, LinearData.anchoredSolve, hcoef, hforce]

theorem commonSolve_eq_of_fiber (d e : LinearData Parameter V E) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) (cutoff : Plane → ℝ) (p : Parameter) (Y : Plane)
    (hA : ∀ Z, d.coefficient (p, Z) = e.coefficient (p, Z))
    (hB : ∀ Z, d.forcingMap (p, Z) = e.forcingMap (p, Z))
    (hf : ∀ Z, d.source (p, Z) = e.source (p, Z)) :
    d.commonSolve g hle cutoff (p, Y) = e.commonSolve g hle cutoff (p, Y) := by
  apply tsum_congr
  intro k
  simp only [LinearData.localizedCopy, copySolve_eq_of_fiber d e g hle k p Y hA hB hf]

noncomputable def liftedSolve (d : LinearData Parameter V E) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) (cutoff : Plane → ℝ) : Point → E :=
  fun x => d.commonSolve g hle cutoff (toChart x)

/-- Radial support is a whole-fiber statement and is preserved by the
literal zero-entry reference solve, independently of its coefficients. -/
theorem liftedSolve_supported (d : LinearData Parameter V E) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) (cutoff : Plane → ℝ)
    {a b : ℝ} {ell : Slow → ℝ} {U : Set Slow}
    (hf : RadialSupport a b ell U (fun x => d.source (toChart x))) :
    RadialSupport a b ell U (liftedSolve d g hle cutoff) := by
  intro x hx hn
  by_contra hr
  have hsource (Y : Plane) : d.source ((x.1, x.2.1), Y) = 0 := by
    by_contra hz
    exact hr (hf (x.1, (x.2.1, Y)) hx hz)
  have hc (k : Frequency) : d.copySolve g hle k (toChart x) = 0 :=
    d.copySolve_zero_of_source_zero g hle k (x.1, x.2.1) x.2.2 (fun _ _ => hsource _)
  apply hn
  simp only [liftedSolve, LinearData.commonSolve, LinearData.localizedCopy, hc, smul_zero, tsum_zero]

noncomputable def positiveParameters (U : Set Slow) : Set Parameter := Ioi 0 ×ˢ U

theorem positiveParameters_open {U : Set Slow} (hU : IsOpen U) : IsOpen (positiveParameters U) :=
  isOpen_Ioi.prod hU

/-- These are primitive continuations, not a continuation of a solved
amplitude. The source is the actual incoming source named in the type. -/
structure ReferencePrimitives {coord a b : ℝ}
    (W : OffplaneCorrectionExtensions.Window coord a b) (original : LinearData Parameter V E) where
  coefficient : Chart → E →L[ℝ] E
  forcingMap : Chart → V →L[ℝ] E
  coefficient_smooth : ContDiffOn ℝ ∞ coefficient (positiveParameters W.carrier ×ˢ univ)
  forcingMap_smooth : ContDiffOn ℝ ∞ forcingMap (positiveParameters W.carrier ×ˢ univ)
  source : FieldContinuation W (fun x => original.source (toChart x))
  coefficient_agrees : ∀ p, p.1 > 0 → p.2 ∈ W.carrier → p.2.1 > 0 → ∀ Y,
    coefficient (p, Y) = original.coefficient (p, Y)
  forcingMap_agrees : ∀ p, p.1 > 0 → p.2 ∈ W.carrier → p.2.1 > 0 → ∀ Y,
    forcingMap (p, Y) = original.forcingMap (p, Y)

namespace ReferencePrimitives

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {original : LinearData Parameter V E} (d : ReferencePrimitives W original)

noncomputable def data : LinearData Parameter V E where
  coefficient := d.coefficient
  forcingMap := d.forcingMap
  source x := d.source.value (ofChart x)

omit [CompleteSpace E] in
theorem source_smooth : ContDiffOn ℝ ∞ d.data.source (positiveParameters W.carrier ×ˢ univ) :=
  d.source.smooth.comp ofChart_smooth.contDiffOn (fun _ hx => hx.1.2)

theorem solve_supported (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit) (cutoff : Plane → ℝ) :
    RadialSupport a b (OffplaneCorrectionExtensions.stableLength coord) W.carrier
      (liftedSolve d.data g hle cutoff) :=
  liftedSolve_supported d.data g hle cutoff d.source.supported

theorem solve_smooth (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit)
    {cutoff : Plane → ℝ} (hcutoff : ContDiff ℝ ∞ cutoff) (hcompact : HasCompactSupport cutoff)
    (hinside : tsupport cutoff ⊆ univ ×ˢ Ioo entry exit) :
    ContDiffOn ℝ ∞ (liftedSolve d.data g hle cutoff) (PhysicalMeanDomain.slowDomain W.carrier) := by
  have hsolve := d.data.commonSolve_contDiffOn g hle (positiveParameters_open W.isOpen)
    d.coefficient_smooth d.forcingMap_smooth d.source_smooth hcutoff hcompact hinside
  apply (PhysicalMeanDomain.slowDomain_open W.isOpen).contDiffOn_iff.mpr
  intro x hx
  by_cases hr : 0 < x.1
  · exact (hsolve.contDiffAt (((positiveParameters_open W.isOpen).prod isOpen_univ).mem_nhds
      (show toChart x ∈ positiveParameters W.carrier ×ˢ univ from ⟨⟨hr, hx⟩, mem_univ _⟩))).comp
        x toChart_smooth.contDiffAt
  · have hlt : x.1 < W.lower := lt_of_le_of_lt (le_of_not_gt hr) W.lower_pos
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(PhysicalMeanDomain.slowDomain_open W.isOpen).mem_nhds hx,
      (isOpen_lt continuous_fst continuous_const).mem_nhds hlt] with y hy hyr
    by_contra hn
    exact (not_lt_of_ge ((W.left _ hy).trans (d.solve_supported g hle cutoff y hy hn).1)) hyr

theorem solve_agrees (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit) (cutoff : Plane → ℝ) :
    OffplaneCorrectionExtensions.FiberAgreement W.carrier
      (liftedSolve d.data g hle cutoff) (liftedSolve original g hle cutoff) := by
  intro x hx
  by_cases hr : 0 < x.1
  · apply commonSolve_eq_of_fiber
    · exact d.coefficient_agrees _ hr hx.1 hx.2
    · exact d.forcingMap_agrees _ hr hx.1 hx.2
    · intro Y
      exact d.source.agrees (x := (x.1, (x.2.1, Y))) hx
  · have hsource (Y : Plane) : d.source.value (x.1, (x.2.1, Y)) = 0 :=
      d.source.zero_below hx.1 (lt_of_le_of_lt (le_of_not_gt hr) W.lower_pos)
    have hc (k : Frequency) : d.data.copySolve g hle k (toChart x) = 0 :=
      d.data.copySolve_zero_of_source_zero g hle k _ _ (fun _ _ => hsource _)
    have ho (k : Frequency) : original.copySolve g hle k (toChart x) = 0 := by
      apply original.copySolve_zero_of_source_zero g hle k
      intro t ht
      exact (d.source.agrees (x := (x.1, (x.2.1, g.path k x.2.2 t))) hx).symm.trans (hsource _)
    simp only [liftedSolve, LinearData.commonSolve, LinearData.localizedCopy, hc, ho, smul_zero, tsum_zero]

noncomputable def continuation (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit)
    {cutoff : Plane → ℝ} (hcutoff : ContDiff ℝ ∞ cutoff) (hcompact : HasCompactSupport cutoff)
    (hinside : tsupport cutoff ⊆ univ ×ˢ Ioo entry exit) :
    FieldContinuation W (liftedSolve original g hle cutoff) where
  value := liftedSolve d.data g hle cutoff
  smooth := d.solve_smooth g hle hcutoff hcompact hinside
  supported := d.solve_supported g hle cutoff
  agrees := d.solve_agrees g hle cutoff

end ReferencePrimitives

end ReferenceSolve

section CoefficientAgreement

open HarmonicFields hiding Coefficients
open HarmonicResidual

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

def CoeffEqOn (U : Set D) (a b : Coefficients D) : Prop := ∀ j, EqOn (a j) (b j) U

namespace CoeffEqOn

variable {U : Set D} {a b c d : Coefficients D}

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem refl (a : Coefficients D) : CoeffEqOn U a a := fun _ _ _ => rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem add (hab : CoeffEqOn U a b) (hcd : CoeffEqOn U c d) : CoeffEqOn U (a + c) (b + d) := by
  intro j x hx
  change a j x + c j x = b j x + d j x
  rw [hab j hx, hcd j hx]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem sub (hab : CoeffEqOn U a b) (hcd : CoeffEqOn U c d) : CoeffEqOn U (a - c) (b - d) := by
  intro j x hx
  change a j x - c j x = b j x - d j x
  rw [hab j hx, hcd j hx]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem mul (hab : CoeffEqOn U a b) (hcd : CoeffEqOn U c d) : CoeffEqOn U (a * c) (b * d) := by
  classical
  intro j x hx
  have hsum (v w : Coefficients D) (T : Finset ℤ) (hT : v.support ⊆ T) :
      (v * w) j x = ∑ i ∈ T, v i x * w (j - i) x := by
    rw [convolution_apply]
    apply Finset.sum_subset hT
    intro i _ hi
    simp only [Finsupp.notMem_support_iff.mp hi, Pi.zero_apply, zero_mul]
  rw [hsum a c (a.support ∪ b.support) Finset.subset_union_left,
    hsum b d (a.support ∪ b.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun i _ => by rw [hab i hx, hcd (j - i) hx])

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem constant {f g : D → ℂ} (hfg : EqOn f g U) :
    CoeffEqOn U (constantCoefficient f) (constantCoefficient g) := by
  intro j x hx
  change Finsupp.single 0 f j x = Finsupp.single 0 g j x
  by_cases hj : j = 0
  · subst j
    simpa only [Finsupp.single_eq_same] using hfg hx
  · simp only [Finsupp.single_apply, ite_eq_right (Ne.symm hj), Pi.zero_apply]

theorem differentiate (hab : CoeffEqOn U a b) (hU : IsOpen U)
    (V : D → D) (k : ℝ) {Φ Ψ : D → ℝ} (hΦ : EqOn Φ Ψ U) :
    CoeffEqOn U (differentiate V k Φ a) (differentiate V k Ψ b) := by
  intro j x hx
  have hc : a j =ᶠ[𝓝 x] b j := eventually_of_mem (hU.mem_nhds hx) (fun _ hy => hab j hy)
  have hp : Φ =ᶠ[𝓝 x] Ψ := eventually_of_mem (hU.mem_nhds hx) (fun _ hy => hΦ hy)
  simp only [differentiate_apply, derivativeCoefficient, along, hc.fderiv_eq, hp.fderiv_eq, hc.self_of_nhds]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angular (hab : CoeffEqOn U a b) (kp : ℤ) :
    CoeffEqOn U (angularDifferentiate kp a) (angularDifferentiate kp b) := by
  intro j x hx
  simp only [angularDifferentiate_apply, hab j hx]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realProjection (hab : CoeffEqOn U a b) : CoeffEqOn U (realCoefficients a) (realCoefficients b) := by
  intro j x hx
  simp only [realCoefficients_apply, hab j hx, hab (-j) hx]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nonconstant (hab : CoeffEqOn U a b) : CoeffEqOn U (nonconstant a) (nonconstant b) := by
  intro j x hx
  by_cases hj : j = 0
  · subst j; simp [HarmonicResidual.nonconstant]
  · change a.coeff.erase 0 j x = b.coeff.erase 0 j x
    rw [Finsupp.erase_ne hj, Finsupp.erase_ne hj]
    exact hab j hx

end CoeffEqOn

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem rotate_eqOn {U : Set D} {a b : VectorCoefficients D}
    (hab : ∀ i, CoeffEqOn U (a i) (b i)) (i : Fin 3) : CoeffEqOn U (rotate a i) (rotate b i) := by
  fin_cases i
  · intro j x hx
    change -(a 1 j x) = -(b 1 j x)
    rw [hab 1 j hx]
  · exact hab 0
  · exact CoeffEqOn.refl _

theorem scalarLaplacian_eqOn {U : Set D} (hU : IsOpen U) (g : Frame D)
    (k : ℝ) (kp : ℤ) {Φ Ψ : D → ℝ} (hΦ : EqOn Φ Ψ U)
    {a b : Coefficients D} (hab : CoeffEqOn U a b) :
    CoeffEqOn U (scalarLaplacian g k Φ kp a) (scalarLaplacian g k Ψ kp b) := by
  exact ((((hab.differentiate hU g.radial k hΦ).differentiate hU g.radial k hΦ).add
    ((CoeffEqOn.refl _).mul (hab.differentiate hU g.radial k hΦ))).add
    ((CoeffEqOn.refl _).mul ((hab.angular kp).angular kp))).add
    ((hab.differentiate hU g.axial k hΦ).differentiate hU g.axial k hΦ)

theorem vectorLaplacian_eqOn {U : Set D} (hU : IsOpen U) (g : Frame D)
    (k : ℝ) (kp : ℤ) {Φ Ψ : D → ℝ} (hΦ : EqOn Φ Ψ U)
    {a b : VectorCoefficients D} (hab : ∀ i, CoeffEqOn U (a i) (b i)) (i : Fin 3) :
    CoeffEqOn U (vectorLaplacian g k Φ kp a i) (vectorLaplacian g k Ψ kp b i) :=
  (scalarLaplacian_eqOn hU g k kp hΦ (hab i)).add ((CoeffEqOn.refl _).mul
    (((CoeffEqOn.refl _).mul (rotate_eqOn (fun j => (hab j).angular kp) i)).add
      (rotate_eqOn (rotate_eqOn hab) i)))

theorem transport_eqOn {U : Set D} (hU : IsOpen U) (g : Frame D)
    (k : ℝ) (kp : ℤ) {Φ Ψ : D → ℝ} (hΦ : EqOn Φ Ψ U)
    {a b c d : VectorCoefficients D} (hab : ∀ i, CoeffEqOn U (a i) (b i))
    (hcd : ∀ i, CoeffEqOn U (c i) (d i)) (i : Fin 3) :
    CoeffEqOn U (transport g k Φ kp a c i) (transport g k Ψ kp b d i) :=
  (((hab 0).mul ((hcd i).differentiate hU g.radial k hΦ)).add
    (((hab 1).mul (CoeffEqOn.refl _)).mul (((hcd i).angular kp).add (rotate_eqOn hcd i)))).add
    ((hab 2).mul ((hcd i).differentiate hU g.axial k hΦ))

theorem gradient_eqOn {U : Set D} (hU : IsOpen U) (g : Frame D)
    (k : ℝ) (kp : ℤ) {Φ Ψ : D → ℝ} (hΦ : EqOn Φ Ψ U)
    {a b : Coefficients D} (hab : CoeffEqOn U a b) (i : Fin 3) :
    CoeffEqOn U (gradient g k Φ kp a i) (gradient g k Ψ kp b i) := by
  fin_cases i
  · exact hab.differentiate hU g.radial k hΦ
  · exact (CoeffEqOn.refl _).mul (hab.angular kp)
  · exact hab.differentiate hU g.axial k hΦ

theorem nonlinearResidual_eqOn {U : Set D} (hU : IsOpen U) (g : Frame D)
    (k : ℝ) (kp : ℤ) {Φ Ψ : D → ℝ} (hΦ : EqOn Φ Ψ U)
    {B C a b : VectorCoefficients D} (hBC : ∀ i, CoeffEqOn U (B i) (C i))
    (hab : ∀ i, CoeffEqOn U (a i) (b i)) {p q : Coefficients D} (hpq : CoeffEqOn U p q)
    (i : Fin 3) : CoeffEqOn U (nonlinearResidual g k Φ kp B a p i) (nonlinearResidual g k Ψ kp C b q i) :=
  (((((hab i).differentiate hU g.time k hΦ).add (transport_eqOn hU g k kp hΦ hBC hab i)).add
    (transport_eqOn hU g k kp hΦ hab hBC i)).add (gradient_eqOn hU g k kp hΦ hpq i) |>.sub
      ((CoeffEqOn.refl _).mul (vectorLaplacian_eqOn hU g k kp hΦ hab i))).add
    (transport_eqOn hU g k kp hΦ hab hab i)

end CoefficientAgreement

section PrimitiveCoefficients

open HarmonicResidual

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}

/-- Continuing a finite coefficient family keeps its original finite
index set. A zero coefficient cannot create a new harmonic off the past. -/
noncomputable def continuedCoefficients (c : Coefficients Point)
    (e : ∀ j, FieldContinuation W (c j)) : Coefficients Point := by
  classical
  exact AddMonoidAlgebra.ofCoeff <| Finsupp.onFinset c.support (fun j => if j ∈ c.support then (e j).value else 0)
    (by intro j hj; by_contra hn; simp only [ite_eq_right hn, ne_eq, not_true_eq_false] at hj)

theorem continuedCoefficients_apply (c : Coefficients Point)
    (e : ∀ j, FieldContinuation W (c j)) (j : ℤ) :
    continuedCoefficients c e j = if j ∈ c.support then (e j).value else 0 := rfl

theorem continuedCoefficients_smooth (c : Coefficients Point)
    (e : ∀ j, FieldContinuation W (c j)) :
    SmoothCoefficients (PhysicalMeanDomain.slowDomain W.carrier) (continuedCoefficients c e) := by
  intro j
  rw [continuedCoefficients_apply]
  split_ifs
  · exact (e j).smooth
  · exact contDiffOn_const

theorem continuedCoefficients_supported (c : Coefficients Point)
    (e : ∀ j, FieldContinuation W (c j)) (j : ℤ) :
    RadialSupport a b (OffplaneCorrectionExtensions.stableLength coord) W.carrier
      (continuedCoefficients c e j) := by
  intro x hx hn
  rw [continuedCoefficients_apply] at hn
  split_ifs at hn
  · exact (e j).supported x hx hn
  · exact (hn rfl).elim

theorem continuedCoefficients_agrees (c : Coefficients Point)
    (e : ∀ j, FieldContinuation W (c j)) :
    CoeffEqOn (PhysicalMeanDomain.slowDomain (W.carrier ∩ OffplaneCorrectionExtensions.positiveSlow))
      (continuedCoefficients c e) c := by
  intro j x hx
  rw [continuedCoefficients_apply]
  split_ifs with hj
  · exact (e j).agrees hx
  · rw [Finsupp.notMem_support_iff.mp hj]

/-- Per-label input data needed in addition to `SRC.Primitives`.
The Gaussian and alias coefficients are explicit primitive inputs. -/
structure HarmonicPrimitives (W : OffplaneCorrectionExtensions.Window coord a b)
    (block : CorrectionState.HarmonicBlock Point) (G A : BlockCoefficients Point) where
  velocity : ∀ n i j, FieldContinuation W (block.velocity n i j)
  pressure : ∀ n j, FieldContinuation W (block.pressure n j)
  gaussian : ∀ n i j, FieldContinuation W (G n i j)
  aliasError : ∀ n i j, FieldContinuation W (A n i j)
  phase : ℕ → Point → ℝ
  phase_smooth : ∀ n, ContDiffOn ℝ ∞ (phase n) (LocalRankDefect.positiveDomain W.carrier)
  phase_agrees : ∀ n, OffplaneCorrectionExtensions.FiberAgreement W.carrier (phase n) (block.phase n)

namespace HarmonicPrimitives

variable {block : CorrectionState.HarmonicBlock Point} {G A : BlockCoefficients Point}
  (p : HarmonicPrimitives W block G A)

noncomputable def continuedBlock : CorrectionState.HarmonicBlock Point where
  velocity n i := continuedCoefficients (block.velocity n i) (p.velocity n i)
  pressure n := continuedCoefficients (block.pressure n) (p.pressure n)
  phase := p.phase
  frequency := block.frequency
  angularFrequency := block.angularFrequency

noncomputable def continuedGaussian : BlockCoefficients Point :=
  fun n i => continuedCoefficients (G n i) (p.gaussian n i)

noncomputable def continuedAlias : BlockCoefficients Point :=
  fun n i => continuedCoefficients (A n i) (p.aliasError n i)

end HarmonicPrimitives

end PrimitiveCoefficients

section MovingCarrier

variable {coord a b : ℝ} (W : OffplaneCorrectionExtensions.Window coord a b)

/-- The exact moving annulus, enlarged only outside the open continuation
domain so that its complement supplies ambient zero germs. -/
noncomputable def movingCarrier : Set Point :=
  {x | x.2.1 ∈ W.carrier → x.1 ∈ Icc
    (OffplaneCorrectionExtensions.stableLength coord x.2.1 * a)
    (OffplaneCorrectionExtensions.stableLength coord x.2.1 * b)}

theorem movingCarrier_closed (hc : 0 < coord) (hc1 : coord < 1) : IsClosed (movingCarrier W) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hxU : x.2.1 ∈ W.carrier := by
    by_contra hn
    exact hx (fun h => (hn h).elim)
  have hxR : x.1 ∉ Icc
      (OffplaneCorrectionExtensions.stableLength coord x.2.1 * a)
      (OffplaneCorrectionExtensions.stableLength coord x.2.1 * b) := fun h => hx (fun _ => h)
  have he : ContinuousAt (OffplaneCorrectionExtensions.stableLength coord) x.2.1 :=
    (W.length_smooth hc hc1).continuousOn.continuousAt (W.isOpen.mem_nhds hxU)
  have hmap : ContinuousAt (fun y : Point => y.2.1) x := continuous_snd.fst.continuousAt
  have hlen : ContinuousAt (fun y : Point => OffplaneCorrectionExtensions.stableLength coord y.2.1) x :=
    ContinuousAt.comp (f := fun y : Point => y.2.1) (x := x) he hmap
  have hU := (PhysicalMeanDomain.slowDomain_open W.isOpen).mem_nhds hxU
  simp only [mem_Icc, not_and_or, not_le] at hxR
  rcases hxR with hlo | hhi
  · have hn : ∀ᶠ y : Point in 𝓝 x,
        y.1 < OffplaneCorrectionExtensions.stableLength coord y.2.1 * a :=
      (continuous_fst.continuousAt.fun_sub (hlen.mul_const a)).eventually_lt_const (by linarith : x.1 - _ < 0)
        |>.mono (fun y hy => by linarith)
    filter_upwards [hU, hn] with y hy hyr
    intro hm
    exact (not_lt_of_ge (hm hy).1) hyr
  · have hn : ∀ᶠ y : Point in 𝓝 x,
        OffplaneCorrectionExtensions.stableLength coord y.2.1 * b < y.1 :=
      ((hlen.mul_const b).fun_sub continuous_fst.continuousAt).eventually_lt_const (by linarith : _ - x.1 < 0)
        |>.mono (fun y hy => by linarith)
    filter_upwards [hU, hn] with y hy hyr
    intro hm
    exact (not_lt_of_ge (hm hy).2) hyr

end MovingCarrier

section SourceConstruction

open HarmonicResidual

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {block : CorrectionState.HarmonicBlock Point} {G A : BlockCoefficients Point}
  (p : HarmonicPrimitives W block G A)

theorem HarmonicPrimitives.inputSupport :
    HarmonicSourceSupport.InputSupportOn (PhysicalMeanDomain.slowDomain W.carrier)
      (fun _ => movingCarrier W) p.continuedBlock p.continuedGaussian p.continuedAlias := by
  have hs (c : Coefficients Point) (e : ∀ j, FieldContinuation W (c j)) :
      HarmonicSourceSupport.NonzeroSupportedOn (PhysicalMeanDomain.slowDomain W.carrier)
        (movingCarrier W) (realCoefficients (continuedCoefficients c e)) := by
    apply HarmonicSourceSupport.NonzeroSupportedOn.realProjection
    intro j hj x hx hn
    by_contra hz
    exact hn (fun _ => continuedCoefficients_supported c e j x hx hz)
  exact ⟨fun n i => hs _ (p.velocity n i), fun n => hs _ (p.pressure n),
    fun n i => hs _ (p.gaussian n i), fun n i => hs _ (p.aliasError n i)⟩

theorem HarmonicPrimitives.source_zero_germ (hc : 0 < coord) (hc1 : coord < 1)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (j : ℤ) (n : ℕ)
    {x : Point} (hx : x.2.1 ∈ W.carrier)
    (hr : x.1 ∉ Icc (OffplaneCorrectionExtensions.stableLength coord x.2.1 * a)
      (OffplaneCorrectionExtensions.stableLength coord x.2.1 * b)) :
    ParticularWaveAssembly.residualSource c u p.continuedBlock p.continuedGaussian p.continuedAlias j n
      =ᶠ[𝓝 x] fun _ => 0 :=
  HarmonicSourceSupport.residualSource_zero_germ_on c u _ _ _
    (PhysicalMeanDomain.slowDomain_open W.isOpen) (fun _ => movingCarrier_closed W hc hc1)
    p.inputSupport j n hx (fun h => hr (h hx))

structure SourceRegular (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (n : ℕ) (W : OffplaneCorrectionExtensions.Window coord a b) : Prop where
  frame : (contextFrame c n).Regular (LocalRankDefect.positiveDomain W.carrier)
  base : ∀ i, ContDiffOn ℝ ∞ (fun x => contextBase c n x i) (LocalRankDefect.positiveDomain W.carrier)
  mean : ∀ i, ContDiffOn ℝ ∞ (fun x => stateMean u n x i) (LocalRankDefect.positiveDomain W.carrier)

theorem HarmonicPrimitives.source_smooth (hc : 0 < coord) (hc1 : coord < 1)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (j : ℤ) (n : ℕ)
    (h : SourceRegular c u n W) :
    ContDiffOn ℝ ∞
      (ParticularWaveAssembly.residualSource c u p.continuedBlock p.continuedGaussian p.continuedAlias j n)
      (PhysicalMeanDomain.slowDomain W.carrier) := by
  have hs (c : Coefficients Point) (e : ∀ j, FieldContinuation W (c j)) :
      SmoothCoefficients (LocalRankDefect.positiveDomain W.carrier) (continuedCoefficients c e) :=
    fun j => (continuedCoefficients_smooth c e j).mono (fun _ hx => hx.2)
  have hpos := LabelData.waveResidualCoefficients_smooth
    (LocalRankDefect.positiveDomain_open W.isOpen) h.frame _ _ h.base h.mean
    (ofBlock p.continuedBlock p.continuedGaussian p.continuedAlias n)
    ⟨p.phase_smooth n, fun i => (hs _ (p.velocity n i)).realCoefficients, (hs _ (p.pressure n)).realCoefficients⟩
    (fun i => hs _ (p.gaussian n i)) (fun i => hs _ (p.aliasError n i))
  apply (PhysicalMeanDomain.slowDomain_open W.isOpen).contDiffOn_iff.mpr
  intro x hx
  by_cases hr : 0 < x.1
  · apply contDiffAt_pi.mpr
    intro i
    exact (hpos i j).contDiffAt ((LocalRankDefect.positiveDomain_open W.isOpen).mem_nhds ⟨hr, hx⟩)
  · apply contDiffAt_const.congr_of_eventuallyEq
    apply p.source_zero_germ hc hc1 c u j n hx
    intro hh
    have hlo := (W.left _ hx).trans hh.1
    exact hr (lt_of_lt_of_le W.lower_pos hlo)

theorem HarmonicPrimitives.source_supported (hc : 0 < coord) (hc1 : coord < 1)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (j : ℤ) (n : ℕ) :
    RadialSupport a b (OffplaneCorrectionExtensions.stableLength coord) W.carrier
      (ParticularWaveAssembly.residualSource c u p.continuedBlock p.continuedGaussian p.continuedAlias j n) := by
  intro x hx hn
  by_contra hr
  exact hn (p.source_zero_germ hc hc1 c u j n hx hr).self_of_nhds

theorem HarmonicPrimitives.source_agrees
    (c c₀ : CorrectionState.Context Point) (u u₀ : CorrectionState.State Point)
    (hops : c.operators = c₀.operators)
    (hbase : ∀ n i, OffplaneCorrectionExtensions.FiberAgreement W.carrier
      (fun x => contextBase c n x i) (fun x => contextBase c₀ n x i))
    (hmean : ∀ n i, OffplaneCorrectionExtensions.FiberAgreement W.carrier
      (fun x => stateMean u n x i) (fun x => stateMean u₀ n x i))
    (j : ℤ) (n : ℕ) :
    OffplaneCorrectionExtensions.FiberAgreement W.carrier
      (ParticularWaveAssembly.residualSource c u p.continuedBlock p.continuedGaussian p.continuedAlias j n)
      (ParticularWaveAssembly.residualSource c₀ u₀ block G A j n) := by
  have hframe : contextFrame c n = contextFrame c₀ n := by simp only [contextFrame, hops]
  have hb : ∀ i, CoeffEqOn (PhysicalMeanDomain.slowDomain (W.carrier ∩ OffplaneCorrectionExtensions.positiveSlow))
      (HarmonicFields.constantCoefficient (fun x => contextBase c n x i + stateMean u n x i))
      (HarmonicFields.constantCoefficient (fun x => contextBase c₀ n x i + stateMean u₀ n x i)) := by
    intro i
    apply CoeffEqOn.constant
    intro x hx
    exact congrArg₂ (· + ·) (hbase n i hx) (hmean n i hx)
  have he (i : Fin 3) :=
    (((nonlinearResidual_eqOn (PhysicalMeanDomain.slowDomain_open (W.isOpen.inter OffplaneCorrectionExtensions.positiveSlow_open))
      (contextFrame c₀ n) (block.frequency n) (block.angularFrequency n) (p.phase_agrees n) hb
      (fun i => (continuedCoefficients_agrees _ (p.velocity n i)).realProjection)
      (continuedCoefficients_agrees _ (p.pressure n)).realProjection i).sub
      (continuedCoefficients_agrees _ (p.gaussian n i))).sub
      (continuedCoefficients_agrees _ (p.aliasError n i))).realProjection.nonconstant
  intro x hx
  funext i
  simp only [ParticularWaveAssembly.residualSource, residualBlock, ofBlock,
    LabelData.waveResidualCoefficients, LabelData.residualCoefficients,
    HarmonicPrimitives.continuedBlock, HarmonicPrimitives.continuedGaussian,
    HarmonicPrimitives.continuedAlias, hframe]
  exact he i j hx

noncomputable def HarmonicPrimitives.sourceContinuation (hc : 0 < coord) (hc1 : coord < 1)
    (c c₀ : CorrectionState.Context Point) (u u₀ : CorrectionState.State Point)
    (hops : c.operators = c₀.operators)
    (hbase : ∀ n i, OffplaneCorrectionExtensions.FiberAgreement W.carrier
      (fun x => contextBase c n x i) (fun x => contextBase c₀ n x i))
    (hmean : ∀ n i, OffplaneCorrectionExtensions.FiberAgreement W.carrier
      (fun x => stateMean u n x i) (fun x => stateMean u₀ n x i))
    (j : ℤ) (n : ℕ) (h : SourceRegular c u n W) :
    FieldContinuation W (ParticularWaveAssembly.residualSource c₀ u₀ block G A j n) where
  value := ParticularWaveAssembly.residualSource c u p.continuedBlock p.continuedGaussian p.continuedAlias j n
  smooth := p.source_smooth hc hc1 c u j n h
  supported := p.source_supported hc hc1 c u j n
  agrees := p.source_agrees c c₀ u u₀ hops hbase hmean j n

end SourceConstruction

section ActualSource

open HarmonicResidual

variable {F : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W₀) {ld : ModulatedProfileAssembly.LoopData W₀}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ) (index : ℕ → ℕ)
  {P : SignedStressPrimitive.Patch}
  (W : OffplaneCorrectionExtensions.Window (2 * F.data.h) P.a P.b)
  {u : CorrectionState.State Point} (inputs : SignedRequestContinuation.Primitives P W u)

theorem actual_source_regular (n : ℕ) :
    SourceRegular (SupportedActualContext.context H v upper B index) inputs.state n W := by
  let c := SupportedActualContext.context H v upper B index
  have ho := SignedRequestContinuation.actual_operators_local H v upper B index W
  have hb := SignedRequestContinuation.actual_base_smooth H v upper B index W
  refine ⟨?_, ?_, ?_⟩
  · apply contextFrame_regular
    · change ContDiffOn ℝ ∞ (ActualCorrectionModels.context H v upper B index).operators.radius _
      rw [ho.radius_eq]
      exact contDiffOn_fst
    · intro x hx
      change (ActualCorrectionModels.context H v upper B index).operators.radius x ≠ 0
      rw [ho.radius_eq]
      exact hx.1.ne'
    · exact ho.radialProfile
  · intro i
    fin_cases i
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hb.radial n)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hb.angular n)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hb.axial n)
  · intro i
    fin_cases i
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((inputs.radial n).smooth.mono (fun _ hx => hx.2))
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((inputs.angular n).smooth.mono (fun _ hx => hx.2))
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((inputs.axial n).smooth.mono (fun _ hx => hx.2))

/-- The source continuation is computed from the actual supported context,
the incoming continued mean, and the continued per-label coefficients. -/
noncomputable def actualSourceContinuation
    {block : CorrectionState.HarmonicBlock Point} {G A : BlockCoefficients Point}
    (p : HarmonicPrimitives W block G A) (j : ℤ) (n : ℕ) :
    FieldContinuation W (ParticularWaveAssembly.residualSource
      (CommonBaseContext.context H v upper B index) u block G A j n) := by
  apply p.sourceContinuation (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (SupportedActualContext.context H v upper B index) (CommonBaseContext.context H v upper B index)
    inputs.state u rfl
  · intro n i x hx
    have hb := SupportedActualContext.context_base_agrees H v upper B index W.carrier
    fin_cases i
    · exact congrArg Complex.ofReal (hb.radial n hx)
    · exact congrArg Complex.ofReal (hb.angular n hx)
    · exact congrArg Complex.ofReal (hb.axial n hx)
  · intro n i x hx
    fin_cases i
    · exact congrArg Complex.ofReal ((inputs.radial n).agrees hx)
    · exact congrArg Complex.ofReal ((inputs.angular n).agrees hx)
    · exact congrArg Complex.ofReal ((inputs.axial n).agrees hx)
  · exact actual_source_regular H v upper B index W inputs n

end ActualSource

section SupportedSourceSmoothness

open HarmonicResidual

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- A local source-smoothness endpoint for actual iteration inputs.
The differential coefficients need only be smooth where the label lives;
the exact closed support supplies zero germs at all remaining points. -/
theorem source_contDiffOn_of_support
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : BlockCoefficients D)
    {U V : Set D} (hU : IsOpen U) (hV : IsOpen V) {K : ℕ → Set D}
    (hK : ∀ n, IsClosed (K n)) (hKV : ∀ n, K n ∩ U ⊆ V)
    (hs : HarmonicSourceSupport.InputSupportOn U K b G A)
    (n : ℕ) (j : ℤ)
    (hg : (contextFrame c n).Regular V)
    (hb : ∀ i, ContDiffOn ℝ ∞ (fun x => contextBase c n x i) V)
    (hm : ∀ i, ContDiffOn ℝ ∞ (fun x => stateMean u n x i) V)
    (hphase : ContDiffOn ℝ ∞ (b.phase n) V)
    (hvelocity : ∀ i, SmoothCoefficients V (b.velocity n i))
    (hpressure : SmoothCoefficients V (b.pressure n))
    (hgaussian : ∀ i, SmoothCoefficients V (G n i))
    (halias : ∀ i, SmoothCoefficients V (A n i)) :
    ContDiffOn ℝ ∞ (ParticularWaveAssembly.residualSource c u b G A j n) U := by
  have hlocal := LabelData.waveResidualCoefficients_smooth hV hg _ _ hb hm
    (ofBlock b G A n) ⟨hphase, fun i => (hvelocity i).realCoefficients, hpressure.realCoefficients⟩
    hgaussian halias
  apply hU.contDiffOn_iff.mpr
  intro x hx
  by_cases hv : x ∈ V
  · exact contDiffAt_pi.mpr (fun i => (hlocal i j).contDiffAt (hV.mem_nhds hv))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (HarmonicSourceSupport.residualSource_zero_germ_on c u b G A hU hK hs j n hx
        (fun hk => hv (hKV n ⟨hk, hx⟩)))

end SupportedSourceSmoothness

section NativeReadout

variable {V E F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A linear native readout includes the actual projected pressure: one
term acts on the solved vector, and the other on the current source. -/
noncomputable def readoutCopy (d : LinearData Parameter V E) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) (cutoff : Plane → ℝ)
    (Q : Chart → E →L[ℝ] F) (B : Chart → V →L[ℝ] F) (k : Frequency) (x : Chart) : F :=
  cutoff (g.coordinates k x.2) •
    (Q (x.1, g.coordinates k x.2) (d.copySolve g hle k x) +
      B (x.1, g.coordinates k x.2) (d.source x))

noncomputable def readoutCommon (d : LinearData Parameter V E) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) (cutoff : Plane → ℝ)
    (Q : Chart → E →L[ℝ] F) (B : Chart → V →L[ℝ] F) (x : Chart) : F :=
  ∑' k, readoutCopy d g hle cutoff Q B k x

theorem readoutCommon_zero_of_source_zero (d : LinearData Parameter V E) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) (cutoff : Plane → ℝ)
    (Q : Chart → E →L[ℝ] F) (B : Chart → V →L[ℝ] F) (p : Parameter)
    (hf : ∀ Y, d.source (p, Y) = 0) (Y : Plane) :
    readoutCommon d g hle cutoff Q B (p, Y) = 0 := by
  have hc (k : Frequency) : d.copySolve g hle k (p, Y) = 0 :=
    d.copySolve_zero_of_source_zero g hle k p Y (fun _ _ => hf _)
  simp only [readoutCommon, readoutCopy, hc, hf, map_zero, add_zero, smul_zero, tsum_zero]

theorem readoutCommon_supported (d : LinearData Parameter V E) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) (cutoff : Plane → ℝ)
    (Q : Chart → E →L[ℝ] F) (B : Chart → V →L[ℝ] F)
    {a b : ℝ} {ell : Slow → ℝ} {U : Set Slow}
    (hf : RadialSupport a b ell U (fun x => d.source (toChart x))) :
    RadialSupport a b ell U (fun x => readoutCommon d g hle cutoff Q B (toChart x)) := by
  intro x hx hn
  by_contra hr
  apply hn
  apply readoutCommon_zero_of_source_zero
  intro Y
  by_contra hz
  exact hr (hf (x.1, (x.2.1, Y)) hx hz)

theorem readoutCopy_smooth (d : LinearData Parameter V E) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) {U : Set Parameter} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))
    {Q : Chart → E →L[ℝ] F} {B : Chart → V →L[ℝ] F}
    (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ univ)) (hR : ContDiffOn ℝ ∞ B (U ×ˢ univ))
    {cutoff : Plane → ℝ} (hcutoff : ContDiff ℝ ∞ cutoff)
    (hinside : tsupport cutoff ⊆ univ ×ˢ Ioo entry exit) (k : Frequency) :
    ContDiffOn ℝ ∞ (readoutCopy d g hle cutoff Q B k) (U ×ˢ univ) := by
  apply (hU.prod isOpen_univ).contDiffOn_iff.mpr
  intro x hx
  have hcoord : ContDiff ℝ ∞ (fun y : Chart => g.coordinates k y.2) :=
    (g.coordinates_contDiff k).comp contDiff_snd
  by_cases hk : g.coordinates k x.2 ∈ tsupport cutoff
  · have hnative : ContDiff ℝ ∞ (fun y : Chart => (y.1, g.coordinates k y.2)) :=
      contDiff_fst.prodMk hcoord
    have hn : (x.1, g.coordinates k x.2) ∈ U ×ˢ (univ : Set Plane) := ⟨hx.1, mem_univ _⟩
    have hQs := (hQ.contDiffAt ((hU.prod isOpen_univ).mem_nhds hn)).comp x hnative.contDiffAt
    have hRs := (hR.contDiffAt ((hU.prod isOpen_univ).mem_nhds hn)).comp x hnative.contDiffAt
    exact (hcutoff.comp hcoord).contDiffAt.smul
      ((hQs.clm_apply (d.copySolve_contDiffAt g hle hU k hA hB hf hx.1 (hinside hk).2)).add
        (hRs.clm_apply (hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds hx))))
  · have hzout : readoutCopy d g hle cutoff Q B k =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hk).comp_tendsto hcoord.continuous.continuousAt
      filter_upwards [hz] with y hy
      have hy0 : cutoff (g.coordinates k y.2) = 0 := hy
      simp only [readoutCopy, hy0, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hzout

theorem readoutCommon_smooth (d : LinearData Parameter V E) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) {U : Set Parameter} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))
    {Q : Chart → E →L[ℝ] F} {B : Chart → V →L[ℝ] F}
    (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ univ)) (hR : ContDiffOn ℝ ∞ B (U ×ˢ univ))
    {cutoff : Plane → ℝ} (hcutoff : ContDiff ℝ ∞ cutoff) (hcompact : HasCompactSupport cutoff)
    (hinside : tsupport cutoff ⊆ univ ×ˢ Ioo entry exit) :
    ContDiffOn ℝ ∞ (readoutCommon d g hle cutoff Q B) (U ×ˢ univ) := by
  apply (hU.prod isOpen_univ).contDiffOn_iff.mpr
  intro x hx
  obtain ⟨T, hT⟩ := g.finite_copy_cutoffs hcompact (‖x.2‖ + 1)
  have he : readoutCommon d g hle cutoff Q B =ᶠ[𝓝 x]
      fun y => ∑ k ∈ T, readoutCopy d g hle cutoff Q B k y := by
    filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds
      (show ‖x.2‖ < ‖x.2‖ + 1 by linarith)] with y hy
    apply tsum_eq_sum
    intro k hk
    simp only [readoutCopy, hT y.2 hy.le k hk, zero_smul]
  apply (ContDiffAt.sum (fun k (_ : k ∈ T) =>
    (readoutCopy_smooth d g hle hU hA hB hf hQ hR hcutoff hinside k).contDiffAt
      ((hU.prod isOpen_univ).mem_nhds hx))).congr_of_eventuallyEq he

structure ReadoutPrimitives {coord a b : ℝ} (W : OffplaneCorrectionExtensions.Window coord a b)
    (Q : Chart → E →L[ℝ] F) (B : Chart → V →L[ℝ] F) where
  solutionMap : Chart → E →L[ℝ] F
  sourceMap : Chart → V →L[ℝ] F
  solutionMap_smooth : ContDiffOn ℝ ∞ solutionMap (positiveParameters W.carrier ×ˢ univ)
  sourceMap_smooth : ContDiffOn ℝ ∞ sourceMap (positiveParameters W.carrier ×ˢ univ)
  solutionMap_agrees : ∀ p, p.1 > 0 → p.2 ∈ W.carrier → p.2.1 > 0 → ∀ Y,
    solutionMap (p, Y) = Q (p, Y)
  sourceMap_agrees : ∀ p, p.1 > 0 → p.2 ∈ W.carrier → p.2.1 > 0 → ∀ Y,
    sourceMap (p, Y) = B (p, Y)

namespace ReadoutPrimitives

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {original : LinearData Parameter V E} (d : ReferencePrimitives W original)
  {Q : Chart → E →L[ℝ] F} {B : Chart → V →L[ℝ] F} (r : ReadoutPrimitives W Q B)

theorem supported (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit) (cutoff : Plane → ℝ) :
    RadialSupport a b (OffplaneCorrectionExtensions.stableLength coord) W.carrier
      (fun x => readoutCommon d.data g hle cutoff r.solutionMap r.sourceMap (toChart x)) :=
  readoutCommon_supported d.data g hle cutoff r.solutionMap r.sourceMap d.source.supported

theorem smooth (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit)
    {cutoff : Plane → ℝ} (hcutoff : ContDiff ℝ ∞ cutoff) (hcompact : HasCompactSupport cutoff)
    (hinside : tsupport cutoff ⊆ univ ×ˢ Ioo entry exit) :
    ContDiffOn ℝ ∞ (fun x => readoutCommon d.data g hle cutoff r.solutionMap r.sourceMap (toChart x))
      (PhysicalMeanDomain.slowDomain W.carrier) := by
  have hr := readoutCommon_smooth d.data g hle (positiveParameters_open W.isOpen)
    d.coefficient_smooth d.forcingMap_smooth d.source_smooth r.solutionMap_smooth r.sourceMap_smooth
    hcutoff hcompact hinside
  apply (PhysicalMeanDomain.slowDomain_open W.isOpen).contDiffOn_iff.mpr
  intro x hx
  by_cases hpos : 0 < x.1
  · exact (hr.contDiffAt (((positiveParameters_open W.isOpen).prod isOpen_univ).mem_nhds
      (show toChart x ∈ positiveParameters W.carrier ×ˢ univ from ⟨⟨hpos, hx⟩, mem_univ _⟩))).comp
        x toChart_smooth.contDiffAt
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(PhysicalMeanDomain.slowDomain_open W.isOpen).mem_nhds hx,
      (isOpen_lt continuous_fst continuous_const).mem_nhds
        (show x.1 < W.lower from lt_of_le_of_lt (le_of_not_gt hpos) W.lower_pos)] with y hy hyr
    by_contra hn
    exact (not_lt_of_ge ((W.left _ hy).trans (r.supported d g hle cutoff y hy hn).1)) hyr

theorem agrees (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit) (cutoff : Plane → ℝ) :
    OffplaneCorrectionExtensions.FiberAgreement W.carrier
      (fun x => readoutCommon d.data g hle cutoff r.solutionMap r.sourceMap (toChart x))
      (fun x => readoutCommon original g hle cutoff Q B (toChart x)) := by
  intro x hx
  by_cases hp : 0 < x.1
  · apply tsum_congr
    intro k
    have hA := d.coefficient_agrees (x.1, x.2.1) hp hx.1 hx.2
    have hB := d.forcingMap_agrees (x.1, x.2.1) hp hx.1 hx.2
    have hf (Y : Plane) : d.data.source ((x.1, x.2.1), Y) = original.source ((x.1, x.2.1), Y) :=
      d.source.agrees (x := (x.1, (x.2.1, Y))) hx
    simp only [readoutCopy, toChart, r.solutionMap_agrees (x.1, x.2.1) hp hx.1 hx.2,
      r.sourceMap_agrees (x.1, x.2.1) hp hx.1 hx.2, hf,
      copySolve_eq_of_fiber d.data original g hle k _ _ hA hB hf]
  · have hf (Y : Plane) : d.source.value (x.1, (x.2.1, Y)) = 0 :=
      d.source.zero_below hx.1 (lt_of_le_of_lt (le_of_not_gt hp) W.lower_pos)
    have ho (Y : Plane) : original.source ((x.1, x.2.1), Y) = 0 :=
      (d.source.agrees (x := (x.1, (x.2.1, Y))) hx).symm.trans (hf Y)
    change readoutCommon d.data g hle cutoff r.solutionMap r.sourceMap ((x.1, x.2.1), x.2.2) =
      readoutCommon original g hle cutoff Q B ((x.1, x.2.1), x.2.2)
    rw [readoutCommon_zero_of_source_zero d.data g hle cutoff r.solutionMap r.sourceMap (x.1, x.2.1) hf,
      readoutCommon_zero_of_source_zero original g hle cutoff Q B (x.1, x.2.1) ho]

noncomputable def continuation (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit)
    {cutoff : Plane → ℝ} (hcutoff : ContDiff ℝ ∞ cutoff) (hcompact : HasCompactSupport cutoff)
    (hinside : tsupport cutoff ⊆ univ ×ˢ Ioo entry exit) :
    FieldContinuation W (fun x => readoutCommon original g hle cutoff Q B (toChart x)) where
  value x := readoutCommon d.data g hle cutoff r.solutionMap r.sourceMap (toChart x)
  smooth := r.smooth d g hle hcutoff hcompact hinside
  supported := r.supported d g hle cutoff
  agrees := r.agrees d g hle cutoff

end ReadoutPrimitives

end NativeReadout

section TangentGeometry

open scoped InnerProductSpace

abbrev Space := ProblemStatement.Space

noncomputable def pressureSolutionMap (frequency : ℝ) (N Nd : Space) (A : Space →L[ℝ] Space) :
    Space →L[ℝ] ℂ :=
  ((Complex.I / (frequency : ℂ)) • Complex.ofRealCLM).comp
    ((⟪N, N⟫_ℝ)⁻¹ • ((innerSL ℝ N).comp A - innerSL ℝ Nd))

noncomputable def pressureSourceMap (frequency : ℝ) (N : Space) : Space →L[ℝ] ℂ :=
  ((Complex.I / (frequency : ℂ)) • Complex.ofRealCLM).comp ((⟪N, N⟫_ℝ)⁻¹ • innerSL ℝ N)

theorem pressure_maps_eq (frequency : ℝ) (N Nd u f : Space) (A : Space →L[ℝ] Space) :
    pressureSolutionMap frequency N Nd A u + pressureSourceMap frequency N f =
      Complex.I * (TangentProjection.pressureCoefficient N Nd u (A u) f : ℂ) / (frequency : ℂ) := by
  simp only [pressureSolutionMap, pressureSourceMap, ContinuousLinearMap.comp_apply,
    _root_.smul_apply, _root_.sub_apply, innerSL_apply_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, TangentProjection.pressureCoefficient, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_div]
  ring

theorem pressure_maps_smooth {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set D} (frequency : ℝ) {N Nd : D → Space} {A : D → Space →L[ℝ] Space}
    (hN : ContDiffOn ℝ ∞ N U) (hNd : ContDiffOn ℝ ∞ Nd U) (hA : ContDiffOn ℝ ∞ A U)
    (hn : ∀ x ∈ U, N x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => pressureSolutionMap frequency (N x) (Nd x) (A x)) U ∧
    ContDiffOn ℝ ∞ (fun x => pressureSourceMap frequency (N x)) U := by
  have hden := (hN.inner ℝ hN).inv (fun x hx => inner_self_ne_zero.mpr (hn x hx))
  have hi := (innerSL ℝ).contDiff.comp_contDiffOn hN
  have hid := (innerSL ℝ).contDiff.comp_contDiffOn hNd
  exact ⟨contDiffOn_const.clm_comp (hden.smul ((hi.clm_comp hA).sub hid)),
    contDiffOn_const.clm_comp (hden.smul hi)⟩

theorem projectedOperator_smooth {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set D} {N Nd : D → Space} {A : D → Space →L[ℝ] Space} {damping : D → ℝ}
    (hN : ContDiffOn ℝ ∞ N U) (hNd : ContDiffOn ℝ ∞ Nd U) (hA : ContDiffOn ℝ ∞ A U)
    (hd : ContDiffOn ℝ ∞ damping U) (hn : ∀ x ∈ U, N x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => TangentODE.projectedOperator (N x) (Nd x) (A x) (damping x)) U ∧
    ContDiffOn ℝ ∞ (fun x => negativeTangentProjection (N x)) U := by
  have hden := (hN.inner ℝ hN).inv (fun x hx => inner_self_ne_zero.mpr (hn x hx))
  have hi := (innerSL ℝ).contDiff.comp_contDiffOn hN
  have hid := (innerSL ℝ).contDiff.comp_contDiffOn hNd
  constructor
  · exact ((hA.neg.add (((hi.clm_comp hA).sub hid).smulRight (hden.smul hN))).sub
      (hd.smul contDiffOn_const))
  · exact (contDiffOn_const.sub (hi.smulRight (hden.smul hN))).neg

/-- Only the primitive normal, normal motion, base action, and damping
are continued. The inhomogeneous source is supplied separately. -/
structure TangentGeometry {coord a b : ℝ} (W : OffplaneCorrectionExtensions.Window coord a b)
    (t : TangentData Parameter Space) where
  normal : Chart → Space
  normalDot : Chart → Space
  action : Chart → Space →L[ℝ] Space
  damping : Chart → ℝ
  normal_smooth : ContDiffOn ℝ ∞ normal (positiveParameters W.carrier ×ˢ univ)
  normalDot_smooth : ContDiffOn ℝ ∞ normalDot (positiveParameters W.carrier ×ˢ univ)
  action_smooth : ContDiffOn ℝ ∞ action (positiveParameters W.carrier ×ˢ univ)
  damping_smooth : ContDiffOn ℝ ∞ damping (positiveParameters W.carrier ×ˢ univ)
  normal_ne : ∀ x ∈ positiveParameters W.carrier ×ˢ univ, normal x ≠ 0
  normal_agrees : ∀ p, p.1 > 0 → p.2 ∈ W.carrier → p.2.1 > 0 → ∀ Y, normal (p,Y) = t.normal (p,Y)
  normalDot_agrees : ∀ p, p.1 > 0 → p.2 ∈ W.carrier → p.2.1 > 0 → ∀ Y, normalDot (p,Y) = t.normalDot (p,Y)
  action_agrees : ∀ p, p.1 > 0 → p.2 ∈ W.carrier → p.2.1 > 0 → ∀ Y, action (p,Y) = t.action (p,Y)
  damping_agrees : ∀ p, p.1 > 0 → p.2 ∈ W.carrier → p.2.1 > 0 → ∀ Y, damping (p,Y) = t.damping (p,Y)

namespace TangentGeometry

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {t : TangentData Parameter Space} (v : TangentGeometry W t)
  (source : FieldContinuation W (fun x => t.source (toChart x)))

noncomputable def referencePrimitives : ReferencePrimitives W t.linearData where
  coefficient x := TangentODE.projectedOperator (v.normal x) (v.normalDot x) (v.action x) (v.damping x)
  forcingMap x := negativeTangentProjection (v.normal x)
  coefficient_smooth := (projectedOperator_smooth v.normal_smooth v.normalDot_smooth v.action_smooth
    v.damping_smooth v.normal_ne).1
  forcingMap_smooth := (projectedOperator_smooth v.normal_smooth v.normalDot_smooth v.action_smooth
    v.damping_smooth v.normal_ne).2
  source := source
  coefficient_agrees p hp hW ht Y := by
    simp only [v.normal_agrees p hp hW ht, v.normalDot_agrees p hp hW ht,
      v.action_agrees p hp hW ht, v.damping_agrees p hp hW ht, TangentData.linearData]
  forcingMap_agrees p hp hW ht Y := by
    simp only [v.normal_agrees p hp hW ht, TangentData.linearData]

noncomputable def pressurePrimitives (frequency : ℝ) :
    ReadoutPrimitives W (fun x => pressureSolutionMap frequency (t.normal x) (t.normalDot x) (t.action x))
      (fun x => pressureSourceMap frequency (t.normal x)) where
  solutionMap x := pressureSolutionMap frequency (v.normal x) (v.normalDot x) (v.action x)
  sourceMap x := pressureSourceMap frequency (v.normal x)
  solutionMap_smooth := (pressure_maps_smooth frequency v.normal_smooth v.normalDot_smooth v.action_smooth v.normal_ne).1
  sourceMap_smooth := (pressure_maps_smooth frequency v.normal_smooth v.normalDot_smooth v.action_smooth v.normal_ne).2
  solutionMap_agrees p hp hW ht Y := by
    rw [v.normal_agrees p hp hW ht, v.normalDot_agrees p hp hW ht, v.action_agrees p hp hW ht]
  sourceMap_agrees p hp hW ht Y := by rw [v.normal_agrees p hp hW ht]

theorem readout_eq_pressure (frequency : ℝ) (g : Geometry) {entry exit : ℝ}
    (hle : entry ≤ exit) (cutoff : Plane → ℝ) (x : Chart) :
    readoutCommon t.linearData g hle cutoff
      (fun x => pressureSolutionMap frequency (t.normal x) (t.normalDot x) (t.action x))
      (fun x => pressureSourceMap frequency (t.normal x)) x =
      ∑' k : Frequency, cutoff (g.coordinates k x.2) • ParticularWaveBounds.copyPressure t g hle k frequency x := by
  apply tsum_congr
  intro k
  simp only [readoutCopy, pressure_maps_eq, ParticularWaveBounds.copyPressure,
    ParticularWaveBounds.copyPressureReal, ParticularWaveBounds.nativePoint, TangentData.linearData]

noncomputable def pressureContinuation (frequency : ℝ) (g : Geometry) {entry exit : ℝ}
    (hle : entry ≤ exit) {cutoff : Plane → ℝ} (hcutoff : ContDiff ℝ ∞ cutoff)
    (hcompact : HasCompactSupport cutoff) (hinside : tsupport cutoff ⊆ univ ×ˢ Ioo entry exit) :
    FieldContinuation W (fun x => ∑' k : Frequency,
      cutoff (g.coordinates k x.2.2) • ParticularWaveBounds.copyPressure t g hle k frequency (toChart x)) := by
  let e := (v.pressurePrimitives frequency).continuation (v.referencePrimitives source) g hle hcutoff hcompact hinside
  refine ⟨e.value, e.smooth, e.supported, ?_⟩
  intro x hx
  exact (e.agrees hx).trans (readout_eq_pressure frequency g hle cutoff (toChart x))

end TangentGeometry

end TangentGeometry

namespace FieldContinuation

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : Point → E}

noncomputable def retarget (e : FieldContinuation W f) (h : ∀ x, f x = g x) :
    FieldContinuation W g where
  value := e.value
  smooth := e.smooth
  supported := e.supported
  agrees := fun x hx => (e.agrees hx).trans (h x)

noncomputable def add (e : FieldContinuation W f) (d : FieldContinuation W g) :
    FieldContinuation W (fun x => f x + g x) where
  value x := e.value x + d.value x
  smooth := e.smooth.add d.smooth
  supported := by
    intro x hx hn
    by_contra hr
    have he : e.value x = 0 := by
      by_contra hz
      exact hr (e.supported x hx hz)
    have hd : d.value x = 0 := by
      by_contra hz
      exact hr (d.supported x hx hz)
    exact hn (by simp [he, hd])
  agrees := fun x hx => congrArg₂ (· + ·) (e.agrees hx) (d.agrees hx)

noncomputable def ofScalar {f : Point → ℝ}
    (e : OffplaneCorrectionExtensions.SupportedContinuation W f) : FieldContinuation W f :=
  ⟨e.value, e.smooth, e.supported, e.agrees⟩

end FieldContinuation

section ComplexReference

open ParticularWaveBounds

theorem commonVelocity_eq_parts (t : TangentData Parameter Space) (f : Chart → ComplexVector)
    (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit) {cutoff : Plane → ℝ}
    (hc : HasCompactSupport cutoff) (x : Chart) :
    commonVelocity t f g hle cutoff x =
      CurlClassBounds.complexify ((realData t f).linearData.commonSolve g hle cutoff x) +
      Complex.I • CurlClassBounds.complexify ((imagData t f).linearData.commonSolve g hle cutoff x) := by
  obtain ⟨I, hI⟩ := g.finite_copy_cutoffs hc ‖x.2‖
  have ht (k : Frequency) (hk : k ∉ I) : cutoff (g.coordinates k x.2) = 0 := hI _ le_rfl k hk
  simp only [commonVelocity, periodizedCopies, LinearData.commonSolve]
  rw [tsum_eq_sum (s := I) (fun k hk => by rw [ht k hk, zero_smul]),
    tsum_eq_sum (s := I) (fun k hk => by simp only [LinearData.localizedCopy, ht k hk, zero_smul]),
    tsum_eq_sum (s := I) (fun k hk => by simp only [LinearData.localizedCopy, ht k hk, zero_smul])]
  simp only [complexCopyVelocity, copyVelocity, LinearData.localizedCopy,
    smul_add, map_sum, map_smul, Finset.smul_sum, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact smul_comm _ _ _

theorem commonPressure_eq_parts (t : TangentData Parameter Space) (f : Chart → ComplexVector)
    (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit) {cutoff : Plane → ℝ}
    (hc : HasCompactSupport cutoff) (frequency : ℝ) (x : Chart) :
    commonPressure t f g hle cutoff frequency x =
      (∑' k : Frequency, cutoff (g.coordinates k x.2) • copyPressure (realData t f) g hle k frequency x) +
      Complex.I * (∑' k : Frequency, cutoff (g.coordinates k x.2) • copyPressure (imagData t f) g hle k frequency x) := by
  obtain ⟨I, hI⟩ := g.finite_copy_cutoffs hc ‖x.2‖
  have ht (k : Frequency) (hk : k ∉ I) : cutoff (g.coordinates k x.2) = 0 := hI _ le_rfl k hk
  simp only [commonPressure, periodizedCopies]
  rw [tsum_eq_sum (s := I) (fun k hk => by rw [ht k hk, zero_smul]),
    tsum_eq_sum (s := I) (fun k hk => by rw [ht k hk, zero_smul]),
    tsum_eq_sum (s := I) (fun k hk => by rw [ht k hk, zero_smul])]
  simp only [complexCopyPressure, smul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Algebra.smul_def]
  ring

namespace TangentGeometry

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {t : TangentData Parameter Space} (v : TangentGeometry W t)

/-- Changing the forcing does not choose another frame or homogeneous ODE. -/
noncomputable def withSource (f : Chart → Space) : TangentGeometry W {t with source := f} where
  normal := v.normal
  normalDot := v.normalDot
  action := v.action
  damping := v.damping
  normal_smooth := v.normal_smooth
  normalDot_smooth := v.normalDot_smooth
  action_smooth := v.action_smooth
  damping_smooth := v.damping_smooth
  normal_ne := v.normal_ne
  normal_agrees := v.normal_agrees
  normalDot_agrees := v.normalDot_agrees
  action_agrees := v.action_agrees
  damping_agrees := v.damping_agrees

noncomputable def continuedData (f : Chart → Space) : TangentData Parameter Space where
  normal := v.normal
  normalDot := v.normalDot
  action := v.action
  damping := v.damping
  source := f

variable {f : Chart → ComplexVector}
  (source : FieldContinuation W (fun x => f (toChart x)))

noncomputable def complexVelocityContinuation (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit)
    {cutoff : Plane → ℝ} (hcutoff : ContDiff ℝ ∞ cutoff) (hcompact : HasCompactSupport cutoff)
    (hinside : tsupport cutoff ⊆ univ ×ˢ Ioo entry exit) :
    FieldContinuation W (fun x => commonVelocity t f g hle cutoff (toChart x)) := by
  let er := ((v.withSource (fun x => realPart (f x))).referencePrimitives (source.map realPart)).continuation
    g hle hcutoff hcompact hinside
  let ei := ((v.withSource (fun x => imagPart (f x))).referencePrimitives (source.map imagPart)).continuation
    g hle hcutoff hcompact hinside
  exact ((er.map CurlClassBounds.complexify).add
    (ei.map ((complexScale Complex.I).comp CurlClassBounds.complexify))).retarget
      (fun x => (commonVelocity_eq_parts t f g hle hcompact (toChart x)).symm)

theorem complexVelocityContinuation_value (g : Geometry) {entry exit : ℝ} (hle : entry ≤ exit)
    {cutoff : Plane → ℝ} (hcutoff : ContDiff ℝ ∞ cutoff) (hcompact : HasCompactSupport cutoff)
    (hinside : tsupport cutoff ⊆ univ ×ˢ Ioo entry exit) (x : Point) :
    (v.complexVelocityContinuation source g hle hcutoff hcompact hinside).value x =
      commonVelocity (v.continuedData (fun _ => 0)) (fun y => source.value (ofChart y))
        g hle cutoff (toChart x) := by
  symm
  exact commonVelocity_eq_parts _ _ g hle hcompact (toChart x)

noncomputable def complexPressureContinuation (frequency : ℝ) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) {cutoff : Plane → ℝ}
    (hcutoff : ContDiff ℝ ∞ cutoff) (hcompact : HasCompactSupport cutoff)
    (hinside : tsupport cutoff ⊆ univ ×ˢ Ioo entry exit) :
    FieldContinuation W (fun x => commonPressure t f g hle cutoff frequency (toChart x)) := by
  let er := (v.withSource (fun x => realPart (f x))).pressureContinuation (source.map realPart)
    frequency g hle hcutoff hcompact hinside
  let ei := (v.withSource (fun x => imagPart (f x))).pressureContinuation (source.map imagPart)
    frequency g hle hcutoff hcompact hinside
  exact (er.add (ei.map ((ContinuousLinearMap.mul ℝ ℂ) Complex.I))).retarget
    (fun x => (commonPressure_eq_parts t f g hle hcompact frequency (toChart x)).symm)

theorem complexPressureContinuation_value (frequency : ℝ) (g : Geometry)
    {entry exit : ℝ} (hle : entry ≤ exit) {cutoff : Plane → ℝ}
    (hcutoff : ContDiff ℝ ∞ cutoff) (hcompact : HasCompactSupport cutoff)
    (hinside : tsupport cutoff ⊆ univ ×ˢ Ioo entry exit) (x : Point) :
    (v.complexPressureContinuation source frequency g hle hcutoff hcompact hinside).value x =
      commonPressure (v.continuedData (fun _ => 0)) (fun y => source.value (ofChart y))
        g hle cutoff frequency (toChart x) := by
  dsimp only [complexPressureContinuation, FieldContinuation.retarget, FieldContinuation.add,
    FieldContinuation.map, pressureContinuation, ReadoutPrimitives.continuation]
  rw [commonPressure_eq_parts _ _ g hle hcompact frequency (toChart x)]
  congr 1
  · exact readout_eq_pressure
      (t := realData (v.continuedData (fun _ => 0)) (fun y => source.value (ofChart y)))
      frequency g hle cutoff (toChart x)
  · exact congrArg (fun z => Complex.I * z) (readout_eq_pressure
      (t := imagData (v.continuedData (fun _ => 0)) (fun y => source.value (ofChart y)))
      frequency g hle cutoff (toChart x))

end TangentGeometry

end ComplexReference

namespace FieldContinuation

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Point → E}

theorem zero_germ (e : FieldContinuation W f) (hc : 0 < coord) (hc1 : coord < 1)
    {x : Point} (hx : x.2.1 ∈ W.carrier)
    (hr : x.1 ∉ Icc (OffplaneCorrectionExtensions.stableLength coord x.2.1 * a)
      (OffplaneCorrectionExtensions.stableLength coord x.2.1 * b)) :
    e.value =ᶠ[𝓝 x] fun _ => 0 := by
  have hn : x ∉ movingCarrier W := fun h => hr (h hx)
  filter_upwards [(movingCarrier_closed W hc hc1).isOpen_compl.mem_nhds hn,
    (PhysicalMeanDomain.slowDomain_open W.isOpen).mem_nhds hx] with y hy hyU
  by_contra hf
  exact hy (fun _ => e.supported y hyU hf)

noncomputable def derivative (e : FieldContinuation W f) (hc : 0 < coord) (hc1 : coord < 1) :
    FieldContinuation W (fderiv ℝ f) where
  value := fderiv ℝ e.value
  smooth := ((contDiffOn_infty_iff_fderiv_of_isOpen
    (PhysicalMeanDomain.slowDomain_open W.isOpen)).mp e.smooth).2
  supported := by
    intro x hx hn
    by_contra hr
    apply hn
    rw [(e.zero_germ hc hc1 hx hr).fderiv_eq, fderiv_fun_const]
    rfl
  agrees := fun x hx => (e.agrees.eventuallyEq W.isOpen hx.1 hx.2).fderiv_eq

/-- A primitive multiplier may be singular on the axis: the source has
an actual zero neighborhood there. Its positive-fiber agreement is the
only identification used below. -/
noncomputable def linear (e : FieldContinuation W f)
    (L L₀ : Point → E →L[ℝ] F)
    (hL : ContDiffOn ℝ ∞ L (LocalRankDefect.positiveDomain W.carrier))
    (heq : ∀ x, x.2.1 ∈ W.carrier → 0 < x.2.1.1 → 0 < x.1 → L x = L₀ x) :
    FieldContinuation W (fun x => L₀ x (f x)) where
  value x := L x (e.value x)
  smooth := by
    apply (PhysicalMeanDomain.slowDomain_open W.isOpen).contDiffOn_iff.mpr
    intro x hx
    by_cases hr : 0 < x.1
    · exact (hL.contDiffAt ((LocalRankDefect.positiveDomain_open W.isOpen).mem_nhds
        (show x ∈ LocalRankDefect.positiveDomain W.carrier from ⟨hr, hx⟩))).clm_apply
        (e.smooth.contDiffAt ((PhysicalMeanDomain.slowDomain_open W.isOpen).mem_nhds hx))
    · have hz : (fun y => L y (e.value y)) =ᶠ[𝓝 x] fun _ => (0 : F) := by
        filter_upwards [(PhysicalMeanDomain.slowDomain_open W.isOpen).mem_nhds hx,
          (isOpen_lt continuous_fst continuous_const).mem_nhds
            (show x.1 < W.lower from lt_of_le_of_lt (le_of_not_gt hr) W.lower_pos)] with y hy hyr
        rw [e.zero_below hy hyr, map_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  supported := fun x hx hn => e.supported x hx (fun hz => hn (by simp only [hz, map_zero]))
  agrees := by
    intro x hx
    change L x (e.value x) = L₀ x (f x)
    by_cases hr : 0 < x.1
    · rw [heq x hx.1 hx.2 hr, e.agrees hx]
    · have hz := e.zero_below hx.1 (lt_of_le_of_lt (le_of_not_gt hr) W.lower_pos)
      have hz₀ := (e.agrees hx).symm.trans hz
      rw [hz, hz₀, map_zero, map_zero]

noncomputable def along (e : FieldContinuation W f) (hc : 0 < coord) (hc1 : coord < 1)
    (V V₀ : Point → Point)
    (hV : ContDiffOn ℝ ∞ V (LocalRankDefect.positiveDomain W.carrier))
    (heq : ∀ x, x.2.1 ∈ W.carrier → 0 < x.2.1.1 → 0 < x.1 → V x = V₀ x) :
    FieldContinuation W (HarmonicCalculus.along V₀ f) where
  value x := fderiv ℝ e.value x (V x)
  smooth := by
    apply (PhysicalMeanDomain.slowDomain_open W.isOpen).contDiffOn_iff.mpr
    intro x hx
    by_cases hr : 0 < x.1
    · exact ((e.derivative hc hc1).smooth.contDiffAt
        ((PhysicalMeanDomain.slowDomain_open W.isOpen).mem_nhds hx)).clm_apply
        (hV.contDiffAt ((LocalRankDefect.positiveDomain_open W.isOpen).mem_nhds ⟨hr, hx⟩))
    · have hz : (fun y => fderiv ℝ e.value y (V y)) =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [(PhysicalMeanDomain.slowDomain_open W.isOpen).mem_nhds hx,
          (isOpen_lt continuous_fst continuous_const).mem_nhds
            (show x.1 < W.lower from lt_of_le_of_lt (le_of_not_gt hr) W.lower_pos)] with y hy hyr
        have he := (e.derivative hc hc1).zero_below hy hyr
        change fderiv ℝ e.value y = 0 at he
        rw [he, _root_.zero_apply]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  supported := by
    intro x hx hn
    exact (e.derivative hc hc1).supported x hx (fun hz => hn (by
      change fderiv ℝ e.value x = 0 at hz
      simp only [hz, _root_.zero_apply]))
  agrees := by
    intro x hx
    change fderiv ℝ e.value x (V x) = fderiv ℝ f x (V₀ x)
    have hd := (e.derivative hc hc1).agrees hx
    change fderiv ℝ e.value x = fderiv ℝ f x at hd
    by_cases hr : 0 < x.1
    · rw [hd, heq x hx.1 hx.2 hr]
    · have hz := (e.derivative hc hc1).zero_below hx.1
        (lt_of_le_of_lt (le_of_not_gt hr) W.lower_pos)
      change fderiv ℝ e.value x = 0 at hz
      rw [← hd, hz, _root_.zero_apply, _root_.zero_apply]

end FieldContinuation

section PrimitiveCurl

/-- Primitive geometric fields only; all differential output continuations
are computed from these fields and a supported incoming coefficient. -/
structure CurlPrimitives {coord a b : ℝ} (W : OffplaneCorrectionExtensions.Window coord a b)
    (R₀ : Point → ℝ) (Vr₀ Vθ₀ Vz₀ : Point → Point) (Φ₀ : Point → ℝ) where
  radius : Point → ℝ
  radial : Point → Point
  angular : Point → Point
  axial : Point → Point
  phase : Point → ℝ
  radius_smooth : ContDiffOn ℝ ∞ radius (LocalRankDefect.positiveDomain W.carrier)
  radial_smooth : ContDiffOn ℝ ∞ radial (LocalRankDefect.positiveDomain W.carrier)
  angular_smooth : ContDiffOn ℝ ∞ angular (LocalRankDefect.positiveDomain W.carrier)
  axial_smooth : ContDiffOn ℝ ∞ axial (LocalRankDefect.positiveDomain W.carrier)
  phase_smooth : ContDiffOn ℝ ∞ phase (LocalRankDefect.positiveDomain W.carrier)
  radius_ne : ∀ x ∈ LocalRankDefect.positiveDomain W.carrier, radius x ≠ 0
  normal_ne : ∀ x ∈ LocalRankDefect.positiveDomain W.carrier,
    phaseNormal radius radial angular axial phase x ≠ 0
  radius_agrees : OffplaneCorrectionExtensions.FiberAgreement W.carrier radius R₀
  radial_agrees : OffplaneCorrectionExtensions.FiberAgreement W.carrier radial Vr₀
  angular_agrees : OffplaneCorrectionExtensions.FiberAgreement W.carrier angular Vθ₀
  axial_agrees : OffplaneCorrectionExtensions.FiberAgreement W.carrier axial Vz₀
  phase_agrees : OffplaneCorrectionExtensions.FiberAgreement W.carrier phase Φ₀

namespace CurlPrimitives

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {R₀ : Point → ℝ} {Vr₀ Vθ₀ Vz₀ : Point → Point} {Φ₀ : Point → ℝ}
  (p : CurlPrimitives W R₀ Vr₀ Vθ₀ Vz₀ Φ₀)

theorem normal_smooth : ContDiffOn ℝ ∞
    (phaseNormal p.radius p.radial p.angular p.axial p.phase)
    (LocalRankDefect.positiveDomain W.carrier) := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact HarmonicCalculus.contDiffOn_along (LocalRankDefect.positiveDomain_open W.isOpen)
      p.radial_smooth p.phase_smooth
  · exact (HarmonicCalculus.contDiffOn_along (LocalRankDefect.positiveDomain_open W.isOpen)
      p.angular_smooth p.phase_smooth).div p.radius_smooth p.radius_ne
  · exact HarmonicCalculus.contDiffOn_along (LocalRankDefect.positiveDomain_open W.isOpen)
      p.axial_smooth p.phase_smooth

theorem normal_agrees : OffplaneCorrectionExtensions.FiberAgreement W.carrier
    (phaseNormal p.radius p.radial p.angular p.axial p.phase)
    (phaseNormal R₀ Vr₀ Vθ₀ Vz₀ Φ₀) := by
  intro x hx
  have hd : fderiv ℝ p.phase x = fderiv ℝ Φ₀ x :=
    (p.phase_agrees.eventuallyEq W.isOpen hx.1 hx.2).fderiv_eq
  simp only [phaseNormal, HarmonicCalculus.along, hd, p.radial_agrees hx,
    p.angular_agrees hx, p.axial_agrees hx, p.radius_agrees hx]

noncomputable def normalMap (N : Space) : ComplexVector →L[ℝ] ComplexVector :=
  (‖N‖ ^ 2)⁻¹ • CurlClassBounds.complexCrossLinear (CurlClassBounds.complexify N)

theorem normalMap_apply (N : Space) (u : ComplexVector) :
    normalMap N u = CurlClassBounds.normalCoefficient N u := rfl

theorem normalMap_smooth : ContDiffOn ℝ ∞
    (fun x => normalMap (phaseNormal p.radius p.radial p.angular p.axial p.phase x))
    (LocalRankDefect.positiveDomain W.carrier) := by
  exact (((contDiff_norm_sq ℝ).comp_contDiffOn p.normal_smooth).inv
    (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr (p.normal_ne x hx)))).smul
      (CurlClassBounds.complexCrossLinear.contDiff.comp_contDiffOn
        (CurlClassBounds.complexify.contDiff.comp_contDiffOn p.normal_smooth))

noncomputable def coefficient {f : Point → ComplexVector} (e : FieldContinuation W f) :
    FieldContinuation W (CurlClassBounds.coefficient R₀ Vr₀ Vθ₀ Vz₀ Φ₀ f) :=
  e.linear
    (fun x => normalMap (phaseNormal p.radius p.radial p.angular p.axial p.phase x))
    (fun x => normalMap (phaseNormal R₀ Vr₀ Vθ₀ Vz₀ Φ₀ x)) p.normalMap_smooth
    (fun x hx ht _ => congrArg normalMap (p.normal_agrees (show x ∈
      PhysicalMeanDomain.slowDomain (W.carrier ∩ OffplaneCorrectionExtensions.positiveSlow) from ⟨hx, ht⟩)))

theorem complexScale_smooth : ContDiff ℝ ∞ ParticularWaveBounds.complexScale := by
  have he (c : ℂ) : ParticularWaveBounds.complexScale c =
      c.re • ContinuousLinearMap.id ℝ ComplexVector +
        c.im • ParticularWaveBounds.complexScale Complex.I := by
    ext u i
    simp only [ParticularWaveBounds.complexScale_apply, _root_.add_apply,
      _root_.smul_apply, ContinuousLinearMap.id_apply, Pi.add_apply,
      Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    have hc : (c.re : ℂ) + (c.im : ℂ) * Complex.I = c := Complex.re_add_im c
    calc
      c * u i = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * u i :=
        congrArg (fun z => z * u i) hc.symm
      _ = _ := by ring
  have hs : ContDiff ℝ ∞ (fun c : ℂ => c.re • ContinuousLinearMap.id ℝ ComplexVector +
      c.im • ParticularWaveBounds.complexScale Complex.I) :=
    (Complex.reCLM.contDiff.smul contDiff_const).add (Complex.imCLM.contDiff.smul contDiff_const)
  rw [funext he]
  exact hs

noncomputable def potential {f : Point → ComplexVector} (e : FieldContinuation W f) (K : ℝ) :
    FieldContinuation W (CurlClassBounds.vectorPotential K R₀ Vr₀ Vθ₀ Vz₀ Φ₀ f) := by
  let d := (p.coefficient e).map (ParticularWaveBounds.complexScale (CurlClassBounds.inverseCarrier K))
  let m := d.linear
    (fun x => ParticularWaveBounds.complexScale (carrier K p.phase x))
    (fun x => ParticularWaveBounds.complexScale (carrier K Φ₀ x))
    (complexScale_smooth.comp_contDiffOn
      (contDiffOn_carrier K p.phase_smooth))
    (fun x hx ht _ => by simp only [carrier, p.phase_agrees (show x ∈
      PhysicalMeanDomain.slowDomain (W.carrier ∩ OffplaneCorrectionExtensions.positiveSlow) from ⟨hx, ht⟩)])
  exact m.retarget (fun x => by
    ext i
    simp only [ParticularWaveBounds.complexScale_apply, Pi.smul_apply, smul_eq_mul,
      CurlClassBounds.vectorPotential, vectorMode, HarmonicCalculus.mode]
    ring)

noncomputable def curl {f : Point → ComplexVector} (e : FieldContinuation W f)
    (hc : 0 < coord) (hc1 : coord < 1) :
    FieldContinuation W (CurlClassBounds.cylindricalCurl R₀ Vr₀ Vθ₀ Vz₀ f) where
  value := CurlClassBounds.cylindricalCurl p.radius p.radial p.angular p.axial e.value
  smooth := by
    have hs := CurlClassBounds.cylindricalCurl_contDiffOn
      (LocalRankDefect.positiveDomain_open W.isOpen) (p.radius_smooth.inv p.radius_ne)
      p.radial_smooth p.angular_smooth p.axial_smooth
      (e.smooth.mono (fun _ hx => hx.2))
    apply (PhysicalMeanDomain.slowDomain_open W.isOpen).contDiffOn_iff.mpr
    intro x hx
    by_cases hr : 0 < x.1
    · exact hs.contDiffAt ((LocalRankDefect.positiveDomain_open W.isOpen).mem_nhds ⟨hr, hx⟩)
    · have hxR : x.1 ∉ Icc (OffplaneCorrectionExtensions.stableLength coord x.2.1 * a)
          (OffplaneCorrectionExtensions.stableLength coord x.2.1 * b) := by
        intro h
        exact (not_lt_of_ge (le_of_not_gt hr)) (W.lower_pos.trans_le ((W.left _ hx).trans h.1))
      have he := ParticularWaveAssembly.curl_germ (e.zero_germ hc hc1 hx hxR)
        p.radius p.radial p.angular p.axial
      rw [PeriodizedWaveBounds.cylindricalCurl_zero] at he
      exact contDiffAt_const.congr_of_eventuallyEq he
  supported := by
    classical
    intro x hx hn
    by_contra hr
    apply hn
    have he := ParticularWaveAssembly.curl_germ (e.zero_germ hc hc1 hx hr)
      p.radius p.radial p.angular p.axial
    simpa only [PeriodizedWaveBounds.cylindricalCurl_zero] using he.self_of_nhds
  agrees := by
    intro x hx
    have he := (ParticularWaveAssembly.curl_germ
      (e.agrees.eventuallyEq W.isOpen hx.1 hx.2) p.radius p.radial p.angular p.axial).self_of_nhds
    change CurlClassBounds.cylindricalCurl p.radius p.radial p.angular p.axial e.value x = _
    rw [he]
    simp only [CurlClassBounds.cylindricalCurl, HarmonicCalculus.along,
      p.radius_agrees hx, p.radial_agrees hx, p.angular_agrees hx, p.axial_agrees hx]

noncomputable def corrected {f : Point → ComplexVector} (e : FieldContinuation W f)
    (hc : 0 < coord) (hc1 : coord < 1) (K : ℝ) :
    FieldContinuation W (CurlClassBounds.realizedCoefficient K R₀ Vr₀ Vθ₀ Vz₀ Φ₀ f) :=
  (e.add ((p.curl (p.coefficient e) hc hc1).map
    (ParticularWaveBounds.complexScale (CurlClassBounds.inverseCarrier K)))).retarget
      (fun x => by rw [CurlClassBounds.realizedCoefficient, CurlClassBounds.curlRemainder_eq]; rfl)

end CurlPrimitives

end PrimitiveCurl

section LocalPhysical

open ProblemStatement PhysicalCurlCovariance

theorem polarCoordinates_slow (delta : ℝ) (j : PolarCharts.Index) (z : SpaceTime) :
    OffplaneCorrectionExtensions.physicalSlow (polarCoordinates delta j z) =
      OffplaneCorrectionExtensions.physicalSlow z := by
  simp only [OffplaneCorrectionExtensions.physicalSlow, polarCoordinates,
    AxisymmetricResidual.pack_two]

/-- Polar gluing on an actual open slow window, rather than on all axial
coordinates. The period is the complete carrier period. -/
theorem cartesian_smooth_on_slow {delta : ℝ} (hd : 0 < delta)
    {U : Set Slow} (hU : IsOpen U) {B : SpaceTime → ComplexVector}
    (hB : ContDiffOn ℝ ∞ B {z | OffplaneCorrectionExtensions.physicalSlow z ∈ U ∧ 0 < z.2 0})
    (hper : ∀ t r z : ℝ, Periodic (fun theta => B (t, AxisymmetricResidual.pack r theta z)) (2 * Real.pi))
    (hzero : ∀ z : SpaceTime, z.2 0 ≤ delta → B z = 0) :
    ContDiffOn ℝ ∞ (globalCartesianPotential delta B)
      (OffplaneCorrectionExtensions.physicalDomain U) := by
  apply (OffplaneCorrectionExtensions.physicalDomain_open hU).contDiffOn_iff.mpr
  intro x hx
  by_cases hex : ∃ j : PolarCharts.Index,
      PhysicalGraphBounds.radialProjection x ∈ PolarCharts.chartDomain delta j
  · obtain ⟨j, hj⟩ := hex
    have hrot : 0 < (PolarCharts.rotate j (PhysicalGraphBounds.radialProjection x)).1 := by
      have hv : delta / 4 < (PolarCharts.rotate j (PhysicalGraphBounds.radialProjection x)).1 := hj
      linarith
    have hrad : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection x) := by
      rw [← PolarCharts.radius_rotate j]
      exact PolarCharts.radius_pos_of_fst_pos hrot
    have hz : OffplaneCorrectionExtensions.physicalSlow (polarCoordinates delta j x) ∈ U ∧
        0 < (polarCoordinates delta j x).2 0 := by
      rw [polarCoordinates_slow, polarCoordinates_radius hd j hj]
      exact ⟨hx, hrad⟩
    have hopen : IsOpen {z : SpaceTime | OffplaneCorrectionExtensions.physicalSlow z ∈ U ∧ 0 < z.2 0} :=
      (OffplaneCorrectionExtensions.physicalDomain_open hU).inter
        (isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous)
    exact (cartesianPotential_smoothAt hd j (hB.contDiffAt (hopen.mem_nhds hz))).congr_of_eventuallyEq
      (globalCartesianPotential_germ_local hd B hper j hj)
  · have hnorm : ‖PhysicalGraphBounds.radialProjection x‖ ≤ delta / 4 := by
      obtain ⟨j, hj⟩ := PolarCharts.exists_rotate_fst_ge (p := PhysicalGraphBounds.radialProjection x) le_rfl
      by_contra hh
      exact hex ⟨j, lt_of_lt_of_le (lt_of_not_ge hh) hj⟩
    have hrad : PolarCharts.radius (PhysicalGraphBounds.radialProjection x) < delta := by
      have hb := PolarCharts.radius_le_two_norm (PhysicalGraphBounds.radialProjection x)
      linarith
    exact contDiffAt_const.congr_of_eventuallyEq (globalCartesianPotential_zero_germ hd hzero hrad)

theorem cartesian_eq_of_slow_fiber {delta : ℝ} {B C : SpaceTime → ComplexVector}
    {x : SpaceTime}
    (he : ∀ z : SpaceTime, OffplaneCorrectionExtensions.physicalSlow z =
      OffplaneCorrectionExtensions.physicalSlow x → B z = C z) :
    globalCartesianPotential delta B x = globalCartesianPotential delta C x := by
  unfold globalCartesianPotential
  split_ifs with h
  · unfold cartesianPotential
    rw [he _ (polarCoordinates_slow _ _ _)]
  · rfl

namespace PhysicalNative

/-- The actual scaled graph with the angular coordinate omitted.  The
reference common-cover index remains in `G.fastCoefficient`. -/
noncomputable def point (G : PhysicalResidualBridge.ScaledGraph) (z : SpaceTime) : Point :=
  (G.radialScale * z.2 0,
    ((G.velocityScale * G.radialScale * G.epsilon * (1 - z.1), G.radialScale * G.epsilon * z.2 2),
      (G.frequency * (G.radialScale * z.2 0) ^ G.exponent) • G.radialVector +
        (G.velocityScale * G.radialScale * G.fastCoefficient * z.1) • G.temporalVector))

noncomputable def slow (G : PhysicalResidualBridge.ScaledGraph) (s : Slow) : Slow :=
  (G.velocityScale * G.radialScale * G.epsilon * s.1, G.radialScale * G.epsilon * s.2)

theorem slow_smooth (G : PhysicalResidualBridge.ScaledGraph) : ContDiff ℝ ∞ (slow G) :=
  (contDiff_const.mul contDiff_fst).prodMk (contDiff_const.mul contDiff_snd)

theorem point_slow (G : PhysicalResidualBridge.ScaledGraph) (z : SpaceTime) :
    (point G z).2.1 = slow G (OffplaneCorrectionExtensions.physicalSlow z) := rfl

theorem point_eq_native (h Q : ℝ) (i : ℕ) (z : SpaceTime) :
    point (PhysicalResidualBridge.commonGraph Q h i) z =
      ofChart ((PhysicalParticularWave.nativeMap h Q i z).1.1,
        (PhysicalParticularWave.nativeMap h Q i z).2) := rfl

theorem point_smoothAt (G : PhysicalResidualBridge.ScaledGraph) {z : SpaceTime}
    (hr : G.radialScale * z.2 0 ≠ 0) : ContDiffAt ℝ ∞ (point G) z := by
  have h := G.map_smoothAt hr
  exact h.fst.fst.prodMk ((h.fst.snd.fst.snd.prodMk h.fst.snd.fst.fst).prodMk h.fst.snd.snd)

theorem point_invariant (G : PhysicalResidualBridge.ScaledGraph) :
    CopyAngularInvariance.Invariant ((0 : ℝ), coordinateVector 1) (point G) := by
  intro z t
  simp [point, coordinateVector]

variable {coord a b : ℝ} (W : OffplaneCorrectionExtensions.Window coord a b)
  (G : PhysicalResidualBridge.ScaledGraph)

noncomputable def window : Set Slow := slow G ⁻¹' W.carrier

theorem window_open : IsOpen (window W G) := W.isOpen.preimage (slow_smooth G).continuous

noncomputable def positiveDomain : Set SpaceTime :=
  {z | OffplaneCorrectionExtensions.physicalSlow z ∈ window W G ∧ 0 < z.2 0}

theorem positiveDomain_open : IsOpen (positiveDomain W G) :=
  (OffplaneCorrectionExtensions.physicalDomain_open (window_open W G)).inter
    (isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous)

noncomputable def amplitude {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (e : FieldContinuation W f) (scale : ℝ) (z : SpaceTime) : E := by
  classical
  exact if OffplaneCorrectionExtensions.physicalSlow z ∈ window W G then scale • e.value (point G z) else 0

theorem amplitude_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (e : FieldContinuation W f) (scale : ℝ) (hr : 0 < G.radialScale) :
    ContDiffOn ℝ ∞ (amplitude W G e scale) (positiveDomain W G) := by
  apply (positiveDomain_open W G).contDiffOn_iff.mpr
  intro z hz
  have hpoint := point_smoothAt G (mul_pos hr hz.2).ne'
  have hf := (e.smooth.contDiffAt ((PhysicalMeanDomain.slowDomain_open W.isOpen).mem_nhds
    (show (point G z).2.1 ∈ W.carrier from hz.1))).comp z hpoint
  apply (hf.const_smul scale).congr_of_eventuallyEq
  filter_upwards [(OffplaneCorrectionExtensions.physicalDomain_open (window_open W G)).mem_nhds hz.1] with y hy
  have hy' : OffplaneCorrectionExtensions.physicalSlow y ∈ window W G := hy
  simp only [amplitude, ite_eq_left hy', Function.comp_apply]

theorem amplitude_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (e : FieldContinuation W f) (scale : ℝ)
    {delta : ℝ} (hdelta : G.radialScale * delta < W.lower) (hr : 0 ≤ G.radialScale)
    (z : SpaceTime) (hz : z.2 0 ≤ delta) : amplitude W G e scale z = 0 := by
  unfold amplitude
  split_ifs with hw
  · have he := e.zero_below (x := point G z) hw
      ((mul_le_mul_of_nonneg_left hz hr).trans_lt hdelta)
    rw [he, smul_zero]
  · rfl

theorem amplitude_invariant {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (e : FieldContinuation W f) (scale : ℝ) :
    CopyAngularInvariance.Invariant ((0 : ℝ), coordinateVector 1) (amplitude W G e scale) := by
  intro z t
  have hs : OffplaneCorrectionExtensions.physicalSlow (z + t • ((0 : ℝ), coordinateVector 1)) =
      OffplaneCorrectionExtensions.physicalSlow z := by
    simp [OffplaneCorrectionExtensions.physicalSlow, coordinateVector]
  simp only [amplitude]
  rw [hs, point_invariant G z t]

theorem amplitude_agrees {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (e : FieldContinuation W f) (scale : ℝ)
    (htime : 0 < G.velocityScale * G.radialScale * G.epsilon) {z : SpaceTime}
    (hz : OffplaneCorrectionExtensions.physicalSlow z ∈ window W G) (ht : z.1 < 1) :
    amplitude W G e scale z = scale • f (point G z) := by
  simp only [amplitude, ite_eq_left hz]
  exact congrArg (scale • ·) (e.agrees ⟨hz, mul_pos htime (sub_pos.mpr ht)⟩)

noncomputable def phase (phi : Point → ℝ) (slope : ℝ) (z : SpaceTime) : ℝ :=
  phi (point G z) + slope * z.2 1

theorem phase_affine (phi : Point → ℝ) (slope : ℝ) :
    CopyAngularInvariance.AffinePhase ((0 : ℝ), coordinateVector 1) slope (phase G phi slope) := by
  intro z t
  simp only [phase, point_invariant G z t]
  simp only [Prod.snd_add, Prod.smul_snd, PiLp.add_apply, PiLp.smul_apply,
    coordinateVector, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
  ring

theorem phase_smooth {phi : Point → ℝ}
    (hphi : ContDiffOn ℝ ∞ phi (LocalRankDefect.positiveDomain W.carrier))
    (slope : ℝ) (hr : 0 < G.radialScale) :
    ContDiffOn ℝ ∞ (phase G phi slope) (positiveDomain W G) := by
  apply (positiveDomain_open W G).contDiffOn_iff.mpr
  intro z hz
  have hpos : 0 < (point G z).1 := mul_pos hr hz.2
  have hp : point G z ∈ LocalRankDefect.positiveDomain W.carrier := ⟨hpos, hz.1⟩
  exact ((hphi.contDiffAt ((LocalRankDefect.positiveDomain_open W.isOpen).mem_nhds hp)).comp z
    (point_smoothAt G hpos.ne')).add
      (contDiffAt_const.mul (PhysicalGraphBounds.coordinateProjection 1).contDiff.contDiffAt)

theorem phase_agrees {phi phi₀ : Point → ℝ}
    (he : OffplaneCorrectionExtensions.FiberAgreement W.carrier phi phi₀) (slope : ℝ)
    (htime : 0 < G.velocityScale * G.radialScale * G.epsilon) {z : SpaceTime}
    (hz : OffplaneCorrectionExtensions.physicalSlow z ∈ window W G) (ht : z.1 < 1) :
    phase G phi slope z = phase G phi₀ slope z := by
  unfold phase
  rw [he (show point G z ∈ PhysicalMeanDomain.slowDomain
    (W.carrier ∩ OffplaneCorrectionExtensions.positiveSlow) from ⟨hz, mul_pos htime (sub_pos.mpr ht)⟩)]

theorem phase_germ {phi phi₀ : Point → ℝ}
    (he : OffplaneCorrectionExtensions.FiberAgreement W.carrier phi phi₀) (slope : ℝ)
    (htime : 0 < G.velocityScale * G.radialScale * G.epsilon) {z : SpaceTime}
    (hz : OffplaneCorrectionExtensions.physicalSlow z ∈ window W G) (ht : z.1 < 1) :
    phase G phi slope =ᶠ[𝓝 z] phase G phi₀ slope := by
  filter_upwards [(OffplaneCorrectionExtensions.physicalDomain_open (window_open W G)).mem_nhds hz,
    (isOpen_lt continuous_fst continuous_const).mem_nhds ht] with y hy hyt
  exact phase_agrees W G he slope htime hy hyt

theorem normal_smooth {phi : Point → ℝ}
    (hphi : ContDiffOn ℝ ∞ phi (LocalRankDefect.positiveDomain W.carrier))
    (slope : ℝ) (hr : 0 < G.radialScale) :
    ContDiffOn ℝ ∞ (phaseNormal LinearWaveResidual.coordinateRadius
      (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
      (LinearWaveResidual.spaceDirection 2) (phase G phi slope)) (positiveDomain W G) := by
  have hφ := phase_smooth W G hphi slope hr
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiffOn_along (positiveDomain_open W G) contDiffOn_const hφ
  · exact (contDiffOn_along (positiveDomain_open W G) contDiffOn_const hφ).div
      (PhysicalGraphBounds.coordinateProjection 0).contDiff.contDiffOn (fun _ hz => hz.2.ne')
  · exact contDiffOn_along (positiveDomain_open W G) contDiffOn_const hφ

theorem normal_ne {phi : Point → ℝ}
    (hphi : ContDiffOn ℝ ∞ phi (LocalRankDefect.positiveDomain W.carrier))
    {slope : ℝ} (hslope : slope ≠ 0) (hr : 0 < G.radialScale)
    {z : SpaceTime} (hz : z ∈ positiveDomain W G) :
    phaseNormal LinearWaveResidual.coordinateRadius
      (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
      (LinearWaveResidual.spaceDirection 2) (phase G phi slope) z ≠ 0 := by
  have hd := ((phase_smooth W G hphi slope hr).contDiffAt
    ((positiveDomain_open W G).mem_nhds hz)).differentiableAt (by simp)
  have hθ := (phase_affine G phi slope).directional_eq hd
  intro hn
  have h1 := congrArg (fun v : Space => v 1) hn
  change fderiv ℝ (phase G phi slope) z (0, coordinateVector 1) / z.2 0 = 0 at h1
  rw [hθ] at h1
  exact (div_ne_zero hslope hz.2.ne') h1

noncomputable def potential {f : Point → ComplexVector} (e : FieldContinuation W f)
    (phi : Point → ℝ) (slope K scale : ℝ) : SpaceTime → ComplexVector :=
  PhysicalCurlCovariance.referencePotential K (phase G phi slope) (amplitude W G e scale)

theorem potential_smooth {f : Point → ComplexVector} (e : FieldContinuation W f)
    {phi : Point → ℝ} (hphi : ContDiffOn ℝ ∞ phi (LocalRankDefect.positiveDomain W.carrier))
    {slope : ℝ} (hslope : slope ≠ 0) (K scale : ℝ) (hr : 0 < G.radialScale) :
    ContDiffOn ℝ ∞ (potential W G e phi slope K scale) (positiveDomain W G) := by
  have hc := CurlClassBounds.normalCoefficient_contDiffOn (normal_smooth W G hphi slope hr)
    (amplitude_smooth W G e scale hr) (fun _ hz => normal_ne W G hphi hslope hr hz)
  apply contDiffOn_pi.mpr
  intro i
  exact contDiffOn_mode K (phase_smooth W G hphi slope hr)
    ((contDiffOn_pi.mp hc i).const_smul (CurlClassBounds.inverseCarrier K))

theorem potential_zero {f : Point → ComplexVector} (e : FieldContinuation W f)
    (phi : Point → ℝ) (slope K scale : ℝ) {delta : ℝ}
    (hdelta : G.radialScale * delta < W.lower) (hr : 0 ≤ G.radialScale)
    (z : SpaceTime) (hz : z.2 0 ≤ delta) : potential W G e phi slope K scale z = 0 := by
  ext i
  simp [potential, PhysicalCurlCovariance.referencePotential, CurlClassBounds.vectorPotential,
    CurlClassBounds.coefficient, amplitude_zero W G e scale hdelta hr z hz,
    vectorMode, HarmonicCalculus.mode]

theorem potential_periodic {f : Point → ComplexVector} (e : FieldContinuation W f)
    (phi : Point → ℝ) (slope K scale : ℝ) (m : ℤ) (hm : K * slope = (m : ℝ))
    (t r z : ℝ) : Periodic (fun theta => potential W G e phi slope K scale
      (t, AxisymmetricResidual.pack r theta z)) (2 * Real.pi) := by
  intro theta
  have hR : CopyAngularInvariance.Invariant ((0 : ℝ), coordinateVector 1) LinearWaveResidual.coordinateRadius := by
    intro x s
    simp [LinearWaveResidual.coordinateRadius, coordinateVector]
  have he := PhysicalCurlCovariance.vectorPotential_fullTurn
    (Vr := LinearWaveResidual.spaceDirection 0) (Vθ := LinearWaveResidual.spaceDirection 1)
    (Vz := LinearWaveResidual.spaceDirection 2) m hR
    (CopyAngularInvariance.Invariant.const _) (CopyAngularInvariance.Invariant.const _)
    (CopyAngularInvariance.Invariant.const _) (phase_affine G phi slope)
    (amplitude_invariant W G e scale) hm (t, AxisymmetricResidual.pack r theta z)
  simpa only [potential, PhysicalCurlCovariance.referencePotential,
    PhysicalParticularWave.angle_translate_pack] using he

theorem potential_agrees {f : Point → ComplexVector} (e : FieldContinuation W f)
    {phi phi₀ : Point → ℝ} (hphi : OffplaneCorrectionExtensions.FiberAgreement W.carrier phi phi₀)
    (slope K scale : ℝ) (htime : 0 < G.velocityScale * G.radialScale * G.epsilon)
    {z : SpaceTime} (hz : OffplaneCorrectionExtensions.physicalSlow z ∈ window W G) (ht : z.1 < 1) :
    potential W G e phi slope K scale z =
      PhysicalCurlCovariance.referencePotential K (phase G phi₀ slope)
        (fun y => scale • f (point G y)) z :=
  PhysicalCurlCovariance.vectorPotential_congr K _ _ _ _
    (phase_germ W G hphi slope htime hz ht) (amplitude_agrees W G e scale htime hz ht)

noncomputable def potentialExtension {f : Point → ComplexVector} (e : FieldContinuation W f)
    {phi phi₀ : Point → ℝ} (hphi : ContDiffOn ℝ ∞ phi (LocalRankDefect.positiveDomain W.carrier))
    (he : OffplaneCorrectionExtensions.FiberAgreement W.carrier phi phi₀)
    {slope : ℝ} (hslope : slope ≠ 0) (K scale : ℝ) (m : ℤ) (hm : K * slope = (m : ℝ))
    (hr : 0 < G.radialScale) (htime : 0 < G.velocityScale * G.radialScale * G.epsilon)
    {delta : ℝ} (hd : 0 < delta) (hdelta : G.radialScale * delta < W.lower)
    {x : Space} (hx : slow G (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension
      (globalCartesianPotential delta (PhysicalCurlCovariance.referencePotential K
        (phase G phi₀ slope) (fun y => scale • f (point G y)))) x where
  value := globalCartesianPotential delta (potential W G e phi slope K scale)
  domain := OffplaneCorrectionExtensions.physicalDomain (window W G)
  isOpen := OffplaneCorrectionExtensions.physicalDomain_open (window_open W G)
  mem := by simpa only [OffplaneCorrectionExtensions.physicalDomain, mem_preimage,
    OffplaneCorrectionExtensions.physicalSlow, sub_self, window] using hx
  smooth := cartesian_smooth_on_slow hd (window_open W G)
    (potential_smooth W G e hphi hslope K scale hr)
    (potential_periodic W G e phi slope K scale m hm)
    (potential_zero W G e phi slope K scale hdelta hr.le)
  agrees := by
    intro z hz
    apply cartesian_eq_of_slow_fiber
    intro y hy
    have hyt : y.1 < 1 := by
      have heq := congrArg Prod.fst hy
      change 1 - y.1 = 1 - z.1 at heq
      have hzt : z.1 < 1 := hz.2.1
      linarith
    exact potential_agrees W G e he slope K scale htime (hy ▸ hz.1) hyt

noncomputable def pressure {f : Point → ℂ} (e : FieldContinuation W f)
    (phi : Point → ℝ) (slope K scale : ℝ) : SpaceTime → ComplexVector :=
  PhysicalParticularWave.pressureVector
    (HarmonicCalculus.mode K (phase G phi slope) (amplitude W G e scale))

theorem pressure_smooth {f : Point → ℂ} (e : FieldContinuation W f)
    {phi : Point → ℝ} (hphi : ContDiffOn ℝ ∞ phi (LocalRankDefect.positiveDomain W.carrier))
    (slope K scale : ℝ) (hr : 0 < G.radialScale) :
    ContDiffOn ℝ ∞ (pressure W G e phi slope K scale) (positiveDomain W G) := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_mode K (phase_smooth W G hphi slope hr) (amplitude_smooth W G e scale hr)

theorem pressure_zero {f : Point → ℂ} (e : FieldContinuation W f)
    (phi : Point → ℝ) (slope K scale : ℝ) {delta : ℝ}
    (hdelta : G.radialScale * delta < W.lower) (hr : 0 ≤ G.radialScale)
    (z : SpaceTime) (hz : z.2 0 ≤ delta) : pressure W G e phi slope K scale z = 0 := by
  ext i
  fin_cases i <;> simp [pressure, PhysicalParticularWave.pressureVector, HarmonicCalculus.mode,
    amplitude_zero W G e scale hdelta hr z hz]

theorem pressure_periodic {f : Point → ℂ} (e : FieldContinuation W f)
    (phi : Point → ℝ) (slope K scale : ℝ) (m : ℤ) (hm : K * slope = (m : ℝ))
    (t r z : ℝ) : Periodic (fun theta => pressure W G e phi slope K scale
      (t, AxisymmetricResidual.pack r theta z)) (2 * Real.pi) := by
  intro theta
  have he := PhysicalParticularWave.mode_fullTurn m (phase_affine G phi slope)
    (amplitude_invariant W G e scale) hm (t, AxisymmetricResidual.pack r theta z)
  rw [PhysicalParticularWave.angle_translate_pack] at he
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact he

theorem pressure_agrees {f : Point → ℂ} (e : FieldContinuation W f)
    {phi phi₀ : Point → ℝ} (hphi : OffplaneCorrectionExtensions.FiberAgreement W.carrier phi phi₀)
    (slope K scale : ℝ) (htime : 0 < G.velocityScale * G.radialScale * G.epsilon)
    {z : SpaceTime} (hz : OffplaneCorrectionExtensions.physicalSlow z ∈ window W G) (ht : z.1 < 1) :
    pressure W G e phi slope K scale z = PhysicalParticularWave.pressureVector
      (HarmonicCalculus.mode K (phase G phi₀ slope) (fun y => scale • f (point G y))) z := by
  ext i
  fin_cases i <;> simp only [pressure, PhysicalParticularWave.pressureVector, HarmonicCalculus.mode,
    amplitude_agrees W G e scale htime hz ht, carrier, phase_agrees W G hphi slope htime hz ht]

noncomputable def pressureExtension {f : Point → ℂ} (e : FieldContinuation W f)
    {phi phi₀ : Point → ℝ} (hphi : ContDiffOn ℝ ∞ phi (LocalRankDefect.positiveDomain W.carrier))
    (he : OffplaneCorrectionExtensions.FiberAgreement W.carrier phi phi₀)
    (slope K scale : ℝ) (m : ℤ) (hm : K * slope = (m : ℝ))
    (hr : 0 < G.radialScale) (htime : 0 < G.velocityScale * G.radialScale * G.epsilon)
    {delta : ℝ} (hd : 0 < delta) (hdelta : G.radialScale * delta < W.lower)
    {x : Space} (hx : slow G (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension (fun z => globalCartesianPotential delta
      (PhysicalParticularWave.pressureVector (HarmonicCalculus.mode K
        (phase G phi₀ slope) (fun y => scale • f (point G y)))) z 2) x where
  value z := globalCartesianPotential delta (pressure W G e phi slope K scale) z 2
  domain := OffplaneCorrectionExtensions.physicalDomain (window W G)
  isOpen := OffplaneCorrectionExtensions.physicalDomain_open (window_open W G)
  mem := by simpa only [OffplaneCorrectionExtensions.physicalDomain, mem_preimage,
    OffplaneCorrectionExtensions.physicalSlow, sub_self, window] using hx
  smooth := (contDiffOn_piLp 2).mp
    (cartesian_smooth_on_slow hd (window_open W G)
      (pressure_smooth W G e hphi slope K scale hr)
      (pressure_periodic W G e phi slope K scale m hm)
      (pressure_zero W G e phi slope K scale hdelta hr.le)) 2
  agrees := by
    intro z hz
    apply congrArg (fun v : Space => v 2)
    apply cartesian_eq_of_slow_fiber
    intro y hy
    have hyt : y.1 < 1 := by
      have heq := congrArg Prod.fst hy
      change 1 - y.1 = 1 - z.1 at heq
      have hzt : z.1 < 1 := hz.2.1
      linarith
    exact pressure_agrees W G e he slope K scale htime (hy ▸ hz.1) hyt

end PhysicalNative

end LocalPhysical

section ActualParticular

open ProblemStatement

/-- Primitive continuations for the same assembled particular wave.  The
source is the actual residual coefficient of `D.state`, not a replacement
forcing.  No velocity, pressure, or potential continuation is a field. -/
structure ParticularPrimitives {coord a b : ℝ} (W : OffplaneCorrectionExtensions.Window coord a b)
    (D : ParticularWaveAssembly.AssemblyData Parameter) (j : ℤ) where
  tangent : TangentGeometry W (D.reference.tangent j)
  source : FieldContinuation W (fun x => ParticularWaveAssembly.residualSource D.context D.state
    D.carrierBlock D.gaussianInput D.aliasInput j D.reference.band (toChart x))
  phase : Point → ℝ
  phase_smooth : ContDiffOn ℝ ∞ phase (LocalRankDefect.positiveDomain W.carrier)
  phase_agrees : OffplaneCorrectionExtensions.FiberAgreement W.carrier phase
    (fun x => D.carrierBlock.phase D.reference.band (toChart x))
  cutoff_smooth : ContDiff ℝ ∞ D.reference.cutoff
  cutoff_inside : tsupport D.reference.cutoff ⊆ univ ×ˢ Ioo 0 D.reference.length

namespace ParticularPrimitives

variable {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
  {D : ParticularWaveAssembly.AssemblyData Parameter} {j : ℤ} (p : ParticularPrimitives W D j)

noncomputable def velocity : FieldContinuation W (fun x =>
    ParticularWaveAssembly.referenceVelocity D.reference D.context D.state D.carrierBlock
      D.gaussianInput D.aliasInput j (toChart x)) :=
  p.tangent.complexVelocityContinuation p.source D.reference.geometry D.reference.length_pos.le
    p.cutoff_smooth D.reference.cutoff_compact p.cutoff_inside

noncomputable def pressure : FieldContinuation W (fun x =>
    ParticularWaveAssembly.referencePressure D.reference D.context D.state D.carrierBlock
      D.gaussianInput D.aliasInput j (toChart x)) :=
  p.tangent.complexPressureContinuation p.source (PhysicalParticularWave.referenceFrequency D j)
    D.reference.geometry D.reference.length_pos.le p.cutoff_smooth D.reference.cutoff_compact p.cutoff_inside

theorem carrier_integer (hk : D.carrierBlock.frequency D.reference.band ≠ 0) :
    PhysicalParticularWave.referenceFrequency D j *
      ((D.carrierBlock.angularFrequency D.reference.band : ℝ) / D.carrierBlock.frequency D.reference.band) =
      ((j * D.carrierBlock.angularFrequency D.reference.band : ℤ) : ℝ) := by
  unfold PhysicalParticularWave.referenceFrequency
  push_cast
  field_simp [hk]

noncomputable def potentialExtension (h Q : ℝ) (hQ : 0 < Q) (index : ℕ)
    (hk : D.carrierBlock.frequency D.reference.band ≠ 0)
    (hm : D.carrierBlock.angularFrequency D.reference.band ≠ 0)
    {delta : ℝ} (hd : 0 < delta) (hdelta : Q ^ (-(1 / 2 : ℝ)) * delta < W.lower)
    {x : Space} (hx : PhysicalNative.slow (PhysicalResidualBridge.commonGraph Q h index) (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension (PhysicalParticularWave.physicalPotential D h Q index delta j) x := by
  have hr : 0 < (PhysicalResidualBridge.commonGraph Q h index).radialScale := Real.rpow_pos_of_pos hQ _
  have ht : 0 < (PhysicalResidualBridge.commonGraph Q h index).velocityScale *
      (PhysicalResidualBridge.commonGraph Q h index).radialScale *
      (PhysicalResidualBridge.commonGraph Q h index).epsilon := by
    rw [PhysicalResidualBridge.commonGraph_slowTimeScale hQ]
    exact Real.rpow_pos_of_pos hQ _
  have hs : (D.carrierBlock.angularFrequency D.reference.band : ℝ) /
      D.carrierBlock.frequency D.reference.band ≠ 0 := div_ne_zero (by exact_mod_cast hm) hk
  exact PhysicalNative.potentialExtension W (PhysicalResidualBridge.commonGraph Q h index)
    p.velocity p.phase_smooth p.phase_agrees hs (PhysicalParticularWave.referenceFrequency D j)
    (Q ^ (-CoordinateAlgebra.A h)) (j * D.carrierBlock.angularFrequency D.reference.band)
    (carrier_integer hk) hr ht hd hdelta hx

noncomputable def pressureExtension (h Q : ℝ) (hQ : 0 < Q) (index : ℕ)
    (hk : D.carrierBlock.frequency D.reference.band ≠ 0)
    {delta : ℝ} (hd : 0 < delta) (hdelta : Q ^ (-(1 / 2 : ℝ)) * delta < W.lower)
    {x : Space} (hx : PhysicalNative.slow (PhysicalResidualBridge.commonGraph Q h index) (0, x 2) ∈ W.carrier) :
    JointResidualLimits.OneSidedExtension (PhysicalParticularWave.physicalPressure D h Q index delta j) x := by
  have hr : 0 < (PhysicalResidualBridge.commonGraph Q h index).radialScale := Real.rpow_pos_of_pos hQ _
  have ht : 0 < (PhysicalResidualBridge.commonGraph Q h index).velocityScale *
      (PhysicalResidualBridge.commonGraph Q h index).radialScale *
      (PhysicalResidualBridge.commonGraph Q h index).epsilon := by
    rw [PhysicalResidualBridge.commonGraph_slowTimeScale hQ]
    exact Real.rpow_pos_of_pos hQ _
  exact PhysicalNative.pressureExtension W (PhysicalResidualBridge.commonGraph Q h index)
    p.pressure p.phase_smooth p.phase_agrees
    ((D.carrierBlock.angularFrequency D.reference.band : ℝ) / D.carrierBlock.frequency D.reference.band)
    (PhysicalParticularWave.referenceFrequency D j) (Q ^ (-(2 * CoordinateAlgebra.A h)))
    (j * D.carrierBlock.angularFrequency D.reference.band) (carrier_integer hk) hr ht hd hdelta hx

end ParticularPrimitives

end ActualParticular

section PhysicalSupport

open ProblemStatement PhysicalCurlCovariance

theorem cartesian_radialSupport {delta : ℝ} (hd : 0 < delta)
    {B : SpaceTime → ComplexVector} {S : Slow → Set ℝ}
    (hB : ∀ z, B z ≠ 0 → z.2 0 ∈ S (OffplaneCorrectionExtensions.physicalSlow z))
    (x : SpaceTime) (hx : globalCartesianPotential delta B x ≠ 0) :
    PolarCharts.radius (PhysicalGraphBounds.radialProjection x) ∈
      S (OffplaneCorrectionExtensions.physicalSlow x) := by
  classical
  unfold globalCartesianPotential at hx
  split_ifs at hx with he
  · have hb : B (polarCoordinates delta (Classical.choose he) x) ≠ 0 := by
      intro hz
      apply hx
      unfold cartesianPotential
      rw [hz]
      have hzero : realVector (0 : ComplexVector) = 0 := by ext i; simp
      rw [hzero, map_zero]
    have hs := hB _ hb
    rw [polarCoordinates_radius hd _ (Classical.choose_spec he), polarCoordinates_slow] at hs
    exact hs
  · exact (hx rfl).elim

namespace PhysicalNative

variable {coord a b : ℝ} (W : OffplaneCorrectionExtensions.Window coord a b)
  (G : PhysicalResidualBridge.ScaledGraph)

noncomputable def radialFiber (_W : OffplaneCorrectionExtensions.Window coord a b)
    (G : PhysicalResidualBridge.ScaledGraph) (s : Slow) : Set ℝ :=
  {r | G.radialScale * r ∈ Icc
    (OffplaneCorrectionExtensions.stableLength coord (slow G s) * a)
    (OffplaneCorrectionExtensions.stableLength coord (slow G s) * b)}

theorem amplitude_radialSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (e : FieldContinuation W f) (scale : ℝ) (z : SpaceTime)
    (hz : amplitude W G e scale z ≠ 0) :
    z.2 0 ∈ radialFiber W G (OffplaneCorrectionExtensions.physicalSlow z) := by
  classical
  by_cases hw : OffplaneCorrectionExtensions.physicalSlow z ∈ window W G
  · have he : e.value (point G z) ≠ 0 := by
      intro h
      exact hz (by simp only [amplitude, ite_eq_left hw, h, smul_zero])
    exact e.supported (point G z) hw he
  · exact (hz (by simp only [amplitude, ite_eq_right hw])).elim

theorem potential_radialSupport {f : Point → ComplexVector} (e : FieldContinuation W f)
    (phi : Point → ℝ) (slope K scale : ℝ) (z : SpaceTime)
    (hz : potential W G e phi slope K scale z ≠ 0) :
    z.2 0 ∈ radialFiber W G (OffplaneCorrectionExtensions.physicalSlow z) := by
  apply amplitude_radialSupport W G e scale z
  intro ha
  apply hz
  ext i
  simp [potential, PhysicalCurlCovariance.referencePotential, CurlClassBounds.vectorPotential,
    CurlClassBounds.coefficient, vectorMode, HarmonicCalculus.mode, ha]

theorem pressure_radialSupport {f : Point → ℂ} (e : FieldContinuation W f)
    (phi : Point → ℝ) (slope K scale : ℝ) (z : SpaceTime)
    (hz : pressure W G e phi slope K scale z ≠ 0) :
    z.2 0 ∈ radialFiber W G (OffplaneCorrectionExtensions.physicalSlow z) := by
  apply amplitude_radialSupport W G e scale z
  intro ha
  apply hz
  ext i
  fin_cases i <;> simp [pressure, PhysicalParticularWave.pressureVector, HarmonicCalculus.mode, ha]

theorem potential_cartesian_radialSupport {f : Point → ComplexVector} (e : FieldContinuation W f)
    (phi : Point → ℝ) (slope K scale : ℝ) {delta : ℝ} (hd : 0 < delta)
    (z : SpaceTime) (hz : globalCartesianPotential delta (potential W G e phi slope K scale) z ≠ 0) :
    PolarCharts.radius (PhysicalGraphBounds.radialProjection z) ∈
      radialFiber W G (OffplaneCorrectionExtensions.physicalSlow z) :=
  cartesian_radialSupport hd (potential_radialSupport W G e phi slope K scale) z hz

theorem pressure_cartesian_radialSupport {f : Point → ℂ} (e : FieldContinuation W f)
    (phi : Point → ℝ) (slope K scale : ℝ) {delta : ℝ} (hd : 0 < delta)
    (z : SpaceTime) (hz : globalCartesianPotential delta (pressure W G e phi slope K scale) z 2 ≠ 0) :
    PolarCharts.radius (PhysicalGraphBounds.radialProjection z) ∈
      radialFiber W G (OffplaneCorrectionExtensions.physicalSlow z) := by
  apply cartesian_radialSupport hd (pressure_radialSupport W G e phi slope K scale) z
  intro h
  exact hz (by rw [h]; rfl)

end PhysicalNative

end PhysicalSupport

end NavierStokes.WaveStageContinuation
