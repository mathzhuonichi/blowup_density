import NSFormalization.Section4.A01.JointRepresentative
import NSFormalization.Section4.A01.ConstructorPressure
import NavierStokes.ResidualRegularity

/-!
# Interior time differentiation of the canonical joint representative

All ambient time derivative assertions are restricted to `Ioo 0 S`.
Bounded evaluation commutes with the datum derivative; equality of continuous
Sobolev representatives transfers this calculation to the fixed joint field.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01
open scoped Topology ContDiff

/-- Canonical bounded evaluation preserves subtraction at every available order. -/
theorem vectorRepresentative_sub (s : ℝ) (hs : 2 ≤ s)
    (A B : RealVectorSobolev s) (x : Space) :
    vectorRepresentative s hs (A - B) x =
      vectorRepresentative s hs A x - vectorRepresentative s hs B x := by
  apply PiLp.ext
  intro i
  change (angularBoundedRepresentative s hs
    (((A i : RealSobolevHilbert s) : FourierData) -
      ((B i : RealSobolevHilbert s) : FourierData)) x).re = _
  simp [map_sub, vectorRepresentative, PiLp.sub_apply]

/-- At a fixed spatial point, bounded linear evaluation commutes with time
 differentiation of an arbitrary vector datum path. -/
theorem vectorRepresentative_hasDerivAt {s : ℝ} (hs : 2 ≤ s)
    {G : ℝ → RealVectorSobolev s} {D : RealVectorSobolev s} {t : ℝ}
    (hG : HasDerivAt G D t) (x : Space) :
    HasDerivAt (fun r => vectorRepresentative s hs (G r) x)
      (vectorRepresentative s hs D x) t := by
  let component (i : Fin 3) : RealVectorSobolev s →L[ℝ] ℝ :=
    Complex.reCLM.comp ((angularEvaluation s hs x).comp
      ((RealSobolevHilbert s).subtypeL.comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => RealSobolevHilbert s) i)))
  have hd : HasDerivAt (fun r i => component i (G r)) (fun i => component i D) t :=
    hasDerivAt_pi.mpr (fun i => (component i).hasFDerivAt.comp_hasDerivAt t hG)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t hd

/-- The ambient time derivative of the joint representative is the bounded
representative of the derivative datum. The sole time locality step uses
`Icc 0 S ∈ 𝓝 t`, hence requires strictly interior time. -/
theorem jointRepresentative_temporalDerivative {S s : ℝ} (hs : 2 ≤ s)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (G : ℝ → RealVectorSobolev s)
    (hG : ∀ t : Icc (0 : ℝ) S, IsSobolevDatum s (⇑(U t)) (G t.1))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) S) (D : RealVectorSobolev s)
    (hderiv : HasDerivWithinAt G D (Icc (0 : ℝ) S) t) (x : Space) :
    temporalDerivative (jointRepresentative U hpaths) t x =
      vectorRepresentative s hs D x := by
  have hI : Icc (0 : ℝ) S ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hd := vectorRepresentative_hasDerivAt hs (hderiv.hasDerivAt hI) x
  have heq : (fun r => jointRepresentative U hpaths (r, x)) =ᶠ[𝓝 t]
      (fun r => vectorRepresentative s hs (G r) x) := by
    filter_upwards [hI] with r hr
    exact congrFun (vectorRepresentative_eq_of_datums (by norm_num) hs
      (U ⟨r, hr⟩) ((Classical.choose_spec (hpaths 0 2)).2 ⟨r, hr⟩)
      (hG ⟨r, hr⟩)) x
  exact (hd.congr_of_eventuallyEq heq).deriv

/-- Equality of Sobolev data determines locally integrable physical fields
almost everywhere. -/
theorem ae_eq_of_isSobolevDatum_locInt {s : ℝ} {v w : Space → Space}
    (hv : A03.LocIntField v) (hw : A03.LocIntField w)
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s v A)
    (hB : IsSobolevDatum s w A) : v =ᵐ[volume] w := by
  have hi (i : Fin 3) : ∀ᵐ x ∂volume, (v x i : ℂ) = (w x i : ℂ) := by
    apply A03.ae_eq_of_schwartz_pairing (hv i) (hw i)
    intro ψ
    exact (hA i ψ).symm.trans (hB i ψ)
  filter_upwards [ae_all_iff.mpr hi] with x hx
  apply PiLp.ext
  intro i
  exact_mod_cast hx i

/-- `L²` is the standard convenient source of the local-integrability
hypotheses in `ae_eq_of_isSobolevDatum_locInt`. -/
theorem ae_eq_of_isSobolevDatum {s : ℝ} {v w : Space → Space}
    (hv : MemLp v 2 volume) (hw : MemLp w 2 volume)
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s v A)
    (hB : IsSobolevDatum s w A) : v =ᵐ[volume] w :=
  ae_eq_of_isSobolevDatum_locInt (A03.locIntField_of_memLp hv)
    (A03.locIntField_of_memLp hw) hA hB

open NSFormalization.Source.ForcedCylinderLocal
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerQuadraticSource EulerVolterraConvolution

/-- Direct consumer of lane 169 at any `2 ≤ m ≤ q-1`: the time derivative
of the fixed joint representative realizes the ordinary projected residual.
No identification of the cylinder projector with the Fourier projector is
assumed or hidden in this theorem. -/
theorem jointRepresentative_temporalDerivative_of_cylinder {q m : ℕ}
    (hq : 6 ≤ q) (hm : m + 2 ≤ q + 1) (hm2 : 2 ≤ (m : ℝ))
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq f) u₀ u t)
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (A R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)))
    (hA : ∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t))
    (hR : ∀ t, IsSobolevDatum (m : ℝ)
      (⇑(ordinaryResidualPath hq hm ν f u t)) (R t))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) S) (x : Space) :
    temporalDerivative (jointRepresentative U hpaths) t x =
      vectorRepresentative (m : ℝ) hm2 (R ⟨t, ht.1.le, ht.2.le⟩) x := by
  apply jointRepresentative_temporalDerivative hm2 U hpaths
    (extendPath S hS.le A) _ ht _
    (datumPath_hasDerivAt hq hm hν hS u₀ f u U hU hduh A R hA hR t ht).hasDerivWithinAt x
  intro r
  simpa only [extendPath, projIcc_of_mem hS.le r.property] using hA r

/-- Interior regularity uses the open slab before taking any ambient derivative. -/
theorem pressureGradientOfVelocity_contDiffOn_interior {S : ℝ} (ν : ℝ)
    (f u : VelocityField)
    (hf : ContDiffOn ℝ ∞ f (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (pressureGradientOfVelocity ν f u)
      (Ioo (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  have hsub : Ioo (0 : ℝ) S ×ˢ (univ : Set Space) ⊆
      Ico (0 : ℝ) S ×ˢ (univ : Set Space) :=
    prod_mono_left Ioo_subset_Ico_self
  have huo := hu.mono hsub
  have hopen := (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) S)).prod (isOpen_univ : IsOpen (univ : Set Space))
  exact (((hf.mono hsub).sub
    (NavierStokes.ResidualRegularity.contDiffOn_advection hopen huo)).add
    ((NavierStokes.ResidualRegularity.contDiffOn_spatialLaplacian hopen huo).const_smul ν)).sub
    (NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative hopen huo)

/-- Order-zero assembly: an a.e. realization of the complement agrees with
`residual - ∂ₜu` everywhere at interior times. The input `htime` is the
projected momentum equation on the physical datum carrier, stated explicitly. -/
theorem interior_momentum_identity_of_datums {S : ℝ} (ν : ℝ)
    (f u G : VelocityField)
    (hf : ContDiffOn ℝ ∞ f (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hG : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (A : Icc (0 : ℝ) S → RealVectorSobolev 0)
    (hcomp : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S), IsSobolevDatum 0
      (fun x => G (t, x))
      (Leray.lerayComplement 0 (A ⟨t, ht.1.le, ht.2.le⟩)))
    (hres : ∀ t : Icc (0 : ℝ) S,
      IsSobolevDatum 0 (fun x => momentumResidualOfVelocity ν f u (t.1, x)) (A t))
    (htime : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      IsSobolevDatum 0 (fun x => temporalDerivative u t x)
        (A ⟨t, ht.1.le, ht.2.le⟩ -
          Leray.lerayComplement 0 (A ⟨t, ht.1.le, ht.2.le⟩))) :
    ∀ t ∈ Ioo (0 : ℝ) S, ∀ x, G (t, x) = pressureGradientOfVelocity ν f u (t, x) := by
  intro t ht
  let τ : Icc (0 : ℝ) S := ⟨t, ht.1.le, ht.2.le⟩
  have hGd := D01.contDiff_slice hG ⟨ht.1.le, ht.2⟩
  have hGc := hGd.continuous
  have hpg : ContDiff ℝ ∞ (fun x => pressureGradientOfVelocity ν f u (t, x)) := by
    rw [← contDiffOn_univ]
    exact (pressureGradientOfVelocity_contDiffOn_interior ν f u hf hu).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨ht, mem_univ _⟩)
  have htc : ContDiff ℝ ∞ (fun x => temporalDerivative u t x) := by
    rw [← contDiffOn_univ]
    exact (NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative
      (isOpen_Ioo.prod isOpen_univ) (hu.mono (prod_mono_left Ioo_subset_Ico_self))).comp
        (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨ht, mem_univ _⟩)
  have hrc : ContDiff ℝ ∞ (fun x => momentumResidualOfVelocity ν f u (t, x)) := by
    convert hpg.add htc using 1
    funext x
    simp [pressureGradientOfVelocity]
  have hrL : MemLp (fun x => momentumResidualOfVelocity ν f u (t, x)) 2 volume :=
    memLp_piLp_iff.mpr (fun i => Complex.reCLM.comp_memLp'
      (memLp_component_of_isSobolevDatum (le_refl 0) hrc.continuous (hres τ) i))
  have htL : MemLp (fun x => temporalDerivative u t x) 2 volume :=
    memLp_piLp_iff.mpr (fun i => Complex.reCLM.comp_memLp'
      (memLp_component_of_isSobolevDatum (le_refl 0) htc.continuous (htime t ht) i))
  have hd := D01.isSobolevDatum_sub
    (schwartzPairable_of_memLp (fun i => memLp_component hrL i))
    (schwartzPairable_of_memLp (fun i => memLp_component htL i)) (hres τ) (htime t ht)
  have ha : A τ - (A τ - Leray.lerayComplement 0 (A τ)) =
      Leray.lerayComplement 0 (A τ) := by abel
  rw [ha] at hd
  have hGL : A03.LocIntField (fun x => G (t, x)) := fun i =>
    Continuous.locallyIntegrable (Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hGc))
  have hae : (fun x => pressureGradientOfVelocity ν f u (t, x)) =ᵐ[volume]
      (fun x => G (t, x)) :=
    ae_eq_of_isSobolevDatum_locInt (A03.locIntField_of_memLp (hrL.sub htL)) hGL
      hd (hcomp t ht)
  have heq := (hpg.continuous.ae_eq_iff_eq volume hGc).mp hae
  exact congrFun heq.symm

/-- Cylinder-to-interior assembly, conditional on the explicit order-zero
bridge `hprojected`.  Despite its short name, `hprojected` bundles two facts:

* identification of the descended cylinder projector with the Fourier Leray
  projector; and
* agreement of the physical force/residual of the joint representative with
  the descended, unprojected cylinder residual.

Lane 197 supplies the projector comparison under its decomposition inputs;
lane 194 supplies the complement path and the a.e. physical-residual bridge;
lane 192 supplies the canonical choices
`fc = sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q`
and `u₀ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff`, with the
initial datum solenoidal.  Lane 169 supplies only the time derivative through
`datumPath_hasDerivAt`; it does not supply either bundled part of
`hprojected`.  The argument remains composite here because lane 197's checked
consumer export has exactly this equality as its conclusion. -/
theorem interior_momentum_identity {q m : ℕ}
    (hq : 6 ≤ q) (hm : m + 2 ≤ q + 1) (hm2 : 2 ≤ (m : ℝ))
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (fc : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (uc : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (uc t))
    (hduh : ∀ t, uc t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq fc) u₀ uc t)
    (hpaths : ∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j H (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (H t.1))
    (B R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)))
    (hB : ∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (B t))
    (hR : ∀ t, IsSobolevDatum (m : ℝ)
      (⇑(ordinaryResidualPath hq hm ν fc uc t)) (R t))
    (f G : VelocityField)
    (hf : ContDiffOn ℝ ∞ f (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hG : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (A : Icc (0 : ℝ) S → RealVectorSobolev 0)
    (w : Icc (0 : ℝ) S → EulerMeanSolenoidal.L2)
    (hw : ∀ t, IsSobolevDatum 0 (⇑(w t)) (Leray.lerayComplement 0 (A t)))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x => G (t.1, x)) =ᵐ[volume] ⇑(w t))
    (hres : ∀ t : Icc (0 : ℝ) S, IsSobolevDatum 0
      (fun x => momentumResidualOfVelocity ν f (jointRepresentative U hpaths) (t.1, x)) (A t))
    (hprojected : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      lowerVectorL (m : ℝ) 0 (Nat.cast_nonneg m) (R ⟨t, ht.1.le, ht.2.le⟩) =
        A ⟨t, ht.1.le, ht.2.le⟩ - Leray.lerayComplement 0 (A ⟨t, ht.1.le, ht.2.le⟩)) :
    ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
      G (t, x) = pressureGradientOfVelocity ν f (jointRepresentative U hpaths) (t, x) := by
  apply interior_momentum_identity_of_datums ν f (jointRepresentative U hpaths) G hf
    ((jointRepresentative_contDiffOn hS U hpaths).mono (prod_mono_left Ico_subset_Icc_self))
    hG A
  · intro t ht
    exact IsSobolevDatum.congr_field (hw ⟨t, ht.1.le, ht.2.le⟩)
      (hslice ⟨t, ht.1.le, ht.2.le⟩).symm
  · exact hres
  intro t ht
  let τ : Icc (0 : ℝ) S := ⟨t, ht.1.le, ht.2.le⟩
  have hd := Leray.isSobolevDatum_lower (Nat.cast_nonneg m) (hR τ)
  rw [hprojected t ht] at hd
  apply IsSobolevDatum.congr_field hd
  have hae := vectorRepresentative_ae hm2
    (Lp.memLp (ordinaryResidualPath hq hm ν fc uc τ)) (hR τ)
  filter_upwards [hae] with x hx
  exact ((jointRepresentative_temporalDerivative_of_cylinder hq hm hm2 hν hS
    u₀ fc uc U hU hduh hpaths B R hB hR ht x).trans hx).symm

/-- Adapter for lane 194's per-time existential residual datum.

`hcomplement` is the body of lane 194's `exists_complement_paths` after its
outer witness `w` is introduced, copied here because that unmerged branch is
not imported.  The adapter chooses `A t` independently at each time using
`Classical.choose`.  The hypotheses `hG` and `hslice` are the corresponding
body of `exists_complement_joint_representative`.  The cylinder force `fc` and
initial datum `u₀` deliberately remain general; the assembly lane specializes
them to lane 192's canonical force path and solenoidal canonical datum.

Unlike the compatibility theorem above, this adapter exposes the two honest
halves separately: `hprojected` identifies the projectors on the selected
descended residual datum, while `hresidualAgreement` identifies lane 194's
`residualSlice` a.e. with the physical residual of the joint representative. -/
theorem interior_momentum_identity_of_complement_paths {q m : ℕ}
    (hq : 6 ≤ q) (hm : m + 2 ≤ q + 1) (hm2 : 2 ≤ (m : ℝ))
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (fc : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (uc : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (uc t))
    (hduh : ∀ t, uc t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq fc) u₀ uc t)
    (hpaths : ∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j H (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (H t.1))
    (B R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)))
    (hB : ∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (B t))
    (hR : ∀ t, IsSobolevDatum (m : ℝ)
      (⇑(ordinaryResidualPath hq hm ν fc uc t)) (R t))
    (f : VelocityField)
    (hf : ContDiffOn ℝ ∞ f (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (residualSlice : Icc (0 : ℝ) S → Space → Space)
    (w : ℝ → (Space → Space))
    (hcomplement :
      (∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j H (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (w t.1) (H t.1)) ∧
      ∀ t : Icc (0 : ℝ) S, ∃ A : RealVectorSobolev 0,
        IsSobolevDatum 0 (residualSlice t) A ∧
        IsSobolevDatum 0 (w t.1) (Leray.lerayComplement 0 A))
    (hresidualAgreement : ∀ t : Icc (0 : ℝ) S, residualSlice t =ᵐ[volume]
      fun x => momentumResidualOfVelocity ν f (jointRepresentative U hpaths) (t.1, x))
    (G : VelocityField)
    (hG : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x => G (t.1, x)) =ᵐ[volume] w t.1)
    (hprojected : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      lowerVectorL (m : ℝ) 0 (Nat.cast_nonneg m) (R ⟨t, ht.1.le, ht.2.le⟩) =
        Classical.choose (hcomplement.2 ⟨t, ht.1.le, ht.2.le⟩) -
          Leray.lerayComplement 0
            (Classical.choose (hcomplement.2 ⟨t, ht.1.le, ht.2.le⟩))) :
    ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
      G (t, x) = pressureGradientOfVelocity ν f (jointRepresentative U hpaths) (t, x) := by
  let A : Icc (0 : ℝ) S → RealVectorSobolev 0 :=
    fun t => Classical.choose (hcomplement.2 t)
  have hselected (t : Icc (0 : ℝ) S) :
      IsSobolevDatum 0 (residualSlice t) (A t) ∧
        IsSobolevDatum 0 (w t.1) (Leray.lerayComplement 0 (A t)) :=
    Classical.choose_spec (hcomplement.2 t)
  apply interior_momentum_identity_of_datums ν f (jointRepresentative U hpaths) G hf
    ((jointRepresentative_contDiffOn hS U hpaths).mono (prod_mono_left Ico_subset_Icc_self))
    hG A
  · intro t ht
    exact IsSobolevDatum.congr_field (hselected ⟨t, ht.1.le, ht.2.le⟩).2
      (hslice ⟨t, ht.1.le, ht.2.le⟩).symm
  · exact fun t => IsSobolevDatum.congr_field (hselected t).1 (hresidualAgreement t)
  · intro t ht
    let τ : Icc (0 : ℝ) S := ⟨t, ht.1.le, ht.2.le⟩
    have hd := Leray.isSobolevDatum_lower (Nat.cast_nonneg m) (hR τ)
    rw [hprojected t ht] at hd
    apply IsSobolevDatum.congr_field hd
    have hae := vectorRepresentative_ae hm2
      (Lp.memLp (ordinaryResidualPath hq hm ν fc uc τ)) (hR τ)
    filter_upwards [hae] with x hx
    exact ((jointRepresentative_temporalDerivative_of_cylinder hq hm hm2 hν hS
      u₀ fc uc U hU hduh hpaths B R hB hR ht x).trans hx).symm

end NSFormalization.Section4.A01
