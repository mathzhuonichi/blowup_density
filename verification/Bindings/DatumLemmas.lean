import Contracts.V1.DatumLemmas
import Contracts.V1.TameProduct
import NSFormalization.Section4.D01.DatumToJets
import NSFormalization.Section4.D01.HomogeneousWitness
import NSFormalization.Section4.D01.ForceClass

/-! The only layer that knows the current implementation's names and paths for the
D01 datum lemmas.

`Contracts.V1.DatumLemmas` is self-contained — its only imports are three other
contracts — so this adapter has two jobs: record by `rfl` that each notion the
four proof modules restate is the notion the specifications use, and assemble the
proved lemmas into the contract.

The four modules restate `Contracts/V1/Data.lean`, `Contracts/V1/GradientL6.lean`
and `Contracts/V1/BoundedRepresentative.lean` declarations verbatim, because
`formalization/` is an upstream Lake package of `verification/` and cannot import
`Contracts.*`.  Each restatement is definitionally the contract one; until now
that was checked only in throwaway scratch files (`research/D01/REVIEW_L2.md` §3,
`REVIEW_DATUM_TO_JETS.md` §2, `REVIEW_HOMOGENEOUS.md`, `REVIEW_FORCECLASS.md` §3,
each of which lists the bridge as the highest-value follow-up).  §1 below commits
them, so CI fails if either side drifts.

Every declaration carries a `datumLemmas_` prefix: `BlowupDensity.Bindings` is a
flat namespace shared by all adapters.
-/

noncomputable section
namespace BlowupDensity.Bindings

open MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. Correspondence: the restated definitions are the contracts' own -/

section Correspondence

variable (s : ℝ) (q : ℝ≥0∞) (m j : ℕ)
  (z w : Contracts.V1.Data.SpatialField) (f g : Contracts.V1.Data.SpaceTimeField)
  (G : ℝ → NSFormalization.Paper3.RealVectorSobolev s)
  (U : Contracts.V1.Data.VectorDistribution)
  (u : 𝓢'(Space, ℂ))

/-- `SmoothDatum.lean:237` is `Data.IsSobolevDatum` (`Data.lean:160`). -/
theorem datumLemmas_isSobolevDatum_eq (A : NSFormalization.Paper3.RealVectorSobolev s) :
    NSFormalization.Section4.D01.IsSobolevDatum s z A
      = Contracts.V1.Data.IsSobolevDatum s z A := rfl

/-- `SmoothDatum.lean:306` is `Data.sobolevENorm` (`Data.lean:189`). -/
theorem datumLemmas_sobolevENorm_eq :
    NSFormalization.Section4.D01.sobolevENorm s z
      = Contracts.V1.Data.sobolevENorm s z := rfl

/-- `DatumToJets.lean:118` is `Contracts.V1.SmoothSquareIntegrableJets`
(`GradientL6.lean:106`), the A05 class.  The jet form of `H^∞` is written out
independently in **four** V1 specifications, because a specification may not
import an implementation module; the three bridges below pin all four spellings
to one another, so none of them can drift. -/
theorem datumLemmas_smoothSquareIntegrableJets_eq :
    NSFormalization.Section4.D01.SmoothSquareIntegrableJets z
      = Contracts.V1.SmoothSquareIntegrableJets z := rfl

/-- The same class again in `BoundedRepresentative.lean:152`, the A03 class of
`A03.bounded_representative`. -/
theorem datumLemmas_boundedRep_smoothSquareIntegrableJets_eq :
    NSFormalization.Section4.D01.SmoothSquareIntegrableJets z
      = Contracts.V1.BoundedRep.SmoothSquareIntegrableJets z := rfl

/-- The fourth copy: `Contracts.V1.TameProduct.SmoothJets` (`TameProduct.lean:207`),
the class `A03.tame_products` states `smoothJets_memHmVector`,
`smoothJets_partialDeriv` and `smoothJets_advectionTame` on.  `D01.datum_lemmas`
claims no Lemma A.1 estimate and feeds `tame_products` nothing, so this bridge
carries no field of `DatumLemmasAPI`; it is here only to complete the anti-drift
net over the four same-body copies (`research/D01/REVIEW_CONTRACT.md` finding 8).

It also records, mechanically, what `TameProduct.lean:203-205` says is open:
"`Section4/D01/SmoothDatum.lean` proves `SmoothJets z → Data.MemHInfty z`; the
converse is open".  The converse is `memHInfty_iff_smoothJets` of this contract,
and with this `rfl` it transfers to `TameProduct.SmoothJets` unchanged.
`Contracts/V1/TameProduct.lean` is a frozen V1 specification, so that sentence
is a note for a hypothetical V2, not an edit. -/
theorem datumLemmas_tameProduct_smoothJets_eq :
    NSFormalization.Section4.D01.SmoothSquareIntegrableJets z
      = Contracts.V1.TameProduct.SmoothJets z := rfl

/-- `DatumToJets.lean:123` is `BoundedRep.SmoothJetsUpTo`. -/
theorem datumLemmas_smoothJetsUpTo_eq :
    NSFormalization.Section4.D01.SmoothJetsUpTo m z
      = Contracts.V1.BoundedRep.SmoothJetsUpTo m z := rfl

/-- `DatumToJets.lean:127` is `BoundedRep.jetSobolevENorm`. -/
theorem datumLemmas_jetSobolevENorm_eq :
    NSFormalization.Section4.D01.jetSobolevENorm m z
      = Contracts.V1.BoundedRep.jetSobolevENorm m z := rfl

/-- `A05/SmoothJets.lean:87`'s coordinate derivative is
`Contracts.V1.partialDeriv` (`GradientL6.lean:83`), i.e. the pinned upstream
`spatialDerivative` on the time-independent lift. -/
theorem datumLemmas_partialDeriv_eq (i : Fin 3) :
    NSFormalization.Section4.A05.dirDeriv i z = Contracts.V1.partialDeriv i z := rfl

/-- `ForceClass.lean:143,147` are `Data.futureTimes` and `Data.forceTimeMeasure`
(`Data.lean:113,118`). -/
theorem datumLemmas_futureTimes_eq :
    NSFormalization.Section4.D01.futureTimes = Contracts.V1.Data.futureTimes := rfl

theorem datumLemmas_forceTimeMeasure_eq :
    NSFormalization.Section4.D01.forceTimeMeasure = Contracts.V1.Data.forceTimeMeasure := rfl

/-- `ForceClass.lean:152,158,169,175` are `Data.IsSobolevPath`, `Data.MemForceR`,
`Data.MemForceCompact` and `Data.AgreesOnFuture`
(`Data.lean:174,544,559,128`). -/
theorem datumLemmas_isSobolevPath_eq :
    NSFormalization.Section4.D01.IsSobolevPath s f G
      = Contracts.V1.Data.IsSobolevPath s f G := rfl

theorem datumLemmas_memForceR_eq :
    NSFormalization.Section4.D01.MemForceR f = Contracts.V1.Data.MemForceR f := rfl

theorem datumLemmas_memForceCompact_eq :
    NSFormalization.Section4.D01.MemForceCompact f
      = Contracts.V1.Data.MemForceCompact f := rfl

theorem datumLemmas_agreesOnFuture_eq :
    NSFormalization.Section4.D01.AgreesOnFuture f g
      = Contracts.V1.Data.AgreesOnFuture f g := rfl

/-- `HomogeneousWitness.lean:232,237,244,248,253,258` are `Data.IsSliceDistribution`,
`Data.IsHomogeneousDatum`, `Data.homogeneousENorm`, `Data.IsHomogeneousVectorDatum`,
`Data.IsHomogeneousSliceDatum` and `Data.homogeneousFourierENorm`
(`Data.lean:298,324,338,358,367,410`). -/
theorem datumLemmas_isSliceDistribution_eq :
    NSFormalization.Section4.D01.Homogeneous.IsSliceDistribution z U
      = Contracts.V1.Data.IsSliceDistribution z U := rfl

theorem datumLemmas_isHomogeneousDatum_eq
    (F : NSFormalization.Source.RealSobolev.FourierData) :
    NSFormalization.Section4.D01.Homogeneous.IsHomogeneousDatum s F u
      = Contracts.V1.Data.IsHomogeneousDatum s F u := rfl

theorem datumLemmas_homogeneousENorm_eq :
    NSFormalization.Section4.D01.Homogeneous.homogeneousENorm s u
      = Contracts.V1.Data.homogeneousENorm s u := rfl

theorem datumLemmas_isHomogeneousVectorDatum_eq
    (A : NSFormalization.Paper3.RealVectorSobolev s) :
    NSFormalization.Section4.D01.Homogeneous.IsHomogeneousVectorDatum s U A
      = Contracts.V1.Data.IsHomogeneousVectorDatum s U A := rfl

theorem datumLemmas_isHomogeneousSliceDatum_eq
    (A : NSFormalization.Paper3.RealVectorSobolev s) :
    NSFormalization.Section4.D01.Homogeneous.IsHomogeneousSliceDatum s z A
      = Contracts.V1.Data.IsHomogeneousSliceDatum s z A := rfl

theorem datumLemmas_homogeneousFourierENorm_eq :
    NSFormalization.Section4.D01.Homogeneous.homogeneousFourierENorm s z
      = Contracts.V1.Data.homogeneousFourierENorm s z := rfl

/-- `HomogeneousWitness.lean:620,624,629` are `Data.bochnerDatumENorm`,
`Data.IsHomogeneousPath` and `Data.forceHomogeneousENorm`
(`Data.lean:205,375,390`). -/
theorem datumLemmas_bochnerDatumENorm_eq :
    NSFormalization.Section4.D01.Homogeneous.bochnerDatumENorm q s G
      = Contracts.V1.Data.bochnerDatumENorm q s G := rfl

theorem datumLemmas_isHomogeneousPath_eq :
    NSFormalization.Section4.D01.Homogeneous.IsHomogeneousPath s f G
      = Contracts.V1.Data.IsHomogeneousPath s f G := rfl

theorem datumLemmas_forceHomogeneousENorm_eq :
    NSFormalization.Section4.D01.Homogeneous.forceHomogeneousENorm q s f
      = Contracts.V1.Data.forceHomogeneousENorm q s f := rfl

end Correspondence

/-! ## 2. The contract -/

/-- Bind the proved D01 datum lemmas to the stable version-one contract. -/
def datumLemmas : Contracts.V1.DatumLemmas.DatumLemmasAPI where
  Cjet := NSFormalization.Section4.D01.jetSobolevConst
  Cjet_pos := NSFormalization.Section4.D01.jetSobolevConst_pos
  smoothJets_exists_datum := fun s _ h =>
    NSFormalization.Section4.D01.exists_isSobolevDatum_of_contDiff_memLp h.1 h.2 s
  smoothJets_sobolevENorm_ne_top := fun s _ h =>
    NSFormalization.Section4.D01.sobolevENorm_ne_top_of_contDiff_memLp h.1 h.2 s
  smoothJets_exists_datum_fderiv := fun s _ v h =>
    NSFormalization.Section4.D01.exists_isSobolevDatum_fderiv h.1 h.2 v s
  memHInfty_iff_smoothJets := fun _ =>
    NSFormalization.Section4.D01.memHInfty_iff_smoothSquareIntegrableJets
  memLp_of_isSobolevDatum := fun _ _ _ hz hA =>
    NSFormalization.Section4.D01.memLp_of_isSobolevDatum hz hA
  jetSobolevENorm_le_sobolevENorm := fun m _ hz =>
    NSFormalization.Section4.D01.jetSobolevENorm_le_sobolevENorm m hz
  memHInfty_partialDeriv := fun _ j h =>
    NSFormalization.Section4.D01.memHInfty_dirDeriv h.1 h.2 j
  initialClass_smoothJets := fun _ ha =>
    (NSFormalization.Section4.D01.memHInfty_jetClasses ha.1.1 ha.1.2).1
  solution_slice_smoothJets := fun _ _ _ _ u _ ht =>
    NSFormalization.Section4.D01.smoothSquareIntegrableJets_slice u.velocity_smooth
      (fun m => (u.sobolev m).imp fun _ h => h.2) ht
  solution_slice_pressureGradient_contDiff := fun _ _ _ _ u _ ht =>
    NSFormalization.Section4.D01.contDiff_pressureGradient_slice u.pressure_smooth ht
  isSobolevDatum_unique := fun _ _ _ _ hA hB =>
    NSFormalization.Section4.D01.isSobolevDatum_unique hA hB
  isSobolevDatum_add := fun _ _ _ _ _ hz hw hA hB =>
    NSFormalization.Section4.D01.isSobolevDatum_add hz hw hA hB
  isSobolevPath_add := fun _ _ _ _ _ hf hg hG hH =>
    NSFormalization.Section4.D01.isSobolevPath_add hf hg hG hH
  memForceR_slice_integrable := fun _ hf _ ht =>
    NSFormalization.Section4.D01.schwartzPairable_slice_of_memForceR hf ht
  memForceCompact_memForceR := fun _ h =>
    NSFormalization.Section4.D01.memForceR_of_memForceCompact h
  memForceR_add := fun _ _ hf hg => NSFormalization.Section4.D01.memForceR_add hf hg
  memForceR_add_compact := fun _ _ hg hh =>
    NSFormalization.Section4.D01.memForceR_add_compact hg hh
  memForceCompact_add := fun _ _ hf hg =>
    NSFormalization.Section4.D01.memForceCompact_add hf hg
  memForceCompact_of_smooth_support := fun _ hs hc hp =>
    NSFormalization.Section4.D01.memForceCompact_of_smooth_support hs hc hp
  memForceR_of_agreesOnFuture := fun _ _ h =>
    NSFormalization.Section4.D01.memForceR_of_agreesOnFuture h
  memForceR_of_compact_difference := fun _ _ hg hd =>
    NSFormalization.Section4.D01.memForceR_of_compact_difference hg hd
  memForceR_of_force_formula := fun _ _ _ _ hg hH hF hform =>
    NSFormalization.Section4.D01.memForceR_of_force_formula hg hH hF hform
  schwartz_exists_homogeneousDatum := fun _ hs z ψ hz =>
    NSFormalization.Section4.D01.Homogeneous.exists_isHomogeneousSliceDatum hs z ψ hz
  compact_exists_homogeneousDatum := fun _ hs _ hzs hzc =>
    NSFormalization.Section4.D01.Homogeneous.isHomogeneousSliceDatum_compact hs hzs hzc
  isHomogeneousSliceDatum_unique := fun _ _ _ _ hA hB =>
    NSFormalization.Section4.D01.Homogeneous.isHomogeneousSliceDatum_unique hA hB
  homogeneousENorm_schwartz_ne_top := fun _ hs φ =>
    NSFormalization.Section4.D01.Homogeneous.homogeneousENorm_schwartz_ne_top hs φ
  isHomogeneousSliceDatum_sub := fun _ _ _ _ _ hZ hW hz hw =>
    NSFormalization.Section4.D01.Homogeneous.isHomogeneousSliceDatum_sub hZ hW hz hw
  schwartz_integrable_component := fun _ ψ hz i χ =>
    NSFormalization.Section4.D01.Homogeneous.integrable_schwartz_mul_component ψ hz i χ
  compact_exists_homogeneousPath := fun _ hs _ hf hc =>
    ⟨_, NSFormalization.Section4.D01.Homogeneous.isHomogeneousPath_compact hs hf hc⟩
  bochnerDatumENorm_eq_eLpNorm_slice := fun _ _ hs _ hf hc G hG =>
    NSFormalization.Section4.D01.Homogeneous.bochnerDatumENorm_eq_eLpNorm_slice hs hf hc G hG
  eLpNorm_slice_le_forceHomogeneousENorm := fun _ _ hs _ hf hc =>
    NSFormalization.Section4.D01.Homogeneous.eLpNorm_slice_le_forceHomogeneousENorm hs hf hc

end BlowupDensity.Bindings
