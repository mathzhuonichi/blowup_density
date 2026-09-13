import NSFormalization.Section4.D01.SmoothDatum
import NSFormalization.Source.FourierPhysicalJets
import NSFormalization.Paper3.AngularTameProduct
import NSFormalization.Section4.A05.SmoothJets

/-!
# From the datum form of `H^m` to square-integrable jets (unit D01/L2, `⟹`)

`verification/Contracts/V1/Data.lean` states every Sobolev quantity of Section 4 in the
**datum** form

```
IsSobolevDatum (s : ℝ) (z : SpatialField) (A : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((A i : FourierData)) ψ = ∫ x : Space, ψ x * ((z x i : ℝ) : ℂ)
```

(`Contracts/V1/Data.lean:160`), with `MemHInfty a := ContDiff ℝ ∞ a ∧ ∀ m : ℕ, ∃ A,
IsSobolevDatum (m : ℝ) a A` (`:495`) and `sobolevENorm s z := ⨅ A : {A // IsSobolevDatum s z A},
‖A.1‖ₑ` (`:189`).  Lane 020's `NSFormalization.Section4.D01.SmoothDatum` proves the `⟸`
direction (jets ⟹ datum).  **This module proves the `⟹` direction, quantitatively**, and adds
the time-slice extraction from `Contracts.V1.Data.ClassicalSolutionR` (`:624`).

Together with `SmoothDatum.memHInfty_of_contDiff_memLp` this closes the equivalence of
`RECONCILIATION.md` unit **L2**, including its third clause
"either implies `∃ A : SmoothL2Field Space, A.field = a`".

## What the consumers get

* `research/A05/REVIEW_CONTRACT.md:93-113` and `research/A03/REVIEW_CONTRACT.md` §6 list three
  missing steps between `Data.MemHInfty` and the registered jet-form contracts
  `Contracts.V1.GradientL6` (`SmoothSquareIntegrableJets`) and
  `Contracts.V1.BoundedRepresentative` (`SmoothJetsUpTo`, `jetSobolevENorm`):
  (1) datum ⟹ jets, (2) a time-slice extraction, (3) the quantitative half
  `jetSobolevENorm 2 z ≤ C · sobolevENorm 2 z`.  All three are proved below:
  (1) `memLp_iteratedFDeriv_of_isSobolevDatum` and `memHInfty_jets`,
  (2) `contDiff_slice` / `smoothSquareIntegrableJets_slice`,
  (3) `jetSobolevENorm_le_sobolevENorm`.
* `research/A03/COMPARISON.md` unit **U2** (`memHInfty_memHm`, `memHInfty_component`): the
  jet side of `MemHInfty` is now available; `memHInfty_component` and `memHInfty_partialDeriv`
  additionally need derivative-closure, which is `SmoothDatum`'s
  `exists_isSobolevDatum_fderiv` composed with `memHInfty_jets` and is **not** stated here.
* `research/A02/COMPARISON.md` unit **U1** (U1a energy, U1b(iii)): `slice_jets_of_sobolevPath`
  starts exactly at `ClassicalSolutionR.velocity_smooth` + `ClassicalSolutionR.sobolev`
  (`Data.lean:632,643`), the place U1b actually begins.  U1b(i) (the embedding) and U1b(ii)
  (the order shift on the datum carrier) remain untouched.

## Conventions

The Fourier normalization is the manuscript's angular one,
`ẑ(ξ) = (2π)^{-3/2} ∫ e^{-i x·ξ} z(x) dx` with
`‖z‖²_{H^s} = ∫ (1+|ξ|²)^s |ẑ(ξ)|² dξ` (`paper/sections/01-introduction.tex:85-91`), carried by
`Paper3.angularRealization`; the three components are summed with the Euclidean `PiLp 2` norm of
`01-introduction.tex:103`, i.e. `Paper3.RealVectorSobolev`.

**The `(2π)` factor.**  Every constant below carries one explicit power of
`Source.frequencyUnit = 2π` (`Source/FourierConvention.lean:15`) per unit of Sobolev order, and
nothing else that depends on the manuscript's normalization.  It enters exactly once, in
`Paper3.cyclesToAngular_symm_norm_le` (`AngularTameProduct.lean:20`), which converts the
manuscript's angular datum into the cycles-convention datum that `Source.FourierPhysicalJets`
inverts: the two Bessel weights `(1+|ξ|²)^{s/2}` and `(1+4π²|ξ|²)^{s/2}` differ by at most
`(2π)^{|s|}`.  The remaining links are contractive (order lowering) or are the fixed
finite-dimensional reassembly constant `‖physicalJetLp j‖`, which depends only on `j` and on the
dimension three.

## Route

`Source.FourierPhysicalJets` already inverts a **cycles-convention** Sobolev datum into physical
Fréchet jets: `physicalJetLp n` (`:159`) is a bounded linear map
`(Fin 3 → SobolevHilbert n) →L[ℝ] Lp (Space [×n]→L[ℝ] Space) 2 volume`, and `physicalJetLp_ae`
identifies its value a.e. with `iteratedFDeriv ℝ n f` as soon as `f` is smooth and each component
datum represents `f` against compactly supported tests (`CompactRep`).  Three things are added
here.

1. *Angular ⟹ cycles.*  `Paper3.cyclesToAngular` (`AngularTameProduct.lean:11`) is a linear
   homeomorphism `SobolevHilbert s ≃L[ℂ] Lp ℂ 2 volume` with
   `angularRealization_eq_cycles` (`:31`) saying that the two realizations agree; so the
   manuscript's angular datum transports to a cycles datum representing the *same* tempered
   distribution, at the cost of `(2π)^{|s|}`.
2. *Order lowering.*  `Paper3.sobolevOrderLowering` (`SobolevOrderLowering.lean:26`) is
   contractive and preserves the realization (`sobolevRealization_orderLowering`, `:78`), so a
   datum at order `m` gives one at every order `j ≤ m`.
3. *The pairing shape.*  `Data.IsSobolevDatum` pairs against **every** Schwartz test, which is
   strictly more than `CompactRep` asks; the conversion is `smul_eq_mul`.

The identification of the distributional with the classical derivative — the analytic heart — is
already inside `FourierPhysicalJets.compactRep_directional` (`:60`), which routes through
`Paper3.sobolevRealization_directionalDerivative` and
`Source.WeakClassicalDerivative.ae_eq_classical_derivative`.  Nothing here re-proves it.

`IsSobolevDatum`, `sobolevENorm` (from `SmoothDatum`) and `SmoothSquareIntegrableJets`,
`SmoothJetsUpTo`, `jetSobolevENorm` (below) are *definitionally* the corresponding declarations of
`Contracts/V1/Data.lean`, `Contracts/V1/GradientL6.lean` and
`Contracts/V1/BoundedRepresentative.lean`; they are restated because the `NSFormalization`
package is a dependency of the `Contracts` library and cannot import it.  The agreement is
`Iff.rfl` / `rfl` and is recorded in `research/D01/ATTEMPTS_DATUM_TO_JETS.md`.
-/

noncomputable section

namespace NSFormalization.Section4.D01

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Source.FourierPhysicalJets
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. The jet-form classes of the two registered contracts, restated

`Contracts.V1.SmoothSquareIntegrableJets` (`Contracts/V1/GradientL6.lean:104`),
`Contracts.V1.BoundedRep.SmoothJetsUpTo` and `Contracts.V1.BoundedRep.jetSobolevENorm`
(`Contracts/V1/BoundedRepresentative.lean`), restated verbatim.  `SpatialField` is an `abbrev`
for `Space → Space` (`Data.lean:99`), so the types agree on the nose. -/

/-- `Contracts.V1.SmoothSquareIntegrableJets`, restated verbatim: the jet form of
`02-preliminaries.tex:12` eq:Rinitial's `H^∞(R³;R³)`. -/
def SmoothSquareIntegrableJets (v : Space → Space) : Prop :=
  ContDiff ℝ ∞ v ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n v) 2 volume

/-- `Contracts.V1.BoundedRep.SmoothJetsUpTo`, restated verbatim: smooth, with every Fréchet jet
of order at most `m` square integrable. -/
def SmoothJetsUpTo (m : ℕ) (v : Space → Space) : Prop :=
  ContDiff ℝ ∞ v ∧ ∀ j ≤ m, MemLp (iteratedFDeriv ℝ j v) 2 volume

/-- `Contracts.V1.BoundedRep.jetSobolevENorm`, restated verbatim: `‖v‖_{H^m(R³)}` in jet form. -/
def jetSobolevENorm (m : ℕ) (v : Space → Space) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (m + 1), eLpNorm (iteratedFDeriv ℝ j v) 2 volume

theorem smoothJetsUpTo_of_allOrders (m : ℕ) {v : Space → Space}
    (h : SmoothSquareIntegrableJets v) : SmoothJetsUpTo m v :=
  ⟨h.1, fun j _ => h.2 j⟩

/-! ## 2. The manuscript's angular datum as a cycles-convention datum -/

/-- One component of the manuscript's angular real-vector datum, read in the cycles convention
that `Source.FourierPhysicalJets` inverts.  `Paper3.cyclesToAngular` (`AngularTameProduct.lean:11`)
is a linear homeomorphism, so no information is lost; only the `(2π)^{|s|}` of
`cyclesToAngular_symm_norm_le` (`:20`) is paid. -/
def cyclesComponentOfAngular (s : ℝ) (A : RealVectorSobolev s) (i : Fin 3) : SobolevHilbert s :=
  (cyclesToAngular s).symm ((A i : FourierData))

/-- The transport preserves the realized tempered distribution
(`Paper3.angularRealization_eq_cycles`, `AngularTameProduct.lean:31`). -/
theorem sobolevRealization_cyclesComponentOfAngular (s : ℝ) (A : RealVectorSobolev s)
    (i : Fin 3) :
    sobolevRealization s (cyclesComponentOfAngular s A i) =
      angularRealization s ((A i : FourierData)) :=
  (angularRealization_eq_cycles s _).symm

/-- The only place a `(2π)` enters: `Source.frequencyUnit = 2π`
(`Source/FourierConvention.lean:15`) to the power `|s|`. -/
theorem norm_cyclesComponentOfAngular_le (s : ℝ) (A : RealVectorSobolev s) (i : Fin 3) :
    ‖cyclesComponentOfAngular s A i‖ ≤ frequencyUnit ^ |s| * ‖A‖ :=
  (cyclesToAngular_symm_norm_le s _).trans
    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le A i)
      (Real.rpow_nonneg frequencyUnit_pos.le _))

/-- `Contracts.V1.Data.IsSobolevDatum` pairs against **every** Schwartz test, which is more than
`FourierPhysicalJets.CompactRep` (`:14`) demands. -/
theorem compactRep_cyclesComponentOfAngular {s : ℝ} {z : Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) (i : Fin 3) :
    CompactRep s (cyclesComponentOfAngular s A i) (fun x => ((z x i : ℝ) : ℂ)) := by
  intro ψ _
  rw [sobolevRealization_cyclesComponentOfAngular, hA i ψ]
  simp only [smul_eq_mul]

/-! ## 3. Lowering to an integer order below `m` -/

/-- The order-`j` cycles datum of one component of `z`, obtained from its order-`m` angular datum
by `Paper3.sobolevOrderLowering` (`SobolevOrderLowering.lean:26`), which is contractive. -/
def loweredComponent (m j : ℕ) (hj : j ≤ m) (A : RealVectorSobolev (m : ℝ)) (i : Fin 3) :
    SobolevHilbert (j : ℝ) :=
  sobolevOrderLowering (m : ℝ) (j : ℝ) (by exact_mod_cast hj)
    (cyclesComponentOfAngular (m : ℝ) A i)

theorem compactRep_loweredComponent {m j : ℕ} (hj : j ≤ m) {z : Space → Space}
    {A : RealVectorSobolev (m : ℝ)} (hA : IsSobolevDatum (m : ℝ) z A) (i : Fin 3) :
    CompactRep (j : ℝ) (loweredComponent m j hj A i) (fun x => ((z x i : ℝ) : ℂ)) := by
  intro ψ hψ
  rw [loweredComponent, sobolevRealization_orderLowering]
  exact compactRep_cyclesComponentOfAngular hA i ψ hψ

theorem norm_loweredComponent_le (m j : ℕ) (hj : j ≤ m) (A : RealVectorSobolev (m : ℝ))
    (i : Fin 3) :
    ‖loweredComponent m j hj A i‖ ≤ frequencyUnit ^ (m : ℝ) * ‖A‖ := by
  refine (sobolevOrderLowering_norm_le _ _ _ _).trans ?_
  refine (norm_cyclesComponentOfAngular_le (m : ℝ) A i).trans_eq ?_
  rw [abs_of_nonneg (Nat.cast_nonneg m)]

/-! ## 4. The jets of a smooth field with a datum -/

/-- The order-`j` Fréchet jet reconstructed from the order-`m` angular datum, as an element of
`L²`.  `FourierPhysicalJets.physicalJetLp` (`:159`) is a bounded linear map, which is where the
constant of `jetDatumConst` comes from. -/
def jetOfDatum (m j : ℕ) (hj : j ≤ m) (A : RealVectorSobolev (m : ℝ)) :
    Lp (Space [×j]→L[ℝ] Space) 2 (volume : Measure Space) :=
  physicalJetLp j (fun i => loweredComponent m j hj A i)

/-- `FourierPhysicalJets.physicalJetLp_ae` (`:159`): for a smooth field the reconstruction is the
classical jet. -/
theorem jetOfDatum_ae {m j : ℕ} (hj : j ≤ m) {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    {A : RealVectorSobolev (m : ℝ)} (hA : IsSobolevDatum (m : ℝ) z A) :
    (jetOfDatum m j hj A : Space → (Space [×j]→L[ℝ] Space)) =ᵐ[volume]
      iteratedFDeriv ℝ j z :=
  physicalJetLp_ae j hz _ (fun i => compactRep_loweredComponent hj hA i)

/-- The constant `C_{j,m}` of the datum ⟹ jet bound.  It depends only on the jet order `j`, the
datum order `m` and the fixed dimension three:

* `‖physicalJetLp j‖` is the operator norm of the finite-dimensional reassembly of the `3^{j+1}`
  coordinate words into a `j`-multilinear map (`FourierPhysicalJets.physicalJetLp`, `:159`);
* `frequencyUnit ^ (m : ℝ) = (2π)^m` is the manuscript-versus-cycles Bessel weight ratio of
  `Paper3.cyclesToAngular_symm_norm_le` (`AngularTameProduct.lean:20`).

The `+ 1` is only there to make `jetDatumConst_pos` free; the honest bound is with
`‖physicalJetLp j‖`. -/
def jetDatumConst (j m : ℕ) : ℝ := (‖physicalJetLp j‖ + 1) * frequencyUnit ^ (m : ℝ)

theorem jetDatumConst_pos (j m : ℕ) : 0 < jetDatumConst j m := by
  have h₁ : (0 : ℝ) < ‖physicalJetLp j‖ + 1 := by positivity
  exact mul_pos h₁ (Real.rpow_pos_of_pos frequencyUnit_pos _)

theorem norm_jetOfDatum_le (m j : ℕ) (hj : j ≤ m) (A : RealVectorSobolev (m : ℝ)) :
    ‖jetOfDatum m j hj A‖ ≤ jetDatumConst j m * ‖A‖ := by
  have hfu : (0 : ℝ) ≤ frequencyUnit ^ (m : ℝ) := (Real.rpow_pos_of_pos frequencyUnit_pos _).le
  have hdata : ‖fun i => loweredComponent m j hj A i‖ ≤ frequencyUnit ^ (m : ℝ) * ‖A‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => norm_loweredComponent_le m j hj A i
  refine ((physicalJetLp j).le_opNorm _).trans ?_
  refine (mul_le_mul_of_nonneg_left hdata (norm_nonneg _)).trans ?_
  have hA : (0 : ℝ) ≤ ‖A‖ := norm_nonneg A
  have hP : (0 : ℝ) ≤ ‖physicalJetLp j‖ := norm_nonneg (physicalJetLp j)
  unfold jetDatumConst
  nlinarith [mul_nonneg hfu hA]

/-! ## 5. Goal 1: datum ⟹ jets, quantitatively -/

/-- **Unit L2, the `⟹` direction.**  A smooth field with an order-`m` angular Sobolev datum in the
sense of `Contracts.V1.Data.IsSobolevDatum` (`Data.lean:160`) has square-integrable Fréchet jets
in every order `j ≤ m`. -/
theorem memLp_iteratedFDeriv_of_isSobolevDatum {m j : ℕ} (hj : j ≤ m) {z : Space → Space}
    (hz : ContDiff ℝ ∞ z) {A : RealVectorSobolev (m : ℝ)} (hA : IsSobolevDatum (m : ℝ) z A) :
    MemLp (iteratedFDeriv ℝ j z) 2 volume :=
  (memLp_congr_ae (jetOfDatum_ae hj hz hA)).mp (Lp.memLp _)

/-- **Unit L2, the `⟹` direction, quantitatively.**  The order-`j` jet norm is bounded by the
manuscript's order-`m` datum norm, with a constant depending only on `j`, `m` and the dimension
three, carrying exactly one `(2π)^m`. -/
theorem eLpNorm_iteratedFDeriv_le_of_isSobolevDatum {m j : ℕ} (hj : j ≤ m) {z : Space → Space}
    (hz : ContDiff ℝ ∞ z) {A : RealVectorSobolev (m : ℝ)} (hA : IsSobolevDatum (m : ℝ) z A) :
    eLpNorm (iteratedFDeriv ℝ j z) 2 volume ≤ ENNReal.ofReal (jetDatumConst j m) * ‖A‖ₑ := by
  have hcong : eLpNorm (iteratedFDeriv ℝ j z) 2 volume
      = eLpNorm (jetOfDatum m j hj A : Space → (Space [×j]→L[ℝ] Space)) 2 volume :=
    (eLpNorm_congr_ae (jetOfDatum_ae hj hz hA)).symm
  have hLp : eLpNorm (jetOfDatum m j hj A : Space → (Space [×j]→L[ℝ] Space)) 2 volume
      = ENNReal.ofReal ‖jetOfDatum m j hj A‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  rw [hcong, hLp, ← ofReal_norm A, ← ENNReal.ofReal_mul (jetDatumConst_pos j m).le]
  exact ENNReal.ofReal_le_ofReal (norm_jetOfDatum_le m j hj A)

/-- **A02 unit U1a's order-zero step** (`research/A02/COMPARISON.md:163`, "a D01 order-0-datum ⟹
`L²`-slice realization lemma"): a smooth field with a datum at *any* integer order is itself square
integrable, which is what `SquareIntegrableAtTime` / `kineticEnergy`
(`vendor/…/NavierStokes/R3/ProblemStatement.lean:71,76,81`) and `Data.energyEssSup`
(`Data.lean:444`) need.  Same normalization step as `A05.SmoothL2.memLp`
(`A05/SmoothJets.lean:52`): `‖iteratedFDeriv ℝ 0 z x‖ = ‖z x‖`. -/
theorem memLp_of_isSobolevDatum {m : ℕ} {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    {A : RealVectorSobolev (m : ℝ)} (hA : IsSobolevDatum (m : ℝ) z A) :
    MemLp z 2 volume :=
  (memLp_iteratedFDeriv_of_isSobolevDatum (Nat.zero_le m) hz hA).congr_norm
    hz.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_zero)

/-- The quantitative form of the previous lemma: the `L²` norm of the field itself against the
manuscript's order-`m` datum norm. -/
theorem eLpNorm_le_of_isSobolevDatum {m : ℕ} {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    {A : RealVectorSobolev (m : ℝ)} (hA : IsSobolevDatum (m : ℝ) z A) :
    eLpNorm z 2 volume ≤ ENNReal.ofReal (jetDatumConst 0 m) * ‖A‖ₑ := by
  have he : eLpNorm z 2 volume = eLpNorm (iteratedFDeriv ℝ 0 z) 2 volume :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_zero.symm)
  rw [he]
  exact eLpNorm_iteratedFDeriv_le_of_isSobolevDatum (Nat.zero_le m) hz hA

/-- **Unit L2, the `⟹` direction of `RECONCILIATION.md:153`.**  The hypothesis is definitionally
`Contracts.V1.Data.MemHInfty z` (`Data.lean:495`); the conclusion is the second half of
`Contracts.V1.SmoothSquareIntegrableJets` (`GradientL6.lean:104`). -/
theorem memHInfty_jets {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    (hA : ∀ m : ℕ, ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) z A) :
    ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n z) 2 volume := by
  intro n
  obtain ⟨A, hA⟩ := hA n
  exact memLp_iteratedFDeriv_of_isSobolevDatum (le_refl n) hz hA

/-- **Unit L2, the equivalence.**  The datum form of `H^∞` used throughout
`Contracts/V1/Data.lean` and the jet form used by the registered contracts
`Contracts.V1.GradientL6` and `Contracts.V1.BoundedRepresentative` are the same class.  The `←`
direction is lane 020's `SmoothDatum.memHInfty_of_contDiff_memLp`. -/
theorem memHInfty_iff_smoothSquareIntegrableJets {z : Space → Space} :
    (ContDiff ℝ ∞ z ∧ ∀ m : ℕ, ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) z A) ↔
      SmoothSquareIntegrableJets z :=
  ⟨fun h => ⟨h.1, memHInfty_jets h.1 h.2⟩,
    fun h => memHInfty_of_contDiff_memLp h.1 h.2⟩

/-- The third clause of `RECONCILIATION.md` unit L2: the datum form produces the upstream
jet carrier `EulerLpTranslation.SmoothL2Field` (`vendor/…/Euler/LpSmoothField.lean:31`). -/
theorem exists_smoothL2Field_of_memHInfty {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    (hA : ∀ m : ℕ, ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) z A) :
    ∃ B : EulerLpTranslation.SmoothL2Field Space, B.field = z :=
  ⟨⟨z, hz, memHInfty_jets hz hA⟩, rfl⟩

/-! ## 6. Goal 1, second half: the jet norm against the manuscript's datum norm -/

/-- The constant of `jetSobolevENorm_le_sobolevENorm`: the sum over the orders `j ≤ m` of
`jetDatumConst j m`.  Depends only on `m` and the dimension three, and carries exactly one
`(2π)^m`. -/
def jetSobolevConst (m : ℕ) : ℝ := ∑ j ∈ Finset.range (m + 1), jetDatumConst j m

theorem jetSobolevConst_pos (m : ℕ) : 0 < jetSobolevConst m :=
  Finset.sum_pos (fun j _ => jetDatumConst_pos j m) ⟨0, Finset.mem_range.mpr m.succ_pos⟩

theorem jetSobolevENorm_le_of_isSobolevDatum (m : ℕ) {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    {A : RealVectorSobolev (m : ℝ)} (hA : IsSobolevDatum (m : ℝ) z A) :
    jetSobolevENorm m z ≤ ENNReal.ofReal (jetSobolevConst m) * ‖A‖ₑ := by
  have hsum : ENNReal.ofReal (jetSobolevConst m)
      = ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (jetDatumConst j m) := by
    rw [jetSobolevConst, ENNReal.ofReal_sum_of_nonneg]
    exact fun j _ => (jetDatumConst_pos j m).le
  rw [hsum, Finset.sum_mul, jetSobolevENorm]
  refine Finset.sum_le_sum fun j hj => ?_
  exact eLpNorm_iteratedFDeriv_le_of_isSobolevDatum
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hz hA

/-- **The quantitative half that `research/A03/REVIEW_CONTRACT.md` §6(3) asks for.**  The jet
`H^m` norm of `Contracts.V1.BoundedRep.jetSobolevENorm` is bounded by the manuscript's datum norm
`Contracts.V1.Data.sobolevENorm` (`Data.lean:189`) — an infimum, so the bound must hold for
*every* datum, which is exactly `jetSobolevENorm_le_of_isSobolevDatum`.

At `m = 2` this is what makes `A03.bounded_representative`'s `eLpNormTop_le` composable with
`04-whole-space.tex:53`, where the extension's bound is supplied in `C_tH²`, the datum norm.

If `z` has no order-`m` datum then `sobolevENorm (m : ℝ) z = ⊤` (the empty infimum) and the bound
is vacuous but true; the constant is positive, so `⊤` is not silently turned into `0`. -/
theorem jetSobolevENorm_le_sobolevENorm (m : ℕ) {z : Space → Space} (hz : ContDiff ℝ ∞ z) :
    jetSobolevENorm m z ≤ ENNReal.ofReal (jetSobolevConst m) * sobolevENorm (m : ℝ) z := by
  by_cases hne : Nonempty {A : RealVectorSobolev (m : ℝ) // IsSobolevDatum (m : ℝ) z A}
  · have := hne
    rw [sobolevENorm, ENNReal.mul_iInf fun h => absurd h ENNReal.ofReal_ne_top]
    exact le_iInf fun A => jetSobolevENorm_le_of_isSobolevDatum m hz A.2
  · have : IsEmpty {A : RealVectorSobolev (m : ℝ) // IsSobolevDatum (m : ℝ) z A} :=
      not_nonempty_iff.mp hne
    have hzero : sobolevENorm (m : ℝ) z = ⊤ := by
      rw [sobolevENorm]
      exact iInf_of_empty _
    rw [hzero, ENNReal.mul_top (by simpa using jetSobolevConst_pos m)]
    exact le_top

/-! ## 7. Goal 2: time-slice extraction from a classical solution -/

/-- The spatial slice of a field smooth on the closed-at-zero slab `[0,T) × R³` is smooth on all
of `R³`, **including at `t = 0`**, where the slab is one-sided in time: the slab still contains a
full spatial neighbourhood of every `(t,x)` with `t ∈ [0,T)`, so composing with the affine
inclusion `x ↦ (t,x)` lands the `ContDiffWithinAt` data on a genuine neighbourhood in the slice.

The hypothesis is field-for-field `Contracts.V1.Data.ClassicalSolutionR.velocity_smooth`
(`Data.lean:632`); the same statement serves `pressure_smooth` (`:634`). -/
theorem contDiff_slice {T : ℝ} {v : ℝ × Space → Space}
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) : ContDiff ℝ ∞ fun x : Space => v (t, x) := by
  rw [← contDiffOn_univ]
  have hmap : ContDiffOn ℝ ∞ (fun x : Space => (t, x)) (univ : Set Space) :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hsub : (univ : Set Space) ⊆
      (fun x : Space => (t, x)) ⁻¹' (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    fun x _ => ⟨ht, mem_univ x⟩
  exact hv.comp hmap hsub

/-- The same for a scalar field, e.g. `ClassicalSolutionR.pressure` (`Data.lean:634`). -/
theorem contDiff_slice_scalar {T : ℝ} {p : ℝ × Space → ℝ}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) : ContDiff ℝ ∞ fun x : Space => p (t, x) := by
  rw [← contDiffOn_univ]
  have hmap : ContDiffOn ℝ ∞ (fun x : Space => (t, x)) (univ : Set Space) :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hsub : (univ : Set Space) ⊆
      (fun x : Space => (t, x)) ⁻¹' (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    fun x _ => ⟨ht, mem_univ x⟩
  exact hp.comp hmap hsub

/-- **Goal 2.**  The velocity slice of a classical solution is a smooth field with all Fréchet
jets square integrable, i.e. it satisfies `Contracts.V1.SmoothSquareIntegrableJets`
(`GradientL6.lean:104`), so `A05.gradient_l6` applies to it.

The two hypotheses are field-for-field `Contracts.V1.Data.ClassicalSolutionR.velocity_smooth`
(`Data.lean:632`) and `.sobolev` (`:643`); the `ContinuousOn` conjunct of `.sobolev` is not used
and is therefore not part of the hypothesis. -/
theorem smoothSquareIntegrableJets_slice {T : ℝ} {v : ℝ × Space → Space}
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => v (t, x)) (G t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    SmoothSquareIntegrableJets fun x : Space => v (t, x) := by
  refine ⟨contDiff_slice hv ht, memHInfty_jets (contDiff_slice hv ht) ?_⟩
  intro m
  obtain ⟨G, hG⟩ := hsob m
  exact ⟨G t, hG t ht⟩

/-- **Goal 2, the `A03` form.**  The velocity slice satisfies
`Contracts.V1.BoundedRep.SmoothJetsUpTo m` (`BoundedRepresentative.lean`) at every order, in
particular at `m = 2`, which is the hypothesis of `A03.bounded_representative`'s `supNorm_le` and
`eLpNormTop_le`. -/
theorem smoothJetsUpTo_slice {T : ℝ} {v : ℝ × Space → Space}
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => v (t, x)) (G t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (m : ℕ) :
    SmoothJetsUpTo m fun x : Space => v (t, x) :=
  smoothJetsUpTo_of_allOrders m (smoothSquareIntegrableJets_slice hv hsob ht)

/-! ## 8. Goal 3: the corollaries the consumers apply -/

/-- **The `A03 → R42` corollary.**  For every time `t < T` of a classical solution, the velocity
slice satisfies `SmoothJetsUpTo 2` *and* its jet `H²` norm is bounded by the manuscript's datum
norm of the same slice.  Chaining with `A03.bounded_representative.eLpNormTop_le` gives

`‖u(t,·)‖_{L^∞} ≤ Cinfty · jetSobolevENorm 2 (u(t,·)) ≤ Cinfty · C₂ · sobolevENorm 2 (u(t,·))`,

which is the `04-whole-space.tex:53` step of Theorem 4.2 with the manuscript's own `C_tH²` norm on
the right. -/
theorem slice_jets_and_bound {T : ℝ} {v : ℝ × Space → Space}
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => v (t, x)) (G t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (m : ℕ) :
    SmoothJetsUpTo m (fun x : Space => v (t, x)) ∧
      jetSobolevENorm m (fun x : Space => v (t, x))
        ≤ ENNReal.ofReal (jetSobolevConst m) * sobolevENorm (m : ℝ) fun x => v (t, x) :=
  ⟨smoothJetsUpTo_slice hv hsob ht m,
    jetSobolevENorm_le_sobolevENorm m (contDiff_slice hv ht)⟩

/-- **The `A05 → R43/R44` corollary.**  For every time `t < T` the velocity slice is in the class
`SmoothSquareIntegrableJets` on which `A05.gradient_l6` and `A05.hessianLaplacianIdentity` are
stated, with the jet-order-`j` bound by the datum norm available at every order. -/
theorem slice_allOrderJets_and_bound {T : ℝ} {v : ℝ × Space → Space}
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => v (t, x)) (G t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    SmoothSquareIntegrableJets (fun x : Space => v (t, x)) ∧
      ∀ m : ℕ, jetSobolevENorm m (fun x : Space => v (t, x))
        ≤ ENNReal.ofReal (jetSobolevConst m) * sobolevENorm (m : ℝ) fun x => v (t, x) :=
  ⟨smoothSquareIntegrableJets_slice hv hsob ht,
    fun m => jetSobolevENorm_le_sobolevENorm m (contDiff_slice hv ht)⟩

/-- **The `H^∞` initial-datum corollary.**  `Contracts.V1.Data.initialClassR` (`Data.lean:509`) is
`MemHInfty a ∧ IsSolenoidal a`; its first conjunct now yields both jet-form classes, so
`A03.bounded_representative` and `A05.gradient_l6` apply to the reference initial velocity and, by
`smoothSquareIntegrableJets_slice`, to every slice of the reference solution. -/
theorem memHInfty_jetClasses {a : Space → Space} (hz : ContDiff ℝ ∞ a)
    (hA : ∀ m : ℕ, ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) a A) :
    SmoothSquareIntegrableJets a ∧ ∀ m : ℕ, SmoothJetsUpTo m a :=
  ⟨memHInfty_iff_smoothSquareIntegrableJets.mp ⟨hz, hA⟩,
    fun m => smoothJetsUpTo_of_allOrders m (memHInfty_iff_smoothSquareIntegrableJets.mp ⟨hz, hA⟩)⟩

/-! ## 9. Derivative closure, and the pressure slice

`Contracts/V1/BoundedRepresentative.lean`'s module docstring records that the uniqueness
coefficient `‖∇u₂‖_∞` of `appendix-a-local-theory.tex:120-123` needs *derivative-closure of the
field class* on top of the clauses it registers, and that the contract supplies none.  Lane 019's
`NSFormalization.Section4.A05.SmoothL2.dir` (`A05/SmoothJets.lean:94`) is exactly that closure on
the jet form; composed with the two directions of unit L2 it becomes closure of the **datum**
form, which is `research/A03/Spec.lean`'s `memHInfty_partialDeriv`.

`A05.dirDeriv i v` (`A05/SmoothJets.lean:87`) is `fun x => fderiv ℝ v x (coordinateVector i)`,
definitionally `Contracts.V1.partialDeriv i v` (`GradientL6.lean:88`), which unfolds to
`spatialDerivative (lift v) 0 x (coordinateVector i)`. -/

/-- Derivative closure of the jet form, reusing lane 019's `A05.SmoothL2.dir`
(`A05/SmoothJets.lean:94`). -/
theorem smoothSquareIntegrableJets_dirDeriv {z : Space → Space}
    (h : SmoothSquareIntegrableJets z) (i : Fin 3) :
    SmoothSquareIntegrableJets (A05.dirDeriv i z) :=
  A05.SmoothL2.dir h i

/-- **Derivative closure of `Contracts.V1.Data.MemHInfty` (`Data.lean:495`)**, i.e.
`research/A03/Spec.lean:339`'s `memHInfty_partialDeriv`.  The route is datum ⟹ jets (this module)
⟹ derivative jets (lane 019) ⟹ datum (lane 020), so it exists only now that both directions of
unit L2 are available. -/
theorem memHInfty_dirDeriv {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    (hA : ∀ m : ℕ, ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) z A) (i : Fin 3) :
    ContDiff ℝ ∞ (A05.dirDeriv i z) ∧
      ∀ m : ℕ, ∃ A : RealVectorSobolev (m : ℝ),
        IsSobolevDatum (m : ℝ) (A05.dirDeriv i z) A := by
  have h := smoothSquareIntegrableJets_dirDeriv
    (memHInfty_iff_smoothSquareIntegrableJets.mp ⟨hz, hA⟩) i
  exact memHInfty_of_contDiff_memLp h.1 h.2

/-- The pressure gradient of a classical solution is smooth in space on every slice.

This is **all** that is cheap for the pressure: `ClassicalSolutionR.pressure_gradient`
(`Data.lean:654`) gives `∇p(t,·) ∈ L²` at order zero only, and no field of the structure gives a
Sobolev datum for `p` or `∇p` at any positive order, so neither
`SmoothSquareIntegrableJets (∇p(t,·))` nor `SmoothJetsUpTo 1 (∇p(t,·))` follows from the class as
specified. -/
theorem contDiff_pressureGradient_slice {T : ℝ} {p : ℝ × Space → ℝ}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ fun x : Space => pressureGradient p t x := by
  have hd : ContDiff ℝ ∞ fun x : Space => fderiv ℝ (fun y : Space => p (t, y)) x :=
    (contDiff_slice_scalar hp ht).fderiv_right (m := ∞) (by simp)
  refine ContDiff.sum (fun i _ => ?_)
  exact ContDiff.smul
    ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).contDiff.comp hd) contDiff_const

end NSFormalization.Section4.D01
