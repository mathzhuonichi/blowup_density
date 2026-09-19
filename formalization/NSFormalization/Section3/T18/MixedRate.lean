import NSFormalization.Section3.T18.ForceClass

/-!
# T18 U10: mixed-norm closeness of the inserted force

Admissible Bochner paths representing the same physical slices agree almost
everywhere on positive time.  Consequently both mixed-norm infima are attained
at every admissible path.  This gives path addition, the triangle inequality,
and a converse honesty fact: a finite mixed norm already supplies a
`MemMixedLebesgueT` witness.  The latter turns the correction record's finite
`force_mixed_bound` into the required correction path without adding a new
record field.
-/

noncomputable section

namespace NSFormalization.Section3.T18

open Set MeasureTheory Filter
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpaceTimeField forceTimeMeasure)
open scoped ENNReal

/-- Every admissible torus slice path attains the mixed-norm infimum. -/
theorem mixedLebesgueENormT_eq_of_path {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : SpaceTimeField} {G : ℝ → Lp Space p periodicTorusMeasure}
    (hG : IsPeriodicLebesgueSlicePath p f G)
    (hm : AEStronglyMeasurable G forceTimeMeasure) :
    mixedLebesgueENormT q p f = eLpNorm G q forceTimeMeasure := by
  refine le_antisymm (iInf_le_of_le ⟨G, hG, hm⟩ le_rfl) (le_iInf ?_)
  rintro ⟨G', hG', -⟩
  have hae : G' =ᵐ[forceTimeMeasure] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply Lp.ext
    exact (hG' t (le_of_lt ht)).trans (hG t (le_of_lt ht)).symm
  exact le_of_eq (eLpNorm_congr_ae hae).symm

/-- Every admissible whole-space slice path attains the corresponding source
mixed-norm infimum. -/
theorem mixedLebesgueENorm_eq_of_path {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : SpaceTimeField} {G : ℝ → Lp Space p (volume : Measure Space)}
    (hG : IsLebesgueSlicePath p f G)
    (hm : AEStronglyMeasurable G forceTimeMeasure) :
    mixedLebesgueENorm q p f = eLpNorm G q forceTimeMeasure := by
  refine le_antisymm (iInf_le_of_le ⟨G, hG, hm⟩ le_rfl) (le_iInf ?_)
  rintro ⟨G', hG', -⟩
  have hae : G' =ᵐ[forceTimeMeasure] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply Lp.ext
    exact (hG' t (le_of_lt ht)).trans (hG t (le_of_lt ht)).symm
  exact le_of_eq (eLpNorm_congr_ae hae).symm

/-- A strictly finite torus mixed norm cannot be an empty or nonintegrable
Bochner infimum: path uniqueness upgrades an admissible measurable path to a
`MemLp` path. -/
theorem memMixedLebesgueT_of_lt_top {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : SpaceTimeField} (hfin : mixedLebesgueENormT q p f < ⊤) :
    MemMixedLebesgueT q p f := by
  classical
  let I := {G : ℝ → Lp Space p periodicTorusMeasure //
    IsPeriodicLebesgueSlicePath p f G ∧ AEStronglyMeasurable G forceTimeMeasure}
  have hI : Nonempty I := by
    by_contra hne
    let _ : IsEmpty I := ⟨fun G => hne ⟨G⟩⟩
    have htop : mixedLebesgueENormT q p f = ⊤ := by
      simp only [mixedLebesgueENormT]
      exact iInf_of_empty _
    rw [htop] at hfin
    exact (lt_irrefl _ hfin)
  obtain ⟨⟨G, hpath, hmeas⟩⟩ := hI
  refine ⟨G, hpath, hmeas, ?_⟩
  rw [← mixedLebesgueENormT_eq_of_path hpath hmeas]
  exact hfin

/-- Addition of two representing paths represents physical-field addition. -/
theorem periodicLebesgueSlicePath_add {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f g : SpaceTimeField} {F G : ℝ → Lp Space p periodicTorusMeasure}
    (hF : IsPeriodicLebesgueSlicePath p f F)
    (hG : IsPeriodicLebesgueSlicePath p g G) :
    IsPeriodicLebesgueSlicePath p (fun z => f z + g z) (F + G) := by
  intro t ht
  calc
    (((F + G) t : Lp Space p periodicTorusMeasure) : PeriodicTorus → Space)
        =ᵐ[periodicTorusMeasure]
      (F t : PeriodicTorus → Space) + (G t : PeriodicTorus → Space) :=
        Lp.coeFn_add _ _
    _ =ᵐ[periodicTorusMeasure]
      torusLift (fun x => f (t, x)) + torusLift (fun x => g (t, x)) :=
        (hF t ht).add (hG t ht)
    _ =ᵐ[periodicTorusMeasure]
      torusLift (fun x => f (t, x) + g (t, x)) := by
        filter_upwards with z
        rfl

/-- Honest torus mixed paths are closed under physical-field addition. -/
theorem memMixedLebesgueT_add {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    {f g : SpaceTimeField} (hf : MemMixedLebesgueT q p f)
    (hg : MemMixedLebesgueT q p g) :
    MemMixedLebesgueT q p (fun z => f z + g z) := by
  obtain ⟨F, hF, hFm⟩ := hf
  obtain ⟨G, hG, hGm⟩ := hg
  exact ⟨F + G, periodicLebesgueSlicePath_add hF hG, hFm.add hGm⟩

/-- Triangle inequality for the honest torus mixed norm. -/
theorem mixedLebesgueENormT_add_le {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    (hq : 1 ≤ q) {f g : SpaceTimeField}
    (hf : MemMixedLebesgueT q p f) (hg : MemMixedLebesgueT q p g) :
    mixedLebesgueENormT q p (fun z => f z + g z) ≤
      mixedLebesgueENormT q p f + mixedLebesgueENormT q p g := by
  obtain ⟨F, hF, hFm⟩ := hf
  obtain ⟨G, hG, hGm⟩ := hg
  rw [mixedLebesgueENormT_eq_of_path
      (periodicLebesgueSlicePath_add hF hG) (hFm.add hGm).aestronglyMeasurable,
    mixedLebesgueENormT_eq_of_path hF hFm.aestronglyMeasurable,
    mixedLebesgueENormT_eq_of_path hG hGm.aestronglyMeasurable,
    show (F + G : ℝ → Lp Space p periodicTorusMeasure) = fun t => F t + G t from rfl]
  exact eLpNorm_add_le hFm.aestronglyMeasurable hGm.aestronglyMeasurable hq

/-- The correction bound is finite, hence supplies an honest correction-force
mixed path. -/
theorem correctionForce_mixed_memLp (data : InsertionData)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] (hq : 1 ≤ q) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data)) :
    MemMixedLebesgueT q p
      (correctionForce data.ν data.reference.velocity data.D ε) := by
  apply memMixedLebesgueT_of_lt_top
  refine lt_of_le_of_lt
    (data.correction.force_mixed_bound p q hq ε (correction_range data hε)) ?_
  exact ENNReal.ofReal_lt_top

/-- The source mixed norm is finite whenever the scaling record carries its
honest whole-space path. -/
theorem packetSource_mixedNorm_ne_top (data : InsertionData)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] (hq : 1 ≤ q) :
    mixedLebesgueENorm q p data.packetForce ≠ ⊤ := by
  obtain ⟨G, hG, hGm⟩ := (data.scaling.mixed_memLp p q hq).1
  rw [mixedLebesgueENorm_eq_of_path hG hGm.aestronglyMeasurable]
  exact hGm.eLpNorm_ne_top

/-- The real mixed-rate constant is the correction constant plus the source
packet mixed norm.  Outside `1 ≤ p` it is set to zero; the theorem only uses
the honest range. -/
def forceDiffMixedConst (data : InsertionData) (p q : ℝ≥0∞) : ℝ :=
  if hp : 1 ≤ p then
    letI : Fact (1 ≤ p) := ⟨hp⟩
    data.correction.mixedConst p q +
      (mixedLebesgueENorm q p data.packetForce).toReal
  else 0

/-- The selected mixed-rate constant is nonnegative on its stated range. -/
theorem forceDiffMixedConst_nonneg (data : InsertionData) :
    ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q → 0 ≤ forceDiffMixedConst data p q := by
  intro p q hp hq
  simp only [forceDiffMixedConst, dite_eq_left hp]
  exact add_nonneg (data.correction.mixedConst_nonneg p q hp hq)
    ENNReal.toReal_nonneg

/-- The actual inserted force difference has an honest torus mixed Bochner
path. -/
theorem forceDifference_mixed_memLp (data : InsertionData) :
    ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
      ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
        MemMixedLebesgueT q p (fun z => force data ε z - data.g z) := by
  intro p q _ hq ε hε
  have hH := correctionForce_mixed_memLp data p q hq hε
  have hF := (data.scaling.mixed_memLp p q hq).2 ε (scaling_range data hε)
  have hadd := memMixedLebesgueT_add hH hF
  have heq : (fun z => force data ε z - data.g z) =
      fun z => correctionForce data.ν data.reference.velocity data.D ε z +
        periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε z := by
    funext z
    simp only [force]
    abel
  rw [heq]
  exact hadd

private theorem mixed_real_arithmetic {C n x y : ℝ}
    (hC : 0 ≤ C) (hn : 0 ≤ n) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    C * y + x * n ≤ (C + n) * (x + y) := by
  nlinarith [mul_nonneg hC hx, mul_nonneg hn hy]

/-- `eq:Fclose`: the force difference has the claimed mixed-norm rate. -/
theorem forceDifference_mixed_bound (data : InsertionData) :
    ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
      ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
        mixedLebesgueENormT q p (fun z => force data ε z - data.g z) ≤
          ENNReal.ofReal (forceDiffMixedConst data p q *
            (ε ^ (alphaT p q) + ε ^ (alphaT p q + 1))) := by
  intro p q _ hq ε hε
  let H : SpaceTimeField := correctionForce data.ν data.reference.velocity data.D ε
  let F : SpaceTimeField :=
    periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε
  let N : ℝ≥0∞ := mixedLebesgueENorm q p data.packetForce
  let C : ℝ := data.correction.mixedConst p q
  let x : ℝ := ε ^ alphaT p q
  let y : ℝ := ε ^ (alphaT p q + 1)
  have hHmem : MemMixedLebesgueT q p H := correctionForce_mixed_memLp data p q hq hε
  have hFmem : MemMixedLebesgueT q p F :=
    (data.scaling.mixed_memLp p q hq).2 ε (scaling_range data hε)
  have hC : 0 ≤ C := data.correction.mixedConst_nonneg p q Fact.out hq
  have hx : 0 ≤ x := (Real.rpow_pos_of_pos hε.1 _).le
  have hy : 0 ≤ y := (Real.rpow_pos_of_pos hε.1 _).le
  have hN : N ≠ ⊤ := packetSource_mixedNorm_ne_top data p q hq
  have hn : 0 ≤ N.toReal := ENNReal.toReal_nonneg
  have hdiff : (fun z => force data ε z - data.g z) = fun z => H z + F z := by
    funext z
    simp only [force, H, F]
    abel
  rw [hdiff]
  calc
    mixedLebesgueENormT q p (fun z => H z + F z)
      ≤ mixedLebesgueENormT q p H + mixedLebesgueENormT q p F :=
        mixedLebesgueENormT_add_le hq hHmem hFmem
    _ ≤ ENNReal.ofReal (C * y) + mixedLebesgueENormT q p F := by
      exact add_le_add_left
        (data.correction.force_mixed_bound p q hq ε (correction_range data hε)) _
    _ = ENNReal.ofReal (C * y) + ENNReal.ofReal x * N := by
      rw [data.scaling.packetMixedScaling p q hq ε (scaling_range data hε)]
    _ = ENNReal.ofReal (C * y) + ENNReal.ofReal (x * N.toReal) := by
      have hNcoe : ENNReal.ofReal N.toReal = N := ENNReal.ofReal_toReal hN
      have hmul : ENNReal.ofReal x * N = ENNReal.ofReal (x * N.toReal) := by
        calc
          ENNReal.ofReal x * N = ENNReal.ofReal x * ENNReal.ofReal N.toReal :=
            congrArg (ENNReal.ofReal x * ·) hNcoe.symm
          _ = ENNReal.ofReal (x * N.toReal) := (ENNReal.ofReal_mul hx).symm
      rw [hmul]
    _ = ENNReal.ofReal (C * y + x * N.toReal) := by
      rw [ENNReal.ofReal_add (mul_nonneg hC hy) (mul_nonneg hx hn)]
    _ ≤ ENNReal.ofReal ((C + N.toReal) * (x + y)) :=
      ENNReal.ofReal_le_ofReal (mixed_real_arithmetic hC hn hx hy)
    _ = ENNReal.ofReal (forceDiffMixedConst data p q *
          (ε ^ alphaT p q + ε ^ (alphaT p q + 1))) := by
      simp only [forceDiffMixedConst, dite_eq_left Fact.out, C, N, x, y]

end NSFormalization.Section3.T18
