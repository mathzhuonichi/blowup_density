import NavierStokes.ActualParticularDynamics

/-!
# Actual particular dynamics with default heartbeat limits

Replacement proofs for the two declarations in `ActualParticularDynamics` that
use `maxHeartbeats 1000000`. The imported module supplies the definitions and
supporting lemmas; the proofs below do not invoke either original target theorem.
The theorem statements are unchanged. This investigation edits only this file.

* `native_fast`: restrict `slotDirection_transport` to the left-hand side with
  `conv_lhs => erw [...]`, then use ordinary `rw` for the remaining rewrites.
  The original unrestricted `erw` also tries to match the transport expression
  against the right-hand side, causing expensive definitional unfolding.
* `selected_principal`: prove the equality between the selected normal and the
  original normal once (`hnormal`, by `rfl`), then rewrite with it in `hN` and
  `hδ`. This avoids rediscovering that equality underneath the squared norm by
  unfolding the Euclidean norm and the reindexed data.

Separate `#count_heartbeats in` measurements without profiler tracing, on the
repository's Lean 4.34.0-rc2 toolchain:

| Declaration | Original | Replacement |
| --- | ---: | ---: |
| `native_fast` | 247571 | 24054 |
| `selected_principal` | 367429 | 125519 |

Both replacement proofs pass with the default 200000-heartbeat limit and use
only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
A temporary copy of the complete original module also passes with these proofs
substituted and both heartbeat overrides removed.

Check with:
`lake env lean -DautoImplicit=false -DwarningAsError=true NavierStokes/ActualParticularDynamicsNoOptions.lean`
-/

noncomputable section

namespace NavierStokes.ActualParticularDynamics.NoOptions

open Set Function Filter HarmonicCalculus
open CorrectionInitialization CorrectionState CorrectionStep
open ActualParticularStageControls CommonCoverSolve TorusInverse ParticularWaveBounds ParticularWaveAssembly
open scoped ContDiff Topology InnerProductSpace BigOperators

variable {B N0 : ℕ}

theorem native_fast (x : CycleState (Label B N0)) (l : Label B N0) (n : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2)) :
    (directions (B := B)).fastScale n • (directions (B := B)).fast =
      ((0 : Parameter × ℝ), ParticularWaveBounds.slotDirection ((parameters x l).geometry n)) := by
  have hs : ParticularWaveBounds.slotDirection ((parameters x l).geometry n) =
      CommonBaseContext.fastCoefficient ActualPrimary.h (CommonWindow.index ActualPrimary.h) n •
        ActualPrimary.temporalVector := by
    apply (coverPower (gap l n)).injective
    change coverPower (gap l n)
      (ParticularWaveBounds.slotDirection
        (CopySolveCompatibility.transportGeometry (reference l).geometry (gap l n) 0 _ _)) = _
    conv_lhs => erw [ScaledTangentTransport.slotDirection_transport]
    rw [reference_slotDirection, map_smul,
      show coverPower (gap l n) ActualPrimary.temporalVector =
        ChartScales.Tg ^ gap l n • ActualPrimary.temporalVector from
          CommonBaseContext.coverPower_temporal _, smul_smul, smul_smul]
    change (PhysicalParticularWave.clockWeight ActualPrimary.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand l.2)) *
        ChartScales.timeCoefficient ActualPrimary.h (BaseChartJets.cellBand l.2)) •
        ActualPrimary.temporalVector = _
    congr 1
    rw [← ActualPrimaryDynamics.clockScale_eq]
    unfold CommonBaseContext.fastCoefficient ChartScales.timeCoefficient ActualPrimaryDynamics.clockScale
    have he : CommonWindow.index ActualPrimary.h n + gap l n =
        ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.2) := Nat.add_sub_of_le hi
    rw [← he, pow_add]
    field_simp [(Real.rpow_pos_of_pos (ChartScales.Q_pos (BaseChartJets.cellBand l.2))
      (1+ActualPrimary.h)).ne']
  rw [hs]
  change CommonBaseContext.fastCoefficient ActualPrimary.h (CommonWindow.index ActualPrimary.h) n •
      ((0 : Parameter × ℝ), ActualPrimary.temporalVector) = _
  simp only [Prod.smul_mk, smul_zero]

theorem selected_principal {x : CycleState (Label B N0)} (Hc : PreservesCarriers x)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (Hs : LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
      nativeEnvelope α (currentSource x j))
    (e : ℕ → ActivePair B N0) (q : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ (modalStrip e).domain) (hcell : z ∈ selectedPatch e () q k)
    (hR : 0 < z.1.1.1) (hT : 0 < z.1.1.2.1)
    (hp : (referencePoint (selectedLabel e q) (selectedBand e q) k z).1 ∈
      (PrimaryGeometryAssembly.domain ActualPrimary.nominal (ActualPrimary.choice B N0).prepared.N).carrier
        (selectedLabel e q).2)
    (ht : (referencePoint (selectedLabel e q) (selectedBand e q) k z).2.2 ∈
      Icc 0 ((ActualPrimary.phases B N0 (selectedLabel e q).1).L (selectedLabel e q).2))
    (hc : (referencePoint (selectedLabel e q) (selectedBand e q) k z).2 ∈
      (ActualPrimary.clockWindow (selectedLabel e q).2).core) :
    ((data x (selectedLabel e q) j).raw k).principal
      (ParticularParameters.nativeStrip associatedStrip) (directions (B := B)) (selectedBand e q) z =
        -(data x (selectedLabel e q) j).source (selectedBand e q) z := by
  let hr := (selectedActualControl e x (carrier_frequency Hc) j hj Hs
    ParticularWaveBounds.realPart).pull (fun q => (q, ()))
  let hi := (selectedActualControl e x (carrier_frequency Hc) j hj Hs
    ParticularWaveBounds.imagPart).pull (fun q => (q, ()))
  have hindex := CommonWindow.index_le (h := ActualPrimary.h) (e q).property.2
  have hfreq : (selectedBackground e x j ()).frequency q ≠ 0 := by
    change (data x (selectedLabel e q) j).background.frequency (selectedBand e q) ≠ 0
    rw [data_frequency Hc]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hj)
      (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos ActualPrimary.h (selectedBand e q))).ne'
  have hnormal :
      (selectedBackground e x j ()).normal (modalStrip e) (selectedDirections e) q z =
        (data x (selectedLabel e q) j).background.normal
          (ParticularParameters.nativeStrip associatedStrip) (directions (B := B))
          (selectedBand e q) z := rfl
  have hN : (selectedBackground e x j ()).normal (modalStrip e) (selectedDirections e) q z =
      (selectedTangent e x j () q).normal
        (ParticularWaveBounds.nativePoint (selectedGeometry e () q) k z) := by
    rw [hnormal]
    exact native_normal_match Hc (selectedLabel e q) j hj (selectedBand e q) k
      hindex hR hT hp ht hc
  have hδ : (selectedTangent e x j () q).damping
      (ParticularWaveBounds.nativePoint (selectedGeometry e () q) k z) =
      (modalStrip e).epsilon q * (selectedBackground e x j ()).frequency q ^ 2 *
        ‖(selectedBackground e x j ()).normal (modalStrip e) (selectedDirections e) q z‖ ^ 2 := by
    rw [hnormal]
    exact native_damping_match Hc (selectedLabel e q) j (selectedBand e q) k hindex hR hT hc
  have hfast : (selectedDirections e).fastScale q • (selectedDirections e).fast =
      ((0 : Parameter × ℝ), slotDirection (selectedGeometry e () q)) :=
    native_fast x (selectedLabel e q) (selectedBand e q) hindex
  have hA := native_action_match x (selectedLabel e q) j (selectedBand e q) k hindex hR hT
  have result := NativePrincipalEquations.complexCopyCoefficients_principal_at
    (s := modalStrip e) (dirs := selectedDirections e)
    (frame := fun r => selectedFrame e r) (t := selectedTangent e x j ())
    (source := selectedSource e x j ()) (harmonic := j)
    (g := selectedGeometry e ()) (L := selectedLength e ())
    (envelope := selectedPulseEnvelope e ()) (K := fun r => selectedPatch e () r)
    (selectedBackground e x j ())
    (fun r => ScaledActualParticularControl.length_pos (selectedConstruction e) (selectedClock e) () r)
    hr hi q k hz hcell hfreq hN hδ hfast hA
  exact result


end NavierStokes.ActualParticularDynamics.NoOptions
