# D01 draft B — source-to-target comparison

Target file: `research/D01/DraftB.lean`, namespace `BlowupDensity.D01.DraftB`.
Typechecks with `lake env lean ../research/D01/DraftB.lean` (exit 0, no
diagnostics). Definitions only; no `sorry`, no `axiom`, no `Prop` placeholder
field. Paths are repository-relative; line numbers were read in this worktree.

Conventions fixed once for the whole draft:

* **Fourier.** `ẑ(ξ) = (2π)^{-3/2} ∫ e^{-ix·ξ} z(x) dx` and
  `‖z‖²_{H^s} = ∫ (1+|ξ|²)^s |ẑ|² dξ` (`01-introduction.tex`). This is
  `NSFormalization.Source.angularFourier`
  (`formalization/NSFormalization/Source/FourierConvention.lean:23`), whose
  `angularFourier_eq_integral` is literally the manuscript display, and its
  distributional extension `angularFourierDistribution`
  (`formalization/NSFormalization/Paper3/AngularFourierDilation.lean:172`).
  Every Sobolev object below goes through `angularRealization`
  (`AngularFourierDilation.lean:176`), whose datum norm is the manuscript norm
  (`norm_angularDatum`, `AngularFourierDilation.lean:228`). Mathlib's `𝓕`
  (cycles) is never used as the normalization.
* **Real.** conjugate-reflection symmetry of the datum, i.e.
  `NSFormalization.Source.RealSobolev.realSubspace` (`RealSobolev.lean:118`).
* **Vector.** Euclidean sum of squared component norms, i.e. the `PiLp 2`
  product `NSFormalization.Paper3.RealVectorSobolev`
  (`Paper3/RealVectorPositiveDensity.lean:15`).
* **Time.** force norms on `(0,∞)` via
  `positiveTimeMeasure = volume.restrict (Ioi 0)`
  (`Paper3/PositiveTemporalDensity.lean:11`); velocity norms on `(0,T)`.

## 1. Comparison table

| Paper object | Paper location | Lean term in DraftB | Status | Differences and risks |
|---|---|---|---|---|
| real 3-vector spatial field | `01-introduction.tex` eq:NS | `SpatialField` = `NavierStokes.ProblemStatement.Space → Space` (`vendor/.../NavierStokes/ProblemStatement.lean:30`) | reused-exact | `EuclideanSpace ℝ (Fin 3)`: real Euclidean norm, as required. |
| spacetime vector field | eq:NS | `SpaceTimeField` = `VelocityField` (`ProblemStatement.lean:35`) | reused-exact | Domain is all of `ℝ × R³`; the manuscript's `[0,∞)` / `[0,T)` appears only in set-restricted hypotheses, so a force is a zero-extension, never a partial function. |
| pressure field | `02-preliminaries.tex` §2.3 | `SpaceTimeScalar` = `PressureField` (`ProblemStatement.lean:36`) | reused-exact | — |
| angular Fourier transform | `01-introduction.tex` footnote 1 | `Source.angularFourier`, `Paper3.angularFourierDistribution` | reused-exact | Risk: the *numeric* companions `angularSobolevSq` / `vectorAngularSobolevNorm` are built on the pointwise Bochner `𝓕`, hence faithful only for slices in `L¹∩L²` (compact smooth profiles). For a general `H^∞` slice they can be junk. The draft therefore uses them only in `physicalSobolevNorm` / `physicalBochnerENorm`, never in the definition of `F_R` or of the topology. |
| `H^s(R³)` and its datum | `01-introduction.tex` | `AngularDatum s` = `FourierData`; realization `angularRealization s` | reused-exact | `MemAngularSobolev` = Mathlib `MemSobolev s 2` (`Paper3/AngularSobolevClass.lean:91`); datum unique (`AngularSobolevClass.lean:68`). |
| real scalar `H^s` | `02-preliminaries.tex` §2.2 last sentence | `RealAngularDatum s` = `RealSobolevHilbert s` | reused-exact | Reality is imposed on the *datum*. That the realized distribution is a real-valued function is a consequence, not proved here. |
| real Euclidean vector `H^s` | `01-introduction.tex` ("sum the squared component norms") | `RealVectorAngularDatum s` = `RealVectorSobolev s` | reused-exact | Deliberately **not** `ForceDatum m = Fin 3 → SobolevHilbert m` of `Paper3/AdmissibleForce.lean:16`, whose `Pi` norm is the supremum norm — the gap flagged in the `RealAdmissibleForce` docstring. |
| `‖z‖_{H^s(R³)}`, `‖·‖` for vectors | `01-introduction.tex` | `sobolevENorm`, `vectorSobolevENorm` | new (over reused pieces) | `ℝ≥0∞`-valued and total: `⊤` exactly off `H^s`, else the datum norm (an `iInf` over the — unique — datum). Advantage: no measurability or membership side condition anywhere downstream. Risk: the identity `sobolevENorm s (angularRealization s l) = ‖l‖ₑ` is an obligation (unit **U1**), not a definitional truth. |
| `‖f‖_{L^q(0,∞;H^s)}`, `q ∈ {1,2}` | `01-introduction.tex` eq:time-norms with `I=(0,∞)` | `bochnerSobolevENorm q s`, `l1SobolevENorm`, `l2SobolevENorm` | new | Lower Lebesgue integral of an `ℝ≥0∞` function over `positiveTimeMeasure`, so no strong-measurability hypothesis is needed; it agrees with the Bochner `eLpNorm` only once measurability of `t ↦ vectorSobolevENorm s (g t)` is available (part of **U5**). Only `q ≥ 1` is intended; the definition is literal for any real `q ≠ 0`. |
| slicewise physical `H^s` norm | same | `physicalSobolevNorm` = `Source.vectorAngularSobolevNorm` (`Source/AngularForceNorms.lean:16`), `physicalBochnerENorm` | reused-exact | This is the form in which eq:RpositiveScale / eq:RnegativeScale are already proved (`compact_angular_force_L1_tendsto`, `AngularForceNorms.lean:88`; `_L2_tendsto`, `:98`). Valid for compact smooth families only. |
| `Ḣ^s` realization | `02-preliminaries.tex` eq:homogeneous-realization; `appendix-b-embeddings.tex` proof | `MemHomogeneous s`, `homogeneousENorm s` | new | Encodes `û = |ξ|^{-s} G`, `G ∈ L²`: at `s=-1` literally the displayed set, at `s=a∈(0,3/2)` Appendix B's completion realization. Risks: (a) `‖ξ‖^{-s}` is `Real.rpow`, giving the junk value `0` at `ξ=0` (a null set, harmless in the integral but visible in a pointwise rewrite); (b) integrability of the displayed integral is part of the manuscript's estimate, not a hypothesis of the definition — a non-integrable integrand silently returns `0` in Mathlib; (c) no `L² → 𝓢'` homogeneous multiplier is constructed, matching the explicit refusal in `Paper3/HomogeneousRealization.lean`. |
| `Ḣ^{-1}(R³)` | eq:homogeneous-realization | `MemDotHNegOne` | new | `s = -1` instance of the previous row. |
| `L²(0,∞;Ḣ^{-1})` | `04-whole-space.tex` prop:Renergy | `vectorHomogeneousENorm`, `bochnerHomogeneousENorm`, `forceHomogeneousDistance` | new | Same shape as the inhomogeneous gauge. |
| `H^∞(R³;R³)` | `02-preliminaries.tex` eq:Rinitial | `MemHInfty` | reused-with-adaptation | Field-for-field the hypotheses of `EulerLpTranslation.SmoothL2Field Space` (`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31`). Not literally imported: that module's import closure pulls `Euler.EulerProof` (≈21k lines), which would make the draft unnecessarily expensive to check. Binding is unit **U2**. Risk: `H^∞` = "all integer orders"; smoothness is stated, not derived from Sobolev embedding. |
| `L²_σ(R³)` | eq:Rinitial | `IsSolenoidal` | reused-with-adaptation | Classical pointwise divergence via `spatialDivergence` (`ProblemStatement.lean:67`) applied to the time-independent lift. Risk: the manuscript's `L²_σ` is the closed divergence-free subspace of `L²`; equality with the pointwise condition for `H^∞` fields is unit **U3**. Two other spellings exist in source (`EulerSmoothLimit.divergence`, `Euler/EulerProof.lean:5216`; `divergenceFreeSpace`, `Euler/EulerProof.lean:1340`). |
| `X_R` | eq:Rinitial | `XR` | new | The Fréchet topology on `H^∞` is *not* installed; Theorem 4.1 fixes `a`, so it is not needed. |
| `S_σ` | `04-whole-space.tex` §4.6 | `SchwartzSolenoidal` | new | Uses `SchwartzMap Space Space`. HeliCorgi's `IsR3AdmissibleSchwartzDatum` (`vendor/HeliCorgi/Formal/R3SchwartzInitialData.lean:77`) is the same class in complex frequency coordinates, unimportable (Lean 4.32.1). |
| `F_R` | `02-preliminaries.tex` eq:Rclasses | `ForceR` (physical + data) and `MemForceR` (purely distributional) | reused-with-adaptation | Adapted from `RealAdmissibleForce` (`Paper3/RealAdmissibleForce.lean:15`). Four changes: Euclidean `PiLp 2` data instead of sup-normed `Fin 3 → SobolevHilbert m`; **angular** realization instead of `sobolevRealization`; reality by construction (`RealVectorSobolev`) instead of a separate `realSymmetry` field; a physical `field` is carried so the same object can feed the PDE definitions. No compact support, no vanishing near `t=0` — as the manuscript stresses for the whole-space class. |
| smoothness into each `H^m` with **one-sided** `t=0` derivatives | eq:Rclasses and the sentence after it | `ForceR.datum_contDiffOn : ContDiffOn ℝ ∞ (datum m) (Ici 0)` | reused-exact (idiom of `RealAdmissibleForce`) | Relies on `UniqueDiffOn ℝ (Ici 0)` for the one-sided derivative to be determined; the manuscript's phrase is exactly this. |
| `‖f‖_{L¹_tH^m_x} + ‖f‖_{L²_tH^m_x} < ∞` for every integer `m ≥ 0` | eq:Rclasses | `datum_memL1`, `datum_memL2` | reused-exact | `MemLp _ 1/2 positiveTimeMeasure`, exactly as in `AdmissibleForce`. |
| `F_c` | `04-whole-space.tex` §4.6 | `MemFc` | reused-exact | Uses `NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport` (`vendor/.../NavierStokes/R3/ProblemStatement.lean:66`), i.e. `tsupport f ⊆ Ioi 0 ×ˢ univ`. |
| `F_rd` | §4.6 | `MemFrd` | new | The manuscript's mixed `∂_x^α ∂_t^j` seminorms are replaced by the joint order-`k` `iteratedFDerivWithin` on `futureDomain`. Equivalent, but a translation; a per-`(α,j)` version would need coordinate word derivatives. |
| `E_T` | `01-introduction.tex` eq:Enorm | `energyNormET` | reused-with-adaptation | Same expression as `NSFormalization.Paper1.InsertionEnergy.energyNorm` (`Paper1/InsertionEnergy.lean:30`), rebuilt from the same two reused primitives `NavierStokesR3.CompactEnergy.l2Sq` (`R3/CompactEnergy.lean:190`) and `dissipation` (`:195`). Not imported: `InsertionEnergy`'s closure is 559 project modules. Open interval `(0,T)`, no endpoint value at `T`, as the manuscript requires. |
| classical solution `(u,p)` on `[0,T)` | `02-preliminaries.tex` §2.1, §2.3, prop:local; `appendix-a-local-theory.tex` | `ClassicalSolutionR ν a f T` | new | Compare `NSFormalization.Source.SmoothLifespan.Flow` (`Source/SmoothLifespan.lean:23`): `Flow` demands uniform finite energy and uniform velocity/gradient bounds on compact subintervals, which the manuscript class does **not**; conversely `Flow` lacks the all-order `C_t H^m` regularity and the `∇p ∈ L²` gauge. Risks: (i) one-sided `t=0` regularity is `ContDiffOn` on `Ico 0 T ×ˢ univ` plus `ContinuousOn _ (Ico 0 T)` of the jet paths, so no extension to `t<0` is differentiated; (ii) `[0,T)` versus `[0,T]`: the manuscript's "`C([0,S];H^m)` on each compact interval of the lifespan" is encoded on the half-open interval, which gives every compact subinterval; (iii) the momentum equation is imposed only at interior times `Ioo 0 T`, matching the source convention. |
| pressure determined by its gradient, modulo functions of time; no `p ∈ L²` | `02-preliminaries.tex` §2.3 | `PressureGaugeEquiv`, `pressurePotential`, and `ClassicalSolutionR.pressure_gradient_memLp` | new | No scalar-`L²` field appears anywhere. `pressure_gradient_memLp` is the manuscript's `∇p ∈ L²`, which excludes a nonzero constant pressure gradient and is invariant under `PressureGaugeEquiv`. **Gap:** eq:Rpressure in the `(I−P)` form is *not* defined — that needs the Leray projection on physical fields. It is equivalent to `momentum` given `divergence`; the reusable distributional statement is HeliCorgi `r3HelmholtzPressure_gradient` (`vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean:259`, `∇(pressure F) = -(I−P)F` for arbitrary `L²` source `F`), which cannot be imported (Lean/mathlib 4.32.1 vs 4.34.0-rc2). |
| `T^ν_{max,R}(a,f)` | `02-preliminaries.tex` §2.1 | `maximalLifespanR` | reused-with-adaptation | Same `⨆ S, ⨆ (_ : Nonempty …), ENNReal.ofReal S` shape as `SmoothLifespan.lifespan` (`Source/SmoothLifespan.lean:41`); only the solution class changes, so `lifespan_le_iff` (`:48`), `lifespan_le_iff_no_extension` (`:58`) and `bad_or_regular_reference` (`:70`) transfer verbatim. Risk: this is a supremum of horizons, **not** a chosen maximal solution; identifying it with the manuscript's unique maximal solution needs local uniqueness (task A02). |
| "regular through `T`" | `02-preliminaries.tex` §2.1 | `RegularThrough` | new | `∃ δ>0` with a solution on `[0,T+δ)`, i.e. the manuscript's smooth extension to `[0,T+δ]`; hypothesis of thm:Rinsert. |
| `B^R_{ν,a,T}` | eq:Rsingularforces | `breakdownSetR`, `breakdownSetRZero` | new | A `Set ForceR`, so membership already carries the `F_R` conditions, matching "`{f ∈ F_R : …}`". |
| relative `L^q(0,∞;H^s)` topology and density | `01-introduction.tex` ("relative topology induced by the stated norm"); `04-whole-space.tex` thm:Rmain (i),(ii) | `forceRelativeDistance`, `RelativelyDense`, and `CompletedDense` for prop:Renergy | reused-with-adaptation | Stated in the `ε`-approximation form. For a pseudometric-induced topology this *is* density; the periodic analogue of that equivalence is already proved: `Paper1.ManuscriptTopology.denseAt_iff_approximation` (`Paper1/ManuscriptTopology.lean:176`), with the metric built in `forceEMetric` (`:139`) / `forceMetric` (`:150`) / `relativeTopology` (`:156`). Risk: installing a genuine `MetricSpace ForceR` needs separation (`distance 0 ⇒ equal`), whose periodic analogue is `eq_of_forceDistance_eq_zero` (`:44`); that is unit **U10**, not assumed here. `CompletedDense` is separated out because prop:Renergy asks for density in the *completion*, not relative density. |
| `s_q = 2/q − 3/2`, `β(q,s)` | thm:Rmain; proof of thm:Rinsert | `criticalOrder`, `scalingExponent` (+ two `norm_num` examples) | reused-with-adaptation | Same arithmetic as the registered `BlowupDensity.Contracts.V1.ThresholdAPI.exponent` (`verification/Contracts/V1/Thresholds.lean`); a binding should make `scalingExponent = ThresholdAPI.exponent`. |
| cell-observation map `A_h` | `04-whole-space.tex` §4.8, thm:Rgrid | `cellAverage`, `gridObservation` | reused-with-adaptation | Reuses `NSFormalization.Paper3.CartesianGrid` and `CartesianGrid.cell` (`Paper3/GridGeometry.lean:15,81`). Codomain is the full index family `(Fin 3 → ℤ) → Space`, i.e. the manuscript's `(R³)^{T_h}` with coordinatewise equality; the volume-weighted sequence norm of §4.8 is not defined (not needed by thm:Rgrid). Existing consequences live in `Paper3/ActualGridObservations.lean:22`. |

### Cross-cutting risks

1. **Real vs complex.** All data are complex `L²` with a reality constraint; the
   physical field is real. Every bridge between the two goes through
   `RepresentsSlice`, whose right-hand side `∫ ψ x * ((F x i : ℝ) : ℂ)` is the
   same pairing already proved for compact slices
   (`angularRealVectorSlice_pairing`, `Paper3/AngularRealVectorBochner.lean:54`).
2. **2π conventions.** The inhomogeneous angular and cycles norms are only
   *equivalent*, with constant `(2π)^{|s|}`
   (`angularSobolevSq_equivalence`, `Source/FourierConvention.lean`); the
   homogeneous ones are *equal up to the exact factor* `(2π)^s`. Any estimate
   imported from a cycles-convention lemma must carry one of these two factors.
   The draft never mixes the conventions inside one definition.
3. **`(0,∞)` vs `[0,T)`.** Force norms use `positiveTimeMeasure`; velocity
   norms and the solution class use `Ioo (0,T)` / `Ico 0 T`. `ForceR` conditions
   are stated for `0 ≤ t`, leaving `t<0` unconstrained; two `ForceR` with the
   same nonnegative-time data can differ for `t<0`, so `ForceR` is not extensional.
4. **Distributional vs classical.** `MemForceR` is distributional, `ForceR`
   carries both. `ClassicalSolutionR` is entirely classical (Fréchet
   derivatives), matching `prop:local`; the only distributional objects in the
   solution class are the `L²` jet paths.
5. **Totalized integrals.** `∫`, `∫⁻` and `eLpNorm` are total in Mathlib. Two
   definitions above (`MemHomogeneous`, `pressurePotential`) therefore hide an
   integrability obligation rather than an error.

## 2. Bounded implementation split

Ten lemma-sized units. Each is a candidate obligation field of a registered
`structure … where` V1 contract in the style of
`verification/Contracts/V1/Thresholds.lean`; "binds to" names the existing
declaration that discharges it, "gap" means no source declaration is close.

| # | Obligation (contract field) | Binds to / gap |
|---|---|---|
| **U1** | `sobolevENorm s (angularRealization s l) = ‖l‖ₑ`, and `sobolevENorm s u = ⊤ ↔ ¬ MemAngularSobolev s u`. Makes the `iInf` definition an honest norm. | Binds: `Paper3.angularRealization_injective` (`AngularFourierDilation.lean:203`), `Paper3.MemAngularSobolev.exists_unique_datum` (`AngularSobolevClass.lean:68`), `mem_range_angularRealization_iff` (`AngularSobolevClass.lean:54`). Small, purely order-theoretic. |
| **U2** | `MemHInfty a ↔ ∃ A : SmoothL2Field Space, A.field = a`, plus: for each `m` an angular datum `G` with `RepresentsSlice m G a`. | Binds (⇐/⇒ of the first half): `EulerLpTranslation.SmoothL2Field` (`Euler/LpSmoothField.lean:31`), `Source.FourierPhysicalJets.smoothL2FieldOfFourier` (`:169`), `physicalJetLp_ae` (`:159`). **Gap** for the second half at non-compact `H^∞` data: only `realCompactSobolevTimeSlice` (`Paper3/RealPositiveDensity.lean:54`, compact smooth) currently produces data. |
| **U3** | `IsSolenoidal a ↔ ∀ x, EulerSmoothLimit.divergence a x = 0`, and this implies membership in the `L²` divergence-free subspace. | Binds: `EulerSmoothLimit.divergence` (`Euler/EulerProof.lean:5216`), `divergenceFreeSpace` (`Euler/EulerProof.lean:1340`), `Source.OrdinaryForcedLocal.initial_divergenceFree` (`Source/OrdinaryForcedLocal.lean:18`). The first equivalence is definitional bookkeeping (trace of `fderiv` vs coordinate sum). |
| **U4** | `ForceR` is closed under adding a smooth spacetime-compact real field, and under `+`, `-`, `0`. This is what thm:Rinsert needs for `g_ε = g + H_ε + F_ε ∈ F_R`. | Binds: `Paper3.realAdmissibleForce_add_compact` (`RealAdmissibleForce.lean:99`) and `realAdmissibleForce_add/neg/sub` (`:30`, `:41`, `:49`); the compact datum path is `angularRealVectorSlice` (`AngularRealVectorBochner.lean:47`) with `memLp_angularRealVectorSlice` (`:64`). Adaptation: transport from sup-`Pi` `ForceDatum` to `RealVectorSobolev`, for which `cyclesToAngularRealVector` (`AngularRealVectorBochner.lean:15`) is available. |
| **U5** | For `f,g : ForceR` whose physical difference is `C_c^∞`, `bochnerSobolevENorm q s (f.toDistribution − g.toDistribution) = physicalBochnerENorm q s (f.field − g.field)`; in particular the map `t ↦ vectorSobolevENorm s (…)` is measurable. This is the bridge that lets the *already proved* scaling estimates discharge thm:Rmain's convergence. | Binds: `angularRealVectorSlice_pairing` (`AngularRealVectorBochner.lean:54`), `norm_angularDatum` (`AngularFourierDilation.lean:228`), `vectorAngularSobolevNorm_equivalence` (`Source/AngularForceNorms.lean:19`), then `compact_angular_force_L1_tendsto` (`:88`) and `compact_angular_force_L2_tendsto` (`:98`). |
| **U6** | `homogeneousENorm s` is attained and finite exactly on `MemHomogeneous s`, and the correspondence `G ↦ u` is injective (no polynomial ambiguity) — the content of eq:homogeneous-realization. | Partially binds: `Source.FractionalRealization.realization_toDistribution` (`Source/FractionalRealization.lean:78`) and `realization_norm_le_datum` (`:96`); `Paper3.compact_homogeneous_norm_bound` (`Paper3/HomogeneousRealization.lean:17`) for finiteness on compact inputs. **Gap:** the completed `L² → 𝓢'` homogeneous multiplier is deliberately absent from `HomogeneousRealization.lean`; `‖ξ‖` is not `HasTemperateGrowth` (not `ContDiff` at `0`), so `TemperedDistribution.smulLeftCLM` cannot be used directly. |
| **U7** | `homogeneousENorm s u = ENNReal.ofReal (frequencyUnit ^ s * Source.homogeneousFourierNorm s f)` for smooth compact `f`. The exact `(2π)^s` factor between the two homogeneous conventions. | Binds: `Source.homogeneousFourierNorm` (`Source/TimeNormScaling.lean:68`), `frequencyUnit` (`Source/FourierConvention.lean:15`), and the dilation/Jacobian computation of `angularSobolevSq_eq_frequency_weight` (`Source/FourierConvention.lean:50`). Pure change of variables; no analysis. |
| **U8** | Pressure package: (a) `PressureGaugeEquiv` preserves `ClassicalSolutionR`; (b) `pressurePotential G` has gradient `G` when `∂_j G_k = ∂_k G_j`; (c) eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` ⟺ `momentum` given `divergence`. | (a),(b) are self-contained calculus (the manuscript's own two-line argument). (c) **gap**: needs the Leray complement on physical fields. Reusable at the distributional level: HeliCorgi `r3HelmholtzPressure_gradient` (`vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean:259`) and `r3LerayComplementL2` (`:228`) — blocked on toolchain task U05. |
| **U9** | Lifespan interface for `ClassicalSolutionR`: restriction to shorter horizons; `maximalLifespanR ν a f ≤ ofReal T ↔ ∀ S, T < S → IsEmpty (ClassicalSolutionR ν a f S)`; the two-case alternative "breaks down by `T`, or is regular through `T`". | Binds by direct transcription: `SmoothLifespan.Flow.restrict` (`Source/SmoothLifespan.lean:83`), `lifespan_le_iff` (`:48`), `lifespan_le_iff_no_extension` (`:58`), `bad_or_regular_reference` (`:70`), `lifespan_eq_of_forall_shorter_of_upper_bound` (`:124`). Only the structure changes; all proofs are order-theoretic. |
| **U10** | `forceRelativeDistance q s` is a pseudometric on `ForceR`, is separating, and `RelativelyDense q s S ↔ Dense S` in the induced topology. | Binds by analogy: `Paper1.ManuscriptTopology.forceEMetric` (`Paper1/ManuscriptTopology.lean:139`), `forceMetric` (`:150`), `relativeTopology` (`:156`), `DenseAt` (`:161`), `denseAt_iff_approximation` (`:176`). **Gap:** separation on `R³` — the periodic proof `eq_of_forceDistance_eq_zero` (`:44`) uses periodic Fourier uniqueness and must be redone with `angularRealization_injective`; also `ForceR` is not extensional in `t<0`, so the quotient must be by nonnegative-time equality. |

### Not covered by these ten units (deliberately out of D01 scope)

* Local existence / uniqueness / continuation for `ClassicalSolutionR`
  (tasks A01, A02, A04): the draft defines the class, never asserts it is
  nonempty.
* Critical embeddings and the `L¹`/`L²` regularity balls (A05, R43, R44).
* The insertion family itself (I02, I03, R42).
