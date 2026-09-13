# I03 review — lane 015, "Same-family scaling and negative norms"

Reviewer pass over `research/I03/Spec.lean` (486 lines, 46 fields) and
`research/I03/COMPARISON.md`. Nothing in this lane was modified.

## Verdict: ACCEPT-WITH-NOTES

The file typechecks clean and is hygienic. Every exponent in the 46 fields is
written through `ThresholdAPI.exponent` and matches Theorem 4.2's displays; the
negative-order homogeneous claim is correctly confined to `-3/2 < s < 0`; the
`E_T` and mixed-norm fields are equalities exactly where the paper writes
equalities; the single-`ε₀`/single-family discipline is real. Every one of the
24 source lines the draft cites is correct and no source claim is overstated;
the five `rfl` bridges re-run green. One genuine defect (issue 1) and four
low-severity fidelity notes. No re-work required.

## Ranked issues

| # | Sev | Field / location | Paper location | What differs | One-line fix |
|---|---|---|---|---|---|
| 1 | **HIGH** | `scalingStatement`, `Spec.lean:478-484` | `04-whole-space.tex:44-55` | **Unsatisfiable, not merely loose.** It quantifies over *arbitrary* `w H : ℝ → VelocityField` and demands `∃ A : ScalingAPI` with `A.correction = w`, `A.forceCorrection = H`. `ScalingAPI` then forces `correction_smooth`, `correction_compactSupport`, `correctionEnergyBound ≤ Cε^{3/2}`, `correctionPositive/NegativeScaling` on `Ioc 0 ε₀`, which is nonempty by `eps_pos`. Take `w` non-smooth, or `w ε ≡ w₀ ≠ 0`: no `A` exists. In the paper `w_ε, H_ε` are Lemma 3.4/3.5 objects, never arbitrary. `COMPARISON.md` row 48 flags only the `HEq`, not this. | Replace `(w H : ℝ → VelocityField)` with a `CorrectionAPI` premise (see below), or add its conclusions as explicit hypotheses of `scalingStatement`. |
| 2 | MED | `forceLowOrderBound`, `Spec.lean:431-439` | `04-whole-space.tex:78` | The docstring quotes the paper's `q=1` route ("all `s<0` follow from `‖z‖_{H^s} ≤ ‖z‖₂`", i.e. index `r=0`, eq:RpositiveScale constants) but the field forces `r < 0` and states both conclusions with `negativeConst` / `correctionNegativeConst` (eq:RnegativeScale constants) for `q=1` too. Still true and derivable (any `r ∈ (-3/2,0)` with `r ≥ s` works, via `packetNegativeScaling`), just not the paper's argument at `q=1`. | Reword the docstring to say the field uses the uniform intermediate-index route for both `q`, or relax `r < 0` to `r ≤ 0` and branch the constants. |
| 3 | LOW | `packetMixedScaling`, `Spec.lean:315` | eq:packetFscale, `03-torus.tex:132` ("for `1 ≤ p,q ≤ ∞`") | Only `p` is constrained (`[Fact (1 ≤ p)]`, required by `Data.mixedLebesgueENorm`); `q` is unconstrained, so `q < 1` is admitted. | Add `1 ≤ q →`. |
| 4 | LOW | `packet/correctionPositiveScaling`, `packet/correctionNegative*`, `Spec.lean:329,344,371,380,392,400` | eq:RpositiveScale / eq:RnegativeScale, `:64-76` | Quantified over all `q : ℝ≥0∞` with `1 ≤ q`, including `q = ⊤` (`q.toReal = 0`, exponent `-3/2-s`); the paper's displays live in the `q ∈ {1,2}` context. True by scaling and matched by source (`force_eLpNorm_{positive,negative}_epsilon` take any `q : ℝ≥0∞`), so a harmless strengthening. | None; note it in the docstring. |
| 5 | LOW | `x₀`, `r`, `Spec.lean:188-198` | `03-torus.tex:103`, `04-whole-space.tex:33` | The paper fixes a ball `B` first and then `x₀ ∈ B`; the spec makes `x₀` the *centre* of `B = ball x₀ r`. Standard WLOG (and the same convention as `Source.exists_local_approximating_insertion`), but nothing records that `ball x₀ r` sits inside the originally given ball, so R42 must do the shrink silently. | One clause in the `r` docstring, or a field `Metric.ball x₀ r ⊆ B₀`. |
| 6 | INFO | `positiveConst`, `negativeConst`, `correctionPositiveConst`, `correctionNegativeConst` | `:66,68,74,75` | No nonnegativity fields, unlike `correctionEnergyConst_nonneg`. Harmless (`ENNReal.ofReal` of a negative is `0`, which only strengthens the obligation) but asymmetric. | Optional. |

Not issues, checked and correct: `eps_time` = `2ε² < min(T,δ)` is genuinely
`03-torus.tex:212` (the bare `2ε² < T` at `:105` is the weaker Section-3
version); `carrierRadius`/`carrier_subset`/`force_carrier_subset` transcribe
`K_*` at `:101-102`; `eq:REclose` reuses *the same* `M`, `D`
(`packet.energyBound/dissipationBound`) and *the same* `C`
(`correctionEnergyConst`) as `eq:packetEscale` and `eq:wE`;
`correctionPositiveScaling`'s exponents `β(q,0)+1 = 2/q-1/2` and `β(q,s)+1`
reproduce eq:RpositiveScale line 2 and, at `q=1`, eq:HHs `C(ε^{3/2}+ε^{3/2-s})`
exactly; `forceLowOrderBound`'s witness is available from
`ThresholdAPI.negativeIndex` for `s < -1/2` and from `r := s` for `-3/2 < s`.

## Source spot-check (all lines opened; all correct)

| Cited | Declaration | Draft's claim | Verdict |
|---|---|---|---|
| `Source/TimeNormScaling.lean:117` | `force_eLpNorm_positive_epsilon` | all `s ≥ 0`, any `q : ℝ≥0∞`, `0 < ε ≤ 1`, exponent `2/q.toReal - 3/2 - s` | correct; single-term, so it implies the paper's two-term bound for `ε ≤ 1` |
| `:133` | `force_eLpNorm_negative_epsilon` | `s ≤ 0`, any `q`, any `ε > 0`, same exponent, RHS `homogeneousFourierNorm` of the **profile** | correct |
| `Paper3/HomogeneousTime.lean:14` | `homogeneous_energy_le_bound_add_L2` | `-3/2 < s ≤ 0`, the paper's `|ξ|<1` / `|ξ|≥1` split | correct |
| `:82` | `uniform_homogeneousFourier_time` | uniform profile bound on `-3/2 < s ≤ 0` | correct |
| `:108` | `memLp_homogeneousFourier_time` | every `q` incl. `1, 2, ⊤` | correct |
| `Paper1/CorrectionVectorNorms.lean:60` | `vectorPhysicalForce_uniform_positive_time` | `0 ≤ s ≤ 1`, `1 ≤ q`, `ε ∈ Ioc 0 1`, exponent `2/q-1/2-s = β(q,s)+1` | correct, exact match |
| `:83` | `vectorPhysicalForce_uniform_negative_time` | `-3/2 < s ≤ 0`, `1 ≤ q`, same exponent | correct |
| `:134` | `scalarPhysicalForce_all_negative_tendsto_zero` | lowers to the **fixed** `r = -1` | correct (`(s := -1)` in the proof); hypotheses `s ≤ 0`, `0 < β(q,s)+1` |
| `:155` | `vectorPhysicalForce_all_negative_tendsto_zero` | vector version | correct |
| `Paper3/Thresholds.lean:28` | `negative_intermediate_index` | `s < -1/2 → ∃ r, -3/2 < r < -1/2 ∧ s < r` | correct; literally `ThresholdAPI.negativeIndex` |
| `Source/CompactForceConvergence.lean:36` | `fourierSobolevNorm_mono_of_compact` | slicewise monotonicity in `s` | correct |
| `:44` | `scalar_force_eLpNorm_mono` | time-`L^q` version | correct |
| `:98` | `compact_scalar_force_L2_tendsto` | all `s < -1/2`, `s ≤ -3/2` included, via `negative_intermediate_index` | correct |
| `:123` | `compact_vector_force_L2_tendsto` | vector version, moving centres | correct |
| `Source/InsertionForceConvergence.lean:66` | `force_angular_L1_tendsto_zero` | `s < 1/2`, whole `H_ε + F_ε`, one family, angular | correct |
| `:78` | `force_angular_L2_tendsto_zero` | `s < -1/2`, same | correct |
| `Source/LocalApproximatingInsertion.lean:86` | `exists_local_approximating_insertion` | one `ε₀` carrying `ForceApproximation`, `EnergyApproximation`, per-`ε` `InsertionProperties` and `AdmissibleCompactForce` | correct (body runs to `:103`) |
| `Source/PacketScaling.lean:37` | `l2Sq_parabolic` | exact slicewise `l2Sq` identity | correct |
| `:78` | `total_dissipation_parabolic` | exact total dissipation identity | correct |
| `:100` | `l2Norm_parabolic` | its square root | correct |
| `:552` | `parabolicForce_positive_support` | positive-time compact support after delay | correct |
| `Paper1/InsertionEnergy.lean:228` | `packet_gradientSquare` | `gradientSquare T U_ε = ε · gradientSquare 1 u`, an **equality** | correct |
| `Source/AngularForceNorms.lean:19` | `vectorAngularSobolevNorm_equivalence` | two-sided, constant `frequencyUnit^{|s|}` | correct; `frequencyUnit = 2π` (`FourierConvention.lean:15`) |
| `:37` | `eLpNorm_angular_le` | one-sided `L^q` version, same constant | correct |

**"Is that really the angular convention?" — yes.** `vectorAngularSobolevNorm`
(`AngularForceNorms.lean:16`) is built on `angularSobolevSq`
(`FourierConvention.lean:44`) over `angularFourier` (`:23`), and
`angularFourier_eq_integral` (`:29`) proves it *is*
`(2π)^{-3/2}∫exp(-i x·ξ)f(x)dx`, the manuscript's normalization. Caveat the
draft already states: the time norm there is over all of `ℝ` and the object is
a slicewise integral, **not** `Data.forceSobolevENorm`'s datum-path infimum.

`rfl` bridges re-run in `/tmp/i03_rfl_review.lean` (deleted after): all five
succeeded, plus `@Contracts.V1.zeroPastField = @Source.PacketScaling.zeroPastField`
(identical bodies).

## Gaps

* **No source bounds the homogeneous norm of a scaled field — confirmed.**
  `grep -rn 'homogeneousFourierNorm'` over `formalization/` hits six files; the
  only occurrence near `parabolic`/`concentrated` is `TimeNormScaling.lean:111`,
  inside `force_eLpNorm_negative`, and there the homogeneous norm is on the
  **profile** while the scaled field carries the *inhomogeneous* norm.
  `Data.forceHomogeneousENorm` / `IsHomogeneousDatum` have **zero** users
  outside `Contracts/V1/Data.lean`. Since `forceHomogeneousENorm` is an
  infimum, `⨅ ∅ = ⊤`: `packetNegativeHomogeneous` and
  `correctionNegativeHomogeneous` are *unprovable* until a witness is built.
  Draft's gap claim is exactly right.
* **eq:packetEscale's `L^∞L²` clause is an inequality in source — confirmed.**
  `PacketScaling.uniform_l2Norm_parabolic:118` gives only
  `√(l2Sq U_ε t) ≤ √(k⁻¹)·N` for an arbitrary uniform bound `N`; the packet-side
  `InsertionEnergy.packet_l2_bound:203` is likewise `≤ ε·E`. The paper's
  equality with the **least upper bound** `M` needs `PacketAPI.energy_isLUB`,
  which nothing currently consumes. Draft says this.
* **U7 is under-sized at "L".** (a) the homogeneous change of variables is
  *easier* than its inhomogeneous twin `fourierSobolevSq_concentrated:51`
  (the weight is exactly homogeneous, and `negative_weight_scale` is already
  there) — S. (b) mirrors `force_eLpNorm_negative_epsilon` — S. (c) is not a
  "lift": the inhomogeneous analogue is the whole 143-line
  `Paper3/AngularRealVectorBochner.lean` with a `RealVectorSobolev s ≃L[ℝ] …`
  construction, and the homogeneous side has **no** counterpart —
  `Paper3/HomogeneousRealization.lean` is 26 lines with one bound and produces
  no `IsHomogeneousDatum`. U7(c) alone is a new Paper3 module, not a unit
  within one. Recommend splitting U7 into U7a/b (S) and U7c (L, own module),
  and noting that R46's `L²_tḢ^{-1}` clause blocks on U7c specifically.

## Recommendations

**Family threading: `I03` should take a `CorrectionAPI` as a field.** The draft
*does* correctly flag the `ScalingAPI.ε₀` vs `CorrectionAPI.ε₀` problem
(§2.3, open question 2) and correctly says the contract as written cannot force
`A.ε₀ = C.ε₀`. But issue 1 above upgrades that open question to a defect: the
six restated `correction*`/`forceCorrection*` fields are precisely what makes
`scalingStatement` unsatisfiable. Taking `corrections : CorrectionAPI` (a) fixes
that, (b) deletes six duplicated fields and the `correctionEnergyBound`
restatement, (c) makes the threading structural rather than an R42 obligation
nothing can enforce. Pin the scale with `ε₀ ≤ corrections.ε₀` (not equality —
I03 legitimately may shrink) plus `x₀`, `r`, `carrierRadius = θRadius`
equations. Cost: `research/I02/Spec.lean` must become a registered module. If
that registration is blocked this cycle, the minimum fix is to add I02's
conclusions as hypotheses of `scalingStatement`, which is what R42 would have
to supply anyway — leaving it as an equation for R42 is the one option to
reject, since it leaves a false Prop in the file.

**Prop 3.3 transport (equation / divergence-free / blowup of the rescaled
fields): give it to `I03`, not `R42`.** The paper puts it in `prop:scaling`
(`03-torus.tex:122-131`) together with eq:packetEscale and eq:packetFscale,
which `ScalingAPI` already owns — owning half of one proposition and orphaning
the other half is the reason it is currently unowned by any contract. I03
already carries `packet : PacketAPI ν` and the three `scaled*` defs, so the
statement needs no new data; R42 would have to re-derive them. It is fully
proved in source (`ParabolicScaling.parabolic_equation:112`,
`PacketScaling.delayed_parabolic_equation:489`, `delayed_parabolic_divergence:506`,
`speed_unbounded_parabolic:147`), so it is an S-sized addendum record.
R42 then consumes it instead of re-proving it.

## Check log

```
$ cd WT/verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 \
    lake env lean ../research/I03/Spec.lean
(no output)                                              EXIT=0   1.99s user
$ grep -nE 'sorry|axiom|admit|native_decide|unsafe' research/I03/Spec.lean
13:  ... introduces no `axiom`, no `sorry` ...           # prose only
$ grep -cE '^  <field> :' Spec.lean:165-452  ->  46      # matches the brief
```
Theorem-like declarations: **none** — 4 plain `def`s, `structure ScalingAPI`
(46 fields), 4 projection `def`s, `def scalingStatement : Prop`. No `theorem`,
`lemma`, `example`, `instance`, `axiom`, `opaque`. Header's claim holds.
`rfl` bridges: `lake env lean /tmp/i03_rfl_review.lean` → EXIT=0; file deleted.

Not verified (out of the brief): the `Bindings`/`contracts.json` registration of
`ScalingAPI`; `research/I02/Spec.lean`'s own fidelity; source declarations the
draft cites but the brief did not list (e.g. `MixedForceScaling.lean:12,62`,
`VectorForceNorms.lean:47,79`, `ForceNormAddition.lean:31`).
