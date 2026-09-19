# Lane 485 attempts

Dependency closure built successfully before proof development (10087 jobs).
The path-infimum / slice-integral distinction is retained; no equality is assumed.

## A1: norm coercion
```text
NormBridge.lean:38:5: error(lean.unknownIdentifier): Unknown identifier `enorm_le_enorm`
```
Use explicit nnnorm / ENNReal coercion instead.

## A2: coercion lemma names
```text
NormBridge.lean:39:55: error(lean.unknownIdentifier): Unknown identifier `nnnorm_le_nnnorm_iff`
NormBridge.lean:39:6: error: Type mismatch: After simplification, term
  Section4.R41.lowerVectorL_norm_le r s hsr A
 has type
  ‖(lowerVectorL r s hsr) A‖ ≤ ‖A‖
but is expected to have type
  ‖(lowerVectorL r s hsr) A‖₊ ≤ ‖A‖₊
```
Resolved with `enorm_le_iff_norm_le.mpr`. A discovery probe also reported:
```text
Unknown identifier `enorm_eq_ofReal`
Unknown constant `ENNReal.lintegral_add_le`
Unknown identifier `MeasureTheory.lintegral_add_le`
```
The triangle proof uses measurable paths and `eLpNorm_add_le` instead.

## A3: inferred infimum witness timed out
```text
NormBridge.lean:25:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```
Resolved without raising heartbeats: give the intermediate norm inequality and
infimum binder explicit types. The preceding checkpoint contained this failure;
the next commit repairs it and the declaration checks with zero output.

## A4: quotient realization spelling
```text
NormBridge.lean:51:93: error: unsolved goals
Ω : Set Space
s r : ℝ
hsr : s ≤ r
z : T22.DomainFunctional Ω
A : Paper3.RealVectorSobolev r
hA : T22.restrictDatum Ω r A = z
i : Fin 3
ψ : T22.DomainTest Ω
⊢ ((Paper3.angularRealization r)
        ↑(↑(ContinuousLinearMap.proj i ∘SL
                ↑(PiLp.continuousLinearEquiv 2 ℝ fun x => ↥(Source.RealSobolev.RealSobolevHilbert r)))
            A))
      ↑ψ =
    T22.restrictDatum Ω r A i ψ
```
The residual is definitional; `rfl` closes it.

## A5: addition-side convention
```text
Rates.lean:58:30: error: Application type mismatch: The argument
  add_le_add_left (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (LT.lt.le hε.left) ?m.249)) ?m.250
has type
  C * ε ^ ?m.249 + ?m.250 ≤ max C 0 * ε ^ ?m.249 + ?m.250
but is expected to have type
  (M + E) * ε ^ (1 / 2) + C * ε ^ (3 / 2) ≤ (M + E) * ε ^ (1 / 2) + energyConst C * ε ^ (3 / 2)
in the application
  ENNReal.ofReal_le_ofReal
    (add_le_add_left (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (LT.lt.le hε.left) ?m.249)) ?m.250)
```
Resolved with `add_le_add le_rfl`.

## A6: slice unification needs the spacetime lambda
```text
../formalization/NSFormalization/Section3/T23/Rates.lean:117:2: error: Tactic `apply` failed: could not unify the conclusion of `LE.le.trans
  (lintegral_sobolevENorm_le_forceSobolevENorm s ?m.438)`
  (∫⁻ (t : ℝ) in Ioi 0, Section4.D01.sobolevENorm s fun x => ?m.438 (t, x)) ≤ ?m.443
with the goal
  (∫⁻ (t : ℝ) in Ioi 0, Section4.D01.sobolevENorm s fun x => H (t, x) + F (t, x)) ≤
    ENNReal.ofReal ((2 * (|A| + |B|) + 1) * (ε ^ (1 / 2 - s) + ε ^ (3 / 2 - s)))

Note: The full type of `LE.le.trans (lintegral_sobolevENorm_le_forceSobolevENorm s ?m.438)` is
  Section4.D01.forceSobolevENorm 1 s ?m.438 ≤ ?m.443 →
    (∫⁻ (t : ℝ) in Ioi 0, Section4.D01.sobolevENorm s fun x => ?m.438 (t, x)) ≤ ?m.443

s ε A B : ℝ
hs : 0 ≤ s
hε : 0 < ε
hε1 : ε ≤ 1
F H : VelocityField
hF : ∀ (t : ℝ), 0 ≤ t → Continuous fun x => F (t, x)
hH : ∀ (t : ℝ), 0 ≤ t → Continuous fun x => H (t, x)
hpacket : Section4.D01.forceSobolevENorm 1 s F ≤ ENNReal.ofReal (A * (ε ^ (1 / 2) + ε ^ (1 / 2 - s)))
hcorr : Section4.D01.forceSobolevENorm 1 s H ≤ ENNReal.ofReal (B * (ε ^ (3 / 2) + ε ^ (3 / 2 - s)))
hA : 0 ≤ max A 0 * (ε ^ (1 / 2) + ε ^ (1 / 2 - s))
hB : 0 ≤ max B 0 * (ε ^ (3 / 2) + ε ^ (3 / 2 - s))
hp : Section4.D01.forceSobolevENorm 1 s F ≤ ENNReal.ofReal (max A 0 * (ε ^ (1 / 2) + ε ^ (1 / 2 - s)))
hc : Section4.D01.forceSobolevENorm 1 s H ≤ ENNReal.ofReal (max B 0 * (ε ^ (3 / 2) + ε ^ (3 / 2 - s)))
⊢ (∫⁻ (t : ℝ) in Ioi 0, Section4.D01.sobolevENorm s fun x => H (t, x) + F (t, x)) ≤
    ENNReal.ofReal ((2 * (|A| + |B|) + 1) * (ε ^ (1 / 2 - s) + ε ^ (3 / 2 - s)))
```
Resolved by passing `(fun z => H z + F z)` explicitly.

## A7: probe imports and overlapping namespaces
```text
../research/T23/probes/T23-U6-rates-convergence_closes.lean:72:22: error: Function expected at
  PacketImportAPI
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  ν

Hint: The identifier `PacketImportAPI` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T23/probes/T23-U6-rates-convergence_closes.lean:74:11: error: Ambiguous term
  Space
Possible interpretations:
  BlowupDensity.Contracts.V1.Space : Type
  
  NavierStokes.ProblemStatement.Space : Type
../research/T23/probes/T23-U6-rates-convergence_closes.lean:74:23: error: Ambiguous term
  Space
Possible interpretations:
  BlowupDensity.Contracts.V1.Space : Type
  
  NavierStokes.ProblemStatement.Space : Type
../research/T23/probes/T23-U6-rates-convergence_closes.lean:74:31: error: Ambiguous term
  Space
Possible interpretations:
  BlowupDensity.Contracts.V1.Space : Type
  
  NavierStokes.ProblemStatement.Space : Type
../research/T23/probes/T23-U6-rates-convergence_closes.lean:74:43: error: Ambiguous term
  VelocityField
Possible interpretations:
  BlowupDensity.Contracts.V1.VelocityField : Type
  
  NavierStokes.ProblemStatement.VelocityField : Type
../research/T23/probes/T23-U6-rates-convergence_closes.lean:80:0: warning: declaration uses `sorry`
../research/T23/probes/T23-U6-rates-convergence_closes.lean:83:0: warning: declaration uses `sorry`
../research/T23/probes/T23-U6-rates-convergence_closes.lean:86:0: warning: declaration uses `sorry`
../research/T23/probes/T23-U6-rates-convergence_closes.lean:89:24: error: Ambiguous term
  VelocityField
Possible interpretations:
  BlowupDensity.Contracts.V1.VelocityField : Type
  
  NavierStokes.ProblemStatement.VelocityField : Type
```
Add PacketImport and open only the three needed contract types.
