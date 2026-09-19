# Lane 467 — U-CAN and Ub1–Ub3

## Construction

Canonical `MultipleRegionsAPI` copies all 30 Spec fields, changing only packet
projections to raw parameters and resolving canonical T10/T13/T15 vocabulary.
`multipleRegionsStatement` carries T15's complete raw-clause antecedent.
`RegionsData` consumes exactly lane 459's sixteen clauses: the eight I03
`PacketData` clauses and pressure support/extension smoothness, force smoothness,
positive compact support/nonpositive-time zero, extended momentum/divergence,
and speed blowup. The probe constructs it from any registered imported packet.
No T18 import or hypothesis is used.

For region j, reuse `placementCarrier K f` and its positive norm bound R.
Choose x₀ = chartCenter = regionCenter j, chartRadius = regionRadius j and
ε₀ = min (min (1/2) (T/4)) (regionRadius j / (2*(R+1))).
Then ε ≤ ε₀ implies ε‖y‖ ≤ εR < regionRadius j and 2ε² < T.
Choose ε j = ε₀, construct the full T15 scaling API, and choose its solution.
The single-copy identities and T15's slice topological-support inclusions
prove both requested zero statements. Force time is unrestricted; velocity
time is exactly Ico 0 T.

## Failed approaches (resolved)

The exact diagnostics below are retained, including downstream elaboration
errors caused by the first failure in a run.

1. Grouped structure fields `M E : ℝ` are parsed as a field with a binder,
not two real fields. Split them into separate lines.
2. The copied time proof needed `hε.1` explicitly supplied to `nlinarith`.
`rw` also did not match definitionally equal horizons; rewrite
`placement_time` in a typed single-copy equality first.
3. Applying `image_eq_zero_of_notMem_tsupport` inferred the spacetime support.
Use `by_contra` and explicitly apply `subset_tsupport` to the spatial slice.
4. Opening both registered and vendor problem namespaces made `Space`
ambiguous in the probe. Retain only the registered namespace.

### Run 1

```text
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:22:55: error: Application type mismatch: The argument
  M
has type
  ?m.1 → ℝ
but is expected to have type
  ℝ
in the application
  Section4.I03.PacketData u K M
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:51:23: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:51:44: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:51:48: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:51:52: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:51:56: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:52:7: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:53:14: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:54:17: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:55:17: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:56:21: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:57:23: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:58:8: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:59:34: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:60:28: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:60:32: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:61:44: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:61:69: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:64:26: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:65:5: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:65:46: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:65:71: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:67:32: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:67:57: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:66:13: error: unsolved goals
RegionsData : Sort ?u.2
d : RegionsData
j : Fin sorry
⊢ 0 < min (min (1 / 2) (sorry / 4)) (sorry / (2 * (placementRadius ⋯ ⋯ + 1)))
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:75:18: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:76:4: error: linarith failed to find a contradiction
RegionsData : Sort ?u.2
d : RegionsData
j : Fin sorry
ε : ℝ
hε : ε ∈ Ioc 0 (min (min (1 / 2) (sorry / 4)) (sorry / (2 * (placementRadius ⋯ ⋯ + 1))))
he : ε ≤ 1 / 2
ht : ε ≤ sorry / 4
a✝ : sorry ≤ 2 * ε ^ 2
⊢ False
failed
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:77:15: error: unsolved goals
RegionsData : Sort ?u.2
d : RegionsData
j : Fin sorry
ε : ℝ
hε : ε ∈ Ioc 0 (min (min (1 / 2) (sorry / 4)) (sorry / (2 * (placementRadius ⋯ ⋯ + 1))))
y : Space
hy : y ∈ placementCarrier sorry sorry
⊢ |ε| * ‖y‖ < sorry
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:90:50: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:90:31: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:94:34: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:95:34: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:94:5: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:95:5: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:98:21: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:98:45: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:98:50: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:98:54: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:98:58: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:98:62: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:98:66: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:98:70: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:98:75: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:99:13: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:99:22: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:99:41: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:99:59: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:100:4: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:100:20: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:100:33: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:100:44: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:100:57: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:100:67: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:103:15: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:103:28: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:106:30: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:106:51: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:107:13: error(lean.unknownIdentifier): Unknown identifier `d.placement`
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:110:24: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:110:36: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:112:13: error(lean.unknownIdentifier): Unknown identifier `d.placement`
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:110:43: error: unsolved goals
j : ?m.2
⊢ sorry ^ 2 < sorry
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:118:23: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:118:49: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:119:27: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:119:50: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:119:55: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:119:63: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:119:32: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:120:21: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:124:56: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:124:79: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:124:84: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:125:56: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:125:79: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:125:84: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:124:5: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:124:61: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:125:5: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:125:61: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:126:35: error(lean.unknownIdentifier): Unknown identifier `d.scaling`
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:129:51: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:130:21: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:130:40: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:130:61: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:143:21: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:143:40: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:144:28: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:144:51: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:144:56: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:144:33: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  d
has type `RegionsData` which does not have the necessary form.
```

### Run 2

```text
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:77:4: error: linarith failed to find a contradiction
d : RegionsData
j : Fin d.N
ε : ℝ
hε : ε ∈ Ioc 0 (min (min (1 / 2) (d.T / 4)) (d.regionRadius j / (2 * (placementRadius ⋯ ⋯ + 1))))
he : ε ≤ 1 / 2
ht : ε ≤ d.T / 4
a✝ : d.T ≤ 2 * ε ^ 2
⊢ False
failed
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:133:4: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  periodizedScaledVelocity d.u (d.placement j).x₀ (d.placement j).T (d.ε j) (t, x)
in the target expression
  periodizedScaledVelocity d.u (d.placement j).x₀ d.T (d.ε j) (t, x) = 0

d : RegionsData
j : Fin d.N
t : ℝ
ht : t ∈ Ico 0 d.T
x : Space
hx : x ∈ fundamentalCube
hout : x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j)
⊢ periodizedScaledVelocity d.u (d.placement j).x₀ d.T (d.ε j) (t, x) = 0
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:146:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  periodizedScaledForce d.f (d.placement j).x₀ (d.placement j).T (d.ε j) (t, x)
in the target expression
  periodizedScaledForce d.f (d.placement j).x₀ d.T (d.ε j) (t, x) = 0

d : RegionsData
j : Fin d.N
t : ℝ
x : Space
hx : x ∈ fundamentalCube
hout : x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j)
⊢ periodizedScaledForce d.f (d.placement j).x₀ d.T (d.ε j) (t, x) = 0
```

### Run 3

```text
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:141:59: error: Application type mismatch: The argument
  hs
has type
  (t, x) ∈ tsupport (scaledVelocity d.u (d.placement j).x₀ d.T (d.ε j))
but is expected to have type
  x ∈ tsupport fun x => scaledVelocity d.u (d.placement j).x₀ d.T (d.ε j) (t, x)
in the application
  scaledVelocity_tsupp_subset (eps_admissible d j).left d.packet.carrier_compact d.packet.support
    (d.placement j).carrier_subset ht.right hs
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:156:64: error: Application type mismatch: The argument
  hs
has type
  (t, x) ∈ tsupport (scaledForce d.f (d.placement j).x₀ d.T (d.ε j))
but is expected to have type
  x ∈ tsupport fun x => scaledForce d.f (d.placement j).x₀ ?m.70 (d.ε j) (t, x)
in the application
  scaledForce_tsupp_subset (eps_admissible d j).left (d.placement j).Kstar_compact d.force_support
    (d.placement j).force_projection_subset t hs
../formalization/NSFormalization/Section3/T24/MultipleComponents.lean:146:77: error: unsolved goals
d : RegionsData
j : Fin d.N
t : ℝ
x : Space
hx : x ∈ fundamentalCube
hout : x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j)
hcopy :
  periodizedScaledForce d.f (d.placement j).x₀ d.T (d.ε j) (t, x) =
    scaledForce d.f (d.placement j).x₀ d.T (d.ε j) (t, x)
hs : (t, x) ∈ tsupport (scaledForce d.f (d.placement j).x₀ d.T (d.ε j))
⊢ x ∈ Metric.ball (d.regionCenter j) (d.regionRadius j)
```

### Run 4

```text
../research/T24/probes/multiple_api_on_canonical.lean:146:15: error: Ambiguous term
  Space
Possible interpretations:
  BlowupDensity.Contracts.V1.Space : Type

  NavierStokes.ProblemStatement.Space : Type
../research/T24/probes/multiple_api_on_canonical.lean:148:12: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:180:12: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:213:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:217:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:221:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:225:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:230:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:236:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:241:19: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:246:6: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:247:8: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:251:32: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:254:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:259:48: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:259:18: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:263:18: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:269:33: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:269:63: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:274:6: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:274:69: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:274:99: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:275:8: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:275:71: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:275:101: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:281:8: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:287:32: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:287:62: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:290:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:295:5: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:295:65: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:298:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:303:5: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:303:65: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:306:9: warning: Variable name `a` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _a

Note: This linter can be disabled with `set_option linter.unusedVariables false`
../research/T24/probes/multiple_api_on_canonical.lean:311:5: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:312:56: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:312:86: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:316:45: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:320:5: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:320:36: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:320:68: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:320:99: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:324:5: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:328:10: error: Ambiguous term
  Space
Possible interpretations:
  BlowupDensity.Contracts.V1.Space : Type

  NavierStokes.ProblemStatement.Space : Type
../research/T24/probes/multiple_api_on_canonical.lean:328:18: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:328:62: error: Function expected at
  toSpec
but this term has type
  x✝

Note: Expected a function because this term is being applied to the argument
  a
../research/T24/probes/multiple_api_on_canonical.lean:327:0: error: (kernel) declaration has metavariables 'MultipleCanonicalProbe._example'
../research/T24/probes/multiple_api_on_canonical.lean:334:7: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:334:47: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:340:7: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:344:22: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:345:54: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:349:24: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
../research/T24/probes/multiple_api_on_canonical.lean:350:59: error: Function expected at
  toSpec
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  a

Hint: The identifier `toSpec` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
```

## Audit detail (resolved representation mismatch)

The initial unparameterized carrier printed:

```text
'NSFormalization.Section3.T24.RegionsData' does not depend on any axioms
```

Its constructor already had the standard three, but the requirement asks for
exactly three for every declaration. The final carrier is naturally indexed
by `ν u p f K M E`, like the canonical API, with raw clauses and prescribed
geometry as fields. Both its type and constructor now print exactly
`[propext, Classical.choice, Quot.sound]`. All 19 canonical audit entries and
all nine named probe declarations have exactly that dependency list.
No artificial proof dependency was inserted.

## Handoff to Ub4–Ub7 (not implemented here)

Ub4 should use disjointness in the form `i ≠ j → Disjoint (ball cᵢ rᵢ)
(ball cⱼ rⱼ)`, available directly as `d.regions_disjoint hij`.
For cross transport, one needs local vanishing of component j near a point
where component i is nonzero, hence vanishing of its spatial derivative.
The compact affine support from `scaledVelocity_tsupp_subset` lies strictly
inside its open region ball. Transport the cube argument using component
periodicity for arbitrary spatial points; the global support of a periodized
field is not contained in one ball. The current zero theorems intentionally
quantify x in the fundamental cube. Ub6 will also need the corresponding
local derivative vanishing and disjoint squared-norm sum identities.

No mathematical residual remains for U-CAN or Ub1–Ub3. No full
`MultipleRegionsAPI` witness or proof of `multipleRegionsStatement` is claimed;
those require Ub4–Ub7.

## Final whitespace check

The staged-file check caught blank lines retained when copying Spec docstrings
and error output: `research/T24/probes/multiple_api_on_canonical.lean:34:
trailing whitespace.` and `research/T24/ATTEMPTS_UB1_UB3.md:413: trailing
whitespace.` (same diagnostic at subsequent blank lines). Removed trailing
spaces only; the final staged check is clean.
