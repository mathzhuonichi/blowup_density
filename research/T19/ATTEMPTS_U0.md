# U0 attempts

1. Zero extension: smoothness, spatial derivatives and momentum transport closed directly. Pressure gauge needed unfolding `pressureMeanT` before simplifying the time conditional. Exact first diagnostic:
```text
../formalization/NSFormalization/Section3/T19/Threading.lean:52:4: error: Type mismatch: After simplification, term
  reference.pressure_gauge t ht
 has type
  pressureMeanT reference.pressure t = 0
but is expected to have type
  pressureMeanT (fun z => if z.1 ∈ Ico 0 S then reference.pressure z else 0) t = 0
../formalization/NSFormalization/Section3/T19/Threading.lean:64:16: warning: declaration uses `sorry`
```
The warning was cascading from the failed definition; no admission was written.
Search attempt at `T11/Restrict.lean` returned `No such file or directory`; recursive search found `Source.PacketScaling.residual_congr_local`, used instead.

2. Record literal layout error (fixed by one field per line); subsequent argument errors were cascading:
```text
../formalization/NSFormalization/Section3/T19/Threading.lean:94:77: error: unexpected identifier; expected '}'
../formalization/NSFormalization/Section3/T19/Threading.lean:94:8: error: Fields missing: `packetForce`, `carrier`, `energyBound`, `dissipationBound`, `place`, `scaling`, `a`, `g`, `r`, `δ`, `D`, `reference`, `correction`, `hδ`, `hg`, `ha`
../formalization/NSFormalization/Section3/T19/Threading.lean:101:72: error: Application type mismatch: The argument
  hT
has type
  0 < T
of sort `Prop` but is expected to have type
  ClassicalSolutionT ν ?m.24 ?m.25 (?m.26 + ?m.27)
of sort `Type` in the application
  insertionData hν ?m.28 ?m.29 hT
../formalization/NSFormalization/Section3/T19/Threading.lean:101:69: error: Application type mismatch: The argument
  hg
has type
  g ∈ forceClassT
but is expected to have type
  0 < ?m.27
in the application
  insertionData hν ?m.28 hg
../formalization/NSFormalization/Section3/T19/Threading.lean:109:61: error: Application type mismatch: The argument
  hT
has type
  0 < T
of sort `Prop` but is expected to have type
  ClassicalSolutionT ν ?m.24 ?m.25 (?m.26 + ?m.27)
of sort `Type` in the application
  insertionData hν ?m.28 ?m.29 hT
../formalization/NSFormalization/Section3/T19/Threading.lean:109:58: error: Application type mismatch: The argument
  hg
has type
  g ∈ forceClassT
but is expected to have type
  0 < ?m.27
in the application
  insertionData hν ?m.28 hg
```

3. `insertionData`, `insertionData_rawPremises`, and `insertion` compile with zero output. The registered `packetImportFamily.select` imports successfully from the new canonical module; the eight raw energy clauses are definitionally compatible. Radius `1/4` fits T15's fixed `3/8` chart without extra geometry. The reference horizon is definitionally `T + δ`.

4. A notation token followed immediately by a dot parsed as a qualified identifier. Parenthesized the notation before projections. Exact diagnostics:
```text
../formalization/NSFormalization/Section3/T19/Threading.lean:128:32: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:129:2: error(lean.unknownIdentifier): Unknown identifier `«ins».eps_pos`
../formalization/NSFormalization/Section3/T19/Threading.lean:131:38: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:131:46: error(lean.unknownIdentifier): Unknown identifier `«ins».force`
../formalization/NSFormalization/Section3/T19/Threading.lean:132:2: error(lean.unknownIdentifier): Unknown identifier `«ins».force_mem`
../formalization/NSFormalization/Section3/T19/Threading.lean:134:48: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:135:14: error(lean.unknownIdentifier): Unknown identifier `«ins».force`
../formalization/NSFormalization/Section3/T19/Threading.lean:136:2: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDifference_mem`
../formalization/NSFormalization/Section3/T19/Threading.lean:138:37: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:139:26: error(lean.unknownIdentifier): Unknown identifier `«ins».force`
../formalization/NSFormalization/Section3/T19/Threading.lean:140:2: error(lean.unknownIdentifier): Unknown identifier `«ins».lifespan`
../formalization/NSFormalization/Section3/T19/Threading.lean:142:37: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:143:34: error(lean.unknownIdentifier): Unknown identifier `«ins».force`
../formalization/NSFormalization/Section3/T19/Threading.lean:144:19: error(lean.unknownIdentifier): Unknown identifier `«ins».velocity`
../formalization/NSFormalization/Section3/T19/Threading.lean:144:49: error(lean.unknownIdentifier): Unknown identifier `«ins».pressure`
../formalization/NSFormalization/Section3/T19/Threading.lean:145:2: error(lean.unknownIdentifier): Unknown identifier `«ins».solution`
../formalization/NSFormalization/Section3/T19/Threading.lean:147:42: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:150:28: error(lean.unknownIdentifier): Unknown identifier `«ins».velocity`
../formalization/NSFormalization/Section3/T19/Threading.lean:151:2: error(lean.unknownIdentifier): Unknown identifier `«ins».blowup_limsup`
../formalization/NSFormalization/Section3/T19/Threading.lean:153:39: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:154:29: error(lean.unknownIdentifier): Unknown identifier `«ins».velocity`
../formalization/NSFormalization/Section3/T19/Threading.lean:157:2: error(lean.unknownIdentifier): Unknown identifier `«ins».energyRate`
../formalization/NSFormalization/Section3/T19/Threading.lean:160:8: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDiffMixedConst`
../formalization/NSFormalization/Section3/T19/Threading.lean:161:2: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDiffMixedConst_nonneg`
../formalization/NSFormalization/Section3/T19/Threading.lean:164:22: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:165:38: error(lean.unknownIdentifier): Unknown identifier `«ins».force`
../formalization/NSFormalization/Section3/T19/Threading.lean:166:2: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDifference_mixed_memLp`
../formalization/NSFormalization/Section3/T19/Threading.lean:169:22: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:170:40: error(lean.unknownIdentifier): Unknown identifier `«ins».force`
../formalization/NSFormalization/Section3/T19/Threading.lean:171:24: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDiffMixedConst`
../formalization/NSFormalization/Section3/T19/Threading.lean:174:2: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDifference_mixed_bound`
../formalization/NSFormalization/Section3/T19/Threading.lean:177:8: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDiffSobolevConst`
../formalization/NSFormalization/Section3/T19/Threading.lean:178:2: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDiffSobolevConst_pos`
../formalization/NSFormalization/Section3/T19/Threading.lean:181:22: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:182:37: error(lean.unknownIdentifier): Unknown identifier `«ins».force`
../formalization/NSFormalization/Section3/T19/Threading.lean:183:2: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDifference_sobolev_memLp`
../formalization/NSFormalization/Section3/T19/Threading.lean:186:22: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:187:39: error(lean.unknownIdentifier): Unknown identifier `«ins».force`
../formalization/NSFormalization/Section3/T19/Threading.lean:188:24: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDiffSobolevConst`
../formalization/NSFormalization/Section3/T19/Threading.lean:190:2: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDifference_sobolev_bound`
../formalization/NSFormalization/Section3/T19/Threading.lean:193:59: error(lean.unknownIdentifier): Unknown identifier `«ins».force`
../formalization/NSFormalization/Section3/T19/Threading.lean:195:2: error(lean.unknownIdentifier): Unknown identifier `«ins».forceDifference_negativeSobolev_tendsto`
../formalization/NSFormalization/Section3/T19/Threading.lean:198:22: error(lean.unknownIdentifier): Unknown identifier `«ins».ε₀`
../formalization/NSFormalization/Section3/T19/Threading.lean:199:37: error(lean.unknownIdentifier): Unknown identifier `«ins».force`
../formalization/NSFormalization/Section3/T19/Threading.lean:200:2: error(lean.unknownIdentifier): Unknown identifier `«ins».negative_s_memLp`
```

5. Limit helper needed an explicit `Ioi 0` filter set; final existence theorem needed `include` for hypotheses used only in its proof. Exact diagnostics:
```text
../formalization/NSFormalization/Section3/T19/Threading.lean:212:15: error: don't know how to synthesize implicit argument `y`
  @Tendsto.mono_left ℝ ℝ (fun ε => ins.forceDiffSobolevConst s * (ε ^ (1 / 2 - s) + ε ^ (3 / 2 - s))) (𝓝 0)
    (𝓝[?m.159] 0) (𝓝 0) (Paper1.sobolev_error_tendsto_zero s (ins.forceDiffSobolevConst s) hs) nhdsWithin_le_nhds
context:
ν : ℝ
hν : 0 < ν
a : SpatialField
g : SpaceTimeField
ha : a ∈ initialClassT
hg : g ∈ forceClassT
T δ : ℝ
hT : 0 < T
hδ : 0 < δ
reference : ClassicalSolutionT ν a g (T + δ)
s : ℝ
hs : s < 1 / 2
hs0 : ¬s < 0
⊢ Filter ℝ
../formalization/NSFormalization/Section3/T19/Threading.lean:213:54: error: don't know how to synthesize implicit argument `s`
  @nhdsWithin_le_nhds ℝ PseudoMetricSpace.toUniformSpace.toTopologicalSpace 0 ?m.159
context:
ν : ℝ
hν : 0 < ν
a : SpatialField
g : SpaceTimeField
ha : a ∈ initialClassT
hg : g ∈ forceClassT
T δ : ℝ
hT : 0 < T
hδ : 0 < δ
reference : ClassicalSolutionT ν a g (T + δ)
s : ℝ
hs : s < 1 / 2
hs0 : ¬s < 0
⊢ Set ℝ
../formalization/NSFormalization/Section3/T19/Threading.lean:212:9: error: failed to infer `have` declaration type
../formalization/NSFormalization/Section3/T19/Threading.lean:226:21: error(lean.unknownIdentifier): Unknown identifier `hν`
../formalization/NSFormalization/Section3/T19/Threading.lean:226:24: error(lean.unknownIdentifier): Unknown identifier `ha`
../formalization/NSFormalization/Section3/T19/Threading.lean:226:27: error(lean.unknownIdentifier): Unknown identifier `hg`
../formalization/NSFormalization/Section3/T19/Threading.lean:226:30: error(lean.unknownIdentifier): Unknown identifier `hT`
../formalization/NSFormalization/Section3/T19/Threading.lean:227:45: error(lean.unknownIdentifier): Unknown identifier `hν`
../formalization/NSFormalization/Section3/T19/Threading.lean:227:48: error(lean.unknownIdentifier): Unknown identifier `ha`
../formalization/NSFormalization/Section3/T19/Threading.lean:227:51: error(lean.unknownIdentifier): Unknown identifier `hg`
../formalization/NSFormalization/Section3/T19/Threading.lean:227:54: error(lean.unknownIdentifier): Unknown identifier `hT`
```

6. Lean requires the declaration docstring after `include … in`. Fixed its position. Exact build diagnostic:
```text
error: NSFormalization/Section3/T19/Threading.lean:220:83: unexpected token 'include'; expected 'lemma'
Some required targets logged failures:
- NSFormalization.Section3.T19.Threading
error: build failed
```

The same docstring error was reproduced after adding the module documentation,
with the identical diagnostic at line `224:83`; the subsequent build passed.

## Final outcome
All requested constructions and exports, including `exists_force_close`, close.
No residual statement remains. No extra hypotheses, heartbeat overrides or
admissions were introduced. The probe applies every exported theorem by `exact`.
