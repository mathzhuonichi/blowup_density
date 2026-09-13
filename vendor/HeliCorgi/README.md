# NS MNS-2 Flow-map Bridge

Navier–Stokes / Hou axisymmetric-with-swirl branch の研究 repo。Lean 4 + mathlib で
**実際の `R³` incompressible Navier–Stokes 方程式**の局所理論(存在・一意性・明示的 lifespan・
continuation・blow-up dichotomy、および real divergence-free Schwartz 初期データからの
入口 adapter)を証明済みで、並行して Type-II / BH candidate の kill ledger を回している。

**Clay problem は未解決。global regularity も blow-up も証明していない。**

## 最上位目標

この repo の最上位仕様は [`PROJECT_GOAL.md`](PROJECT_GOAL.md)。

ultimate target は **Clay / Fefferman の3次元 Navier–Stokes statement A/B/C/D のいずれかを、公式の仮定と domain に一致する形で厳密に解決すること**。

現在の主攻撃は **breakdown 側（C/D）**。その中でも、数学的に成立するなら **unforced `f = 0`** の構成を優先する。

Hou有限円柱、MNS-2、flow-map identity、mild-solution interface、POD/SVD、Lean の条件付き定理は全部中間層。`R³` / periodic Clay domain への厳密な接続なしに Clay 解決扱いはしない。

## いま何がある？

中心 identity は、同じ differentiable flow map `S_T` に対して

```text
S_T(c(1)) - S_T(c(0)) = ∫ DS_T(c(s))[c'(s)] ds
```

という path integral。v2.2 では synthetic MNS control 上で radial / Gamma-first / Omega-first の3経路が一致し、closed rectangle loop もほぼ0まで落ちている。

**これは discrete flow-map consistency の結果であって、3D continuum Navier–Stokes の一般解証明でも Clay A/B/C/D の証明でもない。**

その上で Lean 側は、抽象 bridge から `R³` の具体的な Fourier / `L²` operator 層へ進んでいる。

## 現在の formal frontier

`R³` の具体的な operator 層から、局所理論を経て **実際の incompressible Navier–Stokes 方程式**
までの縦の連鎖が定理として閉じている(local `Formal.+` gate green、`Formal/AxiomAudit.lean` は
標準3公理 `propext` / `Classical.choice` / `Quot.sound` のみ):

```text
explicit R³ operators (Stokes evolution / H²→H³ smoothing / Leray at L², H², H³)
        ↓
projected convection  (r3ProjectedConvectionH3ToH2)
        ↓
concrete endpoint-safe mild equation  (r3EndpointSafeProjectedDuhamelContract)
        ↓
local existence  (Picard, ball uniqueness)
        ↓
real local solution  (reality gate: 全 operator の共役同変性 + 実データ ⇒ 実解)
        ↓
explicit lifespan  (K(T) = T + √T/(π√ν) 閉形式、T₀ = (δ/(1+(π√ν)⁻¹+δ))²)
        ↓
unrestricted uniqueness  (ball 制限なし; 実データの任意の mild 解は無条件に実)
        ↓
restart / concatenation  →  continuation blow-up dichotomy
        ↓
decoded physical velocity U = J⁻³-decode(u) の意味論
  (Laplacian・convection・Helmholtz 圧力・divergence をすべて定理で同定)
        ↓
∂ₜU − νΔU + (U·∇)U + ∇p = 0,  ∇·U = 0
  (r3EndpointSafeProjectedMild_navierStokes:
   空間は成分別 𝓢'、時間は強 L² 微分、局所地平線の内部時刻)
        ↓
admissible 初期データ adapter  (real divergence-free Schwartz datum ⇒ 上の全部)
```

意味論の正確な強さ、定理単位の依存連鎖、edge 分類、残存 edge は
[`docs/formal/R3_NS_VERTICAL_INTEGRATION_STATUS.md`](docs/formal/R3_NS_VERTICAL_INTEGRATION_STATUS.md)
に固定してある。

**まだ無いもの(正確に):**

- 古典解の意味論(時間微分は強 `L²`、空間は分布。pointwise classical solution ではない);
- global time(地平線は局所。dichotomy は証明済みだが global regularity も blow-up も未証明);
- uniform-in-time energy bound / energy inequality(各時刻の有限エネルギーのみ、edge 4 は PARTIAL);
- canonical maximal trajectory `u* : [0, T*) → H³` と pointwise
  `limsup_{t→T*} ‖u*‖ = ∞` 形の定理(dichotomy は証明済み、trajectory-level 言い換えは未構成);
- 圧力の正則性(edge 2a の witness であり、調和項の差を除いて決まる);
- 任意 `H³` 初期データの smoothness 特徴づけ(`H³ ⇒ C^∞` は偽であり主張しない);
- Clay breakdown statement への転送(edge 5)と Clay A/B/C/D の解決(なし)。

形式側は Stage-9 readiness 監査で `PASS`
([`docs/formal/STAGE9_READINESS_AUDIT_2026-08-23.md`](docs/formal/STAGE9_READINESS_AUDIT_2026-08-23.md))、
以後 formal plumbing は stop rule で停止。研究側の凍結後 frontier は
[`docs/gates/TYPE2_KILL_TABLE_2026-08-19.md`](docs/gates/TYPE2_KILL_TABLE_2026-08-19.md)、
次に攻める唯一の decision theorem は
[`docs/gates/STAGE9_DECISION_SELECTION_2026-08-23.md`](docs/gates/STAGE9_DECISION_SELECTION_2026-08-23.md)。

## 主要な式はどこ？

式は PDF や単独ノートではなく、現在は主に `Formal/*.lean` に theorem / definition として直接入っている。

### 1. Incompressibility / divergence

Fourier 空間では

```text
ξ · û(ξ) = 0
```

を divergence-free 条件として使う。

Lean 実装:

- [`Formal/R3DivergencePointwise.lean`](Formal/R3DivergencePointwise.lean)
- [`Formal/R3NormalizedDivergenceFrequency.lean`](Formal/R3NormalizedDivergenceFrequency.lean)
- [`Formal/R3ClosedSolenoidalCarrier.lean`](Formal/R3ClosedSolenoidalCarrier.lean)

closed `L²` solenoidal carrier は概念的には

```text
L²_σ(R³) = ker(D_norm ∘ 𝓕)
```

として定義されている。

### 2. Leray projector の pointwise symbol

[`Formal/R3LerayFrequencySymbol.lean`](Formal/R3LerayFrequencySymbol.lean) に real fiber 版

```text
P(ξ)v = v - ((ξ · v) / |ξ|²) ξ
```

を証明済み。

[`Formal/R3LerayComplexFiberSymbol.lean`](Formal/R3LerayComplexFiberSymbol.lean) は、実際の Fourier velocity fiber `R3C = ℂ³` に対する complex-linear 版

```text
P_C(ξ)v = v - (⟪ξ_C, v⟫ / ‖ξ_C‖²) ξ_C
```

を証明済み(`ξ_C` は real frequency `ξ` の coordinatewise complex embedding)。

matrix notation では引き続き

```text
P(ξ) = I - (ξ ⊗ ξ) / |ξ|².
```

`ξ = 0` では identity になるよう定義と整合させる。

### 3. Stokes / heat semigroup

[`Formal/R3StokesFrequencySymbol.lean`](Formal/R3StokesFrequencySymbol.lean) では mathlib の Fourier convention に合わせて

```text
λ_ν(ξ) = (2π)² ν |ξ|²
```

```text
e^{-t λ_ν(ξ)} = exp(-(2π)² ν |ξ|² t)
```

を使い、

```text
Ŝ_ν(t)u(ξ) = e^{-(2π)² ν |ξ|² t} û(ξ)
```

という scalar Fourier multiplier を定義している。

実際の bounded `L²` operator への lift は

- [`Formal/R3StokesL2Operator.lean`](Formal/R3StokesL2Operator.lean)
- [`Formal/R3StokesSolenoidalOperator.lean`](Formal/R3StokesSolenoidalOperator.lean)

にある。

### 4. Function-space Leray projector

[`Formal/R3LerayL2Operator.lean`](Formal/R3LerayL2Operator.lean) では

```text
P_L² : L²(R³; ℂ³) → L²(R³; ℂ³)
```

を closed solenoidal submodule への orthogonal projection として定義している。

証明済みの性質は

```text
range(P_L²) = L²_σ
P_L²(P_L² u) = P_L² u
P_L² u = u       if u ∈ L²_σ
‖P_L² u‖₂ ≤ ‖u‖₂
```

など。

### 5. Fourier bridge

[`Formal/R3LerayFourierBridge.lean`](Formal/R3LerayFourierBridge.lean) で

```text
𝓕(P_L² u) = P_freq(𝓕u)
```

を証明し、physical-space orthogonal projector と frequency-side orthogonal projector を Plancherel Fourier transform で conjugate している。

abstract Hilbert projection と explicit complex Leray matrix symbol の a.e. 一致

```text
P_freq f(ξ) = P_C(ξ) f(ξ)    a.e. ξ
```

も証明済み(`r3LerayL2FrequencyOperator_ae`)。

### 6. Navier–Stokes 方程式そのもの

[`Formal/R3NavierStokesEquation.lean`](Formal/R3NavierStokesEquation.lean) の capstone
`r3EndpointSafeProjectedMild_navierStokes` は、solenoidal 初期座標に対する endpoint-safe
projected mild solution `u` の decoded 物理速度 `U s = r3H3ToL2Operator (u s)` について、
地平線内部の各時刻で

```text
∂ₜU = νΔU − P((U·∇)U)          -- 強 L² 時間微分
∂ₜU − νΔU + (U·∇)U + ∇p = 0    -- 成分別 𝓢'、p = r3HelmholtzPressure ((U·∇)U)
∇ · U = 0                        -- 分布的
```

を証明している。`Δ` と `(U·∇)U` は名前ではなく定理で同定済み
(`r3L2ToTempered_r3H3LaplacianL2Operator`、edge 2b-i)。

[`Formal/R3SchwartzInitialData.lean`](Formal/R3SchwartzInitialData.lean) は、実・divergence-free
な Schwartz 初期データからこの理論に入るための最小 adapter
(`r3AdmissibleSchwartzDatum_navierStokes`)。decode∘encode が恒等になること
(`r3H3ToL2Operator_r3SchwartzToHsCLM`)、実性の decoder 越しの輸送
([`Formal/R3DecodedVelocityRealness.lean`](Formal/R3DecodedVelocityRealness.lean))、各時刻の
有限エネルギーが揃っている。

## Navier–Stokes 本体との距離

接続対象の equation は unforced incompressible 3D Navier–Stokes

```text
∂ₜu - νΔu + (u · ∇)u + ∇p = 0
∇ · u = 0
```

で、Leray projection 後は形式的に

```text
∂ₜu - νΔu + P((u · ∇)u) = 0
```

mild form は

```text
u(t) = e^{νtΔ}u₀
       - ∫₀ᵗ e^{ν(t-s)Δ} P((u(s) · ∇)u(s)) ds.
```

この projected 形の局所理論(存在・一意性・地平線・restart/continuation)は閉じており、そこから
**unprojected な上の方程式そのもの**への semantic promotion も上記 capstone で閉じた。
残る距離は「意味論の強さ」と「時間の大域性」であって、方程式の同定ではない — 具体的には
古典解・global time・uniform energy・maximal trajectory・Clay breakdown 転送(edge 5)。

legacy の abstract quadratic mild / tangent / continuation bridge 層は残置してあるが、`R³` の
縦連鎖はそれを経由せず具体 operator 上で閉じている(接続 adapter は
`docs/formal/R3_NS_VERTICAL_INTEGRATION_STATUS.md` の Bucket B、bottleneck ではない)。

## ディレクトリ

- `PROJECT_GOAL.md` — 最上位の Clay goal / acceptance specification
- `AGENTS.md` — claim / exploration guardrails
- `FORMAL_SCOPE.md` — Lean 側の現在の定理境界
- `HANDOFF.md` — 次セッションへの継続点
- `Formal/` — Lean 4 formalization。本当に証明されている式・operator・bridge はここ
- `src/core/` — LF-WENO7 / full pilot / physical-metric adjoint
- `src/bridge/` — flow-map bridge
- `src/geometry/` — clustered SVD / 4-way projector geometry / temporal scan
- `src/lattice/` — grid-dt-window convergence planner/gate
- `tests/data/` — synthetic reproducibility seed/meta/schedule
- `docs/reports/` — 進捗レポ
- `failcases/` — proof / numerical inference failcase 集

## References and external formalizations

この repo の最終 target と formalization の cross-check には、少なくとも次を参照している。

- Clay Mathematics Institute, **Navier–Stokes Equation** — 公式 Millennium Prize problem page。最終的な acceptance criterion はこの公式 statement / Fefferman problem description を優先する。<https://www.claymath.org/millennium/navier-stokes-equation/>
- Charles L. Fefferman, **Existence and Smoothness of the Navier–Stokes Equation** — Clay の公式 problem description。A/B/C/D の仮定・domain・decay・energy 条件の基準。
- Robert Joseph George, **Formalization of the Millennium Prize Problem Statements in Lean 4**, version 2.0.0 (2026-07-11), `lean-dojo/LeanMillenniumPrizeProblems`, Apache-2.0. この repo では Clay/Fefferman statement の mechanized cross-check として参照しており、現時点では source code を vendoring していない。<https://github.com/lean-dojo/LeanMillenniumPrizeProblems>
- **Mathlib** — Fourier transform、`Lp`、Hilbert-space projection、Euclidean-space infrastructure の基盤。この repo は `lake-manifest.json` / Lake configuration で revision を固定する。

`LeanMillenniumPrizeProblems` との declaration-level の対応、`R3LerayL2Operator.lean` との非重複部分、Apache-2.0 の再利用方針、将来の semantic promotion obligations は [`docs/formal/LEAN_MILLENNIUM_ALIGNMENT.md`](docs/formal/LEAN_MILLENNIUM_ALIGNMENT.md) に整理している。

外部 source code を将来コピー・改変して配布する場合は、README 上の citation だけで済ませず、その PR で applicable copyright / attribution notices、Apache-2.0 license 条件、変更表示を保持する。

## Claim discipline

現状サポートされるラベルは

`EXACT DISCRETE SOLUTION-MAP REPRESENTATION: SUPPORTED`

など各成果物の明示 scope まで。continuum general solution / blowup proof / Clay resolution への promotion は、`PROJECT_GOAL.md` の最終 gate を満たすまでしない。

## License

[Apache License 2.0](LICENSE)。Lean / mathlib エコシステムの標準に合わせている。

Lean 側は mathlib(Apache-2.0)に依存し、`lake-manifest.json` で revision を固定する。将来
`LeanMillenniumPrizeProblems`(Apache-2.0)等の外部 source を vendoring する場合は、上記
References 節の方針どおり attribution notice と変更表示を保持すること。
