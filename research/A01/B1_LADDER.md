# B1 时间正则阶梯 — lanes 161 / 169

本 lane 已证明 R1，范围 **所有 `m ≤ q + 1`**，包括闭端点。没有假设
`ClassicalSolutionR`、空间光滑代表元、时间可导性或 Duhamel 方程；R1 只消费柱面路径本身的连续性、角不变性和下降恒等式。

以下 `Space` 是 `NavierStokes.ProblemStatement.Space`，`IsSobolevDatum` 是 D01 的谓词，
`RealVectorSobolev` 是 Paper3 的角频率 datum。`I := Icc (0 : ℝ) S`，
`u : C(I, SobolevSpace 1 (q+1))`，`U : C(I, EulerMeanSolenoidal.L2)`，
`hu : ∀ θ t, sobolevTranslation 1 (q+1) (0, θ) (u t) = u t`，
`hU : ∀ t, ordinaryLift (U t) = value 1 (u t)`。

| 阶梯 | 精确 Lean 结论（完整绑定见下方） | 已有供给 | 缺口 / 大小 |
|---|---|---|---|
| R1 | `∃ A : I → RealVectorSobolev (m : ℝ), (∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) ∧ Continuous A` | 本 lane `exists_continuous_datumPath`；`continuous_cylinder_word`；`L2Descent.exists_ordinaryLift_of_invariant`；`EulerPairing.weakDeriv_pairing_of_lift_hasDerivAt`；D01 `exists_isSobolevDatum_norm_le_sharp`, `isSobolevDatum_sub` | **DONE**，全部 `m ≤ q+1`；不是只证范数连续 |
| R2 | `∃ A R : C(I, RealVectorSobolev (m : ℝ)), (∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) ∧ (∀ t, IsSobolevDatum (m : ℝ) (⇑(projectedResidualOrdinaryPath … t)) (R t)) ∧ ∀ t ∈ Ioo 0 S, HasDerivAt (extendPath S hS.le A) (R ⟨t,…⟩) t` | lane 169 `exists_differentiable_datumPath`；vendor `realization_hasDerivAt`；`hasDerivAt_of_injective_map`；R1 的定量 datum 选择；角不变下降 | **DONE**，全部 `m ≤ q-1`；残差精确为 `νΔu + P(F-(u·∇)u)`；端点只声明连续，不声明单侧导数 |
| R3 | `∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ), ContDiffOn ℝ j G (Icc 0 S) ∧ ∀ t : I, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)` | R1；R2 `exists_differentiable_datumPath`；D01 datum 唯一性；A03 有限阶乘积估计；C01 残差代数 | 仍需构造光滑代表元并把投影残差识别为物理 `∂ₜ`；每次时间微分消耗空间阶，力也需时间光滑；固定有限 `q` 不能给任意 `j`。**L** |
| R4 | `∃ v : ℝ × Space → Space, ContDiffOn ℝ ∞ v (Ico 0 S ×ˢ univ) ∧ ∀ t : I, (fun x => v (t.1, x)) =ᵐ[volume] ⇑(U t)` | `Paper3.angularBoundedRepresentative`；`C01.jetOfDatum_continuous`；`D01.jetOfDatum_ae`；`Paper1.PeriodicH3RepresentativeBridge.continuous_pointwise_representative`, `differentiated_path_pointwise_continuous` | 选取各阶兼容的点值代表元，识别混合偏导并升级联合全阶光滑。**L**（已有 C⁰ / 空间导数设备） |

## R1：已核验的完整语句与机制

```lean
theorem exists_continuous_datumPath {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (m : ℕ) (hm : m ≤ q + 1) :
    ∃ A : Icc (0 : ℝ) S → RealVectorSobolev (m : ℝ),
      (∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) ∧ Continuous A
```

`word 1 (u t) hn w` 是有限乘积的连续坐标，`continuous_cylinder_word` 明确证明其连续性。
`weakDerivsBound_word_top` 对剩余导数阶归纳：每个词的角不变性由 `hu` 的坐标投影得到，
`exists_ordinaryLift_of_invariant` 下降到 L²，不经过需要额外三阶的点值切片。
词范数不超过整个柱面数组范数；下降是等距；`word_hasDerivAt` 给平移轨道的强导数，
`weakDeriv_pairing_of_lift_hasDerivAt` 给 Schwartz 配对。于是
`weakDerivsBound_cylinder_top` 得到 `HasWeakDerivsL2Bound (⇑U) (‖u‖²) m`。

D01 的定量构造器给出 datum，随后将同一个估计应用于 **柱面之差**：

```lean
‖A - B‖ ^ 2 ≤ (4 : ℝ) ^ m * ‖u - v‖ ^ 2
```

这里 `A, B` 是两侧任意合法 datum（完整绑定见 `datum_sub_norm_sq_le`）。
D01 的 `isSobolevDatum_sub` 和 `Lp.coeFn_sub` 处理代表元的 a.e. 差异。
开平方得到 `‖A(t)-A(s)‖ ≤ 2^m * ‖u(t)-u(s)‖`，夹逼推出所选择的 `A` 连续。
因此不依赖“逐点 Classical.choose 自动连续”这种错误推理；任意合法选择都有同一增量控制。
范数路径 `fun t => ‖A t‖` 连续直接由 `Continuous.norm` 得到。
不需要将高阶 Bessel 升阶算子错误地当作裸 L² 上的有界算子。

## R2：已核验的完整语句与机制

lane 169 在真实 Duhamel 前提下证明：若 `hq : 6 ≤ q`、`hm : m ≤ q-1`、
`hν : 0 < ν`、`hS : 0 < S`，则存在闭区间上的连续 datum 路径 `A,R`，其中
`A t` 是 `⇑(U t)` 的 order-`m` datum，`R t` 是普通 L² 投影残差的 order-`m` datum，且

```lean
∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
  HasDerivAt (extendPath S hS.le A)
    (R ⟨t, ht.1.le, ht.2.le⟩) t
```

这里 `extendPath` 是用 `projIcc` 的夹紧延拓；只在开区间内部声明两侧导数。
`projectedResidualPath_eq` 把柱面残差逐字识别为

```lean
ν • laplacianOperator 1 m (restrictOperator 1 _ (u t)) +
  restrictOperator 1 _
    (leray 1 q (sobolevPath F hF q t - advection 1 hq (u t) (u t)))
```

即 `νΔu + P(F-(u·∇)u)`。`ordinaryLift_projectedResidualOrdinaryPath` 证明普通 L²
残差重新 lift 后恰为上述柱面残差，所以 `R` 的语义不是仅靠名称约定。

证明先用 `Source.OrdinaryForcedTime.realization_hasDerivAt` 对 mild/Duhamel 方程求导，
得到普通 L² 路径的导数。R1 的定量构造分别为速度与残差选出连续的 order-`m` datum。
将两条路径用 `lowerVectorL m 0` 降到 order zero 后，datum 唯一性把它们识别为普通 L²
的标准 order-zero datum；`lowerVectorL_injective` 与
`EulerInjectivePathDerivative.hasDerivAt_of_injective_map` 再把导数提升回 order `m`。
两阶空间损失来自 Laplacian，给出恰好 `m ≤ q-1`。

`residualDatum_is_timeDerivative` 还给出 R3 接口：若已经有代表元 `v`，并逐点证明其时间
导数等于 `projectedResidualOrdinaryPath`，则 `R t` 是 `fun x => ∂ₜv(t,x)` 的 datum。
目前没有无条件构造该光滑代表元，也没有恢复压力，因此未声称物理式
`F-(u·∇)u+νΔu-∇p`。在不可压缩情形中这应与投影式对应，但该桥属于后续 rung。

物理侧路线仍有循环限制：

- `A04.timeDeriv_isSobolevDatum` 假设 `w : ClassicalSolutionR ...`、`2 ≤ m`、
  `hGc : ContDiffOn ℝ ∞ G (Ico 0 T)`，只能反向识别已经存在的 `deriv G`。
- `C01.residualPath`、jet 连续性和压力梯度路径也以 `ClassicalSolutionR` 为输入，不能用于
  从 A01 的 Duhamel 输入首次建立时间可导性。
- `D01.exists_smoothL2Field_of_memHInfty` 要求 `ContDiff ℝ ∞ z`；它不能从裸 a.e. 切片
  无循环地产生所需的时空光滑代表元。

## R3/R4：同一 horizon、力的时间正则性和代表元

R3 的共同 `U` 必须在同一个 `Icc 0 S` 上被任意高阶柱面解实现；需要跨阶唯一性与供给侧先验界。
单独的 `F : I → SmoothL2Field Space` 加 `∀ n, Continuous (fun t => (F t).jetLp n)`
只给 **时间连续** 外力，不足以证明任意 `j` 的时间光滑性。
重复时间微分前必须从 manuscript 的力类取得各阶时间导数及其 Sobolev 控制；R1 完全不需要该假设。
R3 的一致性由同一物理切片的 datum 唯一性保证，而跨柱面阶的 `U` 相同仍需另证。

R4 表中的假设是 R3 全部 `j,m`（或等价的每阶 `ContDiffOn ℝ ∞` datum 路径），
结论选择 **一个** 联合光滑 `v`，不声称原始 `Lp` coercion 逐点光滑。
低阶连续代表元由高阶降阶一致性固定，空间求导和时间求导用连续线性求值搬运，再识别混合导数。
有限阶 datum⇒喷流定理及周期/柱面 C⁰ 代表元定理只能作为设备。

最终消费者还要 B2 各字段和压力、外力桥。`REVIEW_SLICE_WIRING.md` §3(b) 实际展示的是
`CarrierConstructor`，没有名为 `CarrierConstructorFull` 的定义；该文件中的短版本仅有下降假设，
不足以从任意路径推出经典解。本 checkout 也没有 owner 分支上的 `ConstructorPieces.lean`。
必须使用包含真实 Duhamel 等式和正则外力的完整构造子前提。
另外 `S < T` 的构造子输出需要延拓／余量，R1–R4 在 `[0,S]` 上的正则性本身不会产生 `T > S`。

论文核验：已用 `sed -n '71,76p' paper/sections/appendix-a-local-theory.tex` 核读：
`W^{1,∞}_t H^k_x` → 连续 RHS → 重复时间微分 → 全 `C^j_t H^k_x`，包括初始单侧导数。
这里 R1 提前利用已经给定的强连续柱面路径，既没有证明该 W¹∞ 步，也没有用连续性代替 R2。

树检索：按要求 `grep -rnE 'HasDerivWithinAt|quadraticDuhamel|ContDiffOn|continuous.*[Dd]atum|residualPath'`
覆盖 `Section4/{D01,A03,A04,A01,C01}`；并读了上述候选的签名和证明入口。
缺口判断针对这些现有设备能否从本 lane 的输入闭合，不是仅凭名字搜索断言数学结果不存在。
