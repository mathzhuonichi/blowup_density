# T16 reconciled specification report

## 1. 证了哪个定理

本 lane 不提交证明，而是定稿
`paper/sections/03-torus.tex:176-216` 的 `lem:potential` 陈述。定稿覆盖光滑
Urysohn 空间/时间截断、径向向量势及 `curl A = v`、小尺度统一阈值、
`w_ε=-curl(η_ε θ_ε A)`、全局光滑/周期/无散/支撑性质，以及活跃区间
`[T-ε²,T)` 上开邻域版本的 `eq:bgzero`。

陈述严格采用 reconciliation 的裁决：B 的 `CutoffData`、B 的
`LocalPotentialAPI` 字段名和次序、B 的包名 `U`，配上 A 的精确论文行号。
这里没有 T17 的导数、能量或力范数估计。

## 2. Lean 里现在有什么

`research/T16/Spec.lean` 提供：

- `CutoffData : Type`，保存 `θ`、`η`、plateau、支撑半径、`ε₀`、径向势和
  修正族；
- `LocalPotentialAPI (v U) K x₀ r T δ D : Prop`，按 B 的次序给出 26 个具体
  数学字段；
- `localPotentialStatement : Prop`，先固定参考场、包、紧集、坐标球和时间
  参数，再存在量化一份 `CutoffData`；
- 周期支撑、周期缩放包和 corrected background 的物理层定义。

每个 `CutoffData` 字段和 API 字段都有当前
`03-torus.tex:<line>` 引用及 `Non-vacuity` 说明。文件不从 `research/`
导入：它显式导入 T10 使用的两个基础模块和已注册 I02 correction 合同，并在
原 T10 namespace 下逐字复制实际需要的 `PeriodicFrequency` 与
`IsPeriodicOn`；复制处有要求的 provenance banner。这样 standalone
elaboration 不依赖研究目录的模块注册；`T01.torus_data` 注册后应改为直接
import。

`COMPARISON.md` 合并了逐条 paper-to-Lean 表、A/B provenance、裁决、证明
依赖和 owner 问题。六份 A/B provenance 文件从 lane 271/272 原 branch
逐字复制；逐文件 Git blob hash 均相同。

## 3. 缺口是什么

本陈述尚未注册进 `Contracts/Bindings/Tests`，也没有 inhabitant。后续证明
lane 需要把已有 Section 4 的 `RadialPotential`、
`CorrectionProfile.physicalCorrection` 和 `CorrectionVectorNorms` 局部化到
坐标球，并补齐 cutoff 的 `[0,1]` 值域、统一 `ε₀`、坐标球边界零延拓、
整数平移的局部有限周期化、支撑传递、div-curl 和 plateau cancellation。
T14 还需提供 `periodicScaledPacket` 的紧支撑/局部有限桥。

T10 侧只需物理表示层的两个初等桥：`IsPeriodicOn` 从坐标单位平移推出所有
整数格点平移，以及 `periodicSet` 在坐标单位平移下不变；它们应作为
`research/T10/COMPARISON.md` “Needs a lemma” 第 1 项的细化。T10 的
Fourier/Parseval/均值/Leray/压力/能量等第 2–17 项不是 T16 的前置条件。
owner 仍需确认 B 的全局 `potential_formula`、`r < 1/2` 坐标图接口、是否在
binding 层另给 A 的更强缩放支撑结论，以及 T14 是否应隐藏 `tsum` 的全定义
junk 行为；完整清单在 `COMPARISON.md`。

## 4. 跑了什么命令、什么结果

- `cd verification && lake env lean ../research/T16/Spec.lean`：通过，0 errors、
  0 warnings。
- 六个 provenance 文件逐一比较 source ref 的 `git rev-parse <ref>:<path>`
  与本地 `git hash-object <path>`：全部 `MATCH`。
- `make check`：通过，退出码 0；仍报告仓库基线的
  `source_hashes_match: false` 和
  `Paper1/BoundaryCorollary.lean:90` 既有 `sorry`，本 lane 未修改这些文件。
- `make test`：通过，`10732/10732`；输出只有依赖树既有 linter warning。
- `make test-mutations`：通过；
  `implementation_refactor` accepted，`admitted_proof`、`extra_axiom`、
  `weakened_hypothesis` 均按要求 rejected。
