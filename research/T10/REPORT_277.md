# Lane 277-SPEC-t10-spec report

## 1. 定了哪个合同

本 lane 没有证明分析定理；它按 lead 的 reconciliation 定稿了 T10 周期数据层规格。
`Spec.lean` 以 Draft B 为底：实 Fourier 闭子空间、B 的 Leray/压力/爆破集命名和
参数形状全部保留；新增论文要求的齐次 datum/范数，并把 `ClassicalSolutionT` 的共同
字段按 `Data.ClassicalSolutionR` 的顺序补齐到 `pressure_gradient`，最后追加三个环面
专属字段。`TorusDataAPI` 把 reconciliation 指定的 datum、Parseval/TorusCube、均值、
Leray、压力、能量和经典解 transport 事实写成了具体字段；每个字段都列出精确量词
顺序和 non-vacuity 说明。

## 2. Lean 里现在有什么

`research/T10/Spec.lean` 在 `BlowupDensity.T10.Draft` 命名空间中给出单位三环面、
实三分量加权 `ℓ²(ℤ³)` datum、物理场桥、非齐次和齐次 `ℝ≥0∞` 范数、均值分解、
周期 Leray 图关系、`𝒳_𝕋`/`𝓕_𝕋`、压力零均值规范、经典解、最大寿命、参数化爆破集、
相对稠密和物理/系数两种 `E_T` 写法。齐次权重是 `|2πk|^s`，零支强制
`A(0)=0`，且按论文把物理 realization 限在 mean-zero 层。

论文 `02-preliminaries.tex:9-10,23-26` 决定：`𝒳_𝕋` 不要求零均值；
`𝓕_𝕋=C_c^∞(𝕋³×(0,∞))` 的周期 lift 只在正时间方向紧支撑并在零附近消失。
`COMPARISON.md` 逐项记录了 A/B provenance、lead ruling、这两行原文、proof dependencies、
两稿 “Needs a lemma” 的完整并集和 owner 问题。按任务要求，两个 registered
`CompletedDense*` abbreviation 对 `CompletedDenseVia` 的泛型等式均以
`example ... := rfl` 固定，Lean 接受。

六个 provenance 文件从 lane 263/264 原样复制；逐一比较 source branch blob id 与
工作区 `git hash-object`，六对 hash 全部相同。

## 3. 缺口是什么

本 lane 只交付规格，没有创建 `verification/Contracts/V1/TorusData.lean`、binding 或
tests。后续证明 lane 仍需完成 `TorusCube` 双向桥、Parseval、datum 存在唯一性与实性、
零模/均值分解、Leray 良定义/收缩/投影/交换、压力规范保持方程、物理与系数能量恒等、
均值演化/常输运、谱隙，以及 `ClassicalSolutionT` 与本地 periodic flow 的逐字段双向
转换和 lifespan 对齐；完整 17 项清单在 `COMPARISON.md`。

任务 brief 留有 R46 模板残片：`q∈{1,2}`/`criticalOrder q.toReal` 和
`04-whole-space.tex` field citation 并不对应 T10 reconciliation 中的任何字段。
本稿没有虚构 whole-space density theorem；只保留 brief 明确要求且无害的两个 `rfl`
检查。另有 homogeneous mean-zero 放置、local conversion 的 contract/binding 边界、
以及 “one structure” 与 reconciliation 同时要求 `ClassicalSolutionT`/`TorusDataAPI`
两结构的冲突，均已列入 `COMPARISON.md` 的 owner questions。

## 4. 跑了什么命令、什么结果

- `cd verification && lake env lean ../research/T10/Spec.lean`：成功，0 errors，0 warnings。
- 同一 workspace 分别 elaboration `DraftA.lean`、`DraftB.lean`：成功，均为 0 errors、
  0 warnings。
- 对六个 provenance 文件分别运行 source `git rev-parse branch:path` 与本地
  `git hash-object`：全部一致。
- `git diff --cached --check`：成功，无 whitespace error。
- 扫描新增 Lean 文件中的 `sorry|admit|axiom|native_decide` 及占位字段：无匹配。
- 检查 `Spec.lean` 直接 import：仅 `Contracts.V1.Data` 与 Mathlib Fourier 模块，符合
  未来 contract import 边界。
