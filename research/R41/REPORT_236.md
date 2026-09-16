# Lane 236 report

## 1. 陈述写了什么

`DraftA.lean` 给出了 Theorem 4.1 的独立 A 版合同：固定初值的次临界稠密性、零初值的充要条件、两个阈值的数值，以及 regular reference 附带的同一族插入解结论。零初值保持为一个 `↔`。最终 rider 的初值、精确 lifespan、较早历史、力收敛和 `E_T` 收敛都绑定在同一个 `ε`-family 上。

## 2. Lean 选择

`q : ℕ` 并显式假设 `q = 1 ∨ q = 2`；阈值侧 cast 到 `ℝ`，Bochner 指数侧 cast 到 `ℝ≥0∞`。相对拓扑直接使用 `BreakdownDenseR`，精确终止时间写成 `maximalLifespanR ... = ENNReal.ofReal T`。为引用某个具体 regular velocity 并保证所有 rider 共用同一族，新增了两个仅在草稿中的显式 structure：`RegularReferenceR` 和 `RegularReferenceApproximation`，均标为 **needs registration**。没有把整个 `ThresholdAPI` 塞进主定理，因为其中还有 Theorem 4.1 没有声称的辅助字段。

## 3. 歧义与缺口

主要歧义有四处：定理开头没有单独说 “fix `s`”；“every reference” 可以指 force，也可以指选定的 solution triple；最终 rider 没有重复次临界条件；“singularity exactly at `T`” 是否还要求显式的 `L∞` blow-up。草稿分别选择：在 `q` 后量化 `s`、对每个显式 regular reference bundle 陈述、保留次临界假设、用 `T_max = T` 而不额外加入未在该句出现的 speed blow-up。`COMPARISON_A.md` 逐项记录了这些决定以及从 Theorem 4.2 re-export 的字段。当前没有 elaboration 缺口。

## 4. 跑过的命令

- `. ../scripts/lean-env.sh && lake env lean ../research/R41/DraftA.lean`（在 `verification/`）：最终 0 errors。
- 首次同一命令发现 3 个 subtype binder 推断错误；显式标注正 `ε` subtype 后重跑通过。
