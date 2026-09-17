# Lane 276 — T22 draft B

## 1. 证了哪个定理

本 lane 是独立双盲 specification 工作，没有证明新定理。陈述对象是 `03-torus.tex:603-625` 的分布限制商范数、固定内部紧支场的零延拓双边界，以及任意实阶的固定截断乘子界。没有读取其他 T22 草稿、禁止的研究目录或其他 lane 简报。

## 2. Lean 里现在有什么

`research/T22/DraftB.lean` 可在 Lean 4.34.0-rc2 elaboration。复用 D01 全空间数据与范数；新增区域测试、分布限制、商范数、物理场限制、零延拓与乘子配对定义。`BoundedDomainNormAPI : Prop` 有三个具体字段：`orderZero`、`cutoffMultiplier`、`zeroExtensionComparison`。常数是显式正实数，在所有数据 / 场之前选取，因此与 ε 无关。新定义均标注待注册及与 T10 对齐，docstrings 引用论文行号。没有占位 Prop、未证公理或证明占位符。比较表、范围选择和后续引理清单在 `COMPARISON_B.md`；更新了本 lane 的 `NEXT_SESSION.md` 入口。

## 3. 缺口是什么

API 尚无实例，不能视为 T22 已证明或已注册。需证明任意实阶乘子界、商范数 / 阶零 L² 桥、内部 cutoff 与分布乘积恒等式，再取下确界。混合时间范数比较及一般张量推广未额外打包；需要可测性和 Bochner 桥。两个目标显示式不含环面范数，未添加不必要的周期系数定义。B02 的频率环带逼近可复用，但不自动给出空间截断乘子定理。待另一独立草稿完成后由 lead reconciliation。

## 4. 跑了什么命令、什么结果

每个 Lean shell 先 `. scripts/lean-env.sh`。

- `cd verification && lake env lean ../research/T22/DraftB.lean`：通过，exit 0，无警告。
- `cd verification && lake env lean ../tmp/T22Names.lean`：通过；核对 Mathlib 的 Schwartz 测试乘法、光滑性、支撑、积分、ENNReal 和 Lp 名称，以及注册数据对象。
- `make check`：通过，exit 0；13 个合同政策测试通过，45 个工作项一致。
- `LEAN_NUM_THREADS=6 make test`：通过，exit 0；现有注册合同测试闭包通过。这不构成本草稿 API 的证明。
- `make test-mutations`：通过，exit 0；实现重构接受，admitted proof / extra axiom / weakened hypothesis 均按预期拒绝。
- `git diff --check`：通过；草稿禁用证明占位符扫描无命中。

交付仅提交于 `erenup/276-SPEC-t22-draft-b`；不 push、merge 或 rebase。
