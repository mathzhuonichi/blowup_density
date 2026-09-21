# 266-SPEC-t13-draft-b

## 1. 证了哪个定理

本 lane 按要求只写陈述，**没有证明** `lem:localization`，也没有构造 `LocalizationAPI`。独立重述论文 `03-torus.tex:22–98`：两条 Gagliardo/Fourier 恒等式、常数及格点尾界、eq:localization 的单向非齐次上界，以及 s=0、s=1 的端点等式。未把论文上界改写成双向范数等价。

## 2. Lean 里现在有什么

`research/T13/DraftB.lean` 包含 I_R、立方体版 I_T、K_s、非零格点尾和、显式 c_s，以及八字段的 `LocalizationAPI : Prop`。R³ 齐次范数直接引用注册 `dotHomogeneousENorm`；周期范数使用三分量 Euclidean 产品中的加权 ℓ² 数据。物理场是 R³ 上的实向量场，周期化是实际格点求和，齐次周期恒等式保留减均值。常数放在所有支撑于固定球的光滑场之前量化，保证对支撑收缩一致。

`COMPARISON_B.md` 给出论文子句→字段表、支撑／周期化、向量约定、精确 2π 规范、歧义与待证引理。未注册定义均有标记，三个已有定义的逐字副本明确列出未来 rfl 桥要求。未修改冻结合同。已追加本 lane 的 NEXT_SESSION 记录；提交范围仅这些产物和该记录。未读取其他 T13/T10 草案、其他相关 lane briefs；未启动子代理。

## 3. 缺口是什么

需要真正构造 API，并与独立 T10 数据层协调注册。主要分析缺口是 Gagliardo–Fourier 识别、周期核尾界与几何 clearance、单拷贝周期化，以及范数／数据的桥接；详见 comparison 的十一项清单。Lean elaboration 只验证陈述类型正确，不证明 API 可满足。现有 D01 和周期 Parseval／weighted-ℓ² 模块仅作词汇与未来引理来源，没有假装已有 T13 证明。

## 4. 跑了什么命令、什么结果

在本 worktree、加载 `. scripts/lean-env.sh` 后：

- `cd verification && lake env lean ../research/T13/DraftB.lean`：通过，退出码 0，无警告／错误。
- `make check`：通过，退出码 0；合同政策 13 项测试通过，30 个 work item 一致。其现有全库盘点仍报告 `source_hashes_match: false` 及既有 `Paper1.BoundaryCorollary` 的 admission；本 lane 未修改那些源文件，草案未导入该模块。
- `make test`：通过，退出码 0；10732 个构建任务完成／回放，注册合同公理审计通过。日志 `/tmp/266-t13-make-test.log`。
- `make test-mutations`：通过，退出码 0；implementation_refactor 被接受，admitted_proof、extra_axiom、weakened_hypothesis 按预期被拒绝。日志 `/tmp/266-t13-mutations.log`。
- `git diff --check`：通过；草案声明扫描没有 theorem、sorry、admit、axiom 或 native_decide。

在 `erenup/266-SPEC-t13-draft-b` 提交；不 push、merge 或 rebase。现有合同测试不是本草案的数学证明。
