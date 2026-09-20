# REPORT 208 — datum identification and shared local solution

## 1. 证了哪个定理

`solution_of_base` 保留 `U 0 = a.toLp`，将零时刻切片的 a.e. 等式通过两侧连续性
升级为 `velocity (0,·) = a.field`，得到以原 datum 为初值的经典解。
`smoothL2_of_initialClassR` 从合同初值类构造逐点相等的光滑 L² 全阶喷流载体和
无散证明；无需额外分析输入。`exists_localSolution` 对合同三项假设给出正视界。
`localHorizon` 是总函数（不满足假设时取 1）；`localHorizon_pos` 证明其正性；
`localSolution` 是该视界上以原始 `a` 为初值的可复用解数据。

## 2. Lean 里现在有什么

新增 `formalization/NSFormalization/Section4/A01/LocalSolution.lean`，共 9 个声明。
`transport_initial` 只改初值证明，速度和压力保持定义相等。后续车道应直接使用
`localHorizon` 和 `localSolution`，避免再次独立选择。

新增 `ATTEMPTS_LOCAL_SOLUTION.md`、`axioms_local_solution.lean` 和本报告；按任务
要求给 `A3_SPLIT.md` 追加 Contract registration 的 208/209/210/211 行。没有修改
任何已有 Lean 模块。Conformance 通过已有 `Bindings.maximalPartial_ofA02` 检查
规范合同 `ClassicalSolutionR` 的 solution 字段类型，并检查零输入、fallback 和
transport 保留速度/压力。所有工作均在指定 worktree 内，没有 push/merge/rebase。

## 3. 缺口是什么

本车道无命名分析输入或遗留证明缺口。正式模块依仓库规则使用 A02 的唯一结构
重述；规范合同结构通过既有逐字段转换衔接，而非宣称两个结构定义相等。

完整 `LocalTheoryAPI` 尚需 209 的 ManuscriptLocalRegularity、210 的 H¹ 一致
寿命下界、211 的注册。当前由 H⁷ 局部存在作选择的视界未证明 H¹ 一致性；若
210 需更换选择，必须协调依赖它的解与正则性，不能直接断言当前选择具有该性质。
指定 review 的 §5 在本 checkout 不存在，其注册清单位于 §3，已按那里读取。

## 4. 跑了什么命令、什么结果

所有 Lean shell 均先 `. scripts/lean-env.sh`，Lake 仅从 verification/ 运行，
`LEAN_NUM_THREADS=6`。

- `lake build NSFormalization.Section4.A01.LocalSolution`：exit 0，新模块无诊断；
  捕获日志含已有依赖警告重放及 Lake 成功提示，因此原始构建日志并非字面静默。
- `lake env lean ../formalization/NSFormalization/Section4/A01/LocalSolution.lean`：
  exit 0，输出 0 bytes。
- `lake env lean ../research/A01/axioms_local_solution.lean`：exit 0，9 个声明均
  恰好 `[propext, Classical.choice, Quot.sound]`，全部 conformance examples 通过。
- `make check`：exit 0。
- `make test-mutations`：exit 0；内部首先运行 `lake test`，已注册合同全部通过；
  implementation_refactor 接受，三项负例均按预期拒绝。
- `git diff --check`、禁止证明命令扫描及公理日志精确检查：通过。

无新增 heartbeat 设置。完整门禁日志保留在未跟踪的 `tmp/*208.log`。
