# Section 3 集成分支全量编译检查（2026-09-18）

目的：验证当前集成批次（#317–#325 合入后）Section 3 全部模块可在同一源码树编译；只读检查。

## 环境

| 项 | 值 |
|---|---|
| 被检提交 | `05b0b9c76794d1b0ac86e401a8066d729d330a18` |
| worktree | `.claude/worktrees/361-MAINT-section3-build-c` |
| 工具链 | Lean 4.34.0-rc2 (`6a10ac8c22be`) |
| 线程 | `LEAN_NUM_THREADS=6` |
| 运行方式 | `. scripts/lean-env.sh`；`lake` 从 `verification/` 执行 |

## Section 3 模块数与全量编译

`find formalization/NSFormalization/Section3 -name '*.lean' | sort` = **48 个模块**：

| 目录 | 模块数 |
|---|---|
| `Section3/T10/` | 7 |
| `Section3/T11/` | 30 |
| `Section3/T12/` | 4 |
| `Section3/T13/` | 4 |
| `Section3/T14/` | 1 |
| `Section3/T16/` | 2 |

删除 Section 3 的 `lib/lean` 与 `ir` 编译产物后，以一条 `lake build` 命令重编全部 48 个模块，日志为 `tmp/section3_build.log`。

| 项 | 值 |
|---|---|
| 退出码 | **0** |
| 墙上时间 | **71.75 s** |
| error | **0** |
| Section 3 Built | **48 / 48** |
| Section 3 Replayed | **0** |
| warning 行 | **96** |
| `grep -c 'warning: NSFormalization/Section3/'` | **0** |
| `.olean` 落盘 | **48** |
| Section 3 `sorry` grep | **2**（均为文档文字：`T11/PairingBound.lean:91`、`T12/TameProduct.lean:59`） |

## 闸门

| 命令 | 退出码 | 结果 |
|---|---:|---|
| `make check` | 0 | `check_work_queue`: 45 work items consistent；13 policy tests OK |
| `make test` | 0 | **42** lines `checked; standard logical axioms only` |
| `make test-mutations` | 0 | implementation_refactor accepted；其余三项 rejected as required |
| `python3 experiments/check_contracts.py --base-ref main` | 0 | `registered_contracts: 40`; `base_compatibility_checked: true` |

## Probe 与公理审计扫描

扫描集合为每个 `research/T1*/**/*_closes.lean`、`axioms_*.lean`、`probes/api_on_canonical.lean`，以及 `research/T11/probes/assembly_closes.lean`，共 **89** 个文件。以 4 路并行、每个 `LEAN_NUM_THREADS=2` 执行 `cd verification && lake env lean ../<file>`：

| 项 | 值 |
|---|---:|
| 通过 | **89 / 89** |
| 失败 | **0** |
| 首个 error 行 | 无 |
| 公理结果 | `[propext, Classical.choice, Quot.sound]` |
| 其他公理名 | **0** |

## 结论

48 个 Section 3 模块全部从删除后的产物目录重新 Built，退出码 0，Section 3 warning 0；全局日志有 96 条 warning。四个闸门均退出码 0，`make test` 输出 42 条标准公理检查行，合同注册检查报告 40。89 个 probe/axioms 文件全部通过；源码 `sorry` grep 命中两处文档文字。

未全绿项目：Section 3 `sorry` grep 计数为 2（两处均为说明文字，见上表）。

## 四段记录

**检查了什么：** Section 3 48 模块全量重编、四个闸门、89 个 probe/axioms 文件及公理扫描。

**树中现在有什么：** T10/T11/T12/T13/T14/T16 分别 7/30/4/4/1/2 个模块；48 个 `.olean`；40 个注册合同。

**什么不绿：** `grep -rn sorry formalization/NSFormalization/Section3` 返回 2 个文档文字命中：`T11/PairingBound.lean:91`、`T12/TameProduct.lean:59`。

**命令及结果：** `lake build` rc 0，71.75 s；`make check`/`make test`/`make test-mutations`/`check_contracts.py --base-ref main` 均 rc 0；probe 扫描 89/89 通过。
