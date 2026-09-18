# Lane 399 — Section 3 全量编译检查

完整表格与 warning 原文见 [编译报告](../../logs/SECTION3_BUILD_20260918e.md)。

**检查了什么：** Section 3 71 模块全量重编、四个闸门、124 个 probe/axioms 文件及公理扫描；被检提交 `dbdac830cec09b6cd3d2aa81823e67a0051ddb70`。

**树中现在有什么：** T10/T11/T12/T13/T14/T15/T16/T17/T20/T22 分别 7/30/7/7/1/4/4/6/1/4 个模块；71 个 `.olean`；42 个注册合同。仅新增本报告与 `research/MAINT/REPORT_399.md`；未改 Lean 源码或台账。

**什么不绿：** 全局日志 99 条含 warning 的行（原文见完整报告）；Section 3 warning 3；`sorry` grep 5 处文档命中，原文：

```text
warning: NSFormalization/Section3/T16/Assembly.lean:327:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: NSFormalization/Section3/T16/Assembly.lean:332:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Section3/T16/Assembly.lean:362:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:46:No `sorry`, no `axiom`; every declaration prints `[propext, Classical.choice, Quot.sound]`.
formalization/NSFormalization/Section3/T15/HaarBridge.lean:42:`T13.eq_zero_of_mem_cube` / `T13.periodize_eventuallyEq`.  No `sorry`, no named
formalization/NSFormalization/Section3/T11/PairingBound.lean:91:No `sorry`, no axiom, no named `Prop` input: every statement below is
formalization/NSFormalization/Section3/T12/HaarCube.lean:42:No `sorry`, no `axiom`, no `native_decide`, no named goal input.  Every
formalization/NSFormalization/Section3/T12/TameProduct.lean:59:No `sorry`, no axiom, no named `Prop` input: every statement below is
```

**命令及结果：** `lake build` rc 0，WALL_SECONDS=80.80，71 Built、0 Replayed、0 error；`make check`/`make test`/`make test-mutations`/`check_contracts.py --base-ref main` rc 0/0/0/0；`make test` 标准公理检查行 44（不是注册合同数量）；probe 124/124 通过，其他公理名 0。
