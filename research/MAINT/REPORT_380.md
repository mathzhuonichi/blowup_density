# Lane 380 — Section 3 全量编译检查

被检提交：`f9738d6f9894035d7a6634ea1aee72e051603952`。完整记录：[SECTION3_BUILD_20260918d.md](../../logs/SECTION3_BUILD_20260918d.md)。

**检查了什么：** Section 3 57 模块全量重编、四个闸门、108 个 probe/axioms 文件及公理扫描。

**树中现在有什么：** T10/T11/T12/T13/T14/T15/T16/T17 分别 7/30/5/6/1/3/4/1 个模块；57 个 `.olean`；41 个注册合同。

**什么不绿：** Section 3 有 3 条弃用 warning，`sorry` grep 有 3 个文档文字命中。原文：

```text
warning: NSFormalization/Section3/T16/Assembly.lean:327:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: NSFormalization/Section3/T16/Assembly.lean:332:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Section3/T16/Assembly.lean:362:11: `if_pos` has been deprecated: Use `ite_eq_left` instead
formalization/NSFormalization/Section3/T15/HaarBridge.lean:42:`T13.eq_zero_of_mem_cube` / `T13.periodize_eventuallyEq`.  No `sorry`, no named
formalization/NSFormalization/Section3/T11/PairingBound.lean:91:No `sorry`, no axiom, no named `Prop` input: every statement below is
formalization/NSFormalization/Section3/T12/TameProduct.lean:59:No `sorry`, no axiom, no named `Prop` input: every statement below is
```

**命令及结果：** `lake build` rc 0，79.33 s，57 Built、0 Replayed、0 error；全局 warning 99 条。`make check`/`make test`/`make test-mutations`/`check_contracts.py --base-ref main` 均 rc 0；`make test` 标准公理检查行 43；probe 扫描 108/108 通过，其他公理名 0。
