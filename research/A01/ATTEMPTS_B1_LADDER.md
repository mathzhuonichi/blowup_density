# B1 ladder — 尝试记录（161）

## 成功路线

先查看 `OrderTwoCap` 的有限阶弱导数定量归纳和 `L2Descent` 的无损 L² 下降。
没有重造 Fourier 升阶算子：把词归纳中的 `exists_descend` 换成
`exists_ordinaryLift_of_invariant`，其余平移导数配对不变，得到全部 `m ≤ q+1`。
对 `u-v` 再应用 D01 的 sharp 定量构造器，得 `4^m` 增量平方控制。
用 `D01.isSobolevDatum_sub` 处理任意阶 datum 差，范数夹逼给完整连续性。

首轮已通过顶阶弱导数归纳、下降和差的范数控制；失败只有下面两处 elaboration。

## 失败 1：谓词展开后，点记法没有解析到 IsSobolevDatum

尝试 `hd.congr_field (Lp.coeFn_sub U V).symm`。
修正：显式 `IsSobolevDatum.congr_field hd (Lp.coeFn_sub U V).symm`。

## 失败 2：连续性夹逼的端点和常量没有从 simpa 自动推断

第一次尝试 `u.continuous.continuousAt.sub continuousAt_const`。
需要显式指定 `(x := t)` 和常量 `u t`。
首轮两个错误原文：

```text
error: NSFormalization/Section4/A01/DatumPathContinuous.lean:71:7: Invalid field `congr_field`: The environment does not contain `Function.congr_field`, so it is not possible to project the field `congr_field` from an expression
  hd
of type
  ∀ (i : Fin 3) (ψ : 𝓢(Space, ℂ)),
    ((Paper3.angularRealization ↑m) ↑((A - B).ofLp i)) ψ = ∫ (x : Space), ψ x * ↑(((↑↑U - ↑↑V) x).ofLp i)
error: NSFormalization/Section4/A01/DatumPathContinuous.lean:97:4: Type mismatch: After simplification, term
  Filter.Tendsto.const_mul (2 ^ m)
    (ContinuousAt.tendsto
      (ContinuousAt.norm (ContinuousAt.sub (Continuous.continuousAt (ContinuousMap.continuous u)) continuousAt_const)))
 has type
  Filter.Tendsto (fun x => 2 ^ m * ‖u x - ?m.330‖) (nhds ?m.342) (nhds (2 ^ m * ‖u ?m.342 - ?m.330‖))
but is expected to have type
  Filter.Tendsto (fun s => 2 ^ m * ‖u s - u t‖) (nhds t) (nhds 0)
```

第二次指定了错误的常量参数名 `(c := u t)`。错误原文：

```text
../formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean:97:79: error: Invalid argument name `c` for function `continuousAt_const`

Hint: Perhaps you meant one of the following parameter names:
  • `X`: c̵X̲
  • `Y`: c̵Y̲
  • `x`: c̵x̲
  • `y`: c̵y̲
  • `U`: c̵U̲
```

最终参数名为 `(y := u t)`。第三轮直接 Lean 检查退出 0，输出 0 字节。
随后加入的连续词坐标定理也通过检查；最终模块五个 theorem 全部标准三公理。

## 读取路径的不一致（不是证明失败）

brief 引用的 owner 分支文件不在本 checkout：

```text
cat: formalization/NSFormalization/Section4/A01/ConstructorPieces.lean: No such file or directory
```

没有到其他工作树取文件；直接消费本树 `EulerPairing`、`OrderTwoCap`、`L2Descent`。
`rg -n 'CarrierConstructorFull' research/A01` 当时无输出、退出 1；已读的
`REVIEW_SLICE_WIRING.md` §3(b) 实际是 `CarrierConstructor`。

误把声明名拼成文件名：

```text
rg: formalization/NSFormalization/Paper3/AngularBoundedRepresentative.lean: IO error for operation on formalization/NSFormalization/Paper3/AngularBoundedRepresentative.lean: No such file or directory (os error 2)
```

随后按文件名和声明搜索定位 `Paper3.angularBoundedRepresentative` 于
`Paper3/AngularTameProduct.lean`，并读其定义；它组合 `sobolevBoundedRepresentative` 与角频率变换。

## 未当作已证路线的候选

这些是读签名排除的循环使用，不是失败的 Lean 草稿：
`A04.timeDeriv_isSobolevDatum` 需要已光滑的 datum 路径与经典解；
`C01.residualPath` 也需要经典解；`D01.exists_smoothL2Field_of_memHInfty`
要求输入代表元本来就 `ContDiff ℝ ∞`。R2–R4 的精确缺口见 B1_LADDER.md。
已按要求 grep 全部 D01/A03/A04/A01/C01，再读候选；没有声称仅凭搜索命名就能证明树里不存在某结果。

没有尝试超心跳、占位证明或新增公理；没有改既有模块。
