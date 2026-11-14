# BTnSS 的固定行数 BMS 上界 · [English](README.md)

本目录收录的纸面论证以如下上界为目标：对每个有限 $n\ge2$，将 **strong BT*(-1)Y-nSS v2 的整个标准域**保序嵌入一个固定标准 BMS 节点以下。关键步骤仍在补全和严格核验，下面的不等式目前不作为已完成认证的结论。记

$$
B_r=(0^r)(1^r),\qquad U_r=(0^r)(1^r)(2^r)(3^r),
$$

则

$$
\boxed{\lim(\mathrm{BTnSS})\le |U_{n+1}|<|B_{n+2}|.}
$$

右端 $|B_{n+2}|$ 是**标准 $(n+1)$ 行 BMS 的上确界**。中间的固定界 $U_{n+1}=B_{n+2}[3]$ 采用冻结的短基本列，不随源种子、嵌套深度或项大小改变。

原稿将其记录为完成并经自审的纸面证明；**当前审计不再无保留沿用这一完成判定**。
尚未发现推翻主结论的反例，但标准域块不变量、完整编码运输及具体覆盖仍有实质性核验义务，
不能预先认定只是 Lean 翻译困难。原稿保留作研究来源，当前证据范围以独立 Lean 项目为准。
没有声称等号、像为初段或逐指标交换基本列。拟议论证使用 BTnSS 的有限不变量与 Hunter 的 BMS 良序定理，
不以旧 BTnSS 的 I3／almost 2-huge 模型解释为前提；这里不主张最小公理体系。

**仅论 BT3SS 也尚未完成该上界证明。** `d=2` 只将中间数值行条件减为 `SB₁`，不消除
任意深度的附属森林、标准域块序保持及目标标准性问题。严格关闭祖先对的完整块插入支配现已核验，
但不等于最终的实际块序不等式。四行裸矩阵编码保序且有统一裸界也已核验，
但尚不能据此推出 BT3SS 的序型小于 BMS 极限。这不是对外部 BT3SS 独立良序证明的反驳。

## 阅读顺序

2026-10-22：已新增独立的 [Lean 部分形式化项目](../../lean/BTnSSBMS/README.zh-CN.md)，
核验具体语法、父链与完整键、编码线性长度界，以及条件性的“覆盖推标准性”。
续接已核验零键绑定保持及兜底分支不可达、有限字最末孔引理、任意维种子展开公式；
已写出完整源展开，并把24条外部路径升级为 Lean 内的有限可达证书。
进一步已核验所有种子可达源项的编码统一小于 `U_(n+1)` 的**裸矩阵界**，
以及真实递归中绑定栈按键和高度排序、前缀截取、第 `i` 个绑定高度恰为 `2*i`，
并核验真实指针见证与键高度比较分支。实际 BMS 的逐级父链、祖先激活、
非负坐标差和已定义展开的裸字典序严格下降也已核验。
本轮补齐了[首对角引理的 Lean 版本](../../lean/BTnSSBMS/src/BTnSSBMS/BMSBlocks.lean)：
使用实际父表、完整块与变基，只依赖 BN 及更低行的 SB，没有循环使用当前行 SB。
另已核验数值合法 BMS 的展开总性、完整块的后裔锥刻画，以及首副本和变基前缀的精确一致性。
全递归作用域及保存绑定的实际键行祖先关系也已证明。
普通有限数值合法源的完整 d+2 行编码合法性已经接通，包含键行／标签行；
源有限条件的标准域保持性和完整编码保序现已接通；覆盖及目标标准性仍未完成，不能声称完成上界。
续接核验了全部源对角种子的有限合法性、实际删除／特殊分支的总性及合法性保持，
以及所有已定义零指标展开的合法性保持。低类第一份新首的实际父运输已接到原 `shift`／`delta`；
随后已核验任意嵌套普通无孔材料的完整合法性、从实际选根构造第一份入口，
以及由前一份运输状态构造下一份数值接缝；最高键父标注不改变数值激活也已证明。
实际最末孔位置及其上下文运输、任意深度拼接和根模板的第零后裔区间现已核验。
低类任意份数复制已在正数类及零类同森林条件下接通，初始入口和差向量由实际选根构造，
并已装回原根模板；没有把后续副本合法性或所属边界当作假设。
最高类任意有限份数的实际复制及每份首列表替换也已接通，首次捐赠从原终端森林
删去末森林得到，后续捐赠由前一阶段的运输状态推出。
原 `locateRoot`/`spine`/`drop` 的数值片段已对应到实际上下文；停止层与模板孔一致。
真实最高父选根排除开放所属列表，由此证明最高类根片段必有尾部，不再外加此假设。
根标记片段、原可见根向量和差向量现已精确对应；实际低类选根也已接到数值父表。
`expand_positive_low_finiteLegal` 对原函数所有成功返回的正数低类步骤证明全项有限合法性保持。
最高键父的实际数值祖先解释、原捐赠的完整激活历史及最高类全项拼接也已接通；
`expand_high_finiteLegal` 对任意正维数中成功返回的最高类步骤证明全项有限合法性保持。
最新续接证明最高键父存在性和低类停止列的叶性；零类若跨出森林会触发更早的特殊停止，
因而其根和孔必同森林，完整零类围栏及全项拼接随之闭合。
`standard_finiteLegal` 已对所有标准源项证明有限合法性，编码的完整 d+2 行合法性不再附加源条件。
`expand_total_finiteLegal` 进一步对任意正维数、任意有限合法输入及任意指标证明实际展开总有结果且仍合法，
`standard_expand_total` 将此结论接到整个种子可达域。尚未证明连续展开终止、剩余 SB/G 块序条件、
具体覆盖或目标标准性。
最新的[原展开严格下降](../../lean/BTnSSBMS/src/BTnSSBMS/SourceDescent.lean)对任意正维数、
有限合法非空项及任意指标证明源递归比较严格变小，覆盖全部实际分支和任意有限嵌套深度。
实际低类首副本在选中坐标处下降；最高类首坐标相等而首附属列表严格删去末槽。
因此非空项不可能在一次展开后经有限路径回到自身，实际原始矩阵编码也随源展开严格下降。
这补齐延迟改写论证的一项前提，**仍不证明完整块序保持、目标标准性或无穷展开终止**；
原始矩阵比较下降不等于由真实 BMS 基本列模拟。
[HW 的全分支闭合](../../lean/BTnSSBMS/src/BTnSSBMS/SourceHWClosure.lean)现已完成：
`standard_HW` 对所有正维数中所有种子可达式证明，每列的附属森林列表递归不增。
低类包括第零类，最高类精确使用前一阶段的删末槽捐赠；末孔替换的严格下降保证其不超过先前森林。
证明不假设 BN、SB、G，也未把 HW 放入标准性的定义。它消除了一项标准域闭包义务，
但不证明剩余块序条件、目标标准性或主上界。
[BN 的定义](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBN.lean)现已精确限定为同森林、
实际同第零父的完整块比较，并证明所有对角种子满足它。
末列删除和末附属列表改小的保持已证明；
[特殊分支](../../lean/BTnSSBMS/src/BTnSSBMS/BNSpecial.lean)覆盖实际停止层和任意份数，
[全部零指标分支](../../lean/BTnSSBMS/src/BTnSSBMS/BNPruning.lean)也已接回原展开规则。
[完整块运输](../../lean/BTnSSBMS/src/BTnSSBMS/RelocationBlocks.lean)另证明在合法运输入口下，实际数值复制与
第零块截取交换。
[真正的共同入口归约](../../lean/BTnSSBMS/src/BTnSSBMS/SiblingEntry.lean)现将较早同父列向后移过上下文间隔，
并证明其全部父层和整段语法合法性不变；
[跨入口完整块比较](../../lean/BTnSSBMS/src/BTnSSBMS/SiblingComparison.lean)及实际后缀入口恢复，进而给出
[完整普通运输的 BN 保持](../../lean/BTnSSBMS/src/BTnSSBMS/BNRelocation.lean)，包含任意深度附属森林。
[首列组装](../../lean/BTnSSBMS/src/BTnSSBMS/BNRootCopy.lean)还覆盖实际强制复制新首，
第一份低类复制的入口状态由实际父选择构造。
[正类围栏拼接](../../lean/BTnSSBMS/src/BTnSSBMS/BNSplice.lean)现已处理任意孔深度下的全部新外部第零同父块，
[正数低类迭代](../../lean/BTnSSBMS/src/BTnSSBMS/BNPositiveCopies.lean)逐份推导真实围栏及终端比较，
再[装回冻结规则的整个源分支](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBNPositive.lean)。
`ordinary_positive_expand_BN` 覆盖 `0 < cap < d`，包括 BT3SS 的 `cap=1` 分支，
不限制森林深度或复制份数。
[最高类 BN](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBNHigh.lean)现已接通实际前一阶段捐赠的严格接缝；
[第零类 BN](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBNZero.lean)通过完整首根块等式，保留根前同父比较，
再提升至整个外层。[全部分支闭包](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBNClosure.lean)的
`standard_BN` 对所有正维数、所有实际种子可达式证明 BN；标准性定义不假设 BN，证明也不假设 SB/G。
**源 BN 已完成；目标 BMS 的全部 BN/SB、标准性及完整上界仍未完成。**
[普通复制的部分变基比较](../../lean/BTnSSBMS/src/BTnSSBMS/PartialRebaseCopyComparison.lean)
现已对冻结的实际复制保持整个三值比较结果，包含任意深度森林和完整根块。
普通复制首的精确父对应在证明内构造，不从祖先保持擅自推出。
此结论不覆盖强制根、末端实际改写或跨副本的 SB 组装。
[所属捐赠键引理](../../lean/BTnSSBMS/src/BTnSSBMS/DonationInternalKey.lean)另证明：
若内部列的键已经不超过“捐赠键后接空森林”，则它严格小于捐赠键；
递归尺寸只用于排除等号，不代替键比较。这些仍是尚未闭合的源 SB/G 保持证明的局部材料。
[源 SB 定义及种子证明](../../lean/BTnSSBMS/src/BTnSSBMS/SourceSB.lean)现已包含真实开放所属列和完整历史块，
所有对角种子满足所有适用层的 SB。[原最外层零列删除](../../lean/BTnSSBMS/src/BTnSSBMS/SBDeletion.lean)
通过幸存块不变及全部递归历史更新证明保持性。其余展开分支及整个标准域的 SB 闭包仍未完成。
[同级跨副本排除](../../lean/BTnSSBMS/src/BTnSSBMS/SBCopyAncestry.lean)现从真实目标祖先关系和
原下一份根的父表推出所需源路径；底层精确父反射不要求例外强制根也具有普通运输父。
[精确嵌套复制](../../lean/BTnSSBMS/src/BTnSSBMS/ExactCopyHole.lean)现沿任意深度的真实孔路径
推出普通位置父精确，并保留可见映射前缀，仍明确排除强制根。
[重启间隙论证](../../lean/BTnSSBMS/src/BTnSSBMS/ExactCopyBarrierPath.lean)再推出跨副本祖先必须经过新根。
[连续副本排除](../../lean/BTnSSBMS/src/BTnSSBMS/SBConsecutiveCopies.lean)构造两侧实际孔及原重启，
在 `0 < 复制级 = 所检行 < d` 时排除较早普通列与下一副本所代表的可见列及末端的 SB 比较对，
不外加源路径、父精确或根屏障路径。[相邻复制根](../../lean/BTnSSBMS/src/BTnSSBMS/CopyRootChain.lean)
另已证明在复制级以下各行形成祖先链。
[真实孔区间连续性](../../lean/BTnSSBMS/src/BTnSSBMS/CopyHoleDensity.lean)现由原复制跨度、
严格递增及末端对齐推出连续平移，并证明整个根至孔可见区间无遗漏。
[任意有限份孔迭代](../../lean/BTnSSBMS/src/BTnSSBMS/CopyHoleRun.lean)构造实际复制的固定前缀及根链，
再由[非相邻副本排除](../../lean/BTnSSBMS/src/BTnSSBMS/SBSeparatedCopies.lean)覆盖隔着任意有限份复制
的完整可见区间，条件仍为 `0 < 复制级 = 所检行 < d`，较早比较方仍限普通位置。
最终拼接材料全部作用域入口的枚举、较早强制根、其他所检行、捐赠及末端改写块比较仍未完成，
不等于源 SB 已全分支闭合。
[强制根完整块变基](../../lean/BTnSSBMS/src/BTnSSBMS/CopyRunRootBlock.lean)进一步对实际孔迭代中
任意正数副本间隔证明：早先未拼接模板的完整根块变基后，恰为后来模板的根块。
所需作用域、固定前缀、祖先链及共享父由实际运行推出；任意深度附件与完整尾部均保留。
[末孔替换运输](../../lean/BTnSSBMS/src/BTnSSBMS/RelocationSplice.lean)另在真实进入上下文中
证明规范数值运输与任意末孔替换交换。未拼接模板的等式本身不等于完整历史块的 SB 不等式；
后述完整复制串定理现已处理强制根配对。
[真实历史副本变基](../../lean/BTnSSBMS/src/BTnSSBMS/CopyRunSplicedMaterial.lean)现已直接处理
正低数值类中的完整原 `copies` 结果：早先块变基后，恰为后来模板接上规范运输后的
整个剩余副本串的根块，涵盖任意有限副本间隔。替换材料合法性及所属屏障由实际完整结果提取。
[固定相位的份数单调性](../../lean/BTnSSBMS/src/BTnSSBMS/CopyCountOrder.lean)也已证明。
[完整复制串交换律](../../lean/BTnSSBMS/src/BTnSSBMS/CopyRunNaturality.lean)现已证明运输后的剩余串
等于整份相位平移后的副本串：每个接缝的实际孔映射复合、高行父精确性与下一次重置均在归纳中构造。
[实际复制串变基](../../lean/BTnSSBMS/src/BTnSSBMS/CopyRunRebase.lean)由真实孔迭代取得入口条件，
涵盖任意正有限间隔，并在后来份数不更多时给出强制根之间的 SB 不等式。
这仍不覆盖全部源 SB 配对、捐赠及完整源展开的组装。
后续又核验了严格递增的位置代表，并接通数值首差到完整编码的严格比较；
完整键归一化对任意深度有限合法森林恰保持原附属列表的比较结果。
两新键落在同一绑定空隙时的森林主体及提前退出边界现已由互递归证明闭合：
`encode_strict_order` 对任意深度有限合法材料证明完整实际编码严格保序。
`standard_compare` 与 `standard_injective` 接通全部源标准项的精确比较及编码单射性。
这只是到原始固定行矩阵的保序单射，仍不代替全部块序、覆盖和目标标准性。
又已对完整编码证明键行父只能是定义列或登记过自身的绑定代表，并从实际执行追踪全部森林槽。
槽只保存更早的绑定，因而在任何后续追加后均没有严格键行后裔；标签2的保护列也没有。
这两项已接到全部源标准项，不再依赖理想化父表，但还不是穷尽全部目标块对及其不等式。
最新续接按实际编码追踪源列首次输出，证明其数值父为标签0的位置，而辅助列在所有数值行
共享标签1或2的父。由此整个标准域的中间 SB 对只能以两个首次输出为端点，第零行兄弟对
不能混合首次输出与辅助列；仍需源作用域／整块对应及变基后的块不等式。
保存绑定的源来源现已对全执行证明：每次查询的最近位置来自唯一的可见源列，
它严格更早、位于最高数值祖先链上，且不是开放的森林所属列。
森林进出保持此性质，不泄漏内部绑定。
实际部分变基入口现已构造，整份材料的有限合法性也已接通；分别追踪复制历史和归一化历史，
证明变基根完整键恰保持，以及两份材料经过同一次变基后比较不变。
后续桥梁现已接通：关闭列表移植合法且保持完整键；移植与数值运输按整份语法交换，
因此不同入口的祖先／当前键比较保持。规范运输已证明等于原激活平移复制，
覆盖同一副本中未改附属列表及固定外部祖先，并保留明确的有限入口条件。
保存绑定与其最近源列的实际附属列表现已逐次识别，覆盖所有真实查询，包含原列表的有限合法性
以及当前查询的数值入口。从这些材料明确重算键后，较小键筛选、等键查找和首输出键行高度
均保持；同副本未改列表与固定外部列表也已接到原规则复制。
最新续接将材料对应接到两个真实执行：在明确的数值入口及初始绑定配对条件下，新建／复用判断保持，
保存最近位置、进入森林、关闭森林恢复外层环境均保持绑定的键／高度对应。
完整互递归证明实际新增键行／标签行逐列相同，故新增列数也相同；最终外层位置映射、数值视图
和所有可见绑定对应由证明构造。结论也已接回冻结的原激活平移复制，而非只适用于替代算法。
中间行部分变基的根入口现已接通：固定旧前缀的实际材料键不变，真实根父搜索读取同一保存环境，
完整根键相同，因此新建／复用分支相同。根处理后的可见绑定配对由证明构造；
森林槽逐次从固定旧环境初始化，再使用完整递归运输，覆盖所有嵌套森林及外层尾部。
`partial_rebase_encode_control` 对冻结的原激活复制证明真实新增键行／标签行逐列相同，
不再外加根查询相等、分支一致或入口绑定配对。
实际首次输出快照及其有限合法性、数值视图、材料来源现已对整个执行取得。
每个当前可见源位置都有其真实原入口，源／可见位置／材料恰为当前相应前缀，
包括由槽代表的开放所属。因此 `standard_visible_partial_rebase_control` 从实际源根几何
构造所需历史前缀并给出完整控制行运输；已识别来源的端点共享父也能反推回源。
最新续接以辅助父路径的数值纤维证明可见来源恢复：任意中间数值行 SB 对的左端确为右端作用域中的源位置，
源祖先关系及共享截断父均由实际目标关系推出，不以时间先后代替作用域包含。
这接通全部这类实际目标对的完整键／标签行运输，且增量列数相同。
对应来源的各数值行祖先资格双向等价，实际源／目标激活阈值也相同；
变基首列低行变为目的位置的实际编码值，高行保持旧值。
继而已证明全部内部数值列的运输，并与控制行接合：对全部实际中间行比较对，
完整局部输出的全部 d+2 行恰等于原 BMS 的一次复制。
完整块边界也已另证：每个真实入口的第零块不能跨出该次局部执行，
且祖先敏感的第零行平移保持根块精确长度。因此
[`standard_intermediate_pair_block`](../../lean/BTnSSBMS/src/BTnSSBMS/CompleteBlockTransport.lean)
给出变基前后**实际完整目标块**的相等，而非将整个词法后缀冒充一个块。
源完整块的编码边界现也已证明：外层截断保留各列全部附属森林，编码恰好填满目标根块。
[`standard_intermediate_source_block`](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBlockTransport.lean)
把原规则作用于完整源块的变基接到实际目标块；
[`standard_intermediate_block_compare`](../../lean/BTnSSBMS/src/BTnSSBMS/SourceBlockComparison.lean)
从实际入口环境进一步证明两边的三值比较完全相同，未假设源 SB 不等式。
[`关闭列块公式`](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingBlockEncoding.lean)进一步识别每个实际入口
恢复后的代表块，包括新定义的关闭 P：从完整源块编码中去掉关闭列之前的输出，
所得恰为全局完整关闭块。这不把关闭 P 与首次输出混同，也未证明最高行全部比较。
最新续接已将所有自登记代表识别为真实源入口的关闭列，并把零标签列穷尽为关闭代表或森林槽，
正标签列穷尽为新定义列或其保护列。由正标签列实际键父与标签父相同，
[`standard_top_pair_classes`](../../lean/BTnSSBMS/src/BTnSSBMS/TopRowEndpointClasses.lean)
对整个标准源域排除最高标签行比较中的正标签端点，构造左端关闭入口和右端关闭入口／槽的穷尽分类。
它未假设源 SB/G 或目标标准性，也未证明这两类的块不等式。
对 P/P 情形，[真实关闭入口](../../lean/BTnSSBMS/src/BTnSSBMS/VisibleClosingOrigins.lean)
现已恢复较晚源作用域中的非所属祖先及原关闭位置；
[完整保存环境](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingFrameExtension.lean)证明旧键及全部指针逐项保留，
后端只追加非空绑定串，高度差恰为追加长度的两倍；
[完整键比较](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingKeyOrder.lean)还证明键严格递增。
这些结论覆盖实际递归编码，不假设源块序条件，但仍不替代完整块的插入支配不等式。
[插入查询](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingQueryInsertion.lean)现已证明实际关闭环境中的三段高度公式，
包括插入区间内“旧新建／新复用”的严格比较；[完整头保存](../../lean/BTnSSBMS/src/BTnSSBMS/InsertionHead.lean)
已接到真实森林返回后的键表。
[查询祖先判据](../../lean/BTnSSBMS/src/BTnSSBMS/QueryAncestry.lean)及其
[反向恢复](../../lean/BTnSSBMS/src/BTnSSBMS/QueryAncestorRecovery.lean)现已覆盖标准源域的每次真实查询首输出：
旧代表是键行祖先，当且仅当它保留在本次查询的较小键环境中；不在当前环境就不能获得激活平移。
[重算键插入](../../lean/BTnSSBMS/src/BTnSSBMS/RekeyInsertion.lean)和
[实际激活高度界](../../lean/BTnSSBMS/src/BTnSSBMS/InsertionActivation.lean)允许搬运后完整键发生改变。
这些局部界仍以带激活门槛的拼接区间为前提。
[有界键拼接](../../lean/BTnSSBMS/src/BTnSSBMS/KeySplice.lean)、
[完整头保持](../../lean/BTnSSBMS/src/BTnSSBMS/SplicedSaving.lean)及
[外层执行归纳](../../lean/BTnSSBMS/src/BTnSSBMS/EncoderSpliceTransport.lean)现已证明：
保存环境中的未匹配键只会从初始集合中删减，完整头的两侧分支和内部输出长度可以不同。
[实际关闭入口](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingSpliceEntry.lean)从严格关闭祖先对构造初始关系，
[完整外层尾部](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingSpliceTransport.lean)将其保持到后续全部可见位置，
包含森林返回及后续重新查询外部父；不再假设存在初始配对或实际执行的环境拼接。
[原根门槛](../../lean/BTnSSBMS/src/BTnSSBMS/RootedSplice.lean)现已将该关系加强：
每个未匹配键都高于一个仍指向原根的绑定。真实过滤和保存保持它，
[真实入口及外层尾部](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingRootedTransport.lean)从标准关闭对构造并保持它，
[森林槽](../../lean/BTnSSBMS/src/BTnSSBMS/RootedSlots.lean)进入也保持它。
[查询结论](../../lean/BTnSSBMS/src/BTnSSBMS/RootedQuery.lean)直接使用实际 BMS 激活阈值：
未激活时高度恰不变；达到最大平移量时全部插入键必须保留且两侧新建／复用分支相同。
[真实首列比较](../../lean/BTnSSBMS/src/BTnSSBMS/RootedHeadComparison.lean)现已给出严格较小或相等且分支一致的二分；
[辅助列](../../lean/BTnSSBMS/src/BTnSSBMS/FreshShift.lean)的完整行对齐条件也已由实际激活推出。
[真实关闭入口](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingRowEntry.lean)同时构造原根门槛和实际逐行差向量。
[完整头决策](../../lean/BTnSSBMS/src/BTnSSBMS/RootedDecision.lean)证明首列严格差异可推广到任意后续输出，
至少一侧复用时已比较完整头部。
[完整互递归比较](../../lean/BTnSSBMS/src/BTnSSBMS/RootedComparison.lean)现已补齐双方都新建时的森林和外层尾部，
允许严格差异后的长度不同，兄弟森林各自恢复所属的进入环境。
[真实关闭入口](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingInsertionComparison.lean)构造全部初始化条件，
[精确块截取](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingBlockSlice.lean)将输出区间接到真实 BMS 变基。
[`standard_closing_block_insertion`](../../lean/BTnSSBMS/src/BTnSSBMS/ClosingBlockComparison.lean)
因此对全部标准关闭祖先对证明：运输旧块尾到新入口所得到的完整编码，不超过旧目标块的实际变基。
这里比较的是搬来的旧材料，尚须证明新入口自己的块不超过它，不能冒充最终的目标 SB。
源 SB/G 的标准域保持、键行端点分类及最高两行块不等式、全部目标 BN/SB、
具体覆盖及目标标准性仍未闭合；比较归约不等于证明所需比较结果必非“小于”。
最近一次完整构建已核验297个模块、1777份公理报告，包含最近四十九个部分变基运输、源 SB、精确孔、区间连续性、有限副本、强制根块、末孔替换、完整拼接材料、份数比较、接缝运输、孔映射相容及完整复制串模块的127个公开定理；
源码哈希、依赖顺序和报告完整性已另行复核。
此统计不表示主上界定理完成。
**完整标准域保序嵌入与上述序型上界尚未成为 Lean 定理。**
原文及历史检验收据保持不变，不以新的局部核验回溯认证原稿的全部主张。

- [中文主证明](upper-bound.zh-CN.md) · [完整英文主证明](upper-bound.md)。
- [冻结定义与标准域有限不变量](source-finite/definitions-and-invariants.zh-CN.md)：摘录旧 BTnSS 主文第1至3节，配套18份有限组合引理；后续模型论部分不收入。
- [省略所属绑定的上下文编码](lemmas/context-encoder.zh-CN.md)：有限性、精确父表、固定入口保序、中间行运输。
- [所属入口键下降](lemmas/owner-entry.zh-CN.md)、[部分变基的键比较](lemmas/partial-key-comparison.zh-CN.md)。
- [跨叶延拓](lemmas/cross-leaf.zh-CN.md)、[最高两行的块运输](lemmas/top-row-transport.zh-CN.md)、[首对角引理](lemmas/first-diagonal.zh-CN.md)。

主证明与总览为中英双语；配套引理完整保留中文论证，没有把英文导读冒充全部引理的译文。历史文稿的完成声明保留作来源记录，不代表当前审计认可；当前证明状态以上述说明为准。

## 行数与非标准式的区别

源的数值维数为 $d=n-1$，编码使用 $d+2=n+1$ 行。例如

$$
\lim(\mathrm{BT3SS})\le |(0000)(1111)(2222)(3333)|<|(00000)(11111)|.
$$

**这一 BT3SS 特例同样尚未完成证明。** 固定 $d=2$ 会把中间数值块条件减少为 SB₁，
但不会限制附属森林的嵌套深度，也不会省去源块序保持及具体标准性覆盖。
增键环境的完整块插入支配现已补齐；新入口自己的块与搬来材料之间的不等式仍须由源块序条件推出。
原 BT3SS 专门文稿的最终块序与覆盖论证仍未闭合，不能因为不再量化维数就视为已经补齐。
这是 BMS 上界证明的状态，不是对另一个 BT3SS 良序性证明作出否定。

首列为零的数值合法 $r$ 行矩阵，补零后在裸字典序上小于 $B_{r+1}$，但这**不自动给它赋予该界以下的序数**。原始合法矩阵的字典序甚至含有

$$
(0)(1)>_{\mathrm{lex}}(0)(0)(1)>_{\mathrm{lex}}(0)(0)(0)(1)>_{\mathrm{lex}}\cdots.
$$

这不是声称存在基本列展开降链。对本次编码的像，拟议证明还需建立全部有限块条件，再由有限覆盖及标准 BMS 良序性推出目标标准性，不能用“只有固定行数”跳过这一环节。

## 来源、检验及收录边界

规则固定在 NER 提交 `c539d8f68c5553da2d681c1251ea443b6b735e62`：

- [strong BT*(-1)Y-nSS v2](https://github.com/SmileLee-lyx/ne-rewritten/blob/c539d8f68c5553da2d681c1251ea443b6b735e62/src/notations/BM-like/Minus1_Y_nSS-series/BT_star_Minus1_Y_nSS-v2.ts)。
- [BMS 源文件及默认 BM4 短基本列](https://github.com/SmileLee-lyx/ne-rewritten/blob/c539d8f68c5553da2d681c1251ea443b6b735e62/src/notations/BM-like/BM.ts)。
- Rachel Hunter，[《Well-Orderedness of the Bashicu Matrix System》](https://arxiv.org/abs/2307.04606)，提供目标 BMS 的良序定理。

[收录清单](MANIFEST.json)记录来源与收录后的哈希、主文摘录行范围、编辑项目及冻结规则哈希。此次导入26份数学文稿和一份仅统一为 LF 换行的[历史有限核验记录](verification.json)。不收录私人 PDF、上游实现及旧实验脚本，不新增展开器或 Lean 项目。文中的实验脚本名、收据内原有的 `repository_changes` 字段均描述当时研究状态，不是这次发布状态。

核验记录区分真实标准路径样本、原始数值样本与原始有限条件样本，保留逐项上限及一次超时退出的范围；不同批次有重叠。它们用于寻找实现错误，不能代替全称证明。可从仓库根目录运行：

```sh
node research/btnss-bms/tools/validate.cjs
```

这只验证收录文件、链接、哈希及记录一致性，不是数学证明检查器。附带收录脚本需要显式传入原工作区，只供来源复核；阅读和验证新克隆的仓库不依赖原工作区。
