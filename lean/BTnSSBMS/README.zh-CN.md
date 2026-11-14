# BTnSS 固定行数 BMS 上界：Lean 形式化进度 · [English](README.md)

[纸面证明](../../research/btnss-bms/upper-bound.zh-CN.md) · [编译核验记录](VERIFICATION.json)

**整个上界定理尚未完成证明及形式化。** 原稿中的完整块运输、标准域不变量和具体覆盖仍须补证，
不能将目前的困难仅归结为 Lean 翻译。本独立项目已把若干具体定义和引理交给
Lean 4.33.1 核验；没有把尚缺的核心结论写成公理。原有七个记号的 Lean
项目、依赖和核验记录均不受影响。

**只取 BT3SS（`d=2`）也尚未闭合这个 BMS 上界证明。** 固定维数将中间数值行条件减为
`SB₁`，但不限制附属森林的嵌套深度。源 BN 已由 `standard_BN` 对整个标准域证明；
剩余 SB/G 块序保持、具体覆盖和目标标准性仍需证明。
严格关闭祖先对的完整块插入支配现已核验，尚不能替代这些步骤。四行裸矩阵保序编码及统一裸界
也不能替代它们。这一判断针对本项目的
BT3SS→BMS 比较论证，不是对外部 BT3SS 独立良序证明的反驳。

最终要证明的仍是：对 `d = n - 1`，

\[
\lim(\mathrm{BTnSS})\le |U_{d+2}|<|B_{d+3}|,
\qquad U_r=(0^r)(1^r)(2^r)(3^r).
\]

## 已核验的部分

- [语法](src/BTnSSBMS/Syntax.lean)：数值列、附属森林列表、对角种子、
  递归比较；比较返回相等时，结构确实相同。空森林槽与没有槽严格区分。
- [父链](src/BTnSSBMS/Parents.lean)：有限数值父搜索和森林退出时的上下文恢复；
  父指标严格小于所在列的上下文指标；去除父标注后恢复原项，节点数与槽数不变。
  追加实际算出的父标注保持上下文合法性；沿父链搜索不会触发防御非法父指针的分支。
- [逐级父链](src/BTnSSBMS/ParentChains.lean)、[激活语义](src/BTnSSBMS/Activation.lean)、
  [坐标差](src/BTnSSBMS/ParentValues.lean)：实际算出的高行祖先也是所有低行祖先；
  BMS 的激活阈值恰好等于指定上限内的逐行祖先资格。所有根到端点的相应坐标严格增加，
  因此复制所用自然数减法确实给出原差值。这些结论对任意原始矩阵成立，不假定标准性。
- [搜索几何](src/BTnSSBMS/SearchGeometry.lean)：搜索只依赖当前前缀，所有被跳过的
  低行祖先都满足相应的坐标下限；第零父的后裔恰好组成坐标高于根的连续区间。
- [逐行记录链](src/BTnSSBMS/RowGeometry.lean)：高行祖先资格等价于低行路径上的
  相应坐标屏障；从该祖先的任一高行后裔开始搜索“祖先值加一”，实际算法恰好返回该祖先。
  [父运输](src/BTnSSBMS/NumericalTransport.lean)据此证明首次输出头部的前 d 行父精确正确，
  而不只是证明所用指针处于有效范围内。
- [作用域恢复](src/BTnSSBMS/NumericalScope.lean)：`source_numerical_view` 对任意有限输入，
  在明确的 `ForestSeparated` 条件下，证明完整实际编码保持数值祖先关系；
  **覆盖所有嵌套森林与退出后的外部作用域恢复**，不再把递归保持性留作前提。
  该有限条件只要求每个附属森林的外层列第零坐标严格高于其所属列，并递归要求同样的性质。
  [路径伸长](src/BTnSSBMS/ViewExtension.lean)、[辅助父](src/BTnSSBMS/AuxiliaryParents.lean)、
  [森林围栏](src/BTnSSBMS/ForestFence.lean)和[槽／关闭列](src/BTnSSBMS/ForestScope.lean)
  分别处理实际 D、H、槽和关闭 P 的数值父链。
  `NumericalView` 现还保证位置代表严格保持先后；追加、森林进出、复制首项及接缝重置
  均已核验这一更强条件，而不把祖先保持误当作自动排除位置合并。
- [数值单位步](src/BTnSSBMS/NumericalUnits.lean)：在同一有限条件下，
  `source_unitSteps` 证明**每一个实际输出列**的前 d 行都是“无父为零、有父为父值加一”。
  不假设源项的单位步条件，也没有有限深度或规模上限。
  这两个模块只处理前 d 行；新增键行／标签行由下面的完整合法性证明处理。
  `ForestSeparated` 现已由下面的 `SourceFiniteClosure` 在整个源标准域上取得。
- [保存绑定的祖先链](src/BTnSSBMS/KeyScope.lean)：`source_framesAncestral` 证明每个已保存绑定
  的最近实际位置、已有定义位置都是保存列的实际键行祖先，覆盖完整递归执行。
  [祖先截取](src/BTnSSBMS/FrameAncestry.lean)、[定义／复用入口](src/BTnSSBMS/KeyEntries.lean)
  与[森林键作用域](src/BTnSSBMS/KeyForestScope.lean)给出新 D、复用 P、H、槽和关闭 P 的
  计算父关系；[高行搜索](src/BTnSSBMS/KeyParentGeometry.lean)直接调用实际 BMS 搜索。
- [完整输出合法性](src/BTnSSBMS/FullLegality.lean)：`source_numericallyLegal` 证明每个输出列
  的**全部 d+2 行**都数值合法，包含键行和标签行，并推出对该编码矩阵任意一次 BMS 展开
  均有结果。输入前提是有限森林分离，以及每个带附属列表的源列存在最高数值父。
  [源有限合法性](src/BTnSSBMS/SourceLegality.lean)从文稿的普通有限条件——固定宽度、
  数值单位步、带森林所属各坐标为正、森林分离——推出这两个前提。
  `finiteLegal_source_numericallyLegal` 因此不把目标父表、目标合法性或递归保持性当作假设。
  源 FS 的有限条件保持性现已由下面的全分支闭合证明接通。
  **数值合法性仍不推出 BMS 标准性、BN/SB 或保序。**
- [绑定代表自身登记](src/BTnSSBMS/BindingAnchors.lean)证明每个保存的最近位置确实指向
  曾将自己登记为绑定代表的实际列；后续追加不会改变这一事实。
  [键行父类型](src/BTnSSBMS/KeyParentTypes.lean)对完整真实编码证明：每个实际算出的
  键行父都是定义列或这样的绑定代表，涵盖任意森林嵌套与退出后的追加。
  [森林槽叶性](src/BTnSSBMS/ForestSlotLeaves.lean)按原编码追踪全部实际槽，证明它们只保存
  更早的绑定，永远不属于上述父类型。因此 `standard_slot_no_strict_key_descendant`
  对整个源标准域证明槽没有严格键行后裔；标签2的保护列也没有严格键行后裔。
  这补齐了一项目标块分类依据，**不是全部块类型分类或 BN/SB 证明**。
- [数值列类型](src/BTnSSBMS/NumericalKinds.lean)与[实际首次输出轨迹](src/BTnSSBMS/EncoderHeadTypes.lean)
  进一步对完整编码分类：源列的首次输出是新 D 或复用 P，其数值父只会带标签0；
  辅助列的所有数值父为同一个带标签1或2的位置。实际轨迹不把新键的关闭 P 混作首次输出。
  `standard_intermediate_pair_heads` 因此对整个源标准域证明：每个 `0<j<d` 的 SB 比较对
  两端均为源首次输出；`standard_sibling_pair_types` 排除第零行兄弟对混合首次输出与辅助列，
  辅助兄弟则共享全部数值父。**尚需将这些首次输出对对应回源块、核验作用域及变基，
  没有据此声称 BN/SB 的整块不等式已成立。**
- [绑定的源来源](src/BTnSSBMS/BindingSources.lean)与[全执行来源保持](src/BTnSSBMS/EncoderBindingSources.lean)
  现将可见源作用域、正在展开森林的所属列，与目标位置分开追踪。
  `standard_readsSources` 对实际编码中的每次读取证明：保存的最近位置来自最高数值源祖先链上
  严格更早的可见列，且不是任何开放所属列。进入森林时加入当前所属，退出时恢复原所属列表，
  不将森林内局部绑定泄漏到外部；`inherited_source_unique` 还证明源来源唯一。
  `standard_binding_sources` 将完整外层输出的来源与数值视图接到同一个位置代表列表。
  这覆盖任意有限嵌套，不靠样例，也不把数值祖先运输擅自倒推。
  **尚未据此证明整块变基对应或 BN/SB 不等式。**
- [实际部分变基入口](src/BTnSSBMS/PartialRebaseEntry.lean)从中间行比较对的真实几何构造
  数值运输状态：两端共享截断行父，旧根是新位置的低一行祖先。实际重算的新首在低行接新位置的父，
  高行保留旧根的父；原差向量及整份变基材料的有限合法性均在证明内取得，不是假设入口正确。
  这与普通 FS 复制的选根条件不同，未混用两种入口。
- [完整键运输](src/BTnSSBMS/CopyKeyTransport.lean)分别追踪截断复制历史和全维归一化历史，
  证明实际重算后，变基根的完整键恰等于原完整键，包含全部嵌套森林。
  没有声称所有内部列的键也保持不变。
  [同一次变基比较](src/BTnSSBMS/PartialRebaseComparison.lean)进一步证明：从同一个入口变基的
  任意有限合法材料，其三种比较结果均保持；真实部分变基入口在此被实际构造。
  这个同入口结论与下述跨入口结论不同；它们都不单独替代整个编码／整块运输或目标 BN/SB。
- [关闭森林移植](src/BTnSSBMS/ClosedForestTransplant.lean)现已从实际最高数值祖先路径出发，
  将旧祖先的整个附属列表放到当前列。实际重算父、所属分离及所有嵌套森林均保持合法，
  完整相对键恰保持。因此不同前缀中的两个键可归约为同一入口的两份有限合法列表比较；
  没有声称移植结果必标准。
- [规范数值运输](src/BTnSSBMS/NumericalRelocation.lean)由对应父位置重建坐标；
  `relocate_eq_copied` 及森林版本已证明它与原来的激活平移复制完全相等。
  它是辅助证明工具，**未改 FS 规则**。[合成律](src/BTnSSBMS/RelocationComposition.lean)、
  [精确比较](src/BTnSSBMS/RelocationOrder.lean)与[有限合法性](src/BTnSSBMS/RelocationLegality.lean)
  覆盖任意有限深度，森林退出恢复原作用域。
  [移植交换](src/BTnSSBMS/TransplantNaturality.lean)实际推导两条复合位置映射相等，
  进而证明先移植再运输与先运输再移植的**完整语法相等**，不只是根坐标相等。
- [跨入口键运输](src/BTnSSBMS/CrossEntryKeyTransport.lean)据此证明：祖先键与当前键各自在
  原前缀中计算，经过相应数值运输后，小于、等于、大于三种结果均保持。
  [原复制接合](src/BTnSSBMS/CopyKeyComparison.lean)从当前复制状态实际截出祖先入口，
  `copied_ancestor_key_compare` 覆盖同一副本中未被替换的两份附属列表；
  `copied_external_ancestor_key_compare` 覆盖前缀及位置保持不动的外部祖先。
  没有额外假设端点键相等或比较保持。
  这些局部材料定理现由下面的模块接到真实保存绑定的附属列表，但本身不代替整个块运输。
- [绑定附属材料](src/BTnSSBMS/BindingMaterials.lean)区分旧定义指针与最近源代表。
  新建、复用两种情形都证明：保存键恰是最近那一源列的完整附属列表所计算出的键；
  复用情形实际使用原编码的完整键相等测试。
  [全执行材料追踪](src/BTnSSBMS/EncoderBindingMaterials.lean)在每次真实查询中携带原列表及其
  有限合法性。兄弟森林从同一个完整所属列表重新进入，退出恢复原材料上下文。
  `standard_readsMaterials` 同时给出真实数值入口和当前材料合法性，覆盖所有标准源项的
  所有查询，没有深度上限。
- [查询运输](src/BTnSSBMS/QueryMaterialTransport.lean)从这些实际材料重新计算键，证明每个比较
  保持，并推出原 `smaller` 筛选与 `equal` 查找交换；首输出的键行高度也恰保持，包含新键空隙。
  [原复制查询](src/BTnSSBMS/QueryCopyTransport.lean)将同副本旧键识别为真实复制列表的键，
  证明固定外部键不变，并将当前查询接回冻结的激活平移复制。
  真实执行的键／高度对应现由下面的模块保持；这仍不等于全部矩阵／块运输。
- [真实绑定配对](src/BTnSSBMS/FrameCoupling.lean)、[材料延续](src/BTnSSBMS/MaterialStability.lean)
  与[作用域配对](src/BTnSSBMS/ScopedFrameCoupling.lean)分别追踪搬运前后真实状态的键和高度，
  不错误地要求绝对定义／最近位置相同。旧材料在追加后保持，新保存绑定的材料来源更新到当前列。
  [真实查询](src/BTnSSBMS/CoupledQuery.lean)读取搬运后实际最高数值父处的绑定；新建／复用选择、
  较小键列表及首高度由已经证明的材料比较推出，而不假设分支相同。
  [保存与关闭](src/BTnSSBMS/CoupledSaving.lean)接到真实 `headState` 的两个分支，包含任意森林结束后
  恢复入口环境、保存新最近位置；没有把森林内局部绑定留给外层。
- [全执行控制行运输](src/BTnSSBMS/EncoderControlTransport.lean)现以互递归证明：在明确的数值入口、
  实际材料来源和入口绑定配对条件下，规范搬运前后**真实编码新增的键行／标签行逐列相同**，
  任意森林深度、任意外层长度均适用。
  [输出轨迹](src/BTnSSBMS/ControlTrace.lean)直接读取实际矩阵最后两行，因此也推出新增列数相同；
  不是用另一个理想化执行器替代实际输出。
  [完整外层绑定](src/BTnSSBMS/EncoderFrameTransport.lean)构造最终位置映射、两侧实际数值视图及
  结束后的全部可见绑定对应；最终状态不作为前提。
  [冻结复制接合](src/BTnSSBMS/CopyControlTransport.lean)用已证相等性接回原激活平移复制。
  中间行变基的入口配对现由下面的具体根处理构造；其余分支仍需逐项核验。
- [固定前缀材料](src/BTnSSBMS/FixedPrefixMaterials.lean)证明更长走廊不改变旧绑定的完整材料键，
  不将旧前缀到更长前缀的包含关系错误地当作满足末端条件的数值视图。
  [实际根查询](src/BTnSSBMS/PartialRebaseQuery.lean)从中间行变基的真实父链几何证明：
  新旧根读取同一个保存环境，完整查询键也相同，因此新建／复用分支相同。
  [固定前缀保存](src/BTnSSBMS/FixedPrefixCoupling.lean)与
  [实际根配对](src/BTnSSBMS/PartialRebaseCoupling.lean)构造根处理后的全部可见绑定对应，
  包括新最近位置，不假设入口配对。
  [森林与尾部](src/BTnSSBMS/FixedPrefixControl.lean)每次从真实槽初始化，再调用完整递归运输，
  森林退出恢复各自外层作用域。
  [实际部分变基全执行](src/BTnSSBMS/PartialRebaseControl.lean)因此对原激活复制证明：
  **根、任意嵌套森林及外层尾部新增的键行／标签行逐列相同**。
  所需输入为有限合法材料、实际父链几何、两次执行的数值视图与历史状态／可见位置的前缀关系；
  不再外加查询相等、分支一致或初始绑定配对。
  **中间数值行目标对的真实源快照及普通变基的完整块运输现已由下述模块取得；剩余源 SB/G
  不变量、最高两行的块分类与目标 BN/SB 仍未完成；这不是标准域覆盖或完整上界。**
- [实际源快照](src/BTnSSBMS/EncoderEntries.lean)逐次记录源上下文、完整剩余材料、可见位置和真实输出状态；
  投影恰为原先的首次输出轨迹。[快照合法性](src/BTnSSBMS/EntrySoundness.lean)和
  [执行包含](src/BTnSSBMS/EntryExecution.lean)对全部实际记录证明有限合法性、数值视图、材料来源，
  以及入口状态和完整局部结果确为全执行的前缀。所有中间行 SB 端点均取得这样的真实快照。
  时间先后只推出状态前缀，不自动推出源作用域前缀。
  [可见来源](src/BTnSSBMS/EntryOrigins.lean)与[全执行来源保持](src/BTnSSBMS/EncoderEntryOrigins.lean)
  另证明每个当前可见源位置都有其实际原入口，源／可见位置／材料恰为当前上下文的相应前缀。
  这包括由槽代表的开放所属；没有把槽或关闭代表当成首次输出。
  [真实入口变基](src/BTnSSBMS/EntryRebaseControl.lean)据此从实际源根几何推出完整控制行运输，
  不再外加历史状态前缀、可见位置前缀或两侧入口合法性。
  [实际端点父关系](src/BTnSSBMS/EntryParentGeometry.lean)还证明在已确定真实可见来源的前提下，
  目标首次输出共享数值父精确反推为源共享父。
  任意目标祖先对的可见来源及反向祖先资格现由下一项接通；全部整块对应和 BN/SB 仍未完成。
- [数值纤维](src/BTnSSBMS/EntryFibers.lean)记录首次输出到当前代表的实际父路径：
  路径上的辅助列不会引入别的源首次输出祖先。
  [可见纤维](src/BTnSSBMS/VisibleEntryFibers.lean)与[完整执行](src/BTnSSBMS/EncoderEntryFibers.lean)
  对所有嵌套森林进入、退出、复用及关闭保持此性质，并证明可见代表标签为零。
  [来源顺序](src/BTnSSBMS/EntryOriginOrder.lean)证明可见源位置的首次输出严格保序，
  不借用尚未证明的全轨迹单射。
  [反向祖先恢复](src/BTnSSBMS/EntryAncestry.lean)先缩去辅助路径，再沿严格更小的源父指标归纳，
  从任意实际中间行 SB 对构造真实可见源根、源祖先路径及共享截断行父。
  因而 [实际目标对控制运输](src/BTnSSBMS/TargetPairControl.lean)直接适用于全部这类目标对，
  不再要求调用方提供源几何、原入口或历史前缀；两个实际输出的控制行后缀相等且增量列数相同。
  [逐行祖先与激活](src/BTnSSBMS/EntryActivation.lean)进一步证明这些来源之间数值祖先资格双向等价，
  实际 BMS 阈值恰等于源查询算出的阈值。
  [首列数值](src/BTnSSBMS/EntryRebaseNumerics.lean)核验原激活复制的变基根：
  截断行以下等于目的位置的实际编码值，其余数值行保留旧值，不把源坐标与目标坐标混同。
  这组首列定理本身不把完整词法后缀认作完整 BMS 块；内部运输及真实块边界由下面的模块另证。
- [逐行变基轨迹](src/BTnSSBMS/RowRebaseTrace.lean)与
  [可见位置值](src/BTnSSBMS/RowRebaseValues.lean)直接追踪实际父表决定的增量。
  [全执行数值运输](src/BTnSSBMS/EncoderRowTransport.lean)以互递归覆盖每个内部输出列，
  包括保护列、槽、任意嵌套森林和关闭列；不把内部运输当作递归前提。
  [固定前缀入口](src/BTnSSBMS/FixedPrefixRows.lean)和
  [原复制接合](src/BTnSSBMS/PartialRebaseRows.lean)由真实源根几何初始化，接回冻结的激活复制。
  [矩阵运输](src/BTnSSBMS/RebaseMatrixTransport.lean)将其与控制行证明合并：
  `standard_intermediate_pair_copy` 对全部实际中间数值行比较对证明，完整局部输出片段的
  **全部 d+2 行**恰等于真实 BMS 的一次复制。片段终点是局部执行终点，还不是块终点。
- [低退出边界](src/BTnSSBMS/BlockCutoff.lean)与
  [实际入口块闭合](src/BTnSSBMS/EntryBlockClosure.lean)证明每个源入口的完整第零块都留在
  该入口的局部执行内：后继兄弟森林的槽或外层关闭列阻止块越界。
  该结论覆盖整个标准源域及所有嵌套入口，不假设块终点，也不要求 BN/SB。
  `standard_entry_block_ends_before` 进一步用实际反向祖先关系证明：后面的可见源列一旦
  第零坐标不高于旧源根，它的首次输出就已在旧目标块之外，给出源外层截断的真实上界。
  [变基块边界](src/BTnSSBMS/RebaseBlockBoundary.lean)另证明实际第零行祖先敏感平移保持
  根块的精确长度，首个块外位置不会因平移被错误吸入。
  [完整块运输](src/BTnSSBMS/CompleteBlockTransport.lean)据此证明
  `standard_intermediate_pair_block`：对任意 `0<cut<d` 的实际目标比较对，将对应源材料按原规则
  搬到目的入口并重新编码，**所得实际完整 BMS 块恰为原完整块的 BMS 变基**。
  输入不包括源根、历史快照、局部截止点或运输结论；这些均由实际目标关系推出。
  这个等式本身尚未给出块不等式；下面进一步识别完整源块并接通比较。
- [源完整块](src/BTnSSBMS/SourceBlocks.lean)只截断外层尾部，保留各列全部附属森林。
  [源截断边界](src/BTnSSBMS/SourceBlockCutoff.lean)与
  [完整块编码](src/BTnSSBMS/SourceBlockEncoding.lean)证明：截到首个第零坐标不高于根的位置后，
  编码产生的整个新增片段恰为实际目标根块；截断前的内部森林和关闭列全部包含在内。
  [源块运输](src/BTnSSBMS/SourceBlockTransport.lean)将这个边界接到冻结的部分变基，
  `standard_intermediate_source_block` 对全部实际普通中间行比较对给出完整源块编码等式。
  [实际入口比较](src/BTnSSBMS/EntryOrder.lean)从全执行中证明所有入口的零绑定可用性、
  键环境有序性和高度稠密性，不假设目的入口满足比较前提。
  [整块比较](src/BTnSSBMS/SourceBlockComparison.lean)据此证明
  `standard_intermediate_block_compare`：目标变基块与目的块的三值比较，
  **恰等于变基后的完整源块与目的完整源块的比较**，覆盖任意有限嵌套深度。
  **这不是源 SB 保持性：尚须证明源比较从不为“小于”，并处理最高两行、覆盖和目标标准性。**
- [后裔块边界](src/BTnSSBMS/DescendantBlocks.lean)证明第零行后裔的完整块不越过祖先块终点，
  并证明只要整块留在某个实际执行前缀内，在该前缀计算所得块就与全局完全相同。
  [关闭列块](src/BTnSSBMS/ClosingBlockEncoding.lean)据此处理恢复后的实际代表，
  不将新定义的关闭 P 当作源列首次输出。`standard_entry_closing_source_block` 对所有标准项
  的实际入口给出精确公式：编码完整源块后，去掉关闭列之前的输出，恰好留下全局关闭列块。
  定义列及附属森林输出被去掉，关闭列本身与其后的完整块保留；复用单列也包含在内。
  关闭块的变基运输及块不等式仍需另外证明，不能从边界公式直接推出。
- [关闭代表来源](src/BTnSSBMS/ClosingEntryOrigins.lean)对整个有限源语言证明：
  自登记的代表位置恰为真实执行中某次源列的关闭位置。证明覆盖新建、复用、任意嵌套森林
  及外层退出，不访问复用分支实际跳过的森林；槽中继承的旧指针不能登记槽自身。
  [零标签分类](src/BTnSSBMS/ZeroEndpointClasses.lean)将所有零标签输出穷尽为关闭代表或实际森林槽；
  [正标签来源](src/BTnSSBMS/PositiveEndpointOrigins.lean)将正标签输出穷尽为新定义列或其紧随的保护列，
  并给出真实入口和查找失败证据。
  [最高标签行端点](src/BTnSSBMS/TopRowEndpointClasses.lean)进一步使用实际父关系证明
  `standard_top_pair_classes`：对整个源标准域的任意严格键行祖先、共享标签父的两端，
  左端必为关闭代表，右端必为关闭代表或森林槽。正标签列的键父与标签父是同一个已存在的位置，
  因而不可能成为这样的端点。输入不包括源 SB/G 或目标标准性。
  **最高标签行的端点分类已经闭合，但这两类的块不等式，以及较低键行的完整分类，仍未完成。**
- [祖先绑定恢复](src/BTnSSBMS/FrameAncestorRecovery.lean)使用实际保存环境的精确偶数高度，
  结合父链上同高度位置唯一性，从两个关闭代表间的键行祖先关系恢复后端环境里真实保存的前端绑定。
  [关闭祖先的源位置](src/BTnSSBMS/ClosingAncestorSources.lean)由此恢复当前作用域内的非所属最高数值祖先；
  没有把时间上更早的输出误当成仍然可见的源位置。
  [保存环境持久性](src/BTnSSBMS/FramePersistence.lean)对整个有限编码证明：每个绑定的最近位置
  所保存的完整环境，恰为当前环境截到该绑定的前缀，包括键、定义指针及最近位置指针。
  [关闭环境扩展](src/BTnSSBMS/ClosingFrameExtension.lean)因而得到 `standard_closing_frame_extension`：
  严格键行祖先的旧环境逐项保留，后端只追加非空绑定串，高度差恰为追加绑定数的两倍。
  [可见关闭入口](src/BTnSSBMS/VisibleClosingOrigins.lean)进一步记录：非所属可见位置恰为原入口的关闭列，
  而所属位置可以是森林槽。`standard_closing_pair_origin` 据此构造 P/P 比较对的真实源根、历史入口、
  原关闭位置及非所属祖先证据；[完整键序](src/BTnSSBMS/ClosingKeyOrder.lean)证明这样的严格键行路径
  必使两入口的完整键严格递增。
  **这闭合了最高行 P/P 情形的源对应与环境扩展，但尚未证明带插入环境的整块变基支配。**
- [插入查询计算](src/BTnSSBMS/FrameInsertion.lean)用实际新建／复用查询证明精确高度平衡式，
  允许两环境已有任意共同的高键尾部，指针不要求相等。插入 r 个键后，首高度最多增加 2r；
  若查询未越过全部插入键，则严格小于该平移值，包含“旧查询新建、目的查询复用”的情况。
  [过滤及保存](src/BTnSSBMS/InsertionSaving.lean)证明插入关系经真实 `smaller` 及保存操作保持；
  查询低于插入区间时清除插入键，高于时保留全部插入键。
  [实际关闭查询](src/BTnSSBMS/ClosingQueryInsertion.lean)从标准域的真实关闭链构造插入区间，
  证明 `standard_closing_query_cases`：旧键以下不变，新键以上恰加真实高度差，未越过新键时严格小于平移值。
  [完整头操作](src/BTnSSBMS/InsertionHead.lean)把保存关系接到真实新建／复用及森林返回后的关闭列，
  并证明首个严格列差异不受后续材料影响。
  **这些局部查询结论本身不处理任意外部重入和嵌套森林的整块支配；完整归纳及真实块接合见后文。**
- [查询祖先判据](src/BTnSSBMS/QueryAncestry.lean)对整个标准源域的每次真实查询证明：
  已保存旧绑定的最近位置是首输出的键行祖先，当且仅当旧键严格小于查询键；查询等键时不会保留旧代表祖先。
  该判据已接到 BMS 原算法的实际激活阈值，不是假设的激活标记。
  [查询祖先反向恢复](src/BTnSSBMS/QueryAncestorRecovery.lean)还证明：任意更早关闭代表若为查询首输出的
  键行祖先，它的真实最近位置绑定必在本次查询的较小键环境中。
  因而旧代表不在当前实际环境中时，键行不激活；结论覆盖所有真实嵌套入口，不能用全局出现次序替代环境。
  [重算键后的插入](src/BTnSSBMS/RekeyInsertion.lean)允许搬运前后键字面不同，利用实际源附属材料的
  重算比较证明查询的三段高度公式，未假设存在无上下文的统一键变换。
  [插入与实际激活](src/BTnSSBMS/InsertionActivation.lean)把它与真实 BMS 阈值接合：
  `standard_relocated_query_height_bound` 只在原键行实际激活时加入插入高度差。
  **此局部高度界仍需带实际激活门槛的插入区间；下述外层环境保持不自动满足这个更强条件。**
- [有界键拼接](src/BTnSSBMS/KeySplice.lean)允许两次执行的完整键重算及高度不同，证明过滤、保存
  不产生新的未匹配键，留下的插入键始终是同一个初始集合的子列。
  [可见位置拼接](src/BTnSSBMS/SplicedFrames.lean)逐个记录实际父位置自己的保存环境，
  不用全局最近环境替代重新接回的外部父。
  [完整头保持](src/BTnSSBMS/SplicedSaving.lean)允许一边新建、一边复用，及内部森林输出长度不同；
  关闭恢复后的键拼接仍保持。[外层执行归纳](src/BTnSSBMS/EncoderSpliceTransport.lean)
  将此关系保持到整个尾部执行，构造最终数值视图、材料来源及全部可见位置的保存环境。
  [关闭根重算](src/BTnSSBMS/ClosingRekey.lean)证明真实祖先根的完整键移植不变，
  所有旧保存键也不变。[真实入口](src/BTnSSBMS/ClosingSpliceEntry.lean)据此从标准域的严格关闭祖先对
  构造初始拼接，不要求调用方给出环境配对或插入集合。
  [`standard_closing_tail_spliced`](src/BTnSSBMS/ClosingSpliceTransport.lean)接通该入口与完整外层尾部，
  每个保存环境的未匹配键都来自较晚关闭环境实际新增的那段绑定。
  **这组未带门槛的拼接定理本身不比较被跳过或重新输出的森林内部列，也不推出选择性高度平移。**
- [原根门槛](src/BTnSSBMS/RootedSplice.lean)加强拼接关系：每个未匹配键都严格高于旧环境中
  一个最近位置仍为原根的绑定。真实筛选保留未匹配键时，由传递性强制保留该根绑定；
  保存操作不改变这些旧绑定。[逐个可见位置](src/BTnSSBMS/RootedFrames.lean)和
  [完整头返回](src/BTnSSBMS/RootedSaving.lean)保持这个更强条件。
  [真实关闭入口](src/BTnSSBMS/ClosingRootedEntry.lean)从标准关闭祖先对构造门槛及初始插入集合，
  [外层执行](src/BTnSSBMS/EncoderRootedTransport.lean)和
  [`standard_closing_tail_rooted`](src/BTnSSBMS/ClosingRootedTransport.lean)将其接到完整外层尾部，
  不把初始门槛或最终环境保持作为前提。
  [激活敏感查询](src/BTnSSBMS/RootedQuery.lean)据此证明：原 BMS 阈值不激活旧根时，
  新查询高度**恰等于**旧查询高度；激活时才允许加上初始插入集合长度的两倍。
  高度恰达到该最大平移量还强制全部插入键保留且新建／复用分支一致，而不是假设两侧分支相同。
  [森林槽进入](src/BTnSSBMS/RootedSlots.lean)证明两侧进入对应槽时，真实筛选后的槽环境继续保留原根门槛；
  槽读取所属的进入环境，不读取前一兄弟森林结束后的局部环境，允许两侧输出长度不同。
  这不声称任意两个完整执行都会访问同一森林；相应的分支对齐必须在未出现严格差异的部分另证。
  **这些保持性和首高度结论本身不推出完整块的插入支配不等式。**
- [辅助列实际激活](src/BTnSSBMS/KeyRowRebase.lean)按实际 BMS 父链识别保护列、森林槽、关闭列的
  增量；[查询首列](src/BTnSSBMS/RootedHeadComparison.lean)据此将真实比较分成首列严格较小，
  或首列完全相同且新建／复用分支一致，而不是预设两侧有同样长度或同样分支。
  [实际输出平移](src/BTnSSBMS/ShiftedOutput.lean)精确等于冻结 `BMS.copy` 的相应片段，
  明确区分激活根和截取片段的起点。[比较拼接](src/BTnSSBMS/ShiftComparison.lean)允许两侧长度不同。
  [新建头辅助列](src/BTnSSBMS/FreshShift.lean)从首列相等推导保护列、槽、关闭列的完整行相等条件；
  这没有跳过中间森林的比较。
  [真实数值入口](src/BTnSSBMS/ClosingRowEntry.lean)从标准关闭祖先对同时构造原根门槛及实际逐行差向量，
  键行差恰等于新增绑定数的两倍，不再另行假设数值已经对齐。
  [完整头决策](src/BTnSSBMS/RootedDecision.lean)证明首列严格差异不受任意后续输出影响；
  至少一侧复用时，首列结论已推广到完整头部。
  双方都新建时的剩余比较现已由下一项闭合。
- [全输出插入比较](src/BTnSSBMS/RootedComparison.lean)以森林／外层互递归覆盖任意有限嵌套深度。
  首个严格差异以前，逐列建立数值平移、保存环境和实际激活；之后允许两边分支及输出长度不同。
  兄弟森林重新使用所属列的进入环境，不要求前一兄弟的两侧输出等长。
  [标准关闭入口](src/BTnSSBMS/ClosingInsertionComparison.lean)从真实严格关闭祖先对推导所有进入条件，
  对旧入口的任意有限合法材料取得完整比较，不把递归比较或数值对齐作为调用方前提。
  [完整块截取](src/BTnSSBMS/ClosingBlockSlice.lean)证明真实源块尾的编码是全执行前缀，
  并把逐行差向量、首关闭列及实际 `BMS.rebase` 的完整区间精确连接。
  [完整块插入支配](src/BTnSSBMS/ClosingBlockComparison.lean)因此证明：
  `standard_closing_block_insertion` 对所有标准源项中的严格关闭祖先对，
  将旧块尾运输至新关闭入口后得到的完整编码，不超过目标 BMS 对旧块的实际变基。
  **左侧是搬来的旧材料，不是新入口自己的块。还须证明后者不超过前者；这依赖源块序条件，
  不能把本定理冒充最高行 SB 或全部目标标准性。**
- [数值合法性](src/BTnSSBMS/NumericalLegality.lean)：将“无父则零，有父则父值加一”
  写成实际父表上的有限条件，证明合法 BMS 输入的 `expand?` 总有结果。
  **这不声称该条件已在所有源／目标标准展开中保持。**
- [首对角引理](src/BTnSSBMS/BMSBlocks.lean)：完整第零块与实际父后裔锥一致；
  对数值合法矩阵，BN 及 `SB₁,…,SB_(k−1)` 加上根的严格第 k 行后裔，
  推出块第二列的前 k+1 个值全为根加一。
  已接到具体完整块及祖先敏感变基，**不使用 `SB_k`**，不是只假定头部结论的接口。
  [逐行归约](src/BTnSSBMS/FirstDiagonal.lean)单独记录了其归纳证明。
- [复制／变基对应](src/BTnSSBMS/CopyRebase.lean)：在固定宽度及截取范围条件下，
  BMS 算法的第一个实际副本恰为完整变基块的相应前缀；不是由有限样例推断。
  对实际选根，截取范围条件也由父链推出，无须另作假设。
  这接通了一部分具体复制，但还不是全部最末孔覆盖证明。
- [源展开](src/BTnSSBMS/SourceFS.lean)：数值父、完整键最高父、停止层、特殊森林分支、
  激活、复制、前一阶段捐赠，以及有限路径和种子可达域。无资源阈值进入数学定义。
  错误原始输入的根缺失返回 `none`，不偷偷改成零。
  标准可达域上不会失败已由 `SourceTotality` 证明；
  **与冻结外部实现的全称对应及块不变量仍待证明。**
- [源删除和特殊分支](src/BTnSSBMS/SourcePruning.lean)：已证明实际零叶删除分支，以及由实际
  停止层选中的特殊分支，均有结果且保持有限合法性。结论适用于任意维数、任意指标和
  任意森林嵌套深度。特殊分支的每份森林都在同一个所属上下文中独立核验，未把前一份
  内部结点留给后一份找父。
- [普通复制首列](src/BTnSSBMS/SourceCopyHead.lean)：对任意低类 `b<d` 的实际数值选根，
  原规则 `shift` 和 `delta` 生成的第一份新首列，其实际前 b 行父恰继承停止列，
  第 b 行及以上的父恰继承旧根；父值加一条件因此保持。低行自然数差由真实祖先关系保证。
  该模块只处理首列；下面的模块进一步处理内部材料和后续数值接缝。
- [复制历史](src/BTnSSBMS/CopyHistory.lean)和[整个内部材料](src/BTnSSBMS/CopyBody.lean)：
  复制历史逐项等价于真实源祖先资格；实际 `shift` 值恰为所表示的目标父值加一，
  实际重算的父表因而正确。`copied_finiteLegal` 和 `copiedForests_finiteLegal` 对任意
  嵌套深度证明普通无孔材料的完整有限合法性与森林分离，退出森林恢复原作用域。
  `copied` 只是原 `annotate`、`mark`、`shift` 的组合，并已证明等于原 `ascendReplace`
  的无孔分支；没有更改展开规则。
- [实际复制入口](src/BTnSSBMS/CopyEntry.lean)：`first_copy_shiftView` 从实际低类选根、
  原坐标差和原上下文构造第一份副本的运输状态，**不假设该入口状态成立**。
  `first_copy_finiteLegal` 将它接到根列及任意嵌套普通材料，得到完整材料的合法性。
- [后续数值接缝](src/BTnSSBMS/CopySeam.lean)：若已运输到原停止列之前，
  `ShiftView.restart` 用同一个原始差向量和 `phase+1` 的真实新首列构造下一份入口。
  它保留旧根之前的映射，核验低行的伸长父链和高行的旧父链，并重置激活历史。
  [最高父标注相容性](src/BTnSSBMS/CopyAnnotation.lean)另证明：`cap≤d` 时，真实
  `Source.parents` 追加的最高键父不改变数值激活结果。
- [最末孔拼接](src/BTnSSBMS/CopySplice.lean)与[孔上下文运输](src/BTnSSBMS/CopyHole.lean)：
  计算真正的最末孔及其所属上下文，证明结构拼接等于原 `ascendReplace`。
  复制时一直将数值运输状态带到这个实际孔位；替换后任意层数的外部作用域恢复与合法性
  由结构归纳证明。[根模板](src/BTnSSBMS/CopyRoot.lean)再从真实终端祖先路径推出整个
  外层材料位于根的第零后裔区间，不额外假设材料的坐标下界。
- [任意份数低类复制](src/BTnSSBMS/CopyIteration.lean)：`copies_low_finiteLegal`
  直接对原 `copies` 的份数归纳，在 `0<b<d`（任意孔深度），或 `b=0` 且根、孔同森林时，
  证明整个输出有限合法并保留其外层坐标下界。下一份入口、整个替换尾部的合法性及
  所属边界均在证明内构造，不作为替换材料的假设。
  `initial_copies_low_finiteLegal` 从实际数值选根构造首次入口和原差向量；
  `rooted_low_expansion_finiteLegal` 将全部副本装回原根模板，包含最外层零平移拼接。
  根片段的实际标记、差向量和全项接合现已对正数低类接通，见下面的全项定理。
  零类的完整外部所属围栏和停止规则排除跨森林情形，现由下面的零类模块接通。
- [最高类捐赠接缝](src/BTnSSBMS/CopyDonation.lean)：证明第 `phase+1` 份的新根向量
  恰等于第 `phase` 份的虚拟终端向量；从而前一阶段的整个捐赠森林在实际新所属上下文中
  有限合法、保持所属分离，任意嵌套深度均适用。同时构造下一份普通材料的根运输状态。
  [捐赠材料](src/BTnSSBMS/DonationMaterial.lean)将捐赠精确写成原终端森林删去末森林，
  并证明正确激活历史的唯一性以及第一份的零平移恒等式。
  [最高类迭代](src/BTnSSBMS/DonationIteration.lean)已对任意有限份数证明实际 `copies`
  的有限合法性，包含每份首列表替换；首次入口和首次捐赠从原模板构造，后续捐赠
  从前一份真实运输状态推出，再接回原根模板的零平移拼接。
  这些根模板定理现已由下面的最高类全项模块接到原 `expand?`：
  数值祖先解释、捐赠历史与外层拼接均在证明内取得。
- [实际选根](src/BTnSSBMS/SourceRootSearch.lean)、[作用域脊柱](src/BTnSSBMS/SourceSpine.lean)
  与[停止孔](src/BTnSSBMS/SourceSpineHole.lean)：`locateRoot`/`spine`/`drop` 选出的
  数值根片段非空、有限合法，其进入上下文长度恰等于所选根的绝对指标；
  层上下文不混入已经关闭的森林。停止层的末列恰为复制定理中的实际孔，
  删除根前缀不改变这个孔的上下文。
- [最高父作用域](src/BTnSSBMS/SourceTopScope.lean)与[实际最高类根](src/BTnSSBMS/SourceTopSelection.lean)：
  对任意有限源项证明真实 `parents` 的最高键父严格在前，并排除整个开放所属列表。
  `selected_top_root_tail` 将此性质接到实际停止层、`highestParent` 和 `locateRoot`，
  推出根片段不可能仅有一列，**不另外假设根非所属或根片段有尾部**。
  这些模块本身处理已取得的搜索结果；所有查找的成功性由下面的 `SourceTotality` 取得。
- [父标注脊柱](src/BTnSSBMS/SourceAnnotatedSpine.lean)与[实际标记片段](src/BTnSSBMS/SourceMarkedSpine.lean)：
  `actual_marked_root_piece` 证明原 `mark/spine/drop` 取出的整个材料恰等于复制引理的
  规范模板，包含全部嵌套森林与激活标记；根以前的历史精确为零，不只是去标记后相等。
  [父表截取](src/BTnSSBMS/SourceParentPrefix.lean)证明删去追加的最高父字段后，整个树
  恰恢复数值父标注，因此实际低类选根就是停止列真正的相应数值父。
- [根与停止孔](src/BTnSSBMS/SourceRootHole.lean)及[原差向量](src/BTnSSBMS/SourceRootCoordinates.lean)：
  证明层查找的组合律，将根片段孔连接到全项停止列；原算法的可见列列表读取到的
  根向量恰是模板首列。复制使用原定义中的差向量，未另换参数。
- [正数低类全项保持](src/BTnSSBMS/SourceLowAssembly.lean)：
  `expand_positive_low_finiteLegal` 对真实 `expand?` 的每个成功返回且 `0<b<d` 的步骤，
  证明**整个输出**有限合法。实际选根、材料标记、所有副本和外层孔拼接均已连接；
  所属围栏由新首列第零坐标等于原停止列推出，不作为替换材料的假设。
  **本模块不证明该分支必返回结果，也不处理零类；最高类由下一组模块处理。**
- [最高父数值祖先](src/BTnSSBMS/SourceTopAncestry.lean)：
  `selected_top_numerical_ancestor` 对任意正维数有限源项，证明实际最高键父是停止列
  在原数值上下文中的最高数值行祖先。逐层删去追加父字段，并恢复森林作用域；
  不假设标准性，也不将所需祖先关系作为输入。
- [实际捐赠历史](src/BTnSSBMS/SourceMarkedHistory.lean)：从原根以前、根处一直到停止列，
  证明实际标记历史与数值祖先资格一致；关闭的森林不进入外部历史。
  `actual_marked_top_donation` 将真实停止列捐赠精确识别为迭代引理中的材料，
  包含全部激活标记，不只是抹去标记后的结构相等。
- [最高类全项保持](src/BTnSSBMS/SourceHighAssembly.lean)：
  `expand_high_finiteLegal` 对真实 `expand?` 的每个成功返回且 `b=d>0` 的步骤，
  证明**整个输出**有限合法。实际祖先、非所属根片段、首次及后续捐赠、任意份数复制、
  外层孔拼接与所属围栏全部接通。该模块不处理零类或查找总性，见下面的接合。
- [最高父存在性](src/BTnSSBMS/SourceTopExistence.lean)与
  [低类叶结论](src/BTnSSBMS/SourceLowLeaf.lean)：在任意正维数有限合法源中，
  带非空附属列表的列必有实际最高键父。搜索走到最高数值坐标为零的位置时，
  该位置的键为空且不是开放所属，因此不会失去根。由此证明所有低类停止列都是叶子，
  包括数值维数为一的情形；没有将叶性额外加入源定义。
- [零类几何](src/BTnSSBMS/SourceZeroGeometry.lean)与
  [首停止层选根](src/BTnSSBMS/SourceZeroSelection.lean)：零类停止叶的高坐标全部为零。
  若其根落到当前森林之外，森林分离和单位步迫使根正是所属列，并触发前一层的
  原特殊停止测试，与当前层为首个停止层矛盾。因此实际根和孔必在同一个森林。
- [零类全项保持](src/BTnSSBMS/SourceZeroAssembly.lean)：
  `expand_zero_class_finiteLegal` 接通实际零类的任意份数复制和整个外层拼接。
  此时不靠新首等于停止列来证明所属围栏，而使用同森林原根的坐标下界。
- [全分支有限闭合](src/BTnSSBMS/SourceFiniteClosure.lean)：
  `expand_finiteLegal` 对所有成功返回的实际展开证明完整有限合法性保持。
  `standard_finiteLegal` 将其沿真实有限路径接到所有对角种子后裔；
  `Encoder.standard_numericallyLegal` 因而对整个源标准域给出完整 d+2 行编码合法性，
  不再额外假设源森林分离或单位步条件。
- [停止层总性](src/BTnSSBMS/SourceStopTotality.lean)与
  [完整展开总性](src/BTnSSBMS/SourceTotality.lean)：首个停止层必存在，非空输入不会
  误选空森林；非零停止列必有父，根位于可见前缀，父标注和标记保留所有所需位置。
  `expand_total_finiteLegal` 对任意正维数、任意有限合法输入和任意指标给出实际结果及其合法性。
  `standard_expand_total` 将结果接到整个标准可达域。
  **这证明单步算法总性和有限条件闭合，不证明连续展开终止，也不证明 BN/HW/SB/G。**
- [末位改写比较](src/BTnSSBMS/SourceLastOrder.lean)、
  [实际叶子最高父](src/BTnSSBMS/SourceLeafParents.lean)及
  [首份复制下降](src/BTnSSBMS/SourceCopyDescent.lean)现已接到
  [原展开严格下降](src/BTnSSBMS/SourceDescent.lean)：`expand_lt` 对任意正维数、有限合法非空项
  及任意指标，证明实际展开在源递归比较下严格变小，不假设任何块序不变量。
  低类在选中数值坐标处出现首次严格差异；最高类首坐标向量不变，但首附属列表严格删去末槽。
  实际选根、特殊复制和任意深度的末位拼接均已连接。
  `no_return_after_step` 排除非空项在一次展开后沿有限展开路径回到自身；
  `standard_expansion_lt` 还证明实际原始矩阵编码随源展开严格下降。
  **这是原论证“延迟改写”所需的严格变化前提，不是全部块序保持、BMS 展开模拟、目标标准性
  或良序证明；排除有限循环仍不能排除无穷降链。**
- [森林次序](src/BTnSSBMS/SourceHW.lean)、[末孔拼接](src/BTnSSBMS/HWSplice.lean)及
  [实际运输](src/BTnSSBMS/HWTransport.lean)定义并保持 HW：每列的附属森林列表按源比较不增，
  且其中的森林递归满足同一条件。它没有被加入标准性的定义。
  [低类迭代](src/BTnSSBMS/HWLowCopies.lean)包含第零类，后续副本的进入状态逐份从实际末孔构造；
  [最高类迭代](src/BTnSSBMS/HWHighCopies.lean)证明下一份的捐赠列表恰为当前虚拟末列列表删去末槽，
  不把不同份数的平移混为一谈。末位替换严格变小，因而不会超过同所属列表中先前的森林。
  [全分支接合](src/BTnSSBMS/SourceHWClosure.lean)的 `expand_HW` 覆盖实际删除、特殊及所有普通分支；
  `standard_HW` 对所有正维数、所有实际种子可达项证明 HW，不限制森林深度或展开次数。
  **这一标准域不变量已闭合，不依赖 BN、SB 或 G；它不单独给出这些条件、具体覆盖或主上界。**
- [源完整块次序](src/BTnSSBMS/SourceBN.lean)现在明确定义 BN：只比较同一森林中、
  实际算出的第零父相同的两列，并比较各自的完整第零块；无父情形也包含在内。
  各附属森林从所属上下文独立进入，BN 没有被写进标准性的定义。
  [块截取次序](src/BTnSSBMS/SourceBlockOrder.lean)及
  [同父几何](src/BTnSSBMS/SourceSiblingGeometry.lean)证明同父两列的第一坐标相等，
  因而较早块已在较晚列之前关闭；后者的末位删除或附属列表改小不影响前者。
  全部正维数、全部对角种子的 BN 已证明；[末列删除](src/BTnSSBMS/BNDeletion.lean)与
  [末列表修改](src/BTnSSBMS/BNLastChange.lean)实际保持完整块不等式。
  [特殊分支](src/BTnSSBMS/BNSpecial.lean)覆盖实际停止层、任意嵌套深度及任意份数；
  [零指标全部分支](src/BTnSSBMS/BNPruning.lean)还接通普通分支在 `[0]` 时的实际末脊删除。
  **下述全部分支现已接通，`standard_BN` 已证明整个源标准域的 BN；这不是目标 BMS 的 BN 或标准性。**
- [完整块数值运输](src/BTnSSBMS/RelocationBlocks.lean)在已构造的数值运输入口下，证明第零块的截止条件在运输前后
  双向等价，得到 `relocate_rootBlock`，再以 `copied_rootBlock` 接回原激活平移复制。
  这是完整有限块的语法等式，涵盖全部嵌套附件，并非只比较首列或任意截取的前缀。
  不同入口间的使用及强制新首的入口由下面的结果补接；这些结果不单独证明跨副本 BN。
- [同父共同入口](src/BTnSSBMS/SiblingEntry.lean)将较早首列向后移过上下文间隔：
  只要求它实际算出的第零父保持不变，随后推出全部高层父、单位步、数值视图和整段有限合法性。
  [同父运输交换](src/BTnSSBMS/SiblingRelocation.lean)对包含任意嵌套森林的完整语法证明交换关系，
  [同父完整块比较](src/BTnSSBMS/SiblingComparison.lean)将目标同第零父反映回源，
  并证明不同入口下的完整块比较恰保持，也接通原激活平移复制。
  [实际后缀入口](src/BTnSSBMS/RelocationSuffix.lean)从递归执行恢复每个比较对的上下文和位置映射。
  因而 [BN 运输](src/BTnSSBMS/BNRelocation.lean)对所有正维数证明 `relocate_BN`、`copied_BN`，
  递归涵盖全部附属森林。[强制首列组装](src/BTnSSBMS/BNRootCopy.lean)还包含实际复制新首；
  `initial_selected_root_copied_BN` 从真正选出的低类父构造第一份的入口，没有额外的运输状态前提。
  此结果处理末孔尚未替换时的完整普通复制；下面的结果再接通正数低类的真实接缝。
- [末列替换几何](src/BTnSSBMS/TerminalSplice.lean)将输出列精确分为旧列与替换材料内的新列，
  保留实际进入上下文和完整块边界。[第零坐标围栏](src/BTnSSBMS/ZeroFloor.lean)证明：
  新材料中只要一列仍以旧前缀为第零父，它的第零坐标必为围栏值，且与新材料首列同父。
  [外层 BN 接缝](src/BTnSSBMS/BNSpliceZero.lean)据此将新同父完整块压到新材料首块以下，
  再压到旧终端以下；此前的同父块不变。
  [任意深度拼接](src/BTnSSBMS/BNSplice.lean)只在真实孔上下文检查替换材料，
  没有假设它在任意可能的上下文都满足 BN。
  [正数低类迭代](src/BTnSSBMS/BNPositiveCopies.lean)逐份构造真实接缝，覆盖任意复制份数和森林深度。
  [整项组装](src/BTnSSBMS/SourceBNPositive.lean)再定位冻结 FS 的真实根与终端：
  `ordinary_positive_expand_BN` 证明 `0 < cap < d` 的整个普通展开分支保持 BN；
  对 BT3SS，这包括 `cap=1`。
- [实际捐赠运输](src/BTnSSBMS/BNDonation.lean)提取真实孔上下文中的末附属列表，
  并证明在后续外层首项严格高于根时替换首附属列表保持 BN。
  [最高类复制](src/BTnSSBMS/BNHighCopies.lean)逐阶段构造新的运输状态；下一份的捐赠恰为
  当前虚拟终端的附属列表删去末槽，因此接缝严格下降。
  [最高类整项组装](src/BTnSSBMS/SourceBNHigh.lean)把这些事实接回实际选根、激活标记及外层拼接。
- [第零类完整块形状](src/BTnSSBMS/ZeroCopyShape.lean)证明非空复制的首根块恰为原模板删末列，
  不是只证明新首数值相同。[第零类拼接](src/BTnSSBMS/BNZeroSplice.lean)和
  [任意份数复制](src/BTnSSBMS/BNZeroCopies.lean)利用这一完整块等式处理等根重复。
  [根前前缀](src/BTnSSBMS/BNPrefixSplice.lean)、[整个停止森林](src/BTnSSBMS/BNZeroForest.lean)、
  [外层脊提升](src/BTnSSBMS/BNSpineLift.lean)及[实际零类分支](src/BTnSSBMS/SourceBNZero.lean)
  保留原根以前的所有同父比较，再装回任意层数的原始外层。
- [BN 全分支闭包](src/BTnSSBMS/SourceBNClosure.lean)的 `expand_BN` 覆盖冻结规则的每个分支；
  `standard_BN` 对所有正维数、所有实际种子可达式证明 BN。标准性定义没有加入 BN 假设，
  证明不限制复制份数或森林深度，也不假设 SB/G。
  **源 BN 已完成；源 SB/G、全部目标 BN/SB、具体覆盖及整个上界仍未完成。**
- [精确复制位置](src/BTnSSBMS/ExactNumericalPosition.lean)将精确父对应与仅保持祖先关系区分；
  [实际后缀入口](src/BTnSSBMS/ExactRelocationEntries.lean)对普通新增复制首构造前者，
  不把任意强制复制根也算进去。[部分变基首](src/BTnSSBMS/PartialRebaseHead.lean)、
  [完整材料](src/BTnSSBMS/PartialRebaseMaterial.lean)及其
  [交换律](src/BTnSSBMS/PartialRebaseNaturality.lean)处理任意深度森林和完整外层尾部。
  [完整块比较](src/BTnSSBMS/PartialRebaseBlockComparison.lean)与
  [旧根材料合法性](src/BTnSSBMS/RelocatedRootMaterial.lean)进一步接回
  [冻结的实际复制](src/BTnSSBMS/PartialRebaseCopyComparison.lean)：
  `copied_partial_block_compare` 保持整个三值比较结果，不假设两次独立变基的材料相等。
  它处理普通同副本 SB 运输，尚不处理末端实际改写、强制新首及跨副本组装。
- [键的最小列表延长](src/BTnSSBMS/KeyEmptyExtension.lean)及
  [所属捐赠边界](src/BTnSSBMS/DonationInternalKey.lean)证明：若真正在捐赠列表内部的列，
  其键已知不超过“捐赠键后接一个空森林”，则它严格小于捐赠键。
  使用完整递归节点数排除两个等号，不把尺寸较小直接当成键较小。
  仍须从原 SB 比较取得前述上界；此局部结论不等于最高类 SB 全分支保持。
- [源 SB 定义](src/BTnSSBMS/SourceSB.lean)保留每个当前可见祖先的完整剩余材料，
  包括开放的森林所属列。`seed_SB` 对所有维数、所有种子深度及所有适用层证明种子满足 SB，
  不是整个可达域的闭包定理。[历史块上下文](src/BTnSSBMS/SBBlockContext.lean)将这些材料
  对应到真实父前缀入口，并证明实际变基合法。
  [历史块外延性](src/BTnSSBMS/SBHistory.lean)证明只需完整块相等，块后尾部不影响 SB，
  包括递归森林进入与外层恢复。[最外层零列删除](src/BTnSSBMS/SBDeletion.lean)
  利用幸存块不变并显式更新历史材料，接到原展开的 `expand_outer_zero_SB`，覆盖所有 SB 层。
  正数末端改写、特殊重复及普通复制分支仍未闭合。
- [跨副本父搜索屏障](src/BTnSSBMS/SBCrossPhase.lean)直接由实际搜索排除共享父，
  不假设理想化父表。复制级恰等于所检查的 SB 行时，
  [原下一份根公式](src/BTnSSBMS/SBCopyBarrier.lean)给出对较早普通路径列的较低坐标屏障。
  [精确祖先反射](src/BTnSSBMS/ExactAncestryReflection.lean)只要求强制根以上的普通位置父精确，
  不错误地要求强制根本身也精确。[实际接缝接合](src/BTnSSBMS/SBCopyAncestry.lean)
  再从复制后的真实祖先路径反推出源路径，去掉该排除定理中手工给出源路径的前提。
- [精确嵌套孔遍历](src/BTnSSBMS/ExactCopyHole.lean)现从真实复制根出发，沿任意有限深度
  森林的实际末端孔路径构造全部普通可见位置的精确父，并保留原可见位置映射的前缀。
  强制根仍明确排除在精确父要求之外，不再外加“孔位处父已经精确”的假设。
  [实际孔位屏障](src/BTnSSBMS/SBCopyHoleBarrier.lean)已接上这份构造。
- [重启间隙引理](src/BTnSSBMS/ExactCopyBarrierPath.lean)证明：来自上一副本间隙的祖先链
  若进入新副本，就必须经过重启根。原因是普通项的精确父只能来自所代表的源位置，
  而固定源前缀的代表位于该间隙之前。
  [连续真实副本](src/BTnSSBMS/SBConsecutiveCopies.lean)构造两侧嵌套孔上下文及原重启，
  据此推出根屏障路径。在 `0 < 复制级 = 所检 SB 行 < d` 时，较早副本的普通可见列
  不能与下一副本的任何所代表的可见列（包含新强制根）或末端构成 SB 比较对。
  定理返回真实作用域的数值映射，不使用任意无约束位置表；源路径、精确父及屏障路径
  都是推出的，不再作为前提。[任意位置屏障](src/BTnSSBMS/SBCopyBarrierPosition.lean)
  也单独处理端点恰为新根的情形。
  [相邻根祖先链](src/BTnSSBMS/CopyRootChain.lean)另证明：复制级以下每一行上，旧根都是新根的祖先。
  以下结果进一步处理同级普通比较方，但仍不是 SB 全分支闭包。
- [实际孔跨度](src/BTnSSBMS/CopyHoleSpan.lean)由原复制等式证明：沿末端孔路径，源和目标
  新增的可见位置数量完全相等，允许任意深度森林，关闭的兄弟森林恢复进入上下文。
  [位置映射连续性](src/BTnSSBMS/NumericalViewDensity.lean)由严格递增、末端对齐及区间等长
  推出连续平移；[真实孔区间](src/BTnSSBMS/CopyHoleDensity.lean)接入实际跨度及根位置，
  因而目标根至孔的每个位置都有源原像，不假设映射满射。
  [完整相邻区间](src/BTnSSBMS/SBConsecutiveIntervals.lean)据此把代表位置条件换成真实下标范围。
- [任意有限份孔迭代](src/BTnSSBMS/CopyHoleRun.lean)直接观察原复制模板与孔查找递归，
  对所有有限份数构造后续入口、固定根前映射、受保护首部及首根至末根的低行祖先链。
  这个观察函数不改变展开规则，也不是新标准域定义。
  [后续间隙路径](src/BTnSSBMS/CopyRunBarrierPath.lean)及
  [非相邻副本排除](src/BTnSSBMS/SBSeparatedCopies.lean)据此在同级条件下，排除较早孔可见区间
  内任意普通位置与隔着任意有限份复制后的根至末项区间内任意位置形成 SB 比较对。
  真实孔、精确父、区间原像与屏障路径都在证明内构造，不是输入假设。
  这仍未枚举最终拼接材料的全部作用域入口；较早强制根、其他所检行、捐赠及末端改写后的
  块比较仍未完成，不能据此声称完整 SB 保持。
- [复制运行几何](src/BTnSSBMS/CopyRunGeometry.lean)证明任意有限份数的精确可见长度增长，
  以及复制级和更高各行的根父保持。[强制根重置](src/BTnSSBMS/RootCopyReset.lean)与
  [完整模板变基](src/BTnSSBMS/RootCopyMaterial.lean)据此处理两份根的混合首列、全部附件和外层尾部。
  [完整根块截断](src/BTnSSBMS/RootCopyBlock.lean)与复制交换；
  [`copyHoleAfter_root_rebaseBlock`](src/BTnSSBMS/CopyRunRootBlock.lean)因此对实际孔迭代中的
  任意正数副本间隔证明：早先未拼接模板的完整根块变基后，恰为后来模板的完整根块。
  它从实际运行推出作用域、固定前缀、低行祖先链和共享高行父，不把这些作为额外结论假设。
  [末孔替换运输](src/BTnSSBMS/RelocationSplice.lean)另沿实际孔路径构造进入上下文与映射，
  证明规范数值运输和任意替换材料的拼接交换，涵盖任意森林深度。
  **尚未把这些等式接成最终拼接材料中强制根之间的 SB 不等式**；特别不能把未拼接模板
  当成历史中实际保存的、已经含后续副本的完整块。
- [安装根后的运输](src/BTnSSBMS/RootedRelocation.lean)与
  [拼接后变基](src/BTnSSBMS/RebaseSplice.lean)现证明真实 SB 变基与末孔替换交换，
  孔位上下文按实际计算取得，完整根块也被保留。
  [强制副本拼接](src/BTnSSBMS/RootCopySplice.lean)将该等式用于任意正数实际副本间隔。
  [反向合法性提取](src/BTnSSBMS/SpliceExtraction.lean)从完整拼接结果中取出替换材料的
  进入合法性和所属列屏障，不额外假设它们。
  因此[真实历史材料定理](src/BTnSSBMS/CopyRunSplicedMaterial.lean)已经直接用于原 `copies`：
  在正的低数值类中，早先完整副本串的根块变基后，恰为“后来模板在末孔接上规范运输后的
  全部剩余副本串”的根块；不再用未拼接模板冒充历史材料，也没有深度或份数上限。
  [份数单调性](src/BTnSSBMS/CopyCountOrder.lean)另证明固定起始相位时，较少普通副本
  对应不更大的式子及完整根块。
  [接缝混合首列](src/BTnSSBMS/CopySeamNaturality.lean)在明确的高行父精确性条件下与运输交换，
  不错误地要求初始根的低行父也精确。
  [真实孔映射复合](src/BTnSSBMS/CopyHoleSquare.lean)现由可见区间连续性与入口映射导出，
  不把末孔处映射相容另列为假设。[材料及混合首列运输](src/BTnSSBMS/CopyMaterialNaturality.lean)
  与[接缝相容](src/BTnSSBMS/CopySeamSquare.lean)保持高行父及重置映射等式。
  [完整复制串交换律](src/BTnSSBMS/CopyRunNaturality.lean)对真实 `copies` 份数归纳，
  证明整个相位平移恒等式，包含所有末孔替换。
  [实际复制串变基](src/BTnSSBMS/CopyRunRebase.lean)再由 `copyHoleAfter` 构造入口条件：
  任意正有限间隔下，完整早先副本串变基，恰为后来相位下相同份数的完整根块。
  配合份数单调性，后来份数不更多时，两强制根之间的 SB 不等式成立。
  **这一类配对已证明，但全体源 SB 保持尚未证明。** 其他端点类型、复制类与测试行不同的情况、
  捐赠及完整源展开的组装仍需分别处理。
- [源种子合法性](src/BTnSSBMS/SourceSeeds.lean)：所有正维数及所有指标的真实对角种子
  都满足有限合法条件；其完整编码的 d+2 行合法性随之成立，不是有限种子抽查。
- [零指标展开](src/BTnSSBMS/SourceZero.lean)：证明最高父标注和激活标记的抹除恒等式，
  以及空尾、零平移的实际孔替换恰为指定深度的删除。由此 `expand_zero_index_finiteLegal`
  对**全部分支的已定义 `[0]` 展开**证明有限合法性保持，包含普通复制和捐赠分支。
  该早期模块本身不排除普通分支返回 `none`；正维数有限合法域上的排除现由上述总性定理完成。
- [完整键](src/BTnSSBMS/Keys.lean)、[还原](src/BTnSSBMS/Decoding.lean)、
  [相等判定](src/BTnSSBMS/KeyEquality.lean)：差值使用有符号整数。
  固定数值基点时，相等的完整键能还原出相同的整个附属结构；两边的激活历史
  不必相同。实际比较函数返回相等也足以推出这个结论。
- [编码](src/BTnSSBMS/Encoder.lean)：可执行的省略所属绑定编码 C⁻；
  递归终止、每列恰有 `d+2` 行、任意有限输入的输出列数至多 `3N+F`；
  编码只追加，不改写已有输出和所保存的环境。
  **这些结论还不是数值合法性或严格保序性。**
- [编码环境](src/BTnSSBMS/Environment.lean)：零键绑定在真实递归执行中一直可用，
  新键的较小绑定列表非空；`source_noFallback` 证明从空上下文开始，
  对任何有限输入都不会用到 `base []` 的兜底值。
- [键序](src/BTnSSBMS/KeyOrder.lean)、[栈排序](src/BTnSSBMS/FrameOrder.lean)、
  [精确高度](src/BTnSSBMS/FrameHeight.lean)：实际完整键比较具有反对称性与传递性；
  所有输出列保存的环境都按键及高度严格递增；较小键筛选和包含等键的截取均为前缀。
  `source_framesDense` 进一步证明每个栈第 `i` 项的高度**恰为 `2*i`**。
  这些结论覆盖整个真实递归调用，不以源项标准性或有限测试为前提。
- [绑定指针](src/BTnSSBMS/FrameReferences.lean)：保存环境中的每个定义指针和最近位置
  都在保存当时的输出前缀内，且实际列的高度／标签吻合；定义严格早于最近实际位置。
  这排除了悬空指针和前向引用。该模块本身不识别计算父关系；后续键作用域证明已把
  它接到实际祖先链和父搜索上。
- [键高度分支](src/BTnSSBMS/KeyLevels.lean)：同一环境中，较小键的首输出高度不会更大；
  任一键已绑定时比较严格。两个不同键的首高度相等，**当且仅当两者均为新键且较小绑定
  前缀完全相同**。该分支需要递归比较附属森林，现已由下面的整体保序模块完成。
- [数值首差](src/BTnSSBMS/NumericalOrder.lean)：在同一真实数值入口，两个合法列的
  首个不同坐标决定所选父在同一记录链上的严格次序；严格递增的位置代表将它传到目标。
  `encode_lt_of_numerical_heads` 已把结论接到**完整实际编码输出**，不限制附属列表及后续材料。
- [完整键归一化保序](src/BTnSSBMS/KeyNormalizationOrder.lean)：首差以前激活标志相同，
  首差处激活标志只能从不激活变为激活，不能反向跳转；有符号差值保持同标志内的严格比较。
  `ofColumn_annotate_compare` 对同一所属入口中的任意深度有限合法森林，证明完整键的比较结果
  **恰等于原附属列表的比较结果**。历史正确性沿实际标注递归保持，退出森林恢复原历史；
  没有假设两项的全部激活标志相同，也没有用样例代替归纳。
- [编码首部比较接合](src/BTnSSBMS/EncoderHeadOrder.lean)：更低首键高度已推出完整编码严格较小。
  `encode_attachment_compare_cases` 将原附属列表比较、完整键比较、真实环境高度与真实输出连接：
  或者已经严格较小，或者两键均新建且整个较小绑定环境相同。
  同空隙分支现已接到下面的整体互递归证明。
- [森林比较边界](src/BTnSSBMS/EncoderBoundary.lean)：从真实第零父搜索及数值位置代表，
  证明仍在森林内部的下一输出列严格高于所属的表示位置。严格首差的比较还被证明不受
  任意后续材料影响；这与仅因一侧结束而较小的真前缀情形明确区分。
  [整列拆分](src/BTnSSBMS/EncoderHeadState.lean)证明原编码在完整一列之后的精确分解，
  恢复位置确为关闭列。[退出围栏](src/BTnSSBMS/EncoderOrderScope.lean)据此核验后续槽及
  关闭列的真实高度界，没有把所需递归保序作为输入。
- [完整严格保序](src/BTnSSBMS/EncoderStrictOrder.lean)：`encode_strict_order` 对任意正维数、
  同一合法进入状态及任意有限合法材料，证明**完整实际编码严格保序**。
  互递归证明覆盖两新键同空隙、任意森林嵌套、一个森林提前结束、附属列表提前结束，
  以及相同列后的外层尾部；通过真实槽／关闭列界控制不同后缀，未偷用裸前缀比较。
- [源标准域比较](src/BTnSSBMS/SourceEncodingOrder.lean)：`standard_compare` 将有限合法性闭合
  接到完整保序，证明所有源标准项的原比较与实际编码比较**完全相同**；
  `standard_injective` 排除不同源项编码成同一个矩阵。
  **这是到原始固定行矩阵的保序单射，尚未证明像是标准 BMS 项，不能据此推出序型上界。**
- [最末孔](src/BTnSSBMS/LastHole.lean)：已证明一般有限字引理及定量版本。
  对具有固定正延迟、保持长度增量与共同前缀的上下文 `F`，令 `W₀=[]`、
  `Wₙ₊₁=F(Wₙ)`，则 `F(Y) ≥ Y` 蕴含 `W_(|Y|+1) ≥ Y`。
  加上严格保序性就得到文稿的双向等价。不借用裸字典序良基性。
  **尚未证明真实 BMS 各复制分支满足这个上下文接口。**
- [BMS 短展开](src/BTnSSBMS/BMS.lean)：固定宽度的父表、激活阈值、逐份复制和
  任意维／任意指标的种子展开公式；由通用算法证明 `U_r = B_(r+1)[3]`，
  显式投影掉末尾全零行。没有把该公式写成种子的特殊展开规则。
- [实际展开下降](src/BTnSSBMS/BMSDescent.lean)：`BMS.expand_lt` 证明任何非空、固定宽度
  原始矩阵的已定义短展开，都严格降低裸字典序；直接展开复制首列，而非使用假定的下降模型。
  **裸字典序不是良序，所以这不代替 BMS 良序定理，也不证明根总存在。**
- [首列保持](src/BTnSSBMS/SourceHead.lean)及[统一固定界](src/BTnSSBMS/Ceiling.lean)：
  对真实 FS 的删除、特殊及复制分支证明首个零叶列保持，接到有限可达性归纳。
  `standard_source_below_ceiling` 已证明**所有种子可达源项的完整编码**在裸字典序上
  严格小于同一个 `U_(d+2)`。这一步不再只是四列开头的条件引理。
  **该裸矩阵界不推出标准性；保序性已由上述独立递归证明取得，BMS 标准性仍未完成。**
  [比较模块](src/BTnSSBMS/Order.lean)另形式化了裸固定行数矩阵的 `0^(k+1),1 < 0^k,1` 降链，
  提醒不能把裸矩阵字典序当作标准 BMS 良序；这不是基本列降链反例。
- [覆盖推标准性](src/BTnSSBMS/Coverage.lean)：**假如**有限覆盖性质成立，
  且标准目标域上的展开关系良基，就能有限步到达目标，从而推出目标标准。
  它只需要标准域上的良基性，不需要非标准矩阵上的良基性。
  这是明确的条件引理，尚未为本编码证明其覆盖前提。

最近一次完整构建的[公理审计](src/BTnSSBMS/Audit.lean)已核验297个模块、1777个公开声明：1681个一般引理及证明构造、
72个封闭样例等式和24个有限可达性证书。私有辅助引理随调用者核验。
最近四十九个部分变基运输、源 SB、精确孔、区间连续性、有限副本、强制根块、末孔替换、
完整拼接材料、份数比较、接缝运输、孔映射相容及完整复制串模块（127个公开定理）已纳入完整构建，
源码哈希、依赖顺序和公理报告均已复核；这不表示完整上界证明完成。
实际依赖见[审计日志](verification/Audit.log)及核验记录；构建检查禁止
占位证明、新增公理以及把原生程序求值当作证明的捷径。

## 样例一致性不是全称正确性

[样例模块](src/BTnSSBMS/Fixtures.lean)包含维数1、2、3、5中的24个输入，
逐一核验父标注和完整编码与研究版程序的预期结果相等，共48个等式。
使用的是产生证明项的 `decide_cbv`，由 Lean 核验。

此外，[源路径模块](src/BTnSSBMS/SourceFixtures.lean)在新写的完整 Lean 展开器中
核验同24条路径等式，并据此证明这24个输入由相应种子有限可达。
这修复了此前“路径只记在外部元数据里”的不足，但**没有证明所有合法可达项上的
实现等价性，也没有证明全体标准项的块不变量**。
[元数据](fixtures.json)包含路径与参考编码文件哈希。
[可选只读生成器](tools/oracle-fixtures.cjs)需显式传入旧研究目录并输出 JSON；
正常编译不依赖该目录，也不需要上游 JavaScript。
规则来源见[原文收录清单](../../research/btnss-bms/MANIFEST.json)。

## 距离完整形式化还缺什么

1. 对已写出的源 FS，完成与冻结外部实现的全称对应；形式化各层 SB、最高 G
   和跨叶引理在标准域上的保持性。
   种子有限合法性、删除／特殊分支、所有已定义零指标展开，以及低类第一份新首的
   实际父运输已经核验。整个无孔普通材料、真实第一份入口、后续数值接缝、实际孔位运输
   与任意深度拼接也已核验。正数低类任意份数复制、零类同森林复制及装回原根模板已接通，
   包含替换材料相对所属的分离。最高类任意份数复制、每份首列表替换、首次捐赠
   及其后续运输也已证明。实际数值根片段和孔上下文已定位，最高类真实选根
   已推出片段有尾部，而不以非所属性作为外加假设。
   原 `mark`／`spine`／`drop` 根标记片段已精确等于模板；原可见根向量及差向量也已接通。
   正数低类和最高类成功返回分支已证明全项 `expand?` 有限合法性保持，而不只是根模板结论。
   最高键父的实际数值祖先路径、原终端捐赠的完整激活历史及最高类全项拼接均已完成。
   零类同森林性、外部围栏、全项拼接现已接通；所有普通分支的查找总性也已证明。
   `standard_finiteLegal` 与 `standard_expand_total` 已闭合整个源标准域的有限合法性及单步总性。
   HW 现由 `standard_HW` 单独证明：源递归比较下降、真实复制运输与最高类捐赠共同保证
   全部附属列表递归不增。剩余 SB、G 及跨叶块序不变量仍不能由有限合法性、HW 或源 BN 代替。
   BN 已取得全部种子、末列删除、特殊分支和所有 `[0]` 分支的保持。
   共同入口归约及跨入口完整同父块比较现已证明，进而接通完整普通复制的 BN，
   包括任意嵌套附件和第一份低类复制的实际强制新首。正数低类的末孔替换及全部跨份新第零同父对
   现已证明：第零坐标围栏迫使外部同父列具有虚拟终端的第零坐标，其完整块因而不超过替换首块，
   再不超过虚拟终端。该结论覆盖任意深度、任意份数及真实整项组装，而非仅有根模板定理。
   最高类别现由实际前一阶段捐赠的严格接缝闭合，第零类别现由完整首根块等式、根前同父比较
   及外层脊提升闭合；没有把第零类别错误套入正类围栏。`standard_BN` 已证明全部源标准式满足 BN。
2. 完成最高行等剩余块类型的源／目标对应与运输；普通中间行的完整块对应及比较归约已完成。
   零绑定可用性、`base []` 不可达、键栈顺序、前缀截取、精确 `2*i` 高度、
   真实指针见证及同空隙分支分类已经完成。前 d 行的实际父搜索、全递归作用域恢复和
   单位步条件已证明。保存绑定也已接到实际键行祖先链，所有定义／复用／辅助分支的
   高行父搜索已接通，普通有限合法源的完整 d+2 行输出合法性已证明。
   源有限条件现已在标准域上证明；全部实际槽及保护列没有严格键行后裔也已接到源标准域。
   中间数值行的 SB 对现已严格归约为两个源首次输出，第零行兄弟对也已排除首次输出／辅助混合。
   每次读取的绑定代表的源祖先／非所属性现已对真实执行证明，包含所属进入／退出及可见源来源唯一性。
   实际部分变基入口、变基根的完整键相等及同一次变基的精确比较现已证明。
   完整森林移植、移植与数值运输的交换、原复制附属列表键的跨入口比较现已证明，
   也包含带显式有限前缀条件的固定外部祖先情形。
   保存绑定的键与其最近源列的实际附属列表现已逐次识别，连同列表原入口的有限合法性、
   每次真实查询的数值入口及当前材料合法性，已覆盖整个执行。
   在从这些材料明确重算的环境上，`smaller`、`equal` 和首输出键行高度均保持，
   并接到原规则的复制。现已在明确的入口绑定配对条件下，对完整真实执行证明配对保持、
   键行／标签行输出逐列相同、输出增量长度相同，覆盖所有嵌套森林及退出后的尾部。
   最终外层映射和实际保存环境也已构造，而不假设它们满足运输关系。
   中间行部分变基的初始配对现已从真实根几何及历史前缀关系构造，
   根、全部嵌套森林和外层尾部的真实键行／标签行运输已接回原复制；
   不再要求作为输入给出根查询相等、分支相同或入口配对。
   中间数值行的所有目标对现已提取真实源快照，且全部数值行与控制行的普通变基运输已接通；
   孔或捐赠替换列表、不同副本之间的比较不在未改列表定理的范围内。
   中间数值行首次输出端点的源作用域及完整源块对应已取得；键行完整分类仍未完成，
   最高标签行的端点分类现已闭合，见下文。
   `partial_rebase_encode_control` 已单独处理变基根的真实查询／保存，
   并从根后的数值视图连接完整递归运输。实际执行快照及其有限合法性、数值视图、材料来源现已取得；
   每个当前可见源位置的原入口也已定位，包括开放所属。`standard_visible_partial_rebase_control`
   因而从源根的真实几何推导历史前缀和完整控制行运输，不再把它们作为调用方前提。
   `standard_intermediate_pair_source` 现已从目标祖先路径证明可见来源、源祖先关系及共享父，
   不是把时间先后当作源作用域包含。`standard_intermediate_pair_control` 接通全部这类目标对的完整控制行运输。
   `standard_intermediate_pair_threshold` 核验实际数值激活阈值，
   `standard_intermediate_pair_first_numeric` 核验变基首列所有数值行。
   `standard_intermediate_pair_copy` 现已接通所有内部列的全部行；
   `standard_entry_block_closed` 证明完整第零块不越过原入口的局部执行终点，
   `RowRebaseTrace.block_length` 证明变基前后根块的精确长度相同。
   `standard_intermediate_pair_block` 因此是实际完整目标块的精确变基等式，而非只截取任意输出片段。
   源外层截断及其全部内部输出现已接通：`standard_entry_source_block` 识别完整源／目标块，
   `standard_intermediate_source_block` 将源完整块的实际变基接到目标完整块。
   `standard_intermediate_block_compare` 又从实际入口环境证明两边比较结果完全相同，
   没有把源 SB 不等式或目的入口比较环境作为前提。
   下一步是证明源 SB 块序条件在整个标准域上保持，再处理其他块类与具体覆盖；
   不应重复把已闭合的普通中间行整块边界、运输和精确比较列为未决。
   最高两行所用实际 P 还可能是新定义的关闭列，而不是 `entries` 记录的首次输出。
   `standard_entry_closing_block_closed` 已证明这类关闭块不越过局部执行边界；
   `standard_entry_closing_source_block` 已给出剔除定义列及附属森林输出后的精确完整块公式。
   `source_selfLatest_iff_closing_entry` 已追踪全部自登记关闭代表；正标签列的来源及两最高父相等
   也已对真实执行证明。`standard_top_pair_classes` 因而将最高标签行所有比较端点穷尽地归为
   关闭代表／关闭代表或关闭代表／森林槽，源入口是构造出来的而非外加假设。
   仍须完成较低键行的端点分类及最高两行的最终块不等式；严格关闭祖先对的完整块插入支配
   现已由 `standard_closing_block_insertion` 证明，但它尚未比较新入口自己的块；
   不把边界公式或端点分类冒充这些剩余结论。
   P/P 严格键行祖先情形的非所属源根、原关闭入口、完整旧环境保留、精确新增绑定数及完整键严格递增
   现已由实际执行推出。新增键区间内的查询高度严格比较、区间外的精确高度及完整头返回后的键表关系
   也已证明。每个实际源查询首输出的键行激活现已双向等价于旧代表绑定留在较小键环境，
   搬运后的完整键比较与选择性高度界也已接合。真实关闭对的初始拼接以及整个外层尾部的保存环境保持
   现已证明，包含完整头返回及后续查询外部父；未匹配键始终受初始插入集合约束。
   激活敏感的原根门槛现已证明随过滤、保存、完整头返回、外层执行及森林槽进入保持，
   并从真实关闭祖先对初始化。旧根绑定未保留时，不能使用全局 `2*pool.length` 增量；
   `standard_rooted_query_height` 已直接按原 BMS 阈值证明此时查询高度相等。
   `equal_shift_forces_full` 另证明：高度恰达到最大平移量，则全部初始插入键仍保留且均低于查询键；
   首高度奇偶性也强制两侧新建／复用分支一致。
   真实查询首列的数值对齐、辅助列的实际激活及首列严格差异对任意后续输出的保持现已证明；
   真实关闭对也已同时给出原根门槛和实际差向量。至少一侧复用时的完整头比较已取得。
   双方都新建时的森林／外层互递归比较现已完成，覆盖任意有限深度，允许严格差异后的输出不等长。
   标准关闭对的所有初始化条件均由实际执行推导；精确截取完整源块并连接真实 `BMS.rebase` 后，
   `standard_closing_block_insertion` 证明搬来的旧材料编码不超过旧目标块的变基。
   下一步是把新入口自己的块与这份搬来的材料比较，接通最高源块序条件及其标准域保持。
   不能把已经证明的这一半不等式当作新旧实际块之间的最终 SB。
   固定入口的整体严格保序现已完成，包括此前未闭合的同空隙森林主体、提前结束边界和
   相同列后的尾部归纳；源标准域上的精确比较及单射性也已接通。
   不应再将完整保序列为未决，但它不替代目标块序条件、变基运输或目标标准性。
3. 证明编码目标的全部 BN/SB，把最末孔引理接到真实复制，完成具体 BMS 有限覆盖引理。
   通用首对角引理、完整块的后裔锥刻画及第一个副本与变基前缀的一致性已完成；
   这些并不自动证明编码像满足 BN/SB 或所有复制接缝受控。
   再用已验证的 BMS 定义和
   实际构造的良基定理实例化 `Coverage.standard_of_coverage`，不能假设存在下降模型。
4. 接合目标规范化／标准域，构造真正的标准域保序嵌入并推出序型不等式。
   **标准源域编码的统一裸矩阵界**及种子展开的投影等式已经完成。

以上仍是实质性的工作，不是简单填几个接口。当前成功编译只认证已写出的引理，
不认证完整上界，更不等于确定最小公理体系。

## 编译

仅需 Lean 4.33.1，目前没有 Mathlib 或外部 BMS 依赖。

```sh
cd lean/BTnSSBMS
lake build
lake env python build.py --publish
```

也可以给 `build.py` 传入 `--lean /绝对路径/lean`。有界构建每次从源码编译
列出的模块，每次仅一个编译器、一个线程，编译器内存限制2048 MiB，
每模块超时120秒；超时会回收该编译器进程。这些限制不是记号定义的一部分。

缓存放在本项目的 `.build/`，`--publish` 生成不含机器路径的核验记录及公理日志；
普通 Lake 构建只使用本项目的 `.lake/`。不重写已有记号或共享基础的核验记录。
