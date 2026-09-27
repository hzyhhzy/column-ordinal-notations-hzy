# SRPD/TBMS final-route material and reading order · [中文版](README.zh-CN.md)

Packaged **2026-09-28**. This directory retains only dependencies of two final routes in the [summary](../README.md): **the recursive-bank carrier for whole ordinary TBMS**, and **the fixed finite-bank carrier for `()(1^ε₀)`**. Mentioning a historical file no longer causes its entire reference graph to be imported.

The [manifest](manifest.json) pins **73 items**: 25 proof/lemma manuscripts, 39 runtime/checking code files, 2 original verification records for these routes, and 7 necessary upstream source/compiled files. Old equality attempts, unrelated candidate searches, obstruction studies and superseded test batches are excluded. Original research files outside Git were not deleted.

**These are paper arguments, not Lean certificates or a fresh independent mathematical final review.** Original papers remain mainly Chinese; this guide and the parent summary are bilingual. Read earlier contracts together with their explicit later modifications.

## 1. Shortest complete reading route

Start with the [SRPD definition](../../../notations/SRPD/definition.md) and [common-segment / well-ordering transfer](../../../notations/SRPD/correspondence.md). Target well-foundedness uses the repository's RPD proof, not finite testing here. Ordinary TBMS's native definition and attribution are in the [source notes](vendor/README.md).

Read in this order. The last two manuscripts are incremental arguments, not independent proofs omitting the preceding lemmas.

| Stage | Obligation | Full manuscripts |
| --- | --- | --- |
| 1 | Capacities after every reflection case, including seams | [Full reflection](output/tbms-e0mn-bridge-20260925/FULL-REFLECTION-CAPACITY-INTERFACE.zh-CN.md), [prefix row covariance](output/tbms-e0mn-bridge-20260925/PREFIX-ROW-STRETCH-COVARIANCE.zh-CN.md) |
| 2 | Main points, three helpers and actual parent return | [Main packets and parent renewal](output/tbms-e0mn-bridge-20260925/PACKET-MAIN-AND-PARENT-RENEWAL.zh-CN.md) |
| 3 | Persistent old labels, later recall and unbounded finite demand | [Persistent ε banks](output/tbms-e0mn-bridge-20260925/PERSISTENT-EPSILON-BOUND.zh-CN.md), [graded resources](output/tbms-e0mn-bridge-20260925/GRADED-RESOURCE-BOUND.zh-CN.md), [amplifiable resources](output/tbms-e0mn-bridge-20260925/AMPLIFIED-RESOURCE-BOUND.zh-CN.md) |
| 4 | Standard cumulative endpoints and finite registration routes | [Ordinary endpoints](output/tbms-e0mn-bridge-20260925/NATIVE-ROW-ENDPOINT-CLOSURE.zh-CN.md), [recursive endpoint closure](output/tbms-e0mn-bridge-20260925/RECURSIVE-ENDPOINT-CLOSURE.zh-CN.md) |
| 5 | All-future closure at any fixed finite depth, including subcovariance | [Recursive row-bank proof](output/tbms-e0mn-bridge-20260925/RECURSIVE-ROW-BANK-BOUND.zh-CN.md) |
| 6 | Arbitrarily many finite levels from one fixed target | [Fixed-child whole-TBMS bound](output/tbms-e0mn-bridge-20260925/FIXED-CHILD-WHOLE-TBMS.zh-CN.md) |
| 7 | One-row access and genuinely paid main-region recovery | [One-port proof](output/tbms-e0mn-bridge-20260925/ONE-PORT-WHOLE-TBMS.zh-CN.md) |
| 8 | Further tightening by actual target descent | [Trimmed seed](output/tbms-e0mn-bridge-20260925/TRIMMED-ONE-PORT-SEED.zh-CN.md), [latest weakened archive](output/tbms-e0mn-bridge-20260925/WEAK-ARCHIVE-SEED.zh-CN.md) |

In the last paper, §4 checks the weakened contract operation by operation; §5 fixes V before choosing recursive depth and then takes the supremum of source top children. The current whole-system bound is

$$\rho(\mathrm{TBMS\ Limit})\le\rho(V)<\rho(Q_w)<\rho(W[1])<\rho(W).$$

W has counts `1,2,4,8,4,2`; exact V/Qw graphs are in the [summary](../README.md) and [native-path test](../../../tests/srpd_tbms_bounds.cjs). **Only ≤ passes through the supremum; subsequent strict inequalities come from genuine target descent.**

### Specialized route for `TBMS ()(1^ε₀)`

After the finite-bank contract, read the [fixed finite ε-bank paper](output/tbms-e0mn-bridge-20260925/EPSILON-FIXED-BANK-BOUND.zh-CN.md). Sections 2–3 keep the greatest label ε=`()(1,1)` as a persistent capacity-4 finite bank; §§4–5 give actual seed reachability and arbitrary source-width initialization. This route does not require the arbitrary-depth ceiling stack.

For E=`()(1^ε)` and J=`()(1^ε,1)`, it gives

$$\rho(E)<\rho(J)\le\rho(C_\varepsilon).$$

Cε has counts `1,2,4,8,4,1,2,9,38,4,9,10,17,51`. The original §7 concerned a separate candidate search and is omitted here. This does not establish a smaller carrier or optimality.

## 2. What the construction actually does

The papers construct a **continuing fundamental-sequence descent simulation**. A state contains the source and target, per-level endpoint dictionaries, physical representatives, archives, main packets and call coupons. Each source step continues inside the same target's genuine descendants; changing seeds midway or freely editing the graph is forbidden.

After receiving source index n:

1. Compute the native TBMS child and its new cumulative row endpoints.
2. Plan finite routes from the nearest registered upper endpoints, handling lower recursive levels first without assuming whole-TBMS well-foundedness circularly.
3. Pay for the finite number of calls by real target descent.
4. Activate an existing archive, consuming one coupon, and allocate by the deletion, unit-tail or recursive-limit branch. Smaller old banks may stay in place while larger banks move with copying.
5. Once registration is complete, perform the actual main-source step, trim to the preserved healthy helper, and restore the selected archive's work state.
6. Check every bank, main packet, archive and row-code invariant for an arbitrary next index.

The latest constants have different roles: finite-bank coverage still requires `2 + row-code demand` for **all pairs, including source nonedges**; general access ports need 1; the ceiling's control background remains 2 and its high pair still needs H>r; only the high-pair-to-archive access falls to 1. This is not a global replacement of every 2 by 1.

Target-rank induction turns nonempty-step simulation into the stated rank bounds. **This is not a delivered canonical, history-independent assignment of one SRPD expression to each TBMS term, nor same-index FS commutation.** The earlier common-segment isomorphisms are a different kind of comparison.

## 3. Paper-to-code map

| Component | Implementation |
| --- | --- |
| Native ordinary TBMS | [Original TypeScript](vendor/ne-rewritten/src/notations/BM-like/TBM.ts), [time-bounded loader](output/tbms-e0mn-bridge-20260925/load-tbm.cjs) |
| Current implicit-root SRPD | [Public expander](../../../notations/SRPD/SRPD.ne-rewritten.js), [exact archived snapshot](output/m13-lists-20260926/SRPD.ne-rewritten.js) |
| Capacities, sparse native target, main-packet operations | [Capacities](output/tbms-e0mn-bridge-20260925/full-reflection-capacities.cjs), [sparse state](output/tbms-e0mn-bridge-20260925/packet-sparse-native-state.cjs), [main packets](output/tbms-e0mn-bridge-20260925/packet-main-cover.cjs) |
| Finite descent certificates for exposure, local lowering and truncation | [Independent local certifier](output/e0mn-y13425810-20260920/finite-local-certificate.cjs) |
| Recursive registration and full invariant | [Recursive core](output/tbms-e0mn-bridge-20260925/packet-recursive-row-bank-cover.cjs): `plan`, `register`, `prepareBudget`, `activate`, `allocateStep`, `allocateCeiling`, `step`, `check` |
| Latest whole-TBMS simulation | [Weak-archive module](output/tbms-e0mn-bridge-20260925/weak-archive-row-bank.cjs), applying listed deltas after the [one-port module](output/tbms-e0mn-bridge-20260925/one-port-recursive-row-bank.cjs) |
| ε₀-label special case | [Fixed finite-bank module](output/tbms-e0mn-bridge-20260925/epsilon-fixed-row-bank.cjs) |

Incremental modules apply **exact, occurrence-count-checked text patches** to the preserved simulation core and load the result in memory. All base modules are included. These patches change the simulation interface, not native TBMS or SRPD rules. `*.generated.cjs` names identify in-memory modules, not missing files.

`output/` preserves the research relative directory layout. Historical explicit-root helpers must not be confused with current implicit-root SRPD; modules load their original interfaces. Mathematical assertions, guards and failure branches were not removed to obtain passing tests.

## 4. Required supporting lemmas

Section 1 gives the main route. The following older arguments remain actual dependencies rather than historical alternatives.

| Role | Retained material |
| --- | --- |
| Amplifying finite demand and strict resource separation | [Strict separation](output/tbms-e0mn-bridge-20260925/STAR-RESOURCE-STRICT-SEPARATION.zh-CN.md), [extra-copy resource](output/tbms-e0mn-bridge-20260925/crossing-lower-extra-copy-resource.zh-CN.md) |
| Persistent finite levels and ε labels | [Layered resources](output/tbms-e0mn-bridge-20260925/LAYERED-RESOURCE-BOUND.zh-CN.md), [ε row labels](output/tbms-e0mn-bridge-20260925/EPSILON-ROW-BOUND.zh-CN.md), [native row banks](output/tbms-e0mn-bridge-20260925/NATIVE-ROW-BANK-BOUND.zh-CN.md) |
| Source cumulative labels, finite breakpoints and truncation | [Whole-TBMS interface](output/tbms-e0mn-bridge-20260925/WHOLE-TBMS-INTERFACE.zh-CN.md), [polynomial rows](output/tbms-e0mn-bridge-20260925/POLYNOMIAL-ROW-BOUND.zh-CN.md), [profile/truncation lemmas](output/tbms-e0mn-bridge-20260925/RANKED-ROW-RESERVOIRS.zh-CN.md) |
| Actual helper columns and controller maintenance | [Spaced private controllers](output/tbms-e0mn-bridge-20260925/SPACED-PRIVATE-CONTROLLERS.zh-CN.md), [finite bands](output/tbms-e0mn-bridge-20260925/FINITE-BAND-BOUND.zh-CN.md), [ω degree](output/tbms-e0mn-bridge-20260925/OMEGA-DEGREE-BOUND.zh-CN.md) |

The profile/truncation manuscript retains original §§1–3 only, used in final source-endpoint closure; its later reverse-embedding candidates are excluded. Optional smaller-seed obstructions in the weakened-archive paper and candidate searches in the fixed-ε paper are explicitly omitted too. Historical-only references remain identified as text, without importing their files or reference chains.

Code is selected by actual imports. Some required local-descent macros or loaders retain filenames from earlier Y/e0MN work; including these runtime dependencies does not import the earlier exploration's conclusions.

## 5. Reproduction

From the repository root, using only Python's standard library and Node.js; no private machine path, TypeScript installation or full NER checkout is required:

```sh
python -B research/srpd-tbms/archive/verify_archive.py
python -B research/srpd-tbms/archive/run_checks.py --suite smoke
python -B research/srpd-tbms/archive/run_checks.py --suite current
```

`current` reruns 14 weak-archive source/initialization cases, one paid-local case, the common-state check and 12 fixed-ε cases: 28 checks in total. Fixed-ε cases 3 and 8 are expected to hit the width guard and are separately **guarded**, not fully completed paths. Any other error, timeout or historical-result mismatch still fails the run.

Each child runs one bounded case with a 30-second external timeout, a 512 MiB Node heap ceiling, and the original 650 MiB RSS checkpoints and width/work limits. Execution is sequential; timed-out children are killed and reaped. This is not astronomical fixed-index countdown search. The runner does not launch every historical exploratory script.

The [post-pruning replay receipt](ARCHIVE-VALIDATION.json) is separate from the two original route-specific verification records. Retained case results and guards are unchanged. Only unrelated candidate-search/audit fields were removed from the fixed-ε record, as documented in the manifest. Finite checks test implementation and bounded examples; **the universal claim rests on the paper induction**.

## 6. Integrity, attribution and limits

The [manifest](manifest.json) records original/packaged hashes, final-route roles and changes per file, including the explicit excerpts and omissions above. Retained lemma bodies and simulator kernels are unchanged; earlier path redaction and portable-loader edits remain listed. Pruning did not change public SRPD, other notations or Lean modules.

Necessary upstream source and fixed compiler output are included with attribution; see [third-party provenance and licensing boundaries](vendor/README.md). This does not verify every source-program line, formalize the TBMS comparison, settle `…6,7,9`, or turn historical conjectures into theorems. The package supports following the arguments and code used by the final routes; it is not a backup of the entire research history.
