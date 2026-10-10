# CDMN finite properties and proof boundary · [中文版](cdmn-properties.zh-CN.md)

[Definition](../../notations/CDMN/definition.md) · [Research status](../../research/cdmn/README.md). These are collected self-reviewed paper arguments, not a well-ordering proof or Lean certification. Global CDMN well-ordering remains open.

## 1 Legality and strict decrease

At an active position the control parent is c and its owner is m. Lowering preserves other parents. Every incoming source parent is below c, whereas every retained-shell parent is at least c, so the seam still has decreasing parents. Source and middle columns and their nested rows move together with addresses at or above the cut; lower references still read the original prefix. Owner-excluding scope prevents reading an enclosing owner through this copying. Recursive replacement preserves these facts.

At the first changed record, the control row loses its final empty column and becomes a proper prefix. If it disappears, every incoming record has a smaller parent than the removed control. Thus the active graph strictly decreases, regardless of later copied material. Fixed enclosing syntax preserves this decrease. Zero and empty-column cases are pruning or prefix removal. Nonzero expansion therefore cannot cycle finitely.

This does not establish well-foundedness of the raw lexicographic order or rule out infinite strict descent.

## 2 Hereditary trim and prefix-zero

The current zero index deletes the whole last column at the active copy layer, recursing through enclosing nonempty final rows. It is not the hereditary one-column-occurrence trim δ used in the previous implementation. Define δ separately: delete an empty last column; otherwise apply δ to the last record's row and remove that record if the row becomes zero. Each nonzero δ decreases the total number of nested column occurrences by exactly one. Current [0] may remove several occurrences, but also strictly decreases finite syntax.

### Finite erasure of the final record

Fix any legal external context. Write the final column as $S\mathbin{\|}(c,R)$, where S is its retained record prefix. There is a finite current-rule path that removes only $(c,R)$, preserving S, all preceding columns and the context. If S is empty, the endpoint retains an empty last column.

Use strong induction on c, and for fixed c induction on the remaining row's finite syntax size. If R ends in a nonempty column, current [0] only changes R, strictly reducing its syntax. If R ends in an empty column, use [1]. Its first seam consists of S, the optional lowered control $(c,R^-)$, and inherited records whose parents are all strictly smaller than c. Delete the extra columns after that first seam by current zeros: until the original width is restored these zeros touch only the extra suffix, and each decreases its finite syntax. Remove the inherited records from right to left by the induction hypothesis on their smaller parents. The original control now has row $R^-$, a strict syntactic reduction, or has disappeared. This is a terminating recursion on the pair (control parent, remaining row size), not an appeal to global CDMN well-ordering.

### Lifting contextual row paths

Any given finite row path can be lifted into its owning final record, preserving its preceding records and columns. For one row step, a nonempty last row column makes the outer operation recurse with the same index. An empty last row column is a successor step: perform outer [1], delete the extra suffix, then use the preceding erasure lemma to remove inherited records. This exactly deletes the row's last empty column while retaining the shell. Each row operation uses its actual owner-excluding context; no open row is treated as a closed graph.

### Two-way finite simulation

Induct on the input's finite syntax to realize δ by current operations. On an empty last column the two zero rules agree. Otherwise construct the δ path in the final row by the induction hypothesis and lift it by the preceding lemma. This uses only indices 0 and 1. Conversely, the current zero result is reached by finitely many old δ steps, which remove the entire active last column and leave enclosing syntax unchanged. Positive indices are identical in the two versions. Therefore, for every legal input in every fixed legal context,

$$D_{\mathrm{old}}(G)=D_{\mathrm{current}}(G).$$

The seeds and comparator are unchanged, so the standard domain and its finite reachability order coincide. If this order is well founded, the two versions have the same order type; this lemma does not establish well-foundedness. Same-index fundamental terms need not coincide.

### Adjacent retreat

At an active copy layer the current items, including index zero, are literal prefixes of one fixed block stream. Hereditary trim δ deletes the extra suffix to reach the preceding item. This path lifts through enclosing rows. Replacing its δ steps by the finite simulations just proved gives

$$G[n+1]\xrightarrow{\{0,1\}^*}G[n].$$

Do not replace this statement by pure-zero reachability. For example, $S_2[1]=[][0:1]$ and $S_2[0]=[][]$; current zeros take the former to `[]`, skipping the latter, whereas the path [1] reaches `[][]` exactly.

## 3 Standard-domain comparability

First work with the old rule whose zero step is δ, and write $V\preceq_\delta U$ when V occurs on U's hereditary-trim path. If V is a proper trim ancestor of U, it is an ancestor of δU, which is an ancestor of every old U[n]: positive items retain the lowered shell and only append material. An old expansion path cannot leave this trim cone without visiting V.

For two finite paths from a common starting term, induct on the sum of their lengths. Their first children are pruning-comparable. If the path from the larger child visits the smaller one, apply induction after deleting the initial segment. Otherwise its endpoint stays in the smaller child's pruning cone, so it can prune there and follow the other path. Equal first children allow immediate removal of the common step. The endpoints are equal or one finitely reaches the other.

The seeds themselves are δ-comparable, giving a common larger finite seed for any two standard terms. This proves comparability for old finite paths. The two-way finite simulation in Section 2 transfers it to the current rule. Strict decrease then identifies reachability direction with the finite syntactic comparator. This is an argument about finite paths, not well-ordering.

## 4 One-step size

For a closed input graph, count fully unfolded graph, column and record nodes, charging repeated occurrences separately. At the unique active position, the source, middle and active columns are disjoint pieces of the input. The seam contains at most the lowered active column and a subset of the source column. Relocation changes no shape. Each copied block is therefore bounded by the original input size, while enclosing material is retained once:

$$\operatorname{size}(G[n])\le(n+1)\operatorname{size}(G),\qquad n\ge1.$$

The default view writes a natural row k as a decimal number. Positive recursion enters only rows with nonempty final columns, so it never expands a natural-row abbreviation into an internal computation. A natural control only decreases by one or disappears; relocation leaves it unchanged. Giving constant weight to visible columns, records and parent tokens, and charging natural-row digit lengths, yields the same linear multiplier. Restoring parent-address digits gives the loose character bound

$$L(G[n])\le2(n+1)(L(G)+1)\operatorname{digits}((n+1)(L(G)+1)).$$

Here the input is an actual closed canonical list, not an operation-path abbreviation such as `S8[9][9]`. For an open graph, external context used as a copy source must also be counted; these bounds do not apply to the open subgraph alone. No bound on the cumulative size after arbitrarily many steps is claimed.

## 5 Paper lower bound from ordinary BMS

Use ordinary BMS short fundamental sequences and the parent-table splice formula, with the same source-side interface described in the repository's [BMS parent-table lemma](bms-le-fmp-12242444.md). This preserves the earlier self-reviewed paper route; packaging adds no BMS or CDMN Lean theorem.

Let $P_q(j)$ be the row-q parent of BMS column j. In a standard parent table these addresses are nonincreasing with q. Compress each maximal equal-parent run ending at q into $(P_q(j),q+1)$, with q+1 encoded as that many empty row columns, obtaining E. Parents decrease and row heights increase. The standard numerical matrix is recovered as the depths of its row-parent forests, so E is injective modulo padding zero rows. The h-row two-column seed maps to `[][0:h]=S2[h]`.

For last column x, highest nonzero row r, bad root $c=P_r(x)$ and block width ℓ=x−c, relocation moves parents at or above c by the appropriate block distance. Internal copied columns only relocate their parent tables. At the seam of copy t, rows q<r inherit the correspondingly moved parents of the old final column, while rows q≥r inherit the source column c's parents. This is the source-side BMS formula, not a definition of BMS using CDMN.

Let the encoded control be $(c,H)$ and let h be the preceding encoded row height, or zero if absent. If H−1>h, or H=1, a direct CDMN [n] gives the encoded positive BMS expansion. The only correction occurs when H−1=h>0: BMS merges the redundant control, but CDMN retains the shell. First lower the control row to1 with H−1 hereditary trims δ, then use [n]. Section 2 realizes each δ by a finite current 0/1 path. This removes the control while the source threshold remains h; the bad root, block and relocation are unchanged. Writing $F_n$ for the positive expansion operation,

$$
E(B[n])=\begin{cases}
F_n(\delta^{H-1}E(B)),&H-1=h>0,\\
F_n(E(B)),&\text{otherwise}
\end{cases}\quad(n>0).
$$

BMS index0 deletes the outer final column. In the current rule the encoded graph has natural rows, so one current [0] performs that deletion directly. The old implementation required $1+\sum_i h_i$ hereditary trims for final-row heights $h_i$. Do not use that old δ count as a count of current zero steps.

Seed images are standard and every source step has a nonempty finite simulation, so the entire BMS standard domain maps strictly below S2. Source standard reachability and target strict decrease make this an order embedding. **This construction is not same-index FS equality, does not show its image fills the initial segment, and alone proves neither S2=lim(BMS) nor CDMN well-ordering.** The later [sibling-code paper](../../research/cdmn/papers/s2-equals-bms.md) separately proves the S2 equality and well-ordering of that initial segment; it still does not prove global CDMN well-ordering.

## 6 What a well-ordering proof still needs

The standard graph `[][0:3][1:2;0:1]` acts on row1 while retaining row2, so the RPD maximum-control reflection lemma cannot simply be invoked at that control. Rows can also read external columns and regenerate syntax beyond the seed's original nesting depth, defeating a naive depth induction.

The strict guard blocks a known regeneration mechanism in rejected variants, and bounded checks found no standard descent for the present rule. Neither establishes global termination. The [research status](../../research/cdmn/README.md) separates these observations from open claims. The [dilation lemma](../../research/cdmn/dilation.md) provides another sufficient counterexample certificate but no known instance. The axiomatic-strength analysis remains unfinished.
