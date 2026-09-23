# Well-ordering of FMP in ZFC + I3 · [中文](fmp-well-ordering.zh-CN.md)

2026-09-23. Author-audited paper manuscript; **not Lean-formalized and not independently refereed**.

The subject is the packaged [FMP definition](../../notations/FMP/definition.md), [Python kernel](../../notations/FMP/fmp.py) and [NER implementation](../../notations/FMP/FMP.ne-rewritten.js): the index counts COPY operations; unavailable copied maps become empty; the actual controller self-copy is deleted before full completion. This is neither output-length reindexing nor DMP's deferred one-point completion.

This manuscript combines the earlier FMP bounded-certificate argument with the subsequently expanded weak calculus, internal-extension and minimum-bad-cap arguments. It does not infer FMP well-ordering merely from DMP well-ordering. COPY and the actual full-completion operation are verified separately below.

## 0. Theorem and axiom bound

**Theorem.** ZFC + I3 proves that the true fundamental-sequence expansion tree below each actual seed $S_n$ is well-founded. The entire standard finite domain, with column comparison, is well-ordered. Adjoining the display top preserves well-ordering.

Here I3 asserts a nontrivial elementary embedding

$$
g:V_\lambda\longrightarrow V_\lambda,\qquad
\lambda=\sup_{i<\omega}g^i(\operatorname{crit}(g)).
$$

This is a sufficient upper bound on axioms, not a necessary or optimal bound and not a lower bound on the notation's order type. Neither ZFC alone nor weak KP is claimed to prove this result. Invoking I3 does not show that FMP exceeds another notation.

The proof uses finite certificates made of bounded elementary maps. After a step, the smaller cap lies in a new inner model: it is not a smaller ordinary ordinal in the original model at every step. One finite elementary transfer contradicts a minimum bad cap. No well-founded direct limit of an infinite iteration is assumed.

## 1. Rules, auxiliary graphs and finite closure

Columns are numbered from 1. A nonempty column $r$ is a strictly increasing finite map, with $x<y$ on every edge and final edges

$$
p_r\mapsto r,\qquad e_r\mapsto r+1,\qquad 1\le p_r<e_r\le r.
$$

Its least source is $a_r$. Every target below the pivot is also a source. An internal marked edge $d\mapsto b$ has $b\ge e_r$ and an accurate pivot trace from $b$ to $d$. Let $t$ be its bottom column and $c$ its next source. The auxiliary invariant is $e_t\le c$, denoted Q. Completed standard syntax has $e_r=p_r+1$, so Q holds automatically.

COPY uses the partial increasing address map $\phi$ in the definition. An unavailable copy forgets its map but retains its point. Marks survive in the all-high, fixed-low-tail or controller-bridge cases, followed by an accurate-new-trace check. Merely checking the new trace would be a different rule.

**Finite Q lemma.** COPY preserves Q. In the all-high case, the bottom endpoint and next source are transported by the same $\phi$. In the fixed-low-tail case, the bottom endpoint is below $a$, so remains fixed and below the new next source. In the mixed case, $\phi(c)\le a$ forces $c<a$; the bottom remains in the old low tail and old Q still applies. The final trace check only removes marks. Self-closure supplies images for every controller address, so any prescribed finite number of COPY operations is available.

A positive-index step at a nonempty last column is COPY $n$ times, cut the last controller self-copy, then complete fully starting at the original last position. The original strict prefix is already complete. Section 6 verifies finite syntax and certificates for this actual operation, without treating repeated one-point scans as free descent steps.

Zero has no descent edge; its programming self-loop is excluded. Only finite seed descendants are standard. Arbitrary handwritten legal maps are not asserted to have I3 certificates.

## 2. Calculus of bounded maps

Work in a transitive ZFC model $M$, with ranks interpreted internally. Let $\alpha,\beta$ be inaccessible and let $K:V_{\alpha+1}\to V_{\beta+1}$ be elementary with $K(\alpha)=\beta$. For any set $z$ and ordinal $\eta$, define

$$
K^\#(z)=K(z\cap V_\alpha),\qquad
\rho_K(\eta)=K(\min(\alpha,\eta)). \tag{2}
$$

For a finite word $W$, compose the $\#$ operators and the $\rho$ maps in the same order. Its natural output cap $D_W$ starts with the innermost factor's output cap and transports it through the outer $\rho$ maps. An empty word is the identity and needs no finite natural cap of its own.

### 2.1 Cutback

Every such word satisfies

$$
W^\#(z\cap V_\eta)=W^\#(z)\cap V_{\rho_W(\eta)}. \tag{3}
$$

For one factor, transfer the definitions of intersection and $V_{\min(\alpha,\eta)}$ through $K$. Induct on word length. In particular, restricting $K$ to $V_{\alpha'+1}$, for $\alpha'\le\alpha$, replaces its action by

$$
K^\#(z)\cap V_{K(\alpha')}. \tag{4}
$$

Restricting several factors likewise cuts back the old word to the new natural cap: move each intersection outwards by (3) and take the minimum of the resulting output cutoffs.

### 2.2 Weak equality

For a limit cutoff $\delta$, write $F\equiv_\delta G$ when their outputs agree below $V_\delta$ for inputs $z\in V_\delta$. This is equivalent to the same test on every set $z\in M$.

Indeed, for $x\in V_\delta$, choose $\operatorname{rank}(x)<\eta$ and $\eta+1<\delta$. Each word satisfies

$$
\rho_W(\eta)\ge\min(\eta,D_W).
$$

If $x$ is above its natural cap it belongs to neither relevant output. Otherwise (3) shows that replacing $z$ by $z\cap V_\eta$ does not affect membership of $x$. The replacement belongs to $V_\delta$, so the assumed equality applies. Do this for both words.

Consequently right composition preserves weak equality, while left composition by $H$ transports cutoff $\delta$ to $\rho_H(\delta)$. Apply (3) to the already equal truncated sets. No equality of complete low-rank function graphs is being assumed.

## 3. One internal extension, not infinite iterability

**Lemma.** Suppose $M$ is an externally countably closed transitive proper-class inner model of ZFC. Let $K\in M$ be internally elementary from $V_{\alpha+1}^M$ to $V_{\beta+1}^M$, where $\alpha,\beta$ are inaccessible in $M$, $K(\alpha)=\beta$ and $\operatorname{crit}(K)>\omega$. There is an internal set-extender ultrapower

$$
I:M\longrightarrow N,
$$

whose collapse $N\subseteq M$ is externally well-founded and externally countably closed, and

$$
I\upharpoonright V_{\alpha+1}^M=K,\qquad
V_\beta^N=V_\beta^M. \tag{5}
$$

### 3.1 Construction

Let $X=V_\alpha^M$, using finite-tuple codes inside $X$. For finite seed tuples $a$ from $V_\beta^M$, define

$$
E_a=\{B\subseteq X^{|a|}:B\in M,\ a\in K(B)\}.
$$

Finite relations can be coded as subsets of $X$, hence lie in the domain of $K$. Elementarity gives compatibility with Boolean operations, projections and finite relations. Use all functions in $M$ to form the internal ultrapower; write representatives as $[f,a]$. The usual induction for Łoś's theorem gives elementarity before any assumption of well-foundedness.

### 3.2 External well-foundedness

If there were a countable descending membership chain, choose representatives $[f_i,a_i]$. External countable closure puts this sequence in $M$. Regularity of $\beta$ in $M$ permits a single seed $a^*\in V_\beta^M$ coding all the seeds. Fixed natural-index projection functions, after applying $K$, recover each $a_i$ from $a^*$.

The consecutive membership relations therefore give sets $B_i\subseteq X$ with $a^*\in K(B_i)$ on a common seed space. It is unnecessary to assume the sequence $\langle B_i\rangle$ itself lies in $V_{\alpha+1}$. Encode it by one relation

$$
C=\{(i,x):i<\omega,\ x\in B_i\}\subseteq X.
$$

Since $K$ fixes $\omega$, slices and their intersection are definable from $C$, so

$$
K\left(\bigcap_i B_i\right)=\bigcap_i K(B_i).
$$

The right side contains $a^*$, hence the source intersection is nonempty. A point in it gives a genuine infinite membership descent in $M$, contradicting Foundation.

The same argument inside $M$ handles its internal countable sequences and gives internal well-foundedness. Internal and external transitive collapses agree; therefore $N\subseteq M$.

### 3.3 Exactly which rank is preserved

Elements of $I(X)$ have representatives with range in $X$; such function graphs are still subsets of $X$. The map

$$
[f,a]\longmapsto K(f)(a)
$$

is a membership isomorphism of $I(X)$ with $V_\beta^M$. Seed representatives give surjectivity. Both structures are transitive, so this isomorphism is the identity. Testing subsets of $X$ on all seeds then gives $I(x)=K(x)$ for every $x\subseteq X$.

Thus $I$ extends $K$ on all of $V_{\alpha+1}^M$, sends $\alpha$ to $\beta$, and preserves $V_\beta$ as in (5). We do not claim equality of the two models' $V_{\beta+1}$.

### 3.4 Closure and internal coding

For an external countable sequence of elements of $N$, choose and collect representatives in $M$ and combine their seeds. The ultrapower value of

$$
x\longmapsto\langle f_i(\pi_i(x)):i<\omega\rangle
$$

is the desired sequence. Hence it belongs to $N$. This permits any specified **finite** number of subsequent extensions of the same kind.

All seeds and ultrafilters form a set in $M$. To use ordinal seeds, choose in $M$ a bijection $h:\alpha\to V_\alpha^M$. Its graph lies in $V_{\alpha+1}^M$, and $K(h)$ bijects $\beta$ with $V_\beta^M$. Encoding by these maps gives the equivalent ordinary extender presentation.

The lemma is a ZFC theorem conditional on the supplied bounded $K$, not an additional large-cardinal axiom. The critical points here are inaccessible, so the embeddings fix reals. Finite composites can be represented by a set extender, or by a finite internal construction history. No infinite-iteration theorem is needed.

Proper-class notation abbreviates the class formulas defined by these set extenders. The final argument applies elementarity only to one fixed first-order BadCap formula, by the corresponding Łoś instance. It requires neither a truth predicate for the universe nor a class-iterability axiom.

## 4. Finite FMP certificates

For an $N$-column graph, take strictly increasing inaccessible points

$$
\theta_1<\cdots<\theta_{N+1}=\Theta.
$$

Assign each nonempty column $r$ an actual set map

$$
K_r:V_{\theta_{e_r}+1}^M\longrightarrow V_{\theta_{r+1}+1}^M,
\qquad \operatorname{crit}(K_r)=\theta_{a_r}, \tag{6}
$$

realizing every listed edge: $K_r(\theta_x)=\theta_y$. An empty column names a point without requiring an attached map.

For a marked edge $d\mapsto b$, compose the accurate trace maps from bottom to top. An outer factor's endpoint is at least one point beyond its pivot, so its domain covers the inner word's natural output cap. Restrict outer factors to the required rank structures to form an actual bounded elementary composite $W$; do not assume that inclusion between different ranks is elementary.

For the bottom column $t$, put $\alpha_t=\theta_{e_t}$. Then

$$
\Delta=W(\alpha_t),\qquad \theta_b<\Delta\le\theta_{b+1}. \tag{7}
$$

Also $\alpha_t<\Delta$, since the bottom factor sends its endpoint to a larger point and outer factors do not decrease ordinals. The marked-edge certificate is

$$
K_r^\#(z)\cap V_\Delta=W^\#(z)\qquad(z\in V_\Delta). \tag{8}
$$

Section 2 extends this identity to every set input in the model. Auxiliary graphs may have $\Delta<\theta_{b+1}$: incomplete gaps must not be treated as saturated.

### 4.1 Recovering Q from semantics

Let $c$ be the next source. Its next target gives $K_r(\theta_c)\ge\theta_{b+1}\ge\Delta$. If $\theta_c<\alpha_t$, then $W(\theta_c)<\Delta$. At input ordinal $\theta_c$, the left side of (8) is $\Delta$ and the right side is smaller, a contradiction. Thus $\alpha_t\le\theta_c$, exactly Q. After COPY, Q can also be recovered once the new weak certificates are established.

### 4.2 First-order definability

The certificate quantifies over finite point lists, finitely many set maps and satisfaction for set-sized rank structures. Weak equality only quantifies over $V_\Delta$. Thus “$P$ has a certificate with total cap $\Theta$” is one first-order set-theoretic formula. It contains no external closure, class embedding or future iteration-strategy parameter.

## 5. COPY preserves certificates

Apply Section 3 to the controller $K_N$, with source endpoint $\alpha=\theta_e$ and target endpoint $\beta=\Theta$, obtaining $I:M\to M'$. Name the new points by

$$
\theta'_i=\theta_i\ (i\le N),\qquad
\theta'_{N+s}=I(\theta_{p+s})\ (1\le s\le N-p+1). \tag{9}
$$

The seam is $I(\theta_p)=\theta_N$. For an incomplete controller, the old $\Theta$ becomes the internal point at position $N+e-p$, not necessarily the next position $N+1$. The new total cap is $I(\Theta)$.

Retained maps at $r<N$ have graphs of rank below $\Theta$. Since the models share $V_\Theta$, these maps, points, inaccessibility facts and weak certificates remain available. A surviving copy uses $I(K_r)$; every address named by that copy satisfies

$$
\theta'_{\phi(x)}=I(\theta_x). \tag{10}
$$

An unavailable copy is empty and needs no attached map, while its ordinal point remains. Self-closure ensures that the controller's self-copy is nonempty, allowing the next COPY.

It remains to check marks. Write $\kappa=\theta_a=\operatorname{crit}(I)$. For $z\in M$,

$$
(IF)^\#(I(z))=I(F^\#(z)),\qquad
I(z)\cap V_\Theta=K_N^\#(z). \tag{11}
$$

For a bounded word $H$ in $M'$ and $z\in M'\subseteq M$,

$$
H^\#(I(z))\equiv_{\rho_H(\kappa)}H^\#(z). \tag{12}
$$

For evaluated sets, $\equiv_\gamma$ means equality after intersecting with $V_\gamma$. Equation (11) follows from elementarity and (5); (12) follows from $I(z)\cap V_\kappa=z\cap V_\kappa$ and cutback.

### 5.1 All-high trace

The survival check guarantees that every nonterminal copied factor actually has map $I(K)$. The new trace and natural cap are the images of the old ones, and elementarity transfers the certificate. The terminal source may lie in the low region; its column need not carry a map.

### 5.2 Fixed low tail

Write the old word as $U\circ V$, with the low tail beginning at $u<a$ and natural cap $D_V\le\theta_{u+1}\le\kappa$. The actions of $V$ and $IV$ agree weakly below $D_V$, by fixed low-rank inputs and output truncation. Even when $D_V=\kappa$, only weak equality is asserted, not fixedness of the full map graph.

The new word is $(IU)\circ V$, with natural cap $D=\rho_{IU}(D_V)$. Since $D_V\le I(D_V)$, we have $D\le I(\Delta)$. Left composition transports the weak equality to $D$; combine it with the transported old certificate. If $U$ is empty, interpret it as the identity.

### 5.3 Mixed trace: all three cutoffs

Let the first low factor satisfy $a\le u<p$. The controller star $u\mapsto v=\phi(u)$ supplies a trace word $T$ with natural cap $\tau$. Write the old marked word as $U\circ V$, with old cap $\delta=\rho_U(D_V)$.

The guard $\phi(c)\le a$ and strict increase of $\phi$ force $c<a$, hence the marked source $d<c<a$ is fixed. The new accurate word is exactly

$$
W'=(IU)\circ T\circ V. \tag{13}
$$

The copied high part reaches $v$, the old controller bridge reaches $u$, and the old low tail reaches $d$. Accuracy of a coincidental new path would not by itself justify this factorization.

For $z\in M'$, use

$$
\begin{aligned}
(IF)^\#(z)
&\equiv_{\rho_{IF}(\kappa)}(IF)^\#(I(z))\\
&=I(F^\#(z))\\
&\equiv_{I(\delta)}I((U\circ V)^\#(z))\\
&=(IU)^\#(I(V^\#(z)))\\
&\equiv_{\rho_{IU}(\tau)}(IU)^\#(T^\#(V^\#(z))).
\end{aligned} \tag{14}
$$

The last line replaces $I$ below $\tau$ by $K_N$ using (11), then applies the controller's star certificate. The equality is therefore valid below the minimum of three cutoffs; it remains to cover the new natural cap $D$.

Because $D_V\le\theta_{u+1}\le\alpha$, testing the controller's weak equality on ordinal $D_V$ yields

$$
\rho_T(D_V)=\min(I(D_V),\tau)\le I(D_V).
$$

Consequently

$$
D=\rho_{IU}(\rho_T(D_V))\le I(\delta),\qquad
D\le\rho_{IU}(\tau). \tag{15}
$$

The new next source is at most $\kappa$; under $IF$ it maps to the next target, which is at least the accurate word's natural cap. Hence

$$
\rho_{IF}(\kappa)\ge D. \tag{16}
$$

Equations (14)–(16) prove the new weak certificate without enlarging any equality interval. The position of a trace's natural cap between its head and the next point is the general endpoint fact (7), not the certificate currently being proved.

All cases close. Recover Q by Section 4.1; the increasing address map preserves the remaining finite syntax.

## 6. Full completion: induction over actual events

Freeze all entry-old points, attached maps and historical marked words. Integer addresses move, but historical points and maps do not. Process entry-old columns in left-to-right order, skipping new restriction families.

### 6.1 Source and target capacity; no competition

Assume earlier events are correct. The lowest native restriction retains the old pivot, and packets do not alter final sources. Thus a current old mark still follows the entry-old base points.

If the historical parent relation is $p_u=v$ and the event at $v$ inserts $h_v$ points, the old endpoint $e_u>v$ moves at least to $v+h_v+1$. At the event for $u$,

$$
h_u=e_u-p_u-1\ge h_v.
$$

Along the accurate trace, the bottom width $h$ is at most every higher factor's available family width.

For a carrier star $d\mapsto b$, let $e_0(t)$ denote the **historical endpoint** used by the bottom event. Its position there is $d+h+1$. These sources lie no later than $t$ and never move in the remaining rightward scan. Historical Q gives $e_0(t)\le c_0$; the carrier's next old source can only move right later. Therefore at the current event,

$$
d+h<c.
$$

On the target side, the family at $b$ has width at least $h$, placing $b+1,\ldots,b+h$ before the next old point. The carrier's next target is not earlier than that point. Every packet therefore lies in genuine open source and target gaps. Distinct old marks have disjoint gaps on both sides. There is no collision, competition or deduplication.

### 6.2 Certificates for propagated edges and marks

Let $W$ and $\Delta$ be the old mark's historical word and natural cap. The bottom family and every family above it contain the first $h$ corresponding restrictions. Their maps carry each newly named source up to the newly named head point, giving

$$
W(\theta_{d+j})=\theta_{b+j}<\Delta\qquad(1\le j\le h).
$$

Historical weak equality gives

$$
K_r(\theta_{d+j})=\theta_{b+j}.
$$

Here $\theta_{b+j}$ denotes the newly inserted point, not the original value attached to the integer $b+j$.

The accurate trace of the new mark is

$$
b+j\longrightarrow\cdots\longrightarrow t+j\longrightarrow d+j.
$$

Its factors are restrictions of the corresponding historical maps; the capacity lemma supplies every required member. Cutback reduces the historical word to this trace's natural cap, which is no greater than $\Delta$. Old marks follow the lowest restrictions and also need only smaller caps. Both certificates follow from the historical equality, never by extending a previously shortened equality.

### 6.3 The native family consists of actual restrictions

When the carrier itself is processed, let its final sources have gap $p<e$, with $h=e-p-1$. Between the retained points $\theta_r,\theta_{r+1}$ insert

$$
\xi_s=K_r(\theta_s)\qquad(p<s<e).
$$

These are strictly increasing inaccessible points in a genuine gap. The map for family member $j$ is

$$
K_r\upharpoonright V_{\theta_{p+j+1}+1},\qquad 0\le j\le h.
$$

The final member retains the original map; earlier members are smaller restrictions. This realizes exactly the continuous tail and restrictions output by the code. Each new direct star has a one-factor accurate word consisting of the corresponding lower family member, so cutback immediately proves its certificate.

Historical natural caps for old and newly propagated stars are at most the carrier's entry base point $\theta_r$, since their heads lie strictly before the carrier. Even the lowest restriction has output cap strictly above $\theta_r$. Restricting the carrier cannot remove a required weak cutoff, and subsequent restrictions in accurate words only reduce obligations.

### 6.4 Closing syntax and the event induction

Packets stay in old gaps, leave $a,p,e$ unchanged and remain in the star window. Raising a family pivot from $p$ to $p+j$ creates only lower-target obligations covered by the filled continuous source interval; old obligations are covered by self-closure. New stars have accurate traces. Completed restrictions have adjacent final sources and therefore Q. Unprocessed carriers preserve Q under common relabeling and the packet-capacity argument, or recover it from their weak certificates.

Only now is this event admitted to the induction hypothesis. Each event creates finitely many restrictions, and there are finitely many entry-old columns. The scan terminates, every output column is completed, every nonempty map has an internal certificate, and the total cap is **unchanged**. The original completed prefix requires no insertion, so scanning from the original last position agrees here with scanning the whole graph.

This proves closure for actual full FMP completion. A deferred DMP sweep can use the same calculus, but the indexed rules are not equal. No standard-domain embedding between those systems is needed.

## 7. Strict cap inequality for one true step

Let $A$ have total cap $\Theta=\theta_{N+1}$.

A cut retains the first $N$ named points and has cap $\theta_N<\Theta$ in the same model.

Otherwise perform the prescribed $m>0$ COPY operations. Sections 3 and 5 preserve the model conditions for each of these finitely many extensions. Let their composite be $J:M\to M'$. The final actual controller self-copy has base point $J(\theta_N)$ and right cap $J(\Theta)$. Deleting that whole column gives

$$
\Theta'=J(\theta_N)<J(\Theta). \tag{21}
$$

Section 6 inserts only internal points and leaves $\Theta'$ unchanged. Every resulting map is an internal image, retained map or restriction and genuinely belongs to $M'$. No external complete owner is supplied afterwards.

Equation (21) does **not** assert $\Theta'<\Theta$; the change of model is essential.

## 8. I3 supplies every actual seed

Write $\kappa_i=g^i(\operatorname{crit}(g))$ and choose $\theta_i=\kappa_{i-1}$. These points are inaccessible. Let $g_0=g$ and, for $s>0$, put

$$
g_s=(g^s)*g,
$$

where $g^s$ is ordinary composition and $*$ is Laver application, defined by images of bounded restrictions followed by union. Its standard identities

$$
(j*k)\circ j=j\circ k,\qquad
\operatorname{crit}(j*k)=j(\operatorname{crit}(k))
$$

give

$$
\operatorname{crit}(g_s)=\kappa_s,\qquad
g_s(\kappa_t)=\kappa_{t+1}\quad(t\ge s). \tag{22}
$$

For the second identity, evaluate $(g^s*g)\circ g^s=g^s\circ g$ at $\kappa_{t-s}$. See Dougherty, Section 1, in the references for the application identities.

The actual seed begins with an empty column and the edges $1\mapsto2,2\mapsto3$, realized by a restriction of $g_0$. Each subsequent pair has least source $a=2i+1$, displacements $d=1,2$ and edges $x\mapsto x+d$. Assign that column

$$
(g_{a-1})^d\upharpoonright V_{\theta_e+1}. \tag{23}
$$

Equation (22) realizes every explicit and cap edge and gives the correct critical point. Initial star sets are empty. Thus a single I3 witness supplies certificates for **every** finite seed, not just one fixed low fragment.

## 9. Minimum bad cap excludes an infinite branch

Fix a seed $S$ and define the first-order formula

$$
\operatorname{Good}_S(P,\Theta):
\quad P\text{ is a finite true descendant of }S
\text{ with a certificate of cap }\Theta.
$$

Let $\operatorname{BadCap}_S(\Theta)$ mean that some such $P$ has a real coding an infinite true expansion branch. Path facts are arithmetic, and Section 4.2 gives first-order definability of certificates. This formula mentions neither the I3 witness, external closure nor class embeddings.

Suppose $S$ has a bad branch. Section 8 makes the class of bad caps nonempty. Choose a witness $\Theta_0$ and use Separation within $\Theta_0+1$ to obtain a least bad cap $\Theta$. Minimize over **all certified finite descendants**, not just the seed. Fix witnesses $P$, its certificate and branch real $b$; start in $V$.

If the branch begins with a cut, its child has smaller cap $\theta_N$ in the same model, immediately contradicting minimality. Otherwise perform only the finitely many internal extensions needed for that first actual step, giving $J:V\to M'$. Elementarity transfers minimality:

$$
M'\models\text{“}J(\Theta)\text{ is the least bad cap”.} \tag{24}
$$

The codes for the seed, $P$, the index and the branch real are fixed. The same actual branch tail belongs to $M'$. Recursive syntax is absolute to this transitive inner model, so it is an infinite branch from the actual $P[m]$.

By Section 7, that child has in $M'$ a certificate of cap $J(\theta_N)<J(\Theta)$ and is a finite descendant of the same seed. This contradicts (24).

Only one finite macro-step was performed. No infinite system of models or well-founded direct limit was assumed. Nor was inner-model well-foundedness substituted for external well-foundedness: the contradiction retains the same real coding the actual branch.

## 10. From branch well-foundedness to the standard column order

Do not assume that ordinary lexicographic order on all finite integer words is well-founded.

**Prefix barrier.** If $P$ is a prefix of $Q$, a finite expansion path from $Q$ that leaves the $P$-prefix cone must first visit $P$ itself. While the length exceeds $|P|$, modifying only the last column cannot touch $P$. Before changing a column of $P$, the entire right tail must have disappeared.

**Comparability.** For standard $A,B$, nested seeds provide a common seed and two finite witness paths. Induct on their total length. If either path is empty, comparability is immediate. Otherwise their first children $C,D$ are prefix-comparable; suppose $C$ is a prefix of $D$.

- If $B$ still extends $C$, cut from $B$ to $C$ and follow the path to $A$.
- Otherwise the prefix barrier forces the path to $B$ through $C$; apply induction to shorter paths starting at $C$.

Finite reachability is therefore a total preorder. Section 9 rules out cycles and infinite branches, making strict reachability a strict total order. An infinite descending sequence in that order would concatenate into an infinite expansion branch. Hence it is a well-order. The required prefix facts come from COPY followed by cut and from prefix-compatible full completion.

**Counts and column comparison.** With a left prefix fixed, all positive indices have the same first replacement column. Repeatedly expand and cut off the new right tail; this is a deterministic local trajectory. An infinite trajectory would concatenate into a genuine infinite branch, so it is finite. Give the empty column count 1 and each nonempty column one plus its replacement count.

Each true step either deletes the last count or decreases it by 1 and appends a finite suffix; earlier counts remain fixed. Thus it strictly decreases the ordinary count-word lexicographic order. Comparability implies that distinct standard graphs cannot have the same word, and that lexicographic direction agrees with reachability. Comparing trajectories at the first differing column is precisely the implemented comparison. The shortcut omits only marks and head endpoints that cannot affect the first replacement.

This proves standard well-ordering and unique standard count representation, not uniqueness of arbitrary legal handwritten syntax. The common-seed argument covers the entire union, rather than isolated finite fragments. The display top first enters a seed, so adjoining it preserves well-ordering.

## 11. Audit boundary and axiom ledger

- This is a paper argument in ZFC + I3. The main technical audit targets are the internal extension in Section 3, the three mixed-copy cutoffs in Section 5.3 and the full-completion event induction in Section 6.
- I3 is used in Section 8 to supply every actual finite seed. The remaining arguments are in ZFC conditional on the supplied finite certificates.
- Proper-class model notation does not add a truth predicate or an infinite iteration strategy. Section 3 explains its set-extender coding; Section 9 transfers one fixed first-order formula.
- The theorem concerns designated standard descendants, not every legal raw graph.
- Neither “all local counts are finite, therefore global descent terminates” nor “the new cap is below the old cap” is used.
- I3, internal extenders, certificate transport and this theorem are not formalized. No abstract Lean interface assuming well-foundedness is offered as a proof of actual FMP. Existing seven-system Lean receipts do not cover FMP.
- Bounded tests check kernels, marks, prefixes, counts and displays, not the infinite-domain theorem. See [validation records](../../VALIDATION.md).
- No exact FMP comparison with BMS, Y, RPD, ARD or IBLP is established here. A stronger proof hypothesis does not imply a stronger notation.

## 12. Sources and attribution

The finite-map rules and manuscript are project research. This self-contained edition combines the 2026-09-20 full-completion certificate argument with the weak-calculus and minimum-bad-cap details expanded on 2026-09-23. It does not relabel the later DMP rule as FMP, and it redistributes neither private paths nor third-party PDFs.

- [Astra–Qi, IBLP well-foundedness manuscript](https://github.com/QiRenrui/basic-laver-pattern/blob/main/IBLP_wellfoundedness_en.pdf): the bounded-certificate and minimum-bad-cap organization. FMP's full completion, unavailable-map projection and closure are proved here, not obtained by unconditional transfer of IBLP-specific pattern lemmas.
- [Dougherty, Critical points in an algebra of elementary embeddings, II](https://arxiv.org/abs/math/9503204): Section 1's application/composition identities, used in Section 8.
- [Goldberg, Rank-to-Rank Embeddings and Steel's Conjecture](https://math.berkeley.edu/~goldberg/Papers/RankIntoRankEmbeddingsAndSteel%27sConjecture.pdf): background on internal extenders and finite composition. The one-extension argument needed here is supplied above, without importing an additional iterability theorem.
