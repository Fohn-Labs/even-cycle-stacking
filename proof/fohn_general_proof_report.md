## Answer
Question: Can a smallest unstackable configuration of size $2^{n+1}-1$ on $C_{2n}$ exist, for any $n\ge2$, without assuming ASH?
Result: answered

No: the argument below gives an unconditional stacking sequence for every such configuration. A balanced root and at most one pivot reduce all cases to charged arm-clearing operations, leaving a path above its unconditional stacking threshold. Together with the known lower bound [1], this yields $\mathrm{stack}(C_{2n})=2^{n+1}-1$. The argument is submitted for independent checking; no literature priority is claimed. Published ingredients are the path theorem [1] and exact tree transfer machinery [2], with an elementary alternative derivation also supplied below.

## Findings
1. PROVED-HERE: I ruled out every target-mass counterexample for all $n\ge2$, and anyone can check it by the mass-sensitive path lemmas, the balanced-root inequalities, the parity budgets, and the one-pivot calculation below.

### Theorem

For every integer n>=2, every configuration of S=2^(n+1)-1 pebbles on C_(2n) is stackable. Consequently stack(C_(2n))=2^(n+1)-1, using the known matching lower bound.

Put A=2^n and B=A/2. A move removes two pebbles from a vertex and adds one to a neighbor. Every move reduces the total mass by one.

We use two unconditional published results [1], [2]:

1. stack(P_k)=2^k-1 for k>=2, from Csernak--Soukup, *Stacking and Clearing in Graph Pebbling*, arXiv:2604.22341v1, Theorem 7.4.
2. The exact tree boundary messages and root-score criterion, from Fairfax-Ball, *The stacking number of a tree*, arXiv:2609.31811v2, Theorems 3.1 and 3.3.

Neither input assumes the Almost Stacked Hypothesis. An optional elementary derivation of the required path facts is supplied after the cycle argument below. Larger path masses also stack: while above the threshold, a legal path move exists, and one can reduce to the threshold.

### 1. Boundary messages and two path lemmas

An occupied branch has message obtained by recursively applying
$
F(x)=
\begin{cases}
2x-3,&x\le1,\\
x/2,&x\ge2\text{ even},\\
(x-3)/2,&x\ge3\text{ odd}.
\end{cases}
$
The input at a vertex is its pile plus its occupied child messages. An entirely empty branch is EMPTY and contributes zero; an occupied message zero remains occupied.

At a boundary carrying q pebbles, an occupied branch with message m can be emptied to a positive boundary stack iff q+m>0; its maximum attainable pile is q+m. A tree stacks at a target iff its own pile plus its incoming occupied messages is positive.

Three elementary identities will be useful:
$
F(z-3k)\le F(z)\quad(k\ge0),\qquad F(z)\equiv2z\pmod3,
$
$
X+F(-F(X))=
\begin{cases}-3,&X>0\text{ even},\\0,&\text{otherwise}.\end{cases} \tag{1}
$
They follow directly by cases in F.

**Zero-score observation.** If an initially occupied vertex has score zero, the tree configuration is unstackable. More generally a nonpositive score divisible by three propagates over the minimal occupied subtree. Indeed, for adjacent vertices u,v in that subtree, write the score at u as -3k, and let X be the effective input at v excluding the u-side. Both sides are occupied, and
$
S_v=X+F(-F(X)-3k)\le X+F(-F(X))\le0.
$
The new score is again divisible by three, by (1). All scores on the occupied subtree are nonpositive. A target outside it receives a negative message along its empty connecting chain. The exact tree criterion proves the observation.

**Negative-message mass lemma.** For an occupied arm of L>=1 edges, excluding its boundary root, let M be its mass and m<0 its boundary message. Then
$
M-m\le2^{L+1}-2. \tag{2}
$
Attach -m pebbles at its boundary. This is an occupied zero-score vertex, so the resulting P_(L+1) is unstackable. Its mass M-m is therefore below the path threshold 2^(L+1)-1. This proves (2).

It follows that this arm can be pulled to one reserved pebble at its root with fuel p=1-m and
$
p+M\le2^{L+1}-1.
$
For m>=0, some fuel p in {0,1,2} gives p+m>=1 and p+m congruent to one modulo three. Attain that pile and burn surplus triples: root->neighbor twice, then neighbor->root, reduces the pile by three and restores the empty neighbor. An empty arm needs no operation. Every nonempty exact-unit pull uses p+M-1 moves.

**Unit-push lemma.** On a length-L path with an initially empty target endpoint, L>=2, any active configuration of mass at least 2^L-2 whose target score is congruent to one modulo three clears to exactly one pebble there.

For otherwise the target score m, a nonpositive F-output congruent to one, must satisfy m<=-5. Its last effective input is X=(m+3)/2<=-1. Write X=d+u, where d is the adjacent vertex's pile and u<0 its occupied child-branch message; let that child branch have mass C. By (2), applied to the path with L vertices,
$
C-u\le2^L-2.
$
The original mass is C+d=C-u+X<=2^L-3, a contradiction. Thus the score is positive, congruent to one, and its attained maximum can be burned to one.

For L=1 the assertion follows directly from F and its residue class.

Consequently, on this path, if internal mass M<=T-2, T=2^L, some source reserve s satisfies
$
s+M\le T. \tag{3}
$
Choose the largest s<=T-M in the correct residue; the three consecutive available residues ensure s+M>=T-2. If instead M>=T-2, choose s in {0,1,2} in that residue. Thus in all cases one may use
$
s\le\max(T-M,2), \tag{4}
$
with s+M<=T in the first regime and s<=2 in the second. For L=1 there are no internal vertices and reserve two suffices.

Existing target pebbles and source surplus can be kept inactive throughout each unit operation. The operation on the designated active configuration remains legal in their presence. Its move count is s+M-1.

### 2. Choose a balanced root

Let H_i be the mass on the n consecutive vertices i,...,i+n-1, cyclically. Since H_(i+n)=S-H_i, there is a high-to-low transition
$
H_i\ge A,\qquad H_{i+1}\le A-1.
$
Rename i as vertex0, with root pile a, antipode pile b at n, and open-arm masses q,r. Then
$
q+b\le A-1,\qquad r+b\le A-1,\qquad a>b,
$
$
a+q\ge A,\qquad a+r\ge A. \tag{5}
$
We call this root balanced. In particular it is occupied.

Our aim is to clear one open arm and the antipode in at most A moves. Remaining support is then on the other P_n with mass at least S-A=A-1, which stacks by the path theorem. There is one harmless direct tree-score case below.

An even pile h at the antipode clears into its retained neighbor in h/2 moves. An odd h>=5 clears in (h+3)/2 moves: make (h-1)/2 outward moves, then neighbor->antipode and antipode->neighbor. The latter also works for h=3 when the retained neighbor is positive. Write
$
\eta(h)=\frac{h+3\mathbf1_{h\text{ odd}}}{2}. \tag{6}
$

### 3. The antipodal piles zero, one, and two

If b=0 and a>=2, pull either complete open arm of mass q. A negative message uses p+q<=A-1, so p<=A-1-q<a by (5), and loses at most A-2 moves. A nonnegative message needs at most two fuel and loses at most q+1<=A. Empty arms require no moves.

If b=0,a=1, (5) and the mass identity force q=r=A-1. Neither arm message can be negative, by (2). The spanning path through both arms therefore has positive root score at least one, so it stacks directly.

If b=1, q<=A-2. Push a unit across either arm to the antipode with s+q<=A. It is funded since s<=A-q<=a. Empty the resulting antipodal pair into the retained arm. Total loss is s+q<=A.

If b=2, first empty its pair into the retained arm, then pull the other complete open arm. Its mass q<=A-3; negative-message total loss is at most A-1, and nonnegative-message loss at most q+2<=A-1. Fuel is available by (5) or a>=3.

### 4. An even pile next to the antipode

Assume b>=3 and one chosen arm ends in an even pile 2k. If b=3 choose such an arm whose retained neighbor is positive, whenever possible. This choice exists unless both neighbors of the antipode are zero.

First empty the ending pile inward in k moves. The shorter arm has mass q-k and n-2 edges. If its message is negative, (2) gives fuel
$
p\le B-1-q+k\le A-q\le a.
$
Combined arm-clearing loss is at most B+k-2. Including (6), with o the parity of b,
$
2\,\mathrm{loss}\le A+2k-4+b+3o
\le A+q+b-4+3o\le2A-2.
$
If the shortened message is nonnegative, at most two fuel suffices, and
$
2\,\mathrm{loss}\le2q+2+b+3o
\le2A-b+3o\le2A.
$
Thus the reduction is legal and loses at most A moves.

This case only requires n>=3: for n=2,b>=3 balance forces b=3 and both neighbors zero.

If b=3 and both neighbors are zero, choose either arm (mass q<=A-4). Donate once from the antipode to its ending vertex. Push one unit along the shorter path to that ending vertex, then move its pair back to the antipode and empty the antipodal pair into the retained arm. Total loss is
$
s+q+2.
$
If q>=B-2, (4) permits s<=2, so loss<=q+4<=A. If q<B-2, (3) gives s+q<=B, funded by (5), so loss<=B+2<=A. This includes n=2, where q=0.

### 5. Both ending piles odd

All remaining cases have b>=3 and ending piles
$
x=2t-1,\qquad y=2u-1,\qquad t,u\ge1.
$
For an arm of mass q ending in x, put M=q-x, its prefix mass. Push one unit along that shorter path to x. Empty its resulting 2t pebbles into the antipode, then clear the pile b+t there into the retained arm. It is at least four, so (6) applies.

The exact total loss is
$
s+q-t+\eta(b+t). \tag{7}
$

**Large prefix.** If M>=B-2, choose s<=2. It is funded because a>b>=3. By q+b<=A-1,
$
2\,\mathrm{loss}\le4+2q+b-t+3o
\le2A+2-(b+t)+3o\le2A,
$
where o is the parity of b+t: an even b+t is at least four, an odd one at least five. This settles either arm with a large prefix.

Hence assume both prefixes are less than B-2.

**Small opposite triple.** Suppose K=b+x+y<=A-1. Choose t=min(t,u). Then
$
b+4t\le A+1,\qquad x\le B-2.
$
By (5), a>=A-M-x>=B+2-M, so (3) on the short path is affordable with s+M<=B. Equation (7) gives loss<=A provided
$
b+3t+3o\le A+2. \tag{8}
$
For t>=2, the left side is at most A+1-t+3<=A+2. For t=1, b<=A-3: odd b gives o=0 and b+3<=A; even b gives b<=A-4,o=1 and b+6<=A+2. Thus (8) always holds.

**Large opposite triple: one pivot.** Suppose K>=A. Write the arm prefix masses as P=q-x and R=r-y. Then
$
a+P+R=S-K\le A-1. \tag{9}
$
Both ending vertices themselves are balanced roots. For example, root x at n-1 has antipode p=c(2n-1). One of its semicircles has mass b+r<=A-1. The other has mass a+P+p<=a+P+R<=A-1. The reflected argument proves the assertion for y.

Pivot to root x.

If n>=4, the new antipodal triple has total
$
K'=a+c(2n-1)+c(2n-2)\le a+P+R\le A-1,
$
because the last two terms are distinct vertices in the old R-prefix. Therefore the new balanced root is settled by sections 3 or 4, or by the large-prefix case or the small-triple case above. No second pivot is needed.

For n=3, our exclusion of large prefixes means P,R<B-2=2. Thus the new antipode p, the sole vertex of the old R-prefix, is at most one; section 3 applies.

For n=2 the remaining odd-ending case is impossible: a>=b+1,b>=3 and x,y>=1 would give mass at least nine, exceeding seven.

This exhausts all configurations.


Thus every target-mass configuration stacks. The matching cycle lower bound is [1], Corollary 7.5, giving the asserted equality. Every construction above uses actual legal moves; the universal assertion is deductive rather than an extrapolation from finite computations.

### Elementary alternative for the path ingredients

The preceding proof is already complete using the published unconditional inputs [1], [2]. For an independent derivation of all upper-bound ingredients from legal moves, the following arithmetic induction and construction suffice. This alternative uses no necessity direction of a tree criterion and no prior path threshold.

For an occupied path arm of length $L\ge1$, mass $M$, and recursively defined message $m$, prove simultaneously:
$$
m\ge3-2^{L+1}; \tag{U}
$$
$$
m<0\ \Longrightarrow\ M-m\le2^{L+1}-2; \tag{N}
$$
$$
m\ge0\ \Longrightarrow\ M\le2^L(m+3)-3. \tag{P}
$$
For $L=1$ the only negative case is the pile one, with $m=-1$; every nonnegative output has initial pile at most $2m+3$. This proves all three base bounds.

For $L\ge2$, let the first pile be $c$, and an occupied tail have mass $T$ and message $t$. Write $x=c+t$, $M=c+T$, and $k=2^{L-1}$. If the tail is empty, the one-pile bounds above imply the claimed weaker length-$L$ bounds, so assume it is occupied.

For U, child U gives $x\ge3-2k$. If $x\le1$, then $m=2x-3\ge3-4k$; if $x\ge2$, then $m\ge0$.

For N, $m<0$ forces $x\le1$, and
$$
M-m=T-c-2t+3.
$$
If $t<0$, child N and U give
$$
M-m=(T-t)-t-c+3
\le(2k-2)+(2k-3)-c+3\le4k-2.
$$
If $t\ge0$, then $t$ is zero or one. For $t=0$, child P bounds the expression by $3k-c\le4k-2$ because $k\ge2$. For $t=1$, $c=0$, and child P bounds it by $4k-2$.

For P, $m\ge0$ implies $2\le x\le2m+3$. If $t\ge0$, child P and $t\le x$ give
$$
M=x+(T-t)
\le x+(k-1)t+3k-3
\le kx+3k-3
\le2k(m+3)-3.
$$
If $t<0$, child N gives
$$
M\le x+2k-2\le2m+2k+1\le2k(m+3)-3,
$$
where the last inequality follows from
$(2k-2)m+4k-4\ge0$. This completes the simultaneous induction.

It remains to justify constructive boundary sufficiency directly. Suppose a boundary contains $q\ge0$, and its occupied arm has message $m$, with $q+m>0$. At the first arm vertex, let $x$ be its pile plus its occupied child message (zero contribution for an empty child).

If $x\ge2$, first clear the child by induction, leaving $x$. For $x=2h$, send $h$ outward; the boundary becomes $q+h=q+F(x)$. For $x=2h+1\ge3$, send $h$ outward, then boundary $\to$ first vertex and first vertex $\to$ boundary. The assumption $q+h-1>0$ ensures at least two pebbles at the boundary when the borrowed move is needed; the final pile is $q+h-1=q+F(x)$.

If $x\le1$, put $j=2-x$. The assumption $q+F(x)=q-2j+1>0$ gives $q\ge2j$. Make $j$ moves from the boundary to the first vertex. Its child-clearing effective input is now two, so induction clears the child and leaves two there. Return one pebble to the boundary, leaving $q-2j+1=q+F(x)$. Thus all moves are legal and the attained boundary pile is exactly $q+m$. This also proves the occupied-zero-message case; it requires a positive boundary. Empty arms need no action.

Bound N now proves the path upper threshold directly. Choose the first occupied vertex along a path with $N$ vertices, pile $a\ge1$. If another vertex is occupied, its remaining arm has some length $L\le N-1$, mass $M$ and message $m$. If $a+m\le0$, N gives
$$
a+M\le M-m\le2^{L+1}-2\le2^N-2.
$$
Therefore total mass at least $2^N-1$ forces $a+m>0$, and the constructive lemma stacks the path at that occupied endpoint. A configuration with only one occupied vertex is already stacked.

The exact-unit pull and push arguments in the cycle proof use only N, this constructive lemma, the congruence $F(x)\equiv2x\pmod3$, and the explicitly legal triple burn. Hence the upper-bound proof can be read entirely as a constructive argument from the move rule. The path/tree papers [1], [2] are credited for the established path formula and transfer machinery.


## Dead ends
- A positive initial spanning-path score is sufficient but need not exist at the target mass. The proof therefore permits cycle moves before the final path reduction.
- Choosing an arbitrary balanced root and checking only the two cuts incident with its antipode is insufficient. For example $(6,0,3,3,3,0)$ on $C_6$ has score zero at root zero for both those cuts. The pivot construction addresses this obstacle.
- Universal-threshold monotonicity does not justify assuming coordinatewise monotonicity of stackability. The proof uses active reserved pebbles and explicit move sequences.

## Gaps
No mathematical case is left by the argument as written; independent checking of the report is pending. No formal proof-assistant certificate or literature priority is claimed.

The stronger hypothesis that every configuration without a majority pile has an initial spanning-path certificate remains unproved and is not needed by this proof.

## Sources
1. Tamás Csernák and Lajos Soukup. Stacking and Clearing in Graph Pebbling. arXiv:2604.22341v1, submitted 2026-04-24. https://arxiv.org/html/2604.22341v1
   > "For every $n\geq2$," followed by "$\mathrm{stack}(P_n)=2^n-1$." (Theorem 7.4.)
   > "$\mathrm{stack}(C_{2n})\geq2^{n+1}-1$." (Corollary 7.5.)
   The pinned theorem statements agree between the inspected HTML and PDF.

2. John Fairfax-Ball. The stacking number of a tree. arXiv:2609.31811v2, 2026-10-09. https://arxiv.org/html/2609.31811v2
   > "In that case the greatest possible final pile at $p$ is $q+d$." (Theorem 3.1.)
   Equation (6) defines F; equations (7)-(8) define occupied messages and root scores. Theorem 3.3 gives the exact rooted criterion. Remark 3.4 distinguishes EMPTY from occupied message zero. These inputs are unconditional. The optional derivation above requires only constructive sufficiency and proves it directly.

## Method
The work developed mass-sensitive arbitrary-arm clearing, a balanced-root geometry, and the odd-ending budget and pivot as independent parts. Three subagents derived these parts; the parent integrated the argument, rechecked all funding and move counts, handled the small-cycle interfaces, and reopened the two primary sources. Separate audits checked the published inputs for hidden ASH assumptions and searched for an already stated unconditional cycle formula. No such later general theorem was found in those inspected primary sources; that bounded search is not a priority claim.

The user explicitly authorized self-written computation. A complete constructor and a separately implemented checker supplemented the proof by constructing and replaying actual legal sequences on finite configurations, including pivot and boundary cases. No numerical claim is needed to establish the theorem above. These programs used only self-written code and standard libraries, with hard memory caps within the user's ten-GB team budget. No external repository code was executed.

This report answers the counterexample-structure question by ruling out every counterexample, and its theorem also addresses the task's full deliverable. The proof does not require any earlier unchecked board report as a premise. Independent report checking is the next step.
