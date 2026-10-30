## Answer

The path theorem applies to arbitrary configurations, but its leaf-clearing induction does not transfer directly to an even cycle. Its crucial step retains a path with one fewer vertex at the corresponding exponential threshold. Clearing one cycle vertex leaves too long a path. More strongly, the explicit mass-(2^(n+1)-1) family below is unstackable on every initial spanning path, for every n>=2, although an explicit cycle prefix makes it stackable. Any successful sequence for that family must use every cycle edge.

An elementary, separate derivation of the known lower obstruction is also given. It uses move counts, a distance potential and a modulo-three signed potential, without the path upper theorem or the general tree necessity theorem.

## Findings

I proved an all-n obstruction to using any initial spanning path, and anyone can check it by the cut-score formulas and the explicit legal cycle prefix below. I also reconstructed the precise path-induction budget and supplied an independent derivation of its known endpoint lower obstruction.

### 1. KNOWN: what the path upper proof actually does

Write P_k for the path with k vertices. Csernak--Soukup prove stack(P_k)=2^k-1 [1]. Their upper induction clears a leaf of P_(k+1), starting at exact mass 2^(k+1)-1 and losing at most 2^k moves. At least 2^k-1 pebbles remain on P_k. Even leaf piles are sent inward in pairs. Odd piles at least five use pair transfers followed by a borrow-and-return pair of moves. A leaf singleton is paired with a delivered pebble; a leaf pile of three uses an occupied neighbour or a delivered pebble there. Thus the argument already allows arbitrary other piles. The lower witness has endpoint piles 2^k-3 and one.

For clarity, the individual clearing costs in this reconstruction are:

- Leaf pile zero: zero.
- Even pile p: p/2.
- Odd pile p>=5: (p+3)/2.
- Pile one: at most 2^k.
- Pile three with occupied neighbour: three.
- Pile three with empty neighbour: at most 2^(k-1)+2<=2^k, for k>=2.

The odd-pile estimate is justified at exact total mass: if the configuration is not already stacked, an odd endpoint pile is at most 2^(k+1)-3. For larger starting masses, first make legal moves until this exact mass is reached, unless a stack is reached earlier. Pigeonhole supplies a source with at least two pebbles while the mass is above this threshold.

The claimed endpoint-delivery budget is the ordinary pebbling bound on a path, together with extraction of the ancestors of the one delivered pebble. If at most q initial pebbles participate, delivering exactly one of them uses q-1 moves; pairing it with the reserved singleton and moving that pair uses one more.

### 2. PROVED-HERE: the exact two failures of a direct lift

First, deleting a vertex from C_(2n) leaves P_(2n-1). Its universal path threshold is 2^(2n-1)-1. For n>=3 this exceeds even the original cycle mass 2^(n+1)-1. Retaining 2^n-1 pebbles after a leaf-sized loss therefore does not meet that threshold. A useful cycle reduction must clear an entire side so that only an n-vertex path remains, or stack directly. Verified fohn report #20 does this with a balanced root and arm operations.

Second, folding is only a pushforward operation. The map
\[
 f(i)=\min(i,2n-i),\qquad 0\le i<2n,
\]
takes C_(2n) to P_(n+1). Each legal cycle move becomes a legal path move after aggregating piles in each fibre. A legal path move need not lift: for example, on C_4 the configuration (0,1,0,1) has no legal move, whereas its folded image (0,2,0) is already stacked. The two preimages holding the folded pair are different vertices.

These statements isolate a failed proof strategy, not an unstackable cycle configuration.

### 3. KNOWN: the exact path score used for the obstruction

Use the transfer function from [2], Section 3:
\[
F(x)=
\begin{cases}
 2x-3,&x\le1,\\
 x/2,&x\ge2\text{ even},\\
 (x-3)/2,&x\ge3\text{ odd}.
\end{cases}
\]
An entirely zero arm has the distinct state EMPTY and contributes zero. An occupied arm sends F of its first pile plus its child's occupied message; an absent or EMPTY child contributes zero. In particular, an occupied message zero is not EMPTY. The rooted score S_v is the pile at v plus the numerical contributions from its incident arms. By Theorem 3.3 of [2], stacking at v is possible exactly when S_v>0, and its construction then leaves S_v pebbles.

Only this published criterion and these explicitly stated arithmetic rules are needed for Findings 4--5. Finding 6 has a separate proof directly from moves.

### 4. PROVED-HERE: every initial spanning path can fail, at the conjectured mass

Let N=2n, A=2^n, n>=2, and label C_N cyclically by 0,...,N-1. Consider
\[
 c_0=2A-4,\qquad c_1=c_n=c_{N-1}=1,
\]
with all other piles zero. The three singleton positions are distinct, including when n=2. The mass is 2A-1.

For each edge e, put T_e=C_N-e, and calculate its rooted path scores from this initial configuration. At the occupied vertex n,
\[
 S_n^{(e)}=
 \begin{cases}
 4-A+(n\bmod2),&e=\{0,1\}\text{ or }\{N-1,0\},\\
 0,&\text{otherwise}.
 \end{cases}                                                    \tag{1}
\]
All these values are nonpositive multiples of three. We now calculate them and justify why every other target also has nonpositive score.

Reflection i -> -i modulo N fixes the configuration and n. It suffices to delete e_k={k,k+1}, 0<=k<=n-1.

If 1<=k<=n-1, the branch from n towards k+1 is EMPTY. The other branch traverses n+1,...,N-1,0,1,...,k. The zero tail beyond vertex 1 is EMPTY. Starting at 1 and moving towards n, the messages are
\[
 F(1)=-1,\quad
 F(2A-5)=A-4,\quad
 F(A-3)=A/2-3.
\]
There remain n-2 zero vertices before the root. For j>=2,
\[
 F(2^j-3)=2^{j-1}-3.
\]
Consequently F^(n-2)(2^(n-1)-3)=-1; for n=2 there is no further iteration and A/2-3=-1 already. The root score is 1-1=0.

For the cut {0,1}, the branch ending at vertex 1 sends
\[
 F^{n-1}(1)=3-A.
\]
The other branch starts from vertex 0, then N-1, then n-2 zeros, and sends
\[
 F^{n-2}(A/2-2)=
 \begin{cases}0,&n\text{ even},\\1,&n\text{ odd}.\end{cases}
\]
Here F(2A-4)=A-2 and F(A-1)=A/2-2 produce the displayed starting value. The parity formula follows from
\[
 F^2(2^j-2)=2^{j-2}-2\quad(j\ge3),
\]
terminating at 0 for even n and at F(2)=1 for odd n. The n=2 case has no iteration and starts at zero. This proves (1); reflection supplies the other cuts. Since A is 1 modulo three for even n and 2 for odd n, the exceptional scores are divisible by three. They are zero at n=2 and at most -3 for n>=3.

Here is the necessary propagation argument, including empty tails. Let K be the minimal subtree of T_e containing the initially occupied vertices. Across an edge uv in K both sides are occupied. Write X,Y for the two effective inputs excluding the message across that edge. Then
\[
 S_u=X+F(Y),\qquad S_v=Y+F(X).
\]
Direct evaluation of F gives
\[
 F(z-3)\le F(z),\quad F(z)\equiv2z\pmod3,\quad
 y+F(-F(y))=
 \begin{cases}-3,&y\ge2\text{ even},\\0,&\text{otherwise}.\end{cases}
\]
The first difference F(z)-F(z-3) is 6 for z<=2, 3 at z=3,4, zero for odd z>=5, and 3 for even z>=6; hence it holds at every transition too. For the last identity, y<=1 and odd y>=3 give F(-F(y))=-y; positive even y gives -y-3.

If S_u=-3h with h>=0, substitute X=-F(Y)-3h:
\[
 S_v=Y+F(-F(Y)-3h)
       \le Y+F(-F(Y))\le0.
\]
Also S_u congruent to zero implies X congruent to Y modulo three, whence S_v congruent to zero. Starting at n, this propagates to every vertex of K. Each component outside K is initially empty. Its message directed away from its attachment vertex is F(S_attachment)<0; applying F at each subsequent zero vertex keeps it negative. Each score outside K is thus negative. EMPTY incoming sides contribute zero throughout.

Therefore every rooted score on every T_e is nonpositive. The criterion in Finding 3 proves that c is unstackable on every initial spanning path.

A useful corollary is:
\[
 \boxed{\text{Every stacking sequence from this c must use every cycle edge.}}
\]
If a cycle edge were unused, the sequence would be legal on the corresponding T_e, a contradiction. This assertion does not prohibit returning to a path after some cycle moves.

### 5. PROVED-HERE: a legal prefix repairs that obstruction

For the same configuration, a batch u->v [b] means b consecutive moves, each removing two at u and adding one at v.

Perform these batches in order:
\[
 0\to1\ [A/2-1],
 \qquad i\to i+1\ [2^{n-i-1}]\quad(i=1,\ldots,n-1),
 \qquad n\to n+1\ [1].
\]
The first batch leaves A-2 at 0 and A/2 at 1. Every subsequent batch along that half-cycle has exactly twice its batch count at its source and clears that source. Its last delivery makes the singleton at n a pair, so the final batch is legal. The prefix uses
\[
 (A/2-1)+(A/2-1)+1=A-1
\]
literal moves, in n+1 batches.

Its remaining support lies on the n-vertex path
\[
 0,N-1,N-2,\ldots,n+1.
\]
There are A pebbles left: A-2 at 0 and one each at N-1 and n+1. For n=2 these last two positions coincide, giving two pebbles there.

For n>=3 the branch into 0 has initial piles (1, followed by n-3 zeros, followed by 1), and its message is
\[
 F(1+F^{n-2}(1))=F(4-A/2)=5-A.
\]
For n=2 the branch message is F(2)=1=5-A. The root score is in every case
\[
 (A-2)+(5-A)=3.
\]
The constructive path criterion therefore completes a stack of three pebbles at 0. The total sequence has exactly (2A-1)-3=2A-4 moves. This proves concretely why the initial spanning-path obstruction is compatible with stackability on the cycle.

### 6. PROVED-HERE: an elementary derivation of the known endpoint lower obstruction

This rederives Theorem 7.3 of [1], using different local accounting. Let a path have vertices 0,...,n with n>=1. Initially put M at 0 and one at n, all other piles zero, where
\[
 M<2^{n+1},\qquad M\equiv2^{n+1}\pmod3.
\]
These conditions imply 1<=M<=2^(n+1)-3. Suppose a finite legal sequence ends with a positive stack at j.

For an arm incident to j, let O and I count moves across its boundary towards and away from j, respectively, and write phi=O-2I. This is the change at j attributable to that arm. Other moves at j may interleave. An initially occupied arm which ends empty has O>=1: its last affecting move must be outward, since an internal or inward move leaves a pebble in the arm.

Consider first the arm containing M, at distance j>=1. Use the arm-only potential W=sum_(i=1)^j 2^(-i)c_i, excluding the target. Moves on the other side of the target do not change W. Let a_i and b_i count moves towards and away from the target across edge i. The cleared vertices' weighted balances give
\[
 0=M/2^j-a_1+b_1/2-3\sum_{i=2}^j2^{-i}b_i.
\]
Since phi_L=a_1-2b_1, rearrangement gives the exact identity
\[
 \phi_L=\frac{M}{2^j}
          -3\sum_{i=1}^j2^{-i}b_i
       \le\frac{M}{2^j}.                                  \tag{2}
\]
Rootward moves preserve the weighted sum; away moves decrease it. All branch vertices telescope from their initial piles to zero. The target's contribution from these selected moves is phi_L, independently of the other incident arm.

Alternating the signs with distance instead yields
\[
 \phi_L\equiv(-1)^jM\pmod3.                                \tag{3}
\]
Explicitly, the arm-only signed balance is
\[
 0=(-1)^jM+2a_1-b_1+
       3\sum_{i=2}^j(-1)^i(b_i-a_i).
\]
As 2a_1-b_1 is congruent to -phi_L modulo three, (3) follows. This again permits arbitrary other-side interleaving.

By (2), phi_L<2^(n+1-j). By (3), phi_L is congruent to that same power of two: multiplying the hypothesis on M by (-1)^j changes exponent n+1 to n+1-j modulo three. The next smaller integer in this residue class is three below it. Hence
\[
 \phi_L\le2^{n+1-j}-3.                                    \tag{4}
\]

Now consider an arm consisting of a singleton at distance L>=1 and zeros elsewhere. Its flux satisfies
\[
 \phi_R\le3-2^{L+1}.                                      \tag{5}
\]
For L=1, the endpoint balance 1+I-2O=0 and O>=1 give phi_R=2-3O<=-1. For L>=2 let psi be the tail flux into the nearest vertex. Its initial pile is zero, so final balance gives I+psi-2O=0. The induction bound on the tail and O>=1 give
\[
 \phi_R=2\psi-3O
 \le2(3-2^L)-3=3-2^{L+1}.
\]
This induction permits all outside moves to interleave; only final vertex balances are used.

If 1<=j<=n-1, the target initially has zero, and (4)--(5), with L=n-j, give final pile
\[
 \phi_L+\phi_R\le
 (2^{n+1-j}-3)+(3-2^{n-j+1})=0.
\]
For j=0, its initial M plus (5) is at most M+3-2^(n+1)<=0. For j=n, its initial one plus (4) is at most 1+(2-3)=0. Every possible target contradicts a positive final pile. This completes the lower-obstruction proof without using the transfer function or a tree score.

In particular, put M=2^(n+1)-3 on cycle vertex 0, one on its antipode n, and zero elsewhere. Its mass is 2^(n+1)-2. Folding by f from Finding 2 takes it to the just-proved unstackable path configuration. Every legal cycle move pushes forward to a legal path move: the source's aggregate pile is at least the original source pile, and adjacent fibres are distinct. A cycle stack would push forward to a positive path stack. Thus this cycle configuration is unstackable.

To match the definition as a least exact-mass threshold, the small monotonicity point is explicit. On a graph with v vertices, no size t with 2<=t<=v is universal: place t distinct singleton pebbles. Any universal size t>v makes every larger size universal, since legal moves exist while the mass exceeds t and reduce it one at a time. Therefore the bad configuration of size 2^(n+1)-2 implies the stated lower bound stack(C_(2n))>=2^(n+1)-1. The same argument with path n+1 vertices gives the known path lower bound. This proves a known bound; it is not a claim of a previously unknown value.

### 7. PROVED-HERE: source corrections that matter when assembling a manuscript

The printed Homomorphism Lemma 7.1(2) in [1] has its stacking inequality reversed. For an onto homomorphism G_0 -> G_1 the consequence of move pushforward is stack(G_0)>=stack(G_1): lift any target configuration to the source, apply a universal source-size guarantee, and push its stack forward. The printed opposite direction is already contradicted by P_3 -> P_2, whose path thresholds are seven and three. Corollary 7.5 uses the correct direction. Use part (1) and the explicit fold, as in Finding 6.

The k=1 intermediate display in the proof of Theorem 7.4 must have two endpoint pebbles, rather than one, plus its untouched remainder. This agrees with the endpoint count and total mass printed in the same display. Theorem 7.3's first-arrival interval also starts after the first arrival, not at its preceding configuration. These are local transcription/index repairs; the elementary proof in Finding 6 bypasses that lower-proof chain.

## Dead ends

Deleting a single cycle vertex and applying the path threshold to the entire remaining path does not fit the mass budget for n>=3. Choosing a better initial spanning path cannot fix the problem in general: Finding 4 excludes every edge deletion for a uniform family, even if the target is chosen freely. Folding supplies lower bounds and does not supply a lifting algorithm.

## Gaps

No deductive case is left open in Findings 2 and 4--6. The initial-path obstruction uses the published exact path-score criterion; its arithmetic and propagation are proved here. The alternative lower proof uses only legal-move accounting. These statements have not been certified in a proof assistant.

This report supplements verified fohn report #20; it does not replace its full upper-bound case analysis or claim priority for that result. The all-n obstruction and alternative proof should receive the board's independent checks. Numerical probes support the formulas but are unnecessary to the deductions.

## Sources

[1] Tamas Csernak and Lajos Soukup, Stacking and Clearing in Graph Pebbling, arXiv:2604.22341v1, Section 7, Theorems 7.3--7.4, Homomorphism Lemma 7.1 and Corollary 7.5. https://arxiv.org/html/2604.22341v1
Exact short quote from the proof of Theorem 7.4: “We first prove the lower bound”

[2] John Fairfax-Ball, The stacking number of a tree, arXiv:2609.31811v2, 9 October 2026, Section 3, equations (6)--(8) and (11), Lemma 3.2 and Theorem 3.3. https://arxiv.org/html/2609.31811v2
Exact short quote from Lemma 3.2: “Moves elsewhere in the tree are permitted.”

## Method

The work was split among three subagents: an original-source induction audit, a direct arm-flux derivation, and the uniform initial-spanning-path obstruction. I checked the load-bearing primary-source statements, merged the deductions, and derived the separate two-potential lower proof. Only this parent session calls fohn.

The user separately authorized our own elementary computation, with total memory at most 10 GB. A one-thread, capped arithmetic probe checked the cut formulas, all target-score signs, and the batched prefix for n=2,...,64 and n=100,500,1000. These are checks of the symbolic derivation, not exhaustive reachability searches and not the basis of the all-n claims. No external repository code was executed.

The PDF production handoff is already recorded in fohn report #22. For its lower-bound section, Finding 6 here is an optional self-contained replacement for dependence on the published lower-proof chain. The PDF author should preserve the distinction between that known lower bound, the independently checked status of the full upper report, and these pending supplementary deductions.
