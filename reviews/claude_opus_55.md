# Independent review: stack(C_2n) = 2^(n+1) − 1 (fohn report #20, task #2)

Reviewer: Claude Opus 5.5 (claude-opus-5-5), local independent review. This is not a fohn board check.
Reviewed text: `fohn_general_proof_report.md`. Line numbers below refer to this file. `cycle_stacking_proof.md` has the same body plus a 4-line header; I confirmed this with `diff`.

## Verdict: **SUPPORTED**

I re-derived every load-bearing inequality, move sequence, funding check and budget by hand. None of them fails. I found no counterexample and no unjustified implication that matters to the theorem. The issues I list below are presentational: things left implicit or ambiguous wording. Each one can be fixed in a line, and none of them changes the argument.

---

## 1. Self-contained path ingredients (appendix, L203–260): verified, not circular

**U, N and P (L207–246).** I re-did the induction with k = 2^(L−1) ≥ 2.
- **Base case L=1:** m = F(c) ≥ −1 = 3−4. The only negative case is c=1, which gives M−m = 2. A nonnegative message gives c ≤ 2m+3.
- **Empty tail:** the length-1 bounds are stronger than the length-L bounds.
- **U:** x ≥ 3−2k gives 2x−3 ≥ 3−4k.
- **N:** M−m = T−c−2t+3.
  - For t<0: (T−t) + (−t) − c + 3 ≤ (2k−2) + (2k−3) + 3 = 4k−2.
  - For t=0 (an occupied zero message): child P gives T ≤ 3k−3, and 3k ≤ 4k−2 because k ≥ 2.
  - For t=1, x ≤ 1 forces c=0, so T+1 ≤ 4k−2.
- **P:**
  - For t ≥ 0: M ≤ x + (k−1)t + 3k−3 ≤ kx + 3k−3 ≤ 2k(m+3) − 3, using x ≤ 2m+3.
  - For t<0: M ≤ 2m+2k+1 ≤ 2k(m+3)−3, because (2k−2)m + 4k−4 ≥ 0.

None of these steps uses a path threshold or the necessity direction of a tree criterion. The induction is genuinely simultaneous and well-founded.

**Constructive boundary lemma (L248–252).** I checked every branch for legality.
- **x even ≥ 2:** the child clears into v1 by induction, because c+t = x > 0. Then h moves outward.
- **x odd ≥ 3:** after h outward moves the boundary holds q+h, and q+h−1 > 0 gives q+h ≥ 2 for the borrowed move.
- **x ≤ 1:** q − 2j + 1 > 0 gives q ≥ 2j for the j borrows. The child then sees input exactly 2 (it may be empty only when c=1, j=1). One pebble returns, so the final pile is q+F(x).

**EMPTY vs. occupied zero.** An occupied child with message 0 is handled correctly: c=0 lands in the x ≤ 1 branch, and c ≥ 1 in the clear-then-send branch. An EMPTY child contributes nothing and needs no clearing. EMPTY and an all-zero occupied chain agree modulo 3, because F(0) = −3 ≡ 0. This fact is what makes the residue selection below valid.

**Path threshold (L254–258).** If a+m ≤ 0, then a+M ≤ M−m ≤ 2^(L+1) − 2 ≤ 2^N − 2. This gives stack(P_N) ≤ 2^N − 1 from scratch. Equation (2) in the main text is exactly N, so the main text's use of [1] and [2] (L56–58) can be replaced entirely by the appendix.

## 2. Exact-unit pull and unit push (L60–86): verified

- **Pull with m<0:** p = 1−m and p+M = M−m+1 ≤ 2^(L+1) − 1.
- **Pull with m ≥ 0:** p ∈ {0,1,2} reaches residue 1 with p+m ≥ 1.
- **Triple burn:** root→nb, root→nb, nb→root. It needs an active pile ≥ 4 and an empty neighbour; both hold after clearing. The move count is p+M−1, because every move loses exactly one pebble.
- **Unit-push lemma (L66–74).** m ≤ 0 and m ≡ 1 (mod 3), together with the fact that negative F-outputs are odd, force m ≤ −5. Then X = (m+3)/2 ≤ −1, so the adjacent child is occupied with u<0. N on the length-(L−1) child gives C − u ≤ 2^L − 2, so the mass is at most 2^L − 3. That contradicts the assumed mass ≥ 2^L − 2. The lemma needs L ≥ 2, and the report states this.
- **L=1:** a reserve of 2 gives F(2) = 1.
- **(3)/(4):** the score modulo 3 is affine in s with a unit coefficient (see the EMPTY remark above), so three consecutive values of s cover every residue. In the M ≤ T−2 regime this gives T−2 ≤ s+M ≤ T.
- **Fuel 0 and inactive pebbles:**
  - s=0 or p=0 is allowed and handled.
  - Inactive pebbles at the target or source only make moves easier: legality on the active configuration implies legality on the real one.
  - Unused source pebbles stay in place. Inactive target pebbles stay and receive exactly +1.

## 3. Balanced root (L88–107): verified

H_i + H_(i+n) = 2A−1, so exactly one of the two is ≥ A, and a high-to-low transition exists. From H_i − H_(i+1) = c(i) − c(i+n) ≥ 1 we get a > b. The four window inequalities give all of (5): a+q ≥ A, q+b ≤ A−1, b+r = S−H_i ≤ A−1, and a+r = S−H_(i+1) ≥ A.

I also checked a fact the pivot relies on. A vertex is a balanced root **iff** both n-windows that contain its antipode but not the vertex itself have mass ≤ A−1. The complementary windows are then ≥ A, and a' > b' follows from a'+q' ≥ A > q'+b'.

η(h) (L105–107): even h takes h/2 moves. Odd h ≥ 5, or h=3 with a positive retained neighbour, takes (h−1)/2 outward moves, then one in and one out.

Budget: at most A moves leaves at least A−1 = 2^n − 1 pebbles on the retained P_n, which then stacks by the appendix.

## 4. Case-by-case audit (L110–196)

| Case | Moves / funding checked | Bound |
|---|---|---|
| b=0, a≥2 (L112) | m<0: p ≤ A−1−q < a. m≥0: p ≤ 2 ≤ a. | ≤ A−2, or ≤ q+1 ≤ A |
| b=0, a=1 (L114) | q=r=A−1 is forced. m<0 would give M−m ≥ A > 2^n − 2, contradicting N. Root score 1+m1+m2 ≥ 1, so stacking is direct, using constructive sufficiency twice. | direct |
| b=1 (L116) | L=n ≥ 2, q ≤ A−2 = T−2, s ≤ A−q ≤ a. b=1 is inactive at the target. | s+q ≤ A |
| b=2 (L118) | One move from the antipode, then a pull with q ≤ A−3. a ≥ 3 funds p ≤ 2. | ≤ A−1 |
| b≥3, even ending 2k (L122–138) | k ≥ 0, with ending 0 allowed. The shortened arm has L=n−2 ≥ 1. 2k ≤ q ≤ A−1−b gives k ≤ B−2, so p ≤ B−1−q+k ≤ A−q ≤ a. | 2·loss ≤ 2A−2 or ≤ 2A−b+3o ≤ 2A |
| b=3 choice rule (L122) | The rule picks a different arm only when both endings are 0. Checked all parity/zero combinations. | — |
| b=3, both neighbours 0 (L142–146) | Moves: donate, push (L=n−1), pair back, pair out. Loss s+q+2. q ≥ B−2 gives s ≤ 2 and loss ≤ q+4 ≤ A. q < B−2 gives s+q ≤ B ≤ A−q ≤ a and loss ≤ B+2 ≤ A. For n=2 (L=1, q=0): s=2, loss 4 = A. | ≤ A |
| n=2, b≥3 (L140) | Mass 7 and (5) force b=3, q=r=0, a=4. | handled above |
| Odd endings, large prefix (L161–166) | L=n−1 ≥ 2. a ≥ 4 funds s ≤ 2. 2·loss ≤ 2A+2−(b+t)+3o. b+t ≥ 4, and b+t ≥ 5 when it is odd. | ≤ A |
| Small triple K ≤ A−1 (L170–178) | t=min gives b+4t ≤ A+1 and x ≤ B−2. a ≥ A−M−x ≥ B+2−M ≥ s+2. Loss ≤ B+t−1+η(b+t). (8) checked for t ≥ 2, and for t=1 with b odd and b even (b ≤ A−4 because A is even). | ≤ A |
| Large triple: pivot (L180–196) | (9): a+P+R = S−K ≤ A−1. The new root n−1 has antipode 2n−1, with windows b+r ≤ A−1 and p+a+P ≤ a+P+R ≤ A−1, so it is balanced. **n ≥ 4:** 2n−1 and 2n−2 are distinct vertices of the old R-prefix {n+2,…,2n−1}, so K' ≤ a+R ≤ A−1 and the pivot never returns to the large-triple case. **n=3:** the large-prefix exclusion gives P, R ≤ 1, so b' = c(5) ≤ 1 and §3 applies (including b'=0, a'=x=1, which is the general b=0, a=1 argument). **n=2:** impossible, since mass ≥ 4+3+1+1 = 9 > 7. | at most 1 pivot |

**Exhaustiveness.** b ∈ {0,1,2} is covered with every a. For b ≥ 3, the cases are: at least one even ending (with or without the b=3/both-zero special case), or both endings odd, which splits into large prefix, small triple, or large triple. a ≥ 1 always holds because a > b. Every procedure leaves the cleared arm and the antipode at 0 and all other pebbles on the retained P_n. The second application after the pivot uses only (5), which the new root satisfies.

**Theorem statement.** [1] defines stack(G) as the least t ≥ 2 such that every configuration *with exactly t* pebbles is stackable. I fetched the source page and confirmed this definition, Theorem 7.4, and Corollary 7.5 (lower bound via the homomorphism C_2n → P_(n+1) and Lemma 7.1). So "every configuration of size S stacks" together with Cor 7.5 gives the equality. Larger sizes also stack by the trivial move-down argument, since mass > 2n forces a pile ≥ 2. In any case the definition does not need them.

## 5. Presentational issues (none substantive)

1. **L36:** the "iff"/maximum claim of the boundary lemma is proved in the appendix only in the sufficiency direction. The cycle argument needs only sufficiency, plus N. Recommend saying so in that line.
2. **L66–70, L124:** the length conventions are ambiguous. "Length-L path" means L edges from source to target (an arm of L vertices from the target). "Path with L vertices" in L69 refers to the child arm plus its boundary. "n−2 edges" in L124 means an arm of n−2 vertices. The arithmetic is consistent with these readings.
3. **L80:** "three consecutive available residues" silently needs the score mod 3 to be affine in s across the EMPTY→occupied switch at s=0. This is true because F(0) = −3 ≡ 0, but it should be stated.
4. **L122:** "even pile 2k" must include 2k=0 for exhaustiveness, and the text uses it that way.
5. **L126:** the step B−1−q+k ≤ A−q uses k ≤ B−2 (from 2k ≤ q ≤ A−1−b). This is unstated.
6. **L183:** "Both ending vertices are balanced roots" uses the window characterisation of (5), including the derived inequality a' > b'. This is implicit.
7. **L48–52 (zero-score observation):** the propagation sketch is terse and depends on [2]'s necessity direction. It is not load-bearing once the appendix is used, so I did not audit it to full rigour. I did check identity (1) and the claim F(z−3k) ≤ F(z), and both are correct. Note that F itself is not monotone (F(2)=1 > F(3)=0); the stated inequality is still true.
8. **L114:** "positive root score … so it stacks directly" uses the tree criterion. The appendix lemma, applied to each arm in turn, gives this constructively.

## 6. Independent computation (supplementary)

I wrote my own stdlib Python probe from my reading of the text, not from the authors' code. It is at `probe.py` and `targeted.py`. Limits: RLIMIT_AS 1 GiB, single thread. Every move is asserted legal on the **active** configuration alone. Each operation's move count is asserted equal to its stated formula. Total loss ≤ A, emptiness of the cleared region, at most one pivot, and final stacking are all asserted.

- **U/N/P:** checked on all arms with L ≤ 6 and piles ≤ 7. 0 failures.
- **Constructive lemma:** 209,857 (arm, q) instances. All produce exactly q+m.
- **Lower bound by BFS:** C4 and C6 each have unstackable configurations of size S−1, for example (0,1,0,5) and (0,0,1,0,0,13).
- **Exhaustive C4 and C6:** all configurations (120 and 15,504) pass. Every case was hit, including the n=2 b=3 zero case and 20 n=3 pivots.
- **Random C8–C24:** about 20,000 configurations; all pass.
- **Targeted large-triple configurations for n=4..10:** 3,000 per n, with b ≥ 3, odd endings, K ≥ A and small prefixes. Each was solved both from the forced original root and from the automatic root. 42,000 runs, all pass, and the post-pivot root never needed a second pivot.

I did not re-run the authors' C8 enumeration and did not inspect their implementations. This computation is evidence only; the infinite statement rests on §§1–4 above.

## 7. Limits of this review

This is a careful human-style mathematical audit, not a proof-assistant certificate. I relied on [1] only for the lower bound (Cor 7.5) and the definition of stack. I read those statement texts in the source but did not re-audit the proofs of Lemma 7.1 or Theorem 7.3 for general n; I confirmed them by brute force for n=2,3 only. I did not audit [2], because the appendix makes it unnecessary for the upper bound.
