# Constructive corollary: compact certificates

The candidate proof in fohn report #20 yields more than existence of a stacking sequence.

For an input configuration on C_(2n), with each count written in binary, a stacking certificate can be written with O(n) transfer/triple-burn batches and O(n^2) bits. It can be constructed and replayed using O(n) arithmetic operations on O(n)-bit integers, apart from ordinary input/output handling.

A transfer batch records k consecutive moves u->v, and is legal whenever u,v are adjacent and c(u)>=2k. Its net change is -2k at u and +k at v.

A triple-burn batch records k repetitions of u->v, u->v, v->u. It is legal whenever c(u)>=3k+1: before the last repetition the source still has at least four pebbles. Its net change is -3k at u, with v unchanged. Neither batch needs a loop over k.

To see the certificate bound, compute a balanced root by one rolling-half-window scan, and pivot at most once. Every arm-clearing recursion processes each arm vertex once, emitting at most a constant number of transfer batches per vertex. Exact-unit normalization emits one triple-burn batch. The opposite-pile clear uses a constant number of batches. The remaining path is cleared with the same recursion. A direct initial-tree case processes its two disjoint arms once each. Thus the total batch count is O(n).

Fuel selection needs no search: F multiplies residues by two modulo three. Compute the required source residue r in {0,1,2}. If internal mass M<=T-2, choose the largest s<=T-M with s congruent to r; otherwise choose s=r. The proved mass/residue lemma supplies positivity in either case. All balance and message scans use O(n) integer operations.

Initial counts are at most 2^(n+1)-1. Intermediate physical counts are no larger. Formal signed messages on paths of O(n) vertices have O(n) bits, directly from the transfer recurrence and its uniform negative bound. Batch repetition counts are bounded by the expanded move count, at most the initial mass minus one, hence also have O(n) bits. O(n) batches therefore require O(n^2) bits.

This statement concerns a compact exact certificate. It does not identify the shortest stacking sequence.

Implementation: compressed/construct.py and compressed/replay.py in cycle_stacking_proof_bundle.zip. The independent replayer uses only the two batch guards, cyclic adjacency, exact integer arithmetic, and final mass/support checks; it does not use the mathematical message criterion.

A checked C2000 example has 2,998 batches representing 2^1001-3 individual moves and ends with a pile of two. This is a particular certificate, not an extrapolation used to prove the universal corollary.
