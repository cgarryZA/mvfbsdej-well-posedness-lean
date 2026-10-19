### A:lem:lawflow: Dissertation.Law.P2.toP2WH
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash d1c4f8da3396bc50d397270158b14316 (pl-fp-v1:1e16e82ece402cd0d9820096df152afbba5279bdb5e1c766e03577de6e2e84e3)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:36:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:43Z):
# Reading: def Law.P2.toP2WH

Paper notion: P2(H), the probability measures on the Hilbert space
H = R^n x R^m x R^{m x d} x L^2(nu;R^m) with finite second moment, with the norm
|theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||^2 and the W2 distance built from |.|_H; laws of
tuples are elements of P2(H).
The name suggests a coercion from P2 on the plain product type (whose Lean norm is the sup norm) to
P2 on the WithLp 2 (Hilbert, "WH") version of the same product. A faithful definition must:
* send mu to the pushforward of mu under the canonical identification of the plain product with
  its WithLp 2 copy (identity on points; a continuous linear equivalence, hence a Borel
  isomorphism);
* produce an element of P2 on the Hilbert-normed space: the image is a probability measure and its
  second moment for the Hilbert norm is finite (equivalent norms), so membership is preserved;
* not alter the measure in any other way (no junk value: the map is total and exact).
So for a tuple Theta, toP2WH (Law Theta) must be the law of Theta seen as an H-valued variable with
the Hilbert norm, and W2 computed after the coercion is the paper's W2 on P2(H).
Comparison (verdict recorded 2026-10-19T03:25:08Z):
# Comparison: def Law.P2.toP2WH

Lean: P2.toP2WH (mu : P2 (Tuple HX HY HZY HUY)) : P2WH HX HY HZY HUY := mu — the identity into
the type synonym P2WH := P2 (Tuple ...). P2WH carries the pseudometric induced by
mu |-> (toL2 # mu) in the 2-Wasserstein space of TupleL2 = WithLp 2 (HX x WithLp 2 (HY x WithLp 2
(HZY x HUY))) (the iterated L^2 product, norm (|x|^2+|y|^2+|z|^2+|u|^2)^{1/2}, the paper's |.|_H),
so dist mu.toP2WH mu'.toP2WH = w2H mu mu' = W2 of the images under toL2; and the Borel
sigma-algebra of that topology.

Against my reading: I expected a pushforward along the canonical identification to the WithLp 2
copy. The Lean keeps the same measure on the max-norm product (same points, same Borel sets, same
finite-second-moment class, since the two norms are within a factor 2) and instead puts on the
target type the W2 of the Hilbert norm, computed after pushing forward along toL2. The two
encodings are isometric: mu.toP2WH in P2WH corresponds to toL2 # mu in P2W(TupleL2), and the
correspondence is exactly the pseudometric's definition. So for a tuple Theta,
(Law Theta).toP2WH is the law of Theta in P2(H) with the paper's W2 topology; the map is total and
exact, no junk value.
Representation choice: a type synonym carrying the Hilbert-norm W2 (and its Borel sets) instead
of a pushforward to the WithLp copy; harmless since the metric is defined as the W2 of the
pushforward.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choice: toP2WH is the identity into the type synonym P2WH, which carries the
2-Wasserstein pseudometric of the Hilbert norm of H (defined as W2 of the images under the
canonical map toL2 into the iterated WithLp 2 product) and its Borel sigma-algebra, instead of a
pushforward of the measure to the WithLp copy. The measure, its Borel sets and its finite second
moment are the same under both norms (equivalent within a factor 2), and the distance is by
definition the paper's W2 on P2(H), so the encoding is isometric to the pushforward one.
Disagreements with the author's review (shown 2026-10-19T03:36:15Z): Classification only. The reviewer records "faithful"; I record "faithful with representation
choices", because toP2WH is the identity into a type synonym whose metric is defined as the W2 of
the pushforward along toL2 (the Hilbert-norm copy of H), rather than a pushforward of the measure
itself; the encoding is isometric to the paper's P2(H), so there is no disagreement about meaning.
