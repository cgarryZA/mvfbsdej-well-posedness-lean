### A:lem:lawflow: Dissertation.Law.P2.toP2WH
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash d1c4f8da3396bc50d397270158b14316 (pl-fp-v1:1e16e82ece402cd0d9820096df152afbba5279bdb5e1c766e03577de6e2e84e3)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:01:48Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.Law.P2.toP2WH (locked before seeing Lean).

Inverse direction of P2WH.toP2: the conversion from P2 over one carrier of H (by name, the
"Law" module's P2 on a plain product type or another model) to P2 over the Hilbert carrier WH
(WithLp-2 product with norm |x|^2+|y|^2+|z|_F^2+||u||^2) on which the coefficients take their
measure argument and on which W2 is the paper's W2. Faithful: pushforward along the canonical
measurable equivalence between the carriers (no alteration of the measure), preserving finite
second moments (norm equivalence), and inverse to toP2. Context Lemma A.1 (law flow): the law
of the tuple computed on the product carrier is converted to the coefficient carrier; a
faithful conversion makes mu_t the law of Theta_t on H.
Comparison (verdict recorded 2026-10-17T15:56:20Z):
Comparison for def:Dissertation.Law.P2.toP2WH.

Lean (System/HilbertW2Space.lean): P2.toP2WH mu := mu : P2WH HX HY HZY HUY, where P2WH is the type synonym of
P2 (Tuple HX HY HZY HUY) carrying the Hilbert-norm W2 pseudometric (dist = w2H, via toL2 into the
WithLp-2 carrier) and its Borel sigma-algebra.

Against my reading: the conversion is the identity on the underlying law (no alteration, no junk),
inverse to P2WH.toP2 (rfl lemmas both ways); second moments unchanged; on the target, distances are
the paper's Hilbert-norm W2 (P2WH.dist_toP2WH). The canonical identification of the max-norm product
with the Hilbert carrier is toL2 inside w2H, as my reading required. Used e.g. in JointBorel to give
P2(H) the Borel structure of the paper's W2 (measurable_toP2WH relates it to the evaluation
sigma-algebra).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:44Z): none
