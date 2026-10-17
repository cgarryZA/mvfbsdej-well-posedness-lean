### A:cor:robust, A:eq:coefmeas, A:eq:hborel, A:ex:brownian, A:ex:concrete, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:sec2:coefmeas, A:sec2:hborel-derivation, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.lawToL2
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 4034513072b6f988f8b3198000db33c5 (pl-fp-v1:a5951a2506aeacc26e979ee8767ca777ef37c5478d79166838fd34440f63eadb)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:18Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:35Z):
Reading for lawToL2 (used by Cor 3.6 and other claims; no notion named so in the paper).
The paper's laws live on P_2(H) (H = R^n x R^m x R^{m x d} x L^2(nu;R^m)) and P_2(R^n) (terminal),
and P_2(L^2(nu)) for the U-marginal mu^U (eq. (2.12)). A Lean map "lawToL2" most plausibly converts a
law to a law on an L^2-type space: e.g. (a) the pushforward of a law on H to the corresponding law on
an isometric L^2 model of H, or (b) the U-marginal projection mu |-> mu^U in P_2(L^2(nu)), or (c) the law
of a random tuple as an element of P_2. A faithful definition must be a pushforward by a (Borel)
isometry/projection that preserves probability and finite second moment, so that W_2 distances are
preserved (isometry) or not increased (1-Lipschitz projection, (2.12)); for marginal projection it
must be the pushforward under theta |-> u. Any junk value (e.g. when the source measure is not in
P_2) must arise only off P_2.
Comparison (verdict recorded 2026-10-17T15:04:36Z):
Comparison for lawToL2 (System/HilbertW2Space.lean:74): lawToL2 mu := mu.mapOfLe measurable_toL2
norm_toL2_le, i.e. the P2 law with underlying measure mu.law.map toL2 on TupleL2 (finite second moment
from |toL2 theta| <= 2 ||theta||_max). toL2 : Tuple -> TupleL2 is the identity of the underlying set
(toLp of the nested pairs; ofL2 is its two-sided inverse by rfl), measurable both ways, from the
max-normed carrier to the Hilbert-normed one.
Against my reading (a pushforward by a Borel isometry/projection preserving probability and finite
second moment; option (a): the law on the carrier re-read as a law on an isometric L^2 model of H):
it is option (a). Since the paper's H carries the Hilbert norm, TupleL2 with the paper's channels is
the paper's H and toL2 is the identity of H re-normed; so lawToL2 sends a law on the carrier to the
same law viewed on the paper's H. W_2 computed after lawToL2 is the paper's W_2 (w2H; used via
P2WH's pseudometric). Probability and finite second moment are preserved; no junk value arises (the
map is total and P2 -> P2). It is not a W_2-isometry between the max-norm and Hilbert-norm W_2 (those
differ by up to 2), but it is exactly the identification that makes the Hilbert-norm W_2 the paper's.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:05:48Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
