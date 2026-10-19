### A:abstract, A:ass:lip, A:conclusion, A:cor:robust, A:eq:coeffint, A:eq:coefmeas, A:eq:hborel, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:expfunc, A:ex:fulllaw, A:intro:limin-comparison, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:prop:strict, A:rem:beta1-dich, A:rem:cwp-class, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:regimes, A:rem:uniq-no-integ, A:rem:wasserstein-bounds, A:sec2:hborel-derivation, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.TupleL2
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 5c620c846d4820ad66b1a5b8e7220ca2 (pl-fp-v1:443385cf9a5c4a4ade7a4d3fcf242bf6e0c57bf8cbb8409a7a0c639579454d3c)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:23Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:11Z):
Reading for def:Dissertation.WellPosedness.System.TupleL2 (locked before any Lean is shown).

Paper notion (Def 2.1 diag): L^2(Omega, F_t; H), the space of square-integrable F_t-measurable
H-valued tuples on the standing basis (Omega,F,(F_t),P): (classes of) strongly measurable
Theta: Omega -> H, F_t-measurable, with E|Theta|_H^2 < infinity, |.|_H the Hilbert norm of H.
(Also L^2(Omega;H) without the sub-sigma-field appears in Lemma A.1.)

A faithful Lean definition must be:
- the L^2 (Bochner) space of H-valued functions w.r.t. P restricted to F_t (e.g.
  Lp TupleH 2 (P.trim (F_t <= F)) or the subspace of Lp TupleH 2 P of F_t-measurable classes),
  or L^2(Omega;H) with F_t-measurability carried separately where it is used;
- equivalence classes P-a.e. (harmless: laws only depend on the class);
- the H-norm must be the paper's (Hilbert) norm.
If the t-dependence (F_t) is missing in this definition, the F_t-measurability must appear in
diagonalInputs, else the diagonal is larger than the paper's D_t (broader hypotheses become
stronger assumptions: Lipschitz/monotone along a larger set - a narrower theorem).
Comparison (verdict recorded 2026-10-19T03:25:27Z):
Comparison for def:Dissertation.WellPosedness.System.TupleL2.

Lean: TupleL2 HX HY HZY HUY := WithLp 2 (HX x WithLp 2 (HY x WithLp 2 (HZY x HUY))), docstring "the
tuple space with the Hilbert norm (|x|^2+|y|^2+|z|^2+|u|^2)^{1/2}". My reading guessed
L^2(Omega,F_t;H) (square-integrable random tuples); the Lean unit is instead the paper's H with
its Hilbert norm (the target of toL2), and I judge it against that notion (H with |.|_H), which my
reading did require ("the H-norm must be the paper's (Hilbert) norm").
- iterated WithLp 2 products: ||w||^2 = |x|^2 + ||(y,(z,u))||^2 = |x|^2+|y|^2+|z|^2+|u|^2
  (norm_toL2_sq proves |toL2 theta|^2 = channelSq theta). Exactly the paper's |theta|_H. Since the
  channels are inner product spaces, WithLp 2 of a product is an inner product space with the sum
  of the inner products - the paper's Hilbert structure. Complete when the channels are.
- measurable structure: Mathlib's instance on WithLp (product sigma-algebra transported), Borel
  when the channels are second countable Borel spaces (true at the paper's instance).
No junk. Verdict: faithful with representation choices (iterated binary WithLp products for the
four-fold Hilbert sum).
Witness: —
Verdict: faithful with representation choices — Representation choice, harmless: the four-fold Hilbert sum H = R^n (+) R^m (+) R^{m x d} (+)
L^2(nu;R^m) is built as iterated binary l^2 products WithLp 2 (HX x WithLp 2 (HY x WithLp 2
(HZY x HUY))). Its squared norm is the sum of the four squared channel norms (norm_toL2_sq) and
its inner product the sum of the channel inner products, which are the paper's |.|_H and Hilbert
structure. (The unit is the space H with the Hilbert norm, not the L^2 space of random tuples.)
Disagreements with the author's review (shown 2026-10-19T03:25:39Z): No substantive disagreement. The review shown records "faithful". I recorded "faithful with
representation choices" because of the encoding steps I listed, which the review also describes
as harmless. The difference is only in the label.
