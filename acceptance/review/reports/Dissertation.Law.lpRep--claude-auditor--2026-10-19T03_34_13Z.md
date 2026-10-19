### A:abstract, A:conclusion, A:cor:robust, A:rem:generalrank, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.Law.lpRep
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 4d8f19766d30be6bf897d6959240d0e7 (pl-fp-v1:c0f6b23921a70e52a3a0cab714a261ce14c4b293456499779210f83ed4cfb0e7)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:14Z):
Reading of def Law.lpRep (used across the paper's main claims; the paper's notion is the
identification of a square-integrable random tuple with its L^2 class, through which laws are
taken: "the law map Theta |-> Law(Theta) is 1-Lipschitz from L^2(Omega;H) into (P_2(H),W_2)"
(App. A Step 2), and the L^2(nu)-valued integrands "read through such a representative" (2.3)).

Paper notion (best reading without the Lean): passing between a function and its L^p equivalence
class (or back to a representative). Laws depend only on the a.e.-class: Law(Theta) =
Law(Theta') when Theta = Theta' a.s. Pointwise formulas u(e) for u in L^2(nu) are meaningful only
when they descend to classes.
A faithful Lean definition must: (a) if it maps a function f to its class in L^p: for f with
Memℒp f p (AE-strongly measurable and finite p-norm) give exactly the class of f; for other f a
junk value (e.g. 0) - and every use must be guarded by membership or be insensitive to the junk;
(b) if it maps an L^p element to a function: give an a.e.-representative (measurable), and all
statements built on it must be invariant under the choice (a.e. equal). In either case the
law of lpRep-related objects must equal the paper's law of the tuple (pushforward of P), and
the norm must be the paper's (L^2 with Hilbert norm |x|^2+|y|^2+|z|_F^2+||u||^2 on H).
Comparison (verdict recorded 2026-10-19T03:32:34Z):
Comparison, Law.lpRep (Law/LpRepresentative.lean:129-135).

lpRep nu V : L^2(nu;V) x E -> V is Classical.choose of Lp.exists_stronglyMeasurable_rep: a strongly
measurable (for Borel(L^2) x mE) map Phi with Phi(u, .) = u nu-a.e. for every u and Phi(0, .) = 0,
under the hypothesis that L^2(nu;V) is separable (true for the paper's countably generated E and
sigma-finite nu, sec. 2 first paragraph). This is case (b) of my reading: a representative of each
L^2 class, here chosen jointly measurably in the class, as the paper's "read through a P (x) E
representative" ((2.3), (2.5)) needs. Any statement depending on it is invariant up to null sets
(two such representatives agree nu-a.e. for each u, hence a.e. on products by Fubini); the
normalisation Phi(0,.) = 0 is a harmless choice. Not a junk-valued map (defined everywhere with the
right a.e. class).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: the representative is selected non-canonically (Classical.choose) and
jointly measurably in (u, e) - a measurable selection of representatives, slightly more than the
paper's pointwise "a representative", which it implies; it is normalised by Phi(0, .) = 0; it needs
L^2(nu;V) separable, which holds in the paper's setting (countably generated E, sigma-finite nu).
Every use reads h through it only up to null sets, which is the paper's reading (2.3).
Disagreements with the author's review (shown 2026-10-19T03:32:45Z): none
