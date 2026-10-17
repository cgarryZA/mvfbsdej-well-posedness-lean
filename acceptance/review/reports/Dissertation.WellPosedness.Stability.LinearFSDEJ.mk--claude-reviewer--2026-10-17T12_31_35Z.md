### A:sec4:horizon-not-contractive: Dissertation.WellPosedness.Stability.LinearFSDEJ.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 302302b2a85c5d690000000000000000 (pl-fp-v1:ef266bd0afea39aa14085ba657e01d37c5d25a84a702f754bb8e542946db7fea)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:31:35Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:31:21Z):
Reading: LinearFSDEJ.mk is the constructor of the predicate "X solves the linear forward
equation with frozen integrands" (the paper's (4.5)/(4.12) in one coordinate). Its meaning is
fixed by the structure: it must take exactly the conditions of the notion (measurability /
progressivity / square integrability of the integrands, initial value, adapted right-continuous
X, the identity a.s. at every t in [0,T]) and nothing more, and produce the predicate. Faithful
iff the structure is, and the constructor adds no field beyond the structure's.
Comparison (verdict recorded 2026-10-17T12:31:30Z):
LinearFSDEJ.mk takes exactly the 18 fields of the structure LinearFSDEJ (sigma_meas/prog/vanish/sq,
gamma_meas/prog/vanish/sq, b_meas/prog/vanish/sq, xi0_sq, X_adapted, X_rightCont, eqn) and no
other hypothesis, and returns LinearFSDEJ D F hW hN T xi0 b X sigma gamma. It is the
auto-generated constructor; its meaning is the structure's, reviewed as faithful with
representation choices (scalar coordinate form; integrands extended by 0 off [0,T]; gamma marked
progressive instead of predictable; X right-continuous everywhere without a left-limit field;
identity a.s. at each t; xi0 in L^2).
Witness: —
Verdict: faithful with representation choices — (1) Scalar coordinate form (one coordinate of X, a row sigma in R^d, a scalar jump integrand):
the paper's vector equation is the conjunction over coordinates. (2) Integrands extended by 0
off [0,T] (fields *_vanish): only [0,T] enters. (3) gamma marked progressively measurable rather
than predictable: the L^2 compensated integral does not distinguish integrands equal
dP x dt x nu-a.e. (4) X right-continuous on every path at every real time and adapted at every
real time, with no left-limit field: left limits follow a.s. from the identity, and any paper
solution on [0,T] extends (0 before time 0, X_T after T). (5) identity a.s. at each t in [0,T],
the paper's "a.s. for every t". (6) xi0 in L^2, as in Assumption 2.2 and Lemma 4.3.
Disagreements with the author's review (shown 2026-10-17T12:31:30Z): none (the author review shows only a marker, definitions.md:300; nothing to disagree with).
