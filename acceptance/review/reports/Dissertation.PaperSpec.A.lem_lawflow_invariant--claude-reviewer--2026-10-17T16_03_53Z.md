### A:lem:lawflow: Dissertation.PaperSpec.A.lem_lawflow_invariant
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba184c9d1f8d6f2b814 (pl-fp-v1:5b592b7821c070fecd50bbe1798b7b7ff34350b9115d2311b8dc73c336b059ac)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:53Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:47Z):
Reading of spec lem_lawflow_invariant (Lemma A.1: "...admit Borel representatives, unique up to
Lebesgue-null sets of times ... Coefficient evaluations along these representatives are
invariant, up to dt (x) dP-null sets, under the choice of predictable representatives of (Z,U)
and of the Borel representatives").

Setting: standing basis, T > 0, H = R^n x R^m x R^{m x d} x L^2(nu;R^m), sigma-finite nu on a
countably generated E; X, Y cadlag adapted; Z, U predictable versions with
E int_0^T (|X|^2 + |Y|^2 + |Z|_F^2 + int_E |U(e)|^2 nu(de)) dt < infinity.
Conclusions:
 1. uniqueness of the flows: any two Borel maps mu^1, mu^2 : [0,T] -> (P_2(H), W_2) that agree
    with t |-> Law(Theta_t) for a.e. t agree with each other for a.e. t; likewise for
    t |-> Law(Theta^-_t);
 2. invariance under the representatives: if (Z', U') is another predictable version
    (Z = Z' dt (x) dP-a.e., U = U' dt (x) dP (x) nu-a.e.), Theta' the corresponding tuple, and
    mu', mu'^- any Borel representatives of the flows of Theta', then for every coefficient
    psi in {b, sigma, f} (functions [0,T] x H x P_2(H) -> R^.), psi(t, Theta_t, mu_t) =
    psi(t, Theta'_t, mu'_t) for dt (x) dP-a.e. (t, omega); and h(t, Theta^-_t, ., mu^-_t) =
    h(t, Theta'^-_t, ., mu'^-_t) in L^2(nu) for dt (x) dP-a.e. (t, omega). Also invariance under
    changing only the Borel representative (same Z, U).
 The coefficients need no regularity for this (the arguments coincide a.e.); a statement
 for arbitrary functions psi, h is fine; one requiring Lipschitz/Borel coefficients is
 harmlessly narrower only if the standing setting already assumes it (it does: Borel).
 The integrals "hence every identity and estimate unchanged" is commentary.
Representation choices: U as an L^2(nu)-valued strongly measurable predictable process with
"U = U' a.e. in L^2(nu)" (equivalent by Fubini) is fine. Existence of the representatives is a
separate clause (not here).
Comparison (verdict recorded 2026-10-17T16:01:29Z):
Comparison, lem_lawflow_invariant (AppA.lean:52-76).
Setting: any probability space, sigma-finite nu on countably generated E, n m d, T; coordinate
processes X (n), Y (m), Z, Z' (m x d), U, U' (m, mark-indexed); Theta_s = tupleAt(X,Y,Z,U,s)
(jump channel the L^2(nu) class of e |-> U_s(omega,e), and 0 when not square integrable),
Theta'_s likewise with Z', U'.
Hypotheses: Z = Z' energyMeasure-a.e. (P (x) Leb|[0,T]) for every coordinate; U = U'
markedEnergyMeasure-a.e. (P (x) Leb|[0,T] (x) nu) for every coordinate - the printed
"Z = Z' dt (x) dP-a.e., U = U' dt (x) dP (x) nu-a.e."; rho, rho' : R -> P2(H) with (rho s).law =
Law(Theta_s) and (rho' s).law = Law(Theta'_s) for a.e. s in [0,T] (flows representing the laws).
Conclusions: rho = rho' for a.e. s in [0,T] (taking Z' = Z, U' = U this is the uniqueness of the
representative flow up to Lebesgue-null sets; in general also the invariance of the flow under
the predictable versions); and for EVERY psi : R -> H -> P2(H) -> W (any target type),
psi(s, Theta_s, rho_s) = psi(s, Theta'_s, rho'_s) for dt (x) dP-a.e. (s, omega) - the invariance of
coefficient evaluations (b, sigma, f, and h as an L^2-valued map; along Theta^- by taking
X := X_-, Y := Y_- as the coordinate processes). Present.
Differences: no cadlag/adaptedness of X, Y, no predictability of Z, U, no square-integrability
hypothesis, and the flows need not be Borel (the printed "Borel representatives"); psi
arbitrary. All dropped hypotheses are unused (the argument is that the arguments coincide a.e.):
broader. The integrability is implicitly forced where needed: (rho s).law in P2 equals the law,
so the laws have finite second moments for a.e. s; the uLift junk 0 only acts on null sets
under the paper's hypotheses.
Instantiation: the paper's X, Y cadlag adapted, Z, U predictable square-integrable, mu, mu^-
Borel representatives - an instance; the existence of the flows is a separate clause.
Witness lem_lawflow_invariant_hypotheses: on a one-point space every tuple's law flow
represents its laws - hypotheses met (degenerate but sufficient; the hypotheses are clearly
satisfiable in general by rho := lawP2).
Verdict: broader.
Witness: —
Verdict: broader — Broader than printed. The Lean drops the lemma's hypotheses (X, Y cadlag adapted; Z, U
predictable; the square-integrability) and does not require the representative flows to be
Borel; it allows every function psi into any type. Its conclusions are the printed uniqueness
(rho = rho' a.e. on [0,T], with Z' = Z, U' = U for two representatives of one flow) and
invariance (psi along (Theta, rho) and (Theta', rho') agree dt (x) dP-a.e.) under changing Z, U on
dt (x) dP- resp. dt (x) dP (x) nu-null sets. Instantiation: the paper's processes and Borel
representatives mu, mu^- (for the predictable tuple, the coordinates X_-, Y_-), psi in
{b, sigma, f} and h as an L^2(nu)-valued map.
Disagreements with the author's review (shown 2026-10-17T16:01:36Z): The author's review recorded for this unit is empty (its text is attached to an adjacent review marker of a unit outside this chunk and was not shown), so there is nothing to compare point by point. My verdict: broader - the proposition drops the lemma's hypotheses (cadlag adapted X, Y; predictable square-integrable Z, U; Borel representatives) and allows any coefficient psi into any type; the printed uniqueness and invariance are its instance.
