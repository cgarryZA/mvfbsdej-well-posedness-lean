### A:sec3:HH-banach: Dissertation.PaperSpec.A.sec3_HH_definite
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba12b4c9985cfe528af (pl-fp-v1:9238ee69573b14140e3037360bc0cb4c0c116d92a2df27e1bbd116f0995043aa)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:14Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:14Z):
Reading of spec sec3_HH_definite: sec. 3 "Solution space" (03-main-results.tex:21-32), clause
"under the identification ||.||_HH is a norm: it vanishes exactly on the zero class".

Paper claim. For Theta = (X,Y,Z,U) in HH (X, Y cadlag adapted with E sup |.|^2 < inf, Z predictable
in H^2_W, U predictable in H^2_N), with
 ||Theta||^2_HH = E sup_{t<=T}|X_t|^2 + E sup_{t<=T}|Y_t|^2 + E int_0^T (|Z_t|_F^2 + ||U_t||^2) dt,
||Theta||_HH = 0 if and only if Theta is the zero class: X and Y indistinguishable from 0
(P(exists t <= T: X_t != 0) = 0), Z = 0 dt dP-a.e., U = 0 dt dP nu-a.e. (equivalently ||U_t|| = 0
dt dP-a.e.). Since elements are classes, the same applies to differences: ||Theta - Theta'|| = 0
iff Theta and Theta' are identified.
A faithful formal statement: both directions (norm zero <=> zero class), for all Theta in HH (or for
all Theta; for Theta outside HH, the "norm" may be infinite or junk - must not be used to give a
spurious statement); on the time interval [0,T]; indistinguishability for X, Y (not merely
"X_t = 0 a.s. for each t" which is weaker for non-cadlag, though for cadlag equivalent); a.e. for
Z and U with the right product measures. If the norm is an ENNReal lintegral, fine; in R via
Bochner integrals, the class must guarantee integrability (it does for HH).
Comparison (verdict recorded 2026-10-19T03:32:34Z):
Comparison, sec3_HH_definite (Sec3Space.lean:110-125).

- For every tuple Theta = (X,Y,Z,U) in PaperWeakTuple over enlJoint (Hweak: cadlag adapted X, Y with
  finite dt dP energy, Z predictable, U marked predictable, both with finite energy, vanishing off
  [0,T]) - a superset of HH:
  supSize (= E sup_[0,T]|X|^2 + E sup_[0,T]|Y|^2 + E int_0^T (|Z|_F^2 + ||U||^2), in [0,inf]) = 0
  iff X and Y are indistinguishable from 0 on [0,T] (a.s., for all t in [0,T]), Z = 0
  (P x Leb|[0,T])-a.e., U = 0 (P x Leb|[0,T] x nu)-a.e. Both directions; [0,T]; indistinguishability;
  the right product measures. ENNReal values: for Theta in Hweak \ HH the norm is infinite and the
  right side false, consistent. Measurability of the sup holds since every path is right-continuous
  on [0,T) (so int^- = 0 does give a.e. vanishing - not a vacuous use of lintegral of a
  non-measurable function).
- Quantifying over Hweak instead of HH is broader; HH is contained in it.
- Witness sec3_space_hypotheses (generic).
Verdict: broader.
Witness: —
Verdict: broader — Broader: the equivalence is stated for every tuple of Hweak (PaperWeakTuple over the sec. 2
filtration), which contains HH. Instantiation giving the printed clause: restrict to Theta in HH
(E sup |X|^2, E sup |Y|^2 < inf, so in particular finite dt dP energies, Theta in PaperWeakTuple);
then ||Theta||_HH = 0 iff X, Y indistinguishable from 0 on [0,T], Z = 0 dt dP-a.e., U = 0
dt dP nu-a.e. Representation: coordinates, Z, U vanishing off [0,T], ||.||^2_HH in [0,inf].
Disagreements with the author's review (shown 2026-10-19T03:32:45Z): Label only. The review records "faithful with representation choices" while noting in its point 2
that the statement is broader (every tuple of H_weak, with HH the instance). I record "broader"
with that instantiation. On the substance (both directions, indistinguishability on [0,T], a.e.
with respect to the energy measures, ENNReal values) we agree. I add that the lintegral of the
supremum is of a measurable function because every path is right-continuous on [0,T), so
"supSize = 0" does give the a.e. vanishing.
