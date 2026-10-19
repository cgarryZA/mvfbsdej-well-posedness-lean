### A:lem:lawflow: Dissertation.PaperSpec.A.lem_lawflow_invariant
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba184c9d1f8d6f2b814 (pl-fp-v1:5b592b7821c070fecd50bbe1798b7b7ff34350b9115d2311b8dc73c336b059ac)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:38:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:45Z):
# Reading: spec lem_lawflow_invariant (Lemma A.1: uniqueness of the flows and invariance under representatives)

Lemma A.1, second part: the Borel representatives mu, mu^- of t -> Law(Theta_t), Law(Theta^-_t)
are unique up to Lebesgue-null sets of times; and coefficient evaluations along these
representatives are invariant, up to dt x dP-null sets, under the choice of predictable
representatives of (Z,U) and of the Borel representatives.
A faithful formal statement (hypotheses as Lemma A.1: X, Y cadlag adapted, Z, U predictable,
E int (|X|^2+|Y|^2+|Z|^2+||U||^2) dt < oo):
* Uniqueness: any two Borel maps mu, mu~ : [0,T] -> P2(H) with mu_t = Law(Theta_t) a.e. and
  mu~_t = Law(Theta_t) a.e. agree for a.e. t (same for mu^-).
* Invariance: for (Z',U') another pair of predictable versions (Z = Z' dt x dP-a.e., U = U'
  dt x dP x nu-a.e., or a.e. as L^2(nu)-valued processes), with flows mu', mu'^- representing the
  laws of Theta' = (X,Y,Z',U') and Theta'^-, and for ANY coefficient psi (b, sigma, f evaluated at
  (s, Theta_s, mu_s); h at (s, Theta^-_s, mu^-_s)):
  psi(s, Theta_s(omega), mu_s) = psi(s, Theta'_s(omega), mu'_s) for dt x dP-a.e. (s,omega)
  (in L^2(nu) for h), and likewise when only the Borel representative is changed.
  No regularity of psi is needed (the arguments coincide a.e.); a statement requiring Lipschitz
  or continuity of psi would be narrower but harmless if the paper's coefficients satisfy it.
* The time domain [0,T], Lebesgue measure; P the standing measure.
Comparison (verdict recorded 2026-10-19T03:35:21Z):
# Comparison: lem_lawflow_invariant (Lemma A.1: uniqueness of the flows, invariance)

Lean (AppA.lean): for every probability space, sigma-finite nu on countably generated E, n, m, d,
T, ANY processes X, Y, two versions Z, Z' (equal dP x dt-a.e. on Omega x [0,T]) and U, U' (equal
dP x dt x nu-a.e.), ANY flows rho, rho' : R -> P2(H) with (rho s).law = P.map Theta_s and
(rho' s).law = P.map Theta'_s for a.e. s in [0,T] (Theta = tupleAt X Y Z U, Theta' = tupleAt X Y Z'
U'), and ANY function psi : R -> H -> P2(H) -> W (any target type):
  rho s = rho' s for a.e. s in [0,T], and
  psi(s, Theta_s(omega), rho_s) = psi(s, Theta'_s(omega), rho'_s) for dP x dt-a.e. (omega, s).

Against my reading:
* Uniqueness of the flows: the case Z' = Z, U' = U gives that any two representatives of
  t -> Law(Theta_t) agree a.e.; the Borel property is not even needed. Yes.
* Invariance under the choice of versions of (Z, U) and of representatives: yes, both changes at
  once, for every coefficient psi, with no regularity of psi (as my reading said none is needed);
  the jump coefficient (L^2(nu)-valued, at Theta^-) is covered by taking W = L^2(nu; R^n) and X, Y
  replaced by their left-limit processes, since X, Y are arbitrary.
* a.e. w.r.t. dt x dP on [0,T] x Omega: yes (energyMeasure = P x Lebesgue on [0,T]).
Differences (generalisations): X, Y, Z, U need not be cadlag/predictable/square integrable (the
statement is for arbitrary processes); the versions Z', U' need not be predictable; the flows need
not be Borel; psi is arbitrary.
Instantiation giving the printed clause: X, Y, Z, U as in Lemma A.1, (Z', U') another pair of
predictable versions, rho, rho' the Borel flows of the first clause for the two pairs (and the
same pair for the uniqueness statement), psi in {b, sigma, f}, and for h the same with X, Y
replaced by leftLimProc X, leftLimProc Y and the flows mu^-.
Verdict: broader.
Witness: —
Verdict: broader — Broader than printed: the statement holds for arbitrary processes X, Y, arbitrary versions Z', U'
equal to Z, U dP x dt (x nu)-a.e. (not necessarily predictable), arbitrary flows rho, rho' that
represent the laws of Theta_s, Theta'_s for a.e. s (not necessarily Borel) and an arbitrary
coefficient psi with any target. Instantiation giving the printed clause: take X, Y cadlag adapted
and Z, U predictable as in Lemma A.1; for uniqueness of the flows take Z' = Z, U' = U and two Borel
representatives rho, rho' (conclusion rho = rho' a.e.); for invariance take (Z', U') another
pair of predictable versions and rho, rho' the corresponding Borel flows, with psi = b, sigma, f,
and for h the same applied to X, Y replaced by their left limits (the predictable tuple Theta^- and
the flows mu^-), W = L^2(nu; R^n).
Disagreements with the author's review (shown 2026-10-19T03:38:30Z): none
