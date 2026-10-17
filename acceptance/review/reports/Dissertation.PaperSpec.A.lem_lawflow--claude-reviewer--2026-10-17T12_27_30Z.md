### A:lem:lawflow: Dissertation.PaperSpec.A.lem_lawflow
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1090c1a53f2a6cf7f (pl-fp-v1:4eeba240aecc16dc401abc87b1417f47a47d085549d3ad71adab8d545fa03dfc)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:27:30Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:26:08Z):
# Reading: lem_lawflow (Lemma A.1, first part: the Borel law flows)

Hypotheses: standing basis (filtration of §2), horizon T > 0, dimensions n, m, d; X (R^n), Y (R^m)
cadlag adapted; Z (R^{m x d}) and U (R^m-valued on E, P x E-measurable) fixed predictable
versions; E int_0^T (|X_t|^2 + |Y_t|^2 + |Z_t|_F^2 + int_E |U_t(e)|^2 nu(de)) dt < infinity.
Objects: Theta_t = (X_t, Y_t, Z_t, U_t) and Theta^-_t = (X_{t-}, Y_{t-}, Z_t, U_t) as H-valued random
variables, U_t(omega) the L^2(nu)-class of e -> U_t(omega, e) (defined for a.e. (t, omega)); the maps
t -> Law(Theta_t), t -> Law(Theta^-_t) are defined (as elements of P_2(H)) for a.e. t.
Conclusion:
- there exist Borel maps mu, mu^- : [0,T] -> (P_2(H), W_2) (Borel for the W_2 topology, W_2 for the
  Hilbert norm of H) with mu_t = Law(Theta_t) for a.e. t and mu^-_t = Law(Theta^-_t) for a.e. t;
- uniqueness up to Lebesgue-null sets (any two Borel maps with these properties agree a.e. --
  immediate from the a.e. identities, but part of the statement);
- mu^-_t = mu_t for a.e. t.
Faithful formalisation must use the genuine left limits (not X itself) for Theta^-, the genuine law
(pushforward) in P_2(H), and a.e. in Lebesgue measure on [0,T]. Junk values of Law where Theta_t is
not square integrable are harmless only because the identities are a.e. in t. The second sentence
(invariance of coefficient evaluations) is a separate clause (lem_lawflow_invariant).
Non-vacuity: hypotheses met e.g. by Theta = 0 (witness).
Comparison (verdict recorded 2026-10-17T12:27:14Z):
# Comparison: lem_lawflow

Lean (AppA.lean:32): for every filtration F, probability P, sigma-finite nu on countably generated
E, n, m, d, T and processes X, Y, Z, U with CadlagPredTuple (X, Y adapted, every path right-
continuous with left limits at every real t; Z predictable; U marked predictable; finite energies
on [0,T]): (1) s -> lawP2 P (tupleAt X Y Z U s), viewed in P2WH (P_2(H) with the Hilbert-norm W_2
metric and its Borel sigma-algebra), is measurable; (2) likewise for Theta^- (leftLimProc X,
leftLimProc Y = genuine left limits Function.leftLim); (3) for a.e. s in [0,T]: both are the
image measures P o Theta_s^{-1}, P o (Theta^-_s)^{-1}, and they coincide.

Against my reading:
- Hypotheses: cadlag adapted X, Y, predictable Z, U, finite energy -- yes. Differences: the
  filtration is arbitrary (broader); X, Y are required cadlag along every path and at every real t
  rather than on [0,T] (a paper process on [0,T] extends, e.g. by 0 before 0 and by X_T after T,
  to one satisfying this; the left limit at 0 changes only at the single time 0; a.s.-cadlag
  processes can be modified on a null set under the usual conditions) -- representation choice.
- Conclusion: the Borel representatives are chosen canonically as the junk-extended flows
  s -> lawP2 P Theta_s (the image measure when Theta_s is square integrable, delta_0 otherwise);
  the Lean proves they are Borel for the W_2 topology and equal to the genuine laws for a.e. s,
  i.e. they are representatives as the lemma asserts; mu_s = mu^-_s for a.e. s: yes.
- "Unique up to Lebesgue-null sets" is not stated; it is immediate from the a.e. identities.
- The U-channel is the L^2(nu)-class uLift of e -> U_s(omega, e) (0 when not square integrable),
  the paper's U_t(omega, .) for a.e. (s, omega). Correct.
- Non-vacuity: witness lem_lawflow_hypotheses (zero tuple on a one-point space).

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The Borel representatives mu, mu^- are taken to be the flows s -> lawP2 P Theta_s and
   s -> lawP2 P Theta^-_s themselves (the law where Theta_s is square integrable, delta_0
   otherwise); the proposition proves them Borel into (P_2(H), W_2) and equal to the genuine image
   laws for a.e. s, which is what being a representative means.
2. "Unique up to Lebesgue-null sets" is omitted: any two maps a.e. equal to the same a.e.-defined
   map agree a.e.
3. The hypothesis "cadlag adapted" is required along every path and at every real time, for an
   arbitrary filtration; a paper process on [0,T] (cadlag a.s., usual conditions) can be modified
   on a null set and extended outside [0,T] to meet it without changing any law at times of
   (0,T].
Disagreements with the author's review (shown 2026-10-17T12:27:14Z): Agreement on the correspondence. Classification differs mildly: the author records "faithful",
I record "faithful with representation choices": the representatives are the canonical
junk-extended flows s -> lawP2(Theta_s) (delta_0 where Theta_s is not square integrable), the
cadlag hypothesis is imposed on every path at every real time over an arbitrary filtration, and
uniqueness up to null sets is left to lem_lawflow_invariant. All harmless.
