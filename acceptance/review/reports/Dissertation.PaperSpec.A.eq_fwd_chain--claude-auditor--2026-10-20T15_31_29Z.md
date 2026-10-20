### A:eq:fwd: Dissertation.PaperSpec.A.eq_fwd_chain
Pins: manuscript A None; project 53a4ee4fc8767ba8884b5732431dded9772b47df; hash ed839d34f480cba15b2aba22478deb02 (pl-fp-v1:b56170ae83577f471ab4e5c3832c9838bc458038a063356d215dfcc908662444)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T15:31:29Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T15:21:24Z):
Reading of the clause "the chain fed into Gronwall, at every t in [0,T], and monotonicity /
finiteness of t -> E sup_{s<=t} |dX_s|^2" of claim A:eq:fwd
(manuscript/paper/sections/04-proof-wellposedness.tex, proof of Lemma lem:pert, Step 3,
lines 697-711, before (4.23)).

Setting and hypotheses in force (Lemma lem:pert): standing basis; Assumptions ass:lip,
ass:G, ass:mono (ass:integ is NOT assumed by Lemma lem:pert); lower bound lambdalow in (0,1],
lambda in [lambdalow, 1]; Theta^1, Theta^2 solve the forced system (4.1) at parameter lambda (same
coefficients b, sigma, h, f, g) with F_0-measurable initial data xi_0^k and square-integrable
forcings q^k; for each k, X^k, Y^k cadlag adapted with E int_0^T (|X^k|^2 + |Y^k|^2) dt < infinity,
X^k_T in L^2(F_T), Z^k in H^2_W, U^k in H^2_N; and Theta^1 - Theta^2 in S. Only ass:lip is used in
this step; a statement dropping ass:G/ass:mono is broader and acceptable.
Notation: q := delta q = q^1 - q^2; P := E|dxi_0|^2 + E|q^g_T|^2 + E int_0^T (|q^b|^2 +
|q^sigma|_F^2 + ||q^h||^2 + |q^f|^2) dt; delta psi_t = psi(t, Theta^1_t, mu^1_t) -
psi(t, Theta^2_t, mu^2_t) (h at the predictable tuples, equal a.e.), mu^k_t = Law(Theta^k_t).
The difference dynamics (4.15): d dX = (lambda db + q^b) dt + (lambda dsigma + q^sigma) dW +
int_E (lambda dh + q^h) Ntilde, dX_0 = dxi_0.

Constant: C > 0 depending only on T, L, ||G||, c_G, alpha, beta_1, beta_2, c_BDG (section
convention; for this step only T, L, c_BDG matter), chosen before t, lambda, the solutions and
the forcings. "Not the same at each occurrence": the three C of the chain may be different
constants of that dependence, but none may depend on t (Gronwall needs t-uniform constants).

Conclusion, for every t in [0,T]:
  (i)   E sup_{s<=t} |dX_s|^2 <= C (E|dxi_0|^2 + E int_0^t (|db_s|^2 + |dsigma_s|_F^2 +
        ||dh_s||^2) ds + P);
  (ii)  the right side of (i) <= C (E|dxi_0|^2 + E int_0^t (|dX_s|^2 + |dY_s|^2 + |dZ_s|_F^2 +
        ||dU_s||^2) ds + P)   (a link B(t) <= C' B'(t) with an admissible constant);
  (iii) that <= C (int_0^t E sup_{r<=s} |dX_r|^2 ds + E int_0^T (|dY_s|^2 + |dZ_s|_F^2 +
        ||dU_s||^2) ds + P);
and t -> E sup_{s<=t} |dX_s|^2 is nondecreasing and finite on [0,T].
A faithful formalization: exists constants (as functions of the listed parameters only), for all
lambda, solutions, forcings satisfying the hypotheses, for every t: the three links. A
formalization with one constant C for all links in the form A <= C B, B <= C B', B' <= C B'' is
equivalent (take the max); one that writes C B <= C B' literally (i.e. B <= B') would be
stronger than printed and likely false. Expectations must be genuine (finite: sup-moment by
Theta^1 - Theta^2 in S, coefficient differences by ass:lip). A witness should have lambda > 0,
nonzero forcing difference or initial difference, so the chain is not 0 <= 0.
Comparison (verdict recorded 2026-10-20T15:28:33Z):
Comparison of Dissertation.PaperSpec.A.eq_fwd_chain (Dissertation/PaperSpec/A/Sec4ProofSteps.lean)
with the locked reading (Step 3 of the proof of Lemma lem:pert, lines 697-711).

Constants and their order. "exists K_1 K_2 K_3 : R^7 -> R" BEFORE the probability space and all
data; the constants of the chain are C_i = K_i(T, L, ||G||, c_G, alpha, beta_1, beta_2), with
||G|| the operator norm of x -> Gx (norm of GX G) and c_G = s_min(G)^{-2} ((sMin G ^ 2)^{-1}).
So the constants depend only on the section's parameters, are independent of t, lambda,
lambdalow, the dimensions, the solutions, the forcings and the initial data, and are chosen
before everything else. Three distinct constants realise "C, not necessarily the same at each
occurrence", in the form A <= C_1 B, C_1 B <= C_2 B', C_2 B' <= C_3 B'' (exactly the printed chain;
no link of the form B <= B' is imposed). c_BDG does not appear among the arguments: it is one
universal number, so a function of the other parameters subsumes any dependence on it; the
proposition is at least as strong as the printed dependence. Match.

Setting and hypotheses (Lemma lem:pert): standing basis; n, m, d > 0, T > 0; JointBorel (2.3);
Assumption23 with L (ass:lip); G.rank = min m n (ass:G, full rank); Assumption25 with
G, alpha, beta_1, beta_2 (ass:mono, with the admissible constants); NOT Assumption22, exactly as
Lemma lem:pert ("Let Assumptions ass:lip-ass:mono hold"). lamLow in (0,1], lam in [lamLow, 1].
Initial data xi_1, xi_2 measurable for the time-0 field of enlJoint (F_0-measurable, no L^2
requirement, as printed). Forcings q^1, q^2 each of the class of (4.1) (PredForcing).
Theta^k: WeakForcedSolution at lam with (xi_k, q^k): (4.1) in H_weak with X^k_T in L^2, cadlag
adapted X^k, Y^k with finite energy, Z^k, U^k predictable with finite energy. Theta^1 - Theta^2 in
S: supSize of the difference finite. Match.

Conclusion, for every t in [0,T]:
- LHS: E sup_{s in [0,t]} |dX_s|^2 (lintegral of the pointwise sup over Icc 0 t). Match.
- B = E|dxi_0|^2 + [sum_i E int_0^t |db_i|^2 + sum_ij E int_0^t |dsigma_ij|^2
  + sum_i E int_0^t int_E |dh_i(e)|^2 nu(de)] + P, with db, dsigma the drift and diffusion
  processes along (Theta^k_s, Law Theta^k_s) and dh through coeffJump, the canonical
  representative of h(s, Theta^{k-}_s, ., mu^{k-}_s) at the predictable tuple (as the proof
  specifies for dh), P = dataSize of the DIFFERENCES of the data (E|dxi_0|^2 + E|dq^g|^2 +
  E int_0^T (|dq^b|^2 + |dq^sigma|^2 + ||dq^h||^2 + |dq^f|^2)), i.e. the proof's P with q := delta q.
  Match.
- B' = E|dxi_0|^2 + E int_0^t (|dX|^2 + |dY|^2 + |dZ|_F^2 + ||dU||^2) ds + P. Match.
- B'' = int_0^t E sup_{r <= s} |dX_r|^2 ds + E int_0^T (|dY|^2 + |dZ|_F^2 + ||dU||^2) ds + P. Match.
- MonotoneOn [0,T] of t -> E sup_{s <= t} |dX_s|^2, and finiteness at every t in [0,T]. Match.
All expectations in [0, infinity]; quantities are finite under the hypotheses (difference in S,
P possibly infinite only if the data differences are not square integrable, in which case the
links hold trivially, exactly as in the paper).

Representation choices (harmless): constants as functions K_i of the parameter tuple
(T, L, ||G||, c_G, alpha, beta_1, beta_2) with c_BDG absorbed; ofReal(K_i) as the multiplier in
[0, infinity]; coordinates; expectations in [0, infinity]; dh read through the canonical
representative coeffJump (unique up to dt x dP x nu-null sets, so the energy is
representative-independent); Theta^1 - Theta^2 in S as finiteness of supSize of the difference.

Witness. Dissertation.Acceptance.A.lem_pert_backward_window_hypotheses: Example 5.1(i)
(b = -y, sigma = -z, h = -u, f = x, g = x) with n = m = d = 1, nu = Dirac mass at 0, T = 1, L = 1,
G = 1, alpha = beta_1 = beta_2 = 1, lam = lamLow = 1, solutions built from everywhere-cadlag
versions M^W, M^N of int 1_{(0,1]} dW and int int 1_{(0,1]} dNtilde: the difference has dX = 1,
dY = M^W + M^N, dZ = dU = 1_{(0,1]}, initial difference 1, with forcings of the paper's class.
All hypotheses of the proposition are supplied; the chain is not 0 <= 0 (E sup_{s <= t} |dX_s|^2
= 1 and B, B', B'' > 0). It is an instance the paper intends (Example 5.1(i) satisfies
Assumptions ass:lip-ass:mono).

Coverage. Claim A:eq:fwd has two clauses: eq_fwd ((4.23): E sup |dX|^2 <= C (E int (|dY|^2 +
|dZ|^2 + ||dU||^2) + P), C a function of (T, L, ||G||, c_G, alpha, beta_1, beta_2)) and this one
(the three-link chain at every t and the monotonicity and finiteness of lines 710-711). Together
they state every mathematical assertion of lines 697-714 (the Gronwall step itself is the
passage from this clause to (4.23)). Nothing beyond the passage is stated, and the hypotheses
are those of Lemma lem:pert in force at that point. The clause reads lines before the pinned
region (712-714), so a change to lines 697-711 would not by itself reopen the review.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless: (1) the three constants are values K_i(T, L, ||G||, c_G,
alpha, beta_1, beta_2) of functions chosen before everything else, one per link in the form
A <= C_1 B, C_1 B <= C_2 B', C_2 B' <= C_3 B'' (the printed chain with "C not necessarily the same
at each occurrence"); c_BDG, a single universal number, is absorbed into the functions, which
makes the statement at least as strong as the printed dependence; (2) expectations are lower
Lebesgue integrals in [0, infinity] with ofReal(K_i) as multipliers; (3) coordinates; (4) dh is
read through the canonical representative coeffJump of h at the predictable tuple, which fixes
the energy independently of the representative; (5) Theta^1 - Theta^2 in S is finiteness of supSize
of the difference. Hypotheses (Lemma lem:pert: (2.3), ass:lip, ass:G, ass:mono, lamLow in (0,1],
lambda in [lamLow,1], F_0-measurable initial data, forcings of the paper's class, solutions in
H_weak with X_T in L^2, difference in S), the "every t in [0,T]" quantifier, the three links and
the monotonicity/finiteness assertion match the printed step.
Disagreements with the author's review (shown 2026-10-20T15:30:43Z): No disagreement on substance: same hypotheses (those of Lemma lem:pert, without Assumption
ass:integ), same three links with one constant per link chosen first as functions of (T, L, ||G||,
c_G, alpha, beta_1, beta_2), no dependence on t, lambda or lamLow, delta h through coeffJump at the
predictable tuples, the same monotonicity/finiteness reading, and a nondegenerate witness. Verdict
label: I record "faithful with representation choices" because c_BDG, a universal number, is
absorbed into the functions K_i rather than being an argument, and because of the usual choices
(coordinates, [0, infinity] expectations with ofReal multipliers, Theta^1 - Theta^2 in S as finite
supSize). Procedural remark: the clause reads lines 697-711, before the pinned region (712-714).
