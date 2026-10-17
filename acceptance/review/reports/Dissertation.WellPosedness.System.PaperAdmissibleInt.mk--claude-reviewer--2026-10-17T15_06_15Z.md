### A:cor:robust, A:rem:cwp-class, A:rem:generalrank, A:sec3:one-null-set, A:sec:examples, A:thm:uniq: Dissertation.WellPosedness.System.PaperAdmissibleInt.mk
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 9e454a38d7aa3b8f0000000000000000 (pl-fp-v1:16ca1169031a44afd34efb05b878ea52bb12541d5428a97e0701ad53429c4231)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:06:15Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:33:34Z):
Reading for PaperAdmissibleInt.mk (the anonymous constructor of the structure PaperAdmissibleInt).
Paper notion: same as PaperAdmissibleInt -- "the integrals of (1.1) along Theta exist" (coefficient
processes along the candidate tuple are measurable in the right sense, progressively measurable
for b, sigma, f, predictable for the jump integrand h(s, Theta_{s-}, e, mu^-_s), and integrable
enough for the Lebesgue, Ito and compensated-Poisson integrals of (1.1) to be defined).
A faithful constructor must take exactly the fields of the structure as arguments and produce the
structure; it may add nothing and drop nothing. Its type must be: (all field hypotheses) ->
PaperAdmissibleInt F P T C X Y Z U gamma. Its faithfulness reduces to that of the structure: every
field must be one the paper's notion requires (measurability, integrability for the integrals, the
predictable representative of the jump coefficient), and none may impose more than the paper's
admissible class (e.g. no square-integrability of b or f beyond what the paper's integrals need in
the classes where the paper does not have it).
Comparison (verdict recorded 2026-10-17T12:38:01Z):
Comparison for PaperAdmissibleInt.mk. The constructor's type takes exactly the 13 fields of the
structure PaperAdmissibleInt (b_meas, b_prog, b_int, sigma_meas, sigma_prog, sigma_sq, gamma_meas,
gamma_prog, gamma_sq, f_meas, f_prog, f_int, jump_rep), in that order, with the implicit parameters
of the structure, and returns PaperAdmissibleInt F P T C X Y Z U gamma. It adds and drops nothing,
so its meaning is the structure's, reviewed under PaperAdmissibleInt: faithful to the paper's
"the integrals of (1.1) along Theta exist" with the representation choices listed there (indicator
cut to [0,T], exact laws at every time with Dirac-0 junk off L^2, uLift junk on a null set, marked
progressive representative gamma of the predictable jump integrand, finite energy of sigma and gamma,
junk left limits at s = 0 / on null paths).
Witness: —
Verdict: faithful with representation choices — Representation choices (all harmless):
1. Coefficient processes are extended by 0 off [0,T] (indicator); only [0,T] enters (1.1).
2. mu_s, mu^-_s are the exact laws lawP2 P Theta_s at every time (Dirac 0 when Theta_s is not in L^2)
   instead of Lemma A.1's Borel representatives; they agree for a.e. s, so coefficient processes
   agree dt dP-a.e. and every integral is unchanged.
3. The L^2(nu) channel uLift is 0 where U_s(omega,.) is not square integrable: a dt dP-null set.
4. The Poisson integrand is a representative gamma required marked progressively measurable and
   equal nu-a.e. to h(s,Theta^-_s,.,mu^-_s) for a.e. s, a.s. (the paper's is predictable); the L^2
   compensated integral depends only on the dP dt nu class, so it is the paper's integral.
5. Finite energy of sigma and gamma (L^2 stochastic integrals) rather than mere existence; under
   Ass 2.3 (assumed wherever the unit is used) any Hweak tuple along which these integrals exist
   satisfies it. Drift/driver only need a.s. integrable paths, matching the Lebesgue integrals.
6. Joint measurability is asked besides progressive measurability (implied).
7. leftLimProc at s = 0 / where no left limit exists takes junk values: a single time and a null set
   of paths, irrelevant to the a.e.-s representation.
Disagreements with the author's review (shown 2026-10-17T15:05:44Z): none (the author's excerpt shown for this unit is a marker and at most a section heading, with no
item-level reading to compare against; my comparison file records the representation choices in
detail).
