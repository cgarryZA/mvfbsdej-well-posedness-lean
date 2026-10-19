### A:ex:brownian: Dissertation.PaperSpec.A.BrownianWeakSolution
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ad5f899adde540f582430c5fbb5efc55 (pl-fp-v1:90bb9a29f8dd89b4f17dfaef61ab09da22a7a6b5535cce0528d7f4cbffd0d0e9)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:12Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:13Z):
Reading of def PaperSpec.A.BrownianWeakSolution (Brownian specialisation of the weak class
Hweak used in Theorem 3.3 and Remark 3.2: Theta in Hweak satisfying (1.1)).

Paper notion. As BrownianSolution (r_05) but with the weak integrability class
Hweak = L^2(0,T;R^n) x L^2(0,T;R^m) x H^2_W: X, Y cadlag adapted with E int_0^T |X_t|^2 dt < inf,
E int_0^T |Y_t|^2 dt < inf; Z predictable with E int_0^T |Z|_F^2 < inf; both identities hold
a.s. for every t in [0,T]. The terminal condition presupposes Law(X_T) in P_2(R^n), i.e.
X_T in L^2 (proof of Thm 3.3: "As the terminal conditions presuppose Law(X^k_T) in P_2(R^n), we
have X^k_T in L^2"); a faithful definition must include X_T in L^2 explicitly or make it
automatic. Coefficient processes need not be a priori square-integrable (Remark 3.4: no
Assumption 2.2), but the integrals in the identities must be meaningful (stochastic integral of
sigma(s,Theta_s,mu_s) requires local square integrability at least).
A faithful Lean definition must: require cadlag adapted X,Y with finite dt dP L^2 norms,
predictable Z in H^2_W, X_T in L^2 (or the P_2 presupposition), the two identities a.s. for every
t, same integrals and law flows as r_05; no extra conditions such as E sup < inf (which would make
it the strong class and lose Theorem 3.3's "Furthermore" content).
Comparison (verdict recorded 2026-10-19T03:32:33Z):
Comparison, PaperSpec.A.BrownianWeakSolution (Sec5BrownianReduction.lean:66-73).

BrownianWeakSolution := BrownianPaperWeakSolution over enlBrownian, plus left limits on every path.
- Weak class Hweak: X, Y cadlag adapted with E int_0^T |.|^2 < inf; Z in H^2_W; X_T in L^2 (the
  paper's presupposition Law(X_T) in P_2); identities a.s. for every t (null set uniform).
- Drift/driver pathwise integrable (no origin integrability needed - Remark 3.4), diffusion finite
  energy (L^2 Ito integral), as analysed in c_17.
- Filtration enlBrownian; hW as for BrownianSolution.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: nu = 0 modelling of the Brownian basis (filtration enlBrownian, trivial
U-channel); and those of BrownianPaperWeakSolution: coordinates, processes on R constrained on
[0,T], Z vanishing off [0,T], identities on one full-measure set with cadlag versions of the Ito
integrals, pointwise law flow, X_T in L^2 as a field (the paper's presupposition Law X_T in P_2),
and "the integrals exist" made explicit (b, f measurable with integrable paths; sigma measurable
with finite energy - under Assumption 2.3 along an Hweak tuple equivalent to sigma(.,0,delta_0) in
L^2(0,T), which any Ito integral of the diffusion requires).
Disagreements with the author's review (shown 2026-10-19T03:32:44Z): none
