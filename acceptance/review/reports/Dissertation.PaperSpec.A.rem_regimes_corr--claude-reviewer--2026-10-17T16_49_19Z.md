### A:rem:regimes: Dissertation.PaperSpec.A.rem_regimes_corr
Pins: manuscript A None; project aaff2d964a19fbd6388335c908ac88573d3d4516; hash ed839d34f480cba16f1e06b2c31d2e18 (pl-fp-v1:c78a86f90c24dff11ccf87bfb57b3218878a3f3f7c3d7e5c32028722daa8b8f0)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:49:19Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T16:41:44Z):
# Reading: spec rem_regimes_corr (Remark 5.7, corrected clause "the dealer interaction is affine
in the U-law, no function of its mean, and nonlinear in the valuation curve, with L^2(nu) != 0")

Printed: "Example 5.6 shows that a genuinely nonlinear U-law interaction can have arbitrary
strength when its geometry is itself monotone." This clause concerns only the first half: that
the dealer crowding correction is "a genuinely nonlinear U-law interaction". Example 5.6:
  A_lambda(u) := integral_{L^2(nu)} grad V(u - v) lambda(dv),  V(w) = sqrt(1 + |w|^2) - 1,
  grad V(w) = w / sqrt(1 + |w|^2), lambda in P_2(L^2(nu)), entering h through
  h = h_c - beta_1 u - eps A_{mu^U}(u), mu^U the U-marginal of the full-tuple law argument.
In Example 5.6 n = m = d = 1, so L^2(nu) = L^2(nu; R). The "Beyond the mean" paragraph shows: for
a unit w, lambda_1 = (delta_{-w} + delta_w)/2 and lambda_2 = (delta_{-2w} + delta_{2w})/2 have the
same mean (0) but A_{lambda_1}(w) = w/sqrt5 != (3/sqrt10 - 1/sqrt2)/2 w = A_{lambda_2}(w).

What "genuinely nonlinear U-law interaction" means: A depends on the U-law beyond its mean, and
is nonlinear (A_lambda(u) is an integral of the NONLINEAR kernel grad V against lambda). As a
function of the measure lambda, A is mixture-affine (an integral against lambda), so "nonlinear"
cannot sensibly mean "non-affine in lambda"; recording that A is affine in lambda is an extra,
true conjunct not printed in the remark (harmless if correct, but it is an addition). The
printed claim implicitly needs L^2(nu) != {0} ("a unit w"): with nu = 0 (allowed: sigma-finite),
A == 0, which is a function of the mean and linear -- so the printed reading is false there; the
correction "with L^2(nu) != 0" is the right one.

A faithful corrected statement must contain:
1. Setting: every measurable space (E, calE) [countably generated] and every sigma-finite nu
   with L^2(nu; R) (or R^m) nontrivial. (Dropping countably-generated / sigma-finite is harmless
   broadening.) No other hypothesis (no restriction to the specific nu of "Marks and activity").
2. The object: the paper's A_lambda(u) with V, grad V as above, lambda over P_2(L^2(nu))
   (or a superset, as long as the witnesses are P_2 laws), integral = Bochner integral in
   L^2(nu). Whether stated for A itself or for the eps-term with eps > 0 does not matter (the
   properties are invariant under positive scaling), but eps = 0 must not be included.
3. Conclusions:
   (a) not a function of its mean: NOT EXISTS F with A_lambda(u) = F(u, mean(lambda)) for all
       lambda, u; equivalently EXISTS lambda_1, lambda_2 in P_2 with equal means and u with
       A_{lambda_1}(u) != A_{lambda_2}(u). Mean = Bochner mean (no junk at the witnesses).
   (b) nonlinear in the valuation curve u: u |-> A_lambda(u) is not linear/affine (for some
       lambda suffices; in fact for every lambda it is bounded and non-constant, hence not
       affine).
   (c) [affine in the U-law: A_{t l1 + (1-t) l2}(u) = t A_{l1}(u) + (1-t) A_{l2}(u)] -- extra.
4. No constants. Must not narrow beyond L^2(nu) != 0 (e.g. no requirement nu(E) = infinity or a
   specific E).
Comparison (verdict recorded 2026-10-17T16:48:21Z):
# Comparison: spec rem_regimes_corr (Remark 5.7, corrected clause)

(Numbering note: my reading called the dealer example "Example 5.6"; in the printed numbering it is
Example 5.5 and the nonlinear-functionals example is 5.4. Substance unaffected.)

Lean (PaperSpec/A/Sec5Regimes.lean): for every measurable E, sigma-finite nu, E countably generated,
if some u in Lp(R^1) 2 nu is nonzero, then
 (1) for all Lam1, Lam2 in P2(L^2(nu)), s in [0,1], u:
     A_{s Lam1 + (1-s) Lam2}(u) = s A_{Lam1}(u) + (1-s) A_{Lam2}(u)       [affine in the law]
 (2) NOT exists Phi : L^2 -> L^2 -> L^2 with A_Lam(u) = Phi(int v dLam, u) for all Lam in P2, u
                                                                         [no function of the mean]
 (3) exists Lam in P2 such that NOT exists linear A0 and c with A_Lam(u) = A0 u + c for all u
                                                                         [not affine in u]
where A = ex55Crowd: A_Lam(u) = int (sqrt(1 + |u - v|^2))^{-1} (u - v) dLam(v) (Bochner, in L^2(nu)).
The refuted original (corrects:) is rem_regimes_law_nonlinear, "not affine in the law".

Item by item against my locked reading:
- Object: ex55Crowd is exactly grad V(u - v) integrated against lambda, grad V(w) = w/sqrt(1+|w|^2),
  on L^2(nu; R) (EuclideanSpace R (Fin 1) = R; m = 1 as in the dealer example). Lam ranges over
  P2 (probability laws, finite second moment, Borel sigma-algebra on L^2). The integrand is bounded
  by 1 and continuous, L^2(nu) separable (countably generated E, sigma-finite nu), so the Bochner
  integrals are genuine (no junk 0) for every probability law, mixtures included; the mean of a P2
  law is a genuine Bochner mean. The clause is about A itself, not eps*A; scaling by eps > 0
  preserves (2), (3) (and (1)); eps = 0 is not included. Fine.
- Setting: every sigma-finite nu on a countably generated E with L^2(nu) != 0 -- exactly the
  correction, nothing narrower (no restriction to the dealer marks nu or to infinite activity).
  The hypothesis is met (witness ex_dealer_unit_hypotheses: a unit vector for the dealer marks
  measure).
- (2) = my (a) "not a function of its mean" (equivalent to two P2 laws with equal means and a u
  separating A). Matches the "Beyond the mean" paragraph.
- (3) = my (b) "nonlinear in the valuation curve": not affine, with an arbitrary (not necessarily
  continuous) linear part -- strong form; "for some Lam" suffices for "nonlinear".
- (1) = my (c): an extra conjunct, not printed in Remark 5.7, true (A is an integral against
  lambda). As I anticipated, it records that "nonlinear" cannot mean nonlinear in the law. It adds
  content and narrows nothing.
- Scope: this clause covers only "the dealer interaction is a genuinely nonlinear U-law
  interaction"; "arbitrary strength when its geometry is monotone" and the Example 5.4 sentence are
  not in this proposition (other clauses of A:rem:regimes, presumably).

Relative to "printed claim + named correction": under my reading of "genuinely nonlinear U-law
interaction" (dependence on the U-law beyond its mean through the nonlinear kernel grad V), the
printed claim corrected by L^2(nu) != 0 is exactly conjuncts (2) and (3), at the printed
generality. Conjunct (1) is additional. So the proposition says strictly more: broader.
Note on the correction: relative to the refuted reading ("not affine in the law"), the corrected
clause does not add only "with L^2(nu) != 0" -- it replaces the reading (and asserts the opposite,
affinity in the law); its clause name says so. Under my reading that replacement is the right
reading of the printed words, and the only needed correction is L^2(nu) != 0.
Witness: —
Verdict: broader — The proposition is the printed claim with the correction L^2(nu) != 0, plus one conjunct the remark
does not print. Reading "a genuinely nonlinear U-law interaction" as dependence on the U-law beyond
its mean through the nonlinear kernel grad V (Example 5.5, "Beyond the mean"), the printed claim
corrected by L^2(nu) != 0 is exactly conjuncts 2 and 3: for every sigma-finite nu on a countably
generated E with a nonzero element of L^2(nu; R), there is no Phi with A_Lam(u) = Phi(mean Lam, u)
for all Lam in P2(L^2(nu)) and u, and for some Lam the map u |-> A_Lam(u) is not affine.
Instantiation giving the printed claim: drop conjunct 1. Conjunct 1 (A is affine under mixtures of
the law, for Lam1, Lam2 in P2 and s in [0,1]) is an addition: true, and it records that
"nonlinear" cannot mean nonlinear in the law. Relative to the refuted reading ("not affine in the
law", false at every nu), the correction is not only "with L^2(nu) != 0": the clause re-reads the
printed words, as its name says.
Disagreements with the author's review (shown 2026-10-17T16:49:03Z): 1. What is shown is not a review of this proposition: it points to a claude-reviewer verdict
   "faithful" on rem_regimes_law_nonlinear, the refuted original ("the crowding correction is not
   affine in the law"). rem_regimes_corr itself (affine in the law; no function of the mean; for
   some Lam not affine in u; under L^2(nu) != 0) has no review shown, so nothing here checks it.
2. I disagree with treating "not affine in the law" as the faithful reading of "a genuinely
   nonlinear U-law interaction". The paper's own context points the other way: Example 5.4 sets
   its nonlinear law functionals apart from "the expectation and two-point-kernel" interactions,
   and the crowding correction int grad V(u - v) lambda(dv) is a two-point-kernel interaction, so
   the authors cannot mean "nonlinear in lambda"; the "Beyond the mean" paragraph of Example 5.5
   gives the intended sense (dependence on the U-law beyond its mean, through the nonlinear kernel
   grad V). Under that reading the printed claim is true once L^2(nu) != 0, and the only
   correction it needs is that hypothesis. The refutation is a valid proof against the strong
   reading, but that reading is at best one of two, and the printed claim is better described as
   "needs L^2(nu) != 0" than as "false".
3. Verdict for this unit: `broader`. Conjuncts 2-3 are the printed claim (in the reading above)
   with the correction L^2(nu) != 0, at the printed generality (every sigma-finite nu on a
   countably generated E with L^2(nu) != 0); conjunct 1 (affine in the law) is an unprinted,
   true addition. The clause therefore changes more than its trailing "with L^2(nu) != 0" relative
   to the refuted reading, which the review shown does not record.
