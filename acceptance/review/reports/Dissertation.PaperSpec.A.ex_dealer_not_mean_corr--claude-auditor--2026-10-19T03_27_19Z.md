### A:ex:dealer, A:rem:regimes: Dissertation.PaperSpec.A.ex_dealer_not_mean_corr
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1d76cfc2366e08961 (pl-fp-v1:0a0d3574c8f3a2fc3812ff4578067f4af1b7159ccef7be9852c753c3604c4c8c)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:19Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:07Z):
Reading of spec:Dissertation.PaperSpec.A.ex_dealer_not_mean_corr (Example 5.5 and Remark 5.7,
clause "the crowding correction is no function of the mean and is nonlinear in the valuation
curves, with L2(nu) != 0; Example 5.5: the U-law interaction is nonlinear in the valuation curves
(and no function of the mean of the U-law), with L2(nu) != 0").

Paper. Ex. 5.5 (05-examples.tex:401-412): "The crowding correction is not a function of E[U]: ...
The correction is nonlinear in the valuation curves, but affine in their population law".
Rem. 5.7 (05-examples.tex:544-549): "Example 5.5 shows that a U-law interaction nonlinear in the
valuation curves can have arbitrary strength when its geometry is itself monotone, and remain
active along the solution."  (The "arbitrary strength / active" parts are other clauses.)

Faithful statement (conjunction), under nu != 0 / fibre nontrivial, fibre L2(nu; R) (m = 1; general
m broader and harmless):
(a) No function of the mean: there is no F with A_lambda(u) = F(mean lambda, u) for all
    lambda in P2(L2(nu)) and u in L2(nu) (equivalently two laws in P2 with equal barycentres and a
    u at which the corrections differ).
(b) Nonlinear in the valuation curves: the dependence of A on the curves is not affine; the natural
    formalisation is that for some lambda in P2 the map u |-> A_lambda(u) is not affine (e.g. at
    lambda = delta_0, A(u) = grad V(u) = u/sqrt(1+||u||^2), bounded, vanishing at 0 and nonzero at
    w != 0, hence not affine and not linear), or that the kernel grad V is not affine.  Given the
    paper's contrast "nonlinear in the valuation curves, but affine in their population law", the
    content is "not affine"; "not linear" is the literal word and is acceptable when the witness
    has A_lambda(0) = 0 (then the two coincide), otherwise "not linear" alone is weaker (A could be
    affine with nonzero constant).  A non-additivity statement (A(u+u') != A(u)+A(u')) at a lambda
    where A is not affine is acceptable.
- Crowding correction must be the paper's A_lambda.
Comparison (verdict recorded 2026-10-19T03:21:20Z):
Comparison for spec:Dissertation.PaperSpec.A.ex_dealer_not_mean_corr (Sec5.lean:667-682).

Lean: forall E nu [SigmaFinite] [CountablyGenerated], (exists u : L2(nu;R^1), u != 0) ->
  (not exists Phi, forall Lam : P2 L2, forall u, ex55Crowd Lam.law u = Phi (int v dLam.law) u)
  /\ exists Lam : P2 L2, not exists (A : L2 ->_l[R] L2) (c : L2), forall u, ex55Crowd Lam.law u = A u + c.

Against my reading:
- (a) No function of the mean: identical to ex_dealer_mean_corr (non-factorisation through
  (barycentre, u) over all P2 laws). Matches.
- (b) Nonlinear in the valuation curves: for some Lam in P2(L2(nu)), u |-> A_Lam(u) is not affine,
  with "affine" meaning (algebraically) linear map plus constant. This is the stronger reading
  ("not affine", contrasting with "affine in the population law"), and "not algebraically affine" is
  at least as strong as "not continuous-affine". Matches (e.g. Lam = delta_0 gives gradV, bounded,
  0 at 0, nonzero at a nonzero w, so not affine).
- Setting/hypothesis: sigma-finite, countably generated, fibre L2(nu; R^1) nontrivial (equivalent to
  nu != 0 for sigma-finite nu); satisfiable (witness ex_dealer_unit_hypotheses gives a unit vector
  for dealerMarks).
- ex55Crowd is the paper's A_lambda (checked under ex_dealer_mean_corr). No junk value: the
  integrand is bounded and continuous on a separable space.
- Covers both clauses (Ex. 5.5 "not a function of E[U]" and "nonlinear in the valuation curves";
  Rem. 5.7 "nonlinear in the valuation curves"), as printed at this revision.
Representation choices: nontriviality on the fibre instead of nu != 0 (equivalent); fibre valued in
EuclideanSpace R (Fin 1); "nonlinear" formalised as "not affine" for some law.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — (1) nu != 0 is stated as "L2(nu; R^1) has a nonzero element", equivalent for sigma-finite nu.
(2) "Nonlinear in the valuation curves" is formalised as "for some Lam in P2(L2(nu)) the map
u |-> A_Lam(u) is not of the form A u + c with A linear", the natural reading given the paper's
contrast with "affine in their population law" (and stronger than "not linear"). (3) Fibre valued
in EuclideanSpace R (Fin 1) = R.
Disagreements with the author's review (shown 2026-10-19T03:26:58Z): Minor, no effect on the verdict: the author calls the hypothesis "L2(nu) != {0}" broader than the
example's nu != 0. For sigma-finite nu (assumed) the two are equivalent (nu = 0 makes L2(nu) trivial,
and nu != 0 gives a nonzero element; both halves of rem_beta1_fibre), so the proposition is exactly
the printed claim, not broader. Otherwise none.
