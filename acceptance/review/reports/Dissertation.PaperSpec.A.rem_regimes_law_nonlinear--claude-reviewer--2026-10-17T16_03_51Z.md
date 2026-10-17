### A:rem:regimes: Dissertation.PaperSpec.A.rem_regimes_law_nonlinear
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba1ce2bdab6776d4961 (pl-fp-v1:9b733e15fdc04455a3b94b50e2f4864a0fb86032436f400c176f30f3a6d23c41)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:51Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:46Z):
Reading of spec rem_regimes_law_nonlinear (Remark 5.7: "Example 5.5 shows that a genuinely
nonlinear U-law interaction can have arbitrary strength when its geometry is itself
monotone"), the clause "the dealer interaction is a genuinely nonlinear U-law interaction, as
printed".

The interaction: lambda |-> A_lambda(u) = int gradV(u - v) lambda(dv) on P_2(L^2(nu)).
"genuinely nonlinear U-law interaction": in the paper's own vocabulary (Section 5 overview:
"Example 5.4 carries the law dependence beyond those subclasses [Brownian, expectation
functional], to genuinely nonlinear functionals"; Example 5.4: "All three lie beyond the
expectation and two-point-kernel jump-integrand interactions of the preceding examples")
"genuinely nonlinear law dependence" means: the dependence on the law is not of expectation
(two-point-kernel) type int phi(theta,theta') mu(dtheta'), equivalently, not affine in the
law under mixtures. Read this way the printed sentence asserts: the map lambda |-> A_lambda(u)
is NOT affine in lambda (for some u: A_{t l1 + (1-t) l2}(u) != t A_{l1}(u) + (1-t) A_{l2}(u)),
i.e. not an expectation functional in the law. This is false for every nu: A_lambda(u) is
an integral of the kernel gradV(u - v) against lambda, hence affine (indeed of the
two-point-kernel class of Example 5.3) - and the refutation does not even need nu = 0.

Alternative reading (weaker): "genuinely nonlinear" = beyond the mean (not a function of
E[U]) and nonlinear in u. That reading is true when L^2(nu) != 0 (Example 5.5 "Beyond the
mean"). I take the primary reading (nonlinear = not affine/expectation-type in the law) as the
printed meaning of "genuinely nonlinear U-law interaction", since "U-law interaction" names the
dependence on the law and the paper's Section 5 uses "genuinely nonlinear" for
non-expectation law functionals.

Faithful formal printed proposition: for every sigma-finite nu (countably generated E) [or
the specific dealer nu], the dealer law interaction lambda |-> A_lambda(u) is not affine /
not an expectation functional in lambda. It must be no stronger than that. A refutation that
proves the dealer interaction is affine in the law (for all nu, or for an instance the
setting covers) is valid. If instead the proposition encodes "nonlinear" as a property that
the dealer interaction does have under the alternative reading, the refutation could only work
through nu = 0, which would make the reading questionable; check which.
Comparison (verdict recorded 2026-10-17T16:01:28Z):
Comparison, rem_regimes_law_nonlinear (Sec5Regimes.lean:33-43), printed reading, refuted.
Lean: for every sigma-finite nu on countably generated E, exist Lambda_1, Lambda_2 in P2(L^2(nu)),
s in [0,1], u with A_{s L1 + (1-s) L2}(u) != s A_{L1}(u) + (1-s) A_{L2}(u): "not affine in the
law" - my primary reading of "genuinely nonlinear U-law interaction" (nonlinear as a function of
the U-law; the paper's Section 5 uses "nonlinear law dependence/functionals" for laws beyond the
expectation and two-point-kernel class, and A_lambda(u) = int gradV(u-v) lambda(dv) is of that
class). The mixture ofReal s . L1 + ofReal(1-s) . L2 is the convex combination of laws.
Not stronger than printed under that reading (existence of one failure of affinity).
Alternative reading (I recorded it): "genuinely nonlinear" = not a function of E[U] / beyond the
linear-in-the-mean interactions of the cited models; under it the printed claim is true for
L^2(nu) != 0 and is the content of the corrected clause rem_regimes_corr (second conjunct). The
paper's own vocabulary (Example 5.4 "nonlinear law functionals ... beyond the expectation and
two-point-kernel interactions") favours the Lean's reading; I keep it as the faithful printed
reading, noting the ambiguity.
Refutation rem_regimes_law_nonlinear_false: nu = delta_0 on R (nonzero, finite, sigma-finite,
countably generated), and ex_dealer_affine gives affinity in the law for every nu. The
counterexample is a genuine instance of the setting (not the degenerate nu = 0), so the
refutation holds at intended instances too. Valid.
Verdict: faithful (refutation valid).
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T16:01:35Z): none
