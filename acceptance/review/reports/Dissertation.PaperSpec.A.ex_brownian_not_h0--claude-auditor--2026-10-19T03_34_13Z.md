### A:ex:brownian: Dissertation.PaperSpec.A.ex_brownian_not_h0
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba13fa0ef4acc9fb310 (pl-fp-v1:f3ca509922faf1c36c26aae5e5be820d6e132dec8b45c2f21ef3ab25469904e0)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:13Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:14Z):
Reading of spec ex_brownian_not_h0: Example 5.2, "Merely setting h = 0 on a Brownian-Poisson basis
is not a reduction, since the backward Poisson integral and its integrand U persist in the
representation."

Paper claim. On a Brownian-Poisson basis (sec. 2) with a genuine Poisson channel (nu != 0), taking
h = 0 does not reduce the problem to the Brownian one: the representation of square-integrable
martingales of the Brownian-Poisson filtration still needs the Poisson integral, so the backward
equation still carries int int U dNtilde with a non-trivial integrand U (the solution space keeps
its U-coordinate). The mathematical core: when nu != 0 there is a square-integrable martingale of
the Brownian-Poisson filtration that is NOT of the form M_0 + int Z dW (its representing U is not
dt dP nu-a.e. zero); e.g. M_t = Ntilde([0,t] x A) with 0 < nu(A) < infinity. Equivalently, the
Brownian PRP fails on the Brownian-Poisson filtration.
A faithful formal statement must contain: the sec. 2 basis with nu != 0 (necessary: at nu = 0 the
claim is false, so the hypothesis must be present, implicitly or explicitly); conclusion: existence
of a square-integrable martingale (possibly the backward component of a solution with h = 0, which
is a stronger and more specific form) whose representation has U != 0, or non-representability by
a Brownian integral alone. A statement that only says "L^2(nu) != {0}" or "a U-coordinate exists
in the type" would be too weak (not the claim). Hypotheses must be satisfiable (a basis with
nu != 0 exists).
Comparison (verdict recorded 2026-10-19T03:32:34Z):
Comparison, ex_brownian_not_h0 (Sec5Brownian.lean:40-47).

- Setting: the sec. 2 basis (Levy driver with sigma-finite nu on countably generated E, G0
  independent of the driver filtration), with 0 < d and nu != 0 (the hypothesis my reading said must
  be present: at nu = 0 the claim is false), every T > 0.
- Conclusion: there is a martingale M of enlJoint (the sec. 2 filtration) with M_t in L^2 for all t
  such that no Z gives RepresentsMart ... M Z 0, i.e. M has no representation
  M_t = M_0 + int Z dW + int 0 dNtilde on [0,T]. With the sec. 2 PRP (uniqueness), every
  representation of M has U != 0: "the backward Poisson integral and its integrand U persist in the
  representation" - the mathematical core I identified (the Brownian PRP fails on the
  Brownian-Poisson filtration). The zero integrand meets all the fields of RepresentsMart, so the
  negation is not vacuous for a technical reason.
- "Setting h = 0 is not a reduction" itself is the paper's interpretive conclusion; the reason
  given is what is formalised. Not the too-weak "L^2(nu) != {0}".
- Witness: ex_brownian_not_h0_hypotheses (nu = delta_0 on R, d = 1, G0 = bot).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:32:45Z): none
