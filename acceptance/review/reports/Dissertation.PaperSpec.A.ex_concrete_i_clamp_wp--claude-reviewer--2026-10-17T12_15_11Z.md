### A:ex:concrete: Dissertation.PaperSpec.A.ex_concrete_i_clamp_wp
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba14bccae170a8d514d (pl-fp-v1:a853e0968b88de6447c1f219dd000ae8420dc63f558b9e3eb3c36970debbbad3)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:15:11Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:14:15Z):
# Reading: ex_concrete_i_clamp_wp, clause "(i) with the drift (3.6): well-posedness"

Paper: replacing the drift by (3.6) "leaves (2.7) intact with constants (beta1 - eps, beta2), so
Theorem 3.5 continues to apply." Theorem 3.5: for every T > 0, under Ass. 2.2-2.5 the system
(1.1) admits a solution Theta = (X,Y,Z,U) in S (= S^2 x S^2 x H^2_W x H^2_N), unique by Thm 3.3
(any two solutions in H_weak with the same initial condition coincide), and depending
continuously on coefficients and data in the sense of (3.1).

Faithful formal statement:
- Setting/data exactly as in ex_concrete_i_clamp: standing basis, n = m = d = 1, any sigma-finite
  nu, T > 0, beta1, beta2 > 0, 0 < eps < beta1, sigma_c in R, h_c in L^2(nu), xi0 in L^2(F_0);
  coefficients b = -beta1 y + eps g0(y - m_Y(mu)), sigma = sigma_c - beta1 z,
  h = h_c - beta1 u, f = beta2 x, g = x.
- Conclusion: existence of a solution of (1.1) (with mu_t = Law(Theta_t), h at the predictable
  tuple, identities a.s. for every t, Theta in S, with initial datum xi0), and uniqueness
  (every other solution -- in S, or in the H_weak class of Thm 3.3 -- coincides, up to the
  identification of S). Continuous dependence (3.1) is part of Thm 3.5's statement; a
  well-posedness clause that omits it is narrower than "Theorem 3.5 continues to apply" in full,
  though "well-posedness" in the paper's usage (Thm 3.5 title, "WP(lambda)" = unique solution)
  is existence + uniqueness. I would accept existence + uniqueness, and note the omission.
- The solution notion must be the paper's (the real system with the law of the solution
  itself, not a frozen or linearised version).
Comparison (verdict recorded 2026-10-17T12:15:03Z):
# Comparison: ex_concrete_i_clamp_wp

Lean (Sec5.lean:201): same setting/data as ex_concrete_i_clamp (every basis d = 1, any
sigma-finite nu, G0 independent, T > 0, beta1, beta2 > 0, 0 < eps < beta1, sigma_c, h_c, xi0 in
L^2(F_0)); conclusion: (exists X Y Z U, Solution ... (clampAffineCoeffs ...) xi0 X Y Z U) and
for any two Solutions: X's indistinguishable on [0,T], Y's indistinguishable on [0,T], energy of
Z1 - Z2 = 0, marked energy of U1 - U2 = 0.

Solution (PaperSpec/A/Setting.lean) is the paper's notion: Theta in S over the §2 filtration
enlJoint, cadlag X, Y (right-continuous everywhere on [0,T), left limits on (0,T]), adapted with
E sup < infinity, Z, U predictable with finite energy, both identities of (1.1) a.s. for every
t, h at the predictable tuple (left limits, mu^-) through a representative gamma, laws of the
solution itself. (Its detailed faithfulness is a definition review of its own.)

Against my reading:
- Setting and data: identical to ex_concrete_i_clamp, no added hypotheses: yes.
- Existence of a solution in S: yes.
- Uniqueness: equality in S (indistinguishable cadlag components; Z, U equal dt dP (nu)-a.e.),
  which is the identification of §3: yes. It is uniqueness among solutions in S, not the
  H_weak uniqueness of Thm 3.3; the paper's own definition of well-posedness (WP(lambda): "has a
  unique solution in S") is exactly this.
- Continuous dependence (3.1), mentioned in Thm 3.5's statement, is not restated; it is
  Theorem 3.1 applied to this system, whose hypotheses are ex_concrete_i_clamp. Harmless for a
  "well-posedness" clause.
- Non-vacuity: hypotheses are only the data; witness ex_concrete_hypotheses (nu = dirac 0, d = 1,
  G0 = bot, xi0 = 0, beta1 = beta2 = 1, eps = 1/2).

Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. "Theorem 3.5 continues to apply" is rendered as its well-posedness conclusion in the paper's
   own sense (WP: a unique solution in S): existence of a Solution and equality in S of any two
   Solutions (indistinguishable X, Y; Z, U equal dt dP (nu)-a.e. via zero energies).
2. Uniqueness is among solutions in S; the stronger H_weak uniqueness of Theorem 3.3 is not
   restated here.
3. The continuous dependence in the sense of (3.1) named in Theorem 3.5 is not restated; it is
   Theorem 3.1 applied to this system, whose hypotheses are the companion clause
   ex_concrete_i_clamp.
Disagreements with the author's review (shown 2026-10-17T12:15:03Z): The displayed entry is empty; the author's review is the combined one shown under
ex_concrete_i_clamp ("Theorem 3.5 continues to apply" read as its hypotheses and its conclusion;
verdict faithful). One difference: that review calls the conclusion "the conclusion of
Theorem 3.5", but the proposition states only existence and uniqueness in S (equality in S of
any two Solutions); Theorem 3.5 also asserts continuous dependence in the sense of (3.1) and
uniqueness via Theorem 3.3 in the larger class H_weak. I consider these omissions harmless
(the paper's own WP notion is "a unique solution in S", and (3.1) is Theorem 3.1 applied to this
system), hence "faithful with representation choices" rather than "faithful"; but the review
should say that the continuous-dependence part is not restated.
