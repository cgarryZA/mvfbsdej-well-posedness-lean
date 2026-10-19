### A:ex:concrete: Dissertation.WellPosedness.Existence.clampAffineCoeffs
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 5dc0669bb7724f483dd7fd8e2ba08292 (pl-fp-v1:460c847baaabd522780f5ab41bda70ccb49e02a682e2b7bf1ef8c601466c03ea)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:07Z):
Reading of def clampAffineCoeffs (used by claim ex:concrete).
Paper notion: Example 5.1(i) last paragraph: "The baseline also realises the example of Proposition 3.8:
replacing its drift -beta1 y by (eq:bmean) leaves (mono) intact with constants (beta1-eps, beta2)".
So the coefficient system must be, with n=m=d=1, parameters beta1, beta2 (>0), eps (0<eps<beta1),
sigma_c in R, h_c in L2(nu):
  b(t,theta,mu) = -beta1*y + eps*g0(y - m_Y(mu)),  g0(r)=max{-1,min{1,r}},  m_Y(mu)=int y dmu;
  sigma(t,theta,mu) = sigma_c - beta1*z  (1x1 matrix);
  h(t,theta,mu) = h_c - beta1*u in L2(nu;R) (pointwise h(e)=h_c(e)-beta1 u(e));
  f(t,theta,mu) = beta2*x;
  g(x,rho) = x.
Deterministic, time-independent. A faithful Lean def is exactly this system (in whatever coefficient record
the library uses), with m_Y a Bochner mean on P_2(H) and g0 the clamp to [-1,1]. Any extra or missing term,
wrong sign, or clamp to another interval would be unfaithful. Parameter constraints (beta's>0, eps<beta1) may
live in the propositions rather than the def.
Comparison (verdict recorded 2026-10-19T03:29:17Z):
Comparison, def clampAffineCoeffs (ClampAffine.lean:44-49) vs reading.
{ affineCoeffs β1 β2 σc hc with b := clampDrift β1 ε }: affineCoeffs gives b=-(β1•y), σ=σc-β1•z,
h=hc-β1•u (in L2(ν;R^1)), f=β2•x, g x _ = x; the drift is replaced by clampDrift β1 ε =
-(β1•y)+ε•clampVec(y - meanY μ). Exactly the reading: Example 5.1(i) with drift (eq:bmean).
Differences: d is a free parameter and σc ∈ R^{1×d} (paper Ex 5.1(i) has d=1 and σc ∈ R; Prop 3.8 has
d≥1) -- generalisation of the parameter space, instantiation d=1. Time ranges over ℝ, coefficients
ignore it. Parameter constraints are not in the def (fine).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) n=m=1 fixed, d left free with σc ∈ EuclideanSpace ℝ (Fin 1 × Fin d)
(the paper's d=1, σc ∈ R, is d=1); (2) h valued in Lp (EuclideanSpace ℝ (Fin 1)) 2 ν, h = hc - β1•u
as an L2 class (the paper's h(e) = hc(e) - β1 u(e)); (3) time argument over ℝ and ignored; (4) the
parameter constraints β1,β2>0, 0<ε<β1 live in the statements, not the def. None changes the meaning.
Disagreements with the author's review (shown 2026-10-19T03:29:27Z): No disagreement on substance. Label only: the review records "broader" (free diffusion dimension d);
I record "faithful with representation choices", treating the free parameter d of a definition (the
printed system being the instance d = 1, σc ∈ R^{1×1}) as a representation choice. Same instantiation.
