### A:abstract, A:ass:G, A:ass:mono, A:conclusion, A:cor:robust, A:eq:monomargin, A:eq:monomarginu, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:lem:cont, A:lem:pert, A:rem:beta1-dich, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:margin, A:rem:regimes, A:rem:uniq-no-integ, A:sec3:margin-paragraph, A:sec4:horizon-not-contractive, A:sec5:overview, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.GU
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash af77e6209c5a6f02054d4dc4b9937972 (pl-fp-v1:7fbae66b03e0a3b98254d5a483c261dc7d3c025fb0d226e846db3292c562cc2a)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:50:56Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:41:48Z):
Reading for def:Dissertation.WellPosedness.System.GU.

Paper notion: G^T applied to the jump integrand: G^T delta U in L^2(nu;R^n), the function
e |-> G^T delta U(e) (well defined on classes, since G^T is linear/continuous), paired with delta h
in L^2(nu;R^n) by int_E <delta h(e), G^T delta U(e)> nu(de), and ||G^T delta U||^2_{L^2(nu)} in (2.6).

Faithful Lean: GU G u = the L^2(nu)-class of e |-> G^T u(e) (e.g. the composition of u with the
continuous linear map G^T : R^m -> R^n, via ContinuousLinearMap.compLp), from L^2(nu;R^m) to
L^2(nu;R^n). To check: transpose, codomain L^2(nu;R^n) with the L^2(nu) norm built from the
Euclidean norm on R^n.
Comparison (verdict recorded 2026-10-17T15:50:04Z):
Comparison for def:Dissertation.WellPosedness.System.GU: GU G nu = (GX G).compLpL 2 nu :
Lp (R^n) 2 nu ->L Lp (R^m) 2 nu, u |-> class of e |-> G u(e) (coeFn_GU).

My reading expected u |-> G^T u from L^2(nu;R^m) to L^2(nu;R^n). The Lean defines the G-action on the
jump-coefficient side (L^2(nu;R^n) -> L^2(nu;R^m)) and the paper's G^T delta U is its adjoint:
adjoint_GU proves adjoint (GU G nu) = GU G^T nu, and coeFn_adjoint_GU that it acts mark by mark as
G^T nu-a.e.; interiorPairing/dissipation use inner(delta h, adjoint GU delta U) and
||adjoint GU delta U||^2, i.e. int_E <delta h(e), G^T delta U(e)> nu(de) and ||G^T delta U||^2. The
L^2(nu) norm is built from the Euclidean norm. Well-defined on classes (compLpL). Verdict: faithful
with representation choices.
Witness: —
Verdict: faithful with representation choices — Choice: the paper writes G^T delta U in L^2(nu;R^n); the Lean defines the forward operator
GU G nu : u |-> G o u on L^2(nu;R^n) -> L^2(nu;R^m) (ContinuousLinearMap.compLpL) and recovers the
paper's G^T U as its Hilbert adjoint (adjoint_GU: adjoint (GU G nu) = GU G^T nu, acting mark by mark
nu-a.e.), which is how the pairing and dissipation use it. Harmless: same operator pair, adjoint
identity proved; L^2(nu) inner product int_E <.,.> d nu.
Disagreements with the author's review (shown 2026-10-17T15:50:12Z): No disagreement with a stated position (the author's entry shown is empty). For the record: GU is the
G-action u |-> G o u on L^2(nu;R^n), not the paper's G^T U; the paper's G^T delta U is its adjoint
(adjoint_GU, mark by mark nu-a.e.), which is what the monotonicity predicates use -- faithful with
that representation choice.
