### A:ex:expfunc: Dissertation.PaperSpec.A.ex_expfunc_jump
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1e622a1683bfc9f0d (pl-fp-v1:b312119d7e390edefb2eb4847df26a49c6234afd6007d7aad19f2308fbfea6fa)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:22Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:08Z):
Reading of spec ex_expfunc_jump, clause "the jump coefficient through the Nemytskii map" (Example 5.3).
Setting: H = R^n x R^m x R^{m x d} x L2(nu;R^m), nu sigma-finite (arbitrary activity in the hypotheses as
stated; the "natural quantitative hypotheses" are imposed directly on H_t), T>0; a two-point kernel
hbar: [0,T] x (R^n x R^m x R^{m x d} x R^m) x (R^n x R^m x R^{m x d} x R^m) x E -> R^n (measurable).
Nemytskii map [H_t(theta,theta')](e) := hbar(t,x,y,z,u(e),x',y',z',u'(e),e) for nu-a.e. e.
Claims:
 (a) H_t is well defined on equivalence classes (changing u,u' on nu-null sets changes H_t(theta,theta') only on
     a nu-null set);
 (b) under the hypotheses: H jointly Borel; ||H_t(t1,t1') - H_t(t2,t2')||_{L2(nu)} <= C(|t1-t2|_H + |t1'-t2'|_H);
     int_0^T ||H_t(0,0)||^2 dt < inf -- H_t is Lipschitz into L2(nu;R^n) and (2.10) (lipfun with K=L2(nu;R^n))
     applies to h(t,theta,mu) := int_H H_t(theta,theta') mu(dtheta') (Bochner integral in L2(nu;R^n)):
     ||h(t,theta,mu) - h(t,theta,mu')|| <= C W_2(mu,mu') for all mu, mu' in P_2(H) (constant C = Lip of
     H_t(theta,.)), giving the law-dependence component of Assumption 2.3 for h; presumably also the
     theta-Lipschitz part ||h(t,theta1,mu) - h(t,theta2,mu)|| <= C|theta1-theta2| and origin integrability of
     h(.,0,delta_0)=H_.(0,0) (supplying Assumption 2.2 for h) -- the paragraph says "so that ... (2.10)
     applies".
Faithful formal: for all hbar and C satisfying those hypotheses, all t, theta, mu, mu' in P_2(H):
||h(t,theta,mu)-h(t,theta,mu')||_{L2} <= C W_2(mu,mu'); with h defined via the Nemytskii map of hbar (not an
arbitrary Lipschitz H). Also acceptable: the combined bound with |theta - theta'|. The constant C is the
hypothesis' C (chosen before theta, mu). Narrower if it requires finite nu or bounded hbar. Witness: e.g.
hbar = 0 or hbar(...,u(e),...,u'(e),e) = u(e)-u'(e) type (a genuine instance from Li-Min).
Comparison (verdict recorded 2026-10-19T03:29:18Z):
Comparison, ex_expfunc_jump (Sec5.lean:401-430) vs reading.
- Setting: ν σ-finite, E countably generated, n,m,d; a kernel hbar(t, block, block', e) on
  B = R^n × R^m × R^{m×d} × R^m and the mark. Matches.
- (a) for all t, θ, θ' and all functions v =ᵐ θ.u, v' =ᵐ θ'.u, the Nemytskii integrand built from v, v'
  agrees ν-a.e. with the one built from the coercions of θ.u, θ'.u: well definedness on equivalence
  classes. Matches.
- (b) for every L²(ν;R^n)-valued H representing the Nemytskii map (H t θ θ' =ᵐ hbar(..u(e)..u'(e)..e))
  and C ≥ 0 with ‖H t θ1 θ1' - H t θ2 θ2'‖ ≤ C(|θ1-θ2|_H + |θ1'-θ2'|_H) (Hilbert norms via toL2), for all
  t, θ, μ, μ' ∈ P2(H): ‖∫ H t θ θ' dμ - ∫ H t θ θ' dμ'‖ ≤ C w2H(μ,μ'). This is "(2.10) applies, with K =
  L²(ν;R^n), to h(t,θ,μ) := ∫ H_t(θ,θ') μ(dθ')", the law-dependence component of Assumption 2.3 for h.
  The Bochner integrals are non-junk: H t θ · is Lipschitz, hence continuous, into a separable space and of
  linear growth, so integrable under μ ∈ P2.
- Hypotheses dropped versus the paper: joint Borel measurability of H and ∫_0^T ‖H_t(0,0)‖² dt < ∞ (not
  needed for the law-Lipschitz bound; they serve Assumptions 2.2 and the measurability, which the paper
  says are "imposed on the full coefficient system"). The θ-Lipschitz and origin parts are not concluded,
  consistent with the paragraph, which claims only that (2.10) applies.
- Witness ex_expfunc_jump_hypotheses: an instance of hbar, H, C at ν = δ_0.
Verdict: broader.
Witness: —
Verdict: broader — Broader: the hypotheses "H jointly Borel" and "∫_0^T ‖H_t(0,0)‖² dt < ∞" are dropped (only the
Lipschitz bound is assumed), and t ranges over ℝ. The printed clause is the instance where H_t is the
paper's jointly Borel, origin-square-integrable Nemytskii map with Lipschitz constant C, t ∈ [0,T], and
h(t,θ,μ) := ∫ H_t(θ,θ') μ(dθ'); the conclusion is (2.10) with K = L²(ν;R^n) and Lip ≤ C.
Disagreements with the author's review (shown 2026-10-19T03:29:29Z): none
