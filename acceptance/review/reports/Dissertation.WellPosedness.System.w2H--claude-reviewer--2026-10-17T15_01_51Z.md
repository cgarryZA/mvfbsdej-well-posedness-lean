### A:ass:lip, A:cor:robust, A:eq:coeffint, A:ex:brownian, A:ex:concrete, A:ex:expfunc, A:lem:cont, A:lem:pert, A:lem:small, A:prop:strict, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:remark-2.6, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.w2H
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 9b325b0ab6c710a41121705bb1470821 (pl-fp-v1:97fb784ac386bf2c3080aa25c51579c81a3172ac7ded7542af854ae1bc7c52e7)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:51Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:24Z):
Reading for def:Dissertation.WellPosedness.System.w2H (written before seeing any Lean).

Paper notion. W_2 on P_2(H), H = R^n x R^m x R^{m x d} x L^2(nu;R^m) with
|theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||_{L^2(nu)}^2: the quadratic Wasserstein distance of
Villani Def 6.1, W_2(mu,mu')^2 = inf over couplings pi of (mu,mu') (probability measures on
H x H with marginals mu, mu') of \int |theta - theta'|_H^2 dpi. Remark 2.6 uses that every
synchronous pair (Theta,Theta') gives a coupling, so W_2^2 <= E|Theta-Theta'|_H^2, and that an
optimal coupling exists (so the infimum is attained) in the reverse bounds.

A faithful Lean definition must:
- take the infimum over ALL couplings (measures on H x H with the given marginals), not only over
  couplings realised by random variables on the standing basis (which would coincide only on a
  rich enough Omega; Remark 2.9 discusses this for F_t, t > 0, but the paper's W_2 is the
  intrinsic one);
- use the cost |theta - theta'|_H^2 with the Hilbert (sum-of-squares) norm of H — NOT Lean's
  default product sup-norm and not the sup-norm on Fin n -> R or matrices; a different equivalent
  norm gives a different W_2 and changes Lipschitz constants in Ass 2.3 / Prop 3.8 / Ex 5.1;
- be the square root of the squared cost (W_2, not W_2^2), compared in the paper with
  L(|delta X| + ... + W_2(mu,mu'));
- edge cases: for laws outside P_2 the paper does not define W_2; any junk value (e.g. toReal of
  infinity = 0) is harmless only if every use is at P_2 laws (diagonal laws of L^2 tuples,
  delta_0); if the value lives in R>=0-infinity, comparisons must be read accordingly.
Comparison (verdict recorded 2026-10-17T12:39:11Z):
Comparison for System.w2H.
Lean: w2H μ μ' := w2 (μ.law.map toL2) (μ'.law.map toL2), where (Dissertation.Law)
w2 μ ν = √((w2sq μ ν).toReal), w2sq μ ν = ⨅ γ (IsCoupling μ ν γ), ∫⁻ ofReal ‖p.1 - p.2‖² ∂γ,
IsCoupling μ ν γ := γ.fst = μ ∧ γ.snd = ν.
- Infimum over ALL couplings: every measure on the product with the two marginals, not only
  couplings realised on the standing Ω. Matches Villani Def 6.1.
- Cost: ‖p.1 − p.2‖² in TupleL2, the nested L² product with ‖toL2 θ‖² = channelSq θ. With the
  TupleH channels this is |θ−θ'|_H² for the paper's Hilbert norm, NOT the max norm of the Lean
  product (that version is w2P). Couplings of the image laws correspond to couplings of μ, μ'
  under toL2 × toL2, a measurable bijection with measurable inverse ofL2. So w2H is the paper's W₂
  on P₂(H). Matches.
- W₂ (square root), not W₂². Matches.
- Real-valued via toReal. An infinite infimum would give junk 0. For P2 laws the image laws have
  finite second moment in the Hilbert norm (factor 4), so w2sq is finite (w2sq_map_toL2_ne_top,
  in the second-countable setting of the paper). The junk is not reached on P2 in the paper's
  setting.
- The σ-algebras on HX..HUY are instance parameters. For TupleH they are Borel (EuclideanSpace;
  Lp via the scoped borel instance), and the product σ-algebra equals the Borel σ-algebra when
  L²(ν) is second countable (ν σ-finite, E countably generated).
- Separation of w2 is not established in the repository. That concerns properties, not meaning.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices. (1) W₂ for the Hilbert norm is computed by pushing both laws forward along
toL2 into the nested-L² copy of H and taking the generic w2 there. The bijection toL2 × toL2
identifies the couplings, so the value is the paper's W₂(μ,μ') for |·|_H. (2) The value is
real-valued: √(toReal of an ℝ≥0∞ infimum over all couplings, as measures on the product with the
prescribed marginals). For laws in P2 the infimum is finite in the paper's setting, where L²(ν)
is second countable, so the toReal junk (∞ ↦ 0) is not reached. (3) Couplings live on the
product σ-algebra of the channel σ-algebras. For TupleH these are Borel, and the product
σ-algebra is the Borel σ-algebra of H under the paper's separability assumptions.
Disagreements with the author's review (shown 2026-10-17T15:01:22Z): None on the substance: it is the paper's W₂ for the Hilbert norm. The author's entry does not
record the edge cases I checked: the real value is √(toReal ·), which is finite on P2 in the
paper's second-countable setting, and couplings live on the product σ-algebra, which is Borel
there.
