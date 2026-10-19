### A:abstract, A:ass:lip, A:conclusion, A:cor:robust, A:eq:coeffint, A:eq:coefmeas, A:eq:hborel, A:eq:termg, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:expfunc, A:ex:fulllaw, A:intro:limin-comparison, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:prop:strict, A:rem:beta1-dich, A:rem:cwp-class, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:regimes, A:rem:uniq-no-integ, A:rem:wasserstein-bounds, A:sec2:hborel-derivation, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.Law.transportCostSq
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 26527e1b01e0a835bf6cd2c0e3b72557 (pl-fp-v1:47089ea2e781acd1a5b9e8c2a0b76ab4ba0f6a97de4a9aa23cd127212b4701b8)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:45Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:55Z):
Reading of def:Dissertation.Law.transportCostSq.

Paper notion. The quadratic transport cost of a coupling pi of (mu, mu'): int_{S x S}
|x - y|_S^2 pi(dx,dy) (Villani Def. 6.1 with cost c = d^2; Remark 2.6 "synchronous transport
cost" E|Theta - Theta'|^2 = cost of Law(Theta,Theta'); Ex. 5.5 int ||v - v'||^2 d gamma).

Faithful Lean definition: transportCostSq pi := int (or lintegral) of ||x - y||^2 (equivalently
dist x y ^ 2) over pi on S x S, with the paper's norm on S (Hilbert norm for H). A real-valued
Bochner integral has junk value 0 when ||x-y||^2 is not pi-integrable; this is harmless where pi
is a coupling of two P_2 measures (then ||x-y||^2 <= 2||x||^2 + 2||y||^2 is integrable), but
would make an infimum over couplings wrong if couplings with non-integrable cost were admitted
(e.g. marginals outside P_2). An ENNReal lintegral version has no junk. The cost must be the
squared distance (not the distance, not a capped distance).
Comparison (verdict recorded 2026-10-19T03:18:45Z):
def:Dissertation.Law.transportCostSq (Dissertation/Law/Wasserstein.lean:104-106):
  transportCostSq γ := ∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂γ   (ℝ≥0∞).
Against the reading: the quadratic cost ∫|x−y|² dγ, ENNReal-valued (no junk for non-integrable
costs; infinite costs are ⊤ and do not lower an infimum). Squared distance, not distance. The
integrand is measurable for the product sigma-algebra on second-countable Borel E
(measurable_normSq_sub); otherwise the lintegral is still the lower integral, a corner outside the
paper's spaces. Norm = E's norm (see P2W for the TupleH remark). Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:27:24Z): none
