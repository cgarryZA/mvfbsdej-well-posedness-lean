### A:abstract, A:conclusion, A:cor:robust, A:eq:coefmeas, A:eq:hborel, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:beta1-dich, A:rem:cwp-class, A:rem:diag-mono, A:rem:generalrank, A:rem:intrinsic, A:rem:regimes, A:rem:uniq-no-integ, A:sec2:hborel-derivation, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.Law.P2W
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash d98c9fdcb4351918cf1dd08443113a27 (pl-fp-v1:bddc37044d5aa2fc893cca6755c6e7f05018710f596bff6cee236e7465091990)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:45Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:54Z):
Reading of def:Dissertation.Law.P2W.

Paper notion. The metric space (P_2(S), W_2) of probability measures with finite second moment
under the quadratic Wasserstein distance W_2 (Villani Def. 6.1 and ch. 6), for S = H, R^n,
L2(nu). Used as: the measure argument space of b, sigma, h, f (P_2(H)) and g (P_2(R^n)), with
"Lipschitz in W_2" hypotheses (Assumption 2.3) and "jointly Borel measurable in their arguments"
(the Borel sigma-algebra of the W_2 topology), and as the codomain of Borel law flows
(Lemma A.1). (P_2(S), W_2) is a (genuine) metric space; on a Polish S it is Polish.

Faithful Lean definition: a type whose elements are exactly the elements of P_2(S) (e.g. a type
synonym / structure wrapping P2 S) and whose metric is dist mu nu = W_2(mu, nu) with W_2 the
paper's quadratic Wasserstein distance (inf over couplings of the expected squared distance, then
square root) computed with the paper's norm on S (for H, the Hilbert norm). The topology,
uniformity and Borel sigma-algebra used on it must be those induced by this distance. Having only
a PseudoMetricSpace (not MetricSpace) structure is harmless provided dist is W_2 itself
(W_2 separates points anyway; the Borel sigma-algebra of a pseudometric is the same notion).
Comparison (verdict recorded 2026-10-19T03:18:45Z):
def:Dissertation.Law.P2W (Dissertation/Law/P2Metric.lean:41-42): def P2W : Type _ := P2 E, a
type synonym carrying (same file) the PseudoMetricSpace instance with dist := w2P (on complete,
second-countable Borel E) and the MeasurableSpace instance borel (P2W E) with BorelSpace.
Against the reading: elements are exactly those of P_2(E); metric = w2P = the quadratic
Wasserstein distance (inf over couplings of ∫⁻‖x−y‖², square root) for the norm of E; topology,
uniformity and Borel sigma-algebra are those induced by dist (default fields, instMeasurableSpace :=
borel). Representation choices: (1) only a pseudometric structure (separation not established);
harmless since dist is W_2 itself and the Borel sigma-algebra of the pseudometric topology is the
same notion; (2) the distance is computed in E's norm: for E = TupleH (max of channels) it differs
from the paper's Hilbert-norm W_2 by at most a factor 2 (same topology, same Borel sets); the
project provides a separate Hilbert-norm space (System.P2WH / w2H) for the paper's W_2 on H, which
is outside this unit. For E = ℝⁿ or L²(ν) the norm is the paper's. Verdict: faithful with
representation choices.
Witness: —
Verdict: faithful with representation choices — (1) PseudoMetricSpace rather than MetricSpace: the distance is exactly w2P (W₂), so topology,
uniformity and the Borel σ-algebra (instMeasurableSpace := borel) are the paper's; only the
separation axiom is not recorded, which nothing in the paper's use of (P₂, W₂) needs. (2) W₂ is
taken in the norm of the underlying type: on ℝⁿ and L²(ν) that is the paper's norm; on the
max-norm TupleH it is within a factor 2 of the paper's (same topology and Borel sets), and the
project's separate Hilbert-norm space P2WH carries the paper's W₂ on H.
Disagreements with the author's review (shown 2026-10-19T03:27:23Z): Only a classification difference: the earlier review says faithful; I record "faithful with
representation choices" for two points worth keeping on record. (1) Only a PseudoMetricSpace is
provided: separation is not established, which is harmless because dist is W₂ itself. (2) W₂ is
taken in the norm of the underlying type, so on TupleH (the max of the channel norms) it differs
from the paper's Hilbert-norm W₂ by up to a factor 2 (same topology and Borel sets); the paper's
W₂ on H is the project's separate P2WH/w2H. Neither point changes the meaning of P2W as the
generic Wasserstein space of a normed type.
