### A:abstract, A:ass:integ, A:ass:lip, A:ass:mono, A:conclusion, A:cor:robust, A:def:diag, A:eq:coeffint, A:eq:coefmeas, A:eq:forced, A:eq:hborel, A:eq:monomargin, A:eq:monomarginu, A:eq:mvfbsdej, A:eq:termg, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:expfunc, A:ex:fulllaw, A:intro:limin-comparison, A:intro:mvfbsdej, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:prop:strict, A:rem:beta1-dich, A:rem:cwp-class, A:rem:diag-mono, A:rem:freelaw, A:rem:generalrank, A:rem:intrinsic, A:rem:margin, A:rem:regimes, A:rem:uniq-no-integ, A:rem:wasserstein-bounds, A:sec2:hborel-derivation, A:sec3:margin-paragraph, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.Law.P2
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash d98c9fdcb43519180000000000000000 (pl-fp-v1:b7f6cc533fe4d85d5cbfdb822e1922f3b3dcd5b9370e22bb08ef9f49b2620617)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:44Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:54Z):
Reading of def:Dissertation.Law.P2.

Paper notion. P_2(H) (Sections 1-2, signatures of b, sigma, h, f, g; Def. 2.2 of the diagonal),
P_2(R^n) (terminal law argument of g), P_2(L2(nu)) (Remark 2.6, Ex. 5.4, 5.5): the set of Borel
probability measures mu on the (separable) normed / Hilbert space S with finite second moment
  int_S |x|_S^2 mu(dx) < infinity,
equipped (as the domain of the coefficients and of the law flows) with W_2 (Villani ch. 6).
For S = H the norm is the Hilbert norm |theta|_H^2 = |x|^2 + |y|^2 + |z|_F^2 + ||u||_{L2(nu)}^2.

What a faithful Lean definition must be: a type of measures mu on S (S carrying its Borel
sigma-algebra, BorelSpace) such that mu is a probability measure and its second moment is
finite, the second moment taken in the norm of S (finite second moment is independent of the
choice among equivalent norms, so the set P_2 itself does not depend on which equivalent norm is
used; but the W_2 metric put on it does). Finiteness must be genuine: e.g. lintegral of ||x||^2
(or ||x||_e^2) < top, or Integrable (fun x => ||x||^2) mu; a real-valued Bochner
"int ||x||^2 < infinity" condition would be vacuous (junk 0) and unfaithful. Equivalent
alternatives (MemLp id 2 mu, second moment about a fixed point) are fine. It must not add
conditions (e.g. compact support, finitely many atoms) nor drop the probability condition.
If S's MeasurableSpace instance is not the Borel one, the notion changes (fewer/more measures);
it must be Borel (on separable spaces Borel = product sigma-algebra for H's coordinates).
Comparison (verdict recorded 2026-10-19T03:18:44Z):
def:Dissertation.Law.P2 (Dissertation/Law/P2.lean:46-53): structure with fields law : Measure E,
IsProbabilityMeasure law, secondMoment law ≠ ⊤, secondMoment μ = ∫⁻ ofReal(‖x‖²) dμ (ENNReal).
Against the reading:
- probability measure: yes (field).
- finite second moment: genuine (ENNReal lintegral ≠ ⊤), no Bochner junk. Matches.
- sigma-algebra: the structure takes whatever MeasurableSpace instance E has; Borelness is not
  part of the structure. In the project's instantiations it is Borel: EuclideanSpace carries its
  Borel instance; L²(ν; ℝᵐ) carries the scoped lpMeasurableSpace := borel _ (System/Tuple.lean:65)
  with BorelSpace; TupleH carries the product sigma-algebra of these, equal to the Borel one for
  second-countable factors (L²(ν) is second countable for countably generated E and sigma-finite ν,
  the paper's standing assumption). Representation choice, harmless on the paper's spaces.
- norm: the norm of E. For E = TupleH (System/Tuple.lean:134) this is the maximum of the channel
  norms, not the paper's Hilbert norm; the two are equivalent (within factor 2), so the SET
  P2(TupleH) equals the paper's P_2(H). The value of W_2 does depend on the norm, but that belongs
  to w2P / P2W (and the project's separate Hilbert-norm w2H), not to P2.
- nothing added (no support or atom conditions), nothing dropped.
Verdict: faithful with representation choices (sigma-algebra by instance, norm by instance).
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the measurable structure is the type's instance rather than an
enforced Borel σ-algebra; on the paper's spaces the instances are Borel (EuclideanSpace; the scoped
lpMeasurableSpace := borel on L²(ν); products of second-countable Borel spaces), so P2 is the
paper's P₂. (2) Finiteness of the second moment is taken in the type's norm; on TupleH that is the
max-of-channels norm, equivalent to the paper's Hilbert norm, so the set of laws is unchanged.
The second moment is an ENNReal lintegral (≠ ⊤), so there is no junk.
Disagreements with the author's review (shown 2026-10-19T03:27:23Z): Only a classification difference: the earlier review says faithful; I record "faithful with
representation choices" because the structure takes the σ-algebra and the norm from the type's
instances. Both choices are harmless on the paper's spaces (Borel instances: EuclideanSpace, the
scoped lpMeasurableSpace := borel on L²(ν), products of second-countable Borel spaces; on the max-norm
TupleH, finiteness of the second moment equals the paper's Hilbert-norm one). No disagreement about
the meaning.
