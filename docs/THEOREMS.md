# Statement-by-statement correspondence

Each “Checked” entry refers to the precise real-number, recursion, or combinatorial statement listed below. It does not certify every sentence of the manuscript or reprove external optimization certificates.

[Scope and trust boundary](VERIFICATION.md) · [Machine-readable coverage](../audit/coverage.json) · [CSV table](THEOREMS.csv)

| Paper result | Description | Status | Proof declaration(s) and source |
|---|---|---|---|
| Proposition 2.5 | Treewise conjugacy and Bellman recursion | Checked (scalar interface) | [`GD.proposition_2_5`](../GD/Conjugacy.lean), [`GD.primitive_tree_optimum`](../GD/Conjugacy.lean), [`GD.s_tree_optimum`](../GD/Conjugacy.lean), [`GD.Tree.primitive_conjugacy`](../GD/Conjugacy.lean), [`GD.Tree.s_conjugacy`](../GD/Conjugacy.lean), [`GD.join_step_conjugacy`](../GD/Conjugacy.lean), [`GD.objective_reciprocal`](../GD/Objective.lean) |
| Proposition 2.6 | Kernel properties | Checked | [`GD.rho_gt_two`](../GD/Kernel.lean), [`GD.rho_sq`](../GD/Kernel.lean), [`GD.K_continuous`](../GD/Kernel.lean), [`GD.K_symm`](../GD/Kernel.lean), [`GD.K_hom`](../GD/Kernel.lean), [`GD.K_zero_left`](../GD/Kernel.lean), [`GD.K_diag`](../GD/Kernel.lean), [`GD.K_gt_sum`](../GD/Kernel.lean), [`GD.K_strict_left`](../GD/Kernel.lean), [`GD.K_strict_right`](../GD/Kernel.lean), [`GD.K_ratio_bounds`](../GD/KernelRatios.lean) |
| Theorem 3.1 | Sharp four-point rearrangement | Checked | [`GD.theorem_3_1`](../GD/Rearrangement.lean) |
| Lemma 3.2 | Sign of conjugate polynomial | Checked | [`GD.lemma_3_2`](../GD/Algebra.lean) |
| Lemma 3.3 | Pairing-difference identity | Checked | [`GD.lemma_3_3_first`](../GD/Algebra.lean), [`GD.lemma_3_3_second`](../GD/Algebra.lean) |
| Lemma 3.4 | Quartic evaluation | Checked | [`GD.lemma_3_4`](../GD/Algebra.lean) |
| Theorem 4.1 | Abstract balanced-composition principle | Checked | [`GD.theorem_4_1`](../GD/Balanced.lean) |
| Corollary 4.2 | Balanced optimality and supercomposition | Checked | [`GD.corollary_4_2`](../GD/Balanced.lean) |
| Lemma 4.3 | All supercomposition equality cases | Checked | [`GD.lemma_4_3`](../GD/Equality.lean) |
| Corollary 4.4 | Complete maximizing root-split set | Checked | [`GD.corollary_4_4`](../GD/RootSplits.lean) |
| Theorem 4.5 | Resolution of Zhang-Jiang conjecture | Checked | [`GD.theorem_4_5_balanced`](../GD/Conjugacy.lean), [`GD.theorem_4_5_ties`](../GD/Conjugacy.lean), [`GD.primitive_tree_optimum`](../GD/Conjugacy.lean), [`GD.proposition_2_5`](../GD/Conjugacy.lean) |
| Corollary 4.6 | All optimal composition trees | Checked | [`GD.corollary_4_6`](../GD/TreesAlgorithm.lean), [`GD.optimal_tree_iff_patterns`](../GD/RootSplits.lean) |
| Lemma 5.1 | Silver power inequality | Checked | [`GD.lemma_5_1`](../GD/SilverPower.lean) |
| Proposition 5.2 | Sharp power envelope; dyadic equality | Checked | [`GD.proposition_5_2`](../GD/PowerEnvelope.lean) |
| Lemma 5.3 | Adjacent-ratio contraction | Checked | [`GD.lemma_5_3`](../GD/AdjacentRatios.lean) |
| Theorem 5.4 | Canonical bi-Lipschitz interpolation | Checked | [`GD.theorem_5_4`](../GD/InterpolationRegularity.lean) |
| Theorem 5.5 | Exact symmetric phase and uniqueness | Checked | [`GD.theorem_5_5`](../GD/PhaseTheorem.lean) |
| Corollary 5.7 | Symmetric scalar and rate cluster intervals | Checked | [`GD.corollary_5_7`](../GD/ClusterPhase.lean) |
| Theorem 5.8 | Tight objective-gap phase | Checked (scalar interface) | [`GD.theorem_5_8_scalar`](../GD/ObjectivePhase.lean) |
| Proposition 6.2 | Reciprocal sandwich | Checked | [`GD.proposition_6_2`](../GD/Proposition62.lean) |
| Theorem 6.3 | Uniform OBS-F phase and cluster interval | Checked | [`GD.theorem_6_3`](../GD/OBSInterpolation.lean) |
| Lemma 6.4 | Sharp support inequality; equality ratio | Checked | [`GD.lemma_6_4`](../GD/SharpSupport.lean) |
| Theorem 6.5 | Nonconstant phase; strict support separation | Checked | [`GD.theorem_6_5`](../GD/ContactPhase.lean) |
| Theorem B.1 | Number of optimal plane trees | Checked | [`GD.theorem_B_1`](../GD/TreeCounts.lean) |
| Theorem C.1 | Derivative products and one-sided derivatives | Checked | [`GD.theorem_C_1`](../GD/DerivativeTheorem.lean) |
| Corollary C.2 | Strict corner at 3/2 | Checked | [`GD.corollary_C_2`](../GD/CornerTheorem.lean) |
| Theorem C.3 | Nested finite phase-minimum certificates | Checked | [`GD.theorem_C_3`](../GD/GridAlgorithm.lean) |
| Lemma D.1 | Local A-versus-K inequalities | Checked | [`GD.lemma_D_1_upper`](../GD/Asymmetric.lean), [`GD.lemma_D_1_lower`](../GD/Asymmetric.lean) |
| Lemma D.2 | Discrete modulus for U, W, C | Checked | [`GD.lemma_D_2`](../GD/DiscreteModulus.lean) |
| Proposition D.3 | Support barrier and exact deficit identity | Checked | [`GD.proposition_D_3`](../GD/DeficitBounds.lean) |
| Lemma D.4 | Strict interior power envelope | Checked | [`GD.lemma_D_4`](../GD/StrictEnvelope.lean) |
| Lemma D.5 | Contact fraction and dyadic exclusion | Checked | [`GD.lemma_D_5`](../GD/ContactFraction.lean) |
| Theorem D.6 | Strict dyadic-ray separation | Checked | [`GD.theorem_D_6`](../GD/ContactPhase.lean) |
| Lemma D.7 | Constant-phase rigidity | Checked | [`GD.lemma_D_7`](../GD/OBSConstant.lean) |
| Theorem D.8 | Strict separation at every phase | Checked | [`GD.theorem_D_8`](../GD/ContactPhase.lean) |
| Proposition D.9 | Upper phase enclosure | Checked | [`GD.proposition_D_9`](../GD/OBSUpperBarrier.lean) |

## Exact scope notes

| Result | Mathematical correspondence / limitation |
|---|---|
| 2.5 | Complete scalar/tree conjugacy and attained optima. Smooth-convex GD certificate interfaces from the cited papers are not formalized. |
| 2.6 | Domain assumptions and both strict ratio inequalities retained. K_gt_sum implies the displayed strict maximum comparison. |
| 3.1 | Complete statement, or the explicitly documented equivalent formulation, proved over exact real/natural numbers. |
| 3.2 | The sign identity is encoded equivalently as the negative/zero/positive trichotomy, with z strictly beyond both inner roots. |
| 3.3 | Complete statement, or the explicitly documented equivalent formulation, proved over exact real/natural numbers. |
| 3.4 | Complete statement, or the explicitly documented equivalent formulation, proved over exact real/natural numbers. |
| 4.1 | Operation laws are the original abstract hypotheses. silverLaw separately proves that the actual radical kernel satisfies them. |
| 4.2 | Complete statement, or the explicitly documented equivalent formulation, proved over exact real/natural numbers. |
| 4.3 | Complete statement, or the explicitly documented equivalent formulation, proved over exact real/natural numbers. |
| 4.4 | Equivalent unified formula using 2^l*((nu±1)/2), avoiding natural subtraction in l-1. No extra optimizer is admitted. |
| 4.5 | ConPP sums are represented by Tree.primitiveSum. Step indexing is n=N-1; the even tie theorem writes the positive valuation as l+1. |
| 4.6 | Complete statement, or the explicitly documented equivalent formulation, proved over exact real/natural numbers. |
| 5.1 | Full nonnegative real inequality and all equality cases, via a compact-interval calculus proof equivalent to the hyperbolic argument. |
| 5.2 | Full sharp power envelope and equality iff N is a power of two, for the actual recursive U. |
| 5.3 | All recurrence and contraction bounds proved; uses an algebraic mean bound instead of the paper derivative argument. |
| 5.4 | The actual supremum-defined F is proved to interpolate the grid, be bi-Lipschitz with the exact constants, have the stated range and midpoint rule, and be unique. |
| 5.5 | Full positive periodic Lipschitz profile, exact identity, uniqueness, strict minimum bounds and maximum; includes the stated numerical expression for the Lipschitz constant. |
| 5.7 | Both complete cluster intervals and nonconvergence, with actual strictly increasing integer subsequences. |
| 5.8 | Full scalar phase identity, uniform explicit remainder and cluster interval. Smooth-convex GD worst-case tightness is still an external certificate input. |
| 6.2 | Finite-N sandwich, actual Bellman doubling, dyadic-ray convergence and exact phase bounds proved. No imported asymptotic axiom. |
| 6.3 | Actual piecewise affine logarithmic interpolants, uniform phase limit, exact Lipschitz constant, uniqueness, rays and full cluster interval. |
| 6.4 | Actual infimum-defined interior root, uniqueness, sharp support bound and all positive and boundary equality cases proved. |
| 6.5 | Strict minimum/support separation, nonconstancy, distinct minimum and maximum and the upper support enclosure. |
| B.1 | Actual finite enumeration of all optimal plane trees, root-class disjointness, cardinal recurrence, dyadic, odd and even-odd-part formulas proved. |
| C.1 | Integral representation, uniform slope and binary-product limits, actual infinite products, uniform absolute log tail, nondyadic differentiability/continuity and both dyadic expansions. |
| C.2 | Exact generated rational intervals for the radical recurrence; all square inequalities checked by the kernel. Strict left/right derivative separation and nondifferentiability proved. |
| C.3 | Nested finite-grid certificates, all gap bounds and convergence; explicit cached array algorithm and at most 30*2^k scalar operations in the documented real-RAM model. The optional level-17 printed decimals are not a Lean interval certificate. |
| D.1 | Complete statement, or the explicitly documented equivalent formulation, proved over exact real/natural numbers. |
| D.2 | All three discrete increment/modulus bounds, retaining the stated constants and quantification over every admissible LF. |
| D.3 | Support barrier and C lower bound for actual W, exact deficit identity, and nonnegativity of every summand proved. |
| D.4 | Full strict interior envelope. A stronger explicit tent-deficit estimate is proved and passed to the continuous limit. |
| D.5 | Both contact identities and all strict rational bounds proved using exact arithmetic, real powers and logarithms. |
| D.6 | Strict separation of the dyadic-ray limit from the support constant. |
| D.7 | Constant-profile Bellman limit for arbitrary positive split ratio and sharp-support rigidity, with no asymptotic hypotheses imported. |
| D.8 | Pointwise strict separation of the phase profile from the support constant, and strict separation of its minimum over one period. |
| D.9 | Global maximum-phase Bellman test at arbitrary split ratios and resulting support upper barrier. |

For a listed `GD.Targets` definition, the audit requires an actual theorem whose return type directly mentions that exact target. A `def ... : Prop` alone is never counted as a proof. Other entries use the documented equivalent formulations and named supporting theorems.

Numbering is pinned to the manuscript SHA-256 in `repository.json`; update the registry and correspondence if the paper is renumbered.
