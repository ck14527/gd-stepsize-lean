#!/usr/bin/env python3
from pathlib import Path
import csv,json
ROOT=Path(__file__).resolve().parents[1]
raw=json.loads((ROOT/'audit/inventory.json').read_text())
verified={
'2.5':['proposition_2_5','primitive_tree_optimum','s_tree_optimum','Tree.primitive_conjugacy','Tree.s_conjugacy','join_step_conjugacy','objective_reciprocal'],
'2.6':['rho_gt_two','rho_sq','K_continuous','K_symm','K_hom','K_zero_left','K_diag','K_gt_sum','K_strict_left','K_strict_right','K_ratio_bounds'],
'3.1':['theorem_3_1'], '3.2':['lemma_3_2'], '3.3':['lemma_3_3_first','lemma_3_3_second'], '3.4':['lemma_3_4'],
'4.1':['theorem_4_1'], '4.2':['corollary_4_2'], '4.3':['lemma_4_3'], '4.4':['corollary_4_4'],
'4.5':['theorem_4_5_balanced','theorem_4_5_ties','primitive_tree_optimum','proposition_2_5'],
'4.6':['corollary_4_6','optimal_tree_iff_patterns'],
'5.3':['lemma_5_3'], 'D.1':['lemma_D_1_upper','lemma_D_1_lower'],
'5.1':['lemma_5_1'], '5.2':['proposition_5_2'], '5.4':['theorem_5_4'],
'5.5':['theorem_5_5'], '5.7':['corollary_5_7'], '5.8':['theorem_5_8_scalar'],
'6.2':['proposition_6_2'], '6.4':['lemma_6_4'], 'B.1':['theorem_B_1'],
'D.2':['lemma_D_2'], 'D.3':['proposition_D_3'], 'D.4':['lemma_D_4'], 'D.5':['lemma_D_5'],
}
verified.update({
'6.3':['theorem_6_3'], '6.5':['theorem_6_5'],
'C.1':['theorem_C_1'], 'C.2':['corollary_C_2'], 'C.3':['theorem_C_3'],
'D.6':['theorem_D_6'], 'D.7':['lemma_D_7'], 'D.8':['theorem_D_8'], 'D.9':['proposition_D_9'],
})
partial={}
notes={
'2.5':'Complete scalar/tree conjugacy and attained optima. Smooth-convex GD certificate interfaces from the cited papers are not formalized.',
'2.6':'Domain assumptions and both strict ratio inequalities retained. K_gt_sum implies the displayed strict maximum comparison.',
'3.2':'The sign identity is encoded equivalently as the negative/zero/positive trichotomy, with z strictly beyond both inner roots.',
'4.1':'Operation laws are the original abstract hypotheses. silverLaw separately proves that the actual radical kernel satisfies them.',
'4.4':'Equivalent unified formula using 2^l*((nu±1)/2), avoiding natural subtraction in l-1. No extra optimizer is admitted.',
'4.5':'ConPP sums are represented by Tree.primitiveSum. Step indexing is n=N-1; the even tie theorem writes the positive valuation as l+1.',
'5.3':'All recurrence and contraction bounds proved; uses an algebraic mean bound instead of the paper derivative argument.',
'5.1':'Full nonnegative real inequality and all equality cases, via a compact-interval calculus proof equivalent to the hyperbolic argument.',
'5.2':'Full sharp power envelope and equality iff N is a power of two, for the actual recursive U.',
'5.4':'The actual supremum-defined F is proved to interpolate the grid, be bi-Lipschitz with the exact constants, have the stated range and midpoint rule, and be unique.',
'5.5':'Full positive periodic Lipschitz profile, exact identity, uniqueness, strict minimum bounds and maximum; includes the stated numerical expression for the Lipschitz constant.',
'5.7':'Both complete cluster intervals and nonconvergence, with actual strictly increasing integer subsequences.',
'5.8':'Full scalar phase identity, uniform explicit remainder and cluster interval. Smooth-convex GD worst-case tightness is still an external certificate input.',
'6.2':'Finite-N sandwich, actual Bellman doubling, dyadic-ray convergence and exact phase bounds proved. No imported asymptotic axiom.',
'6.4':'Actual infimum-defined interior root, uniqueness, sharp support bound and all positive and boundary equality cases proved.',
'D.2':'All three discrete increment/modulus bounds, retaining the stated constants and quantification over every admissible LF.',
'D.3':'Support barrier and C lower bound for actual W, exact deficit identity, and nonnegativity of every summand proved.',
'D.4':'Full strict interior envelope. A stronger explicit tent-deficit estimate is proved and passed to the continuous limit.',
'D.5':'Both contact identities and all strict rational bounds proved using exact arithmetic, real powers and logarithms.',
'6.3':'Actual piecewise affine logarithmic interpolants, uniform phase limit, exact Lipschitz constant, uniqueness, rays and full cluster interval.',
'C.1':'Integral representation, uniform slope and binary-product limits, actual infinite products, uniform absolute log tail, nondyadic differentiability/continuity and both dyadic expansions.',
'C.3':'Nested finite-grid certificates, all gap bounds and convergence; explicit cached array algorithm and at most 30*2^k scalar operations in the documented real-RAM model. The optional level-17 printed decimals are not a Lean interval certificate.',
'B.1':'Actual finite enumeration of all optimal plane trees, root-class disjointness, cardinal recurrence, dyadic, odd and even-odd-part formulas proved.',
'C.2':'Exact generated rational intervals for the radical recurrence; all square inequalities checked by the kernel. Strict left/right derivative separation and nondifferentiability proved.',
'D.6':'Strict separation of the dyadic-ray limit from the support constant.',
'D.7':'Constant-profile Bellman limit for arbitrary positive split ratio and sharp-support rigidity, with no asymptotic hypotheses imported.',
'D.8':'Pointwise strict separation of the phase profile from the support constant, and strict separation of its minimum over one period.',
'D.9':'Global maximum-phase Bellman test at arbitrary split ratios and resulting support upper barrier.',
'6.5':'Strict minimum/support separation, nonconstancy, distinct minimum and maximum and the upper support enclosure.',

}
targets={
'5.1':'lemma_5_1','5.2':'proposition_5_2','5.4':'theorem_5_4','5.5':'theorem_5_5','5.7':'corollary_5_7',
'5.8':'theorem_5_8_scalar','6.2':'proposition_6_2','6.3':'theorem_6_3','6.4':'lemma_6_4','6.5':'theorem_6_5',
'C.1':'theorem_C_1','C.2':'corollary_C_2','C.3':'theorem_C_3',
'D.2':'lemma_D_2','D.3':'proposition_D_3','D.4':'lemma_D_4','D.5':'lemma_D_5','D.6':'theorem_D_6','D.7':'lemma_D_7','D.8':'theorem_D_8','D.9':'proposition_D_9'}
rows=[]
for n in raw['nodes']:
 if n['kind'] not in ['Theorem','Lemma','Proposition','Corollary']:continue
 k=n['id'];status='verified_scalar_model' if k in verified else 'partial' if k in partial else 'open'
 rows.append({'paper_id':k,'kind':n['kind'],'title':n['title'],'page':n['pages'][0],'status':status,
  'proof_declarations':['GD.'+x for x in verified.get(k,partial.get(k,[]))],
  'target_definition': 'GD.Targets.'+targets[k] if k in targets else None,
  'scope_note':notes.get(k,'No full Lean proof supplied for this numbered result.') if status!='verified_scalar_model' else notes.get(k,'Complete statement, or the explicitly documented equivalent formulation, proved over exact real/natural numbers.')})
result={'scope':'36 numbered scalar/combinatorial results in the manuscript snapshot identified by repository.json.',
 'full_paper_formalization_complete':False,'external_GD_certificate_interfaces_formalized':False,
 'scalar_numbered_results_complete':all(x['status']=='verified_scalar_model' for x in rows),
 'optional_level17_interval_certificate_formalized':False,
 'semantic_statement_matching':'Manual mathematical comparison, not an automatic proof that PDF prose equals a Lean proposition.',
 'counts':{s:sum(x['status']==s for x in rows) for s in ['verified_scalar_model','partial','open']},'results':rows,
 'additional_verified':{'ALG1':['GD.algorithm_1','GD.bitStep_correct','GD.runBits_correct'],
 'EQ21':['GD.U_dyadic'],'objective_coefficient_comparison':['GD.quadratic_not_objective_extremizer']}}
(ROOT/'audit/coverage.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
by_id={r['paper_id']:r for r in rows}
for n in raw['nodes']:
 if n['id'] in by_id:n['formal_status']=by_id[n['id']]['status']
(ROOT/'audit/inventory.json').write_text(json.dumps(raw,ensure_ascii=False,indent=2))
with (ROOT/'audit/inventory.csv').open('w') as f:
 w=csv.writer(f,lineterminator="\n");w.writerow(['id','kind','title','pages','prerequisites','formal_status'])
 for n in raw['nodes']:w.writerow([n['id'],n['kind'],n['title'],','.join(map(str,n['pages'])),','.join(n['depends_on']),n['formal_status']])
print(json.dumps(result['counts']))
