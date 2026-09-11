#!/usr/bin/env python3
"""Independent finite checks. These are NOT Lean proofs or asymptotic proofs.
Python Decimal at 60 digits is used for exhaustive DP and paper certificates.
"""
from decimal import Decimal as D, localcontext
from pathlib import Path
import argparse,json,time
ROOT=Path(__file__).resolve().parents[1]
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--level',type=int,default=17);ap.add_argument('--dp',type=int,default=160);args=ap.parse_args()
 started=time.time()
 with localcontext() as ctx:
  ctx.prec=60
  rho=1+D(2).sqrt();p=rho.ln()/D(2).ln();q=1/p
  def K(x,y):return (x+y+(x*x+6*x*y+y*y).sqrt())/2
  def A(x,w):return (4*x+w+(w*w+8*x*w).sqrt())/2
  def T0(r):return K(D(1),r)/rho
  def T1(r):return rho*r/K(D(1),r)
  def w0(r):return 2*(T0(r)-1)/(r-1)
  def w1(r):return 2-w0(r)
  cap=max(2**(args.level+1),args.dp)
  U=[D(0),D(1)]+[D(0)]*(cap-1)
  for n in range(2,cap+1):U[n]=K(U[n//2],U[(n+1)//2])
  def split_pattern(m,n):
   if m==n:return True
   while m%2==0 and n%2==0:m//=2;n//=2
   return abs(m-n)==1
  # Full quadratic Bellman DP is independent of assuming a balanced root.
  B=[D(0),D(1)];W=[D(0),D(1)];errors=[];counts=[0,1];max_diff=D(0)
  for n in range(2,args.dp+1):
   vals=[K(B[m],B[n-m]) for m in range(1,n)]
   best=max(vals);B.append(best);max_diff=max(max_diff,abs(best-U[n]))
   observed=[i+1 for i,v in enumerate(vals) if abs(v-best)<D('1e-45')]
   expected=[m for m in range(1,n) if split_pattern(m,n-m)]
   if observed!=expected:errors.append({'n':n,'observed':observed,'expected':expected})
   counts.append(sum(counts[m]*counts[n-m] for m in expected))
   W.append(max(A(U[m],W[n-m]) for m in range(1,n)))
   assert 2*U[n]-1-D('1e-45') <= W[n] <= rho*U[n]+D('1e-45')
  lo=(D('Infinity'),0);hi=(D('Infinity'),0)
  for n in range(2**args.level,2**(args.level+1)):
   lb=U[n]/((D(n+1).ln()*p).exp());ub=U[n]/((D(n).ln()*p).exp())
   if lb<lo[0]:lo=(lb,n)
   if ub<hi[0]:hi=(ub,n)
  x=T0(rho);y=T1(rho);L=(rho-1)*w0(rho);R=(rho-1)*w1(rho)
  for _ in range(6):L*=w1(x);R*=w0(y);x=T1(x);y=T0(y)
  # The following checks compare numbers, not formal interval proof objects.
  corner={'x6':str(x),'y6':str(y),'L6':str(L),'R6':str(R),'L6_gt_R6':L>R}
  eta=1/rho;pure=eta/(2-eta);quad=eta*eta
  # Unique support contact: bisection on the interior crossing.
  a,b=D('0.48'),D('0.5')
  def g(x):return ((2*q-1)*x.ln()).exp()*(2-x)-1
  for _ in range(220):
   mid=(a+b)/2
   if g(mid)>0:b=mid
   else:a=mid
  xi=(a+b)/2;tau=(1-xi)/(2*xi*xi);bs=(q*D(2).ln()).exp()*(1-(2*q*xi.ln()).exp())/((q*(1-xi).ln()).exp());alpha=1-(2*q*xi.ln()).exp()
  result={'status':'finite high-precision checks only; not Lean proofs','precision_digits':ctx.prec,'full_dp_horizons':args.dp,'balanced_dp_max_abs_difference':str(max_diff),'optimizer_pattern_mismatches':errors,'tree_counts_1_to_12':counts[1:13],'minimum_grid':{'level':args.level,'lower_candidate':str(lo[0]),'lower_index':lo[1],'upper_candidate':str(hi[0]),'upper_index':hi[1]},'corner':corner,'quadratic_correction_N2':{'eta':str(eta),'quadratic_coefficient':str(quad),'pure_objective_coefficient':str(pure),'strict_gap':quad<pure},'support':{'xi':str(xi),'tau':str(tau),'Bsup':str(bs),'cstar':str((-p*bs.ln()).exp()),'alpha':str(alpha),'remainder_fraction':str(1-alpha)},'elapsed_seconds':time.time()-started}
  (ROOT/'audit/numerical_checks.json').write_text(json.dumps(result,indent=2))
  print(json.dumps(result,indent=2))
if __name__=='__main__':main()
