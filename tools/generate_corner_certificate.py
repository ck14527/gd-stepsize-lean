#!/usr/bin/env python3
"""Generate exact rational enclosures; Lean checks every arithmetic premise.
No floating point values and no native_decide are used in the certificate.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
S=10**24
def down(x): return Q(x.numerator*S//x.denominator,S)
def up(x): return -down(-x)
def sqrt_down(x): return Q(isqrt(x.numerator*S*S//x.denominator),S)
def sqrt_up(x):
    a=sqrt_down(x)
    return a if a*a==x else a+Q(1,S)
def fmt(x):
    return f'({x.numerator}:ℝ)' if x.denominator==1 else f'({x.numerator}/{x.denominator}:ℝ)'
rho=(1+sqrt_down(Q(2)),1+sqrt_up(Q(2)))
values={1:(Q(1),Q(1))}; rows=[]
out=['import GD.IntervalKernel','import GD.Balanced','','namespace GD','noncomputable section','open Set','set_option maxHeartbeats 4000000','','/-- Certified by integer squaring, not by decimal evaluation. -/',
f'theorem corner_rho_interval : rho ∈ Icc {fmt(rho[0])} {fmt(rho[1])} := by',
'  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)',
'  have hn := Real.sqrt_nonneg 2','  unfold rho','  constructor <;> nlinarith [hs,hn]','',
'theorem corner_U_1 : U 1 ∈ Icc (1:ℝ) 1 := by simp','']
def enclose(n):
    if n in values:return values[n]
    a=n//2; al,au=enclose(a)
    if n%2==0:
        lo,hi=down(rho[0]*al),up(rho[1]*au)
        out.extend([f'theorem corner_U_{n} : U {n} ∈ Icc {fmt(lo)} {fmt(hi)} := by',
            f'  have h := positive_product_interval rho (U {a}) {fmt(rho[0])} {fmt(rho[1])} {fmt(al)} {fmt(au)} (by norm_num) (by norm_num) corner_rho_interval corner_U_{a}',
            f'  rw [show {n}=2*{a} by norm_num,U_even]',
            '  constructor','  · apply le_trans _ h.1','    norm_num','  · apply le_trans h.2','    norm_num',''])
        rows.append(dict(n=n,kind='even',a=a,lower=str(lo),upper=str(hi)))
    else:
        b=a+1;bl,bu=enclose(b)
        dl=al*al+6*al*bl+bl*bl;du=au*au+6*au*bu+bu*bu
        sl,su=sqrt_down(dl),sqrt_up(du)
        lo,hi=down((al+bl+sl)/2),up((au+bu+su)/2)
        out.extend([f'theorem corner_U_{n} : U {n} ∈ Icc {fmt(lo)} {fmt(hi)} := by',
            f'  have h := radical_kernel_interval (U {a}) (U {b}) {fmt(al)} {fmt(au)} {fmt(bl)} {fmt(bu)} {fmt(sl)} {fmt(su)} (by norm_num) (by norm_num) corner_U_{a} corner_U_{b} (by norm_num) (by norm_num) (by norm_num)',
            f'  rw [show {n}=2*{a}+1 by norm_num,U_odd]',
            '  constructor','  · apply le_trans _ h.1','    norm_num','  · apply le_trans h.2','    norm_num',''])
        rows.append(dict(n=n,kind='odd',a=a,b=b,lower=str(lo),upper=str(hi),sqrt_lower=str(sl),sqrt_upper=str(su)))
    values[n]=(lo,hi);return lo,hi
for n in [191,192,193]: enclose(n)
out += ['theorem corner_discrete_gap : 0 < 2*U 192-U 191-U 193 := by',
'  have h1 := corner_U_191.2','  have h2 := corner_U_192.1','  have h3 := corner_U_193.2',
'  norm_num at h1 h2 h3','  linarith','','end','end GD','']
(ROOT/'GD/CornerCertificate.lean').write_text('\n'.join(out))
(ROOT/'audit/corner_rational_certificate.json').write_text(json.dumps({'decimal_scale':S,'rho':list(map(str,rho)),'rows':rows,'gap_lower':str(2*values[192][0]-values[191][1]-values[193][1]),'trusted':'Only the Lean kernel check certifies the generated claims.'},indent=2))
print(f'Generated {len(rows)} recurrence enclosures; exact gap lower bound = {2*values[192][0]-values[191][1]-values[193][1]}')
