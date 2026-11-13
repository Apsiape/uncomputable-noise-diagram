// Independently written BigInt fixed-point interval certificate. No floating decisions.
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const here=path.dirname(fileURLToPath(import.meta.url));
const Q=1n<<384n;
const ceil=(a,b)=>(a+b-1n)/b;
function assert(v,m='certificate assertion'){if(!v)throw Error(m);}
const add=(a,b)=>[a[0]+b[0],a[1]+b[1]];
const scale=(a,k)=>k>=0n?[a[0]*k,a[1]*k]:[a[1]*k,a[0]*k];
const minus=(a,b)=>add(a,scale(b,-1n));
const divide=(a,b)=>{assert(a[0]>=0n&&b[0]>0n);return[a[0]*Q/b[1],ceil(a[1]*Q,b[0])];};
function atanhLog(p,r){
  // All endpoints are integer multiples of 2^-384; 0<=p/r<=1/3.
  assert(p>=0n&&3n*p<=r);
  const z=[p*Q/r,ceil(p*Q,r)];
  const zz=[z[0]*z[0]/Q,ceil(z[1]*z[1],Q)];
  let power=z.slice(), total=[0n,0n];
  const M=220;
  for(let j=0;j<M;j++){
    const odd=BigInt(2*j+1);
    total=add(total,[power[0]/odd,ceil(power[1],odd)]);
    power=[power[0]*zz[0]/Q,ceil(power[1]*zz[1],Q)];
  }
  // Remainder <= 3 z^(2M+1)/(2M+1), since z<=1/3.
  return[2n*total[0],2n*total[1]+ceil(3n*power[1],BigInt(2*M+1))];
}
const L2=atanhLog(1n,3n);
function ln(n){const e=BigInt(n.toString(2).length-1), b=1n<<e;return add(scale(L2,e),atanhLog(n-b,n+b));}
const L10=ln(10n);
function show(v,digits=12,upper=false){const unit=10n**BigInt(digits);const fixed=upper?ceil(v*unit,Q):v*unit/Q;return(fixed/unit).toString()+'.'+(fixed%unit).toString().padStart(digits,'0');}
const span=(v,base)=>{const a=divide(v,base);return[show(a[0]),show(a[1],12,true)];};
const D=3474844000000n;
const mem=(1n<<20n)*(2n*D**2n)**257n;
const invC=(128n*mem)**2n;
const LM=ln(mem), LC=ln(invC);
const tail=ceil(Q,1n<<250n);
let B=1n,k=0,prev=null,accepted;
while(true){
 k++;B<<=2n;
 if(B<20n*invC)continue;
 const z=B/(3n*invC), w=B/(50n*invC**2n), u=3n*B/(100n*invC);
 if(z<=2n||w===0n)continue;
 assert(u-w>=252n);
 const degree=10n**30n*502n**10n*769n**10n*(B+1n)**4n;
 const LF=add(scale(L2,20n),scale(add(L2,scale(ln(degree),2n)),1n<<41n));
 const m=scale(add(scale(L2,6n),LM),6n), f=scale(add(scale(L2,6n),LF),4n);
 const rhs=[m[0]>f[0]?m[0]:f[0],m[1]>f[1]?m[1]:f[1]];
 const lhs=scale(L2,w-1n);lhs[0]-=tail;
 const margin=minus(lhs,rhs);
 if(margin[0]>0n){accepted={LF,w,margin};break;}
 assert(margin[1]<0n,'unresolved k');prev={k,margin};
}
assert(k===43429&&prev.k===k-1);
const terms=[add(ln(100n),LC),scale(ln(382205952n),33720n),
 scale(add(scale(L2,6n),LM),4n),scale(add(scale(L2,6n),accepted.LF),44n)];
assert(terms.slice(0,3).every(x=>x[1]<terms[3][0]));
const target=add(minus(ln(21n),ln(10n)),minus(terms[3],LC));
const quotient=divide(target,L2);
const nlo=(quotient[0]-3n*Q)/(2n*Q),nhi=(quotient[1]-3n*Q)/(2n*Q);
assert(nlo===nhi);const n0=nlo+1n;assert(n0===33644133613821753975n&&n0>BigInt(k+2));
const E=2n*n0+3n;
const at=minus(scale(L2,E),target);at[0]-=tail;
const before=minus(scale(L2,E-2n),target);
assert(at[0]>0n&&before[1]<0n);
const rate=ln((1n<<42n)*17600000000n*(B+176363n));
const sval=ceil(3n*B,4n*invC).toString();
const result={engine:'Node BigInt outward fixed-point Taylor intervals',k,n0:n0.toString(),
 binding:'(64K_full)^(-44)',Fw:accepted.w.toString(),s_digits:sval.length,s_leading:sval.slice(0,20),
 log10_epsilon_reciprocal:span(terms[3],L10),log10_K_full:span(accepted.LF,L10),
 log10_c_reciprocal:span(rate,L10),c:'1/(2^42*17600000000*(4^43429+176363))',
 k_previous_margin_log2:span(scale(prev.margin,-1n),L2),k_margin_log2:span(accepted.margin,L2),
 n0_margin_log2:span(at,L2),n0_previous_failure_log2:span(scale(before,-1n),L2),
 all_decisions:'CERTIFIED by BigInt interval separation',
 earlier_k:'exhaustively rejected by exact floors or separated intervals',
 eta_tail:'0 < ln(eta*2^(Fw-1)) < 2^-250; no enormous powers constructed'};
const out=JSON.stringify(result,null,2)+'\n';
fs.writeFileSync(path.join(here,'scale-node.json'),out);
fs.writeFileSync(path.join(here,'scale-node.out.txt'),out);
process.stdout.write(out);
