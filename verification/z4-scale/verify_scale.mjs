import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const here=path.dirname(fileURLToPath(import.meta.url));
const T=500n,q=768n,V=175n;
const Delta=1000000n*(T+2n)*(9n*q+10n),X=2n*Delta*Delta;
const Km=(1n<<20n)*X**257n;
const Kh=(1n<<40n)*(100n*(V+1n))**10n*X**100n;
const Cden=(128n*Km)**2n;
const d1=(64n*Km)**6n,d2=(64n*Kh)**4n;
const targetDen=d1>d2?d1:d2;
const cap=BigInt(targetDen.toString(2).length+64);
function minimum(a,b){return a<b?a:b;}
function qualifies(k){
 const B=1n<<BigInt(2*k);
 if(B<20n*Cden)return false;
 const ue=3n*B/(100n*Cden),ze=B/(3n*Cden),we=B/(50n*Cden*Cden);
 if(ze<3n)return false;
 const u=1n<<minimum(ue,cap),z=1n<<minimum(ze,cap),w=1n<<minimum(we,cap);
 const den=u*(z-4n)*w,num=3n*z*w+2n*u*(z-4n);
 if(num*targetDen<den)return true;
 if(we<=cap && 2n*targetDen>=(1n<<we))return false;
 throw Error('Indeterminate exact B comparison');
}
let lo=1,hi=2;
while(!qualifies(hi)){lo=hi;hi*=2;}
while(hi-lo>1){const mid=Math.floor((lo+hi)/2);if(qualifies(mid))hi=mid;else lo=mid;}
const k=hi,B=1n<<BigInt(2*k);
if(!qualifies(k)||qualifies(k-1))throw Error('B minimality');
const nQ=(2n*T+1n)**2n*(T*V+1n)**2n;
const kappa=2n*B*(9n*q+nQ+2n);
let N0=1n;for(let j=1n;j<=256n;j++)N0=N0*(352n**2n-j+1n)/j;
const Dr=1000000n*(kappa+B+352n**2n+q+T+1n);
const P=256n,U=1n<<P;
const ceilDiv=(a,b)=>(a+b-1n)/b;
// Certified fixed-point intervals, independent of the Fraction implementation.
// ln x = 2 sum y^(2j+1)/(2j+1), y=(x-1)/(x+1).
// For x in [1,2], the 200-term remainder is <3^-400 <2^-256.
function lnMantissa(n,den){
 const ylo=(n-den)*U/(n+den),yhi=ceilDiv((n-den)*U,n+den);
 const zlo=ylo*ylo/U,zhi=ceilDiv(yhi*yhi,U);
 let plo=ylo,phi=yhi,slo=0n,shi=0n;
 for(let j=0n;j<200n;j++){
  const odd=2n*j+1n;
  slo+=plo/odd;shi+=ceilDiv(phi,odd);
  plo=plo*zlo/U;phi=ceilDiv(phi*zhi,U);
 }
 return [2n*slo,2n*shi+1n];
}
const ln2=lnMantissa(2n,1n);
function log2(n){
 const e=BigInt(n.toString(2).length-1),den=1n<<e;
 const ln=lnMantissa(n,den);
 return [e*U+ln[0]*U/ln2[1],e*U+ceilDiv(ln[1]*U,ln2[0])];
}
const add=(a,b)=>[a[0]+b[0],a[1]+b[1]];
const mul=(a,c)=>[a[0]*c,a[1]*c];
const con=c=>[c*U,c*U];
const terms={
 C_over_100:log2(100n*Cden),
 memory:mul(add(con(6n),log2(Km)),4n),
 history:mul(add(con(6n),log2(Kh)),44n),
 rare:mul(add(add(con(26n),mul(add(con(1n),mul(log2(Dr),2n)),513n)),log2(N0+1n)),16n),
 density:mul(log2(382205952n),33720n)
};
const rare=terms.rare;
for(const [name,v] of Object.entries(terms))if(name!=='rare'&&rare[0]<=v[1])throw Error('Binding threshold');
const x=log2(10n*Cden),y=log2(21n),rat=[x[0]-y[1],x[1]-y[0]];
const nlo=(rare[0]-rat[1]-3n*U)/(2n*U),nhi=(rare[1]-rat[0]-3n*U)/(2n*U);
if(nlo!==nhi)throw Error('n0 uncertain');
const n0=nhi+1n;
if(rat[0]+(2n*n0+3n)*U-(1n<<(P-60n))<=rare[1])throw Error('n0 pass');
if(rat[1]+(2n*(n0-1n)+3n)*U>=rare[0])throw Error('n0-1 fail');
const compact=v=>({lowerNumerator:String(v[0]>>(P-60n)),upperNumerator:String(ceilDiv(v[1],1n<<(P-60n))),denominator:String(1n<<60n)});
const result={engine:'Node.js BigInt certified fixed-point intervals with 200-term logarithm bounds',k,n0:Number(n0),kMinimalCertified:true,n0MinimalCertified:true,bindingTerm:'rare',inverseThresholdLog2Bounds:Object.fromEntries(Object.entries(terms).map(([name,v])=>[name,compact(v)])),log2_10Cden_over_21:compact(rat)};
const python=JSON.parse(fs.readFileSync(path.join(here,'scale-python.json'),'utf8'));
if(result.k!==python.k||result.n0!==python.n0)throw Error('Independent engine mismatch');
for(const [name,v] of Object.entries(result.inverseThresholdLog2Bounds)){
 const w=python.inverseThresholdLog2Bounds[name];
 if(BigInt(v.lowerNumerator)>BigInt(w.upperNumerator)||BigInt(w.lowerNumerator)>BigInt(v.upperNumerator))throw Error('Disjoint logarithm bounds');
}
result.independentEngineAgreement=true;
fs.writeFileSync(path.join(here,'scale-node.json'),JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result,null,2));
