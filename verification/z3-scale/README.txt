Z3 scale certificates for version 1.4.0

Run from this directory, as separate jobs:
  python -I -B verify_scale.py
  node verify_scale.mjs

Python 3.11 or later is required. verify_scale.py uses only the Python standard library. It implements exact Fraction-series intervals: integer mantissas are bounded outward at 300 bits, and logarithms use a finite rational arctanh series with an explicit remainder. Printed decimal endpoints are rounded outward by exact integer division and are never used for threshold decisions.

verify_scale.mjs uses only standard Node modules and requires native BigInt and ES-module support. Its independent implementation computes integer degree polynomials and uses outward-rounded fixed-point logarithm intervals with 384 fractional bits and 220 series terms. Neither program imports code or results from the other.

Both programs reject earlier k by exact floor tests or separated intervals, establish the binding epsilon term, enclose the n0 floor, check its adjacent threshold inequalities, and certify the exact decay coefficient. Huge powers are represented by formulas and rigorous logarithmic intervals. The sensor-tail correction is bounded by 2^-250 from exact exponent gaps.

Expected values: k=43429; floor(BC^2/50)=10747726824774400122; n0=33644133613821753975; binding term (64K_full)^(-44); log10(1/epsilon_*) in [20255786791774346221.279452991654, 20255786791774346221.279452991655]; c=1/(2^42*17600000000*(4^43429+176363)); log10(1/c) in [26169.752135867780, 26169.752135867781].

Each program writes its scale-python.json or scale-node.json certificate and matching .out.txt file beside the script, and prints the same content. Recorded outputs are supplied. All common mathematical fields agree; engine descriptions and certification wording identify the independent methods.
