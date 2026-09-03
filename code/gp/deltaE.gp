\\ Phase two: delta_E for E: y^2 = x^3 - 56x  (CM by Z[i], f = (56), N = 12544)
\\ ---------------------------------------------------------------------------
\\ Computes the Eisenstein--Kronecker grade-<=2 jet package of def:deltaE
\ and equation eq:jetpackage, computed for the testbed curve in Section 6:
\\   * the canonical class-invariant twisted sums S_{a,b} (exact integers), and
\\   * the resultant-norms over D_E (products over the 384 primary 56-division
\\     points) of each jet section,
\\ then intersects all prime supports with the 1611-prime regulator scan.
\\
\\ Conventions (verified against Bannai-Kobayashi, Duke 153 (2010)):
\\   - lattice L = w1*Z[i], A = area/pi = w1^2/Pi; s2 = e*_{0,2}(L) = 0 by CM
\\     symmetry (checked to 130 digits), so the BK reduced theta = sigma.
\\   - closed forms from BK Thm 1.17 (w-expansion of e^{-w tbar/A}Theta(t+z,w)):
\\       e*_{0,1} = E1*(t) := zeta(t) - tbar/A       e*_{0,2} = wp(t)
\\       e*_{1,1} = -(A/2)(E1*^2 - wp)               e*_{0,3} = -wp'(t)/2
\\       e*_{1,2} = -A(E1* wp + wp'/2)               e*_{2,1} = (A^2/3)(E1*^3 - 3E1* wp - wp')
\\   - psi_E((alpha)) = eps(alpha) alpha, primary alpha == 1 mod (2+2i);
\\     eps = (56/.)_4^{-1} (verified vs a_p at 3018 split primes, 0 conflicts).
\\   - t_g = g*w1/56, g over the 384 primary classes mod 56; class-invariant
\\     weight for slot (a,b) is eps(g)^{-(a+b)} (unique rep-independent choice).
\\   - BK Prop 1.6(i): grade-0 sum = (unit)*L(psi_bar,1) = 0 (rank two).
\\ Output: ../data/deltaE_phase2.txt
\\ ---------------------------------------------------------------------------
default(parisizemax, 4000000000);
default(realprecision, 3200);
E = ellinit([0,0,0,-56,0]);
w1 = E.omega[1];
A = w1^2/Pi;
isprimary(a, b) = ((a + b - 1) % 4 == 0) && ((b - a + 1) % 4 == 0);
classid(a, b) = ((a % 56) + 56) % 56 * 56 + ((b % 56) + 56) % 56;

\\ --- eps table from a_p (Deuring: a_p = psi(p) + conj(psi(p))) ---
epstab = vector(56*56);
Q = Qfb(1, 0, 1);
{forprime(p = 5, 60000,
  if(p % 4 != 1 || p == 7, next);
  my(sol = qfbsolve(Q, p));
  if(sol == 0, next);
  my(a = sol[1], b = sol[2], fa = 0, fb = 0);
  for(k = 0, 3, if(isprimary(a, b), fa = a; fb = b; break); [a, b] = [-b, a]);
  my(ap = ellap(E, p), cand = [2*fa, -2*fb, -2*fa, 2*fb], kk = 0, nm = 0);
  for(k = 1, 4, if(cand[k] == ap, kk = k; nm++));
  if(nm != 1, next);
  my(id = classid(fa, fb));
  if(epstab[id] == 0, epstab[id] = kk));}

\\ --- section values at the 384 primary points ---
CA = List(); CB = List(); CK = List();
{for(a = 0, 55, for(b = 0, 55,
  if(!isprimary(a, b), next);
  my(id = classid(a, b));
  if((a + b) % 2 == 0, next);
  if(a % 7 == 0 && b % 7 == 0, next);
  if(epstab[id] == 0, print("MISSING CLASS ", [a,b]); next);
  listput(CA, a); listput(CB, b); listput(CK, epstab[id] - 1)));}
n = #CA;
print("classes: ", n, " (expect 384)");
VE1 = vector(n); VP = vector(n); VPd = vector(n); VW = vector(n);
{for(j = 1, n,
  my(t = (CA[j] + CB[j]*I)*w1/56, wp2 = ellwp(E, t, 1));
  VE1[j] = ellzeta(E, t) - conj(t)/A;
  VP[j]  = wp2[1];
  VPd[j] = wp2[2];
  VW[j]  = I^(-CK[j]));}
print("section values done");

\\ --- class-invariant sums ---
ints(x) = my(r = bestappr(real(x), 10^40)); if(exponent(abs(x - r)) < -1000, r, "FAIL");
S01 = ints(sum(j=1,n, VW[j]^1*VE1[j]));
S02 = ints(sum(j=1,n, VW[j]^2*VP[j]));
S11 = ints(sum(j=1,n, VW[j]^2*(-1/2)*(VE1[j]^2 - VP[j])));
S03 = ints(sum(j=1,n, VW[j]^3*(-1/2)*VPd[j]));
S12 = ints(sum(j=1,n, VW[j]^3*(-1)*(VE1[j]*VP[j] + VPd[j]/2)));
S21 = ints(sum(j=1,n, VW[j]^3*(1/3)*(VE1[j]^3 - 3*VE1[j]*VP[j] - VPd[j])));
print("S(0,1) [~L(psibar,1)] = ", S01);
print("S(0,2) = ", S02, "   S(1,1)/A = ", S11);
print("S(0,3) = ", S03, "   S(1,2)/A = ", S12, "   S(2,1)/A^2 = ", S21);

\\ --- resultants; {2,7}-denominators forced, clear & round ---
\\ Output staging: results are written to TMP and moved onto OUT only after all
\\ six resultants have been reported in full.  NOK counts reports that reach
\\ their last line, so a resultant that fails the rounding gate and a resultant
\\ that raises a PARI error both leave NOK short of 6; a run that aborts part-way
\\ never reaches the move.  In each case the committed OUT is untouched and the
\\ partial output is left in TMP.
OUT = "../data/deltaE_phase2.txt";
TMP = "../data/deltaE_phase2.txt.partial";
system(Str("rm -f ", TMP));
NOK = 0;
scanp = List();
{my(ls = readstr("../data/all_primes_vreg.txt"));
 for(i = 1, #ls,
   my(v = strsplit(ls[i], " "));
   if(#v >= 2 && eval(v[1]) > 0, listput(scanp, eval(v[1]))));}
scanset = Set(Vec(scanp));
print("scan primes: ", #scanset);
{write(TMP, "delta_E phase-two results, E: y^2 = x^3 - 56x, f = (56), computed 2026-07-13");}
{write(TMP, "invariant sums: S01 ", S01, "  S02 ", S02, "  S11/A ", S11, "  S03 ", S03, "  S12/A ", S12, "  S21/A^2 ", S21);}

report(name, x, A2, B7) = {
  my(z = real(x)*2^A2*7^B7, r = round(z));
  if(r == 0 || exponent(abs(z - r)) > -1200,
     print(name, ": FAILED err 2^", exponent(abs(z - r))); return);
  my(v2 = valuation(r,2) - A2, v7 = valuation(r,7) - B7);
  my(odd = abs(r)/2^valuation(r,2)/7^valuation(r,7));
  my(hits = List(), scanhits = List(), rem = odd);
  forprime(q = 3, 30000, if(q == 7, next);
    my(v = valuation(rem, q)); if(v, rem /= q^v; listput(hits, [q, v])));
  for(i = 1, #hits, if(setsearch(scanset, hits[i][1]), listput(scanhits, hits[i])));
  print(name, " = sgn ", sign(r), " * 2^", v2, " * 7^", v7, " * ", Vec(hits), " * C[", if(rem == 1, "1", Str(#digits(rem), "dig")), "]   SCAN HITS: ", if(#scanhits == 0, "NONE", Vec(scanhits)));
  write(TMP, "== ", name, " ==");
  write(TMP, "sign ", sign(r), "  v2 ", v2, "  v7 ", v7, "  smallprimes ", Vec(hits), "  scanhits ", if(#scanhits == 0, "NONE", Str(Vec(scanhits))));
  write(TMP, "cofactor(all prime factors > 30000): ", rem);
  NOK++;
};

report("RES E1*      (grade 0) ", prod(j=1,n, VE1[j]), 520, 260);
report("RES E1^2-P   (e11-core)", prod(j=1,n, VE1[j]^2 - VP[j]), 1000, 480);
report("RES P        (e02)     ", prod(j=1,n, VP[j]), 40, 20);
report("RES Pd       (e03-core)", prod(j=1,n, VPd[j]), 40, 20);
report("RES E1P+Pd/2 (e12-core)", prod(j=1,n, VE1[j]*VP[j] + VPd[j]/2), 100, 60);
report("RES e21-core (grade 2) ", prod(j=1,n, VE1[j]^3 - 3*VE1[j]*VP[j] - VPd[j]), 1600, 720);

{NLINE = if(NOK == 6, #readstr(TMP), 0);
 if(NOK == 6 && NLINE == 20,
    system(Str("mv -f ", TMP, " ", OUT));
    print("DELTAEDONE"),
    print("INCOMPLETE: ", NOK, " of 6 resultants reported, ", NLINE, " of 20 lines written.");
    print(OUT, " left unchanged; partial output in ", TMP, "."));}
quit
