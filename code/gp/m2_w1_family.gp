\\ m2_w1_family.gp -- the algebraic bracket B_alg of (W1)/(W2) for E_D : y^2 = x^3 - D x.
\\ ---------------------------------------------------------------------------
\\ Backs the bracket table of paper Section 8 (eq:bracket, prop:exactreduction,
\\ thm:criterion) for the
\\ five rank-two curves of Coates--Liang--Sujatha: D = 56, 17, -33, -34, -39.
\\ gp/m2_w1.gp does the same computation for D = 56 alone and is the reference:
\\ its fourteen class sums are re-checked here whenever D = 56.
\\
\\ WHAT THIS COMPUTES
\\     B_alg = E(2p-2,0) (2p-2)!             P_{0,2p-1}
\\           - 2 E(p-1,p-1) (p-1)! N(f)^{p-1} P_{p-1,p}
\\           + E(0,2p-2)          N(f)^{2p-2} P_{2p-2,1} ,
\\     P_{a,b} = sum_{[g] in D_E} eps(g)^{-(a+b)} e*_{a,b}(t_g,0)/A^a ,
\\     E(k,l) = (1 - pi^{k+l+1}/p^{l+1})(1 - pi^{k+l+1}/p^{k+1}),  pi = psi_E(fp),
\\ reports v_p(B_alg) and p^{-2} B_alg mod p, and compares the vanishing against
\\ the criterion class kappa(p) of the Mazur--Tate--Teitelbaum normalisation,
\\ read from the output of sage/m2_msd_family.sage.  (W2) predicts
\\ v_p(B_alg) = 2 exactly when kappa(p) != 0 and v_p(B_alg) >= 3 when it is 0.
\\ It also checks the residue identity of the paper (cor:residue),
\\     kappa(p) = (f_0 omega_E)^{-1} a_p^{-2} p^{-2} B_alg   mod p,
\\ where omega_E = Omega_E/Omega is 2 for D > 0 (two real components,
\\ Omega = omega_1) and 1 - i for D < 0 (one component, Omega = omega_1 (1+i)/2),
\\ embedded by i |-> i_p; the predicted kappa(p) is printed and gated against
\\ the kappa(p) read from the modular-symbol side.
\\
\\ THE THREE THINGS THAT DEPEND ON THE CURVE
\\  1. The Grossencharacter conductor.  N(f) = N/4 = 2^e m^2 with m odd, and f is
\\     the unique conjugation-stable ideal of that norm, f = (1+i)^e (m).  Its
\\     generator is f_0 = (1+i)^e m for e odd and 2^{e/2} m for e even.  The
\\     divisor D_E is enumerated as the primary residues x + y i coprime to f in
\\     the box 0 <= x < H[1,1], 0 <= y < H[2,2] of H = idealhnf(K, f_0); one
\\     primary residue lies in each orbit of the units because (1+i)^3 | f.  The
\\     count is gated against bnrinit(K, H, 1).no.
\\  2. The period lattice.  The Z[i]-generator is Omega = omega_1 for D > 0 and
\\     Omega = omega_1 (1+i)/2 for D < 0; A = Omega conj(Omega)/Pi and
\\     t_g = (x + y i) Omega / f_0.  The quasi-period identity
\\     eta(Omega) = conj(Omega)/A separates the two by 250 bits and is gated.
\\  3. The field of the class sums.  For D = 56 the three class sums are rational.
\\     In general they lie in K = Q(i) and are recognised there, one rational for
\\     the real part and one for the imaginary part.  With
\\     u = (conj(Omega)/Omega)(f_0/conj(f_0)), a fourth root of unity, they satisfy
\\     conj(S) = u^{-(2p-1)} S; that relation is gated, and it pins the sums to a
\\     line in K: real for u = 1 (D = 56), imaginary for u = -1 (D = -39), and on
\\     Q(1+i) for u = -i (D = 17, -33, -34).  The p-adic bracket is formed through
\\     the embedding i |-> i_p fixed by the labelling of fp.
\\
\\ Run from this directory:   D=-33 W1PRIMES=37 gp -q m2_w1_family.gp
\\ Parameters from the environment:
\\     D         the curve y^2 = x^3 - D x                required
\\     W1PRIMES  comma-separated split primes             default "5,13,17"
\\     W1PREC    realprecision                            default 600
\\     W1OUT     output file                              default ../data/m2_w1_D<D>.out
\\     F0        generator of f, overriding the closed form
\\     EPSBOUND  prime bound for the table of eps         default 10^6
\\     KAPPAFILE file of "KAPPA <p> <value>" lines        default ../data/m2_msd_D<D>.out
\\ Cost is #Cl_f times a per-class cost that grows like p^4 and does not depend on
\\ the conductor: at realprecision 600, 78 s at (D = -33, p = 13), 379 s at
\\ (D = 17, p = 37), 14 s at (D = -39, p = 5).  At (D = -33, p = 37), 1920
\\ classes, the run at realprecision 600 took 2779 s and was inconclusive: the
\\ (0,2p-2) slot lost about 240 digits, S[0,2p-2] was not recognised, the
\\ exactness gate did not pass, and no output was written.  A higher precision was not run; the pair is a
\\ reported gap in the paper.
\\ The rational recognition searches denominators up to 10^(W1PREC/3) and the gate
\\ demands a denominator below 10^(W1PREC/6), so a class sum that is not a rational
\\ of that height fails the gate instead of being fitted to numerical noise.  If a
\\ prime fails it, raise W1PREC.
\\ Output staging: results are written to TMP and moved onto OUT only when every
\\ gate passes.  An interrupted run, or one whose gates do not all pass, never
\\ reaches the move: the committed OUT is untouched and the partial output is
\\ left in TMP.
\\ ---------------------------------------------------------------------------

default(parisizemax, 3000000000);
getdef(name, dflt) = { my(s = getenv(name)); if(type(s) == "t_STR" && s != "", s, dflt) };
DSTR   = getdef("D", "");
if(DSTR == "", error("D is required: the curve is y^2 = x^3 - D x"));
D      = eval(DSTR);
PRIMES = eval(Str("[", getdef("W1PRIMES", "5,13,17"), "]"));
PREC   = eval(getdef("W1PREC", "600"));
OUT    = getdef("W1OUT", Str("../data/m2_w1_D", D, ".out"));
EPSBOUND = eval(getdef("EPSBOUND", "1000000"));
KFILE  = getdef("KAPPAFILE", Str("../data/m2_msd_D", D, ".out"));
TMP    = Str(OUT, ".partial");
default(realprecision, PREC);
APPRB = 10^(PREC\3);                           \\ denominator bound of the search
DMAX  = PREC\6;                                \\ largest denominator accepted, in digits
THR   = -2*PREC;                               \\ relative residual threshold, in bits

NGATE = 0; NGTOT = 0;
system(Str("rm -f ", TMP));
say(s) = { print(s); write(TMP, s); };
gate(name, ok) = { NGTOT++; if(ok, NGATE++); say(Str(name, if(ok, "PASS", "FAIL"))); };

E = ellinit([0,0,0,-D,0]);
N = ellglobalred(E)[1];
NF = N/4;                                      \\ N(f)
EE = valuation(NF, 2); MM = sqrtint(NF/2^EE);
G2 = E.c4/12;
w1 = E.omega[1];
Om = if(D > 0, w1, w1*(1+I)/2);
A  = Om*conj(Om)/Pi;
F0 = if(EE % 2 == 1, (1+I)^EE*MM, 2^(EE/2)*MM);
{my(s = getdef("F0", "")); if(s != "", F0 = eval(s));}
UPH = (conj(Om)/Om)*(F0/conj(F0));             \\ the phase u, a fourth root of unity
{UEX = if(abs(UPH - 1) < 1e-20, 1, if(abs(UPH + 1) < 1e-20, -1,
         if(abs(UPH - I) < 1e-20, I, if(abs(UPH + I) < 1e-20, -I, 0))));}

K  = bnfinit(x^2+1, 1);
H  = idealhnf(K, Mod(imag(F0)*x + real(F0), x^2+1));
AH = H[1,1]; BH = H[1,2]; DH = H[2,2];

say("=== m2_w1_family.gp : the algebraic bracket B_alg of (W1)/(W2) ===");
say(Str("pari version      : ", version()));
say(Str("curve             : E : y^2 = x^3 - ", D, "x   [0,0,0,", -D, ",0]   conductor ", N));
say(Str("N(f) = N/4        : ", NF, " = 2^", EE, " * ", MM, "^2"));
say(Str("f                 : (1+i)^", EE, " * (", MM, ")   generator f_0 = ", F0));
say(Str("idealhnf(K, f_0)  : ", H, "   norm ", AH*DH));
say(Str("period generator  : Omega = ", if(D > 0, "omega_1", "omega_1 (1+i)/2"), " = ", Om));
say(Str("phase u           : ", UEX, "   (conj(S) = u^{-(2p-1)} S)"));
say(Str("realprecision     : ", default(realprecision)));
say(Str("primes            : ", PRIMES));
say(Str("root number       : ", ellrootno(E)));
gate("conductor shape  : ", MM % 2 == 1 && MM^2 * 2^EE == NF && EE >= 3);
gate("f_0 generates f  : ", AH*DH == NF);
gate("u a 4th root     : ", UEX != 0);

\\ --------------------------- the fast slot machinery ------------------------
wptayv(P0, Q0, n) = {
  my(pv = vector(n+1)); pv[1] = P0; if(n >= 1, pv[2] = Q0);
  for(m = 0, n-2, my(s = 0); for(a = 0, m, s += pv[a+1]*pv[m-a+1]);
    pv[m+3] = (6*s - if(m == 0, G2/2, 0))/((m+2)*(m+1)));
  pv;
};
mkl0(NL) = {
  my(wp0 = ellwp(E, 'u + O('u^(NL+3))));
  my(zt0 = 1/'u - intformal(wp0 - 'u^-2));
  intformal(zt0 - 1/'u);
};
mkde(t, NN) = {
  my(P0 = ellwp(E,t), Q0 = ellwp(E,t,1)[2], Z0 = ellzeta(E,t));
  my(pv = wptayv(P0, Q0, NN), d = vector(NN+1), e = vector(NN+1));
  d[1] = Z0; for(m = 0, NN-1, d[m+2] = -pv[m+1]/(m+1));
  for(n = 1, NN+1, e[n] = d[n]/n);
  [d, e];
};
slotk0(t, de, k) = if(k == 0, de[1][1] - conj(t)/A, k! * de[1][k+1]);
slot0l(t, de, l, l0s) = {
  my(L = l+1, X = O('u^(L+1)));
  for(n = 1, L, X += (de[2][n] - polcoef(l0s,n,'u) - if(n == 1, conj(t)/A, 0))*'u^n);
  l! * polcoef(exp(X), L, 'u);
};
slotkl(t, de, k, l, l0s) = {
  my(KW = l+1, Xm = vector(KW), Ph = vector(KW+1));
  for(m = 1, KW,
    my(s = O('z^(k+1)));
    for(n = m, m+k, s += de[2][n]*binomial(n,m)*'z^(n-m));
    Xm[m] = s - polcoef(l0s,m,'u) - if(m == 1, conj(t)/A, 0));
  Ph[1] = 1 + O('z^(k+1));
  for(j = 1, KW, my(s = O('z^(k+1)));
    for(m = 1, j, s += m*Xm[m]*Ph[j-m+1]); Ph[j+1] = s/j);
  k! * l! * polcoef(Ph[KW+1], k, 'z);
};
{cslot(t, de, k, l, l0s) = if(l == 0, slotk0(t,de,k),
                           if(k == 0, slot0l(t,de,l,l0s), slotkl(t,de,k,l,l0s)));}

\\ --------------------------- the divisor and eps ---------------------------
isprimary(a,b) = ((a+b-1) % 4 == 0) && ((b-a+1) % 4 == 0);
\\ canonical representative of x + y i in the box of H, and its index
redx(u1, u2) = { my(y2 = ((u2 % DH) + DH) % DH, k = (u2 - y2)/DH);
                 [((u1 - k*BH) % AH + AH) % AH, y2]; };
classid(u1, u2) = { my(r = redx(u1,u2)); r[1]*DH + r[2] + 1; };
qrs4(fa, fb, m) = {
  my(p = fa^2 + fb^2, r = Mod(-fa, p) / Mod(fb, p), v = Mod(m, p)^((p - 1)/4));
  if(r^2 != Mod(-1, p), return(-2));
  for(k = 0, 3, if(v == r^k, return(k)));
  -1;
};
primgen(q) = {
  my(sol = qfbsolve(Qfb(1,0,1), q));
  if(sol == 0, return(0));
  my(a = sol[1], b = sol[2], fa = 0, fb = 0);
  for(k = 0, 3, if(isprimary(a,b), fa = a; fb = b; break); [a,b] = [-b,a]);
  if(fa == 0 && fb == 0, return(0));
  [fa, fb];
};
unitclass(q) = {
  my(g = primgen(q)); if(g == 0, return(0));
  my(fa = g[1], fb = g[2], ap = ellap(E,q), cand = [2*fa,-2*fb,-2*fa,2*fb], kk = 0, nm = 0);
  for(k = 1, 4, if(cand[k] == ap, kk = k; nm++));
  if(nm != 1, return(0));
  [fa, fb, kk-1];
};

epstab = vector(AH*DH);
NQ = 0; NQBAD = 0; NUND = 0;
{forprime(q = 5, EPSBOUND,
  if(q % 4 != 1 || MM % q == 0, next);
  my(v = unitclass(q)); if(v == 0, NUND++; next);
  my(id = classid(v[1], v[2]));
  if(epstab[id] == 0, epstab[id] = v[3] + 1,
     if(epstab[id] - 1 != v[3], NQBAD++));
  NQ++;
  my(mq = qrs4(v[1], v[2], D));
  if(!(mq >= 0 && (v[3] + mq) % 4 == 0), NQBAD++));}
say("");
{say(Str("eps: split primes tested to ", EPSBOUND, " : ", NQ,
         "   with no unique candidate: ", NUND,
         "   conflicts or closed-form failures: ", NQBAD));}
gate("eps consistent and (D/.)_4^-1 : ", NQBAD == 0);

CA = List(); CB = List(); CK = List(); NMISS = 0;
{for(u1 = 0, AH-1, for(u2 = 0, DH-1,
  if(!isprimary(u1,u2), next);
  if(gcd(u1^2 + u2^2, MM) != 1, next);
  my(id = classid(u1,u2));
  if(epstab[id] == 0, NMISS++; next);
  listput(CA,u1); listput(CB,u2); listput(CK, epstab[id]-1)));}
NC = #CA;
NRAY = bnrinit(K, H, 1).no;
{say(Str("classes of D_E    : ", NC, "   #Cl_f(K) = ", NRAY,
         "   unreached by the eps table: ", NMISS));}
gate("class count      : ", NC == NRAY && NMISS == 0);

\\ eps(conj g) = conj(eps g) on the divisor
{my(bad = 0);
 for(j = 1, NC, my(id = classid(CA[j], -CB[j]));
   if(epstab[id] == 0 || (epstab[id]-1 + CK[j]) % 4 != 0, bad++));
 gate("eps conjugation  : ", bad == 0);}

\\ --- gate: the quasi-period identity fixes Omega ----------------------------
{my(d1 = abs(2*ellzeta(E, Om/2) - conj(Om)/A),
    d2 = abs(2*ellzeta(E, I*Om/2) - conj(I*Om)/A),
    e1 = if(d1 == 0, -oo, exponent(d1)), e2 = if(d2 == 0, -oo, exponent(d2)));
 say("");
 say(Str("quasi-period      : |eta(Omega) - conj(Omega)/A| = 2^", e1,
         " , |eta(i Omega) - conj(i Omega)/A| = 2^", e2));
 gate("quasi-period     : ", e1 < -0.4*PREC && e2 < -0.4*PREC);}

\\ Recognition in K = Q(i): [re, im, relative residual in bits, denominator digits]
rec(x) = {
  my(re = bestappr(real(x), APPRB), im = bestappr(imag(x), APPRB));
  my(err = abs(x - (re + im*I)), sc = vecmax([abs(x), 1]));
  my(dd = vecmax([#digits(denominator(re)), #digits(denominator(im))]));
  [re, im, if(err == 0, -oo, exponent(err/sc)), dd];
};
{fmtq(q) = if(#digits(numerator(q)) > 40 || #digits(denominator(q)) > 20,
              Str("(", #digits(numerator(q)), " digits)/(", #digits(denominator(q)), " digits)"),
              Str(q));}

\\ --- gate: the fast slot routines against a full bivariate expansion --------
\\ ckl below is the bivariate routine of legacy/gp/m2_katz.gp, run at one class
\\ point with KZ = 8, KW = 9: it reaches the three slots (8,0), (4,4), (0,8) that
\\ p = 5 uses, and the whole 5 x 5 block.
KZ = 8; KW = 9; DEG = KZ + KW;
zero2() = matrix(KZ+1, KW+1);
one2()  = { my(M = zero2()); M[1,1] = 1; M; };
mul2(M, NN) = {
  my(R = zero2());
  for(a = 0, KZ, for(b = 0, KW,
    if(M[a+1,b+1] == 0, next);
    for(c = 0, KZ-a, for(d = 0, KW-b,
      R[a+c+1, b+d+1] += M[a+1,b+1]*NN[c+1,d+1]))));
  R;
};
exp2(X) = { my(R = one2(), T = one2()); for(j = 1, DEG+1, T = mul2(T,X)/j; R += T); R; };
subzw(S) = { my(R = zero2()); for(a = 0, KZ, for(b = 0, KW,
               R[a+1,b+1] = polcoef(S, a+b, 'u)*binomial(a+b, a))); R; };
subz(S)  = { my(R = zero2()); for(a = 0, KZ, R[a+1,1] = polcoef(S, a, 'u)); R; };
subw(S)  = { my(R = zero2()); for(b = 0, KW, R[1,b+1] = polcoef(S, b, 'u)); R; };
wptay(P0, Q0, n) = {
  my(pv = wptayv(P0, Q0, n));
  sum(j = 0, n, pv[j+1]*'u^j) + O('u^(n+1));
};
ckl(t, l0) = {
  my(P0 = ellwp(E,t), Q0 = ellwp(E,t,1)[2], Z0 = ellzeta(E,t));
  my(Lu = intformal(Z0 - intformal(wptay(P0, Q0, DEG+2))));
  my(X = subzw(Lu) - subz(Lu) - subw(l0));
  X[1,2] -= conj(t)/A;
  my(Ph = exp2(X), M = matrix(KZ+1, KW));
  for(kk = 0, KZ, for(ll = 0, KW-1, M[kk+1,ll+1] = kk!*ll!*Ph[kk+1,ll+2]));
  M;
};
say("");
say("--- gate: the fast slot routines against the full bivariate expansion ---");
{my(l0s = mkl0(DEG+2), t = (CA[1] + CB[1]*I)*Om/F0, de = mkde(t, DEG+2), bad = 0, worst = -oo);
 my(M = ckl(t, l0s), sl = [[0,0]]);
 for(kk = 0, 4, for(ll = 0, 4, sl = concat(sl, [[kk,ll]])));
 sl = concat(sl, [[8,0],[4,4],[0,8]]);
 for(s = 2, #sl,
   my(kk = sl[s][1], ll = sl[s][2]);
   my(g = cslot(t, de, kk, ll, l0s), r = M[kk+1,ll+1], d = abs(g - r));
   my(sc = vecmax([abs(r), 1]), ex = if(d == 0, -oo, exponent(d/sc)));
   if(ex > worst, worst = ex);
   if(ex > -0.4*PREC, bad++; say(Str("  MISMATCH c_{", kk, ",", ll, "} at 2^", ex))));
 say(Str("  28 coefficients at one class point, worst relative deviation 2^", worst));
 gate("bivariate check  : ", bad == 0);}

\\ --- gate: for D = 56, the fourteen reference class sums of gp/m2_w1.gp -----
{if(D == 56,
 my(l0s = mkl0(11), SW = matrix(5,5), bad = 0);
 for(j = 1, NC,
   my(t = (CA[j] + CB[j]*I)*Om/F0, ep = I^CK[j], de = mkde(t, 8));
   for(kk = 0, 4, for(ll = 0, 4,
     SW[kk+1,ll+1] += ep^(-(kk+ll+1)) * cslot(t, de, kk, ll, l0s))));
 my(ref = [[0,0,0], [1,0,-3584], [0,1,-32], [2,0,451584], [1,1,0], [0,2,-144],
           [3,1,3612672], [2,3,-24832/7], [4,4,3686400/7], [0,3,9/35],
           [0,4,79200/49], [1,4,-5168/7], [4,1,-1037238272], [3,0,-68812800]]);
 for(r = 1, #ref,
   my(kk = ref[r][1], ll = ref[r][2], v = ref[r][3], got = SW[kk+1,ll+1]);
   my(d = abs(got - v));
   if(d != 0 && exponent(d/vecmax([abs(v),1])) > -1000, bad++;
      say(Str("  MISMATCH S[", kk, ",", ll, "]: expected ", v, " got ", got))));
 say("");
 say(Str("  D = 56 reference class sums checked: 14, mismatches: ", bad));
 gate("D = 56 reference : ", bad == 0));}

\\ --------------------------- kappa(p) from the MSD side ---------------------
KAPPA = List();
{my(ls = externstr(Str("grep '^KAPPA ' ", KFILE, " 2>/dev/null")));
 for(j = 1, #ls, my(w = strsplit(ls[j], " "), v = List());
   for(k = 1, #w, if(w[k] != "", listput(v, w[k])));
   if(#v >= 3, listput(KAPPA, [eval(v[2]), if(v[3] == "NA", 0, eval(v[3]))])));}
kapof(p) = { my(r = -1); for(j = 1, #KAPPA, if(KAPPA[j][1] == p, r = KAPPA[j][2])); r; };

\\ --------------------------- the per-prime computation ---------------------
say("");
say("--- B_alg per prime ---");
say(Str("kappa(p) is read from ", KFILE, " (MSD normalisation); (W2) predicts"));
say("v_p(B_alg) = 2 exactly when kappa(p) != 0, and v_p(B_alg) >= 3 when it is 0.");
say(Str("kappa lines found : ", #KAPPA));

{for(r = 1, #PRIMES,
  my(p = PRIMES[r], t0 = getabstime());
  if(p % 4 != 1 || MM % p == 0,
     say(Str("p = ", p, " : not a split prime of good reduction; skipped")); next);
  my(NMAX = 2*p-2, l0s = mkl0(NMAX+3));
  my(S1 = 0, S2 = 0, S3 = 0);
  for(j = 1, NC,
    my(t = (CA[j] + CB[j]*I)*Om/F0, wt = I^(-CK[j]*(2*p-1)), de = mkde(t, NMAX));
    S1 += wt*slotk0(t, de, 2*p-2);
    S2 += wt*slotkl(t, de, p-1, p-1, l0s);
    S3 += wt*slot0l(t, de, 2*p-2, l0s));
  my(r1 = rec(S1), r2 = rec(S2), r3 = rec(S3));
  my(ex = (r1[3] < THR) && (r2[3] < THR) && (r3[3] < THR));
  my(ht = (r1[4] <= DMAX) && (r2[4] <= DMAX) && (r3[4] <= DMAX));
  \\ the conjugation relation conj(S) = u^{-(2p-1)} S
  my(uk = UEX^(-((2*p-1) % 4)), cj = 1);
  for(s = 1, 3, my(S = [S1,S2,S3][s]);
    if(abs(conj(S) - uk*S) > abs(S)*2.0^THR, cj = 0));
  my(pi_ok = 1);
  for(s = 1, 3, my(w = [r1,r2,r3][s]);
    if(denominator(w[1]) % p == 0 || denominator(w[2]) % p == 0, pi_ok = 0));
  \\ the fp-labelling and psi_E(fp)
  my(g = primgen(p), fa = g[1], fb = g[2]);
  if(fb < 0, fb = -fb);
  my(ipm = lift(Mod(-fa,p)/Mod(fb,p)), NP = 4*p+12);
  my(ip = sqrt(-1 + O(p^NP))); if(lift(ip + O(p^1)) != ipm, ip = -ip);
  my(ck = epstab[classid(fa,fb)] - 1);
  my(pia = ip^ck * (fa + fb*ip));
  my(nrm = pia * (ip^(-ck)) * (fa - fb*ip));
  my(lab_ok = (valuation(pia,p) == 1) && (lift(nrm + O(p^5)) == p));
  my(KK = 2*p-1);
  my(E1 = (1 - pia^KK/p^(2*p-1))*(1 - pia^KK/p), E2 = (1 - pia^KK/p^p)^2);
  my(E3 = (1 - pia^KK/p)*(1 - pia^KK/p^(2*p-1)));
  my(P1 = r1[1] + r1[2]*ip, P2 = r2[1] + r2[2]*ip, P3 = r3[1] + r3[2]*ip);
  my(B = E1*P1 - 2*E2*NF^(p-1)*P2 + E3*NF^(2*p-2)*P3);
  my(vB = valuation(B + O(p^8), p));
  my(kp = kapof(p), pred = if(kp < 0, -1, if(kp != 0, 2, 3)));
  \\ the residue identity (cor:residue): f_0 omega_E through i |-> i_p
  my(uK = (real(F0) + imag(F0)*ip) * if(D > 0, 2, 1 - ip), apv = ellap(E, p));
  my(predk = lift(Mod(lift(B/p^2/uK/apv^2 + O(p)), p)));
  say("");
  say(Str("p = ", p, "   fp = (", fa, " + ", fb, "i)   i_p = ", ipm,
          "   eps(pi) = i^", ck, "   [labelling ", if(lab_ok,"OK","BAD"), "]"));
  say(Str("   S[2p-2,0]  = ", fmtq(r1[1]), " + ", fmtq(r1[2]),
          " i   residual 2^", r1[3], "   denominator ", r1[4], " digits"));
  say(Str("   S[p-1,p-1] = ", fmtq(r2[1]), " + ", fmtq(r2[2]),
          " i   residual 2^", r2[3], "   denominator ", r2[4], " digits"));
  say(Str("   S[0,2p-2]  = ", fmtq(r3[1]), " + ", fmtq(r3[2]),
          " i   residual 2^", r3[3], "   denominator ", r3[4], " digits"));
  say(Str("   in Q(i) ", ex, "   denominators under 10^", DMAX, " ", ht,
          "   conj(S) = u^{-(2p-1)} S ", cj, "   denominators prime to p ", pi_ok));
  say(Str("   E(2p-2,0) = ", E1 + O(p^3), "    E(p-1,p-1) = ", E2 + O(p^3)));
  say(Str("   term valuations : ", valuation(E1*P1 + O(p^8), p), " ",
          valuation(2*E2*NF^(p-1)*P2 + O(p^8), p), " ",
          valuation(E3*NF^(2*p-2)*P3 + O(p^8), p)));
  say(Str("   v_p(B_alg) = ", vB, "   B_alg = ", B + O(p^(vB+2))));
  if(vB == 2, say(Str("   p^{-2} B_alg mod p = ", lift(B/p^2 + O(p)),
                      "     [alpha^2 mod p = ",
                      lift(Mod(lift((1/(pia/p))^2 + O(p)), p)), "]")));
  say(Str("   kappa(p) = ", if(kp < 0, "not tabulated", kp),
          "   predicted v_p(B_alg) = ", if(pred < 0, "n/a", if(pred == 2, "2 exactly", ">= 3")),
          "   -> ", if(pred < 0, "no comparison",
                       if((pred == 2 && vB == 2) || (pred == 3 && vB >= 3), "AGREE", "MISMATCH"))));
  say(Str("   predicted kappa(p) = ", predk,
          "   ((f_0 omega_E)^{-1} a_p^{-2} p^{-2} B_alg mod p, f_0 omega_E mod p = ",
          lift(uK + O(p)), ", a_p = ", apv, ")"));
  say(Str("   (", round((getabstime()-t0)/100)/10., " s)"));
  gate(Str("  p = ", p, " exactness   : "), ex && ht && cj && pi_ok && lab_ok);
  gate(Str("  p = ", p, " v>=2 (W1)   : "), vB >= 2);
  if(pred > 0, gate(Str("  p = ", p, " vs kappa(p) : "),
                    (pred == 2 && vB == 2) || (pred == 3 && vB >= 3)),
     say(Str("  p = ", p, " vs kappa(p) : SKIPPED (no KAPPA line in ", KFILE, ")")));
  if(kp >= 0, gate(Str("  p = ", p, " residue     : "), predk == kp)));}

say("");
say(Str("gates passed      : ", NGATE, " of ", NGTOT));
{if(NGATE == NGTOT,
    system(Str("mv -f ", TMP, " ", OUT)); print("M2W1DONE"),
    print(OUT, " left unchanged; partial output in ", TMP, ".");
    print("M2W1INCOMPLETE"));}
quit
