\\ m2_katz.gp -- the p-adic side of the criterion class, for E: y^2 = x^3 - 56x.
\\ ---------------------------------------------------------------------------
\\ Task C1a of project_management/SINNOT_HYPOTHESIS_PLAN.md.  Companion note:
\\ project_management/SINNOT_C1A_NOTE.md.  Bannai--Kobayashi (BK) is cited in
\\ Duke numbering (DMJ 153 (2010)) throughout, as the paper does.
\\
\\ WHAT THIS SCRIPT COMPUTES
\\   (1) The Kronecker-theta jet package in BK's own indexing, built from the
\\       theta function itself rather than from the closed forms, and checked
\\       against eq:EKclosed at all 384 points of D_E.
\\   (2) The BK-indexed class sums
\\           S[k,l] = sum_g eps(g)^{-(k+l+1)} c_{k,l}(t_g),
\\       where c_{k,l}(t) is the (z^k w^l/(k! l!))-coefficient of
\\       Theta_{t,0}(z,w) - 1/w.  By BK Prop. 3.1/3.3 these are the plain
\\       moments of the two-variable measure, up to the p-adic period:
\\           int x^k y^l d mu  =  Omega_p^{k+l} S[k,l].
\\       Through c_{k,l} = (-1)^{k+l} k! e*_{l,k+1}/A^l these are the paper's
\\       S_{a,b} of numerics.tex re-indexed; the script checks all six.
\\   (3) The same sums in the central-twist (BK Prop. 3.13) normalisation,
\\       sum over generators with weight eps(alpha), and the mu_K selection
\\       rule relating the two.
\\   (4) Per split prime: the eligibility conditions, the labelling of fp by
\\       the embedding iota_p, and the obstruction that stops the assembly --
\\       the p-adic period Omega_p of BK p. 272 lies in W^x and in no finite
\\       unramified extension of Z_p.
\\
\\ WHAT IT DOES NOT COMPUTE
\\   p^{-2} M_2(fp) mod m_W itself.  See section 8 of the companion note: the
\\   assembly needs Omega_p to precision p^3, and Frob(Omega_p)/Omega_p is the
\\   unit root alpha, which is not a root of unity.  This script produces the
\\   archimedean half of the input and certifies the conventions; the p-adic
\\   half is blocked, and the script says so rather than guessing.
\\
\\ THE REDUCTION THE OUTPUT IS ORGANISED AROUND
\\   With (x,y) the local unit coordinates at fp, fpbar and <.> the principal
\\   unit part, eq:M2moments reads M_2(fp) = int (<x> + <y> - 2)^2 d mu_psi.
\\   BK Def. 3.8 inverts the second leg, so in BK's coordinates the integrand
\\   is (<x> + <y>^{-1} - 2)^2.  On Zp^x x Zp^x write <x> = 1+pu, <y> = 1+pv.
\\   Then <x> + <y>^{-1} - 2 = p(u-v) + p^2 v^2 + O(p^3), so
\\       M_2(fp) = p^2 int_{Zp^x x Zp^x} (u-v)^2 d mu  +  O(p^3),
\\   that is
\\       p^{-2} M_2(fp) = Omega_p p^{-2} int_{Zp^x x Zp^x} (<x>-<y>)^2 d mu
\\   modulo m_W.  Only the three second-order twisted moments survive; the six
\\   slots of eq:M2moments enter only through that square.
\\
\\ CONVENTIONS (identical to gp/deltaE.gp of the paper's code; see numerics.tex)
\\   - lattice Gamma = w1*Z[i], A = w1^2/Pi, s2 = 0 (checked below), so the
\\     BK reduced theta is sigma and Theta(z,w) = sigma(z+w)/(sigma(z)sigma(w)).
\\   - Theta_{t,0}(z,w) = exp(-w*conj(t)/A) sigma(z+w+t)/(sigma(z+t) sigma(w)).
\\   - psi_E((alpha)) = eps(alpha) alpha on primary alpha == 1 mod (2+2i);
\\     eps = (56/.)_4^{-1}, read off from a_p as in deltaE.gp.
\\   - t_g = g*w1/56 over the 384 primary classes mod 56 prime to ff.
\\   - fp-labelling: pi = a+b*i is the primary generator with b > 0, fp := (pi),
\\     and iota_p is fixed by i |-> i_p, the square root of -1 in Z_p with
\\     i_p = -a/b mod p.  Then iota_p(pi) = 0 mod p, so fp = ker(iota_p) as it
\\     must be.  Every S[k,l] below is rational, so iota_p acts trivially on the
\\     moment data; it enters only the Euler factors and the translation weights.
\\
\\ Run from this directory:  gp -q m2_katz.gp        (about 15 seconds)
\\ Output: m2_katz.out
\\ ---------------------------------------------------------------------------

default(parisizemax, 4000000000);
default(realprecision, 400);

OUT = "m2_katz.out";
TMP = "m2_katz.out.partial";
system(Str("rm -f ", TMP));
NGATE = 0;                   \\ gates passed
say(s) = { print(s); write(TMP, s); };

E  = ellinit([0,0,0,-56,0]);
w1 = E.omega[1];
A  = w1^2/Pi;
G2 = E.c4/12;
G3 = E.c6/216;

say("=== m2_katz.gp : the p-adic side of the criterion class, C1a ===");
say(Str("pari version      : ", version()));
say("curve             : E : y^2 = x^3 - 56x   [0,0,0,-56,0]");
say(Str("conductor         : ", ellglobalred(E)[1]));
say(Str("realprecision     : ", default(realprecision)));
say(Str("g2, g3            : ", G2, ", ", G3, "   (g3 = 0 : lemniscatic)"));

\\ --- gate 1: s2 = 0, so the BK reduced theta is sigma -------------------------
\\ s2 = e*_{0,2}(0,0) = lim_s sum' gamma^{-2}|gamma|^{-2s}.  numerics.tex proves
\\ it vanishes by the i-symmetry of the lattice; we confirm numerically that the
\\ Weierstrass sigma of PARI carries no quasi-period correction, by testing the
\\ quasi-period relation eta(gamma) = conj(gamma)/A on the two basic periods.
{my(e1 = ellzeta(E, w1/2)*2, e2 = ellzeta(E, E.omega[2]/2)*2,
    d1 = abs(e1 - conj(w1)/A), d2 = abs(e2 - conj(E.omega[2])/A));
 say(Str("s2 = 0 gate       : |eta(w1) - conj(w1)/A| = 2^",
         if(d1 == 0, "-oo", exponent(d1)),
         " , |eta(w2) - conj(w2)/A| = 2^", if(d2 == 0, "-oo", exponent(d2))));
 if(exponent(d1) < -1000 && exponent(d2) < -1000,
    NGATE++; say("                  : PASS"),
    say("                  : FAIL -- theta is not sigma; stop."));}

\\ --- the Kronecker theta jet, from the theta function ------------------------
KMAX = 4;                    \\ we tabulate 0 <= k,l <= KMAX
KZ = KMAX; KW = KMAX + 1; DEG = KZ + KW;

zero2() = matrix(KZ+1, KW+1);
one2()  = { my(M = zero2()); M[1,1] = 1; M; };
mul2(M, N) = {
  my(R = zero2());
  for(a = 0, KZ, for(b = 0, KW,
    if(M[a+1,b+1] == 0, next);
    for(c = 0, KZ-a, for(d = 0, KW-b,
      R[a+c+1, b+d+1] += M[a+1,b+1]*N[c+1,d+1]))));
  R;
};
exp2(X) = { my(R = one2(), T = one2()); for(j = 1, DEG+1, T = mul2(T,X)/j; R += T); R; };
\\ substitutions of a univariate series S('u) into u = z+w, u = z, u = w
subzw(S) = { my(R = zero2()); for(a = 0, KZ, for(b = 0, KW,
               R[a+1,b+1] = polcoef(S, a+b, 'u)*binomial(a+b, a))); R; };
subz(S)  = { my(R = zero2()); for(a = 0, KZ, R[a+1,1] = polcoef(S, a, 'u)); R; };
subw(S)  = { my(R = zero2()); for(b = 0, KW, R[1,b+1] = polcoef(S, b, 'u)); R; };

\\ l0(u) = log(sigma(u)/u) at the origin: exact rational coefficients
wp0 = ellwp(E, 'u + O('u^(DEG+4)));
zt0 = 1/'u - intformal(wp0 - 'u^-2);
l0  = intformal(zt0 - 1/'u);

\\ Taylor expansion of wp at t from the ODE wp'' = 6 wp^2 - g2/2
wptay(P0, Q0, n) = {
  my(p = vector(n+1)); p[1] = P0; if(n >= 1, p[2] = Q0);
  for(m = 0, n-2,
    my(s = 0); for(a = 0, m, s += p[a+1]*p[m-a+1]);
    p[m+3] = (6*s - if(m == 0, G2/2, 0))/((m+2)*(m+1)));
  sum(j = 0, n, p[j+1]*'u^j) + O('u^(n+1));
};

\\ c_{k,l}(t) = k! l! [z^k w^l] (Theta_{t,0}(z,w) - 1/w),  0 <= k <= KZ, 0 <= l <= KW-1
ckl(t) = {
  my(P0 = ellwp(E,t), Q0 = ellwp(E,t,1)[2], Z0 = ellzeta(E,t));
  my(Lu = intformal(Z0 - intformal(wptay(P0, Q0, DEG+2))));   \\ log sigma(t+u) - log sigma(t)
  my(X = subzw(Lu) - subz(Lu) - subw(l0));
  X[1,2] -= conj(t)/A;                                        \\ the exp(-w conj(t)/A) factor
  my(Ph = exp2(X), M = matrix(KZ+1, KW));
  for(kk = 0, KZ, for(ll = 0, KW-1, M[kk+1,ll+1] = kk!*ll!*Ph[kk+1,ll+2]));
  M;
};

\\ --- the 384 primary classes and the unit character eps ----------------------
isprimary(a,b) = ((a+b-1) % 4 == 0) && ((b-a+1) % 4 == 0);
classid(a,b)   = ((a % 56) + 56) % 56 * 56 + ((b % 56) + 56) % 56;
epstab = vector(56*56);
QF = Qfb(1,0,1);
{forprime(q = 5, 60000,
  if(q % 4 != 1 || q == 7, next);
  my(sol = qfbsolve(QF, q)); if(sol == 0, next);
  my(a = sol[1], b = sol[2], fa = 0, fb = 0);
  for(k = 0, 3, if(isprimary(a,b), fa = a; fb = b; break); [a,b] = [-b,a]);
  my(ap = ellap(E,q), cand = [2*fa, -2*fb, -2*fa, 2*fb], kk = 0, nm = 0);
  for(k = 1, 4, if(cand[k] == ap, kk = k; nm++));
  if(nm != 1, next);
  my(id = classid(fa,fb)); if(epstab[id] == 0, epstab[id] = kk));}
CA = List(); CB = List(); CK = List();
{for(a = 0, 55, for(b = 0, 55,
  if(!isprimary(a,b), next);
  if((a+b) % 2 == 0, next);
  if(a % 7 == 0 && b % 7 == 0, next);
  my(id = classid(a,b));
  if(epstab[id] == 0, say(Str("MISSING CLASS ", [a,b])); next);
  listput(CA,a); listput(CB,b); listput(CK, epstab[id]-1)));}
NC = #CA;
say(Str("classes of D_E    : ", NC, "   (expect 384)"));
if(NC == 384, NGATE++; say("                  : PASS"), say("                  : FAIL"));

\\ --- gate 2: the theta jet reproduces eq:EKclosed at every point of D_E ------
\\ e*_{0,1} = E1*, e*_{0,2} = wp, e*_{1,1} = -(A/2)(E1*^2-wp), e*_{0,3} = -wp'/2,
\\ e*_{1,2} = -A(E1* wp + wp'/2), e*_{2,1} = (A^2/3)(E1*^3 - 3 E1* wp - wp'),
\\ and c_{k,l} = (-1)^{k+l} k! e*_{l,k+1}/A^l, so the six comparisons below.
CKL = vector(NC);
{my(worst = -oo, t0 = getabstime());
 for(j = 1, NC,
   my(t = (CA[j] + CB[j]*I)*w1/56);
   my(P0 = ellwp(E,t), Q0 = ellwp(E,t,1)[2], Z0 = ellzeta(E,t));
   my(E1 = Z0 - conj(t)/A, M = ckl(t));
   CKL[j] = M;
   my(sc = vecmax([abs(E1), abs(P0), abs(Q0), 1]));
   my(d = [M[1,1] - E1,
           M[2,1] + P0,
           M[1,2] - (E1^2 - P0)/2,
           M[3,1] + Q0,
           M[2,2] + (E1*P0 + Q0/2),
           M[1,3] - (E1^3 - 3*E1*P0 - Q0)/3]);
   for(r = 1, 6, my(e = abs(d[r])/sc); if(e != 0 && exponent(e) > worst, worst = exponent(e))));
 say(Str("eq:EKclosed gate  : worst relative discrepancy over 384 points and 6 slots = 2^", worst));
 if(worst < -1000, NGATE++; say("                  : PASS"), say("                  : FAIL"));
 say(Str("                  : (", round((getabstime()-t0)/100)/10., " s)"));}

\\ --- the class sums, in both normalisations ---------------------------------
\\ SY[k,l]  = sum over the 384 classes of eps(g)^{-(k+l+1)} c_{k,l}(t_g).
\\            This is BK Def. 3.6 / Yager, and eq:jetpackage: the parameter is
\\            eps(g) t_g and e*_{a,b}(eps(g)t_g,0) = eps(g)^{-(a+b)}e*_{a,b}(t_g,0).
\\ SC[k,l]  = sum over all 1536 generators of eps(alpha) c_{k,l}(t_alpha).
\\            This is BK Prop. 3.13: the central (eps-)twist.  It is computed
\\            here by evaluating the theta jet at all four unit multiples u t_g
\\            separately, so that its agreement with the mu_K selection rule is
\\            a test of the scaling law e*_{a,b}(ut) = conj(u)^{a+b} e*_{a,b}(t)
\\            and not a restatement of it.
SY = matrix(KZ+1, KW); SC = matrix(KZ+1, KW);
{for(j = 1, NC,
   my(epsg = I^CK[j], M = CKL[j], t = (CA[j] + CB[j]*I)*w1/56);
   for(kk = 0, KZ, for(ll = 0, KW-1,
     SY[kk+1,ll+1] += epsg^(-(kk+ll+1)) * M[kk+1,ll+1]));
   for(m = 0, 3,
     my(u = I^m, Mu = if(m == 0, M, ckl(u*t)), epsu = conj(u)*epsg);
     for(kk = 0, KZ, for(ll = 0, KW-1,
       SC[kk+1,ll+1] += epsu * Mu[kk+1,ll+1]))));}

\\ exactness gate: recognise in Q(i) and demand a residual below 2^-1000
rec(x) = {
  my(re = bestappr(real(x), 10^60), im = bestappr(imag(x), 10^60));
  my(err = abs(x - (re + im*I)));
  [re, im, if(err == 0, -oo, exponent(err))];
};
fmt(r) = if(r[2] == 0, Str(r[1]), Str(r[1], " + (", r[2], ")*i"));

say("");
say("--- BK-indexed class sums  S[k,l] = sum_g eps(g)^{-(k+l+1)} c_{k,l}(t_g) ---");
say("    (BK Prop. 3.1/3.3:  int x^k y^l d mu = Omega_p^{k+l} S[k,l])");
{my(bad = 0);
 for(kk = 0, KZ, for(ll = 0, KW-1,
   my(r = rec(SY[kk+1,ll+1]));
   if(r[3] > -1000, bad++);
   say(Str("S[", kk, ",", ll, "] = ", fmt(r), "        residual 2^", r[3]))));
 say(Str("exactness gate    : ", if(bad == 0, "PASS", Str("FAIL on ", bad, " entries"))));
 if(bad == 0, NGATE++);}

say("");
say("--- the same sums in the central-twist normalisation (BK Prop. 3.13) ---");
say("    SC[k,l] = sum_{alpha in (O_K/f)^x} eps(alpha) c_{k,l}(t_alpha)");
say("    mu_K selection rule: SC[k,l] = 4 S[k,l] if 4 | k+l+2, and 0 otherwise");
{my(bad = 0, worst = -oo);
 for(kk = 0, KZ, for(ll = 0, KW-1,
   my(r = rec(SC[kk+1,ll+1]), pred = if((kk+ll+2) % 4 == 0, 4*SY[kk+1,ll+1], 0));
   my(d = abs(SC[kk+1,ll+1] - pred), sc = vecmax([abs(pred), 1]));
   if(d != 0 && exponent(d/sc) > worst, worst = exponent(d/sc));
   if(d != 0 && exponent(d/sc) > -1000, bad++);
   say(Str("SC[", kk, ",", ll, "] = ", fmt(r)))));
 say(Str("selection rule    : worst relative discrepancy from the rule = 2^", worst));
 say(Str("                  : ", if(bad == 0, "PASS", Str("FAIL on ", bad, " slots"))));
 if(bad == 0, NGATE++);}

\\ --- gate 3: the mandatory pipeline zero, m_{0,0} = 0 ------------------------
say("");
{my(z = SY[1,1], e = if(z == 0, -oo, exponent(abs(z))));
 say(Str("m_{0,0} zero gate : S[0,0] = ", z, " , log2|S[0,0]| = ", e));
 say("                  : S[0,0] is the mass int d mu_psi, = the paper's S_{0,1},");
 say("                  : a unit multiple of L(psibar_E,1) = L(E,1) = 0 (rank two).");
 if(e < -1000, NGATE++; say("                  : PASS at full working precision"),
    say("                  : FAIL -- the pipeline is wrong; stop."));}

\\ --- gate 4: agreement with the S_{a,b} table of numerics.tex ---------------
\\ dictionary: c_{k,l} = (-1)^{k+l} k! e*_{l,k+1}/A^l, so with the class weight
\\     S[k,l] = (-1)^{k+l} k! * S_{l,k+1}^{paper} / A^l .
say("");
say("--- agreement with the S_{a,b} table of numerics.tex ---");
{my(tab = [[0,1,0], [0,2,3584], [1,1,32], [0,3,225792], [1,2,0], [2,1,-144]], bad = 0);
 for(r = 1, #tab,
   my(a = tab[r][1], b = tab[r][2], val = tab[r][3]);   \\ paper S_{a,b} / A^a
   my(kk = b-1, ll = a, pred = (-1)^(kk+ll) * kk! * val, got = SY[kk+1,ll+1]);
   my(d = abs(got - pred));
   if(d != 0 && exponent(d) > -1000, bad++);
   say(Str("paper S_{", a, ",", b, "}/A^", a, " = ", val,
           "   ->  S[", kk, ",", ll, "] predicted ", pred,
           " , computed ", rec(got)[1],
           if(d == 0, "   exact", Str("   diff 2^", exponent(d))))));
 say(Str("dictionary gate   : ", if(bad == 0, "PASS", Str("FAIL on ", bad, " slots"))));
 if(bad == 0, NGATE++);}

\\ --- per-prime data ---------------------------------------------------------
say("");
say("--- split primes: eligibility, the fp-labelling, and the Omega_p obstruction ---");
say("eligibility: p = 1 mod 4 (split), p not in {2,7} (good), p prime to 384 = #Cl_f(K),");
say("             a_p not = 1 mod p (not anomalous), p not in S_E (S_E is inside {2,3,7}).");
\\ The six slots of eq:M2moments sit at BK index (k,l) = (a,-b): the second leg
\\ is inverted by BK Def. 3.8.  Only m_{0,0}, m_{1,0}, m_{2,0} have l >= 0 and so
\\ appear in the table above; m_{0,1}, m_{1,1}, m_{0,2} sit at l = -1,-1,-2 and
\\ are the p-adic limits of BK Prop. 3.13.  WIN lists the three that are in the
\\ table, as (k,l).
WIN = [[0,0], [1,0], [2,0]];
PRIMES = [5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113];
{my(badal = 0);
 for(r = 1, #PRIMES,
  my(p = PRIMES[r]);
  my(spl = (p % 4 == 1), good = (p != 2 && p != 7), cl = (384 % p != 0));
  my(ap = ellap(E,p), anom = ((ap - 1) % p == 0));
  my(se = (p != 2 && p != 3 && p != 7));
  \\ the primary generator of a prime above p; the conjugate of a primary
  \\ element is primary, so fix the branch by b > 0 and call that prime fp
  my(sol = qfbsolve(QF, p), a = sol[1], b = sol[2], fa = 0, fb = 0);
  for(k = 0, 3, if(isprimary(a,b), fa = a; fb = b; break); [a,b] = [-b,a]);
  if(fb < 0, fb = -fb);                          \\ pi = fa + fb*i with fb > 0
  my(ip = lift(Mod(-fa, p) / Mod(fb, p)));       \\ iota_p : i |-> ip
  my(ipok = (Mod(ip,p)^2 == Mod(-1,p)) && ((fa + fb*ip) % p == 0));
  my(ck = epstab[classid(fa, fb)] - 1);          \\ eps(pi) = i^ck
  \\ unit root alpha of X^2 - a_p X + p over Z_p
  my(al = 0, rts = polrootspadic('x^2 - ap*'x + p, p, 10));
  for(k = 1, #rts, if(valuation(rts[k], p) == 0, al = rts[k]));
  my(isroot1 = (al^(p-1) == 1 + O(p^8)));
  my(d3 = znorder(Mod(lift(al + O(p^3)), p^3)));
  \\ consistency of the labelling: psi(fp) = eps(pi) pi has iota_p(psi(fp)) = 0
  \\ mod p, so the unit root must be iota_p of the conjugate.
  my(ip8 = lift(sqrt(-1 + O(p^8))));             \\ i_p to precision p^8, on the ip branch
  if(ip8 % p != ip, ip8 = p^8 - ip8);
  my(ipsi  = (Mod(ip8,p^8)^ck) * (Mod(fa,p^8) + Mod(fb,p^8)*Mod(ip8,p^8)));
  my(ipsib = (Mod(-ip8,p^8)^ck) * (Mod(fa,p^8) - Mod(fb,p^8)*Mod(ip8,p^8)));
  my(alok = (lift(ipsib) - lift(al + O(p^8))) % p^8 == 0);
  if(!alok, badal++);
  say(Str("p = ", p,
          " | split ", spl, " good ", good, " prime-to-384 ", cl,
          " a_p = ", ap, " anomalous ", anom, " outside S_E ", se,
          " | ELIGIBLE ", (spl && good && cl && !anom && se)));
  say(Str("      fp = (", fa, " + ", fb, "i) , iota_p : i -> ", ip, " mod ", p,
          "  [i_p^2 = -1 and iota_p(pi) = 0 mod p : ", ipok, "]",
          " , eps(pi) = i^", ck));
  say(Str("      psi(fp) = eps(pi) pi , iota_p(psi(fp)) = ", lift(ipsi) % p,
          " mod p (must be 0) ; unit root alpha = ", lift(al + O(p^1)), " mod ", p,
          " ; alpha = iota_p(conj psi(fp)) mod p^8 : ", alok));
  say(Str("      alpha^(p-1) = 1 : ", isroot1,
          "   ord(alpha) in (Z/p^3)^x = ", d3,
          "   [= the unramified degree the assembly would need]"));
  \\ the archimedean input, reduced: the six window slots mod p^5
  my(s = "      S[k,l] mod p^5, the l >= 0 window slots (k,l) : ");
  for(m = 1, #WIN,
    my(kk = WIN[m][1], ll = WIN[m][2], v = rec(SY[kk+1,ll+1])[1]);
    s = Str(s, "(", kk, ",", ll, ")=",
            if(denominator(v) % p == 0, "NOT p-INTEGRAL",
               lift(Mod(numerator(v), p^5)/Mod(denominator(v), p^5))),
            if(m < #WIN, "  ", "")));
  say(s));
 say(Str("alpha labelling   : ", if(badal == 0, "PASS at every prime listed",
                                    Str("FAIL at ", badal, " primes"))));
 if(badal == 0, NGATE++);}

say("");
say("--- the Omega_p obstruction (why p^{-2}M_2 is not assembled here) ---");
say("BK p. 272: Ehat = Gm-hat over W via eta_p(t) = exp[Omega_p^{-1} lambda(t)] - 1,");
say("with Omega_p in W^x a p-adic period.  For E/Q ordinary at p the Galois action");
say("on T_p(Ehat) is the cyclotomic character times the unramified character sending");
say("Frobenius to alpha^{-1}, so Frob(Omega_p)/Omega_p = alpha^{+-1}.  A solution of");
say("Frob(X) = cX with c in Z_p^x lies in W(F_{p^d})/p^N only if c^d = 1 mod p^N.");
say("The lines above show alpha^(p-1) != 1, so Omega_p lies in no finite unramified");
say("extension of Z_p; and the criterion class divides by p^2, so the assembly needs");
say("Omega_p mod p^3, hence unramified degree ord(alpha) in (Z/p^3)^x -- the last");
say("column above -- on top of the ramified Z_p[zeta_p] the level-p Fourier");
say("resolution of the Teichmueller twists needs.  That is the blocker.");

say("");
say(Str("gates passed      : ", NGATE, " of 8"));
{if(NGATE == 8,
   system(Str("mv -f ", TMP, " ", OUT));
   print("M2KATZDONE"),
   print("INCOMPLETE: ", NGATE, " of 8 gates passed; ", OUT, " left unchanged,");
   print("partial output in ", TMP, "."));}
quit
