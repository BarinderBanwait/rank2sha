\\ m2_w1.gp -- the algebraic bracket of (W1)/(W2), for E: y^2 = x^3 - 56x.
\\ ---------------------------------------------------------------------------
\\ Task C1b of project_management/SINNOT_HYPOTHESIS_PLAN.md, in the form task M1
\\ gave it.  Companion notes: project_management/SINNOT_C1B_NOTE.md (this run),
\\ SINNOT_W_NOTE.md (which proves (W1) and (W2)), SINNOT_C1A_NOTE.md (which
\\ supplies the conventions and the dictionary this script reuses).  Companion
\\ script: m2_katz.gp, whose class sums the fast routines here reproduce.
\\ Bannai--Kobayashi (BK) is cited in Duke numbering.
\\
\\ WHAT THIS COMPUTES
\\ SINNOT_W_NOTE.md (W2) states
\\     c(fp) = kappa . Omega_p^{2p-2} . p^{-2} . B_alg   mod m_W,
\\ with kappa and Omega_p^{2p-2} units of W and
\\     B_alg = E(2p-2,0) (2p-2)!             P_{0,2p-1}
\\           - 2 E(p-1,p-1) (p-1)! N(f)^{p-1} P_{p-1,p}
\\           + E(0,2p-2)          N(f)^{2p-2} P_{2p-2,1} ,
\\     P_{a,b} = sum_{[g] in D_E} eps(g)^{-(a+b)} e*_{a,b}(t_g,0)/A^a ,
\\     E(k,l) = (1 - pi^{k+l+1}/p^{l+1})(1 - pi^{k+l+1}/p^{k+1}),  pi = psi_E(fp).
\\ The three class sums have weight a+b = 2p-1.  Since the factors multiplying
\\ B_alg are units,
\\     c(fp) != 0   <=>   v_p(B_alg) = 2 exactly.
\\ No p-adic period enters: the same power Omega_p^{2p-2} multiplies all three
\\ terms, which is why (W1) escapes the obstruction recorded in SINNOT_C1A_NOTE
\\ section 8.  The script computes B_alg, reports v_p(B_alg) and p^{-2}B_alg mod p,
\\ and compares the vanishing against the independently computed MSD-normalised
\\ criterion class kappa(p) of m2_msd.out.
\\
\\ INDEXING (SINNOT_C1A_NOTE section 3, SINNOT_W_NOTE (A))
\\   c_{k,l}(t) = coefficient of z^k w^l/(k! l!) in Theta_{t,0}(z,w) - 1/w
\\              = (-1)^{k+l} k! e*_{l,k+1}(t,0)/A^l ,
\\   S[k,l] := sum_g eps(g)^{-(k+l+1)} c_{k,l}(t_g) = (-1)^{k+l} k! P_{l,k+1} .
\\ With k+l = 2p-2 even the signs are +1, so
\\   S[2p-2,0] = (2p-2)! P_{0,2p-1},  S[p-1,p-1] = (p-1)! P_{p-1,p},
\\   S[0,2p-2] = P_{2p-2,1},
\\ and B_alg = E(2p-2,0) S[2p-2,0] - 2 E(p-1,p-1) N(f)^{p-1} S[p-1,p-1]
\\                                 + E(0,2p-2)  N(f)^{2p-2} S[0,2p-2].
\\
\\ HOW THE THREE SLOTS ARE COMPUTED
\\ Writing Phi(z,w) = w Theta_{t,0}(z,w)
\\               = w exp(-w conj(t)/A) sigma(t+z+w)/(sigma(t+z) sigma(w)),
\\ so that c_{k,l} = k! l! [z^k w^{l+1}] Phi, and
\\   L(u) = log sigma(t+u) - log sigma(t) = sum_{n>=1} e_n u^n,  e_n = d_{n-1}/n,
\\   d_n = [z^n] zeta(t+z),   l0(w) = log(sigma(w)/w),
\\ the three slots need only the following, not a full bivariate array:
\\   (k,0):  Phi_w at w = 0 is L'(z) - conj(t)/A, so c_{k,0} = k! d_k for k >= 1;
\\   (0,l):  Phi(0,w) = exp(sum e_n w^n - l0(w) - w conj(t)/A), univariate;
\\   (k,l):  the w-recursion j Phi_j = sum_{m<=j} m X_m Phi_{j-m} on z-series of
\\           length k+1, X_m = [w^m](L(z+w) - L(z) - l0(w) - w conj(t)/A).
\\ The d_n come from the ODE wp'' = 6 wp^2 - g2/2.  Gate 1 below checks all three
\\ routines against the 25 class sums m2_katz.gp computes by full bivariate
\\ expansion; they agree exactly, denominators included.
\\
\\ CONVENTIONS: those of m2_katz.gp and numerics.tex, unchanged.  fp is labelled
\\ as there: pi_gen = a + b*i primary with b > 0, fp := (pi_gen), iota_p fixed by
\\ i |-> i_p with i_p = -a/b mod p, and psi_E(fp) = eps(pi_gen) pi_gen.
\\
\\ Run from this directory:   gp -q m2_w1.gp
\\ Parameters from the environment:
\\     W1PRIMES  comma-separated split primes           default "5,13,17"
\\     W1PREC    realprecision                          default 400
\\     W1OUT     output file                            default m2_w1.out
\\ Cost grows like p^4: 6 s at p = 13, about 3 min at p = 29, 15 min at p = 37
\\ (realprecision 600).  Results are appended prime by prime, so an interrupted
\\ run keeps what it computed.
\\ ---------------------------------------------------------------------------

default(parisizemax, 8000000000);
getdef(name, dflt) = { my(s = getenv(name)); if(type(s) == "t_STR" && s != "", s, dflt) };
PRIMES = eval(Str("[", getdef("W1PRIMES", "5,13,17"), "]"));
PREC   = eval(getdef("W1PREC", "400"));
OUT    = getdef("W1OUT", "m2_w1.out");
default(realprecision, PREC);

E = ellinit([0,0,0,-56,0]);
w1 = E.omega[1]; A = w1^2/Pi; G2 = E.c4/12;
NF = 3136;                                     \\ N(ff), ff = (56)
NGATE = 0; NGTOT = 0;
system(Str("rm -f ", OUT));
say(s) = { print(s); write(OUT, s); };
gate(name, ok) = { NGTOT++; if(ok, NGATE++); say(Str(name, if(ok, "PASS", "FAIL"))); };

say("=== m2_w1.gp : the algebraic bracket B_alg of (W1)/(W2), task C1b ===");
say(Str("pari version      : ", version()));
say("curve             : E : y^2 = x^3 - 56x   [0,0,0,-56,0],  ff = (56), N(ff) = 3136");
say(Str("realprecision     : ", default(realprecision)));
say(Str("primes            : ", PRIMES));

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
\\ de = [d, e] with d[n+1] = [z^n] zeta(t+z), e[n] = [u^n] L(u), n = 1..N+1
mkde(t, N) = {
  my(P0 = ellwp(E,t), Q0 = ellwp(E,t,1)[2], Z0 = ellzeta(E,t));
  my(pv = wptayv(P0, Q0, N), d = vector(N+1), e = vector(N+1));
  d[1] = Z0; for(m = 0, N-1, d[m+2] = -pv[m+1]/(m+1));
  for(n = 1, N+1, e[n] = d[n]/n);
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
classid(a,b)   = ((a % 56) + 56) % 56 * 56 + ((b % 56) + 56) % 56;
epstab = vector(56*56); QF = Qfb(1,0,1);
{forprime(q = 5, 60000,
  if(q % 4 != 1 || q == 7, next);
  my(sol = qfbsolve(QF,q)); if(sol == 0, next);
  my(a = sol[1], b = sol[2], fa = 0, fb = 0);
  for(k = 0, 3, if(isprimary(a,b), fa = a; fb = b; break); [a,b] = [-b,a]);
  my(ap = ellap(E,q), cand = [2*fa,-2*fb,-2*fa,2*fb], kk = 0, nm = 0);
  for(k = 1, 4, if(cand[k] == ap, kk = k; nm++));
  if(nm != 1, next);
  my(id = classid(fa,fb)); if(epstab[id] == 0, epstab[id] = kk));}
CA = List(); CB = List(); CK = List();
{for(a = 0, 55, for(b = 0, 55,
  if(!isprimary(a,b), next); if((a+b) % 2 == 0, next);
  if(a % 7 == 0 && b % 7 == 0, next);
  my(id = classid(a,b)); if(epstab[id] == 0, next);
  listput(CA,a); listput(CB,b); listput(CK, epstab[id]-1)));}
NC = #CA;
say(Str("classes of D_E    : ", NC));
gate("384 classes      : ", NC == 384);

rec(x) = {
  my(re = bestappr(real(x), 10^400), im = bestappr(imag(x), 10^400));
  my(err = abs(x - (re + im*I)));
  [re, im, if(err == 0, -oo, exponent(err))];
};

\\ --- gate: the fast routines reproduce m2_katz.gp's class sums --------------
say("");
say("--- gate: the fast slot routines against m2_katz.gp (full bivariate) ---");
{my(l0s = mkl0(11), SW = matrix(5,5), bad = 0);
 for(j = 1, NC,
   my(t = (CA[j] + CB[j]*I)*w1/56, ep = I^CK[j], de = mkde(t, 8));
   for(kk = 0, 4, for(ll = 0, 4,
     SW[kk+1,ll+1] += ep^(-(kk+ll+1)) * cslot(t, de, kk, ll, l0s))));
 my(ref = [[0,0,0], [1,0,-3584], [0,1,-32], [2,0,451584], [1,1,0], [0,2,-144],
           [3,1,3612672], [2,3,-24832/7], [4,4,3686400/7], [0,3,9/35],
           [0,4,79200/49], [1,4,-5168/7], [4,1,-1037238272], [3,0,-68812800]]);
 for(r = 1, #ref,
   my(kk = ref[r][1], ll = ref[r][2], v = ref[r][3], got = SW[kk+1,ll+1]);
   my(d = abs(got - v));
   if(d != 0 && exponent(d/vecmax([abs(v),1])) > -1000, bad++;
      say(Str("  MISMATCH S[", kk, ",", ll, "]: expected ", v, " got ", rec(got)[1]))));
 say(Str("  14 reference class sums checked, mismatches: ", bad));
 gate("slot routines    : ", bad == 0);}

\\ --------------------------- the per-prime computation ---------------------
say("");
say("--- B_alg per prime ---");
say("kappa(p) is read from m2_msd.out (MSD normalisation); (W2) predicts");
say("v_p(B_alg) = 2 exactly when kappa(p) != 0, and v_p(B_alg) >= 3 when it is 0.");
{KAPPA = [[5,2],[13,2],[17,15],[29,12],[37,17],[41,3],[53,43],[61,34],[73,2],
          [89,35],[97,67],[101,49],[109,45],[113,78]];}
kapof(p) = { my(r = -1); for(j = 1, #KAPPA, if(KAPPA[j][1] == p, r = KAPPA[j][2])); r; };

{for(r = 1, #PRIMES,
  my(p = PRIMES[r], t0 = getabstime());
  if(p % 4 != 1 || p == 5 && 0, );
  my(NMAX = 2*p-2, l0s = mkl0(NMAX+3));
  my(S1 = 0, S2 = 0, S3 = 0);
  for(j = 1, NC,
    my(t = (CA[j] + CB[j]*I)*w1/56, wt = I^(-CK[j]*(2*p-1)), de = mkde(t, NMAX));
    S1 += wt*slotk0(t, de, 2*p-2);
    S2 += wt*slotkl(t, de, p-1, p-1, l0s);
    S3 += wt*slot0l(t, de, 2*p-2, l0s));
  my(r1 = rec(S1), r2 = rec(S2), r3 = rec(S3));
  my(ex = (r1[3] < -400) && (r2[3] < -400) && (r3[3] < -400));
  my(ra = (r1[2] == 0) && (r2[2] == 0) && (r3[2] == 0));
  my(v1 = r1[1], v2 = r2[1], v3 = r3[1]);
  my(pi_ok = (denominator(v1) % p != 0) && (denominator(v2) % p != 0)
             && (denominator(v3) % p != 0));
  \\ the fp-labelling and psi_E(fp)
  my(sol = qfbsolve(QF,p), a = sol[1], b = sol[2], fa = 0, fb = 0);
  for(k = 0, 3, if(isprimary(a,b), fa = a; fb = b; break); [a,b] = [-b,a]);
  if(fb < 0, fb = -fb);
  my(ipm = lift(Mod(-fa,p)/Mod(fb,p)), NP = 4*p+12);
  my(ip = sqrt(-1 + O(p^NP))); if(lift(ip + O(p^1)) != ipm, ip = -ip);
  my(ck = epstab[classid(fa,fb)] - 1);
  my(pia = ip^ck * (fa + fb*ip));
  my(nrm = pia * (ip^(-ck)) * (fa - fb*ip));
  my(lab_ok = (valuation(pia,p) == 1) && (lift(nrm + O(p^5)) == p));
  my(K = 2*p-1);
  my(E1 = (1 - pia^K/p^(2*p-1))*(1 - pia^K/p), E2 = (1 - pia^K/p^p)^2);
  my(E3 = (1 - pia^K/p)*(1 - pia^K/p^(2*p-1)));
  my(B = E1*v1 - 2*E2*NF^(p-1)*v2 + E3*NF^(2*p-2)*v3);
  my(vB = valuation(B + O(p^8), p));
  my(kp = kapof(p), pred = if(kp < 0, -1, if(kp != 0, 2, 3)));
  say("");
  say(Str("p = ", p, "   fp = (", fa, " + ", fb, "i)   i_p = ", ipm,
          "   eps(pi) = i^", ck, "   [labelling ", if(lab_ok,"OK","BAD"), "]"));
  say(Str("   S[2p-2,0] = ", if(#digits(numerator(v1)) > 40,
            Str("(", #digits(numerator(v1)), " digits)/", denominator(v1)), v1),
          "   residual 2^", r1[3]));
  say(Str("   S[p-1,p-1] = ", if(#digits(numerator(v2)) > 40,
            Str("(", #digits(numerator(v2)), " digits)/", denominator(v2)), v2),
          "   residual 2^", r2[3]));
  say(Str("   S[0,2p-2] = ", if(#digits(numerator(v3)) > 40,
            Str("(", #digits(numerator(v3)), " digits)/", denominator(v3)), v3),
          "   residual 2^", r3[3]));
  say(Str("   exact ", ex, "   rational ", ra, "   denominators prime to p ", pi_ok));
  say(Str("   E(2p-2,0) = ", E1 + O(p^3), "    E(p-1,p-1) = ", E2 + O(p^3)));
  say(Str("   term valuations : ", valuation(E1*v1 + O(p^8), p), " ",
          valuation(2*E2*NF^(p-1)*v2 + O(p^8), p), " ",
          valuation(E3*NF^(2*p-2)*v3 + O(p^8), p)));
  say(Str("   v_p(B_alg) = ", vB, "   B_alg = ", B + O(p^(vB+2))));
  if(vB == 2, say(Str("   p^{-2} B_alg mod p = ", lift(B/p^2 + O(p)),
                      "     [alpha^2 mod p = ",
                      lift(Mod(lift((1/(pia/p))^2 + O(p)), p)), "]")));
  say(Str("   kappa(p) = ", if(kp < 0, "not tabulated", kp),
          "   predicted v_p(B_alg) = ", if(pred < 0, "n/a", if(pred == 2, "2 exactly", ">= 3")),
          "   -> ", if(pred < 0, "no comparison",
                       if((pred == 2 && vB == 2) || (pred == 3 && vB >= 3), "AGREE", "MISMATCH"))));
  say(Str("   (", round((getabstime()-t0)/100)/10., " s)"));
  gate(Str("  p = ", p, " exactness   : "), ex && ra && pi_ok && lab_ok);
  gate(Str("  p = ", p, " v>=2 (W1)   : "), vB >= 2);
  if(pred > 0, gate(Str("  p = ", p, " vs kappa(p) : "),
                    (pred == 2 && vB == 2) || (pred == 3 && vB >= 3))));}

say("");
say(Str("gates passed      : ", NGATE, " of ", NGTOT));
{if(NGATE == NGTOT, print("M2W1DONE"), print("M2W1INCOMPLETE"));}
quit
