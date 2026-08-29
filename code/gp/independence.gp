\\ Pointwise nonvanishing and linear independence of the grade-<=2 sections on D_E
\\ ---------------------------------------------------------------------------
\\ Curve E: y^2 = x^3 - 56x (CM by Z[i], f = (56), N = 12544 = 2^8*7^2).
\\
\\ Backs paper/v2 Sec. 6.5 ("Nonvanishing, independence, and the prime support"),
\\ which asserts four numbers with no script behind them:
\\   (a) min |F(t_g)| over the six sections and the 384 points is 0.01640..., at wp;
\\   (b) the Gram matrix of the six normalised value vectors in C^384 has smallest
\\       eigenvalue 0.0375... and determinant 0.0249...;
\\   (c) hence eq:indep, || sum c_{a,b} e^_{a,b} ||_2 >= 0.19 ||c||_2 on C^6;
\\   (d) on the grade-two row (0,3), (1,2), (2,1) the smallest eigenvalue is
\\       0.2054..., unchanged by the eps-weights.
\\ The mixed-c half of eq:EKforall rests on eq:indep.
\\
\\ Conventions are copied verbatim from deltaE.gp: lemniscatic lattice Gamma =
\\ w1*Z[i], A = w1^2/Pi, s2 = 0 so theta = sigma, the six closed forms of
\\ eq:EKclosed, the 384 primary points t_g = g*w1/56, the unit character
\\ eps = (56/.)_4^{-1} read off from a_p, and the class-invariant weight
\\ eps(g)^{-(a+b)} of eq:classinvwt.
\\
\\ Two conventions are in play and the script computes both, since the paper's
\\ numbers do not come from a single one.
\\   CORE vs FULL.  Sec. 6.1 says "the tables below therefore give the algebraic
\\     cores", the sections of eq:EKclosed stripped of their prefactors
\\     -A/2, -1/2, -A, A^2/3.  Those prefactors are nonzero real scalars, so they
\\     change |F(t_g)| but not the Gram spectrum of the normalised vectors: a real
\\     scalar rescales a vector and at most flips its sign, and a diagonal sign
\\     conjugation leaves a Hermitian spectrum and determinant fixed.
\\   UNWEIGHTED vs EPS-WEIGHTED.  The class-invariant vector attached to slot
\\     (a,b) is eps(g)^{-(a+b)} e*_{a,b}(t_g), which is A^a r_{a,b}([g]) in the
\\     notation of eq:jetpackage.  The weights are unimodular, so they do not
\\     change |F(t_g)|; they do change the 6x6 Gram, because the exponent a+b
\\     differs across grades.  On the grade-two row all three slots have a+b = 3,
\\     so there the weights act by a common unimodular factor and the 3x3 Gram is
\\     unchanged -- the paper's claim (d), tested below rather than assumed.
\\
\\ Eigenvalues: the Gram matrix G is Hermitian positive definite.  Its spectrum is
\\ computed from the real symmetric embedding [[Re G, -Im G], [Im G, Re G]], whose
\\ eigenvalues are those of G each with multiplicity two, by qfjacobi.  The
\\ pairing, the trace and the determinant are cross-checked against G.
\\
\\ eq:indep follows from the smallest eigenvalue: for unit vectors v_k with Gram
\\ G, || sum c_k v_k ||_2^2 = c* G c >= lambda_min ||c||_2^2, so the constant in
\\ eq:indep is sqrt(lambda_min).
\\
\\ Status: floating point, at the working precisions listed below.  Unlike the
\\ resultants and sums of deltaE.gp this quantity passes through no exactness
\\ gate; Caveat 6.x(iv) of the paper records that.  Stability is exhibited by
\\ running the whole computation at each precision in PRECS and comparing.
\\
\\ Cost: about 1 second at the default PRECS = [100, 200, 400].  Override with the
\\ environment variable INDEP_PRECS, e.g. INDEP_PRECS=100,400,800.
\\ Output: ../data/independence.out
\\ ---------------------------------------------------------------------------
default(parisizemax, 4000000000);

OUT = "../data/independence.out";
TMP = "../data/independence.out.partial";
system(Str("rm -f ", TMP));
say(s) = {print(s); write(TMP, s);};
f40(x) = strprintf("%.40f", x);

PRECS = [100, 200, 400];
{my(e = getenv("INDEP_PRECS"));
 if(e != "" && e != 0, PRECS = eval(Str("[", e, "]")));}

{NAM = ["(0,1)  E1*                  ",
        "(0,2)  wp                   ",
        "(1,1)  E1*^2 - wp           ",
        "(0,3)  wp'                  ",
        "(1,2)  E1*wp + wp'/2        ",
        "(2,1)  E1*^3 - 3E1*wp - wp' "];}
SS  = [1, 2, 2, 3, 3, 3];          \\ a+b in slot (a,b); the eps exponent
G2  = [4, 5, 6];                   \\ the grade-two row

isprimary(a, b) = ((a + b - 1) % 4 == 0) && ((b - a + 1) % 4 == 0);
classid(a, b) = ((a % 56) + 56) % 56 * 56 + ((b % 56) + 56) % 56;

\\ Spectrum of a Hermitian matrix, ascending, via the real symmetric embedding.
hermeig(G) = {
  my(m = matsize(G)[1], R = real(G), S = imag(G));
  my(L = vecsort(qfjacobi(matconcat([R, -S; S, R]))[1]));
  my(ev = vector(m, k, L[2*k - 1]), gap = 0);
  for(k = 1, m, gap = max(gap, abs(L[2*k] - L[2*k - 1])));
  [ev, gap];
};

\\ Gram matrix of the vectors of V, each first normalised to Euclidean length 1.
gram(V) = {
  my(m = #V, nn = #V[1], H = matrix(m, m));
  my(nr = vector(m, k, sqrt(sum(j = 1, nn, abs(V[k][j])^2))));
  for(k = 1, m, for(l = 1, m,
    H[k, l] = sum(j = 1, nn, V[k][j] * conj(V[l][j])) / (nr[k] * nr[l])));
  H;
};

\\ Report one Gram matrix.  Returns [lambda_min, det].
report(lab, V, idx) = {
  my(W = vector(#idx, k, V[idx[k]]), G = gram(W), he = hermeig(G));
  my(ev = he[1], m = #ev, d = matdet(G));
  say(Str("  ", lab));
  for(k = 1, m, say(Str("    lambda_", k, " = ", f40(ev[k]))));
  say(Str("    lambda_min           = ", f40(ev[1])));
  say(Str("    det                  = ", f40(real(d))));
  say(Str("    sqrt(lambda_min)     = ", f40(sqrt(ev[1]))));
  say(Str("    checks: |Im det| 2^", exponent(abs(imag(d))),
          "   |det - prod eig| 2^", exponent(abs(real(d) - prod(k = 1, m, ev[k]))),
          "   |trace - ", m, "| 2^", exponent(abs(sum(k = 1, m, ev[k]) - m)),
          "   eigenvalue pairing gap 2^", exponent(he[2])));
  [ev[1], real(d)];
};

\\ ---------------------------------------------------------------------------
KEYS = List();
{for(ip = 1, #PRECS,
  my(prec = PRECS[ip]);
  default(realprecision, prec);
  my(E = ellinit([0,0,0,-56,0]));
  my(w1 = E.omega[1], A = w1^2/Pi);

  \\ --- eps table from a_p (Deuring), verbatim from deltaE.gp ---
  my(epstab = vector(56*56), Q = Qfb(1, 0, 1));
  forprime(p = 5, 60000,
    if(p % 4 != 1 || p == 7, next);
    my(sol = qfbsolve(Q, p));
    if(sol == 0, next);
    my(a = sol[1], b = sol[2], fa = 0, fb = 0);
    for(k = 0, 3, if(isprimary(a, b), fa = a; fb = b; break); [a, b] = [-b, a]);
    my(ap = ellap(E, p), cand = [2*fa, -2*fb, -2*fa, 2*fb], kk = 0, nm = 0);
    for(k = 1, 4, if(cand[k] == ap, kk = k; nm++));
    if(nm != 1, next);
    my(id = classid(fa, fb));
    if(epstab[id] == 0, epstab[id] = kk));

  \\ --- the 384 primary points, verbatim from deltaE.gp ---
  my(CA = List(), CB = List(), CK = List());
  for(a = 0, 55, for(b = 0, 55,
    if(!isprimary(a, b), next);
    my(id = classid(a, b));
    if((a + b) % 2 == 0, next);
    if(a % 7 == 0 && b % 7 == 0, next);
    if(epstab[id] == 0, say(Str("MISSING CLASS ", [a,b])); next);
    listput(CA, a); listput(CB, b); listput(CK, epstab[id] - 1)));
  my(n = #CA);

  my(VE1 = vector(n), VP = vector(n), VPd = vector(n), VW = vector(n));
  for(j = 1, n,
    my(t = (CA[j] + CB[j]*I)*w1/56, wp2 = ellwp(E, t, 1));
    VE1[j] = ellzeta(E, t) - conj(t)/A;
    VP[j]  = wp2[1];
    VPd[j] = wp2[2];
    VW[j]  = I^(-CK[j]));

  \\ the six algebraic cores of eq:EKclosed, and the six full sections
  my(CORE = [vector(n, j, VE1[j]),
             vector(n, j, VP[j]),
             vector(n, j, VE1[j]^2 - VP[j]),
             vector(n, j, VPd[j]),
             vector(n, j, VE1[j]*VP[j] + VPd[j]/2),
             vector(n, j, VE1[j]^3 - 3*VE1[j]*VP[j] - VPd[j])]);
  my(PRE = [1, 1, -A/2, -1/2, -A, A^2/3]);
  my(FULL  = vector(6, k, vector(n, j, PRE[k]*CORE[k][j])));
  my(WCORE = vector(6, k, vector(n, j, VW[j]^SS[k]*CORE[k][j])));
  my(WFULL = vector(6, k, vector(n, j, VW[j]^SS[k]*FULL[k][j])));

  if(ip == 1,
    say("independence.gp --- nonvanishing and independence of the grade-<=2 sections");
    say("curve         E: y^2 = x^3 - 56x, ainvs [0,0,0,-56,0], N = 12544 = 2^8*7^2");
    say("backs         paper/v2 Sec. 6.5, incl. eq:indep");
    say(Str("PARI/GP       ", version()[1], ".", version()[2], ".", version()[3]));
    say(Str("precisions    ", PRECS, " decimal digits"));
    say("status        floating point, outside the exactness gates of Sec. 6.7");
    say(""));

  say("===========================================================================");
  say(Str("WORKING PRECISION: ", prec, " decimal digits requested, ",
          default(realprecision), " allocated"));
  say("===========================================================================");
  say(Str("points on D_E: ", n, " (expect 384)"));
  say(Str("w1 = ", f40(w1), "   A = w1^2/Pi = ", f40(A)));
  say("");

  \\ --- (a) pointwise minima -------------------------------------------------
  say("A. MINIMUM OF |F(t_g)| OVER D_E");
  say("   The eps-weights are unimodular, so they do not change any |F(t_g)|.");
  say("");
  my(mc = 0, mck = 0, mcj = 0, mf = 0, mfk = 0, mfj = 0);
  say("   cores (prefactors of eq:EKclosed stripped):");
  for(k = 1, 6,
    my(m = -1, jm = 0);
    for(j = 1, n, my(v = abs(CORE[k][j])); if(jm == 0 || v < m, m = v; jm = j));
    say(Str("     ", NAM[k], " min ", f40(m), "  at g = ", CA[jm], " + ", CB[jm], "i"));
    if(mck == 0 || m < mc, mc = m; mck = k; mcj = jm));
  say(Str("     OVERALL min ", f40(mc), "  section ", NAM[mck],
          " at g = ", CA[mcj], " + ", CB[mcj], "i"));
  say("");
  say("   full sections e*_{a,b} of eq:EKclosed (prefactors included):");
  for(k = 1, 6,
    my(m = -1, jm = 0);
    for(j = 1, n, my(v = abs(FULL[k][j])); if(jm == 0 || v < m, m = v; jm = j));
    say(Str("     ", NAM[k], " min ", f40(m), "  at g = ", CA[jm], " + ", CB[jm], "i"));
    if(mfk == 0 || m < mf, mf = m; mfk = k; mfj = jm));
  say(Str("     OVERALL min ", f40(mf), "  section ", NAM[mfk],
          " at g = ", CA[mfj], " + ", CB[mfj], "i"));
  say("");

  \\ --- (b) the 6x6 Gram matrices --------------------------------------------
  say("B. GRAM MATRIX OF THE SIX NORMALISED VALUE VECTORS IN C^384");
  my(r1 = report("cores, unweighted",  CORE,  [1,2,3,4,5,6]));
  my(r2 = report("cores, eps-weighted", WCORE, [1,2,3,4,5,6]));
  my(r3 = report("full sections, unweighted",   FULL,  [1,2,3,4,5,6]));
  my(r4 = report("full sections, eps-weighted", WFULL, [1,2,3,4,5,6]));
  say("");
  say(Str("  core vs full, unweighted   : |d lambda_min| 2^", exponent(abs(r1[1]-r3[1])),
          "   |d det| 2^", exponent(abs(r1[2]-r3[2]))));
  say(Str("  core vs full, eps-weighted : |d lambda_min| 2^", exponent(abs(r2[1]-r4[1])),
          "   |d det| 2^", exponent(abs(r2[2]-r4[2]))));
  say("  A nonzero real prefactor does not change the spectrum, as stated above.");
  say("");

  \\ --- (d) the grade-two row -------------------------------------------------
  say("C. GRADE-TWO ROW (0,3), (1,2), (2,1)");
  my(g1 = report("cores, unweighted",  CORE,  G2));
  my(g2 = report("cores, eps-weighted", WCORE, G2));
  my(g3 = report("full sections, unweighted",   FULL,  G2));
  my(g4 = report("full sections, eps-weighted", WFULL, G2));
  say("");
  say(Str("  weighted vs unweighted: |d lambda_min| 2^", exponent(abs(g1[1]-g2[1])),
          "   |d det| 2^", exponent(abs(g1[2]-g2[2]))));
  say("  All three grade-two slots have a + b = 3, so the eps-weights act by the");
  say("  common unimodular factor eps(g)^{-3} and cancel from the Gram matrix.");
  say("");

  \\ --- eq:indep --------------------------------------------------------------
  say("D. THE CONSTANT OF eq:indep");
  say("   || sum_k c_k v_k ||_2 >= sqrt(lambda_min) ||c||_2 for unit vectors v_k.");
  say(Str("   eps-weighted 6x6 : lambda_min = ", f40(r2[1]),
          "  sqrt = ", f40(sqrt(r2[1]))));
  say(Str("   unweighted   6x6 : lambda_min = ", f40(r1[1]),
          "  sqrt = ", f40(sqrt(r1[1]))));
  say("");

  listput(KEYS, [mc, mf, r1[1], r1[2], r2[1], r2[2], sqrt(r2[1]), g1[1], g2[1]]);
)}

{KEYNAM = ["min |core F|                   ",
           "min |full section F|           ",
           "6x6 unweighted lambda_min      ",
           "6x6 unweighted det             ",
           "6x6 eps-weighted lambda_min    ",
           "6x6 eps-weighted det           ",
           "sqrt(eps-weighted lambda_min)  ",
           "grade-2 unweighted lambda_min  ",
           "grade-2 eps-weighted lambda_min"];}

say("===========================================================================");
say("PRECISION STABILITY");
say("===========================================================================");
say(Str("Differences against the run at ", PRECS[#PRECS], " digits, as binary exponents."));
say("");
{for(q = 1, #KEYNAM,
  my(s = Str("  ", KEYNAM[q]));
  for(ip = 1, #PRECS - 1,
    s = Str(s, "   ", PRECS[ip], ": 2^",
            exponent(abs(KEYS[ip][q] - KEYS[#PRECS][q]))));
  say(s));}
say("");

say("===========================================================================");
say("COMPARISON WITH THE VALUES PRINTED IN Sec. 6.5");
say("===========================================================================");
{my(K = KEYS[#PRECS]);
 say(Str("  min |F(t_g)|, paper 0.01640...       computed ", f40(K[1]),
         "   (cores)"));
 say(Str("                                       computed ", f40(K[2]),
         "   (full sections)"));
 say(Str("  Gram lambda_min, paper 0.0375...     computed ", f40(K[5]),
         "   (eps-weighted)"));
 say(Str("                                       computed ", f40(K[3]),
         "   (unweighted)"));
 say(Str("  Gram det, paper 0.0249...            computed ", f40(K[6]),
         "   (eps-weighted)"));
 say(Str("                                       computed ", f40(K[4]),
         "   (unweighted)"));
 say(Str("  eq:indep constant, paper 0.19        computed ", f40(K[7]),
         "   (eps-weighted)"));
 say(Str("  grade-two lambda_min, paper 0.2054   computed ", f40(K[8]),
         "   (unweighted)"));
 say(Str("                                       computed ", f40(K[9]),
         "   (eps-weighted)"));}
say("");
say("Sec. 6.5 quotes 0.01640... and 0.0375... / 0.0249... under two different");
say("conventions, and both are reproduced above.");
say("");
say("  0.01640... is the minimum over the six algebraic CORES.  Over the six full");
say("  sections of eq:EKclosed the minimum is 0.00289..., attained at slot (1,1)");
say("  and not at wp.  Sec. 6.1 declares the tables to be cores, so the number is");
say("  right; the word 'sections' in Sec. 6.5 is what does not match it.");
say("");
say("  0.0375... and 0.0249... are the EPS-WEIGHTED vectors, that is the");
say("  class-invariant vectors eps(g)^{-(a+b)} e*_{a,b}(t_g) of eq:classinvwt,");
say("  equivalently the r_{a,b} of eq:jetpackage, which differ from them by the");
say("  positive scalar A^{-a} and so have the same normalised vectors.  The");
say("  unweighted vectors give 0.0492... and 0.0294... instead.  eq:indep writes");
say("  the hat over e*_{a,b}; the constant 0.19 belongs to the weighted vectors.");
say("");
say("The conclusion that no nonzero constant-coefficient combination of the six");
say("vanishes identically on D_E holds under either convention: both smallest");
say("eigenvalues are bounded away from zero, and only the constant in eq:indep");
say("changes, from 0.19 to 0.22.");

system(Str("mv -f ", TMP, " ", OUT));
print("INDEPENDENCEDONE");
quit
