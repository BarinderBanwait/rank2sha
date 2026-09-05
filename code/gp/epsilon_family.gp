\\ epsilon_family.gp -- the Grossencharacter conductor, the divisor D_E and the
\\ unit character eps, for the five curves E_D : y^2 = x^3 - D x.
\\ ---------------------------------------------------------------------------
\\ gp/epsilon_check.gp does the same for D = 56 alone.  Backs paper Section 7.1
\\ and 7.2: the closed form of f, the count #Cl_f(K), the root number w(E), the
\\ closed form eps = (D/.)_4^{-1} of eq:psiE, and the index of the LMFDB
\\ generators in the saturated Mordell--Weil basis used by the scan.
\\
\\ THE CONDUCTOR IN CLOSED FORM
\\ N = |d_K| Nm(f) gives Nm(f) = N/4 = 2^e m^2 with m odd.  f is stable under
\\ complex conjugation because E is defined over Q, and the conjugation-stable
\\ ideal of Z[i] of that norm is f = (1+i)^e (m).  Its generator is
\\ f_0 = (1+i)^e m for e odd and 2^{e/2} m for e even.  The "unique ideal of norm
\\ N/4" shortcut of gp/excluded_set.gp is available only for D = 56 and D = -33:
\\ 17 and 13 split, so for D = 17, -34, -39 there are three ideals of that norm.
\\
\\ THE DIVISOR AND THE CHARACTER
\\ D_E is enumerated as the primary residues x + y i coprime to f in the box
\\ 0 <= x < H[1,1], 0 <= y < H[2,2] of H = idealhnf(K, f_0), one per orbit of the
\\ units of Z[i] because (1+i)^3 | f for all five curves.  The count is gated
\\ against bnrinit(K, H, 1).no.  eps is filled in by Deuring's relation
\\ a_p = psi_E(p) + conj(psi_E(p)), psi_E((alpha)) = eps(alpha) alpha on the
\\ primary generator alpha = fa + fb i, so a_p is one of
\\   [2 fa, -2 fb, -2 fa, 2 fb]  according as  eps(alpha) = i^0, i^1, i^2, i^3,
\\ the four being distinct for p > 2.  Three checks, all over the split primes of
\\ good reduction up to EPSBOUND:
\\  (1) eps depends only on the residue class modulo f: pass 1 fills the table with
\\      a first-write guard, pass 2 re-determines every prime and compares;
\\  (2) the closed form eps = (D/.)_4^{-1} of eq:psiE;
\\  (3) eps(conj g) = conj(eps g) on the whole divisor.
\\ A fourth check is that no class of D_E is left unreached by the prime range.
\\
\\ Run from this directory:   gp -q epsilon_family.gp        (about two minutes)
\\ Parameters from the environment:
\\     DLIST     comma-separated D          default "56,17,-33,-34,-39"
\\     EPSBOUND  prime bound                default 10^6
\\     OUT       output file                default ../data/epsilon_family.out
\\ Output is staged to <file>.partial and moved onto the committed file only when
\\ every check passes.
\\ ---------------------------------------------------------------------------

default(parisizemax, 4000000000);
default(realprecision, 38);
getdef(name, dflt) = { my(s = getenv(name)); if(type(s) == "t_STR" && s != "", s, dflt) };
DLIST = eval(Str("[", getdef("DLIST", "56,17,-33,-34,-39"), "]"));
EPSBOUND = eval(getdef("EPSBOUND", "1000000"));
OUT = getdef("OUT", "../data/epsilon_family.out");
TMP = Str(OUT, ".partial");
system(Str("rm -f ", TMP));
NGATE = 0; NGTOT = 0;
say(s) = { print(s); write(TMP, s); };
gate(name, ok) = { NGTOT++; if(ok, NGATE++); say(Str(name, if(ok, "PASS", "FAIL"))); };

\\ Quoted from the LMFDB (rows of ../data/lmfdb_five_curves.json, pulled 2026-09-05):
\\ the label and the Mordell--Weil generators of each curve.  D = 56 is 12544.g1,
\\ whose generators are those of tab:testbed and of gp/regulator.gp.
LAB = ["12544.g1", "9248.c1", "69696.i2", "73984.d2", "48672.n2"];
LDS = [56, 17, -33, -34, -39];
LGN = [[[8,8],[9,15]], [[-1,4],[-4,2]], [[4,14],[16,68]], [[8,28],[32,184]], [[3,12],[27,144]]];
labof(d) = { my(r = "not in the pull"); for(j = 1, #LDS, if(LDS[j] == d, r = LAB[j])); r; };
gensof(d) = { my(r = 0); for(j = 1, #LDS, if(LDS[j] == d, r = LGN[j])); r; };

\\ The saturated basis of ../data/family_bases.txt, read as "D|[[x,y],[x,y]]".
BASD = List(); BASG = List();
{my(ls = externstr("grep -v '^#' ../data/family_bases.txt"));
 for(j = 1, #ls, my(w = strsplit(ls[j], "|"));
   if(#w == 2, listput(BASD, eval(w[1])); listput(BASG, eval(w[2]))));}
basof(d) = { my(r = 0); for(j = 1, #BASD, if(BASD[j] == d, r = BASG[j])); r; };

isprimary(a,b) = ((a+b-1) % 4 == 0) && ((b-a+1) % 4 == 0);
qrs4(fa, fb, m) = {
  my(p = fa^2 + fb^2, r = Mod(-fa, p) / Mod(fb, p), v = Mod(m, p)^((p - 1)/4));
  if(r^2 != Mod(-1, p), return(-2));
  for(k = 0, 3, if(v == r^k, return(k)));
  -1;
};
fmtfac(n) = {
  my(f = factor(abs(n)), s = if(n < 0, "-", ""));
  for(i = 1, matsize(f)[1], if(i > 1, s = Str(s, " * "));
      s = Str(s, f[i,1], if(f[i,2] == 1, "", Str("^", f[i,2]))));
  s
};

K = bnfinit(x^2+1, 1);
say("### the Grossencharacter conductor, the divisor D_E and the unit character eps");
say(Str("pari version      : ", version()));
say("field             : K = Q(i), d_K = -4, class number 1");
say(Str("prime range       : split 5 <= p <= ", EPSBOUND, ", p prime to Nm(f)"));
say("LMFDB rows quoted from ../data/lmfdb_five_curves.json (pulled 2026-09-05)");

{for(idx = 1, #DLIST,
  my(D = DLIST[idx], t0 = getabstime());
  my(E = ellinit([0,0,0,-D,0]), N = ellglobalred(E)[1], NF = N/4);
  my(EE = valuation(NF,2), MM = sqrtint(NF/2^EE));
  my(F0 = if(EE % 2 == 1, (1+I)^EE*MM, 2^(EE/2)*MM));
  my(H = idealhnf(K, Mod(imag(F0)*x + real(F0), x^2+1)));
  my(AH = H[1,1], BH = H[1,2], DH = H[2,2]);
  my(redx = (u1, u2) -> my(y2 = ((u2 % DH) + DH) % DH, k = (u2 - y2)/DH);
                        [((u1 - k*BH) % AH + AH) % AH, y2]);
  my(cid = (u1, u2) -> my(r = redx(u1,u2)); r[1]*DH + r[2] + 1);
  say("");
  say(Str("=== D = ", D, "   E : y^2 = x^3 - ", D, "x   LMFDB ", labof(D), " ==="));
  say(Str("  conductor N     : ", N, " = ", fmtfac(N)));
  say(Str("  Nm(f) = N/4     : ", NF, " = 2^", EE, " * ", MM, "^2   (m = ", MM, " odd)"));
  say(Str("  f               : (1+i)^", EE, " * (", MM, ")   generator f_0 = ", F0));
  say(Str("  idealhnf(K,f_0) : ", H, "   norm ", AH*DH));
  say(Str("  ideals of norm ", NF, " in Z[i] : ", #ideallist(K, NF)[NF],
          "   (the uniqueness shortcut is available only when that is 1)"));
  say(Str("  root number w(E): ", ellrootno(E)));
  say(Str("  a_5             : ", ellap(E,5), "   #Etilde(F_5) = ", 6 - ellap(E,5),
          "   anomalous at 5: ", (6 - ellap(E,5)) % 5 == 0));
  gate("  conductor closed form   : ", MM % 2 == 1 && MM^2 * 2^EE == NF && EE >= 3
                                       && AH*DH == NF);

  \\ pass 1: the table with a first-write guard
  my(epstab = vector(AH*DH));
  forprime(q = 5, EPSBOUND,
    if(q % 4 != 1 || MM % q == 0, next);
    my(sol = qfbsolve(Qfb(1,0,1), q)); if(sol == 0, next);
    my(a = sol[1], b = sol[2], fa = 0, fb = 0);
    for(k = 0, 3, if(isprimary(a,b), fa = a; fb = b; break); [a,b] = [-b,a]);
    my(ap = ellap(E,q), cand = [2*fa,-2*fb,-2*fa,2*fb], kk = 0, nm = 0);
    for(k = 1, 4, if(cand[k] == ap, kk = k; nm++));
    if(nm != 1, next);
    my(id = cid(fa,fb)); if(epstab[id] == 0, epstab[id] = kk));

  \\ pass 2: re-determine at every split prime, compare, test the closed form
  my(ntest = 0, nconf = 0, nqbad = 0, nundet = 0, conf = List(), qbad = List());
  forprime(q = 5, EPSBOUND,
    if(q % 4 != 1 || MM % q == 0, next);
    my(sol = qfbsolve(Qfb(1,0,1), q)); if(sol == 0, next);
    my(a = sol[1], b = sol[2], fa = 0, fb = 0);
    for(k = 0, 3, if(isprimary(a,b), fa = a; fb = b; break); [a,b] = [-b,a]);
    my(ap = ellap(E,q), cand = [2*fa,-2*fb,-2*fa,2*fb], kk = 0, nm = 0);
    for(k = 1, 4, if(cand[k] == ap, kk = k; nm++));
    if(nm != 1, nundet++; next);
    ntest++;
    my(ck = kk - 1, stored = epstab[cid(fa,fb)] - 1);
    if(ck != stored, nconf++; if(#conf < 5, listput(conf, [q, fa, fb, ck, stored])));
    my(mq = qrs4(fa, fb, D));
    if(!(mq >= 0 && (ck + mq) % 4 == 0), nqbad++;
       if(#qbad < 5, listput(qbad, [q, fa, fb, ck, mq]))));
  say(Str("  split primes tested     : ", ntest, "   with no unique candidate: ", nundet));
  say(Str("  conflicts mod f         : ", nconf,
          if(nconf, Str("   first: ", Vec(conf)), "")));
  say(Str("  eps != (D/.)_4^{-1} at  : ", nqbad,
          if(nqbad, Str("   first: ", Vec(qbad)), "")));
  gate("  eps well defined mod f  : ", nconf == 0);
  gate("  eps = (D/.)_4^{-1}      : ", nqbad == 0);

  \\ the divisor D_E
  my(NC = 0, NMISS = 0, NCJ = 0);
  for(u1 = 0, AH-1, for(u2 = 0, DH-1,
    if(!isprimary(u1,u2), next);
    if(gcd(u1^2 + u2^2, MM) != 1, next);
    my(id = cid(u1,u2));
    if(epstab[id] == 0, NMISS++, NC++;
       my(jd = cid(u1, -u2));
       if(epstab[jd] == 0 || (epstab[jd] - 1 + epstab[id] - 1) % 4 != 0, NCJ++))));
  my(NRAY = bnrinit(K, H, 1).no, BNR = bnrinit(K, H, 1).cyc);
  say(Str("  classes of D_E          : ", NC + NMISS, "   unreached by the prime range: ", NMISS));
  say(Str("  #Cl_f(K)                : ", NRAY, " = ", fmtfac(NRAY), "   structure ", BNR));
  say(Str("  eps(conj g) != conj eps : ", NCJ));
  gate("  class count = #Cl_f(K)  : ", NC + NMISS == NRAY);
  gate("  eps covers D_E          : ", NMISS == 0);
  gate("  eps conjugation         : ", NCJ == 0);

  \\ the index of the LMFDB generators in the saturated basis
  my(G = gensof(D), B = basof(D));
  if(B == 0,
     say("  saturated basis on file : none (../data/family_bases.txt covers D = 17, -33, -34, -39)"),
     my(rg = matdet(ellheightmatrix(E, G)), rb = matdet(ellheightmatrix(E, B)));
     my(ix = sqrt(rg/rb));
     say(Str("  LMFDB generators        : ", G));
     say(Str("  saturated basis on file : ", B));
     say(Str("  regulators              : ", rg, " and ", rb));
     say(Str("  index of LMFDB gens     : ", round(ix)));
     gate("  index is 1              : ", abs(ix - 1) < 1e-15));
  say(Str("  (", round((getabstime()-t0)/100)/10., " s)"));
);}

say("");
say(Str("checks passed     : ", NGATE, " of ", NGTOT));
{if(NGATE == NGTOT,
    system(Str("mv -f ", TMP, " ", OUT)); print("EPSILONFAMILYDONE"),
    print(OUT, " left unchanged; partial output in ", TMP, ".");
    print("EPSILONFAMILYINCOMPLETE"));}
quit
