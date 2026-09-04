\\ Guard-free re-determination of the unit character eps for E: y^2 = x^3 - 56x
\\ ---------------------------------------------------------------------------
\\ Backs paper/v2 Sec. 6.2 ("The character, the divisor and the weight"), the
\\ sentence after eq:psiE: eps was checked "over 3018 split primes and with no
\\ conflict".
\\
\\ legacy/gp/deltaE.gp records the unit class the first time a residue class mod 56 is
\\ reached and never re-examines it (the guard `if(epstab[id] == 0, ...)`), so it
\\ assigns eps rather than certifying it.  This script removes the guard.
\\
\\ Conventions are copied verbatim from legacy/gp/deltaE.gp.  Deuring's relation gives
\\ a_p = psi_E(p) + conj(psi_E(p)) with psi_E((alpha)) = eps(alpha)*alpha on the
\\ primary generator alpha = fa + fb*i, so a_p is one of
\\   [2*fa, -2*fb, -2*fa, 2*fb]   according as   eps(alpha) = i^0, i^1, i^2, i^3.
\\ The four candidates are pairwise distinct for p > 2, so a_p determines
\\ eps(alpha) uniquely.  Write CK := kk - 1, so eps(alpha) = i^CK; legacy/gp/deltaE.gp
\\ stores kk and uses the weight I^(-CK) = eps^(-1), raised to a+b in slot (a,b).
\\
\\ Two checks:
\\  (1) Consistency.  eps(alpha) depends only on alpha mod 56.  Pass 1 builds the
\\      table with the guard; pass 2 re-determines the class at every split prime
\\      and compares against the table.  Every prime is tested, including the one
\\      that first wrote its class.
\\  (2) Closed form.  eq:psiE asserts eps = (56/.)_4^{-1}.  For alpha primary of
\\      prime norm p, Z[i]/(alpha) = F_p with i mapped to -fa/fb, so the quartic
\\      residue symbol (56/alpha)_4 = i^m is read off from 56^((p-1)/4) in F_p.
\\      The assertion is (CK + m) = 0 mod 4.
\\
\\ Range: split 5 <= p <= 60000, p != 7, matching legacy/gp/deltaE.gp.
\\ Output: ../data/epsilon_check.out
\\ ---------------------------------------------------------------------------
default(parisizemax, 4000000000);
default(realprecision, 3200);

OUT = "../data/epsilon_check.out";
TMP = "../data/epsilon_check.out.partial";
system(Str("rm -f ", TMP));
say(s) = {print(s); write(TMP, s);};

say("epsilon_check.gp --- guard-free re-determination of the unit character eps");
say("curve         E: y^2 = x^3 - 56x, ainvs [0,0,0,-56,0], N = 12544 = 2^8*7^2");
say(Str("backs         paper/v2 Sec. 6.2, the sentence after eq:psiE"));
say(Str("PARI/GP       ", version()[1], ".", version()[2], ".", version()[3]));
say(Str("realprecision ", default(realprecision), " decimal digits (the arithmetic below is exact:"));
say("              integers, Z/p, and ellap; no real number enters a decision)");
say("prime range   split 5 <= p <= 60000, p != 7");
say("");

E = ellinit([0,0,0,-56,0]);
isprimary(a, b) = ((a + b - 1) % 4 == 0) && ((b - a + 1) % 4 == 0);
classid(a, b) = ((a % 56) + 56) % 56 * 56 + ((b % 56) + 56) % 56;
Q = Qfb(1, 0, 1);

\\ Primary generator of the ideal above a split p, and the unit class CK from a_p.
\\ Returns [fa, fb, CK], or 0 if a_p matches no unique candidate.
unitclass(p) = {
  my(sol = qfbsolve(Q, p));
  if(sol == 0, return(0));
  my(a = sol[1], b = sol[2], fa = 0, fb = 0);
  for(k = 0, 3, if(isprimary(a, b), fa = a; fb = b; break); [a, b] = [-b, a]);
  my(ap = ellap(E, p), cand = [2*fa, -2*fb, -2*fa, 2*fb], kk = 0, nm = 0);
  for(k = 1, 4, if(cand[k] == ap, kk = k; nm++));
  if(nm != 1, return(0));
  [fa, fb, kk - 1];
};

\\ (m/alpha)_4 = i^k for alpha = fa + fb*i primary of prime norm p, gcd(m,p) = 1.
qrs4(fa, fb, m) = {
  my(p = fa^2 + fb^2, r = Mod(-fa, p) / Mod(fb, p), u = Mod(m, p)^((p - 1)/4));
  if(r^2 != Mod(-1, p), return(-2));
  for(k = 0, 3, if(u == r^k, return(k)));
  -1;
};

\\ --- pass 1: build the table with the first-write guard, exactly as legacy/gp/deltaE.gp ---
epstab = vector(56*56);
{forprime(p = 5, 60000,
  if(p % 4 != 1 || p == 7, next);
  my(u = unitclass(p));
  if(u == 0, next);
  my(id = classid(u[1], u[2]));
  if(epstab[id] == 0, epstab[id] = u[3] + 1));}
nclass = sum(i = 1, #epstab, epstab[i] != 0);
say(Str("pass 1: residue classes mod 56 determined: ", nclass));

\\ --- pass 2: re-determine at every split prime, compare, and test the closed form ---
ntest = 0; nconf = 0; nqok = 0; nqbad = 0; nundet = 0;
conflicts = List(); qbadlist = List();
{forprime(p = 5, 60000,
  if(p % 4 != 1 || p == 7, next);
  my(u = unitclass(p));
  if(u == 0, nundet++; next);
  my(fa = u[1], fb = u[2], ck = u[3], id = classid(fa, fb), stored = epstab[id] - 1);
  ntest++;
  if(ck != stored,
     nconf++;
     if(#conflicts < 20, listput(conflicts, [p, fa, fb, ck, stored])));
  my(m = qrs4(fa, fb, 56));
  if(m >= 0 && (ck + m) % 4 == 0,
     nqok++,
     nqbad++;
     if(#qbadlist < 20, listput(qbadlist, [p, fa, fb, ck, m])));)}

say("");
say("CHECK 1  eps depends only on the residue class mod 56");
say(Str("  split primes tested : ", ntest));
say(Str("  conflicts           : ", nconf));
if(nconf, say(Str("  first conflicts [p, fa, fb, determined, stored]: ", Vec(conflicts))));
say(Str("  primes with no unique candidate: ", nundet));

say("");
say("CHECK 2  eps = (56/.)_4^{-1}, i.e. CK + m = 0 mod 4 with (56/alpha)_4 = i^m");
say(Str("  primes agreeing     : ", nqok));
say(Str("  primes disagreeing  : ", nqbad));
if(nqbad, say(Str("  first disagreements [p, fa, fb, CK, m]: ", Vec(qbadlist))));

\\ --- coverage of the 384-point divisor D_E ---
ncov = 0; nmiss = 0; misslist = List();
{for(a = 0, 55, for(b = 0, 55,
  if(!isprimary(a, b), next);
  if((a + b) % 2 == 0, next);
  if(a % 7 == 0 && b % 7 == 0, next);
  if(epstab[classid(a, b)], ncov++, nmiss++; if(#misslist < 20, listput(misslist, [a, b])))));}
say("");
say("COVERAGE of the 384 classes used by deltaE.gp");
say(Str("  classes covered by the prime range: ", ncov));
say(Str("  classes not reached               : ", nmiss));
if(nmiss, say(Str("  first uncovered: ", Vec(misslist))));

say("");
{if(nconf == 0 && nqbad == 0 && nmiss == 0,
    say("STATUS: eps is consistent at every split prime tested, agrees with the");
    say("        closed form (56/.)_4^{-1}, and covers all 384 classes of D_E."),
    say("STATUS: at least one check failed; see the counts above."));}

system(Str("mv -f ", TMP, " ", OUT));
print("EPSILONCHECKDONE");
quit
