\\ excluded_set.gp -- the excluded set S_E for E: y^2 = x^3 - 56x.
\\ ---------------------------------------------------------------------------
\\ Discharges the five sets of eq:Sexc for the testbed curve, as the display in
\\ paper Section 5.1 (ssec:testbed) records them:
\\
\\   S_bad  <= {2,3,7}   6N * prod_v c_v * #tors * d_K = 2^14 * 3 * 7^2
\\   S_an   =  {}        lem:noanomalous leaves at most p = 5, and a_5 = -2
\\   S_red  <= {2}       rhobar_{E,p} irreducible at every odd p
\\   S_cmp  <= {2,3,7}   6N * Nm(f) = 2^15 * 3 * 7^4, supp(omega_E) <= {2,7}
\\   S_cl   <= {2,3}     #Cl_f(K) = 384 = 2^7 * 3
\\
\\ and concludes S_E <= {2,3,7}, a set containing no prime = 1 mod 4.  It also
\\ derives the Grossencharacter conductor f = (56) from N = |d_K| * Nm(f) and
\\ the uniqueness of the ideal of Z[i] of norm 3136, and factors Nm(f) - 1 =
\\ 3135, which is check (iii) of Section 6.4.
\\
\\ Computed here: a_5 for E and for the counterexample y^2 = x^3 + 3x; the
\\ enumeration of the ideals of Z[i] of norm 3136; the ray class group Cl_f(K)
\\ of K = Q(i) modulo f = (56), with its cyclic structure; and the four
\\ factorisations.
\\
\\ Quoted, not recomputed: the conductor N, the Tamagawa product, the torsion
\\ order and the isogeny class come from tab:testbed and from the LMFDB page of
\\ 12544.g1 (Cremona 12544b2), whose isogeny_degrees is [1,2].  The bound
\\ supp(omega_E) <= {2,7} on the period ratio of def:periodratio is the paper's
\\ input, not a computation of this script.
\\
\\ Output: stdout and ../data/excluded_set.out.
\\ Run from this directory:  gp -q excluded_set.gp
\\
\\ A statement of a GP script must fit on one line unless it is braced, which
\\ is why the print statements below are long.
\\ ---------------------------------------------------------------------------

default(parisize, 500000000);

LOGF = "../data/excluded_set.out";
fileclose(fileopen(LOGF, "w"));
say(s) = {print(s); write(LOGF, s)};

fmtfac(n) = {
  my(f = factor(abs(n)), s = if(n < 0, "-", ""));
  for(i = 1, matsize(f)[1],
      if(i > 1, s = Str(s, " * "));
      s = Str(s, f[i,1], if(f[i,2] == 1, "", Str("^", f[i,2]))));
  s
};
fmtset(v) = {
  my(s = "{");
  for(i = 1, #v, if(i > 1, s = Str(s, ", ")); s = Str(s, v[i]));
  Str(s, "}")
};
supp(n) = Set(Vec(factor(abs(n))[,1]~));

say("### the excluded set S_E of eq:Sexc, paper Section 5.1 (ssec:testbed)");
say(Str("pari version      : ", version()));
say("curve             : E : y^2 = x^3 - 56x   [0,0,0,-56,0]");
say("field             : K = Q(i), d_K = -4");
say("");

\\ --- quoted invariants (tab:testbed; LMFDB 12544.g1) ---------------------
N = 12544; CV = 4; TORS = 2; DK = -4; NMF = 3136;
say("quoted invariants (tab:testbed, LMFDB 12544.g1)");
say(Str("  conductor N       : ", N, " = ", fmtfac(N)));
say(Str("  prod_v c_v        : ", CV));
say(Str("  #E(Q)_tors        : ", TORS));
say(Str("  d_K               : ", DK));
say("  isogeny_degrees   : [1, 2]   (class {E, E_1}, E_1 : y^2 = x^3 + 14x)");
say("");

\\ --- the Grossencharacter conductor f ------------------------------------
say("the Grossencharacter conductor f, from N = |d_K| * Nm(f)");
quo = N / abs(DK);
say(Str("  N / |d_K|         : ", N, " / ", abs(DK), " = ", quo, "   (paper: Nm(f) = 3136)"));
K = bnfinit(x^2+1, 1);
say(Str("  class number of K : ", K.no, "   (Q(i) has class number 1)"));
il = ideallist(K, NMF);
nid = #il[NMF];
say(Str("  ideals of Z[i] of norm ", NMF, " : ", nid, "   (paper: unique)"));
{for(i = 1, nid, say(Str("    ideal ", i, " : ", il[NMF][i], "   norm ", idealnorm(K, il[NMF][i]))));}
f56 = idealhnf(K, 56);
say(Str("  (56) in HNF       : ", f56));
say(Str("  unique ideal of norm ", NMF, " equals (56) : ", nid == 1 && il[NMF][1] == f56));
say(Str("  Nm(f) - 1         : ", NMF - 1, " = ", fmtfac(NMF - 1), "   (Section 6.4 check (iii): 3135 = 3 * 5 * 11 * 19)"));
say("");

\\ --- S_bad ---------------------------------------------------------------
say("S_bad : the primes dividing 6N * prod_v c_v * #tors * d_K");
Bad = 6*N*CV*TORS*DK;
say(Str("  product           : ", Bad, " = ", fmtfac(Bad), "   (paper: 2^14 * 3 * 7^2, up to sign)"));
say(Str("  S_bad             : ", fmtset(supp(Bad)), "   (paper: <= {2, 3, 7})"));
say("");

\\ --- S_an ----------------------------------------------------------------
say("S_an : the anomalous primes");
say("  lem:noanomalous: for a curve with CM by Z[i] the only prime that can");
say("  be anomalous is p = 5, and 5 is anomalous exactly when a_5 = -4.");
E = ellinit([0,0,0,-56,0]);
a5E = ellap(E, 5);
say(Str("  E  : a_5          : ", a5E, "   (paper: -2)"));
say(Str("  E  : #Etilde(F_5) : ", 5 + 1 - a5E, "   (paper: 8)"));
say(Str("  E  : 5 | #Etilde(F_5)? : ", (5 + 1 - a5E) % 5 == 0, "   (0 = not anomalous)"));
say(Str("  S_an              : ", if((5 + 1 - a5E) % 5 == 0, "{5}", "{}"), "   (paper: empty)"));
say("  The exception at p = 5 is not vacuous.  The counterexample of");
say("  Section 5.1 is E' : y^2 = x^3 + 3x.");
F = ellinit([0,0,0,3,0]);
a5F = ellap(F, 5);
say(Str("  E' : j            : ", F.j, "   (1728: CM by Z[i])"));
say(Str("  E' : discriminant : ", F.disc, " = ", fmtfac(F.disc)));
say(Str("  E' : good reduction at 5? : ", F.disc % 5 != 0));
say(Str("  E' : a_5          : ", a5F, "   (paper: -4)"));
say(Str("  E' : #E'tilde(F_5) : ", 5 + 1 - a5F, "   (paper: 10)"));
say(Str("  E' : 5 | #E'tilde(F_5)? : ", (5 + 1 - a5F) % 5 == 0, "   (1 = anomalous)"));
say("");

\\ --- S_red ---------------------------------------------------------------
say("S_red : the primes at which rhobar_{E,p} is reducible");
say("  Quoted from LMFDB 12544.g1: isogeny_degrees is [1,2], so the isogeny");
say("  class is the two curves E and E_1 : y^2 = x^3 + 14x joined by a");
say("  2-isogeny.  A reducible rhobar_{E,p} gives a rational p-isogeny, so");
say("  rhobar_{E,p} is irreducible at every odd p.");
say("  S_red             : {2}   (paper: <= {2})");
say("");

\\ --- S_cmp ---------------------------------------------------------------
say("S_cmp : the set of lem:comparison: the primes dividing 6N * Nm(f),");
say("        together with supp(omega_E)");
Cmp = 6*N*NMF;
say(Str("  6N * Nm(f)        : ", Cmp, " = ", fmtfac(Cmp), "   (paper: 2^15 * 3 * 7^4)"));
say(Str("  its prime support : ", fmtset(supp(Cmp))));
say("  supp(omega_E)     : {2, 7}   (quoted from Section 5.1, not computed)");
Scmp = Set(concat(supp(Cmp), [2,7]));
say(Str("  S_cmp             : ", fmtset(Scmp), "   (paper: <= {2, 3, 7})"));
say("");

\\ --- S_cl ----------------------------------------------------------------
say("S_cl : the primes dividing #Cl_f(K), the ray class group of K = Q(i)");
say("       modulo f = (56)");
bnr = bnrinit(K, 56, 1);
say(Str("  cyclic structure  : ", bnr.cyc, "   ([48, 4, 2] is Z/48 x Z/4 x Z/2)"));
say(Str("  #Cl_f(K)          : ", bnr.no, " = ", fmtfac(bnr.no), "   (paper: 384 = 2^7 * 3)"));
say(Str("  S_cl              : ", fmtset(supp(bnr.no)), "   (paper: <= {2, 3})"));
say(Str("  conj:EK guard #Cl_f(K) >= 6 : ", bnr.no >= 6, "   (1 = discharged)"));
say("");

\\ --- conclusion ----------------------------------------------------------
SE = Set(concat(concat(concat(supp(Bad), [2]), Scmp), supp(bnr.no)));
split = select(q -> q % 4 == 1, SE);
say("conclusion");
say(Str("  S_E               : ", fmtset(SE), "   (paper: <= {2, 3, 7})"));
say(Str("  members = 1 mod 4 : ", fmtset(split), "   (paper: none)"));
say(Str("  no split prime excluded : ", #split == 0));
say("EXCLUDEDSETDONE");
quit
