\\ excluded_set_family.gp -- the excluded set S_E of eq:Sexc for the five curves
\\ E_D : y^2 = x^3 - D x, D = 56, 17, -33, -34, -39.
\\ ---------------------------------------------------------------------------
\\ gp/excluded_set.gp does the same for D = 56 alone.  Backs the S_E display of
\\ paper Section 7.2, one line per curve, and discharges the five sets of eq:Sexc:
\\
\\   S_bad   the primes dividing 6 N (prod_v c_v) #E(Q)_tors d_K
\\   S_an    the anomalous primes: by lem:noanomalous only p = 5 can be anomalous
\\           for a curve with CM by Z[i], and it is anomalous exactly when a_5 = -4
\\   S_red   the primes at which rhobar_{E,p} is reducible: the isogeny degrees are
\\           [1,2] for each of the five curves, so S_red is inside {2}
\\   S_cmp   the primes dividing 6 N Nm(f), together with supp(omega_E)
\\   S_cl    the primes dividing #Cl_f(K)
\\
\\ The conductor f is derived in closed form, f = (1+i)^e (m) with Nm(f) = N/4 =
\\ 2^e m^2; gp/epsilon_family.gp states the reason and checks the character.  The
\\ enumeration of the ideals of Z[i] of norm N/4 is printed as well: it is unique
\\ only for D = -33 and D = 56, so the uniqueness shortcut of gp/excluded_set.gp
\\ does not generalise.
\\
\\ Quoted, not recomputed: the isogeny degrees, from the LMFDB rows of
\\ ../data/lmfdb_five_curves.json (pulled 2026-09-05).  The period ratio omega_E of
\\ def:periodratio is the paper's input: omega_E = 1 with A = E, so supp(omega_E)
\\ is empty; for D = 56, gp/excluded_set.gp quotes the weaker bound {2,7}, which is
\\ contained in supp(6 N Nm(f)) and so leaves S_cmp unchanged.  Everything else on
\\ each line is computed here.
\\
\\ Run from this directory:   gp -q excluded_set_family.gp        (seconds)
\\ Parameters from the environment:
\\     DLIST  comma-separated D    default "56,17,-33,-34,-39"
\\     OUT    output file          default ../data/excluded_set_family.out
\\ Output is staged to <file>.partial and moved onto the committed file at the end.
\\ ---------------------------------------------------------------------------

default(parisize, 500000000);
getdef(name, dflt) = { my(s = getenv(name)); if(type(s) == "t_STR" && s != "", s, dflt) };
DLIST = eval(Str("[", getdef("DLIST", "56,17,-33,-34,-39"), "]"));
OUT = getdef("OUT", "../data/excluded_set_family.out");
TMP = Str(OUT, ".partial");
system(Str("rm -f ", TMP));
say(s) = { print(s); write(TMP, s); };

fmtfac(n) = {
  my(f = factor(abs(n)), s = if(n < 0, "-", ""));
  for(i = 1, matsize(f)[1], if(i > 1, s = Str(s, " * "));
      s = Str(s, f[i,1], if(f[i,2] == 1, "", Str("^", f[i,2]))));
  s
};
fmtset(v) = { my(s = "{"); for(i = 1, #v, if(i > 1, s = Str(s, ", ")); s = Str(s, v[i])); Str(s, "}") };
supp(n) = Set(Vec(factor(abs(n))[,1]~));

\\ isogeny degrees quoted from the LMFDB rows in ../data/lmfdb_five_curves.json
LDS = [56, 17, -33, -34, -39];
LAB = ["12544.g1", "9248.c1", "69696.i2", "73984.d2", "48672.n2"];
labof(d) = { my(r = "not in the pull"); for(j = 1, #LDS, if(LDS[j] == d, r = LAB[j])); r; };

K = bnfinit(x^2+1, 1);
say("### the excluded set S_E of eq:Sexc for the five curves y^2 = x^3 - D x");
say(Str("pari version      : ", version()));
say("field             : K = Q(i), d_K = -4");
say("isogeny degrees [1,2] quoted from ../data/lmfdb_five_curves.json (2026-09-05);");
say("supp(omega_E) empty (A = E, omega_E = 1), the paper's input to lem:comparison.");

SUMM = List();
{for(idx = 1, #DLIST,
  my(D = DLIST[idx]);
  my(E = ellinit([0,0,0,-D,0]), N = ellglobalred(E)[1], NF = N/4, DK = -4);
  my(EE = valuation(NF,2), MM = sqrtint(NF/2^EE));
  my(F0 = if(EE % 2 == 1, (1+I)^EE*MM, 2^(EE/2)*MM));
  my(H = idealhnf(K, Mod(imag(F0)*x + real(F0), x^2+1)));
  my(CV = 1, cl = []);
  foreach(factor(N)[,1], q, my(c = elllocalred(E,q)[4]); CV *= c; cl = concat(cl, [[q, c]]));
  my(TORS = elltors(E)[1]);
  say("");
  say(Str("=== D = ", D, "   E : y^2 = x^3 - ", D, "x   LMFDB ", labof(D), " ==="));
  say(Str("  conductor N       : ", N, " = ", fmtfac(N)));
  say(Str("  local c_q         : ", cl, "   product ", CV));
  say(Str("  #E(Q)_tors        : ", TORS));
  say(Str("  isogeny_degrees   : [1, 2]   (quoted; a rational p-isogeny only at p = 2)"));
  say(Str("  Nm(f) = N/|d_K|   : ", NF, " = ", fmtfac(NF)));
  say(Str("  f                 : (1+i)^", EE, " * (", MM, ")   generator f_0 = ", F0));
  say(Str("  ideals of Z[i] of norm ", NF, " : ", #ideallist(K, NF)[NF],
          "   f is the conjugation-stable one"));
  say(Str("  Nm(f) - 1         : ", NF - 1, " = ", fmtfac(NF - 1)));

  my(Bad = 6*N*CV*TORS*DK, Sbad = supp(Bad));
  say(Str("  S_bad             : ", fmtset(Sbad), "   from 6 N prod c_v #tors d_K = ", fmtfac(Bad)));

  my(a5 = ellap(E,5), anom = (5 + 1 - a5) % 5 == 0, San = if(anom, [5], []));
  say(Str("  S_an              : ", fmtset(San), "   a_5 = ", a5, ", #Etilde(F_5) = ", 6 - a5,
          if(anom, "   (5 is anomalous)", "   (5 is not anomalous)")));

  my(Sred = [2]);
  say("  S_red             : {2}   from isogeny_degrees [1,2]: rhobar_{E,p} is irreducible at every odd p");

  my(Cmp = 6*N*NF, Scmp = supp(Cmp));
  if(D == 56, Scmp = Set(concat(Scmp, [2,7])));
  say(Str("  S_cmp             : ", fmtset(Scmp), "   from 6 N Nm(f) = ", fmtfac(Cmp),
          if(D == 56, "   union the quoted supp(omega_E) = {2,7}", "   union supp(omega_E) = {}")));

  my(bnr = bnrinit(K, H, 1), Scl = supp(bnr.no));
  say(Str("  S_cl              : ", fmtset(Scl), "   #Cl_f(K) = ", bnr.no, " = ", fmtfac(bnr.no),
          "   structure ", bnr.cyc));

  my(SE = Set(concat(concat(concat(concat(Sbad, San), Sred), Scmp), Scl)));
  my(spl = select(q -> q % 4 == 1, SE));
  my(splgood = select(q -> N % q != 0, spl));
  say(Str("  S_E               : ", fmtset(SE)));
  say(Str("  split primes in S_E                     : ", fmtset(spl)));
  say(Str("  of those, of good reduction             : ", fmtset(splgood)));
  say(Str("  conj:EK guard #Cl_f(K) >= 6             : ", bnr.no >= 6));
  listput(SUMM, [D, SE, spl, splgood]);
);}

say("");
say("summary");
say("  D      S_E                     split primes in S_E   of good reduction");
{for(j = 1, #SUMM, my(r = SUMM[j]);
  say(Str("  ", r[1], if(r[1] > 0, "     ", "    "), fmtset(r[2]),
          "            ", fmtset(r[3]), "                 ", fmtset(r[4]))));}
say("");
say("The split primes of bad reduction in S_E are excluded from the scan and from");
say("the p-adic BSD control as bad primes; the split primes of good reduction in");
say("S_E are the anomalous fives of lem:noanomalous.");
system(Str("mv -f ", TMP, " ", OUT));
print("EXCLUDEDSETFAMILYDONE");
quit
