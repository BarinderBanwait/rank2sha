\\ scan_family.gp -- the horizontal regulator scan for E_D : y^2 = x^3 - D x.
\\ ===========================================================================
\\ The parametrised sibling of gp/scan.gp, which scans the paper's testbed
\\ y^2 = x^3 - 56x on a hard-coded basis.  This script takes the curve and the
\\ basis from the environment and scans the four other rank-two curves of
\\ Coates, Liang and Sujatha (CLS2, Thm 1.3), y^2 = x^3 - Dx with
\\ D = 17, -33, -34, -39, at the same quantity and under the same precision
\\ and escalation rules.
\\
\\ Quantity: v_fp(Reg_fp) at the split primes p = 1 mod 4 of good reduction in
\\ a closed interval [LO, HI], where Reg_fp is the determinant of the cyclotomic
\\ fp-adic height pairing on a Mordell-Weil basis G, through PARI's
\\ ellpadicregulator.  Generic value 2 (rank two); v >= 3 is an exceptional prime.
\\
\\ Precision rule:   n = 6 (p < 2000), n = 5 (2000 <= p < 10^4), n = 4 (p >= 10^4).
\\ Escalation rule:  if v >= n-1, recompute at n+4, flag ESC (MAXED if still v >= n-1).
\\
\\ Parameters, all read from the environment:
\\     D       integer; the curve is ellinit([0,0,0,-D,0])           (required)
\\     G       Mordell-Weil basis, a GP vector of points, e.g. "[[3,12],[27,144]]"
\\             (required; must be saturated at every prime in the interval, and
\\             the four bases of the CLS curves are in ../data/family_bases.txt)
\\     LO, HI  closed interval of primes (default 5, 8000)
\\     OUT     results file (required)
\\     LOG     run record (default OUT with ".log" appended)
\\     RESUME  if "1", an existing OUT is continued from its last recorded prime;
\\             otherwise an existing OUT is a fatal error.
\\
\\ Results: one line per split prime, "p v", with " ESC" / " MAXED" appended
\\ when the escalation rule fires, closed by "JOBDONE lo hi".  Like gp/scan.gp
\\ this script appends the lines one at a time and does not stage to .partial,
\\ so an interrupted run keeps every prime it computed; RESUME=1 continues such
\\ a run from its last recorded prime.  The committed files ../data/scan_D<D>.txt
\\ carry the data lines only and no JOBDONE line.
\\
\\ Run from this directory:
\\     D=-39 G="[[3,12],[27,144]]" LO=5 HI=29999 OUT=../data/scan_D-39.txt gp -q scan_family.gp
\\ ===========================================================================

default(parisizemax, 1200000000);

exists(f) = iferr(fileclose(fileopen(f,"r")) || 1, e, 0);
getdef(name, dflt) = {my(s = getenv(name)); if(type(s) == "t_STR" && s != "", s, dflt)};

D   = eval(getdef("D", "0"));
G   = eval(getdef("G", "0"));
LO  = eval(getdef("LO", "5"));
HI  = eval(getdef("HI", "8000"));
OUT = getdef("OUT", "");
LOG = getdef("LOG", Str(OUT, ".log"));
RESUME = getdef("RESUME", "0");

{if(D == 0 || type(G) != "t_VEC" || OUT == "",
   print("FATAL: set D, G and OUT in the environment.");
   quit(1));}

START = LO;
{if(exists(OUT),
   if(RESUME != "1",
      print("FATAL: results file ", OUT, " exists; set RESUME=1 to continue it.");
      quit(1));
   \\ Continue after the largest prime recorded; JOBDONE lines are ignored here
   \\ (a file may carry several from earlier partial runs).  If no split prime of
   \\ good reduction remains in [START, HI] the loop below is empty and only a
   \\ JOBDONE line is written, which is harmless.
   my(L = readstr(OUT), pmax = 0);
   for(i = 1, #L,
      my(s = strsplit(L[i], " "));
      if(#s >= 2 && s[1] != "JOBDONE",
         my(q = eval(s[1]));
         if(type(q) == "t_INT" && q > pmax, pmax = q)));
   START = max(LO, pmax + 1));}

say(s) = {print(s); write(LOG, s)};

E = ellinit([0,0,0,-D,0]);
{for(i = 1, #G,
   if(!ellisoncurve(E, G[i]),
      say(Str("FATAL: basis point ", G[i], " is not on y^2 = x^3 - ", D, "x"));
      quit(1)));}

say("### horizontal regulator scan, CLS family (parametrised copy of gp/scan.gp)");
say(Str("pari version      : ", version()));
say(Str("curve             : y^2 = x^3 - (", D, ")x   [0,0,0,", -D, ",0]"));
say(Str("conductor         : ", ellglobalred(E)[1]));
say(Str("torsion           : ", elltors(E)[1]));
say(Str("MW basis          : ", G));
say(Str("archimedean Reg   : ", ellheightmatrix(E, G)));
say("quantity          : v_fp(Reg_fp) = valuation(ellpadicregulator(E,p,n,G), p)");
say("precision rule    : n = 6 (p < 2000), n = 5 (2000 <= p < 10^4), n = 4 (p >= 10^4)");
say("escalation rule   : v >= n-1  =>  recompute at n+4, flag ESC (MAXED if still v >= n-1)");
say(Str("interval          : [", LO, ", ", HI, "]  (split primes p = 1 mod 4, good reduction)"));
say(Str("starting at       : ", START, if(START > LO, "  (resumed)", "")));
say(Str("results file      : ", OUT));

nprimes = 0; nesc = 0; nexc = 0; t0 = getabstime();
{forprime(p = START, HI,
  if(p % 4 != 1 || D % p == 0, next);
  nprimes++;
  my(n = if(p < 2000, 6, if(p < 10000, 5, 4)));
  my(v = valuation(ellpadicregulator(E, p, n, G), p));
  if(v >= n-1,
     n += 4;
     v = valuation(ellpadicregulator(E, p, n, G), p);
     nesc++;
     write(OUT, p, " ", v, " ESC", if(v >= n-1, " MAXED", "")),
     write(OUT, p, " ", v));
  if(v != 2, nexc++; say(Str("EXCEPTION  p = ", p, "  v = ", v)));
  if(nprimes % 50 == 0,
     say(Str("progress: p = ", p, "  primes done ", nprimes,
             "  elapsed ", round((getabstime() - t0)/1000), " s"))));}
write(OUT, "JOBDONE ", START, " ", HI);

say(Str("split primes      : ", nprimes));
say(Str("escalations       : ", nesc));
say(Str("exceptions v != 2 : ", nexc));
say("SCANDONE");
quit
