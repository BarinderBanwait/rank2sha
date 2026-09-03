\\ scan.gp -- the horizontal regulator scan for E: y^2 = x^3 - 56x.
\\ ---------------------------------------------------------------------------
\\ Computes v_fp(Reg_fp) at the split primes (p = 1 mod 4) of a closed interval
\\ [LO, HI], where Reg_fp is the determinant of the cyclotomic fp-adic height
\\ pairing on the Mordell-Weil basis P1 = (8,8), P2 = (9,15), obtained from the
\\ p-adic sigma function of Mazur-Stein-Tate through PARI's ellpadicregulator.
\\
\\ Backs: paper Section 5.3 (ssec:scan), the statement "1611 primes; zero
\\ exceptions; zero escalations".  By Proposition prop:scaneq a prime with
\\ v_fp(Reg_fp) = 2 and p < 30000 has tilde c_2(p) in Z_p^*, so the scanned
\\ range is exactly the range in which the scan verifies.
\\
\\ Precision rule, verbatim from Section 5.3:
\\     n = 6  (p < 2000),  n = 5  (2000 <= p < 10^4),  n = 4  (p >= 10^4).
\\ Escalation rule, verbatim from Section 5.3: if the computed valuation v
\\ satisfies v >= n-1, recompute at precision n+4 and flag the output line
\\ with " ESC", and with " MAXED" as well if v >= n-1 still.
\\
\\ Parameters are read from the environment:
\\     LO   lower end of the closed interval, default 5
\\     HI   upper end of the closed interval, default 8000
\\     OUT  results file, default ../data/scan_<LO>_<HI>.txt
\\     LOG  run record, default ../data/scan.out
\\ The scan of the paper is reproduced by
\\     LO=5 HI=29999 OUT=../data/all_primes_vreg.txt  gp -q scan.gp
\\ which computes every split prime below 30000.  Splitting that interval into
\\ chunks and running them in parallel gives the same 1611 lines once they are
\\ concatenated in increasing order of p.
\\
\\ The results file is written one line per split prime, "p v", with the flags
\\ appended when the escalation rule fires, and is closed by a JOBDONE line
\\ recording the interval.  The committed file ../data/all_primes_vreg.txt
\\ carries the data lines only and no JOBDONE line.  Compare a re-run against
\\ it on the data lines.
\\
\\ Results are appended line by line, so that an interrupted run keeps what it
\\ computed.  The script therefore refuses to start if the results file already
\\ exists; move or delete it first.
\\
\\ Run from this directory:  gp -q scan.gp
\\ ---------------------------------------------------------------------------

default(parisizemax,1200000000);

exists(f) = iferr(fileclose(fileopen(f,"r")) || 1, e, 0);
\\ getenv returns the integer 0, not the empty string, when the variable is unset.
getdef(name, dflt) = {my(s = getenv(name)); if(type(s) == "t_STR" && s != "", s, dflt)};

LO  = eval(getdef("LO", "5"));
HI  = eval(getdef("HI", "8000"));
OUT = getdef("OUT", Str("../data/scan_", LO, "_", HI, ".txt"));
LOG = getdef("LOG", "../data/scan.out");

{if(exists(OUT),
   print("FATAL: results file ", OUT, " exists; move or delete it first.");
   quit(1));}

fileclose(fileopen(LOG, "w"));
say(s) = {print(s); write(LOG, s)};

say("### horizontal regulator scan, paper Section 5.3 (ssec:scan)");
say(Str("pari version      : ", version()));
say("curve             : y^2 = x^3 - 56x   [0,0,0,-56,0]");
say("MW basis          : (8,8), (9,15)");
say("quantity          : v_fp(Reg_fp) = valuation(ellpadicregulator(E,p,n,G), p)");
say("precision rule    : n = 6 (p < 2000), n = 5 (2000 <= p < 10^4), n = 4 (p >= 10^4)");
say("escalation rule   : v >= n-1  =>  recompute at n+4, flag ESC (MAXED if still v >= n-1)");
say(Str("interval          : [", LO, ", ", HI, "]  (split primes p = 1 mod 4)"));
say(Str("results file      : ", OUT));

E = ellinit([0,0,0,-56,0]);
G = [[8,8],[9,15]];

nprimes = 0; nesc = 0; nexc = 0;
{forprime(p=LO,HI,
  if(p%4!=1, next);
  nprimes++;
  my(n = if(p<2000,6, if(p<10000,5,4)));
  my(v = valuation(ellpadicregulator(E,p,n,G), p));
  if(v >= n-1,
     n += 4;
     v = valuation(ellpadicregulator(E,p,n,G), p);
     nesc++;
     write(OUT, p, " ", v, " ESC", if(v>=n-1, " MAXED", "")),
     write(OUT, p, " ", v));
  if(v != 2, nexc++));}
write(OUT, "JOBDONE ", LO, " ", HI);

say(Str("split primes      : ", nprimes));
say(Str("escalations       : ", nesc, "   (paper: zero)"));
say(Str("exceptions v != 2 : ", nexc, "   (paper: zero)"));
say("SCANDONE");
quit
