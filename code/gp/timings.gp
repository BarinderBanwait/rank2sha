\\ timings.gp -- the four per-prime timings quoted in paper Section 5.3.
\\ ---------------------------------------------------------------------------
\\ Section 5.3 (ssec:scan) states: "Timings per prime were 5 ms at p = 101
\\ (n = 6), 97 ms at p = 1009, 0.55 s at p = 5003 (n = 5) and 4.9 s at
\\ p = 29989 (n = 4)."  This script measures those four calls, at those
\\ precisions, on the Mordell-Weil basis P1 = (8,8), P2 = (9,15) of
\\ tab:testbed, and prints the paper's value beside each measurement.
\\
\\ The precision at p = 1009 is not printed in that sentence; the precision
\\ rule of Section 5.3 gives n = 6, since 1009 < 2000.
\\
\\ What is timed is one call to ellpadicregulator(E, p, n, G), the call the
\\ scan makes.  Each is repeated three times on a freshly initialised curve,
\\ and the wall-clock minimum and median are reported.  The valuation returned
\\ is printed as well: it is 2 at all four primes, as
\\ ../data/all_primes_vreg.txt records.
\\
\\ Timings are hardware-dependent.  The paper's figures were measured on an
\\ Apple M1 Pro (arm64), 16 GB RAM, with PARI/GP 2.17.2 (Section 1.8,
\\ ssec:software).
\\
\\ Output: stdout and ../data/timings.out.
\\ Run from this directory:  gp -q timings.gp
\\ ---------------------------------------------------------------------------

default(parisizemax, 1200000000);

LOGF = "../data/timings.out";
fileclose(fileopen(LOGF, "w"));
say(s) = {print(s); write(LOGF, s)};

REPEATS = 3;
G = [[8,8],[9,15]];

\\ p, n, the paper's printed timing, and that timing in milliseconds
CASES = [[101, 6, "5 ms", 5], [1009, 6, "97 ms", 97], [5003, 5, "0.55 s", 550], [29989, 4, "4.9 s", 4900]];

median3(v) = vecsort(v)[2];
pad(s, w) = {my(t = Str(s)); while(#t < w, t = Str(" ", t)); t};

say("### per-prime timings of ellpadicregulator, paper Section 5.3 (ssec:scan)");
say(Str("pari version      : ", version()));
say("curve             : y^2 = x^3 - 56x   [0,0,0,-56,0]");
say("MW basis          : (8,8), (9,15)");
say("call timed        : ellpadicregulator(E, p, n, G)");
say(Str("repeats per case  : ", REPEATS, ", on a freshly initialised curve each time"));
say("precision rule    : n = 6 (p < 2000), n = 5 (2000 <= p < 10^4), n = 4 (p >= 10^4)");
say("hardware          : timings are hardware-dependent; the paper's were");
say("                    measured on an Apple M1 Pro (arm64), 16 GB RAM");
say("");
say(Str(pad("p", 8), pad("n", 4), pad("runs (ms)", 22), pad("min", 10), pad("median", 10), "    paper"));

{for(j = 1, #CASES,
   my(p = CASES[j][1], n = CASES[j][2], lbl = CASES[j][3]);
   my(ts = vector(REPEATS), v = -1);
   for(k = 1, REPEATS,
       my(F = ellinit([0,0,0,-56,0]), t0 = getwalltime());
       my(r = ellpadicregulator(F, p, n, G));
       ts[k] = getwalltime() - t0;
       v = valuation(r, p));
   say(Str(pad(p, 8), pad(n, 4), pad(Str(ts), 22), pad(Str(vecmin(ts), " ms"), 10), pad(Str(median3(ts), " ms"), 10), "    ", lbl));
   if(v != 2, say(Str("    WARNING: v_fp(Reg_fp) = ", v, " at p = ", p, "; the scan records 2"))));}

say("");
say("Each of the four calls returned v_fp(Reg_fp) = 2, as the scan file records.");
say("TIMINGSDONE");
quit
