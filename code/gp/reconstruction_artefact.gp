\\ The rational-reconstruction artefact, reproduced
\\ ---------------------------------------------------------------------------
\\ Curve E: y^2 = x^3 - 56x (CM by Z[i], f = (56), N = 12544 = 2^8*7^2).
\\
\\ Backs paper/v2 Sec. 6.7 (ssec:exactness), which records that at working
\\ precision 1600 digits naive rational reconstruction "produced spurious
\\ factorisations of resultants in the table exhibiting 17, 281 and 349 -- all
\\ three split, all three among the 1611 primes of Sec. 5.3".  That is the paper's
\\ reason for certifying the resultants by a forced {2,7}-denominator and an
\\ explicit rounding gate instead.  No record of the artefact was in the
\\ repository; this script reproduces the naive route and reports what it gives.
\\
\\ Method.  Compute the six resultants R[F] = prod_g F(t_g) over the 384 points of
\\ D_E at working precision RECON_PREC (default 1600), then reconstruct each one
\\ with bestappr and no further gate, at eight denominator bounds: none (bestappr
\\ saturates the working precision), 10^40 (the bound deltaE.gp uses for the
\\ sums), and 10^100, 10^200, 10^400, 10^600, 10^800, 10^1200, which straddle the
\\ true denominators 2^a 7^b of the six resultants.  A reconstruction whose
\\ denominator comes out exactly of the form 2^a 7^b has recovered the certified
\\ value; the line reports that.
\\ Each reconstructed rational is trial-divided by every prime 3 <= q <= 20000
\\ other than 7, and the divisors found are reported, split ones marked, and
\\ tested against the 1611-prime scan list of ../data/all_primes_vreg.txt.  The
\\ certified small-prime support of the six resultants is
\\   R[E1*], R[wp], R[wp'], R[E1*wp + wp'/2]: none besides 2 and 7
\\   R[E1*^2 - wp]: 2239        R[E1*^3 - 3E1*wp - wp']: 3 and 5039
\\ (Sec. 6.4), so any other prime reported below is an artefact of the
\\ reconstruction.
\\
\\ The residual error of each reconstruction is printed as a binary exponent.
\\ deltaE.gp gates its rounding at exponent -1200; at 1600 decimal digits the
\\ working precision is about 5315 bits, so a reconstruction that saturates the
\\ precision passes any gate at -1200 without carrying information.
\\
\\ Conventions are copied verbatim from deltaE.gp: lemniscatic lattice
\\ Gamma = w1*Z[i], A = w1^2/Pi, s2 = 0 so theta = sigma, the six cores of
\\ eq:EKclosed, and the 384 primary points t_g = g*w1/56.  The eps-weights do not
\\ enter: a resultant is a product over all of D_E and the weights contribute a
\\ single root of unity, which the paper's table absorbs into the sign.
\\
\\ Status: this reproduces a failure mode.  Nothing it prints is evidence about
\\ E; the certified values are those of ../data/deltaE_phase2.txt.
\\
\\ Cost: about two minutes at 1600 digits.  Override with RECON_PREC.
\\ Output: ../data/reconstruction_artefact.out
\\ ---------------------------------------------------------------------------
default(parisizemax, 8000000000);

OUT = "../data/reconstruction_artefact.out";
TMP = "../data/reconstruction_artefact.out.partial";
system(Str("rm -f ", TMP));
say(s) = {print(s); write(TMP, s);};

PREC = 1600;
{my(e = getenv("RECON_PREC")); if(e != "" && e != 0, PREC = eval(e));}
default(realprecision, PREC);

isprimary(a, b) = ((a + b - 1) % 4 == 0) && ((b - a + 1) % 4 == 0);
classid(a, b) = ((a % 56) + 56) % 56 * 56 + ((b % 56) + 56) % 56;

say("reconstruction_artefact.gp --- naive rational reconstruction of the resultants");
say("curve         E: y^2 = x^3 - 56x, ainvs [0,0,0,-56,0], N = 12544 = 2^8*7^2");
say("backs         paper/v2 Sec. 6.7 (ssec:exactness), the 17 / 281 / 349 sentence");
say(Str("PARI/GP       ", version()[1], ".", version()[2], ".", version()[3]));
{say(Str("realprecision ", PREC, " decimal digits requested, ",
         default(realprecision), " allocated"));}
say("status        reproduces a failure mode; asserts nothing about E");
say("");

\\ --- the 1611-prime scan list ------------------------------------------------
scanp = List();
{my(ls = readstr("../data/all_primes_vreg.txt"));
 for(i = 1, #ls,
   my(v = strsplit(ls[i], " "));
   if(#v >= 2 && eval(v[1]) > 0, listput(scanp, eval(v[1]))));}
scanset = Set(Vec(scanp));
say(Str("scan primes read from ../data/all_primes_vreg.txt: ", #scanset));
say("");

E = ellinit([0,0,0,-56,0]);
w1 = E.omega[1];
A = w1^2/Pi;

\\ --- the 384 primary points, verbatim from deltaE.gp ------------------------
epstab = vector(56*56);
Q = Qfb(1, 0, 1);
{forprime(p = 5, 60000,
  if(p % 4 != 1 || p == 7, next);
  my(sol = qfbsolve(Q, p));
  if(sol == 0, next);
  my(a = sol[1], b = sol[2], fa = 0, fb = 0);
  for(k = 0, 3, if(isprimary(a, b), fa = a; fb = b; break); [a, b] = [-b, a]);
  my(ap = ellap(E, p), cand = [2*fa, -2*fb, -2*fa, 2*fb], kk = 0, nm = 0);
  for(k = 1, 4, if(cand[k] == ap, kk = k; nm++));
  if(nm != 1, next);
  my(id = classid(fa, fb));
  if(epstab[id] == 0, epstab[id] = kk));}
CA = List(); CB = List();
{for(a = 0, 55, for(b = 0, 55,
  if(!isprimary(a, b), next);
  if((a + b) % 2 == 0, next);
  if(a % 7 == 0 && b % 7 == 0, next);
  if(epstab[classid(a, b)] == 0, say(Str("MISSING CLASS ", [a,b])); next);
  listput(CA, a); listput(CB, b)));}
n = #CA;
say(Str("points on D_E: ", n, " (expect 384)"));

VE1 = vector(n); VP = vector(n); VPd = vector(n);
{for(j = 1, n,
  my(t = (CA[j] + CB[j]*I)*w1/56, wp2 = ellwp(E, t, 1));
  VE1[j] = ellzeta(E, t) - conj(t)/A;
  VP[j]  = wp2[1];
  VPd[j] = wp2[2]);}
say("section values done");
say("");

{RES = [prod(j = 1, n, VE1[j]),
        prod(j = 1, n, VE1[j]^2 - VP[j]),
        prod(j = 1, n, VP[j]),
        prod(j = 1, n, VPd[j]),
        prod(j = 1, n, VE1[j]*VP[j] + VPd[j]/2),
        prod(j = 1, n, VE1[j]^3 - 3*VE1[j]*VP[j] - VPd[j])];}
{RNAM = ["R[E1*]              (0,1)",
         "R[E1*^2 - wp]       (1,1)",
         "R[wp]               (0,2)",
         "R[wp']              (0,3)",
         "R[E1*wp + wp'/2]    (1,2)",
         "R[E1*^3-3E1*wp-wp'] (2,1)"];}
\\ certified small odd primes of each resultant, from ../data/deltaE_phase2.txt
{RTRUE = [[], [2239], [], [], [], [3, 5039]];}

{BNAM = ["none   ", "10^40  ", "10^100 ", "10^200 ",
         "10^400 ", "10^600 ", "10^800 ", "10^1200"];}
{BND  = [0, 10^40, 10^100, 10^200, 10^400, 10^600, 10^800, 10^1200];}
NB = #BND;

ALLSPUR = List();
NREC = 0;      \\ reconstructions attempted
NCLEAN = 0;    \\ of these, those whose small-prime support is the certified one
NSPUR = 0;     \\ of these, those reporting at least one prime that is not
NSCAN = 0;     \\ of these, those reporting a spurious prime from the 1611-prime scan

\\ Odd primes q <= 20000, q != 7, dividing the numerator or denominator of r.
smallprimes(r) = {
  my(nu = abs(numerator(r)), de = abs(denominator(r)), h = List());
  forprime(q = 3, 20000,
    if(q == 7, next);
    my(v = valuation(nu, q) - valuation(de, q));
    if(v, listput(h, [q, v])));
  Vec(h);
};

{for(k = 1, 6,
  my(R = real(RES[k]));
  say("===========================================================================");
  say(Str(RNAM[k]));
  say(Str("  magnitude 2^", exponent(R), "   certified small odd primes ", RTRUE[k]));
  for(ib = 1, NB,
    my(r, t0 = getabstime());
    r = if(BND[ib] == 0, bestappr(R), bestappr(R, BND[ib]));
    if(type(r) != "t_INT" && type(r) != "t_FRAC",
       say(Str("  bound ", BNAM[ib], " : bestappr returned ", type(r), ", skipped"));
       next);
    my(nu = numerator(r), de = denominator(r), err = abs(R - r));
    my(d27 = de / 2^valuation(de, 2) / 7^valuation(de, 7));
    my(hits = smallprimes(r), spur = List());
    for(i = 1, #hits,
      my(q = hits[i][1]);
      if(!setsearch(Set(RTRUE[k]), q), listput(spur, hits[i]); listput(ALLSPUR, q)));
    say(Str("  bound ", BNAM[ib],
            " : num ", #digits(nu), " dig, den ", #digits(de), " dig,",
            "  den = 2^", valuation(de, 2), "*7^", valuation(de, 7),
            if(d27 == 1, " exactly", Str("*", #digits(d27), "dig")),
            "  err 2^", exponent(err), "  (", getabstime() - t0, " ms)"));
    say(Str("                 odd primes <= 20000 found: ",
            if(#hits == 0, "NONE", Str(hits))));
    NREC++;
    if(#spur == 0, NCLEAN++, NSPUR++);
    my(insc = 0);
    for(i = 1, #spur, if(setsearch(scanset, spur[i][1]), insc = 1));
    NSCAN += insc;
    if(#spur,
       my(s = "");
       for(i = 1, #spur,
         my(q = spur[i][1]);
         s = Str(s, if(i > 1, ", ", ""), q,
                 if(q % 4 == 1, " (split", " (inert"),
                 if(setsearch(scanset, q), ", in the 1611-prime scan)", ")")));
       say(Str("                 SPURIOUS: ", s)),
       say("                 SPURIOUS: none"))));}

say("===========================================================================");
say("");
{say(Str("Reconstructions attempted (6 resultants x ", NB, " bounds): ", NREC));}
say(Str("  small-prime support equal to the certified one : ", NCLEAN));
say(Str("  reporting at least one prime that is not        : ", NSPUR));
say(Str("  reporting one from the 1611-prime scan           : ", NSCAN));
say("");
SPUR = Set(Vec(ALLSPUR));
{say(Str("Spurious primes over all six resultants and all ", NB, " bounds: ",
         if(#SPUR == 0, "NONE", Str(SPUR))));}
{my(sp = List(), sc = List());
 for(i = 1, #SPUR,
   if(SPUR[i] % 4 == 1, listput(sp, SPUR[i]));
   if(setsearch(scanset, SPUR[i]), listput(sc, SPUR[i])));
 say(Str("  of these, split (= 1 mod 4)      : ", if(#sp == 0, "NONE", Str(Vec(sp)))));
 say(Str("  of these, in the 1611-prime scan  : ", if(#sc == 0, "NONE", Str(Vec(sc)))));}
say("");
{my(want = [17, 281, 349], got = List(), miss = List());
 say("The three primes named in Sec. 6.7 are 17, 281, 349.");
 for(i = 1, 3,
   my(q = want[i]);
   if(setsearch(SPUR, q), listput(got, q), listput(miss, q));
   say(Str("  ", q, ": ", if(q % 4 == 1, "split", "inert"),
           ", ", if(setsearch(scanset, q), "in", "not in"),
           " the 1611-prime scan, ",
           if(setsearch(SPUR, q), "reproduced here", "not reproduced here"))));
 say(Str("  reproduced here : ", if(#got == 0, "NONE", Str(Vec(got)))));
 say(Str("  not reproduced  : ", if(#miss == 0, "NONE", Str(Vec(miss)))));}
say("");
say("READING.  A reconstruction whose residual error saturates the working");
say("precision carries no information: the error test it would face is passed by");
say("construction.  Which spurious primes appear depends on the last digits of a");
say("floating-point product of 384 transcendental factors, so it depends on the");
say("PARI version, the working precision and the order of the product; the three");
say("primes quoted in Sec. 6.7 come from one such run and are not a reproducible");
say("invariant of the curve.  What is reproducible, and is the point, is that the");
say("naive route reports small primes that the certified computation excludes.");

system(Str("mv -f ", TMP, " ", OUT));
print("RECONSTRUCTIONARTEFACTDONE");
quit
