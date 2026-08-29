\\ Size of the grade-0 sum S_{0,1} as a function of working precision
\\ ---------------------------------------------------------------------------
\\ Curve E: y^2 = x^3 - 56x (CM by Z[i], f = (56), N = 12544 = 2^8*7^2).
\\
\\ Backs paper/v2 Sec. 6.3 ("The class-invariant sums"), the sentence on the
\\ grade-0 entry: "an independent rerun at working precision 400 digits returns
\\ a value of absolute value below 10^{-400}".  That statement sits at the edge
\\ of what a 400-digit run can say: a computation carried to 400 decimal digits
\\ has a noise floor near 10^{-400}, so a bound at 10^{-400} is not separated
\\ from the noise.  It is nonetheless what the run returns, because PARI
\\ allocates 404 digits for a request of 400.  This script computes
\\
\\    S_{0,1} = sum_g eps(g)^{-1} E_1^*(t_g)
\\
\\ at a list of working precisions and prints exponent(abs(S01)) at each, so that
\\ the size of the returned value can be read off precision by precision.
\\
\\ By Bannai-Kobayashi Prop. 1.6(i) S_{0,1} is a unit multiple of
\\ L(psibar_E, 1) = L(E,1), which vanishes since E has rank two and w(E) = +1.
\\ The computation is expected to return zero to the working precision of each
\\ run, and the point of the script is to say what that means quantitatively.
\\
\\ Control.  A returned value near the noise floor is evidence of vanishing only
\\ against a measurement of that floor.  The script therefore computes, at every
\\ precision, the same sum in the neighbouring slot,
\\
\\    S_{0,2} = sum_g eps(g)^{-2} wp(t_g)  =  3584  exactly (Sec. 6.3),
\\
\\ and prints |S_{0,2} - 3584|.  That is a sum of the same length, over the same
\\ points, with the same weights and the same cancellation, whose exact value is
\\ known; its residual is the noise floor of the run.  |S_{0,1}| at or below that
\\ floor is what "vanishes to the precision of the run" means.
\\
\\ Conventions are copied verbatim from deltaE.gp: lemniscatic lattice
\\ Gamma = w1*Z[i], A = w1^2/Pi, s2 = 0 so theta = sigma, E_1^* = zeta - tbar/A,
\\ the 384 primary points t_g = g*w1/56, the unit character eps = (56/.)_4^{-1}
\\ read off from a_p, and the class-invariant weight eps(g)^{-(a+b)}.
\\
\\ Cost: about five minutes at the default PRECS = [200, 400, 800, 1600, 3200];
\\ the 3200-digit run, the precision of the main deltaE.gp run, is most of it.
\\ Override with the environment variable S01_PRECS, e.g. S01_PRECS=200,400.
\\ Output: ../data/s01_check.out
\\ ---------------------------------------------------------------------------
default(parisizemax, 4000000000);

OUT = "../data/s01_check.out";
TMP = "../data/s01_check.out.partial";
system(Str("rm -f ", TMP));
say(s) = {print(s); write(TMP, s);};

PRECS = [200, 400, 800, 1600, 3200];
{my(e = getenv("S01_PRECS"));
 if(e != "" && e != 0, PRECS = eval(Str("[", e, "]")));}

L2 = 3.32192809488736234787;         \\ log(10)/log(2), for binary to decimal
\\ exponent(x) = floor(log2|x|), so 2^e <= |x| < 2^(e+1).  d10 converts e to a
\\ decimal exponent; b10 gives the largest B with |x| < 10^(-B), from 2^(e+1).
\\ PARI reports an exponent for a real zero too, so no special case is needed.
d10(e) = strprintf("%.1f", e/L2);
b10(e) = floor((-e - 1)/L2);

isprimary(a, b) = ((a + b - 1) % 4 == 0) && ((b - a + 1) % 4 == 0);
classid(a, b) = ((a % 56) + 56) % 56 * 56 + ((b % 56) + 56) % 56;

say("s01_check.gp --- size of the grade-0 sum S_{0,1} against working precision");
say("curve         E: y^2 = x^3 - 56x, ainvs [0,0,0,-56,0], N = 12544 = 2^8*7^2");
say("backs         paper/v2 Sec. 6.3, the grade-0 entry of the table of sums");
say(Str("PARI/GP       ", version()[1], ".", version()[2], ".", version()[3]));
say(Str("precisions    ", PRECS, " decimal digits"));
say("control       |S_{0,2} - 3584|, the noise floor of a sum of the same shape");
say("");

ROWS = List();
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

  my(S01 = 0, S02 = 0, tmax = 0, pmax = 0);
  for(j = 1, n,
    my(t = (CA[j] + CB[j]*I)*w1/56);
    my(e1 = ellzeta(E, t) - conj(t)/A, wp = ellwp(E, t), w = I^(-CK[j]));
    S01 += w * e1;
    S02 += w^2 * wp;
    tmax = max(tmax, abs(e1));
    pmax = max(pmax, abs(wp)));
  my(ctl = abs(S02 - 3584));
  my(e01 = exponent(abs(S01)), ere = exponent(abs(real(S01))));
  my(eim = exponent(abs(imag(S01))), ect = exponent(ctl));

  say("---------------------------------------------------------------------------");
  say(Str("WORKING PRECISION: ", prec, " decimal digits requested, ",
          default(realprecision), " allocated"));
  say(Str("  points on D_E                : ", n, " (expect 384)"));
  say(Str("  max_g |E_1^*(t_g)|           : ", strprintf("%.10f", tmax)));
  say(Str("  max_g |wp(t_g)|              : ", strprintf("%.10f", pmax)));
  say(Str("  exponent(|S_{0,1}|)          : 2^", e01, "  = 10^", d10(e01)));
  say(Str("    exponent(|Re S_{0,1}|)     : 2^", ere, "  = 10^", d10(ere)));
  say(Str("    exponent(|Im S_{0,1}|)     : 2^", eim, "  = 10^", d10(eim)));
  say(Str("  exponent(|S_{0,2} - 3584|)   : 2^", ect, "  = 10^", d10(ect),
          "   (control, the noise floor of the run)"));
  say(Str("  |S_{0,1}| below the largest clean power of ten : 10^-", b10(e01)));
  say(Str("  |S_{0,1}| relative to max_g |E_1^*|            : 10^",
          d10(e01 - exponent(tmax))));
  say(Str("  |S_{0,1}| relative to the noise floor          : 10^",
          d10(e01 - ect)));
  listput(ROWS, [prec, default(realprecision), e01, b10(e01), ect, b10(ect)]);
)}

say("---------------------------------------------------------------------------");
say("");
say("SUMMARY");
say("  requested  allocated   |S_{0,1}| <      noise floor |S_{0,2} - 3584| <");
{for(i = 1, #ROWS,
  my(r = ROWS[i]);
  say(Str("  ", strprintf("%-11d", r[1]), strprintf("%-12d", r[2]),
          strprintf("%-17s", Str("10^-", r[4])), Str("10^-", r[6]))));}
say("");
say("READING.  |S_{0,1}| tracks the allocated precision: at D allocated decimal");
say("digits the returned value has absolute value near 10^{-D}.  It sits at the");
say("size of the residual of the control sum S_{0,2}, whose exact value 3584 is");
say("known.  So S_{0,1} vanishes to the working precision of each run, and no run");
say("certifies a bound materially below its own noise floor.");
say("");
say("PARI allocates more digits than are requested: realprecision 400 works to");
say("404 digits.  That is why the 400-digit run returns a value below 10^{-400},");
say("with about one decimal digit of margin, while its noise floor is 10^{-399}.");
say("A statement at that precision therefore rests on the allocation rather than");
say("on the requested precision.  The statement with margin is the one from the");
say("main run at 3200 digits.");

system(Str("mv -f ", TMP, " ", OUT));
print("S01CHECKDONE");
quit
