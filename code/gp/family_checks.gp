\\ family_checks.gp -- the exceptional primes of the CLS-family scan, recomputed.
\\ ===========================================================================
\\ The scan of gp/scan_family.gp records v_fp(Reg_fp) at one working precision
\\ per prime.  This script recomputes the primes where that value is not 2 over
\\ a range of precisions, so that a reported valuation cannot be an artefact of
\\ the precision at which the scan happened to run, and reports for each prime
\\ the conductor, a_p, whether p is anomalous, the Tamagawa product and the
\\ torsion order, which decide membership of the excluded set S_E.
\\
\\ Blocks, in order:
\\   1. the exceptional lines of ../data/scan_D17.txt, ../data/scan_D-33.txt and
\\      ../data/scan_D-39.txt at precisions 6 to 14, namely (D, p) = (-39, 5),
\\      (-33, 37), (-33, 5) and (17, 5), together with the paper's testbed
\\      D = 56 at p = 5 as a control, where the expected value is 2;
\\   2. the line "15289 3 ESC" of ../data/scan_D-39.txt at precisions 6 to 16,
\\      with the primality, a_p, anomalousness and class-number data for p;
\\   3. the two primes at which the p-directional criterion of Coates, Liang
\\      and Sujatha fails, D = -39 at p = 17 and D = -34 at p = 577, in the
\\      cyclotomic direction at precision 10.
\\
\\ The bases are those of ../data/family_bases.txt; D = 56 uses the paper's
\\ basis (8,8), (9,15).
\\
\\ Output staging follows gp/deltaE.gp: every line is written to
\\ ../data/family_checks.out.partial, and that file is moved onto
\\ ../data/family_checks.out only once all seven blocks have reported and the
\\ expected number of lines is present.  An interrupted or failed run therefore
\\ leaves the committed file alone and its partial output in the .partial file.
\\ A complete run ends the output file with a FAMILYCHECKSDONE line.
\\
\\ Run from this directory:  gp -q family_checks.gp
\\ ===========================================================================

default(parisizemax, 1200000000);

OUT = "../data/family_checks.out";
TMP = "../data/family_checks.out.partial";
system(Str("rm -f ", TMP));

NOK = 0;
t0 = getabstime();
say(s) = {print(s); write(TMP, s)};

say("### the exceptional primes of the CLS-family scan, recomputed");
say(Str("pari version      : ", version()));
say("quantity          : v_p(Reg_p) = valuation(ellpadicregulator(E,p,n,G), p)");
say("curves            : y^2 = x^3 - Dx; D = 17, -33, -34, -39 are the CLS curves, D = 56 the testbed");
say("bases             : ../data/family_bases.txt; D = 56 uses (8,8), (9,15)");

chk(D, p, G) = {
  my(E = ellinit([0,0,0,-D,0]), N = ellglobalred(E)[1], ap = ellap(E, p), tam = 1);
  foreach(factor(N)[,1]~, q, tam *= elllocalred(E, q)[4]);
  say(Str("D=", D, " p=", p, "  N=", N, " (", factor(N)[,1]~, ")  a_p=", ap,
          "  anomalous=", (ap-1)%p==0, "  Tamagawa product=", tam,
          "  #tors=", elltors(E)[1]));
  for(n = 6, 14,
    say(Str("   prec ", n, ": v_p(Reg) = ", valuation(ellpadicregulator(E, p, n, G), p))));
  NOK++;
};

chk(-39, 5, [[3,12],[27,144]]);
chk(-33, 37, [[4,14],[16,68]]);
chk(-33, 5, [[4,14],[16,68]]);
chk(17, 5, [[-1,4],[-4,-2]]);
chk(56, 5, [[8,8],[9,15]]);

{my(E5 = ellinit([0,0,0,39,0]), p = 15289, G5 = [[3,12],[27,144]]);
 say(Str("D=-39 p=", p, "  isprime=", isprime(p), "  p mod 4=", p % 4,
         "  a_p=", ellap(E5, p), "  anomalous=", (ellap(E5, p) - 1) % p == 0,
         "  p | #Cl_ff candidates (1248, 1152)=", 1248 % p == 0 || 1152 % p == 0));
 for(n = 6, 16,
   say(Str("   prec ", n, ": v_p(Reg) = ", valuation(ellpadicregulator(E5, p, n, G5), p))));
 NOK++;}

{my(E5 = ellinit([0,0,0,39,0]), E4 = ellinit([0,0,0,34,0]));
 say(Str("D=-39 p=17   prec 10: v_p(Reg) = ",
         valuation(ellpadicregulator(E5, 17, 10, [[3,12],[27,144]]), 17)));
 say(Str("D=-34 p=577  prec 10: v_p(Reg) = ",
         valuation(ellpadicregulator(E4, 577, 10, [[8,28],[32,184]]), 577)));
 NOK++;}

{NLINE = if(NOK == 7, #readstr(TMP), 0);
 if(NOK == 7 && NLINE == 69,
    write(TMP, "FAMILYCHECKSDONE");
    system(Str("mv -f ", TMP, " ", OUT));
    print("elapsed ", round((getabstime() - t0)/1000), " s");
    print("FAMILYCHECKSDONE"),
    print("INCOMPLETE: ", NOK, " of 7 blocks reported, ", NLINE, " of 69 lines written.");
    print(OUT, " left unchanged; partial output in ", TMP, "."));}
quit
