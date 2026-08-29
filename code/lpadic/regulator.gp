/* regulator.gp -- height side of eq:padicbsd for E: y^2 = x^3 - 56x, by PARI/GP.
 *
 * One of the TWO INDEPENDENT implementations of Reg_p required by A5 (the other
 * is regulator.sage, using Sage's padic_regulator).  Reproduces the methodology
 * of main.tex app:anchor: "Height side (PARI): ellpadicregulator(E, p, n, G) at
 * p = 5, 13 with n up to 14; unit roots via polrootspadic; the products
 * (1-alpha^-1)^2 Reg_p / log_p(1+p)^2 reported in sec:anchor."
 *
 * Parameters are read from the environment so that run.sh can drive it:
 *   P       -- the prime
 *   NPREC   -- p-adic working precision (number of digits), default 14
 *
 * Usage:  P=17 NPREC=14 gp -q regulator.gp
 */

default(parisize, 1000000000);

p = eval(getenv("P"));
nstr = getenv("NPREC");
n = if(nstr == "", 14, eval(nstr));

print("### PARI/GP height side");
print("pari version      : ", version());
print("p                 : ", p);
print("working precision : O(p^", n, ")");

E = ellinit([0,0,0,-56,0]);
print("curve             : y^2 = x^3 - 56x   [0,0,0,-56,0]");
print("conductor         : ", ellglobalred(E)[1]);
print("discriminant      : ", E.disc);
print("Tamagawa product  : ", ellglobalred(E)[4]);
print("torsion order     : ", elltors(E)[1]);

/* the saturated Mordell-Weil basis of main.tex app:mw */
P1 = [-7, 7];
P2 = [ 9, 15];
print("MW basis          : ", P1, ", ", P2);
print("on curve?         : ", ellisoncurve(E, P1), " ", ellisoncurve(E, P2));

ap = ellap(E, p);
print("a_p               : ", ap);
print("#Etilde(F_p)      : ", p + 1 - ap);
print("p | #Etilde(F_p)? : ", (p + 1 - ap) % p == 0, "   (0 = non-anomalous)");

/* unit root alpha of X^2 - a_p X + p */
rts   = polrootspadic(x^2 - ap*x + p, p, n);
units = select(r -> valuation(r, p) == 0, rts);
if(#units != 1, print("FATAL: expected exactly one unit root, got ", #units); quit(1));
alpha = units[1];
eul   = (1 - 1/alpha)^2;
print("alpha (unit root) : ", alpha);
print("(1-alpha^-1)^2    : ", eul);
print("v_p of that       : ", valuation(eul, p), "   (0 = non-anomalous)");

/* p-adic regulator, PARI's ellpadicregulator (cyclotomic, Mazur-Stein-Tate
 * normalisation -- the same normalisation Sage's padic_regulator uses) */
t0  = getwalltime();
reg = ellpadicregulator(E, p, n, [P1, P2]);
t1  = getwalltime();
print("Reg_p (PARI)      : ", reg);
print("v_p(Reg_p)        : ", valuation(reg, p), "   (expected 2)");
print("ellpadicregulator : ", (t1 - t0)/1000., " s");

lg = log(1 + p + O(p^n));
print("log_p(1+p)        : ", lg);
print("v_p(log_p(1+p))   : ", valuation(lg, p), "   (expected 1)");

/* height side of eq:padicbsd with Sha-factor 1 */
hs = eul * reg / lg^2;
print("HEIGHT SIDE       : (1-alpha^-1)^2 * Reg_p / log_p(1+p)^2 , Sha-factor 1");
print("height side       : ", hs);
print("v_p(height side)  : ", valuation(hs, p), "   (expected 0)");

/* Machine-readable digit expansions.  Format, shared by regulator.gp,
 * regulator.sage and certificates.sage so that check_agreement.py can compare
 * the two independent implementations mechanically:
 *      MACHINE <tag> v=<valuation> prec=<absolute precision> digits=[d0,d1,...]
 * where the value is  sum_i d_i p^(v+i) + O(p^prec). */
hsv = valuation(hs, p); hspr = padicprec(hs, p);
print("MACHINE hs.pari v=", hsv, " prec=", hspr, " digits=", Vecrev(digits(lift(hs/p^hsv + O(p^(hspr-hsv))), p)));
regv = valuation(reg, p); regpr = padicprec(reg, p);
print("MACHINE reg.pari v=", regv, " prec=", regpr, " digits=", Vecrev(digits(lift(reg/p^regv + O(p^(regpr-regv))), p)));
print("MACHINE ap.pari v=0 prec=0 digits=[", ap, "]");
quit;
