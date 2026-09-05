/* regulator.gp -- height side of eq:padicbsd for E: y^2 = x^3 - D x, by PARI/GP.
 *
 * The first of two independent implementations of Reg_p.  The second is
 * ../sage/regulator.sage, which uses Sage's padic_regulator.  The two supply
 * the "two implementations agreeing digit for digit" of the control on the
 * normalisation at the end of ssec:scan.
 *
 * Method: ellpadicregulator(E, p, n, G) on the saturated Mordell-Weil basis;
 * the unit root alpha of X^2 - a_p X + p by polrootspadic; the quantity
 * reported is (1-alpha^-1)^2 (prod_v c_v / #E(Q)_tors^2) Reg_p / log_p(1+p)^2,
 * which is the right-hand side of eq:padicbsd with #Sha(E/Q)[p^oo] = 1.  The
 * normalising factor is 1 for four of the five curves and 2 for D = -39.  That
 * value of the Sha factor is a theorem at every split p < 30000
 * (cor:shavanishing), not an assumption.
 *
 * Parameters are read from the environment so that ../sage/run.sh can drive it:
 *   P       -- the prime
 *   NPREC   -- p-adic working precision (number of digits), default 14
 *   D       -- the curve y^2 = x^3 - D x, default 56
 *   G       -- the saturated Mordell-Weil basis, default [[8,8],[9,15]]
 *
 * Usage:  P=5 NPREC=14 gp -q regulator.gp
 *         D=-39 G="[[3,12],[27,144]]" P=17 NPREC=14 gp -q regulator.gp
 */

default(parisize, 1000000000);

p = eval(getenv("P"));
getdef(name, dflt) = { my(s = getenv(name)); if(type(s) == "t_STR" && s != "", eval(s), dflt) };
n = getdef("NPREC", 14);
D = getdef("D", 56);
G = getdef("G", [[8,8],[9,15]]);

print("### PARI/GP height side");
print("pari version      : ", version());
print("p                 : ", p);
print("working precision : O(p^", n, ")");

E = ellinit([0,0,0,-D,0]);
print("curve             : y^2 = x^3 - ", D, "x   [0,0,0,", -D, ",0]");
print("conductor         : ", ellglobalred(E)[1]);
print("discriminant      : ", E.disc);
cprod = 1;
{foreach(factor(ellglobalred(E)[1])[,1], q, cprod *= elllocalred(E,q)[4]);}
print("Tamagawa product  : ", cprod);
print("torsion order     : ", elltors(E)[1]);

/* the saturated Mordell-Weil basis: tab:testbed for D = 56, and
 * ../data/family_bases.txt for the other curves */
P1 = G[1];
P2 = G[2];
print("MW basis          : ", P1, ", ", P2);
print("on curve?         : ", ellisoncurve(E, P1), " ", ellisoncurve(E, P2));

ap = ellap(E, p);
print("a_p               : ", ap);
print("#Etilde(F_p)      : ", p + 1 - ap);
print("p | #Etilde(F_p)? : ", (p + 1 - ap) % p == 0, "   (0 = non-anomalous, lem:noanomalous)");

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
print("v_p(Reg_p)        : ", valuation(reg, p), "   (prop:scaneq: 2)");
print("ellpadicregulator : ", (t1 - t0)/1000., " s");

lg = log(1 + p + O(p^n));
print("log_p(1+p)        : ", lg);
print("v_p(log_p(1+p))   : ", valuation(lg, p), "   (expected 1)");

/* right-hand side of eq:padicbsd with Sha-factor 1 (cor:shavanishing) */
bsdfac = cprod/elltors(E)[1]^2;
print("prod c_v/#tors^2  : ", bsdfac, "   (eq:padicbsd normalising factor)");
hs = eul * bsdfac * reg / lg^2;
print("HEIGHT SIDE       : (1-alpha^-1)^2 * (prod c_v/#tors^2) * Reg_p / log_p(1+p)^2 , Sha-factor 1");
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
