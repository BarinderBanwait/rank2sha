default(parisizemax,900000000);
E = ellinit([0,0,0,-56,0]);
G = [[8,8],[9,15]];

\\ ---------- p = 5 reconciliation ----------
p = 5; prec = 12;
a = ellap(E,p);
rt = polrootspadic(x^2 - a*x + p, p, prec); al = if(valuation(rt[1],p)==0, rt[1], rt[2]);
print("p=5: a_p = ", a, "   alpha = ", al);
eps = (1 - 1/al)^2;
R = ellpadicregulator(E,p,prec,G);
print("PARI Reg_5 = ", R);
lg = log(1 + p + O(p^prec));   \\ log_5(gamma), gamma = 1+p
Reg_gamma = R / lg^2;
print("v(Reg_gamma) = ", valuation(Reg_gamma,p), "   eps unit? v = ", valuation(eps,p));
c2pred = eps * Reg_gamma;   \\ times Sha * prod(c)/tors^2 = 1 * 4/4 = 1
print("PREDICTED c2 (p=5)  = ", c2pred);
print("SAGE     c2 (p=5)  =  1 + 4*5 + 3*5^2 + 5^3 + 5^5 + 5^6 + O(5^7)");
sagec2 = 1 + 4*5 + 3*5^2 + 5^3 + 5^5 + 5^6 + O(5^7);
print("difference v_5(pred - sage) = ", valuation(c2pred - sagec2, 5), "  (>=7 means full match)");
print("also try -pred: ", valuation(-c2pred - sagec2, 5));

\\ ---------- p = 13 PRE-REGISTERED prediction ----------
p = 13; prec = 10;
a = ellap(E,p);
rt = polrootspadic(x^2 - a*x + p, p, prec); al = if(valuation(rt[1],p)==0, rt[1], rt[2]);
eps = (1 - 1/al)^2;
R = ellpadicregulator(E,p,prec,G);
lg = log(1 + p + O(p^prec));
c2pred13 = eps * R / lg^2;
print("p=13: a_p = ", a);
print("PREDICTED c2 (p=13) = ", c2pred13);
print("PREDICTED v_13(c2) = ", valuation(c2pred13,13));
print("RECDONE");
quit
