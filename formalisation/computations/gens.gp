default(parisizemax,1500000000);
E = ellinit([0,0,0,-56,0]);
gr = ellglobalred(E); N = gr[1];
rk = ellrank(E);
pts = rk[4];
print("ellrank points: ", pts);
\\ build an independent pair: the LMFDB basis first, then anything ellrank found
cand = concat([[8,8],[9,15]], pts);
G = []; M = matrix(0,0);
{for(i=1,#cand,
  my(T = concat(G,[cand[i]]));
  my(H = ellheightmatrix(E,T));
  if(matdet(H) > 1e-10, G = T; if(#G==2, break)));}
print("chosen basis G = ", G);
H = ellheightmatrix(E,G); Reg = matdet(H);
print("arch Reg = ", Reg);
iferr(GS = ellsaturation(E,G,20); print("sat20 basis = ", GS, "  index^2 = ", Reg/matdet(ellheightmatrix(E,GS))), err, print("sat issue"));
om = 2*real(E.omega[1]);
shaan = 11.377310478842081117925144987372230817 * elltors(E)[1]^2 / (om*Reg*gr[3]);
print("Sha_an = ", shaan);
gettime();
R1 = ellpadicregulator(E,5,8,G);  print("p=5    vReg=", valuation(R1,5), " t=",gettime());
R2 = ellpadicregulator(E,13,8,G); print("p=13   vReg=", valuation(R2,13), " t=",gettime());
R3 = ellpadicregulator(E,101,7,G);print("p=101  vReg=", valuation(R3,101), " t=",gettime());
R4 = ellpadicregulator(E,1009,6,G);print("p=1009 vReg=", valuation(R4,1009), " t=",gettime());
R5 = ellpadicregulator(E,5003,5,G);print("p=5003 vReg=", valuation(R5,5003), " t=",gettime());
print("GENSDONE");
quit
