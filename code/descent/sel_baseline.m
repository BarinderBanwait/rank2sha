SetColumns(0);
SetClassGroupBounds("GRH");

p := StringToInteger(pp);
printf "================ p = %o ================\n", p;

K<ii> := QuadraticField(-1);
E  := EllipticCurve([-56,0]);
EK := BaseChange(E, K);

psi  := DivisionPolynomial(EK, p);
d    := (p-1) div 2;
kers := [f[1] : f in Factorization(psi) | Degree(f[1]) eq d];
printf "kernel polys of degree %o : %o\n", d, #kers;
h := kers[1];

Lx<a> := ext<K | h>;
vv := a^3 - 56*a;
if IsSquare(vv) then
  Frel := Lx;
else
  R<Y> := PolynomialRing(Lx);
  Frel := ext<Lx | Y^2 - vv>;
end if;
F := AbsoluteField(Frel);
printf "F = K(E[pi]) : [F:Q] = %o\n", Degree(F);

// the p-torsion point T generating ker(pi)
EF  := BaseChange(E, F);
rts := Roots(ChangeRing(h, F));
x0  := rts[1][1];
pts := Points(EF, x0);
T   := pts[1];
printf "T : order %o\n", Order(T);

// Delta = Gal(F/K), i.e. automorphisms fixing a chosen sqrt(-1)
PF<z> := PolynomialRing(F);
zi    := Roots(z^2+1)[1][1];
auts  := [ s : s in Automorphisms(F) | s(zi) eq zi ];
printf "#Gal(F/K) = %o  (expected %o)\n", #auts, Degree(F) div 2;

// character chi : Delta -> F_p^*  by  sigma(T) = [chi(sigma)] T
chi := [];
for s in auts do
  Ts := EF![s(T[1]), s(T[2])];
  c  := [ k : k in [1..p-1] | k*T eq Ts ][1];
  Append(~chi, c);
end for;
printf "chi values : %o\n", chi;

// S-Selmer group of F
OF := MaximalOrder(F);
S  := {};
for q in [2,7,p] do
  S := S join { pr[1] : pr in Decomposition(OF, q) };
end for;
printf "#S = %o\n", #S;
t := Cputime();
Sel, mSel := pSelmerGroup(p, S);
n := #Generators(Sel);
printf "dim_F%o F(S,%o) = %o   [%os]\n", p, p, n, Cputime(t);

// action of Delta on F(S,p), eigenspace dimensions
reps := [ Sel.k @@ mSel : k in [1..n] ];
for j in [1..#auts] do
  s := auts[j];
  if chi[j] eq 1 then continue; end if;   // identity char: skip (not a generator)
  M := Matrix(GF(p), [ Eltseq(mSel(s(r))) : r in reps ]);
  printf "\nsigma with chi = %o :\n", chi[j];
  for e in [1..p-1] do
    Ei := Eigenspace(Transpose(M), GF(p)!e);
    if Dimension(Ei) gt 0 then
      printf "   eigenvalue %o : dim %o\n", e, Dimension(Ei);
    end if;
  end for;
end for;
quit;
