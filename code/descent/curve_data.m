// *****************************************************************************
//  curve_data.m -- in-house recomputation of every invariant quoted in
//  Paper I, section 2 ("The curve").
//
//  Nothing here is new mathematics.  It exists so that section 2 cites a
//  committed script and a committed output file rather than a remembered
//  number: PM_BRIEF.md, "Claim discipline".  Where a value also appears in
//  the frozen ../../v1/main.tex it is a cross-check on that paper, not a citation
//  of it.
//
//  Run:  ./run.sh -t 600 -j curve -o ../data/curve_data.out curve_data.m
//
//  Author: Track A (descent), 2026-08-21.
// *****************************************************************************

SetColumns(0); SetAutoColumns(false);

vA,vB,vC := GetVersion();
printf "# curve_data.m   Magma V%o.%o-%o\n", vA, vB, vC;
printf "############################################################\n";

E    := EllipticCurve([-56, 0]);
Emin := MinimalModel(E);
printf "E                = %o\n", E;
printf "minimal model    = %o\n", aInvariants(Emin);
printf "is minimal       = %o\n", aInvariants(E) eq aInvariants(Emin);

N := Conductor(Emin);
printf "conductor N      = %o = %o\n", N, Factorization(N);
printf "discriminant     = %o = %o\n", Discriminant(Emin), Factorization(Integers()!Discriminant(Emin));
printf "c4, c6           = %o, %o\n", cInvariants(Emin)[1], cInvariants(Emin)[2];
printf "j-invariant      = %o\n", jInvariant(Emin);
hasCM, cmD := HasComplexMultiplication(Emin);
printf "CM               = %o, discriminant %o  (K = Q(sqrt(%o)) = Q(i))\n", hasCM, cmD, cmD;

// ---- torsion ----
Tor, mTor := TorsionSubgroup(Emin);
printf "torsion          = %o, order %o, generators %o\n",
       Invariants(Tor), #Tor, [ mTor(Tor.i) : i in [1..Ngens(Tor)] ];

// ---- local data at the bad primes ----
printf "bad primes       = %o\n", BadPrimes(Emin);
prodcv := 1;
for q in BadPrimes(Emin) do
  ki, cq := Explode([* KodairaSymbol(Emin, q), TamagawaNumber(Emin, q) *]);
  printf "  q = %-3o  Kodaira %-6o  c_q = %o  (%o reduction)\n",
         q, ki, cq, ReductionType(Emin, q);
  prodcv := prodcv * cq;
end for;
printf "prod_v c_v       = %o\n", prodcv;
printf "root number      = %o\n", RootNumber(Emin);

// ---- rank and Mordell-Weil basis, certified ----
tr := Cputime();
rlo, rhi := RankBounds(Emin);
printf "RankBounds       = [%o, %o]  [%os]  %o\n", rlo, rhi, Cputime(tr),
       rlo eq rhi select "RANK CERTIFIED" else "*** NOT CERTIFIED ***";
G, mG := MordellWeilGroup(Emin);
gens  := [ mG(G.i) : i in [1..Ngens(G)] ];
printf "MordellWeilGroup = %o, generators %o\n", Invariants(G), gens;
free  := [ g : g in gens | Order(g) eq 0 ];
printf "free generators  = %o\n", free;
printf "Regulator(free)  = %o\n", Regulator(free);

// the board's basis, checked to be a basis and not merely independent
P1 := Emin![-7, 7];
P2 := Emin![9, 15];
printf "P1 = %o on E     : %o\n", P1, true;
printf "P2 = %o on E     : %o\n", P2, true;
printf "Regulator(P1,P2) = %o\n", Regulator([P1, P2]);
sat := Saturation([P1, P2], 1000);
printf "Saturation([P1,P2], 1000) = %o\n", sat;
satfree := [ P : P in sat | Order(P) eq 0 ];
printf "  free part returned by Saturation = %o\n", satfree;
printf "  Saturation returned P1 and P2 unchanged (index 1, so SATURATED) : %o\n",
       Seqset(satfree) eq {P1, P2};

// the trap recorded in the frozen paper: (8,8) = P1 + (0,0), so {P1,(8,8)}
// spans a rank-one subgroup modulo torsion
Q := Emin![8, 8];
printf "(8,8) on E, and (8,8) - P1 = %o (the 2-torsion point)\n", Q - P1;
printf "Regulator(P1, (8,8)) = %o   (degenerate: NOT a basis)\n", Regulator([P1, Q]);

// ---- isogeny class: BFS closure, not just the neighbours of E ----
// NOTE.  IsogenousCurves(E) returns the CODOMAINS of prime-degree isogenies
// from E, and that list can contain E itself.  Counting 1 + #IsogenousCurves(E)
// therefore over-counts.  Take the closure and de-duplicate by minimal model.
cls  := [ aInvariants(Emin) ];
todo := [ Emin ];
while #todo gt 0 do
  C := todo[1]; Remove(~todo, 1);
  for D in IsogenousCurves(C) do
    ai := aInvariants(MinimalModel(D));
    if ai notin cls then
      Append(~cls, ai);
      Append(~todo, MinimalModel(D));
    end if;
  end for;
end while;
printf "IsogenousCurves(E) (neighbours, may include E itself) = %o\n",
       [ aInvariants(MinimalModel(C)) : C in IsogenousCurves(Emin) ];
printf "isogeny class (closure, de-duplicated by minimal model) = %o\n", cls;
printf "  #isogeny class = %o\n", #cls;
for ai in cls do
  printf "    %o : conductor %o\n", ai, Conductor(EllipticCurve(ai));
end for;
Rx<xx> := PolynomialRing(Rationals());
try
  Equot := IsogenyFromKernel(Emin, xx);          // kernel <(0,0)>, kernel poly x
  printf "  quotient of E by <(0,0)> = %o, minimal model %o\n",
         aInvariants(Equot), aInvariants(MinimalModel(Equot));
catch e
  printf "  quotient of E by <(0,0)> : IsogenyFromKernel signature differs, skipped\n";
end try;

// ---- E is its own quadratic twist by -1 ----
Etw := QuadraticTwist(Emin, -1);
isiso := IsIsomorphic(Emin, MinimalModel(Etw));
printf "QuadraticTwist(E,-1) minimal model = %o ; isomorphic to E : %o\n",
       aInvariants(MinimalModel(Etw)), isiso;
printf "  hence rank E(K) = 2 rank E(Q) for K = Q(i)\n";

// ---- archimedean and L-data ----
try
  printf "RealPeriod       = %o\n", RealPeriod(Emin : Precision := 30);
catch e
  printf "RealPeriod       = %o\n", RealPeriod(Emin);
end try;
ar, lead := AnalyticRank(Emin : Precision := 30);
printf "AnalyticRank     = %o\n", ar;
printf "leading Taylor coefficient L^(r)(1)/r! (Magma AnalyticRank) = %o\n", lead;
printf "  so L\'\'(E,1) = 2 * that = %o\n", 2*lead;
printf "ConjecturalSha   = %o   (Magma, its own normalisations)\n",
       ConjecturalSha(Emin, free);

// ---- PERIOD NORMALISATION.  READ THIS BEFORE QUOTING Omega_E. ----
// Delta > 0, so E(R) has TWO connected components.  Magma's RealPeriod(E) is
// the period of the IDENTITY COMPONENT.  The Omega_E of the BSD formula is the
// integral over ALL of E(R), which is TWICE that when Delta > 0.  Print both,
// and print the BSD quotient with each, so that the factor of 2 is visible
// rather than inferred.
om1 := RealPeriod(Emin);
om2 := 2*om1;
printf "RealPeriod(E) (identity component)      Omega_0 = %o\n", om1;
printf "full real period (Delta > 0, 2 components) Omega_E = 2*Omega_0 = %o\n", om2;
printf "BSD quotient with Omega_E = 2*Omega_0 : L^(r)(1)/r! * tors^2 / (Omega_E*Reg*prod c_v) = %o   <-- the correct one\n",
       lead * (#Tor)^2 / (om2 * Regulator(free) * prodcv);
printf "BSD quotient with Omega_0 (WRONG normalisation)                                      = %o\n",
       lead * (#Tor)^2 / (om1 * Regulator(free) * prodcv);

// ---- a_p at the split primes that matter, to exhibit a_p even (CM) ----
printf "a_p at the six split primes of Paper I:\n";
for q in [5, 13, 17, 29, 37, 41] do
  printf "  p = %-3o  a_p = %-5o  a_p even : %o   p = 1 mod 4 : %o\n",
         q, TraceOfFrobenius(Emin, q), IsEven(TraceOfFrobenius(Emin, q)), q mod 4 eq 1;
end for;

printf "############################################################\n";
quit;
