// *****************************************************************************
//  field_profile.m -- the cost profile of F = K(E[pi]) as p grows.
//
//  This is the arithmetic behind the reach argument: [F:Q] = 2(p-1), and what
//  that degree costs.  It deliberately SKIPS the pi-torsion point, the
//  automorphism group and the character -- everything the full descent needs
//  beyond the field itself -- so that the cost of the FIELD can be separated
//  from the cost of the DESCENT.  At p = 17 the full descent stalls before it
//  reaches the maximal order; this script establishes whether that is the
//  field's fault or the descent's.
//
//  For each p it reports, each stage guarded so that one failure does not lose
//  the earlier stages:
//     [F:Q], disc(F) and its factorisation, unit rank,
//     MaximalOrder with the ramification hint {bad primes} u {p},
//     MinkowskiBound(F)   -- the search bound an UNCONDITIONAL class group needs,
//     ClassGroup under GRH.
//
//  Run:  ./run.sh --bg -t 1800 -j profile field_profile.m primes:=5,13,17 \
//                 prog:=$HOME/fsr2_descent/profile.prog
//
//  Author: Track A (descent), 2026-08-21.
// *****************************************************************************

SetColumns(0); SetAutoColumns(false);

if not assigned primes then primes := "5,13,17"; end if;
if not assigned prog   then prog   := "";        end if;
PROGFILE := prog;

procedure Emit(s)
  printf "%o\n", s;
  if PROGFILE ne "" then Write(PROGFILE, s); end if;
end procedure;

vA,vB,vC := GetVersion();
Emit(Sprintf("# field_profile.m   Magma V%o.%o-%o", vA, vB, vC));

E    := EllipticCurve([-56, 0]);
badp := [ q : q in BadPrimes(E) ];
K<ii>:= QuadraticField(-1);

for ps in Split(primes, ",") do
  p := StringToInteger(ps);
  Emit("");
  Emit(Sprintf("================ p = %o ================", p));
  SetClassGroupBounds("GRH");

  t0   := Cputime();
  EK   := BaseChange(E, K);
  psi  := DivisionPolynomial(EK, p);
  d    := (p-1) div 2;
  kers := [f[1] : f in Factorization(psi) | Degree(f[1]) eq d];
  if #kers eq 0 then
    Emit(Sprintf("p = %o : no degree-%o factor; not split?  SKIPPED", p, d));
    continue;
  end if;
  h := kers[1];
  Lx<a> := ext<K | h>;
  vv := a^3 - 56*a;
  if IsSquare(vv) then
    Frel := Lx;
  else
    Rr<Y> := PolynomialRing(Lx);
    Frel  := ext<Lx | Y^2 - vv>;
  end if;
  F := AbsoluteField(Frel);
  Emit(Sprintf("[F:Q] = %o   (2(p-1) = %o)   [field %os]",
               Degree(F), 2*(p-1), Cputime(t0)));
  r1, r2 := Signature(F);
  Emit(Sprintf("signature (r1,r2) = (%o,%o), unit rank = %o", r1, r2, r1+r2-1));

  ram := Sort(SetToSequence({ q : q in badp } join {p}));
  tmo := Cputime();
  ok  := true;
  try
    OF := MaximalOrder(F : Ramification := ram);
    Emit(Sprintf("MaximalOrder(F : Ramification := %o)  [%os]", ram, Cputime(tmo)));
  catch e
    ok := false;
    Emit(Sprintf("MaximalOrder FAILED after %os : %o", Cputime(tmo), e`Object));
  end try;
  if not ok then continue; end if;

  D := Discriminant(OF);
  Emit(Sprintf("disc(F) = %o", D));
  try
    Emit(Sprintf("disc(F) factored (trial division over the hint) = %o",
                 [ <q, Valuation(D, q)> : q in ram ]));
    Dr := D;
    for q in ram do Dr := Dr div q^Valuation(Dr, q); end for;
    Emit(Sprintf("residual cofactor after removing %o = %o   %o", ram, Dr,
                 Abs(Dr) eq 1 select "(GOOD: disc supported on the hint)"
                                else "(*** disc NOT supported on the hint ***)"));
  catch e
    Emit("disc factorisation skipped");
  end try;

  tmb := Cputime();
  try
    MB := MinkowskiBound(F);
    Emit(Sprintf("MinkowskiBound(F) = %o   [%os]", MB, Cputime(tmb)));
    Emit(Sprintf("   (this is the search bound an UNCONDITIONAL class group needs)"));
  catch e
    Emit(Sprintf("MinkowskiBound FAILED : %o", e`Object));
  end try;

  tcl := Cputime();
  try
    Cl := ClassGroup(OF);
    Emit(Sprintf("Cl(F) under GRH = %o   [%os]", Invariants(Cl), Cputime(tcl)));
  catch e
    Emit(Sprintf("ClassGroup(GRH) FAILED after %os : %o", Cputime(tcl), e`Object));
  end try;
end for;

Emit("");
Emit("# field_profile.m done");
quit;
