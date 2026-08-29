// *****************************************************************************
//  pi_descent.m -- pi-descent for elliptic curves with CM by Z[i], at split p
//
//  E/Q with CM by Z[i] (j = 1728; model y^2 = x^3 + A x up to isomorphism),
//  K = Q(i), p = pi * pibar split in K, phi = [pi] a degree-p endomorphism.
//
//  Sel^{phihat}(E/K) embeds in the chi^{+/-1}-eigenspace of F^x/(F^x)^p for
//  F = K(E[pi]), via H^1(F, mu_p) = F^x/(F^x)^p  (Hilbert 90, so mu_p inside F
//  is NOT needed).  Classes in the image are unramified outside
//  S = {primes over the bad primes of E, and over p}, hence lie in the
//  p-Selmer group F(S,p) of F.  This script computes the F_p-dimensions of the
//  chi- and chi^{-1}-eigenspaces of F(S,p) under Delta = Gal(F/K).  Their
//  maximum b is a convention-free upper bound for
//         s := dim Sel^{phi}(E/K) = dim Sel^{phihat}(E/K).
//
//  Counting identity (TASK_BOARD_SERIES.md, "Established facts"):
//         s = rank E(Q) + dim Sha(E/K)[phi],
//  using rank E(K) = 2 rank E(Q) -- every curve y^2 = x^3 + A x is its own
//  (-1)-quadratic twist -- together with E(K)[p] = 0, which follows from chi
//  being faithful (checked at run time).  Consequently:
//
//      b <= rank E(Q)   ==>  Sha(E/K)[phi] = 0, so Sha(E/K)[p] = 0 and
//                            Sha(E/Q)[p^oo] = 0;
//      b >= rank E(Q)   is forced, and a computed b < rank E(Q) means the
//                            code is WRONG (this is the A3(iii) internal check);
//      b >  rank E(Q)   is inconclusive on its own, but is the signature the
//                            code must produce on a curve with Sha[p] =/= 0.
//
//  NO LOCAL CONDITIONS ARE IMPOSED.  b is an upper bound only, which is all the
//  argument needs, since s >= rank E(Q) always.
//
//  Derived from sel_baseline.m (= Appendix A of TASK_BOARD_SERIES.md); the
//  p = 5 numbers are reproduced line for line.
//
//  ---------------------------------------------------------------------------
//  PARAMETERS   (magma -b name:=value ... pi_descent.m)
//
//    pp      prime p, must be 1 mod 4.  If unassigned, this file only DEFINES
//            PiDescent() and returns -- which is how controls.m consumes it.
//    curve   Weierstrass coefficients, comma separated:
//            "a1,a2,a3,a4,a6" or "a4,a6"                  [default 0,0,0,-56,0]
//    grh     "on"  -> SetClassGroupBounds("GRH")
//            "off" -> no bound set, so Magma's unconditional Minkowski bound is
//                     used, and ClassGroup is called with Proof := "Full"
//                                                                 [default on]
//    ram     comma-separated hint for MaximalOrder(F : Ramification := [...]).
//            ""     -> derive it as (bad primes of E) union {p}    [default ""]
//            "none" -> omit the parameter entirely
//    optrep  "on" -> OptimisedRepresentation(F) before MaximalOrder
//                                                                [default off]
//    preord  "on" -> compute and cache MaximalOrder(F : Ramification := ...)
//            IMMEDIATELY after F is built, i.e. BEFORE the pi-torsion point,
//            the automorphism group and the character are computed.
//            Rationale: Roots()/Factorization() over a number field and
//            Automorphisms() both want the ring of integers, and if it has
//            not been computed with the ramification hint they trigger an
//            UNHINTED maximal-order computation internally.  At p = 17 the
//            run stalls at exactly that point.  Caching the hinted order
//            first is semantically a no-op -- the maximal order of F is the
//            maximal order of F -- and only changes which algorithm computes
//            it.                                                 [default off]
//    rk      rank of E over Q, for the internal check.  ""  -> skip;
//            "auto" -> compute with Magma's Rank(E)                [default ""]
//    prog    path of a progress file; each summary line is appended to it as it
//            is produced, so a run killed by `timeout` still leaves its partial
//            output on disk.  Essential for the capped p = 13 / 17 attempts.
//    tag     free-form label echoed in the header.
//
//  Author: Track A (descent), 2026-08-20.
// *****************************************************************************

SetColumns(0);
SetAutoColumns(false);

if not assigned prog then prog := ""; end if;
PROGFILE := prog;

procedure Emit(s)
  printf "%o\n", s;
  if PROGFILE ne "" then
    Write(PROGFILE, s);
  end if;
end procedure;

function ParseIntSeq(s)
  if s eq "" then return [Integers()|]; end if;
  return [ StringToInteger(x) : x in Split(s, ",") ];
end function;

DescRec := recformat< p, aInv, degF, nGal, faithful, dimFSp, chi0,
                      dimChi, dimChiInv, b, cl, minkowski, grh, ok, note >;

// ---------------------------------------------------------------------------
//  PiDescent(aInv, p, grhOn, ram, useOptRep) -> DescRec
//
//  aInv     : sequence of Weierstrass coefficients (length 2 or 5)
//  p        : rational prime, 1 mod 4
//  grhOn    : boolean; caller must already have called SetClassGroupBounds
//  ram      : "" for auto, "none" to omit, else an integer sequence
//  useOptRep: boolean
//  preOrder : boolean; cache the hinted maximal order before the T/chi stage
// ---------------------------------------------------------------------------
function PiDescent(aInv, p, grhOn, ram, useOptRep, preOrder)

  R := rec< DescRec | p := p, aInv := aInv, grh := grhOn, ok := true, note := "" >;

  error if p mod 4 ne 1, "p must be 1 mod 4 (split in Q(i))";

  K<ii> := QuadraticField(-1);
  E     := EllipticCurve(aInv);
  Emin  := MinimalModel(E);
  hasCM, cmD := HasComplexMultiplication(E);
  Emit(Sprintf("# E      = %o", E));
  Emit(Sprintf("# minimal model %o, conductor %o, disc %o",
               aInvariants(Emin), Conductor(Emin), Discriminant(Emin)));
  Emit(Sprintf("# CM     = %o (disc %o)", hasCM, hasCM select cmD else 0));
  error if not (hasCM and cmD eq -4), "curve must have CM by Z[i] (disc -4)";
  error if Conductor(Emin) mod p eq 0, "p must be a prime of good reduction";

  badp    := [ q : q in BadPrimes(Emin) ];
  Sprimes := Sort(SetToSequence({ q : q in badp } join {p}));
  Emit(Sprintf("# bad primes of E : %o ; S-primes (bad and p) : %o", badp, Sprimes));

  EK := BaseChange(E, K);

  // ---- F = K(E[pi]) ----
  t0   := Cputime();
  psi  := DivisionPolynomial(EK, p);
  d    := (p-1) div 2;
  kers := [f[1] : f in Factorization(psi) | Degree(f[1]) eq d];
  Emit(Sprintf("kernel polys of degree %o : %o", d, #kers));
  error if #kers eq 0, "no degree-(p-1)/2 factor of psi_p over K: is p split?";
  h := kers[1];

  a1,a2,a3,a4,a6 := Explode(aInvariants(E));
  Lx<a> := ext<K | h>;
  if a1 eq 0 and a3 eq 0 then
    vv := a^3 + a2*a^2 + a4*a + a6;            // identical to the baseline
    if IsSquare(vv) then
      Frel := Lx;
    else
      Rr<Y> := PolynomialRing(Lx);
      Frel  := ext<Lx | Y^2 - vv>;
    end if;
  else
    Rr<Y> := PolynomialRing(Lx);
    fY    := Y^2 + (a1*a + a3)*Y - (a^3 + a2*a^2 + a4*a + a6);
    if #Roots(fY) gt 0 then
      Frel := Lx;
    else
      Frel := ext<Lx | fY>;
    end if;
  end if;
  F := AbsoluteField(Frel);
  Emit(Sprintf("F = K(E[pi]) : [F:Q] = %o", Degree(F)));
  R`degF := Degree(F);

  if useOptRep then
    tor := Cputime();
    F   := OptimisedRepresentation(F);
    Emit(Sprintf("# OptimisedRepresentation applied [%os]", Cputime(tor)));
    Emit(Sprintf("# defining polynomial now %o", DefiningPolynomial(F)));
  end if;
  Emit(Sprintf("# field construction [%os]", Cputime(t0)));

  ramList := (ram cmpeq "none") select [Integers()|]
             else ((ram cmpeq "") select Sprimes else ram);

  if preOrder then
    tpo := Cputime();
    if ram cmpeq "none" then
      _ := MaximalOrder(F);
    else
      _ := MaximalOrder(F : Ramification := ramList);
    end if;
    Emit(Sprintf("# PRE-ORDER: hinted MaximalOrder cached before T/chi [%os]",
                 Cputime(tpo)));
  end if;

  // ---- the pi-torsion point T, Delta = Gal(F/K), the character chi ----
  EF  := BaseChange(E, F);
  rts := Roots(ChangeRing(h, F));
  error if #rts eq 0, "kernel polynomial has no root in F";
  x0  := rts[1][1];
  pts := Points(EF, x0);
  T   := pts[1];
  Emit(Sprintf("T : order %o", Order(T)));
  error if Order(T) ne p, "T is not a point of order p";

  PF<z> := PolynomialRing(F);
  zi    := Roots(z^2+1)[1][1];
  auts  := [ s : s in Automorphisms(F) | s(zi) eq zi ];
  Emit(Sprintf("#Gal(F/K) = %o  (expected %o)", #auts, Degree(F) div 2));
  R`nGal := #auts;

  chi := [];
  for s in auts do
    Ts := EF![s(T[1]), s(T[2])];
    c  := [ k : k in [1..p-1] | k*T eq Ts ][1];
    Append(~chi, c);
  end for;
  Emit(Sprintf("chi values : %o", chi));

  faithful := (#Seqset(chi) eq #auts) and (#auts eq Degree(F) div 2);
  R`faithful := faithful;
  Emit(Sprintf("# chi faithful : %o   (faithful => E(K)[p] = 0)", faithful));

  // a generator sigma0 of Delta: chi(sigma0) must be a primitive root mod p,
  // so that ker(sigma0 - chi(sigma0)) is exactly the chi-isotypic component
  gidx := [ j : j in [1..#auts] | Order(GF(p)!chi[j]) eq p-1 ];
  Emit(Sprintf("# sigma0 candidates (chi(sigma0) a primitive root mod %o) : %o of %o",
               p, #gidx, #auts));

  // ---- the maximal order, the class group, and F(S,p) ----
  tmo := Cputime();
  if ram cmpeq "none" then
    OF := MaximalOrder(F);
    Emit(Sprintf("# MaximalOrder(F) done [%os]", Cputime(tmo)));
  else
    OF := MaximalOrder(F : Ramification := ramList);
    Emit(Sprintf("# MaximalOrder(F : Ramification := %o) done [%os]",
                 ramList, Cputime(tmo)));
  end if;
  Emit(Sprintf("# disc(F) = %o", Discriminant(OF)));

  tcl := Cputime();
  if grhOn then
    Cl, mCl := ClassGroup(OF);
    Emit(Sprintf("Cl(F) = %o   [%os]  (GRH: SetClassGroupBounds(\"GRH\"))",
                 Invariants(Cl), Cputime(tcl)));
  else
    R`minkowski := MinkowskiBound(F);
    Cl, mCl := ClassGroup(OF : Proof := "Full");
    Emit(Sprintf("Cl(F) = %o   [%os]  (UNCONDITIONAL: Proof := \"Full\", Minkowski bound %o)",
                 Invariants(Cl), Cputime(tcl), R`minkowski));
  end if;
  R`cl := Invariants(Cl);

  S := {};
  for q in Sprimes do
    S := S join { pr[1] : pr in Decomposition(OF, q) };
  end for;
  Emit(Sprintf("#S = %o", #S));

  t := Cputime();
  Sel, mSel := pSelmerGroup(p, S);
  n := #Generators(Sel);
  Emit(Sprintf("dim_F%o F(S,%o) = %o   [%os]", p, p, n, Cputime(t)));
  R`dimFSp := n;

  // ---- eigenspace dimensions ----
  reps      := [ Sel.k @@ mSel : k in [1..n] ];
  dimChi    := -1;
  dimChiInv := -1;
  c0        := 0;
  for j in [1..#auts] do
    s := auts[j];
    if chi[j] eq 1 then continue; end if;   // identity char: skip (not a generator)
    M := Matrix(GF(p), [ Eltseq(mSel(s(r))) : r in reps ]);
    Emit(Sprintf("\nsigma with chi = %o :", chi[j]));
    for e in [1..p-1] do
      Ei := Eigenspace(Transpose(M), GF(p)!e);
      if Dimension(Ei) gt 0 then
        Emit(Sprintf("   eigenvalue %o : dim %o", e, Dimension(Ei)));
      end if;
    end for;
    if #gidx gt 0 and j eq gidx[1] then
      c0        := chi[j];
      dimChi    := Dimension(Eigenspace(Transpose(M), GF(p)!c0));
      dimChiInv := Dimension(Eigenspace(Transpose(M), GF(p)!(1/(GF(p)!c0))));
    end if;
  end for;

  R`chi0      := c0;
  R`dimChi    := dimChi;
  R`dimChiInv := dimChiInv;
  R`b         := (#gidx gt 0) select Max(dimChi, dimChiInv) else -1;
  if #gidx eq 0 then
    R`ok   := false;
    R`note := "chi not faithful: no generator of Delta, bound not computed";
  end if;
  return R;
end function;

// ---------------------------------------------------------------------------
//  Verdict(R, r) : the A3(iii) internal check plus the conclusion.
//  r < 0 means "rank not supplied", in which case only the numbers are printed.
// ---------------------------------------------------------------------------
procedure Verdict(R, r)
  p := R`p;
  Emit("");
  Emit("---------------- SUMMARY ----------------");
  Emit(Sprintf("curve %o   p = %o   GRH = %o", R`aInv, p,
               R`grh select "on" else "off"));
  Emit(Sprintf("[F:Q] = %o   #Gal(F/K) = %o   chi faithful = %o   Cl(F) = %o",
               R`degF, R`nGal, R`faithful, R`cl));
  Emit(Sprintf("dim F(S,%o) = %o", p, R`dimFSp));
  if R`b ge 0 then
    Emit(Sprintf("sigma0 with chi(sigma0) = %o (primitive root mod %o)", R`chi0, p));
    Emit(Sprintf("dim chi-eigenspace      = %o", R`dimChi));
    Emit(Sprintf("dim chi^{-1}-eigenspace = %o", R`dimChiInv));
    Emit(Sprintf("BOUND b = max = %o        (s <= b, convention-free)", R`b));
  else
    Emit(Sprintf("bound not computed: %o", R`note));
  end if;
  if r ge 0 and R`b ge 0 then
    Emit(Sprintf("rank E(Q) = %o, so s >= %o always; internal check requires b >= %o",
                 r, r, r));
    if R`b lt r then
      Emit("*** INTERNAL CHECK FAILED : b < rank E(Q).  THE CODE IS WRONG. ***");
    else
      Emit("INTERNAL CHECK b >= rank E(Q) : PASS");
    end if;
    if R`b le r then
      Emit(Sprintf("CONCLUSION : s = %o, so Sha(E/K)[phi] = 0, Sha(E/K)[%o] = 0,", r, p));
      Emit(Sprintf("             hence Sha(E/Q)[%o^oo] = 0.%o", p,
                   R`grh select "   [GRH-CONDITIONAL]" else "   [UNCONDITIONAL]"));
    else
      Emit(Sprintf("CONCLUSION : b = %o exceeds rank %o by %o, so 1 <= dim Sha(E/K)[phi] <= %o",
                   R`b, r, R`b - r, R`b - r));
      Emit("             is NOT excluded.  Inconclusive without local conditions.");
    end if;
  end if;
  Emit("---------------- END --------------------");
end procedure;

// ---------------------------------------------------------------------------
//  driver -- runs only when pp is supplied AND nodriver is unassigned, so that
//  controls.m can set `nodriver := true;` before `load "pi_descent.m";` and get
//  the definitions without the driver firing.
// ---------------------------------------------------------------------------
if assigned pp and not assigned nodriver then
  if not assigned curve  then curve  := "0,0,0,-56,0"; end if;
  if not assigned grh    then grh    := "on";          end if;
  if not assigned ram    then ram    := "";            end if;
  if not assigned optrep then optrep := "off";         end if;
  if not assigned preord then preord := "off";         end if;
  if not assigned rk     then rk     := "";            end if;
  if not assigned tag    then tag    := "";            end if;

  p_    := StringToInteger(pp);
  aInv_ := ParseIntSeq(curve);
  if grh eq "on" then SetClassGroupBounds("GRH"); end if;

  vA,vB,vC := GetVersion();
  Emit(Sprintf("================ p = %o ================", p_));
  Emit(Sprintf("# pi_descent.m   Magma V%o.%o-%o", vA, vB, vC));
  Emit(Sprintf("# curve  = %o", aInv_));
  Emit(Sprintf("# GRH    = %o   (SetClassGroupBounds(\"GRH\") %o)", grh,
               grh eq "on" select "APPLIED" else "NOT applied"));
  Emit(Sprintf("# ram    = %o   optrep = %o   preord = %o   rk = %o   tag = %o",
               ram eq "" select "auto" else ram, optrep, preord,
               rk eq "" select "-" else rk, tag));

  ram_ := (ram eq "none") select "none"
          else ((ram eq "") select "" else ParseIntSeq(ram));
  Res  := PiDescent(aInv_, p_, grh eq "on", ram_, optrep eq "on", preord eq "on");

  r_ := -1;
  if rk eq "auto" then
    tr := Cputime();
    r_ := Rank(EllipticCurve(aInv_));
    Emit(Sprintf("rank E(Q) = %o  (Magma Rank(E), [%os])", r_, Cputime(tr)));
  elif rk ne "" then
    r_ := StringToInteger(rk);
  end if;
  Verdict(Res, r_);
  quit;
end if;
