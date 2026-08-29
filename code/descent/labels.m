// *****************************************************************************
//  labels.m -- derive a database reference for each curve used in Paper I,
//  FROM THE CURVE, rather than entering one by hand.
//
//  Why this file exists.  An earlier draft of the control table carried
//  hand-entered LMFDB labels and two of them were wrong, including the label
//  of the paper's own curve.  Anything identifying a curve in the paper must
//  now be derived.  Magma can derive the CREMONA reference offline from the
//  Cremona database; the LMFDB label is not an offline computation and is
//  handled separately (see docs/A_descent_LOG.md).
//
//  Run:  ./run.sh --bg -t 600 -j labels labels.m
//
//  Author: Track A (descent), 2026-08-21.
// *****************************************************************************

SetColumns(0); SetAutoColumns(false);
vA,vB,vC := GetVersion();
printf "# labels.m   Magma V%o.%o-%o\n", vA, vB, vC;

CURVES := [
  <"C0",  [0,0,0,-56,0]>,
  <"C1",  [0,0,0,571787,0]>,
  <"C1b", [0,0,0,-2287148,0]>,
  <"C2",  [0,0,0,7,0]>,
  <"C6",  [0,0,0,1,0]>,
  <"C3",  [0,0,0,8,0]>,
  <"C4",  [0,0,0,14,0]>,
  <"C5",  [0,0,0,-17,0]>
];

haveDB := true;
try
  D := CremonaDatabase();
  printf "# CremonaDatabase available, largest conductor = %o\n",
         LargestConductor(D);
catch e
  haveDB := false;
  printf "# CremonaDatabase NOT available: %o\n", e`Object;
end try;

printf "\n%-5o %-22o %-10o %-12o %-6o %-8o %o\n",
       "label", "a-invariants", "conductor", "Cremona", "rank", "torsion", "min model";
for c in CURVES do
  lbl, ai := Explode(c);
  E    := EllipticCurve(ai);
  Emin := MinimalModel(E);
  N    := Conductor(Emin);
  rlo, rhi := RankBounds(Emin);
  rk   := rlo eq rhi select Sprintf("%o", rlo) else Sprintf("[%o,%o]", rlo, rhi);
  T    := Invariants(TorsionSubgroup(Emin));
  cr   := "n/a";
  if haveDB then
    try
      cr := CremonaReference(Emin);
    catch e
      cr := "not in DB";
    end try;
  end if;
  printf "%-5o %-22o %-10o %-12o %-6o %-8o %o\n",
         lbl, Sprintf("%o", ai), N, cr, rk, Sprintf("%o", T),
         Sprintf("%o", aInvariants(Emin));
end for;

// the two labels a third party attributed to curves at conductor 12544:
// resolve them from the DATABASE side, by listing every curve of that
// conductor together with its Cremona reference and rank.
printf "\n# every curve of conductor 12544 in the Cremona database:\n";
if haveDB then
  try
    for E in EllipticCurves(CremonaDatabase(), 12544) do
      rlo, rhi := RankBounds(E);
      printf "  %-16o %-12o rank %o\n", Sprintf("%o", aInvariants(E)),
             CremonaReference(E), rlo eq rhi select Sprintf("%o", rlo)
                                    else Sprintf("[%o,%o]", rlo, rhi);
    end for;
  catch e
    printf "  enumeration failed: %o\n", e`Object;
  end try;
else
  printf "  (no database)\n";
end if;
printf "# done\n";
quit;
