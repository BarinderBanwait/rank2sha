SetColumns(0); SetAutoColumns(false);
lo := StringToInteger(lo); hi := StringToInteger(hi);
printf "# scan of y^2 = x^3 + A*x for A in [%o..%o]\n", lo, hi;
printf "# A  N  #badprimes  analytic_rank  Sha_an(if rank 0)  tors  prodcv\n";
for A in [lo..hi] do
  if A eq 0 then continue; end if;
  fpf := true;
  for q in PrimeDivisors(Abs(A)) do
    if A mod q^4 eq 0 then fpf := false; break; end if;
  end for;
  if not fpf then continue; end if;
  E := EllipticCurve([A,0]);
  N := Conductor(E);
  if N gt 250000 then continue; end if;
  bp := BadPrimes(E);
  if #bp gt 3 then continue; end if;
  ok, r := true, -1;
  try
    r := AnalyticRank(E);
  catch e
    ok := false;
  end try;
  if not ok then continue; end if;
  tors := #TorsionSubgroup(E);
  cv   := &*[Integers()| TamagawaNumber(E,q) : q in bp];
  if r eq 0 then
    sh := ConjecturalSha(E, []);
    printf "A=%o N=%o nbad=%o bad=%o rank=%o Sha_an=%o tors=%o cv=%o\n",
           A, N, #bp, bp, r, sh, tors, cv;
  else
    printf "A=%o N=%o nbad=%o bad=%o rank=%o Sha_an=? tors=%o cv=%o\n",
           A, N, #bp, bp, r, tors, cv;
  end if;
end for;
printf "# scan complete\n";
quit;
