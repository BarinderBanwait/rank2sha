default(parisizemax,1200000000);
E = ellinit([0,0,0,-56,0]);
G = [[8,8],[9,15]];
LO = 5; HI = 8000; OUT = "res_1.txt";
{forprime(p=LO,HI,
  if(p%4!=1, next);
  my(n = if(p<2000,6, if(p<10000,5,4)));
  my(v = valuation(ellpadicregulator(E,p,n,G), p));
  if(v >= n-1,
     n += 4;
     v = valuation(ellpadicregulator(E,p,n,G), p);
     write(OUT, p, " ", v, " ESC", if(v>=n-1, " MAXED", "")),
     write(OUT, p, " ", v)));}
write(OUT, "JOBDONE ", LO, " ", HI);
quit
