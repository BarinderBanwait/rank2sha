default(parisizemax,2500000000);
E=ellinit([0,0,0,-56,0]);
r=ellpadicbsd(E,5,5);
write("res_bsd5.txt", "p=5 ", r[1], " v=", valuation(r[2],5));
quit
