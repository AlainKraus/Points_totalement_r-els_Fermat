P<t>:=PolynomialRing(Rationals());
Q:=FieldOfFractions(P);
PQ<x>:=PolynomialRing(Q);

u:=(3*t^2-2*t+2)/(t^2+t-1);
v:=(t^5-5*t^4+10*t^3-20*t^2+15*t-7)/((t-2)*(t^2+t-1)^2);
w:=(-3*t^5+10*t^4-20*t^3+20*t^2-20*t+6)/((t-2)*(t^2+t-1)^2);

ft:=x^6+u*x^5+v*x^4+w*x^3+v*x^2+u*x+1;

s:=(t^4-3*t^3-t^2+3*t+1)*(t-2);
a0:=-(t^2+1)*(t^3-t^2+2*t-3)/s;
a1:=-(3*t^7-9*t^6+16*t^5-15*t^4+10*t^3-11*t^2+8*t-7)/((t^2+t-1)*s);
a2:=(2*t^8-14*t^7+52*t^6-99*t^5+100*t^4-54*t^3+38*t^2-44*t+13)/((t^2+t-1)*(t-2)*s);
a3:=(t^8+t^7-21*t^6+65*t^5-90*t^4+78*t^3-57*t^2+32*t-15)/((t^2+t-1)*(t-2)*s);
a4:=-(2*t^5-6*t^4+13*t^3-14*t^2+7*t-5)/s;
a5:=-(t^2+t-1)*(t^3-t^2+2*t-3)/s;

A:=[a0,a1,a2,a3,a4,a5];


Q<alfa>,toQ:=quo<PQ | ft>;
assert toQ(x) eq alfa;
fromQ:=Inverse(toQ);
alfaInv:=fromQ(1/alfa);


beta:=&+[A[i]*x^(i-1) : i in [1..#A]];
toQ(Evaluate(ft,beta)) eq 0;

gamma:=&+[A[i]*alfaInv^(i-1) : i in [1..#A]];
toQ(Evaluate(ft,gamma)) eq 0;

betaInv:=fromQ(1/toQ(beta));
gammaInv:=fromQ(1/toQ(gamma));

p1:=x^5 + beta^5 + 1;
toQ(p1) eq 0;
p2:=alfaInv^5 + gamma^5 + 1;
toQ(p2) eq 0;
p3:=gammaInv^5 + betaInv^5 + 1;
toQ(p3) eq 0;
p4:=x^2+beta^2+1+t*(x*beta+x+beta);
toQ(p4) eq 0;
p5:=alfaInv^2+gamma^2+1+t*(alfaInv*gamma+alfaInv+gamma);
toQ(p5) eq 0;
p6:=gammaInv^2+betaInv^2+1+t*(gammaInv*betaInv+gammaInv+betaInv);
toQ(p6) eq 0;
