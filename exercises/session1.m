////////////////
// Exercise 1 //
////////////////

Z := Integers();
ZN := Integers(105);

z1 := Random(ZN);
z2 := Random(ZN);
z3 := Random(ZN);

z1;
z2;
z3;

// This will not work, as it's possible that the element is not invertible over the ring.
// This is only the case when z_i is coprime with 105.
//z1^(-1);
//z2^(-1);
//z3^(-1);

print_inverse := procedure(~z)
	d, s, t := XGCD(105, Z ! z);
	if d eq 1 then
		printf "The inverse of %o is: %o.\n", z, t;
	else
		printf "No inverse was found for %o, as the GCD is %o.\n", z, d;
	end if;
end procedure;

print_inverse(~z1);
print_inverse(~z2);
print_inverse(~z3);

print_inverse_lagrange := procedure(~z)
	o := Order(ZN ! z);
	if o ne 0 then
		printf "The inverse of %o is: %o.\n", z, z^(o-1);
	else
		printf "No inverse was found for %o, as the order is zero.\n", z;
	end if;
end procedure;

printf "The Euler Phi function of 105 is:, %o.\n", EulerPhi(105);

print_inverse_lagrange(~z1);
print_inverse_lagrange(~z2);
print_inverse_lagrange(~z3);

////////////////
// Exercise 2 //
////////////////

F31 := GF(31);

for x in F31 do
	res := Modexp(Z ! x, 31, 31);
	if res eq x then
		printf "[SUCCESS]: Fermat's Little Theorem holds for %o.\n", x;
	else
		printf "[FAILURE]: Fermat's Little Theorem does not hold for %o.\n", x;
	end if;
end for;

////////////////
// Exercise 3 //
////////////////

R<x> := PolynomialRing(F31);
R.1;

GenRandomIrreduciblePol := function(K, n)
  R<x> := PolynomialRing(K);
  repeat
    pol := R ! ([Random(K) : i in [1..n]] cat [1]);
  until IsIrreducible(pol);
  return pol;
end function;

print GenRandomIrreduciblePol(F31, 5);

////////////////
// Exercise 4 //
////////////////

print "=== Exercise 4 ===";

f := RandomIrreduciblePolynomial(F31, 3);
Fpn<w> := ext<F31 | f>;

print Evaluate(f, w);


elem := Fpn ! [Random(F31) : i in [1..3]];
print elem;

elem2 := Random(Fpn);
print elem2;
print Eltseq(elem2);

print elem2^(-1);
pol := PolynomialRing(F31) ! Eltseq(elem2);
d, s, t := XGCD(pol, f);
print s;

print "\n";

////////////////
// Exercise 5 //
////////////////

print "=== Exercise 5 ===";

f := RandomIrreduciblePolynomial(F31, 3);
repeat g := RandomIrreduciblePolynomial(F31, 3); until f ne g;

print f;
print g;

Fpn<w1> := ext<F31 | f>;

print Roots(f, Fpn);
print Roots(g, Fpn);

Fpn2<w2> := ext<F31 | g>;

r1 := Roots(f, Fpn2);
for i in [1..#r1] do
  print IsIrreducible(r1[i][1]);
end for;
print Roots(g, Fpn2);

print "\n";
