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

R := PolynomialRing(F31);
R.1;

GenRandomIrreduciblePol := function(K, n)
	f := Random(K);
	while not IsInvertible(f) do
	    f := Random(K);
	end while;
	return f;
end function;

GenRandomIrreduciblePol(R, 5);

