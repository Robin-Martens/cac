R<x, y> := PolynomialRing(Rationals(), 2);
f := 3*x^2*y + 5*x*y^2 + 7;

// Now define the monomial you want:
m1 := x^2*y;
m2 := x*y^2;

// Correct way:
c := MonomialCoefficient(f, 1);
print c;  // Output: 3
