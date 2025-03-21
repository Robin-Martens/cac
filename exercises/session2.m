////////////////
// Exercise 1 //
////////////////

function RSAKeyGen(b)
  bound := Round(2^(b / 2));
  p := NextPrime(Random(bound div 2, bound) : Proof := false);
  q := NextPrime(Random(bound div 2, bound) : Proof := false);

  N := p * q;
  EulerPhi := (p - 1) * (q - 1);

  repeat e := Random(EulerPhi); until GCD(EulerPhi, e) eq 1;
  _, d, _ := XGCD(e, EulerPhi);

  return N, e, d mod EulerPhi;
end function;

function RSAEncrypt(m, N, e)
  return Integers() ! ((Integers(N) ! m)^e);
end function;

function RSADecrypt(c, N, d)
  return Integers() ! ((Integers(N) ! c)^d);
end function;

function GetFactors(N, e, d)
end function;

function RSADecryptCRT(c, N, d, e)

end function;

// N, e, d := RSAKeyGen(4096);
// c := RSAEncrypt(123, N, e);
// print RSADecrypt(c, N, d);

////////////////
// Exercise 2 //
////////////////

function SquareMult(a, n)
  if a eq 0 then
    if n lt 0 then error "Negative power of non-invertible element"; end if;
    return Parent(a) ! 0;
  end if;

  if n eq 0 then return Parent(a) ! 1; end if;
  if n lt 0 then return SquareMult(1/a, -n); end if;

  powa := a;
  res := Parent(a) ! 1;
  e := n;

  while e gt 0 do
    if (e mod 2) eq 1 then res := res * powa; end if;
    powa := powa^2;
    e := e div 2;
  end while;

  return res;
end function;

F := GF(NextPrime(2^1000 : Proof := false));

// t := Cputime();
// for i := 1 to 1000 do
//   A := Random(F)^Random(2^1000);
// end for;
// Cputime(t);
// t := Cputime();
// for i := 1 to 1000 do
//   A := SquareMult(Random(F),Random(2^1000));
// end for;
// Cputime(t);

////////////////
// Exercise 3 //
////////////////

function StringToHill(s)
  if not Regexp("^[A-Z]+$", s) then
    error "The input string should only contain capital letters!";
  else
    return [Integers(26) ! StringToCode(s[i]) - 65 : i in [1..#s]];
  end if;
end function;

function HillToString(a)
  return &cat[CodeToString(((Integers() ! a[i]) + 65)) : i in [1..#a]];
end function;

function HillKeyGen(s)
  if not IsSquare(#s) then
    error "The length of the string should be square!";
  end if;

  k := Integers() ! Sqrt(#s);
  mat := ZeroMatrix(Integers(26), k, k);
  hill := StringToHill(s);

  i := 0;
  for i in [1..#hill] do
    mat[Ceiling(i / k)][((i - 1) mod k) + 1] := hill[i];
  end for;

  return mat;
end function;

function HillEncrypt(s, A)
  hill := StringToHill(s);
  k := Nrows(A);
  padLength := #hill mod k;
end function;

a :=  StringToHill("TEST");
print a;

print HillToString(a);
print HillKeyGen("ABXZ");
print HillKeyGen("ABXZ");
