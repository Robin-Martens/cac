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

N, e, d := RSAKeyGen(4096);
c := RSAEncrypt(123, N, e);
print RSADecrypt(c, N, d);

