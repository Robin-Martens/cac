clear;

// system parameters 

toy_set := true;  // set this to false for standard parameter set

Z := Integers();
Zx<x> := PolynomialRing(Z);

N := 2^6;
if (not toy_set) then N := 2^10; end if;
f := x^N+1;  // polynomial modulus

p := 2^16+1;  // plaintext modulus 
Fp := GF(p);
Fpz<z> := PolynomialRing(Fp);
facs := Factorisation(Fpz ! f);
fs := [facs[i][1] : i in [1..#facs]];  // factors of f(x) for use in encoding / decoding
alpha := -Coefficient(fs[1], 0);

qb := 7*2^15*p + 1;  // base q for the ciphertext modulus, chosen = 1 mod p and coprime by construction

max_level := 8;  // max number of levels
if (not toy_set) then max_level := 12; end if;

dq := qb^max_level;  // default ciphertext modulus 
B := 5;  // errors are uniformly sampled from [-B,B]

// quick method to get max ciphertext modulus
function GetMaxModulus()
    return dq;
end function;

// quick method to get base ciphertext modulus
function GetBaseModulus()
    return qb;
end function;

// quick method to get plaintext modulus
function GetPlaintextMod()
  return p;
end function;

// quick method to get max level of ciphertext
function GetMaxLevel()
    return max_level;
end function;

// quick method to get max level of ciphertext
function GetDimension()
	return N;
end function;

// sample error polynomial
function ErrorPol()
    return Zx![Z | Random(-B,B): i in [1..N]];
end function;

// sample random polynomial with coefficients in [0..bound-1]
function RandPol(bound)
    return Zx![Z | Random(bound-1) : i in [1..N]];
end function;

// sample ternary polynomial 
function TernaryPol()
   return Zx![Z | Random(-1,1): i in [1..N]];
end function;

function RandomMessagePol()
  return Zx ! [Random(p-1) : i in [1..N]];
end function;

// centered reduction of a mod qi
function CenterRed(a, qi)

  res := a mod qi;
  if (res gt qi/2) then
    res -:= qi;
  end if;

  return res;

end function;

// centered reduction of g mod qi
function CenterRedPol(g, qi)

  return Zx ! [CenterRed(ci, qi) : ci in Eltseq(g)];

end function;

// infinity norm of polynomial with coefficients over Z
function InfNorm(a) 
  return Maximum([AbsoluteValue(ai) : ai in Eltseq(a)]);
end function;

// BGV key generation
function BGVKeyGen()

 q := GetMaxModulus();
 a := RandPol(q);
 e := ErrorPol();
 s := TernaryPol();

 return s, [((a*s + p*e) mod f) mod q, -a mod q];
 
end function;


// key switching key of sk2 under sk1
function BGVKeySwitchingKeyGen(sk2, sk1)

 q := GetMaxModulus();
 qb := GetBaseModulus();
 ksk := [];
 for i := 0 to GetMaxLevel()-1 do
   a := RandPol(q);
   e := ErrorPol();
   Append(~ksk, [((a*sk1 + p*e + qb^i*sk2) mod f) mod q, -a mod q]);
 end for;

 return ksk;
 
end function;

// ciphertext is tuple with first entry actual ciphertext coefficients and second entry level of ciphertext
function BGVEncrypt(m, pk)   

 q := GetMaxModulus();
 u := TernaryPol();
 return <[ ((u*pk[1] + p*ErrorPol() + m) mod f) mod q, ((u*pk[2] + p*ErrorPol()) mod f) mod q ], GetMaxLevel()>;

end function;


// computes partial decryption of ciphertext ct under sk
function BGVPartialDecrypt(ct, sk)

  level := ct[2];
  qell := GetBaseModulus()^level;
  coeffs := ct[1];
  part_dec := coeffs[1];
  si := sk;
  for i := 2 to #coeffs do
   part_dec := ((part_dec + coeffs[i]*si) mod f) mod qell;
   if (i lt #coeffs) then 
     si := (si*sk) mod f;
   end if;
  end for;

  return CenterRedPol(part_dec, qell);
end function;

// decryption is just partial decryption mod p
function BGVDecrypt(ct, sk)   
 return BGVPartialDecrypt(ct, sk) mod p; 
end function;

// bound on size of partial decrypt, if this gets close to q/2 expect decryption failure
function BGVNoiseBound(c, sk)
  norm := InfNorm(BGVPartialDecrypt(c, sk));
  if norm eq 0 then
    return -1;
  else
    return Log(2, norm);
  end if;
end function;

// modulus switch over qb^t if there is enough room
function BGVModSwitch(ct, t)
  ell := ct[2];
  coeffs := ct[1];
  if (t ge ell) or (t lt 1) then error "Number of levels higher than available"; end if; 
  
  qb := GetBaseModulus();
  rell := ell - t;
  
  // need to divide everything by qb^t, first need to make everything divisible
  
  _, invp, _ := XGCD(p,qb^t);  // inverse of p mod qb^t  
  coeffsd := coeffs;
  
  for i := 1 to #coeffsd do
    delta := p*CenterRedPol(-coeffs[i]*invp mod qb^t, qb^t);
    coeffsd[i] +:= delta;
    coeffsd[i] := (coeffsd[i] div qb^t) mod qb^rell;
  end for;
  
  return <coeffsd, rell>;

end function;

function CTAdd(ct1, ct2)
  return [ct1[i] + ct2[i] : i in [1..#ct1]];
end function;
function CTMult(ct1, ct2)
  return [ct1[i] * ct2[i] : i in [1..#ct1]];
end function;


// 1.a
function BGVAdd(c1, c2)
  min_level := Minimum([c1[2], c2[2]]);
  t1 := c1[2] - min_level;
  t2 := c2[2] - min_level;

  c1_reduced := c1;
  c2_reduced := c2;
  if t1 ne 0 then
    c1_reduced := BGVModSwitch(c1, t1);
  end if;
  if t2 ne 0 then
    c2_reduced := BGVModSwitch(c2, t2);
  end if;

  return <CTAdd(c1_reduced[1], c2_reduced[1]), min_level>;
end function;

// 1.b
function BGVBasicMul(c1, c2)
  min_level := Minimum([c1[2], c2[2]]);
  t1 := c1[2] - min_level;
  t2 := c2[2] - min_level;

  c1_reduced := c1;
  c2_reduced := c2;
  if t1 ne 0 then
    c1_reduced := BGVModSwitch(c1, t1);
  end if;
  if t2 ne 0 then
    c2_reduced := BGVModSwitch(c2, t2);
  end if;

  RpY := PolynomialRing(Zx);

  print Type(RpY!c1_reduced[1]);
  a := (RpY!c1_reduced[1]) * (RpY!c2_reduced[1]);
  print #a;
  return <(RpY!c1_reduced[1]) * (RpY!c2_reduced[1]), min_level>;
end function;

// 1.c
function BGVKeySwitch(g, ell, ksk)
  L := GetMaxModulus();
  T := L - 1;
  qb := GetBaseModulus();

  first := g mod qb;
  pieces := [first];
  g -:= first;
  for i := T to 1 do
    if g mod qb^i eq 0 then
      value := (g / qb^i mod qb);
      Append(~pieces, value);
      g -:= value * qb^i;
    else
      Append(~pieces, 0);
    end if;
  end for;
  
  res := ksk[0];
  for i := 1 to T do
    for j := 1 to #res do
      res[i][j] +:= pieces[i] * ksk[i][j];
    end for;
  end for;

  return res;
end function;

// 1.d
function BGVMul(c1, c2, ksk)
  min_level := Minimum([c1[2], c2[2]]);
  // Has three elements
  basic_mul_res := BGVBasicMul(c1, c2);
  key_switch := BGVKeySwitch(basic_mul_res[2], min_level, ksk);

  return <[basic_mul_res[0] + key_switch[0], basic_mul_res[1], key_switch[1]] ,min_level>;
end function;

// 1.e

