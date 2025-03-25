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

// base q for the ciphertext modulus, chosen = 1 mod p and coprime by construction
qb := 7*2^15*p + 1;
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

  // print part_dec;

  return CenterRedPol(part_dec, qell);
end function;

// decryption is just partial decryption mod p
function BGVDecrypt(ct, sk)   
 return BGVPartialDecrypt(ct, sk) mod p; 
end function;

// bound on size of partial decrypt, if this gets close to q/2 expect 
// decryption failure
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

function CTAdd(ct1, ct2, level)
  qb := GetBaseModulus();
  return [(ct1[i] + ct2[i] mod f) mod qb^level : i in [1..#ct1]];
end function;


// 1.a
function BGVAdd(c1, c2)
  l1 := c1[2];
  l2 := c2[2];
  min_level := Minimum(l1, l2);
  t1 := l1 - min_level;
  t2 := l2 - min_level;
  if t1 ne 0 then 
    c1 := BGVModSwitch(c1, t1);
  end if;
  if t2 ne 0 then 
    c2 := BGVModSwitch(c2, t2);
  end if;

  return <CTAdd(c1[1], c2[1], min_level), min_level>;
end function;

// 1.b
function BGVBasicMul(c1, c2)
  l1 := c1[2];
  l2 := c2[2];
  min_level := Minimum(l1, l2);
  t1 := l1 - min_level;
  t2 := l2 - min_level;
  if t1 ne 0 then 
    c1 := BGVModSwitch(c1, t1);
  end if;
  if t2 ne 0 then 
    c2 := BGVModSwitch(c2, t2);
  end if;
  qb := GetBaseModulus();

  RpY := PolynomialRing(Zx);
  qb := GetBaseModulus();

  mult_res := Eltseq((RpY!c1[1]) * (RpY!c2[1]));
  return <[(item mod f) mod qb^min_level : item in mult_res], min_level>;
end function;

// 1.c
function BGVKeySwitch(g, ell, ksk)
  L := GetMaxLevel();
  T := L - 1;
  qb := GetBaseModulus();

  Zqb := GF(qb);
  Rqb<x> := PolynomialRing(Zqb);
  tmp_g := g;
  first := g mod qb;
  pieces := [first];
  g -:= first;
  for i in [1..T] do
    if g mod qb^i eq 0 then
      value := ((g div qb^i) mod qb);
      Append(~pieces, value);
      g -:= value * qb^i;
    else
      Append(~pieces, Rqb ! 0);
    end if;
  end for;

  control_g := &+[pieces[i]*qb^(i-1) : i in [1..#pieces]];
  if control_g ne tmp_g then
    error "Splitting up in pieces is not correct!";
  end if;
  
  res := [pieces[1] * ksk[1][1], pieces[1] * ksk[1][2]];
  // print #ksk, T, #pieces;
  for i in [2..T+1] do
    for j in [1..#(ksk[1])] do
      res[j] +:= pieces[i] * ksk[i][j];
    end for;
  end for;
  return <res, L>;
end function;

// 1.d
function BGVMul(c1, c2, ksk)
  min_level := Minimum([c1[2], c2[2]]);
  qb := GetBaseModulus();
  // Has three elements
  basic_mul_res := BGVBasicMul(c1, c2);
  key_switch := BGVKeySwitch(basic_mul_res[1][3], min_level, ksk);
  
  ct := [(basic_mul_res[1][1] + key_switch[1][1] mod f) mod qb^min_level, (basic_mul_res[1][2] + key_switch[1][2] mod f) mod qb^min_level];
  return <ct, min_level>;
end function;

// 1.e
execute_1e := false;
if execute_1e then
  sk, pk := BGVKeyGen();
  m := RandomMessagePol();
  c1 := BGVEncrypt(m,pk);
  ksk := BGVKeySwitchingKeyGen(sk^2 mod f, sk);

  // tests for Task 1
  ck_basic_mul := c1;
  ck_mul := c1;
  noise_basic_mul := [BGVNoiseBound(ck_basic_mul, sk)];
  noise_mul := [BGVNoiseBound(ck_mul, sk)];
  for k := 2 to 16 do
    ck_basic_mul := BGVBasicMul(ck_basic_mul, c1);
    ck_mul := BGVMul(ck_mul, c1, ksk);

    Append(~noise_basic_mul, BGVNoiseBound(ck_basic_mul, sk));
    Append(~noise_mul, BGVNoiseBound(ck_mul, sk));
  end for;

  ck_mul_mod := c1;
  ck_mul_square := c1;
  noise_mul_mod := [BGVNoiseBound(ck_mul_mod, sk)];
  noise_mul_square := [BGVNoiseBound(ck_mul_square, sk)];
  for k := 2 to 16 do
    ck_mul_mod := BGVBasicMul(ck_mul_mod, c1);
    ck_mul_mod := BGVModSwitch(ck_mul_mod, 1);

    ck_mul_square := BGVMul(ck_mul_square, ck_mul_square, ksk);
    ck_mul_square := BGVModSwitch(ck_mul_square, 1);

    Append(~noise_basic_mul, BGVNoiseBound(ck_basic_mul, sk));
    Append(~noise_mul, BGVNoiseBound(ck_mul_square, sk));
  end for;

  // print noise_mul;
  // print noise_basic_mul;
  // print noise_mul_mod;
  // print noise_mul_square;
end if;

////////////
// TASK 2 //
////////////

// 2.a
function BGVEncode(ms, fs)
  Zx := PolynomialRing(Integers());
  return CRT([Zx ! m : m in ms], fs);
end function;

// 2.b
function BGVDecode(m, fs)
  return [m mod fi : fi in fs];
end function;

////////////
// TASK 5 //
////////////

// 5.a
function BGVTrivialKeyRecovery(sk)
  special_ct := <[0, 1], 1>;
  return CenterRedPol(BGVDecrypt(special_ct, sk), p);
end function;

// 5.c
function BGVActiveAttack(pk, sk)
  // print BGVNoiseBound(<pk, GetMaxLevel()>, sk);
  // print BGVPartialDecrypt(BGVEncrypt(Zx ! p - 1, pk), sk);
  return sk, 1;
end function;

////////////
// TASK 6 //
////////////

// 6.a
function RecNTT(a, omega, N)
  if N eq 1 then
    return [a[1]];
  else
    alpha := RecNTT([x : i -> x in a | i mod 2 eq 1], omega^2, N / 2);
    beta := RecNTT([x : i -> x in a | i mod 2 eq 0], omega^2, N / 2);

    gamma := [0 : _ in [1..N]];
    for k in [1..N/2] do
      delta_k := omega^k * beta[k];
      gamma[k] := alpha[k] + delta_k;
      gamma[k + N/2] := alpha[k] - delta_k;
    end for;

    return gamma;
  end if;
end function;

function RecINTT(a, omega, N)
  return 1 / N * RecNTT(a, omega^(-1), N);
end function;


// 6.b
function SchoolBookMult(a, b)
  a_seq := Eltseq(a);
  b_seq := Eltseq(b);
  n := #a_seq;
  m := #b_seq;

  c := [];
  for i in [1..n+m] do
    c_i := 0;
    for j in [1..n] do
      for k in [1..m] do
        if j + k eq i then 
          c_i +:= a_seq[j] * b_seq[k];
        end if;
      end for;
    end for;
    Append(~c, c_i);
  end for;

  return c;
end function;

function PrimitiveNthRoot(ell, N)
  qell := GetBaseModulus()^ell;
  if (qell - 1) mod N ne 0 then
    error "There is no primitive root";
  end if;
  Zqell := Integers(qell);
  repeat
    x := Random(Zqell);
    // The order of an element in the primary cyclic group is phi(q).
    g := x^((EulerPhi(qell)) div N);
  until g^(N div 2) ne 1; 
  print g^N, Order(g);
  return g;
end function;

function IntToSeq(a)
  digits := [];
  while a gt 0 do
    Append(~digits, a mod 10);
    a := a div 10;
  end while;

  return digits;
end function;

function FastMult(a, b, omega, N)
  // a_ntt := RecNTT(IntToSeq(a), omega, N);
  // b_ntt := RecNTT(IntToSeq(b), omega, N);

  // return RecINTT([a_ntt[i] * b_ntt[i]: i in [1..#IntToSeq(a)]], omega, N);
  return a;
end function;

