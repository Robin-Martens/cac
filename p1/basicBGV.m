clear;

// system parameters 

toy_set := false;  // set this to false for standard parameter set

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

 return s, [((a*s + p*e) mod f) mod q, -a mod q], e;
 
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
  for k := 2 to 10 do
    ck_mul_mod := BGVBasicMul(ck_mul_mod, c1);
    ck_mul_mod := BGVModSwitch(ck_mul_mod, 1);

    ck_mul_square := BGVMul(ck_mul_square, ck_mul_square, ksk);
    ck_mul_square := BGVModSwitch(ck_mul_square, 1);

    Append(~noise_mul_mod, BGVNoiseBound(ck_mul_mod, sk));
    Append(~noise_mul_square, BGVNoiseBound(ck_mul_square, sk));
  end for;

  PrintFile("values", "" : Overwrite := true);

  for i in [1..#noise_basic_mul] do 
    if i - 1 lt #noise_mul_mod then
      PrintFile("values", [noise_basic_mul[i], noise_mul[i], noise_mul_mod[i], noise_mul_square[i]]);
    else
      PrintFile("values", [noise_basic_mul[i], noise_mul[i]]);
    end if;
  end for;
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
// TASK 4 //
////////////
function Toeplitz(pol, Zq)
    row := [Zq ! Eltseq(pol)[1]] cat [Zq ! -i : i in Reverse(Remove(Eltseq(pol), 1))];
    col := Eltseq(pol);
    
    n := #row;
    m := #col;
    mat := ZeroMatrix(Integers(GetMaxModulus()), N, N);
    
    for i in [1..n] do
      for j in [1..m] do
        if i eq j then
            mat[i][j] := row[1];
        elif j gt i then
            mat[i][j] := row[(j-i)+1];
        else
            mat[i][j] := col[(i-j)+1];
        end if;
      end for;
    end for;
    
    return mat;
end function;

function CreateBlockMatrix(A, B, C, D, Zq)
  nrows := Nrows(A) + Nrows(C);
  ncols := Ncols(A) + Ncols(B);

  block_matrix := ZeroMatrix(Integers(), nrows, ncols);

  for i := 1 to Nrows(A) do
    for j := 1 to Ncols(A) do
      block_matrix[i, j] := A[i, j];
    end for;
  end for;

  for i := 1 to Nrows(B) do
    for j := 1 to Ncols(B) do
      block_matrix[i, Ncols(A) + j] := B[i, j];
    end for;
  end for;

  for i := 1 to Nrows(C) do
    for j := 1 to Ncols(C) do
      block_matrix[Nrows(A) + i, j] := C[i, j];
    end for;
  end for;

  for i := 1 to Nrows(D) do
    for j := 1 to Ncols(D) do
      block_matrix[Nrows(A) + i, Ncols(A) + j] := D[i, j];
    end for;
  end for;

  return block_matrix;
end function;

function CreateBasisMatrix(pk, q)
  Zq := Integers(q);
  Zxq<x> := PolynomialRing(Zq);

  a := Zxq ! -pk[2];
  b := pk[1];
  B1 := Eltseq(b)[1];

  A := ScalarMatrix(N, 1);

  B := ZeroMatrix(Integers(), N, 3);
  a1 := Eltseq(RowSubmatrix(Toeplitz(a, Zq), 1));
  for i := 1 to Nrows(B) do
      B[i, 1] := a1[i];
  end for;

  C := ZeroMatrix(Integers(), 3, N);
  D := Matrix(Integers(), 3, 3, [p, 1, 0, -B1, 0, 1, q, 0, 0]);

  return CreateBlockMatrix(A, B, C, D, Zq);
end function;

function BGVLatticeAttack(pk, ell)
  qell := GetBaseModulus()^ell;
  Zqell := Integers(qell);
  Zxqell<x> := PolynomialRing(Zqell);

  M := CreateBasisMatrix(pk, qell);
  
  L := Lattice(M);
  LAT, basis := BKZ(L, 20);
  s := (PolynomialRing(Integers()) ! Eltseq(LAT.1)[1..N]);
  m := BGVDecrypt(<pk, GetMaxLevel()>, s);

  if m ne 0 then
    return -s;
  end if;
  return s;
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

function ThresholdCT(ct, sk, idx)
  m1 := BGVDecrypt(ct, sk);
  m2 := BGVDecrypt(<[ct[1][1] + x^(idx), ct[1][2]], ct[2]>, sk);

  return m1 eq m2;
end function;

function FullPol(coeff)
  Z := Integers();
  Zx<x> := PolynomialRing(Z);
  return Zx ! [coeff : i in [0..N-1]];
end function;

function AppendToN(seq)
  n := #seq;

  if n ne N then
    return seq cat [0 : _ in [1..N-n]];
  end if;
  return seq;
end function;

function ThresholdCTParallel(ct, sk)
  pol := FullPol(1);

  m1 := BGVDecrypt(ct, sk);
  m2 := BGVDecrypt(<[ct[1][1] + pol, ct[1][2]], ct[2]>, sk);

  threshold_coeffs := [];
  m1_seq := AppendToN(Eltseq(m1));
  m2_seq := AppendToN(Eltseq(m2));

  for i in [1..#m1_seq] do
    if (m1_seq[i] eq m2_seq[i]) then 
      Append(~threshold_coeffs, i);
    end if;
  end for;

  return threshold_coeffs;
end function;

function FindEIdx(pk, sk, idx)
  q := GetMaxModulus();
  delta := ((q - 1) div 2);
  pk_ct := <pk, GetMaxLevel()>;

  pk_ct[1][1] +:= delta * x^(idx);

  if ThresholdCT(pk_ct, sk, idx) then
    return 0, 2;
  end if;

  for i in [1..B] do
    pk_ct[1][1] -:= p * x^(idx);
    if ThresholdCT(pk_ct, sk, idx) then
      return i, (1 + i) * 2;
    end if;
  end for;

  pk_ct[1][1] +:= B * p * x^(idx);

  for i in [1..B] do
    pk_ct[1][1] +:= p * x^(idx);
    if ThresholdCT(pk_ct, sk, idx) then
      return -i, 2 * (1 + B + i);
    end if;
  end for;

  error "No k found!";
end function;

function Done(e)
  for item in e do 
    if item eq B + 1 then
      return false;
    end if;
  end for;

  return true;
end function;

function AddCoeffsToE(coeff_idxs, value, e)
  for idx in coeff_idxs do
    e[idx] := value;
  end for;
  return e;
end function;

function CheckAndAdd(ct, sk, e, value)
  coeff_idxs := ThresholdCTParallel(ct, sk);
  e := AddCoeffsToE(coeff_idxs, value, e);
  return e;
end function;

function FindEParallel(pk, sk)
  q := GetMaxModulus();
  delta := ((q - 1) div 2);
  pk_ct := <pk, GetMaxLevel()>;
  pol := FullPol(delta);

  pk_ct[1][1] +:= pol;

  e := [B + 1 : _ in [1..N]];
  
  e := CheckAndAdd(pk_ct, sk, e, 0);
  if Done(e) then
    return e, 2;
  end if;

  for i in [1..B] do
    pk_ct[1][1] -:= FullPol(p);

    e := CheckAndAdd(pk_ct, sk, e, i);
    if Done(e) then
      return e, (1 + i) * 2;
    end if;
  end for;

  pk_ct[1][1] +:= B * FullPol(p);

  // e is negative
  for i in [1..B] do
    pk_ct[1][1] +:= FullPol(p);

    e := CheckAndAdd(pk_ct, sk, e, -i);
    if Done(e) then
      return e, 2 * (1 + B + i);
    end if;
  end for;

  error "No k found in parallel!";
end function;

function FindE(pk, sk)
  e := [];
  total_queries := 0;
  for idx in [0..N-1] do
    ei, queries := FindEIdx(pk, sk, idx);
    Append(~e, ei);
    total_queries +:= queries;
  end for;

  return e, total_queries;
end function;

function CreateBMatrix(b, e)
  b_seq := Eltseq(b);
  return Matrix(Integers(GetMaxModulus()), 1, N, [b_seq[i] - p * e[i] : i in [1..#e]]);
end function;

function BGVActiveAttack(pk, sk)
  e, queries := FindE(pk, sk);
  Zq := Integers(GetMaxModulus());
  Zqx<x> := PolynomialRing(Zq);

  a := Zqx ! -pk[2];
  b := pk[1];

  A := Transpose(Toeplitz(a, Zq));
  B := CreateBMatrix(b, e);

  found_s := Zqx ! Eltseq(Solution(A, B));
  return found_s, queries;
end function;

function BGVActiveAttackParallel(pk, sk)
  e, queries := FindEParallel(pk, sk);
  Zq := Integers(GetMaxModulus());
  Zqx<x> := PolynomialRing(Zq);

  a := Zqx ! -pk[2];
  b := pk[1];

  // S := CreateS(sk);
  A := Transpose(Toeplitz(a, Zq));
  B := CreateBMatrix(b, e);

  found_s := Zqx ! Eltseq(Solution(A, B));
  return found_s, queries;
end function;

////////////
// TASK 6 //
////////////

// 6.a
function RecNTT(a, omega, N)
  if N eq 1 then
    return [a[1]];
  else
    alpha := RecNTT([x : i -> x in Eltseq(a) | i mod 2 eq 1], omega^2, N div 2);
    beta := RecNTT([x : i -> x in Eltseq(a) | i mod 2 eq 0], omega^2, N div 2);

    gamma := [0 : _ in [1..N]];
    Ndiv := (N div 2);
    for k in [1..Ndiv] do
      delta_k := omega^(k-1) * beta[k];
      gamma[k] := Universe(a) ! (alpha[k] + delta_k);
      gamma[k + Ndiv] := Universe(a) ! (alpha[k] - delta_k);
    end for;
    
    return gamma;
  end if;
end function;

function RecINTT(a, omega, N)
  n_inv := Universe(a) ! N^(-1);
  return [n_inv * item : item in RecNTT(a, omega^(-1), N)];
end function;


// 6.b
function SchoolBookMult(a, b)
  a_seq := Eltseq(a);
  b_seq := Eltseq(b);
  n := #a_seq;
  m := #b_seq;

  c := [0 : _ in [1..n+m]];
  c := Parent(a) ! 0;
  for i in [1..n] do
    c +:= a_seq[i] * b * (Parent(a).1)^(i-1);
  end for;

  return c;
end function;

function PrimitiveNthRoot(ell, N)
  qell := GetBaseModulus()^ell;
  Zqell := Integers(qell);
  repeat
    x := Random(Zqell);
    g := x^((EulerPhi(qell)) div N);
  until g^(N div 2) ne 1; 
  return g;
end function;

function FastMult(a, b, omega, N)
  a_seq := Eltseq(a);
  b_seq := Eltseq(b);

  len_a := #a_seq;
  len_b := #b_seq;

  if len_a lt N then
    a_seq := Eltseq(a) cat [BaseRing(a) ! 0 : _ in [1..N-len_a]];
  end if;
  if len_b lt N then
    b_seq := Eltseq(b) cat [BaseRing(a) ! 0 : _ in [1..N-len_b]];
  end if;

  a_ntt := RecNTT(a_seq, omega, N);
  b_ntt := RecNTT(b_seq, omega, N);

  return Parent(a) ! RecINTT([a_ntt[i] * b_ntt[i]: i in [1..N]], omega, N);
end function;

