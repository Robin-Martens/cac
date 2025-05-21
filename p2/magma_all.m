//////////////////
// PROJECT CODE //
//////////////////

////////////
// TASK 1 //
////////////

function CalculateCN(N)
  return Log(N) / (-Log(1 - 1/N));
end function;

function RandomDiseq(s, homog)
  ZN := Parent(s[1]);
  ZNn := CartesianPower(ZN, #s);

  if homog then
    b := 0;
  else
    repeat
      b := Random(ZN);
    until b ne 0;
  end if;

  repeat
    a := Random(ZNn);
  until &+[a[i] * s[i] : i in [1..#s]] ne b;

  return a, b;
end function;

////////////
// TASK 2 //
////////////

function FromDiseqToEq(a, b)
  Zp := Parent(a[1]);
  Zpn := CartesianPower(Parent(a[1]), #a);
  Zpnx := PolynomialRing(Zp, #a);
  vars := [Zpnx.i : i in [1..#a]];
  p := Characteristic(Zp);
  ax := Zpnx ! &+[a[i] * vars[i] : i in [1..#a]];

  return (ax - b)^(p - 1) - 1;
end function;

////////////
// TASK 3 //
////////////

// a
function GenW(p)
  Fp := GF(p);
  R<x, y> := PolynomialRing(Fp, 2);

  pol := R ! 0;
  for i in Fp do
    for j in Fp do
      if ((Integers() ! i + Integers() ! j) ge p) then
        pol +:= R ! (1 - (x - i)^(p - 1))*(1 - (y - j)^(p - 1));
      end if;
    end for;
  end for;

  return pol;
end function;

// b
function DigitExtract(c)
  p := Integers() ! Sqrt(#Parent(c));
  Zp := Integers(p);
  c1 := c div p;
  c0 := c - (p * c1);
  return Zp ! c0, Zp ! c1;
end function;

function DigitMerge(c0, c1)
  p := Characteristic(Parent(c0));
  Zp2 := Integers(p^2);
  return Zp2 ! ((Integers() ! c0) + (Integers() ! c1) * p);
end function;

// c
function FromDiseqToEq2(a, b)
  Zp2 := Parent(a[1]);
  p := Integers() ! Sqrt(#Zp2);
  Zp := GF(p);

  n := #a;
  Zpn := CartesianPower(Zp, 2*n);
  Zpnx := PolynomialRing(Zp, 2*n);
  vars := [Zpnx.i : i in [1..2*n]];
  
  as := [];
  for ai in a do
    a1, a2 := DigitExtract(ai);
    Append(~as, Zp ! a1);
    Append(~as, Zp ! a2);
  end for;
  b0, b1 := DigitExtract(b);

  f0 := Zpnx ! &+[as[i] * vars[i] : i in [1..2*n] | i mod 2 eq 1];
  f1 := (Zpnx ! &+[as[i] * vars[i+1] + as[i+1]*vars[i] : i in [1..2*n] | i mod 2 eq 1]); 

  W := GenW(p);
  f0_mon := Monomials(f0);
  f0_coeffs := [MonomialCoefficient(f0, mon) : mon in f0_mon];


  for i in [1..#f0_mon] do
    for j in [1..f0_coeffs[i] - 1] do
      W_partial := Evaluate(W, [j* f0_mon[i], f0_mon[i]]);
      f1 +:= W_partial;
    end for;
  end for;

  for i in [2..#f0_mon] do
    c := &+[f0_coeffs[j] * f0_mon[j] : j in [1..i-1]];
    d := f0_coeffs[i] * f0_mon[i];
    W_partial := Evaluate(W, [c, d]);
    f1 +:= W_partial;
  end for;

  part1 := (f0 - (Zp ! b0))^(p - 1);
  part2 := (f1 - (Zp ! b1))^(p - 1);

  return (part1 + part2 + Evaluate(W, [part1, part2]))^(p-1) - 1, f0, f1, as;
end function;

function EvaluateWithExtract(f, x)
  x_extracted := [];

  for xi in x do
    x1, x2 := DigitExtract(xi);
    x_extracted cat:= [x1, x2];
  end for;

  return Evaluate(f, x_extracted);
end function;

function ExtractS(sols)
  merged_sols := [];
  for sol in sols do
    if IsZero([i : i in sol]) then
        continue;
    else
      s := [DigitMerge(sol[j], sol[j+1]) : j in [1..#sol by 2]];
      Append(~merged_sols, s);
    end if;
  end for;

  return merged_sols;
end function;

////////////
// TASK 4 //
////////////
function FirstNonPositiveCoefficient(f)
  for i in [0..Degree(f)] do
    c := Coefficient(f, i);
    if c le 0 then
      return i;
    end if;
  end for;
end function;

function CalcDreg(eqs, n)
  I := Ideal(eqs);
  b := Basis(I);
  degs := [Degree(e) : e in eqs];

  R<z> := PowerSeriesRing(Integers(), 200);
  H := &*[1-z^2 : i in [1..#eqs]]/(1 - z)^n;
  // print H;

  return FirstNonPositiveCoefficient(H);
end function;


////////////
// TASK 5 //
////////////
function FromDiseqToLinEq(a, b)
  pol := FromDiseqToEq(a, b);
  Z := Parent(pol);
  ZN := BaseRing(Parent(pol));
  p := Characteristic(Z);

  monomials := {@@};
  for i in [1..p-1] do
    monomials join:= MonomialsOfDegree(Z, i);
  end for;

  coeffs := [];
  for monomial in monomials do
    Append(~coeffs, ZN ! MonomialCoefficient(pol, monomial));
  end for;

  return coeffs, MonomialCoefficient(pol, 1);
end function;

////////////
// TASK 6 //
////////////

function TupToSeq(tup)
  return [ tup[i] : i in [1..#tup] ];
end function;

function EltNeq(a, b)
  len_a := Nrows(a);
  len_b := Nrows(b);
  assert len_a eq len_b;

  for i in [1..len_a] do
    if a[i] eq b[i] then
      return false;
    end if;
  end for;

  return true;
end function;

function EltNeq0(s)
  return &and[ s[i][1] ne 0 : i in [1..NumberOfRows(s)]];
end function;

function RandomMat(N, m)
  ZN := Integers(N);
  return RandomMatrix(ZN, m, m);
end function;

function Trunc(C, n)
  return Submatrix(C, 1, 1, n, n);
end function;

function KeyGen(N, n)
  ZN := Integers(N);
  ZNn := CartesianPower(ZN, n);

  s := Random(ZNn);
  CN := CalculateCN(N);
  m :=  Round(CN * n);

  entries := [];
  for _ in [1..m] do
    a, _ := RandomDiseq(s, true);
    entries := entries cat TupToSeq(a);
  end for;

  return Matrix(ZN, n, 1, TupToSeq(s)), Matrix(ZN, m, n, entries);
end function;

function Commit(s, A)
  n := Ncols(A);
  N := Characteristic(BaseRing(A));
  ZN := Integers(N);
  m := Round(CalculateCN(N) * n);

  i := 0;
  repeat
    i +:= 1;
    C := RandomMat(N, m);
  until EltNeq0(C * A * s) and Determinant(Trunc(C, n)) ne 0;

  return C, C * A * Trunc(C, n);
end function;

function Response(c, s, C)
  n := Nrows(s);
  if c eq 0 then
    return C;
  else
    return (Trunc(C, n))^(-1) * s;
  end if;
end function;

function Verify(c, A, M, resp)
  n := Ncols(A);
  N := Characteristic(BaseRing(A));
  ZN := Integers(N);

  if c eq 0 then
    return M eq (resp * A) * Trunc(resp, n);
  else
    return EltNeq0(M * resp);
  end if;
end function;

////////////
// TASK 7 //
////////////

lambda := 160;
function SimpleHash(s)
  input := IntegerToString(SequenceToInteger(StringToBytes(s), 256), 16);
  return Intseq(StringToInteger(SHA1(input), 16), 2, lambda);
end function;

function DiseqSign(s, A, mess)
  n := Ncols(A);
  N := Characteristic(BaseRing(A));
  ZN := Integers(N);

  Cs := [];
  Ms := [];
  for i in [1..lambda] do
    C, M := Commit(s, A);
    Ms cat:= [M];
    Cs cat:= [C];
  end for;

  hash_input := <A, mess, Explode(Ms)>;
  c := SimpleHash(Sprint(hash_input));

  resps := <Response(c[i], s, Cs[i]) : i  in [1..lambda]>;

  sig := <>;
  for i in [1..lambda] do
    sig cat:=<Ms[i], resps[i]>;
  end for;

  return sig;
end function;

function VerifySign(sig, A, mess)
  Ms := <sig[i] : i in [1..#sig by 2]>;
  resps := <sig[i] : i in [2..#sig by 2]>;
  hash_input := <A, mess, Explode(Ms)>;
  c := SimpleHash(Sprint(hash_input));

  for i in [1..lambda] do
    if Verify(c[i], A, Ms[i], resps[i]) eq false then
      return false;
    end if;
  end for;

  return true;
end function;

////////////
// TASK 9 //
////////////

function GetDiseqVectorFromMatrix(M)
  N := Characteristic(BaseRing(M));
  ZN := Integers(N);
  
  i := 0;
  repeat
    m := RandomMatrix(ZN, Ncols(M), 1);
    // i +:= 1;

  until EltNeq0(M * m);
  return m;
end function;

function RandomCommit(A)
  n := Ncols(A);
  N := Characteristic(BaseRing(A));
  ZN := Integers(N);
  CN := CalculateCN(N);
  m :=  Round(CN * n);

  m_vec, M := KeyGen(N, n);

  repeat
    C := RandomMat(N, m);
  until Determinant(C) ne 0 and Determinant(Trunc(C, n)) ne 0 and C * A * Trunc(C, n) eq A;
  return C, m_vec, M;
end function;


function ForgeResponse(c, M, C)
  n := Ncols(M);
  if c eq 0 then
    return C;
  else
    return GetDiseqVectorFromMatrix(M);
  end if;
end function;

function DiseqSignForge(A, mess)
  n := Ncols(A);
  N := Characteristic(BaseRing(A));
  ZN := Integers(N);

  Cs := [];
  Ms := [];
  for i in [1..lambda] do
    C, m, M  := RandomCommit(A);
    break;
    Ms cat:= [M];
    Cs cat:= [C];
  end for;

  hash_input := <A, mess, Explode(Ms)>;
  c := SimpleHash(Sprint(hash_input));

  resps := [ForgeResponse(c[1], Ms[1], Cs[1])];
  for i in [2..lambda] do
    resps cat:= ForgeResponse(c[i], Ms[i], Cs[i]);
  end for;

  sig := <>;
  for i in [1..lambda] do
    sig cat:=<Ms[i], resps[i]>;
  end for;

  return sig;
end function;

//////////////
//TEST CODE //
//////////////
SetPrintLevel("Maximal");
SetQuitOnError(false);

n := 8;

test_task1 := false;
test_task2 := false;
test_task3 := false;
test_task4 := true;
test_task5 := false;
test_task6 := false;
test_task7 := false;
test_task9 := false;

////////////
// TASK 1 //
////////////

if test_task1 then
  ZN := GF(3);
  ZNn := CartesianPower(ZN, n);

  s := Random(ZNn);
  a, b := RandomDiseq(s, false);

  assert b ne 0;
  assert &+[a[i] * s[i] : i in [1..#s]] ne b;

  a, b := RandomDiseq(s, true);

  assert b eq 0;
  assert &+[a[i] * s[i] : i in [1..#s]] ne 0;

  print "All tests of task 1 passed.";
end if;

////////////
// TASK 2 //
////////////

if test_task2 then
  ZN := GF(3);
  ZNn := CartesianPower(ZN, n);

  s := Random(ZNn);
  a, b := RandomDiseq(s, false);
  e := FromDiseqToEq(a, b);

  // 2.c
  for r in [1, 2, 3] do
    for p in [2, 3, 5] do
      ZN := GF(p);
      ZNn := CartesianPower(ZN, n);
      s := Random(ZNn);

      eqs := [];
      Cp := CalculateCN(p);
      t := Cputime();
      for i in [1..Ceiling(Cp * n * r)] do
        a, b := RandomDiseq(s, false);
        e := FromDiseqToEq(a, b);
        // assert Evaluate(e, s) eq 0;
        Append(~eqs, e);
      end for;
      
      print "r = ", r, " | p = ", p, " | ", #eqs;
      sol := Variety(Ideal(eqs));
      // print "SOL:", Variety(Ideal(eqs));
      print "Time taken: ", Cputime(t), " seconds";
      print "=====";
      // print "S:", s;
    end for;
  end for;

  for p in [2, 3, 5, 7] do
    ZN := GF(p);
    ZNn := CartesianPower(ZN, n);
    Zpnx := PolynomialRing(ZN, n);
    s := Random(ZNn);

    eqs := [];
    Cp := CalculateCN(p);
    t := Cputime();
    for i in [1..Ceiling(Cp * n)] do
      a, b := RandomDiseq(s, false);
      e := FromDiseqToEq(a, b);
      Append(~eqs, e);
    end for;
    
    for  i in [1..n] do
      field_eq := Zpnx ! (Zpnx.i^p - Zpnx.i);
      Append(~eqs, field_eq);
    end for;
    // Append(~eqs, field_eq);
    
    print "p = ", p, " | ", #eqs;
    sol := Variety(Ideal(eqs));
    // print "SOL:", Variety(Ideal(eqs));
    print "Time taken: ", Cputime(t), " seconds";
    // print "S:", s;
    print "=====";
  end for;

end if;

////////////
// TASK 3 //
////////////

if test_task3 then
  p := 5;
  Z := Integers(p^2);
  F := GF(p);

  // a
  for p in [3, 5, 7, 11] do
    F := GF(p);
    W := GenW(p);
    for i in F do
      for j in F do
        if (Integers() ! i + Integers() ! j ge p) then
          assert Evaluate(W, [i, j]) eq 1;
        else
          assert Evaluate(W, [i, j]) eq 0;
        end if;
      end for;
    end for;
  end for;

  // b
  c := Z ! 23;

  c0, c1 := DigitExtract(c);
  assert c0 eq 3;
  assert c1 eq 4;

  assert DigitMerge(c0, c1) eq c;

  // c
  for p in [3, 5, 7 , 11] do
    Fp := GF(p);
    W := GenW(p);

    a := Random(Fp);
    b := Random(Fp);

    j := 0;
    for i in [1..a-1] do
      j +:= Evaluate(W, [i*a, b]);
    end for;

    assert (Integers() ! a) * (Integers() ! b) eq (Integers() ! j) * (Integers() ! p) + Integers() ! a*b;
  end for;
  //
  for r in [1, 2, 3, 4, 5] do
    for p in [2, 3] do
      Fp := GF(p);
      ZN := Integers(p^2);
      ZNn := CartesianPower(ZN, 2);
      Zpnx := PolynomialRing(ZN, 2*n);

      s := Random(ZNn);

      eqs := [];
      t := Cputime();
      Cp := CalculateCN(p^2);
      for i in [1..Ceiling(2 * Cp * n * r)] do
        a, b := RandomDiseq(s, false);
        e, f1, f2, as := FromDiseqToEq2(a, b);
        Append(~eqs, e);
      end for;

      print "p^2 = ", p^2, " | # Eqs = ", #eqs, " | r = ", r;
      sols := Variety(Ideal(eqs));
      print s;
      print ExtractS(sols);
      print "Time taken: ", Cputime(t), " seconds";
      print "============";
    end for;
  end for;


  print "All tests of task 3 passed";
end if;

////////////
// TASK 4 //
////////////
if test_task4 then
  for n in [10..1000 by 100] do
    p := 3;
    Fp := GF(p);
    ZNn := CartesianPower(Fp, n);
    Zpnx := PolynomialRing(Fp, n);

    s := Random(ZNn);
    eqs := [];
    t := Cputime();
    Cp := CalculateCN(p);
    for i in [1..Ceiling(Cp * n)] do
      a, b := RandomDiseq(s, false);
      e := FromDiseqToEq(a, b);
      Append(~eqs, e);
    end for;
    print "dreg =", CalcDreg(eqs, n), " | n = ", n, " | m = ", Round(Cp*n);
  end for;
end if;

////////////
// TASK 5 //
////////////

if test_task5 then

  for p in [3, 5, 7] do
    ZN := GF(p);
    ZNn := CartesianPower(ZN, n);

    s := Random(ZNn);

    a, b := RandomDiseq(s, Random(0,1) eq 1);
    a_lin, b_lin := FromDiseqToLinEq(a, b);
    matrix := Matrix(ZN, 1, #a_lin, a_lin);
    b_matrix := [b_lin];
    repeat
      a, b := RandomDiseq(s, Random(0,1) eq 1);
      a_lin, b_lin := FromDiseqToLinEq(a, b);
      a_mat := Matrix(ZN, 1, #a_lin, a_lin);

      matrix := VerticalJoin(matrix, a_mat);
      Append(~b_matrix, b_lin);
    until Nrows(matrix) eq #a_lin;

    repeat
      a, b := RandomDiseq(s, Random(0,1) eq 1);
      a_lin, b_lin := FromDiseqToLinEq(a, b);
      a_mat := Matrix(ZN, 1, #a_lin, a_lin);

      matrix := VerticalJoin(matrix, a_mat);
      Append(~b_matrix, b_lin);
    until Rank(matrix) eq #a_lin;

    A := Matrix(ZN, matrix);
    B := Matrix(ZN, 1, #b_matrix, b_matrix);
    sol := Eltseq(Solution(Transpose(A), B));

    real_sol := [(p - 1) * elt : elt in sol[1..n]];

    print "Needed disequations ", Nrows(A), Ncols(A);
    print "Solution for p =", p;
    print real_sol;
    print s;
  end for;


  print "All tests of task 5 passed.";
end if;

////////////
// TASK 6 //
////////////

if test_task6 then
  N := 3;
  n := 10;

  s, A := KeyGen(N, n);
  C, M := Commit(s, A);

  c := 0;
  resp := Response(c, s, C);
  assert Verify(c, A, M, resp) eq true;

  c := 1;
  resp := Response(c, s, C);
  assert Verify(c, A, M, resp) eq true;

  print "All tests of task 6 passed.";
end if;

////////////
// TASK 7 //
////////////

if test_task7 then
  N := 3;
  n := 30;

  mess := "I will pay 10 EUR to Victor. Best wishes, Peggy";

  s, A := KeyGen(N, n);
  sig := DiseqSign(s, A, mess);
  assert VerifySign(sig, A, mess) eq true;

  print "All tests of task 7 passed.";
end if;

////////////
// TASK 9 //
////////////
if test_task9 then
  N := 3;
  n := 10;

  mess := "I will pay 10000 EUR to Eve. Best wishes, Peggy";

  s, A := KeyGen(N, n);
  sig := DiseqSignForge(A, mess);
  assert VerifySign(sig, A, mess) eq true;

  print "All tests of task 9 passed.";
end if;
