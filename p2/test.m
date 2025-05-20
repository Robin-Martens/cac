load "magma.m";
SetPrintLevel("Maximal");
SetQuitOnError(false);

n := 8;

test_task1 := false;
test_task2 := false;
test_task3 := true;
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
      // assert Evaluate(e, s) eq 0;
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
  for p in [2, 3] do
    Fp := GF(p);
    ZN := Integers(p^2);
    ZNn := CartesianPower(ZN, 2);
    Zpnx := PolynomialRing(ZN, 2*n);

    s := Random(ZNn);
    a, b := RandomDiseq(s, false);
    // s := <ZN ! 4, ZN ! 6>;
    // a := <ZN ! 8, ZN ! 5>; b := ZN ! 2;
    b1, b2 := DigitExtract(b);
    e, f1, f2, as := FromDiseqToEq2(a, b);

    // print "f0=", f1, " f1=", f2;
    // print "s = ", s, " | a = ", a, " | as = ", as, " | b = ", b;
    // print "a * s = ", (Integers() ! &+[Integers() ! a[i] * Integers() ! s[i] : i in [1..#s]]) mod p^2;
    // print "f0(s) ", EvaluateWithExtract(f1, s);
    // print "f1(s) ", EvaluateWithExtract(f2, s);
    // print "f(s) = ", EvaluateWithExtract(e, s);

    eqs := [];
    Cp := CalculateCN(p^2);
    for i in [1..Ceiling(2 * Cp * n * 3)] do
      a, b := RandomDiseq(s, false);
      e, f1, f2, as := FromDiseqToEq2(a, b);
      assert EvaluateWithExtract(e, s) eq 0;
      // if res ne 0 then
      //   print res, a, b, e;
      //   print "f0=", f1, " f1=", f2;
      //   print "s = ", s, " | a = ", a, " | as = ", as, " | b = ", b;
      //   print "a * s = ", (Integers() ! &+[Integers() ! a[i] * Integers() ! s[i] : i in [1..#s]]) mod p^2;
      //   print "f0(s) ", EvaluateWithExtract(f1, s);
      //   print "f1(s) ", EvaluateWithExtract(f2, s);
      //   print "f(s) = ", EvaluateWithExtract(e, s);
      //   break;
      // end if;
      Append(~eqs, e);
    end for;

    print "p = ", p, " | ", #eqs;
    sols := Variety(Ideal(eqs));
    print ExtractS(sols);
    print s;
  end for;



  print "All tests of task 3 passed";
end if;

////////////
// TASK 4 //
////////////
if test_task4 then
  
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
      // b_mat := Matrix(ZN, 1, 1, b_lin);

      matrix := VerticalJoin(matrix, a_mat);
      Append(~b_matrix, b_lin);
      // print Nrows(matrix);
    until Nrows(matrix) eq #a_lin;

    repeat
      a, b := RandomDiseq(s, Random(0,1) eq 1);
      a_lin, b_lin := FromDiseqToLinEq(a, b);
      a_mat := Matrix(ZN, 1, #a_lin, a_lin);
      // b_mat := Matrix(ZN, 1, 1, b_lin);

      matrix := VerticalJoin(matrix, a_mat);
      Append(~b_matrix, b_lin);
      // print Nrows(matrix);
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
