load "magma.m";
SetPrintLevel("Maximal");
SetQuitOnError(false);

////////////
// TASK 1 //
////////////

n := 100;
ZN := Integers(7);
ZNn := CartesianPower(ZN, 100);

s := Random(ZNn);
a, b := RandomDiseq(s, false);

assert b ne 0;
assert &+[a[i] * s[i] : i in [1..#s]] ne b;

a, b := RandomDiseq(s, true);

assert b eq 0;
assert &+[a[i] * s[i] : i in [1..#s]] ne 0;
