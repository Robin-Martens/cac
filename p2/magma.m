////////////
// TASK 1 //
////////////

function RandomDiseq(s, homog)
  ZN := Parent(s[1]);
  ZNn := CartesianPower(ZN, #s);

  if homog then
    b := 0;
  else
    b := Random(ZN);
  end if;

  repeat
    a := Random(ZNn);
  until &+[a[i] * s[i] : i in [1..#s]] ne b;

  return a, b;
end function;
