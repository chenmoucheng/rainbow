/*
 * The Rainbow signature scheme
 */

// Parameters
Fq := ExtensionField<F,X | X^2 + X + F.1> where F is ExtensionField<GF(2),X | X^2 + X + 1>;
v := [32];
o := [32,32];

u := #o;
v cat:= [v[1] + &+o[1..i] : i in [1..u]];
V := [[     1..v[i]]   : i in [1..u]];
O := [[v[i]+1..v[i+1]] : i in [1..u]];
n := v[#v];
m := n - v[1];

// Utilities
I := func<L,... | &+[L[i]*n^(#L - i) : i in [1..#L]]>;

// Whether to generate a random key pair
genkey := #Fq ne 16;
System("gcc swap.c ; cat pub.key | ./a.out > pub2.key ; cat sec.key | ./a.out > sec2.key");
PK := Open("pub2.key","r");
SK := Open("sec2.key","r");
readkey := func<F | f(StringToInteger(Getc(F),16))> where f is func<i | Fq!i + Fq!(i div 2)*Fq.1^5 + Fq!(i div 4)*Fq.1 + Fq!(i div 8)*Fq.1^6>;

Fn := VectorSpace(Fq,n);
if genkey then
  repeat
    _M := RandomMatrix(Fq,n,n);
  until IsInvertible(_M);
  _z := Random(Fn);
else
  _M := Matrix(Fq,n,n,[readkey(SK) : i in [1..n^2]]);
  _z := Fn![readkey(SK) : i in [1..n]];
end if;
T := map<Fn -> Fn | x :-> f(x) + _z, y :-> g(y - _z)>
  where f is Hom(Fn,Fn)!_M^-1
  where g is Hom(Fn,Fn)!_M;
T_ := Inverse(T);

Fm := VectorSpace(Fq,m);
if genkey then
  repeat
    _M := RandomMatrix(Fq,m,m);
  until IsInvertible(_M);
  _z := Random(Fm);
else
  _M := Matrix(Fq,m,m,[readkey(SK) : i in [1..m^2]]);
  _z := Fm![readkey(SK) : i in [1..m]];
end if;
S := map<Fm -> Fm | x :-> f(x) + _z, y :-> g(y - _z)>
  where f is Hom(Fm,Fm)!_M^-1
  where g is Hom(Fm,Fm)!_M;
S_ := Inverse(S);

_<[x]> := PolynomialRing(Fq,n);
A := [Fq|];
B := [Fq|];
r := [Fq|];
d := [Fq|];
for l in [1..u] do
  for k in O[l] do
    for j in O[l] do
      r[I(j,k)] := genkey select Random(Fq) else readkey(SK);
    end for;
  end for;
  for k in O[l] do
    for i in V[l] do
      for j in O[l] do
        B[I(i,j,k)] := genkey select Random(Fq) else readkey(SK);
      end for;
    end for;
  end for;
  for j in V[l] do
    for k in O[l] do
      r[I(j,k)] := genkey select Random(Fq) else readkey(SK);
    end for;
  end for;
  for j in V[l] do
    for i in V[l] do
      if i le j then
        for k in O[l] do
          A[I(i,j,k)] := genkey select Random(Fq) else readkey(SK);
        end for;
      end if;
    end for;
  end for;
  for k in O[l] do
    d[I(k)] := genkey select Random(Fq) else readkey(SK);
  end for;
end for;
f := [&+[A[I(i,j,k)]*x[i]*x[j] : i in V[l], j in V[l] | i le j] + &+[B[I(i,j,k)]*x[i]*x[j] : i in V[l], j in O[l]] + &+[r[I(j,k)]*x[j] : j in V[l] cat O[l]] + d[I(k)]
  where l is Index([k in O[i] : i in [1..u]],true) : k in [v[1]+1..n]];
F := map<Fn -> Fm | x :-> Evaluate(f,ElementToSequence(x)), x :-> InvF(x)>
  where InvF is function(x)
    repeat
      y := [Random(Fq) : i in [1..v[1]]];
      for l in [1..u] do
        vs := VarietySequence(Ideal([phi(f[i - v[1]] - x[i - v[1]]) : i in O[l]]))
          where phi is hom<Parent(f[1]) -> R | y cat [R.i : i in [1..o[l]]] cat [0 : i in &cat(O[l+1..u])]>
          where R is PolynomialRing(Fq,o[l]);
        if IsEmpty(vs) then break; end if;
        y cat:= vs[1];
      end for;
    until #y eq n;
    // For embedded systems
    yy := y[1..v[1]];
    for l in [1..u] do
      xx := VectorSpace(Fq,o[l])![x[i - v[1]] : i in O[l]];
      _M :=  ZeroMatrix(Fq,o[l],o[l]);
      vv :=      Matrix(Fq,v[l],1,yy[V[l]]);
      for k in O[l] do
        AA := ZeroMatrix(Fq,v[l],v[l]);
        BB := ZeroMatrix(Fq,v[l],o[l]);
        rv := ZeroMatrix(Fq,   1,v[l]);
        ro := ZeroMatrix(Fq,   1,o[l]);
        for i in V[l] do
          for j in V[l] do
            if i le j then
              AA[i,j] := A[I(i,j,k)];
            end if;
          end for;
          for j in O[l] do
            BB[i,j - v[l]] := B[I(i,j,k)];
          end for;
          rv[1,i] := r[I(i,k)];
        end for;
        for i in O[l] do
          ro[1,i - v[l]] := r[I(i,k)];
        end for;
        xx[k - v[l]] -:= (Transpose(vv)*AA*vv)[1,1] + (rv*vv)[1,1] + d[I(k)];
        _M[k - v[l]]  := Vector(Transpose(vv)*BB + ro);
      end for;
      yy cat:= ElementToSequence(xx*Transpose(_M^-1));
    end for;
    assert yy eq y;
    return yy;
  end function;
F_ := Inverse(F);

if genkey then
  P := T*F*S;
else
  A := [Fq|];
  r := [Fq|];
  d := [Fq|];
  for j in [1..n] do
    for k in [v[1]+1..n] do
      r[I(j,k)] := readkey(PK);
    end for;
  end for;
  for j in [1..n] do
    for i in [1..n] do
      if i le j then
        for k in [v[1]+1..n] do
          A[I(i,j,k)] := readkey(PK);
        end for;
      end if;
    end for;
  end for;
  for k in [v[1]+1..n] do
    d[I(k)] := readkey(PK);
  end for;
  p := [&+[A[I(i,j,k)]*x[i]*x[j] : i in [1..n], j in [1..n] | i le j] + &+[r[I(j,k)]*x[j] : j in [1..n]] + d[I(k)] : k in [v[1]+1..n]];
  P := map<Fn -> Fm | x :-> Evaluate(p,ElementToSequence(x))>;
end if;

h := Random(Fm);
z := T_(F_(S_(h)));
assert P(z) eq h;

