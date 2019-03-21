universes u v

-- setOption pp.binderTypes False
setOption pp.implicit True
setOption Trace.Compiler.llnf True
setOption Trace.Compiler.boxed True

namespace x1

def f (x : Bool) (y z : Nat) : Nat :=
match x with
| tt := y
| ff := z + y + y

end x1


namespace x2

def f (x : Nat) : Nat := x

end x2


namespace x3

def f (x y : Nat) : Nat := x

end x3

namespace x4
@[noinline] def h (x y : Nat) : Nat := x + y

def f1 (x y : Nat) : Nat :=
h x y

def f2 (x y : Nat) : Nat :=
h (h x y) (h y x)

def f3 (x y : Nat) : Nat :=
h (h x x) x

def f4 (x y : Nat) : Nat :=
h (h 1 0) x

def f5 (x y : Nat) : Nat :=
h (h 1 1) x

end x4

namespace x5

def myMap {α : Type u} {β : Type v} (f : α → β) : List α → List β
| []      := []
| (x::xs) := f x :: myMap xs

end x5

namespace x6

@[noinline] def act : State Nat Unit :=
modify (+1)

def f : State Nat Unit :=
act *> act

end x6

namespace x7

inductive S
| v1 | v2 | v3

def foo : S → S × S
| S.v1 := (S.v2, S.v1)
| S.v2 := (S.v3, S.v2)
| S.v3 := (S.v1, S.v2)

end x7

namespace x8

def f (x : Nat) : List Nat :=
x :: x :: []

end x8
