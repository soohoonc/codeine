/- Can languages stop innovating on what syntax to use for their fucking comments -/
-- wait, this ain't so bad
/- Hello, world! -/
def main : IO Unit := IO.println "Hello, world!"

#eval if 3 == 4 then "equal" else "not equal"
#eval if 3 == 3 then 5 else 6

#eval (1 + 2: Nat)
#eval 1 - 2
#eval (1 - 2: Int)
#check (1 - 2)

def hello := "Hello"
#check hello
#check main

def succ (n : Nat) : Nat := n + 1


def joinStringWith (a: String) (b: String) (j: String): String :=
  a ++ j ++ b

#eval joinStringWith "Hello" "world!" ", "

#check joinStringWith "a"

/- woah types -/
def Str: Type := String

def NatNumber : Type := Nat
/- Bad -/
-- def thirtyEight : NatNumber = 38 /- Lean alows number literals to be overloaded, so literals can be used to create new types. lean does not replace all defined names with theire definitions before looking for overloading-/
-- def thirtyEight : Type := 38
/- Good -/
def thirtyEight : NatNumber := (38: Nat)
