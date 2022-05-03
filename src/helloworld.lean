import system.io
open tactic.unsafe

meta def function_f : tactic unit := do
  tactic.trace "f"

meta def function_g : tactic unit := do
  tactic.trace "g"

meta def function_h : tactic unit → tactic unit → tactic unit
| x y := do tactic.trace "h", y, x

meta def hello_math_2 : tactic unit := do
  function_h function_f function_g,
  tactic.trace "Hello Math!"

section examples

example (α : Type) (a : nat): a=a := begin
  hello_math_2,
  refl
end

end examples

#eval "math" ++ "prover"

meta def show_proof_string : string → string
| "x" := "Mathx!"
| s := "Don't know!"

meta def show_proof_int : int → int
| 0 := 1
| num := 100

class has_proof (α : Type) : Type :=
(proof : α → α)

meta instance : has_proof string := 
⟨show_proof_string⟩

meta instance : has_proof int := 
⟨show_proof_int⟩

#check has_proof int





meta def hello_math : tactic unit := do
  let x := 1,
  tactic.trace "Hello Math!"

meta def solve : tactic unit := do
  let x := 2,
  tactic.trace format! "x: {x}"

section examples

example (α : Type) (a : nat): a=a := begin
  solve,
  refl
end

end examples

#eval list.foldr (+) 0 [1,2,3]

meta def Number : Type := nat
meta def x : Number := nat.zero

#check x


