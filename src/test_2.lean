structure point (α : Type*) :=
(x : α ) (y : α) (z : α)

structure rgb_val :=
(red : nat) (green : nat) (blue : nat)

structure red_green_point extends point nat :=
{x : nat := 2, no_blue : nat := 0}

def p   : point nat := {x := 10, y := 10, z := 20}
def rgp : red_green_point nat :=
{x := 1, y := 2, no_blue := 2, z := 2}
-- {red := 200, green := 40, blue := 0, no_blue := rfl, ..p}

-- example : rgp.x   = 10 := rfl
-- example : rgp.red = 200 := rfl

#eval rgp.x