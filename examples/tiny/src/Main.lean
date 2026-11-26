module
public import Demo.Left
public import Demo.Right
public section

namespace Demo

theorem result (p q : Prop) (hp : p) (hq : q) : (p ∧ q) ∧ (p ∧ q) :=
  ⟨first p q hp hq, second p q hp hq⟩

end Demo
