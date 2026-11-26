module
public section

namespace Demo

/-- Build both conjuncts directly. -/
theorem first (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply And.intro
  · exact hp
  · exact id hq

end Demo
