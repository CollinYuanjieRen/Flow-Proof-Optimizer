module
public section

namespace Demo

/-- Introduce a local name in the first branch. -/
theorem second (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  apply And.intro
  · have keep := hp
    exact keep
  · exact id hq

end Demo
