import Lean

/- A certificate is observed with fixed endpoints and a fixed environment of
   labelled atomic steps. Reflection has no independent occurrence identity. -/
namespace EqualityCleanup

inductive Cert where
  | atom (id : Nat)
  | refl
  | sym (p : Cert)
  | seq (p q : Cert)
  deriving DecidableEq, Repr
open Cert

inductive HasEnds (ends : Nat → Nat × Nat) : Cert → Nat → Nat → Prop where
  | atom (i) : HasEnds ends (.atom i) (ends i).1 (ends i).2
  | refl (a) : HasEnds ends .refl a a
  | sym : HasEnds ends p a b → HasEnds ends (.sym p) b a
  | seq : HasEnds ends p a b → HasEnds ends q b c → HasEnds ends (.seq p q) a c

inductive Step : Cert → Cert → Prop where
  | leftUnit (p) : Step (seq refl p) p
  | rightUnit (p) : Step (seq p refl) p
  | doubleSym (p) : Step (sym (sym p)) p
  | symRefl : Step (sym refl) refl
  | underSym : Step p p' → Step (sym p) (sym p')
  | underLeft : Step p p' → Step (seq p q) (seq p' q)
  | underRight : Step q q' → Step (seq p q) (seq p q')

theorem Step.preservesEnds (s : Step p q) (h : HasEnds ends p a b) : HasEnds ends q a b := by
  induction s generalizing a b with
  | leftUnit => cases h with | seq l r => cases l; exact r
  | rightUnit => cases h with | seq l r => cases r; exact l
  | doubleSym => cases h with | sym h => cases h with | sym h => exact h
  | symRefl => cases h with | sym h => cases h; exact .refl _
  | underSym _ ih => cases h with | sym h => exact .sym (ih h)
  | underLeft _ ih => cases h with | seq l r => exact .seq (ih l) r
  | underRight _ ih => cases h with | seq l r => exact .seq l (ih r)

def volume : Cert → Nat
  | refl | atom _ => 1
  | sym p => volume p + 1
  | seq p q => volume p + volume q + 1

theorem Step.decreases (s : Step p q) : volume q < volume p := by
  induction s <;> simp_all [volume] <;> omega

def reverseNormal : Cert → Cert
  | refl => refl
  | sym p => p
  | p => sym p

def composeNormal : Cert → Cert → Cert
  | refl, q => q
  | p, refl => p
  | p, q => seq p q

@[simp] theorem compose_right (p : Cert) : composeNormal p refl = p := by cases p <;> rfl

def normal : Cert → Cert
  | atom i => atom i
  | refl => refl
  | sym p => reverseNormal (normal p)
  | seq p q => composeNormal (normal p) (normal q)

inductive Normal : Cert → Prop where
  | refl : Normal refl
  | atom (i) : Normal (atom i)
  | symAtom (i) : Normal (sym (atom i))
  | symSeq : Normal (seq p q) → Normal (sym (seq p q))
  | seq : Normal p → Normal q → p ≠ refl → q ≠ refl → Normal (seq p q)

theorem reverse_normal (h : Normal p) : Normal (reverseNormal p) := by
  cases h with
  | refl => exact .refl
  | atom i => exact .symAtom i
  | symAtom i => exact .atom i
  | symSeq h => exact h
  | seq hp hq hl hr => exact .symSeq (.seq hp hq hl hr)

theorem compose_normal (hp : Normal p) (hq : Normal q) : Normal (composeNormal p q) := by
  by_cases hl : p = refl
  · subst p; exact hq
  by_cases hr : q = refl
  · subst q; simpa using hp
  have he : composeNormal p q = seq p q := by cases p <;> cases q <;> simp_all [composeNormal]
  exact he ▸ Normal.seq hp hq hl hr

theorem normal_is_normal (p : Cert) : Normal (normal p) := by
  induction p with
  | atom i => exact .atom i
  | refl => exact .refl
  | sym _ ih => exact reverse_normal ih
  | seq _ _ hp hq => exact compose_normal hp hq

theorem reverse_involution (h : Normal p) : reverseNormal (reverseNormal p) = p := by
  cases h <;> rfl

theorem Step.sameNormal (s : Step p q) : normal p = normal q := by
  induction s <;> simp_all [normal, reverse_involution (normal_is_normal _)] <;> rfl

inductive Steps : Cert → Cert → Prop where
  | refl (p) : Steps p p
  | cons : Step p q → Steps q r → Steps p r

theorem Steps.append (s : Steps p q) (t : Steps q r) : Steps p r := by
  induction s with
  | refl => exact t
  | cons h _ ih => exact .cons h (ih t)

theorem Steps.mapContext (f : Cert → Cert) (liftStep : ∀ {a b}, Step a b → Step (f a) (f b))
    (s : Steps p q) : Steps (f p) (f q) := by
  induction s with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (liftStep h) ih

theorem reverse_reached (p : Cert) : Steps (sym p) (reverseNormal p) := by
  cases p with
  | refl => exact .cons .symRefl (.refl _)
  | sym p => exact .cons (.doubleSym p) (.refl _)
  | atom _ | seq _ _ => exact .refl _

theorem compose_reached (p q : Cert) : Steps (seq p q) (composeNormal p q) := by
  cases p <;> cases q <;> first
    | exact .cons (.leftUnit _) (.refl _)
    | exact .cons (.rightUnit _) (.refl _)
    | exact .refl _

theorem reaches_normal (p : Cert) : Steps p (normal p) := by
  induction p with
  | refl | atom _ => exact .refl _
  | sym p ih => exact (ih.mapContext sym Step.underSym).append (reverse_reached _)
  | seq p q hl hr =>
    exact (hl.mapContext (seq · q) Step.underLeft).append
      ((hr.mapContext (seq (normal p)) Step.underRight).append (compose_reached _ _))

theorem Steps.sameNormal (s : Steps p q) : normal p = normal q := by
  induction s with
  | refl => rfl
  | cons h _ ih => exact h.sameNormal.trans ih

theorem idempotent (p : Cert) : normal (normal p) = normal p :=
  (reaches_normal p).sameNormal.symm

theorem confluent (s : Steps p q) (t : Steps p r) : ∃ u, Steps q u ∧ Steps r u :=
  ⟨normal p, s.sameNormal ▸ reaches_normal q, t.sameNormal ▸ reaches_normal r⟩

def Irreducible (p : Cert) : Prop := ∀ q, ¬ Step p q

theorem normal_irreducible (h : Normal p) : Irreducible p := by
  induction h with
  | refl | atom _ => intro q s; cases s
  | symAtom i => intro q s; cases s with | underSym h => cases h
  | symSeq h ih => intro q s; cases s with | underSym h => exact ih _ h
  | seq hp hq hl hr il ir =>
    intro q s
    cases s with
    | leftUnit => exact hl rfl
    | rightUnit => exact hr rfl
    | underLeft s => exact il _ s
    | underRight s => exact ir _ s

theorem unique_terminal (s : Steps p q) (h : Irreducible q) : q = normal p := by
  have hq : ∀ r, Steps q r → q = r := by
    intro r t
    cases t with
    | refl => rfl
    | cons first _ => exact False.elim (h _ first)
  exact (hq _ (reaches_normal q)).trans s.sameNormal.symm

-- Fix the endpoints as part of a certificate's interface. Every intermediate
-- term on a directed path keeps them, including the computed normal form.
theorem Steps.preservesEnds (s : Steps p q) (h : HasEnds ends p a b) : HasEnds ends q a b := by
  induction s with
  | refl => exact h
  | cons first _ ih => exact ih (first.preservesEnds h)

-- Atomic reason labels survive in syntax order, even when an atom is a self-loop.
def atoms : Cert → List Nat
  | refl => []
  | atom i => [i]
  | sym p => atoms p
  | seq p q => atoms p ++ atoms q

theorem Step.preservesAtoms (s : Step p q) : atoms p = atoms q := by
  induction s <;> simp_all [atoms]

-- The symmetric closure measures the whole equivalence class, including paths
-- which expand first. Joining at the normal form decides this relation.
inductive Equivalent : Cert → Cert → Prop where
  | refl (p) : Equivalent p p
  | step : Step p q → Equivalent p q
  | symm : Equivalent p q → Equivalent q p
  | trans : Equivalent p q → Equivalent q r → Equivalent p r

theorem Steps.equivalent (s : Steps p q) : Equivalent p q := by
  induction s with
  | refl => exact .refl _
  | cons first _ ih => exact .trans (.step first) ih

theorem equivalent_iff : Equivalent p q ↔ normal p = normal q := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | step h => exact h.sameNormal
    | symm _ ih => exact ih.symm
    | trans _ _ ih ij => exact ih.trans ij
  · intro eq
    have a := (reaches_normal p).equivalent
    exact .trans (eq ▸ a) (.symm (reaches_normal q).equivalent)

theorem Steps.volume_le (s : Steps p q) : volume q ≤ volume p := by
  induction s with
  | refl => exact Nat.le_refl _
  | cons h _ ih => exact Nat.le_trans ih (Nat.le_of_lt h.decreases)

theorem class_minimum (h : Equivalent p q) : volume (normal p) ≤ volume q :=
  (equivalent_iff.mp h) ▸ (reaches_normal q).volume_le

end EqualityCleanup

/- A separate counterexample for a proposed high-level extension. All atoms
   can be loops at one point and F an endomorphism fixing that point. -/
namespace MappedChains

inductive Chain where
  | atom (id : Nat)
  | map (p : Chain)
  | seq (p q : Chain)
  deriving DecidableEq
open Chain

-- One fixed map F. Enumerate BOTH root rules and every one-hole context.
def rootMoves : Chain → List Chain
  | seq (seq p q) r => [seq p (seq q r)]
  | seq (map p) (map q) => [map (seq p q)]
  | _ => []

def moves (t : Chain) : List Chain := rootMoves t ++
  match t with
  | atom _ => []
  | map p => (moves p).map map
  | seq p q => (moves p).map (seq · q) ++ (moves q).map (seq p)

def source := seq (seq (map (atom 0)) (map (atom 1))) (atom 2)
def merged := seq (map (seq (atom 0) (atom 1))) (atom 2)
def reassociated := seq (map (atom 0)) (seq (map (atom 1)) (atom 2))

theorem two_distinct_terminal_results :
    merged ∈ moves source ∧ reassociated ∈ moves source ∧
    moves merged = [] ∧ moves reassociated = [] ∧ merged ≠ reassociated := by decide

end MappedChains
