import «AvlVerification»

namespace Primitives

namespace Result

def map {A B: Type} (x: Result A) (f: A -> B): Result B := match x with
| .ok y => .ok (f y)
| .fail e => .fail e
| .div => .div

@[inline]
def isok {A: Type} : Result A -> Bool
| .ok _ => true
| .fail _ => false
| .div => false

@[inline]
def get? {A: Type}: (r: Result A) -> isok r -> A
| .ok x, _ => x

end Result

end Primitives

namespace avl_verification

def Ordering.toLeanOrdering (o: avl_verification.Ordering): _root_.Ordering := match o with 
| .Less => .lt
| .Equal => .eq
| .Greater => .gt

def Ordering.ofLeanOrdering (o: _root_.Ordering): avl_verification.Ordering := match o with
| .lt => .Less
| .eq => .Equal
| .gt => .Greater

end avl_verification

namespace Specifications

open Primitives
open Result

variable {T: Type} (H: outParam (avl_verification.Ord T))

-- TODO: reason about raw bundling vs. refined bundling.
-- raw bundling: hypothesis with Rust extracted objects.
-- refined bundling: lifted hypothesis with Lean native objects.
class OrdSpecInfaillible where
  infallible: ∀ a b, ∃ (o: avl_verification.Ordering), H.cmp a b = .ok o

class OrdSpecDuality extends OrdSpecInfaillible H where
  duality: ∀ a b, H.cmp a b = .ok .Greater -> H.cmp b a = .ok .Less

class OrdSpecRel (R: outParam (T -> T -> Prop)) extends OrdSpecInfaillible H where
  equivalence: ∀ a b, H.cmp a b = .ok .Equal -> R a b

class OrdSpecDualityRel (R: outParam (T -> T -> Prop)) extends OrdSpecDuality H, OrdSpecRel H R
class OrdSpecDualityEq extends OrdSpecDuality H, OrdSpecRel H Eq

instance: Coe (avl_verification.Ordering) (_root_.Ordering) where
  coe a := a.toLeanOrdering

def ordOfOrdSpec (H: avl_verification.Ord T) (spec: OrdSpecInfaillible H): Ord T where
  compare x y := (H.cmp x y).get? (by
    cases' (spec.infallible x y) with o Hcmp
    rewrite [isok, Hcmp]
    simp only
  )

instance [spec: OrdSpecInfaillible H]: Ord T := ordOfOrdSpec H spec
instance [OrdSpecInfaillible H]: LT T := ltOfOrd

theorem ltOfRustOrder {Spec: OrdSpecInfaillible H}: 
  haveI O := ordOfOrdSpec H Spec
  haveI := @ltOfOrd _ O
  ∀ a b, H.cmp a b = .ok .Less -> a < b := by
  intros a b
  intro Hcmp
  rw [LT.lt]
  simp [ltOfOrd]
  rw [compare]
  simp [ordOfOrdSpec]
  -- https://proofassistants.stackexchange.com/questions/1062/what-does-the-motive-is-not-type-correct-error-mean-in-lean
  simp_rw [Hcmp, get?, avl_verification.Ordering.toLeanOrdering]
  rfl

theorem gtOfRustOrder {Spec: OrdSpecDuality H}: 
  haveI O := ordOfOrdSpec H Spec.toOrdSpecInfaillible
  haveI := @ltOfOrd _ O
  ∀ a b, H.cmp a b = .ok .Greater -> b < a := by
  intros a b
  intro Hcmp
  apply ltOfRustOrder
  exact (Spec.duality _ _ Hcmp)


end Specifications
