import «AvlVerification»

namespace Primitives

namespace Result

def map {A B: Type} (x: Result A) (f: A -> B): Result B := match x with
| .ret y => .ret (f y)
| .fail e => .fail e
| .div => .div

end Result

end Primitives

namespace avl_verification

def Ordering.toLeanOrdering (o: avl_verification.Ordering): _root_.Ordering := match o with 
| .Less => .lt
| .Equal => .eq
| .Greater => .gt

end avl_verification

namespace Specifications

open Primitives
open Result

variable {T: Type}

class OrdSpec (U: Type) where
  cmp: U -> U -> Result Ordering
  infallible: ∀ a b, ∃ o, cmp a b = .ret o

instance: Coe (avl_verification.Ordering) (_root_.Ordering) where
  coe a := a.toLeanOrdering

def ordSpecOfInfaillible
  (H: avl_verification.Ord T)
  (Hresult: ∀ a b, ∃ o, H.cmp a b = Primitives.Result.ret o)
  : OrdSpec T where
  cmp x y := (H.cmp x y).map (fun z => z.toLeanOrdering)
  infallible := by
    intros a b
     -- TODO: transform the "raw" hypothesis into the "nice" hypothesis.
    sorry

instance [OrdSpec T]: Ord T where
  compare x y := match (OrdSpec.cmp x y) with 
  | .ret z => z
  | .fail _ => by sorry
  | .div => by sorry

end Specifications
