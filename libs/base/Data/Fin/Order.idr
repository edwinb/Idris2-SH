||| Implementation  of ordering relations for `Fin`ite numbers
module Data.Fin.Order

import Control.Relation
import Control.Order
import Data.Fin
import Data.Fun
import Data.Rel
import Data.Nat
import Data.Nat.Order
import Decidable.Decidable

%default total

using (k : Nat)

  public export
  data FinLTE : Fin k -> Fin k -> Type where
    FromNatPrf : {m, n : Fin k} -> LTE (finToNat m) (finToNat n) -> FinLTE m n

  public export
  Transitive (Fin k) FinLTE where
    transitive (FromNatPrf xy) (FromNatPrf yz) =
      FromNatPrf $ transitive {rel = LTE} xy yz

  public export
  Reflexive (Fin k) FinLTE where
    reflexive = FromNatPrf $ reflexive {rel = LTE}

  public export
  Preorder (Fin k) FinLTE where

  public export
  Antisymmetric (Fin k) FinLTE where
    antisymmetric {x} {y} (FromNatPrf xy) (FromNatPrf yx) =
      finToNatInjective x y $
        antisymmetric {rel = LTE} xy yx

  public export
  PartialOrder (Fin k) FinLTE where

  public export
  Connex (Fin k) FinLTE where
    connex {x = FZ} _ =  Left $ FromNatPrf LTEZero
    connex {y = FZ} _ = Right $ FromNatPrf LTEZero
    connex {x = FS k} {y = FS j} prf =
      case connex {rel = FinLTE} $ prf . (cong FS) of
        Left  (FromNatPrf p) => Left  $ FromNatPrf $ LTESucc p
        Right (FromNatPrf p) => Right $ FromNatPrf $ LTESucc p

  public export
  Decidable 2 [Fin k, Fin k] FinLTE where
    decide m n with (decideLTE (finToNat m) (finToNat n))
      decide m n | Yes prf    = Yes (FromNatPrf prf)
      decide m n | No  disprf = No (\ (FromNatPrf prf) => disprf prf)
