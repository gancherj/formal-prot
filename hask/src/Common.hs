module Common where

import Data.Type.Equality
type PID = String

data P a b = P a b
type (+) a b = P a b
  
data Exp (a :: k) where
  EInt :: Int -> Exp Int
  EInl :: Exp a -> Exp (a + b)
  EInr :: Exp b -> Exp (a + b)
  EBool :: Bool -> Exp Bool
  EUnit :: Exp ()
  ENil :: Exp '[]
  ECons :: Exp a -> Exp xs -> Exp (a ': xs)

data SomeExp = forall a. SomeExp (Exp a)

instance TestEquality Exp where
  testEquality (EInt _) (EInt _) = Just Refl
  testEquality (EBool _) (EBool _) = Just Refl
  testEquality EUnit EUnit = Just Refl
  testEquality ENil ENil = Just Refl
  testEquality (ECons x xs) (ECons y ys) =
    case (testEquality x y, testEquality xs ys) of
      (Just Refl, Just Refl) -> Just Refl
      _ -> Nothing
  testEquality _ _ = Nothing
