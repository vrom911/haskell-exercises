{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Exercises where

import Data.Kind (Constraint, Type)

-- | Before we get started, let's talk about the @TypeOperators@ extension. All
-- this does is allow us to write types whose names are operators, and write
-- regular names as infix names with the backticks, as we would at the value
-- level.


{- ONE -}

data Nat = Z | S Nat

-- | a. Use the @TypeOperators@ extension to rewrite the 'Add' family with the
-- name '+':
type family (+) (a :: Nat) (b :: Nat) :: Nat where
    Z + y = y
    -- x + Z = x This does not work
    (S x) + y = S (x + y)

-- | b. Write a type family '**' that multiplies two naturals using '(+)'. Which
-- extension are you being told to enable? Why?
type family (**) (a :: Nat) (b :: Nat) :: Nat where
    Z ** y = Z
    -- x ** Z = Z -- This doesn't work
    (S x) ** y = y + (x ** y)

data SNat (value :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | c. Write a function to add two 'SNat' values.
addSNat :: SNat n -> SNat m -> SNat (n + m)
addSNat SZ x     = x
addSNat (SS x) y = SS (addSNat x y)


{- TWO -}

data Vector (count :: Nat) (a :: Type) where
  VNil  :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | a. Write a function that appends two vectors together. What would the size
-- of the result be?
addVector :: Vector n a -> Vector m a -> Vector (n + m) a
addVector VNil y           = y
addVector (VCons a rest) x = VCons a (addVector rest x)

-- append :: Vector m a -> Vector n a -> Vector ??? a

-- | b. Write a 'flatMap' function that takes a @Vector n a@, and a function
-- @a -> Vector m b@, and produces a list that is the concatenation of these
-- results. This could end up being a deceptively big job.

flatMap :: Vector n a -> (a -> Vector m b) -> Vector (n ** m) b
flatMap VNil _           = VNil
flatMap (VCons a rest) f = f a `addVector` flatMap rest f


{- THREE -}

-- | a. More boolean fun! Write the type-level @&&@ function for booleans.
type family (&&) (a :: Bool) (b :: Bool) :: Bool where
    'True && 'True = 'True
    _ && _ = 'False

-- | b. Write the type-level @||@ function for booleans.
type family (||) (a :: Bool) (b :: Bool) :: Bool where
    'False || 'False = 'False
    _ || _ = 'True

-- | c. Write an 'All' function that returns @'True@ if all the values in a
-- type-level list of boleans are @'True@.
type family All (bools :: [Bool]) :: Bool where
    All '[] = 'True
    All ('False:xs) = 'False
    All ('True:xs) = All xs


{- FOUR -}

-- | a. Nat fun! Write a type-level 'compare' function using the promoted
-- 'Ordering' type.
type family Compare (a :: Nat) (b :: Nat) :: Ordering where
    Compare Z Z = 'EQ
    Compare Z _ = 'LT
    Compare _ Z = 'GT
    Compare (S x) (S y) = Compare x y

-- | b. Write a 'Max' family to get the maximum of two natural numbers.
type family If (a :: Bool) (true :: t) (false :: t) :: t where
    If 'True t _ = t
    If 'False _ f = f

type family (==) (a :: t) (b :: t) :: Bool where
    a == a = 'True
    _ == _ = 'False

type family Max (a :: Nat) (b :: Nat) :: Nat where
    Max a b = If (Compare a b == 'LT) a b

-- | c. Write a family to get the maximum natural in a list.
type family MaxList (l :: [Nat]) :: Nat where
    MaxList '[] = 'Z
    MaxList '[n] = n
    MaxList (x:xs) = Max x (MaxList xs)


{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.
type family Insert (a :: Nat) (tree :: Tree) :: Tree where
    Insert a 'Empty = 'Node Empty a Empty
    Insert a ('Node l x r) =
        If (Compare a x == 'GT)
        ('Node l x (Insert a r))
        ('Node (Insert a l) x r)


{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.
type family Merge (l :: Tree) (r :: Tree) :: Tree where
    Merge 'Empty r = r
    Merge l 'Empty = l
    Merge ('Node l1 x r1) ('Node l2 y r2) =
        If (Compare x y == 'GT)
        ('Node l2 y (Merge r2 ('Node l1 x r1)))
        ('Node (Merge l2 ('Node l1 x r1)) y r2)

type family Delete (a :: Nat) (tree :: Tree) :: Tree where
    Delete _ 'Empty = 'Empty
    Delete a ('Node l x r) =
        If (Compare a x == 'EQ)
        (Merge l r)
        ( If (Compare a x == 'LT)
          ('Node (Delete a l) x r)
          ('Node l x (Delete a r))
        )


{- SEVEN -}

-- | With @TypeOperators@, we can use regular Haskell list syntax on the
-- type-level, which I think is /much/ tidier than anything we could define.

data HList (xs :: [Type]) where
  HNil  :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

-- | Write a function that appends two 'HList's.
type family (++) (a :: HList xs) (b :: HList ys) :: HList zs where
    'HNil ++ y = y
    x ++ 'HNil = x
    ('HCons x rest) ++ y = HCons x (rest ++ y)


{- EIGHT -}

-- | Type families can also be used to build up constraints. There are, at this
-- point, a couple things that are worth mentioning about constraints:
--
-- - As we saw before, '()' is the empty constraint, which simply has "no
--   effect", and is trivially solved.
--
-- - Unlike tuples, constraints are "auto-flattened": ((a, b), (c, (d, ())) is
--   exactly equivalent to (a, b, c, d). Thanks to this property, we can build
--   up constraints using type families!

type family CAppend (x :: Constraint) (y :: Constraint) :: Constraint where
    CAppend x y = (x, y)

-- | a. Write a family that takes a constraint constructor, and a type-level
-- list of types, and builds a constraint on all the types.
type family Every (c :: Type -> Constraint) (x :: [Type]) :: Constraint where
    Every f '[] = ()
    Every f (x:xs) = CAppend (f x) (Every f xs)

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.
instance (Every Show xs) => Show (HList xs) where
    show HNil         = "[]"
    show (HCons a xs) = show a ++ " : " ++ show xs

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?
instance (Every Eq xs) => Eq (HList xs) where
    HNil == HNil = True
    (HCons a xs) == (HCons b ys) = a == b && xs == ys

instance (Every Ord xs, Every Eq xs) => Ord (HList xs) where
    compare HNil HNil = EQ
    compare (HCons a xs) (HCons b ys) = case compare a b of
        EQ -> compare xs ys
        o  -> o


{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.
type family UpTo (a :: Nat) :: Nat where
    UpTo 'Z = 'Z
    UpTo ('S x) = 'S (UpTo x)

-- | b. Write a type-level prime number sieve.
type family Sieve (a :: Nat) :: [Nat] where

-- | c. Why is this such hard work?
