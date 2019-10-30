{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE Rank2Types           #-}

module Exercises where


import Data.Type.Bool (type (&&))

----------------------------------------------------------------------------
-- ONE
----------------------------------------------------------------------------

-- | Let's introduce a new class, 'Countable', and some instances to match.
class Countable a where count :: a -> Int
instance Countable Int  where count   = id
instance Countable [a]  where count   = length
instance Countable Bool where count x = if x then 1 else 0

-- | a. Build a GADT, 'CountableList', that can hold a list of 'Countable'
-- things.

data CountableList where
    CountableNil  :: CountableList
    CountableCons :: (Show a, Countable a) => a -> CountableList -> CountableList

deriving instance Show CountableList

{- | b. Write a function that takes the sum of all members of a 'CountableList'
once they have been 'count'ed.

>>> countList (CountableCons True (CountableCons "asd" (CountableCons (11::Int) CountableNil)))
15

-}
countList :: CountableList -> Int
countList CountableNil = 0
countList (CountableCons a rest) = count a + countList rest


{- | c. Write a function that removes all elements whose count is 0.

>>> dropZero (CountableCons True (CountableCons "asd" (CountableCons (11::Int) CountableNil)))
CountableCons True (CountableCons "asd" (CountableCons 11 CountableNil))
>>> dropZero (CountableCons True (CountableCons "asd" (CountableCons (0::Int) CountableNil)))
CountableCons True (CountableCons "asd" CountableNil)
-}
dropZero :: CountableList -> CountableList
dropZero CountableNil = CountableNil
dropZero (CountableCons a rest) =
    if count a == 0
    then dropZero rest
    else CountableCons a $ dropZero rest


{- | d. Can we write a function that removes all the things in the list of type
'Int'? If not, why not?

No, I can't get the existential type out of there.
-}
filterInts :: CountableList -> CountableList
filterInts = error "Contemplate me!"


----------------------------------------------------------------------------
-- TWO
----------------------------------------------------------------------------

-- | a. Write a list that can take /any/ type, without any constraints.
data AnyList where
    AnyNil :: AnyList
    AnyCons :: a -> AnyList -> AnyList

-- | b. How many of the following functions can we implement for an 'AnyList'?
reverseAnyList :: AnyList -> AnyList
reverseAnyList = go AnyNil
  where
    go :: AnyList -> AnyList -> AnyList
    go acc AnyNil = acc
    go acc (AnyCons x rest) = go (AnyCons x acc) rest

filterAnyList :: (a -> Bool) -> AnyList -> AnyList
filterAnyList = undefined

lengthAnyList :: AnyList -> Int
lengthAnyList = go 0
  where
    go :: Int -> AnyList -> Int
    go !n AnyNil = n
    go n (AnyCons _ rest) = go (n + 1) rest

foldAnyList :: Monoid m => AnyList -> m
foldAnyList = undefined

isEmptyAnyList :: AnyList -> Bool
isEmptyAnyList AnyNil = True
isEmptyAnyList _ = False

instance Show AnyList where
    show AnyNil = "[]"
    show (AnyCons _ rest) = "elem : " ++ show rest

----------------------------------------------------------------------------
-- THREE
----------------------------------------------------------------------------

-- | Consider the following GADT:

data TransformableTo output where
  TransformWith
    :: (input -> output)
    ->  input
    -> TransformableTo output

-- | ... and the following values of this GADT:

transformable1 :: TransformableTo String
transformable1 = TransformWith show 2.5

transformable2 :: TransformableTo String
transformable2 = TransformWith (uncurry (++)) ("Hello,", " world!")

-- | a. Which type variable is existential inside 'TransformableTo'? What is
-- the only thing we can do to it?

-- | b. Could we write an 'Eq' instance for 'TransformableTo'? What would we be
-- able to check?

instance Eq output => Eq ( TransformableTo output) where
    (TransformWith f1 i1) == (TransformWith f2 i2) = f1 i1 == f2 i2

-- | c. Could we write a 'Functor' instance for 'TransformableTo'? If so, write
-- it. If not, why not?

instance Functor TransformableTo where
    fmap :: (output1 -> output2) -> TransformableTo output1 -> TransformableTo output2
    fmap f (TransformWith t input) = TransformWith (f . t) input

----------------------------------------------------------------------------
-- FOUR
----------------------------------------------------------------------------

-- | Here's another GADT:

data EqPair where
  EqPair :: Eq a => a -> a -> EqPair

-- | a. There's one (maybe two) useful function to write for 'EqPair'; what is
-- it?

isEqual :: EqPair -> Bool
isEqual (EqPair a b) = a == b

-- | b. How could we change the type so that @a@ is not existential? (Don't
-- overthink it!)

data EqPair1 a where
  EqPair1 :: Eq a => a -> a -> EqPair1 a

-- | c. If we made the change that was suggested in (b), would we still need a
-- GADT? Or could we now represent our type as an ADT?
-- Need for Eq constraint.


----------------------------------------------------------------------------
-- FIVE
----------------------------------------------------------------------------

-- | Perhaps a slightly less intuitive feature of GADTs is that we can set our
-- type parameters (in this case @a@) to different types depending on the
-- constructor.

data MysteryBox a where
  EmptyBox  ::                                MysteryBox ()
  IntBox    :: Int    -> MysteryBox ()     -> MysteryBox Int
  StringBox :: String -> MysteryBox Int    -> MysteryBox String
  BoolBox   :: Bool   -> MysteryBox String -> MysteryBox Bool

-- | When we pattern-match, the type-checker is clever enough to
-- restrict the branches we have to check to the ones that could produce
-- something of the given type.

getInt :: MysteryBox Int -> Int
getInt (IntBox int _) = int

-- | a. Implement the following function by returning a value directly from a
-- pattern-match:

getInt' :: MysteryBox String -> Int
getInt' (StringBox _ (IntBox int _)) = int

-- | b. Write the following function. Again, don't overthink it!

countLayers :: MysteryBox a -> Int
countLayers EmptyBox = 0
countLayers (IntBox _ _) = 1
countLayers (StringBox _ _) = 2
countLayers (BoolBox _ _) = 3

-- | c. Try to implement a function that removes one layer of "Box". For
-- example, this should turn a BoolBox into a StringBox, and so on. What gets
-- in our way? What would its type be?
{-
downgradeLayer :: forall a b . MysteryBox a -> MysteryBox b
downgradeLayer EmptyBox = EmptyBox
downgradeLayer (IntBox _ l) = l
downgradeLayer (StringBox _ l) = l
downgradeLayer (BoolBox _ l) = l
-}


----------------------------------------------------------------------------
-- SIX
----------------------------------------------------------------------------

-- | We can even use our type parameters to keep track of the types inside an
-- 'HList'!  For example, this heterogeneous list contains no existentials:

data HList a where
  HNil  :: HList ()
  HCons :: head -> HList tail -> HList (head, tail)

exampleHList :: HList (String, (Int, (Bool, ())))
exampleHList = HCons "Tom" (HCons 25 (HCons True HNil))

-- | a. Write a 'head' function for this 'HList' type. This head function
-- should be /safe/: you can use the type signature to tell GHC that you won't
-- need to pattern-match on HNil, and therefore the return type shouldn't be
-- wrapped in a 'Maybe'!
headHList :: HList (a, b) -> a
headHList (HCons a _) = a

-- | b. Currently, the tuples are nested. Can you pattern-match on something of
-- type @HList (Int, String, Bool, ())@? Which constructor would work?

patternMatchMe :: HList (Int, String, Bool, ()) -> Int
patternMatchMe = undefined

-- | c. Can you write a function that appends one 'HList' to the end of
-- another? What problems do you run into?

----------------------------------------------------------------------------
-- SEVEN
----------------------------------------------------------------------------

-- | Here are two data types that may help:

data Empty
data Branch left centre right

-- | a. Using these, and the outline for 'HList' above, build a heterogeneous
-- /tree/. None of the variables should be existential.

data HTree a where
    HEmpty  :: HTree Empty
    HBranch :: HTree l -> a -> HTree r -> HTree (Branch l a r)

-- | b. Implement a function that deletes the left subtree. The type should be
-- strong enough that GHC will do most of the work for you. Once you have it,
-- try breaking the implementation - does it type-check? If not, why not?
deleteLeft :: HTree (Branch l a r) -> HTree (Branch Empty a r)
deleteLeft (HBranch _ a r) = HBranch HEmpty a r

-- | c. Implement 'Eq' for 'HTree's. Note that you might have to write more
-- than one to cover all possible HTrees. You might also need an extension or
-- two, so look out for something... flexible... in the error messages!
-- Recursion is your friend here - you shouldn't need to add a constraint to
-- the GADT!

instance Eq (HTree Empty) where
    HEmpty == HEmpty = True

instance (Eq a, Eq (HTree l), Eq (HTree r)) => Eq (HTree (Branch l a r)) where
    HBranch l1 a1 r1 == HBranch l2 a2 r2 = a1 == a2 && l1 == l2 && r1 == r2


----------------------------------------------------------------------------
-- EQIGHT
----------------------------------------------------------------------------

-- | a. Implement the following GADT such that values of this type are lists of
-- values alternating between the two types. For example:
--
-- @
--   f :: AlternatingList Bool Int
--   f = ACons True (ACons 1 (ACons False (ACons 2 ANil)))
-- @

data AlternatingList a b where
    ANull :: AlternatingList a b
    AOne :: a -> AlternatingList a b -> AlternatingList a b
    ATwo :: b -> AlternatingList a b -> AlternatingList a b

-- | b. Implement the following functions.

getFirsts :: AlternatingList a b -> [a]
getFirsts ANull = []
getFirsts (AOne a rest) = a : getFirsts rest
getFirsts (ATwo _ rest) = getFirsts rest

getSeconds :: AlternatingList a b -> [b]
getSeconds ANull = []
getSeconds (ATwo b rest) = b : getSeconds rest
getSeconds (AOne _ rest) = getSeconds rest

-- | c. One more for luck: write this one using the above two functions, and
-- then write it such that it only does a single pass over the list.

foldValues :: forall a b . (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues = go (mempty, mempty)
  where
    go :: (a, b) -> AlternatingList a b -> (a, b)
    go res ANull = res
    go (a, b) (AOne x rest) = go (a `mappend` x, b) rest
    go (a, b) (ATwo x rest) = go (a,  b `mappend` x) rest

----------------------------------------------------------------------------
-- NINE
----------------------------------------------------------------------------

-- | Here's the "classic" example of a GADT, in which we build a simple
-- expression language. Note that we use the type parameter to make sure that
-- our expression is well-formed.

data Expr a where
  Equals    :: Expr Int  -> Expr Int            -> Expr Bool
  Add       :: Expr Int  -> Expr Int            -> Expr Int
  If        :: Expr Bool -> Expr a   -> Expr a  -> Expr a
  IntValue  :: Int                              -> Expr Int
  BoolValue :: Bool                             -> Expr Bool

-- | a. Implement the following function and marvel at the typechecker:

eval :: Expr a -> a
eval (Equals ex1 ex2) = eval ex1 == eval ex2
eval (Add ex1 ex2) = eval ex1 + eval ex2
eval (If ex1 ex2 ex3) = if eval ex1 then eval ex2 else eval ex3
eval (IntValue i) = i
eval (BoolValue b) = b

-- | b. Here's an "untyped" expression language. Implement a parser from this
-- into our well-typed language. Note that (until we cover higher-rank
-- polymorphism) we have to fix the return type. Why do you think this is?

data DirtyExpr
  = DirtyEquals    DirtyExpr DirtyExpr
  | DirtyAdd       DirtyExpr DirtyExpr
  | DirtyIf        DirtyExpr DirtyExpr DirtyExpr
  | DirtyIntValue  Int
  | DirtyBoolValue Bool

parse :: DirtyExpr -> Maybe (Expr Int)
parse (DirtyAdd dex1 dex2) = parse dex1 >>= \ex1 -> parse dex2 >>= \ex2 -> Just $ Add ex1 ex2
parse (DirtyIntValue i) = Just $ IntValue i
parse _ = Nothing

-- | c. Can we add functions to our 'Expr' language? If not, why not? What
-- other constructs would we need to add? Could we still avoid 'Maybe' in the
-- 'eval' function?

----------------------------------------------------------------------------
-- TEN
----------------------------------------------------------------------------

-- | Back in the glory days when I wrote JavaScript, I could make a composition
-- list like @pipe([f, g, h, i, j])@, and it would pass a value from the left
-- side of the list to the right. In Haskell, I can't do that, because the
-- functions all have to have the same type :(

-- | a. Fix that for me - write a list that allows me to hold any functions as
-- long as the input of one lines up with the output of the next.

data TypeAlignedList a b where
  -- ...

-- | b. Which types are existential?

-- | c. Write a function to append type-aligned lists. This is almost certainly
-- not as difficult as you'd initially think.

composeTALs :: TypeAlignedList b c -> TypeAlignedList a b -> TypeAlignedList a c
composeTALs = error "Implement me, and then celebrate!"
