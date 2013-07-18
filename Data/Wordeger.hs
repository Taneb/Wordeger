{-# OPTIONS_GHC -Wall #-}
module Data.Wordeger (Wordeger) where

import Data.Bits
import Data.Maybe
import Data.Profunctor.Unsafe
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as V
import Data.Word

newtype Wordeger = Wordeger {_runWordeger :: Vector Bool}

_padToEqual :: Vector Bool -> Vector Bool -> (Vector Bool, Vector Bool)
_padToEqual a b = let (n, m) = (V.length a, V.length b) in
  case compare n m of
    LT -> (a V.++ V.replicate (m - n) False, b)
    EQ -> (a, b)
    GT -> (a, b V.++ V.replicate (n - m) False)

_strip :: Vector Bool -> Vector Bool
_strip v | not (V.null v || V.unsafeLast v) = _strip (V.unsafeInit v)
         | otherwise = v
                       
_fullAdder :: Bool -> Bool -> Bool -> (Bool, Bool)
_fullAdder a b False = (a /= b, a && b)
_fullAdder a b True = (a == b, a || b)


_fromIntegral :: Integral a => a -> Vector Bool
_fromIntegral 0 = V.empty
_fromIntegral n | n < 0 = error "Data.Wordeger._fromInteger: cannot convert a negative integer"
               | otherwise = 
                 let (q, r) = n `divMod` 2
                 in (r == 1) `V.cons` _fromIntegral q
{-# SPECIALIZE _fromIntegral :: Integer -> Vector Bool #-}
{-# SPECIALIZE _fromIntegral :: Int     -> Vector Bool #-}
{-# SPECIALIZE _fromIntegral :: Word64  -> Vector Bool #-}

_toNum :: Num a => Vector Bool -> a
_toNum v | V.null v = 0
             | otherwise = 2 * _toNum (V.unsafeTail v) + if V.unsafeHead v then 1 else 0
{-# SPECIALIZE _toNum :: Vector Bool -> Integer #-}
{-# SPECIALIZE _toNum :: Vector Bool -> Int     #-}
{-# SPECIALIZE _toNum :: Vector Bool -> Word64  #-}

_succ :: Vector Bool -> Vector Bool
_succ v | V.null v = V.singleton True
        | V.unsafeHead v = False `V.cons` _succ (V.unsafeTail v)
        | otherwise = True `V.cons` V.unsafeTail v

_pred :: Vector Bool -> Vector Bool
_pred v | V.null v = error "Prelude.Enum.pred{Wordeger}: tried to take 'pred' of 0"
        | V.unsafeHead v = False `V.cons` V.unsafeTail v
        | otherwise = True `V.cons` _pred (V.unsafeTail v)



_add :: Vector Bool -> Vector Bool -> Vector Bool
_add a b = case (V.length a, V.length b) of  
  (0, _) -> b
  (_, 0) -> a
  (n, m) -> _strip $ case compare n m of
    LT -> go m False (a V.++ V.replicate (m - n) False) b
    EQ -> go n False a b
    GT -> go n False a (b V.++ V.replicate (n - m) False)
  where
    go :: Int -> Bool -> Vector Bool -> Vector Bool -> Vector Bool
    go 0 c _ _ = if c then V.singleton True else V.empty
    go n c x y = 
      let (o, c') = _fullAdder (V.unsafeHead x) (V.unsafeHead y) c
      in o `V.cons` go (n - 1) c' (V.unsafeTail x) (V.unsafeTail y)

_subFunc :: Bool -> Bool -> Bool -> (Bool, Bool)
_subFunc a b False = (a /= b, not a && b)
_subFunc a b True = (a == b, not a || b)

_subtract :: Vector Bool -> Vector Bool -> Vector Bool
_subtract a b = case (V.length a, V.length b) of
  (0, _) -> V.empty
  (_, 0) -> a
  (n, m) -> _strip . fromMaybe V.empty $ case compare n m of
    LT -> go m False (a V.++ V.replicate (m - n) False) b
    EQ -> go n False a b
    GT -> go n False a (b V.++ V.replicate (n - m) False)
  where
    go :: Int -> Bool -> Vector Bool -> Vector Bool -> Maybe (Vector Bool)
    go 0 c _ _ = if c then Nothing else Just V.empty
    go n c x y =
      let (o, c') = _subFunc (V.unsafeHead x) (V.unsafeHead y) c
      in fmap (V.cons o) $ go (n - 1) c' (V.unsafeTail x) (V.unsafeTail y)

data TCode a = C1 | C2 | C3 | T a deriving (Eq)

_niaveMultiply :: Vector Bool -> Vector Bool -> Vector Bool
_niaveMultiply u v = case (V.length u, V.length v) of
  (0, _) -> V.empty
  (_, 0) -> V.empty
  (n, m) -> 
    foldr _add V.empty 
    [V.replicate (x+y) False `V.snoc` (u V.! x && v V.! y) | x <- [0..n-1], y <- [0..m-1]]

_compare :: Vector Bool -> Vector Bool -> Ordering
_compare v' w' = let (v, w) = (_strip v', _strip w') in
  case V.length v `compare` V.length w of
    LT -> LT
    EQ -> if V.null v then EQ else V.unsafeInit v' `_compare` V.unsafeInit w'
    GT -> GT

instance Eq Wordeger where
  Wordeger a == Wordeger b = _strip a == _strip b

instance Ord Wordeger where
  Wordeger a `compare` Wordeger b = a `_compare` b

instance Show Wordeger where
  showsPrec n = showsPrec n . (_toNum::Vector Bool -> Integer) .# _runWordeger

instance Enum Wordeger where
  toEnum = Wordeger #. _fromIntegral
  fromEnum = _toNum .# _runWordeger
  succ = Wordeger #. _succ .# _runWordeger
  pred = Wordeger #. _pred .# _runWordeger

instance Num Wordeger where
  fromInteger = Wordeger #. _fromIntegral
  Wordeger x + Wordeger y = Wordeger (_add x y)
  Wordeger x - Wordeger y = Wordeger (_subtract x y)
  Wordeger x * Wordeger y = Wordeger (_niaveMultiply x y) -- REALLY SLOW
  negate _ = 0 -- should it be _|_?
  abs = id
  signum 0 = 0
  signum _ = 1

instance Real Wordeger where
  toRational = _toNum .# _runWordeger
  
instance Integral Wordeger where
  quotRem = undefined
  toInteger = _toNum .# _runWordeger
  
instance Bits Wordeger where
  Wordeger a .&. Wordeger b = Wordeger (V.zipWith (&&) `uncurry` _padToEqual a b)
  Wordeger a .|. Wordeger b = Wordeger (V.zipWith (||) `uncurry` _padToEqual a b)
  Wordeger a `xor` Wordeger b = Wordeger (V.zipWith (/=) `uncurry` _padToEqual a b)
  complement = Wordeger #. V.map not #. _runWordeger
  shift (Wordeger a) i | i >= 0 = Wordeger (a V.++ V.replicate i False)
                       | otherwise = Wordeger (V.drop i a)
  rotate = shift
  bit i = Wordeger (V.replicate (i - 1) False `V.snoc` True)
  testBit (Wordeger a) i = fromMaybe False (a V.!? i)
  bitSize _ = error "Data.Bits.bitSize(Wordeger)"
  isSigned _ = False
  popCount = V.foldl' (\acc b -> if b then acc + 1 else acc) 0 .# _runWordeger