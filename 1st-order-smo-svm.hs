{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module SVM where

import Prelude hiding (replicate, zip, map, filter, max, min, not, zipWith, sum, unzip, fst, snd, replicate, maximum, minimum)
  
import qualified Prelude as P
import Data.Array.Accelerate as Acc
import Data.Array.Accelerate.CUDA

-- Scalar a -> Exp a
fromScalar :: (Elt a) => Acc (Scalar a) -> Exp a
fromScalar x = x ! index0

-- Exp a -> a
fromExp :: (Elt a) => Exp a -> a
fromExp x = (toList(run $ unit $ x))!!0

-- Exp Bool -> Bool
fromExpBool :: Exp Bool -> Bool
fromExpBool x
  | int == 1 = True
  | otherwise = False
  where int = (fromExp (x ? (1, 0))) :: Int

-- Create 2d index
index2 :: Int -> Int -> Exp (Z :. Int :. Int)
index2 x y = lift $ Z :. x :. y

-- Get an array with same shape but contains each index instead
indicesOf :: (Shape ix, Elt e) => Acc (Array ix e) -> Acc (Array ix ix)
indicesOf arr = generate (shape arr) (\ix -> ix)

testind = run $ indicesOf (createArray (index1 4) ([1, 3, 5, 7]::[Int]))

-- If n is not between low, high then make it nearest (low,high)
fit :: (Elt t, IsScalar t) => Exp t -> (Exp t, Exp t) -> Exp t
fit n (low, high) = Acc.min (Acc.max low n) high

testfit = fromExp $ fit (1::Exp Int) (2, 4)

-- Check if low < n < high
inside
  :: (Elt t, IsScalar t) => Exp t -> (Exp t, Exp t) -> Exp Bool
inside n (low, high) = (low <* n) &&* (n <* high)

testin1 = fromExp $ inside (3::Exp Int) (2, 4)
testin2 = fromExp $ inside (3::Exp Int) (2, 3)

-- Create Acc(Array sh a) from [a]
createArray :: (Shape dim, Num e, Elt e) => Exp dim -> [e] 
  -> Acc(Array dim e)
createArray sh list = use$fromList(fromExp sh) list

-- Check if two 1d indices are equal
ieq1 :: Exp DIM1 -> Exp DIM1 -> Exp Bool
ieq1 ix iy = x ==* y
  where ((Z:.x),(Z:.y)) = (unlift ix, unlift iy)

testieq = fromExp $ ieq1 (index1 5) (index1 5)

-- Get first value of array
first :: (Shape ix, Elt e) => Acc (Array ix e) -> Exp e
first arr = (reshape (index1 $ size arr) arr) ! (index1 0)

testfst = fromExp $ first (createArray (index1 4) ([1, 3, 5, 7]::[Int]))

-- Find the maximum of an array
maximum :: (Shape ix, IsNum a, Elt a) => Acc (Array (ix :. Int) a) -> 
  Acc (Scalar a)
maximum arr = foldAll max (first arr) arr

testmax = run $ maximum (createArray (index1 4) ([1, 3, 5, 7]::[Int]))

-- Find the minimum of an array
minimum :: (Shape ix, IsNum a, Elt a) => Acc (Array (ix :. Int) a) -> 
  Acc (Scalar a)
minimum arr = foldAll min (first arr) arr

testmin = run $ minimum (createArray (index1 4) ([1, 3, 5, 7]::[Int]))

-- Find the sum of an array
sum :: (Num a, IsNum a, Elt a) => Acc(Vector a) -> Acc (Scalar a)
sum xs = fold (+) 0 xs

testsum = run $ sum (createArray (index1 4) ([1, 3, 5, 7]::[Int]))

-- xs cannot be empty, otherwise same as Prelude.filter
filter
  :: (Elt a) =>
     (Exp a -> Exp Bool) -> Acc (Vector a) -> Acc (Vector a)
filter cond xs = 
  permute (\x y -> x) initial
          (\ix -> (cond (xs!ix)) ? ((index1 (indices!ix)),ignore))
          xs
    where matches = map (\x -> (cond x) ? (1, 0)) xs
          indices = Acc.scanl (+) 0 matches
          count = index1 $ (sum matches)!(index0)
          initial = (generate count (\x -> xs!(index1 0)))

-- Find first value of an array that matches a condition
-- !It'll crash if nothing matches!
find :: (Elt e) => (Exp e -> Exp Bool) -> Acc (Vector e) -> Exp e
find cond arr = first (filter cond arr)  

-- If then else data structure
cond2 :: (Elt t) => (Exp Bool, Exp t) -> (Exp Bool, Exp t) -> Exp t 
  -> Exp t
cond2 (c1, a1) (c2, a2) a3 = c1 ? (a1, (c2 ? (a2, a3)))

-- Get vector at location in matrix
at :: (Elt e) => Acc (Array DIM2 e) -> Exp DIM1 -> Acc (Vector e)
at xs ix = (slice xs (lift $ Z :. x :. All))
  where (Z :. x) = unlift ix :: (Z:. Exp Int)

-- Check if ix is in Ih, given ys!ix, as!ix
isIh c yi ai = 
  (inside ai (0, c)) ||* 
  (yi >* 0 &&* ai ==* 0) ||*
  (yi <* 0 &&* ai ==* c)
    
-- Check if ix is in Il, given ys!ix, as!ix
isIl c yi ai = 
  (inside ai (0, c)) ||* 
  (yi >* 0 &&* ai ==* c) ||*
  (yi <* 0 &&* ai ==* 0)

-- Update As	  
updateAlpha
  :: (Elt e, IsFloating e) =>
     (Exp e, Exp e, t1, Acc (Array DIM2 e), Acc (Vector e))
     -> (Exp e, Exp e, Exp DIM1, Exp DIM1)
     -> Acc (Vector e)
     -> Acc (Vector e)
     -> Acc (Vector e)
     -> Acc (Vector e)
updateAlpha (c, r, kfn, xs, ys) (bh, bl, ih, il) as xhx xlx = 
  map (\ia -> let (i, a) = (fst ia, snd ia) 
              in cond2 (ieq1 i ih, ah') (ieq1 i il, al') a) 
      asx
  where
    n = (xhx!ih) + (xlx!il) - 2*(xhx!il)
    (ah, al, yh, yl) = (as!ih, as!il, ys!ih, ys!il)   -- ERROR WAS HERE
    al' = (al+((yl*(bh-bl))/n))`fit`(0, c)
    ah' = (ah+yl*yh*(al-al'))`fit`(0, c)  -- ERROR WAS HERE
    asx = zip (indicesOf as) as 
    
-- Update Fs
updatePhi
  :: (Elt e, IsFloating e) =>
     (Exp e, Exp e, t1, Acc (Array DIM2 e), Acc (Vector e))
     -> (Exp e, Exp e, Exp DIM1, Exp DIM1)
     -> Acc (Vector e)
     -> Acc (Vector e)
     -> Acc (Vector e)
     -> Exp e
     -> Exp e
     -> Acc (Vector e)
updatePhi (c, r, kfn, xs, ys) (bh, bl, ih, il) fs xhx xlx ahd ald = 
   map (\ix -> (fs!ix) +
               ahd*(ys!ih)*(xhx!ix) + 
			         ald*(ys!il)*(xlx!ix)) 
			 (indicesOf fs)
	 
			 
-- Update bh, bl, ih, il
updateState
  :: (Elt e, IsFloating e) =>
     (Exp e, Exp e, t1, Acc (Array DIM2 e), Acc (Vector e))
     -> Acc (Vector e)
     -> Acc (Vector e)
     -> (Exp e, Exp e, Exp DIM1, Exp DIM1)
updateState (c, r, kfn, xs, ys) as fs =
  (bh, bl, ih, il)
  where
    yix = indicesOf ys
    ihs = filter (\ix -> isIh c (ys!ix) (as!ix)) yix
    ils = filter (\ix -> isIl c (ys!ix) (as!ix)) yix
    bh = fromScalar $ minimum $ map (\ix -> fs!ix) ihs
    bl = fromScalar $ maximum $ map (\ix -> fs!ix) ils
    ih = find (\ix -> (fs!ix) ==* bh) ihs --
    il = find (\ix -> (fs!ix) ==* bl) ils

-- Step in minimization
step
  :: (IsFloating e, Elt e) =>
     (Exp e,
      Exp e,
      Acc (Vector e) -> Acc (Array DIM2 e) -> Acc (Vector e),
      Acc (Array DIM2 e),
      Acc (Vector e))
     -> (Exp e, Exp e, Exp DIM1, Exp DIM1)
     -> Acc (Vector e)
     -> Acc (Vector e)
     -> Bool
     -> Int
     -> (Acc (Vector e), e)
step args state as fs debug iterations =
  if (fromExpBool (bl <=* bh + 2 * r)) || 
     (debug && (iterations == 0)) then
    (as, fromExp (bl + bh)/2)
  else
    step args state' as' fs' debug (iterations-1)
  where 
    (c, r, kfn, xs, ys) = args
    (bh, bl, ih, il) = state
    Z:.h = unlift ih :: Z :. Exp Int
    Z:.l = unlift il :: Z :. Exp Int
    yix = indicesOf ys
    ihs = filter (\ix -> isIh c (ys!ix) (as!ix)) yix
    ils = filter (\ix -> isIl c (ys!ix) (as!ix)) yix
    hs = map (\ix -> let Z:.x = unlift ix :: Z :. Exp Int
                      in x) ihs
    ls = map (\ix -> let Z:.x = unlift ix :: Z :. Exp Int
                      in  x) ils
    (xhx, xlx) = (kfn (xs`at`ih) xs, kfn (xs`at`il) xs)
    as' = updateAlpha args state as xhx xlx
    fs' = updatePhi args state fs xhx xlx (as'!ih-as!ih) (as'!il-as!il)
    state' = updateState args as' fs'

-- Start stepping through minimization and return result.
minimize
  :: (IsFloating e, Elt e) =>
     (Exp e,
      Exp e,
      Acc (Vector e) -> Acc (Array DIM2 e) -> Acc (Vector e),
      Acc (Array DIM2 e),
      Acc (Vector e))
     -> Bool
     -> Int
     -> (Acc (Vector e), e)
minimize args debug iterations = 
  step args (bh, bl, ih, il) as fs debug iterations
  where 
    (c, r, kfn, xs, ys) = args
    fs = map (\y -> -y) ys
    as = generate (shape ys) (\ix -> 0)
    (bh, bl) = (-1, 1)
    ih = find (\ix -> (ys!ix) ==* 1) (indicesOf ys)
    il = find (\ix -> (ys!ix) ==* -1) (indicesOf ys)

-- A template for the lambda to be returned by `train`
template
  :: (Elt e, IsNum e, Elt t2, IsNum t2) =>
     (t1 -> t -> Acc (Array DIM1 e))
     -> t
     -> Acc (Array DIM1 e)
     -> Acc (Array DIM1 e)
     -> Exp e
     -> t1
     -> Exp t2
template kfn xs ys as b z = 
  let zx = kfn z xs
      v = fromScalar $ sum $ map 
            (\ix->(ys!ix)*(as!ix)*(zx!ix)) 
            (indicesOf ys)
      y = -b + v --
  in (y >* 0) ? (1, -1)

  
-- Train a support vector machine and return a classifier of each point
train
  :: (Plain t ~ t, IsFloating t, Elt t, Lift t, Elt t1, IsNum t1) =>
     (Acc (Vector t) -> Acc (Array DIM2 t) -> Acc (Vector t))
     -> Acc (Array DIM2 t)
     -> Acc (Vector t)
     -> Acc (Vector t)
     -> Exp t1
train kfn xs ys =
  let (c, r) = (4, 0.001)
      (as, b) = minimize (c, r, kfn, xs, ys) False 0
  in template kfn xs ys as (lift b)

-- Train a support vector machine and return a classifier of each point
debug xs ys i =
  let (c, r) = (4, 0.001)
      (as, b) = minimize (c, r, vmmult, xs, ys) True i
  in (run as, b)

-- Vector matrix multiplcation
vmmult
  :: Acc (Vector Double)
     -> Acc (Array DIM2 Double)
     -> Acc (Vector Double)
vmmult xs ys = Acc.fold (+) 0 (Acc.zipWith (*) xsm ys)
  where xsm =  (replicate (lift $ Z :. yh:.All) xs)
	Z :. yh :. yw = unlift (shape ys) :: (Z:. Exp Int :. Exp Int)

-- Simple test
xs = createArray (index2 2 2) -- # width, height
       ([-1, 1, 1, -1]::[Double])
ys = createArray (index1 2) -- # height
       ([-1, 1]::[Double])
       
testt :: Exp Int -> Int
testt r = 
  fromExp $ (train vmmult xs ys) 
            (xs`at`(index1 r))

-- More complicated test
rawx = [ 6,148,72,35,0,33.6,0.627,50,
 1,85,66,29,0,26.6,0.351,31,
 8,183,64,0,0,23.3,0.672,32,
 1,89,66,23,94,28.1,0.167,21,
 0,137,40,35,168,43.1,2.288,33,
 5,116,74,0,0,25.6,0.201,30,
 3,78,50,32,88,31,0.248,26,
 10,115,0,0,0,35.3,0.134,29,
 2,197,70,45,543,30.5,0.158,53,
 8,125,96,0,0,0,0.232,54]::[Double]
rawy = [1,-1,1,-1,1,-1,1,-1,1,1]::[Double]

diabx = createArray (index2 4 8) rawx
diaby = createArray (index1 4) rawy
diabb i = (debug diabx diaby i)
diab r = (fromExp $ (train vmmult diabx diaby) (diabx`at`(index1 r)))::Int
