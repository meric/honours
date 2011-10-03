{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
module Main where

import Prelude hiding (replicate, zip, map, filter, max, min, not, zipWith, sum
  , unzip, fst, snd, replicate, maximum, minimum)
  
import qualified Prelude as P
import Data.Array.Accelerate as Acc
import Data.Array.Accelerate.CUDA
import Debug.Trace

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

testin1 = fromExp ((inside (3::Exp Int) (2, 4)) ? (1, 0::Exp Int))

-- Create Acc(Array sh a) from [a]
createArray :: (Shape dim, Elt e) => Exp dim -> [e] -> Acc(Array dim e)
createArray sh list = use$fromList(fromExp sh) list

-- Check if two 1d indices are equal
ieq1 :: Exp DIM1 -> Exp DIM1 -> Exp Bool
ieq1 ix iy = x ==* y
  where ((Z:.x),(Z:.y)) = (unlift ix, unlift iy)

testieq = fromExp $ ((ieq1 (index1 5) (index1 5)) ? (1, 0::Exp Int))

-- Get first value of array
first :: (Shape ix, Elt e) => Acc (Array ix e) -> Exp e
first arr = (reshape (index1 $ lift $ fromExp $ size arr) arr) ! (index1 0)

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
sum
  :: (Elt a, IsNum a, Shape ix) =>
     Acc (Array (ix :. Int) a) -> Acc (Array ix a)
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
--find cond arr = first (filter cond arr) 
find cond arr = (fold (\a b -> (cond a) ? (a, b)) (arr!index1 0) arr) ! index0

testfind = fromExp $ val
  where val = find (\x -> x ==* 3) (createArray (index1 2) [1, 3::Int])

-- If then else data structure
cond2 :: (Elt t) => (Exp Bool, Exp t) -> (Exp Bool, Exp t) -> Exp t 
  -> Exp t
cond2 (c1, a1) (c2, a2) a3 = c1 ? (a1, (c2 ? (a2, a3)))

testcond = fromExp val
  where val = cond2 (1==*(0::Exp Int), 0) (1==*(0::Exp Int), 1) (2::Exp Int)

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
    (ah, al, yh, yl) = (as!ih, as!il, ys!ih, ys!il)
    al' = (al+((yl*(bh-bl))/n))`fit`(0, c)
    ah' = (ah+yl*yh*(al-al'))`fit`(0, c)
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
     -> Acc (Vector e)
     -> Acc (Vector e)
     -> (Exp e, Exp e, Exp DIM1, Exp DIM1)
updateState (c, r, kfn, xs, ys) as fs xhx xxx =
  (bh, bl, ih, il)
  where
    yix = indicesOf ys
    ihs = filter (\ix -> isIh c (ys!ix) (as!ix)) yix
    ils = filter (\ix -> isIl c (ys!ix) (as!ix)) yix
    bh = fromScalar $ minimum $ map (\ix -> fs!ix) ihs
    bl = fromScalar $ maximum $ map (\ix -> fs!ix) ils
    ih = find (\ix -> (fs!ix) ==* bh) ihs 
    
    fils = filter (\ix -> (fs!ih) <* (fs!ix)) ils
    dfs = map (\ix -> 
               let b = ((fs!ih) - (fs!ix))
                   n = (xhx!ih) + (xxx!ix) - 2*(xhx!ix) in
                       (b * b / n)) yix
    maxdf =(maximum dfs) ! index0
    il = find (\ix -> (dfs!ix) ==* maxdf) fils
    --il = find (\ix -> (fs!ix) ==* bl) ils

-- Step in minimization
step
  :: (IsFloating e, Elt e) =>
     (Exp e,
      Exp e,
      Acc (Array DIM2 e) -> Acc (Array DIM2 e) -> Acc (Vector e),
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
    xhx = vm kfn (xs`at`ih) xs
    xlx = vm kfn (xs`at`il) xs
    xxx = kfn xs xs
    as' = updateAlpha args state as xhx xlx
    fs' = updatePhi args state fs xhx xlx (as'!ih-as!ih) (as'!il-as!il)
    state' = updateState args as' fs' xhx xxx

-- Start stepping through minimization and return result.
minimize
  :: (IsFloating e, Elt e) =>
     (Exp e,
      Exp e,
      Acc (Array DIM2 e) -> Acc (Array DIM2 e) -> Acc (Vector e),
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
    ih = lift $ fromExp $ find (\ix -> (ys!ix) ==* 1) (indicesOf ys)
    il = lift $ fromExp $ find (\ix -> (ys!ix) ==* -1) (indicesOf ys)
    
-- use this template to create classifier of a single point   
template
  :: (Elt e, IsFloating e, Elt t, IsNum t) =>
     (Acc (Array DIM2 e) -> Acc (Array DIM2 e) -> Acc (Vector e))
     -> Acc (Array DIM2 e)
     -> Acc (Vector e)
     -> Acc (Vector e)
     -> Exp e
     -> Acc (Vector e)
     -> Exp t
template kfn xs ys as' b z = 
  let zx = vm kfn z xs
      as = use $ run as' -- cache as
      v = fromScalar $ sum $ map 
            (\ix->(ys!ix)*(as!ix)*(zx!ix)) 
            (indicesOf ys)
      y = -b + v --
  in (y >* 0) ? (1, -1)

-- use this template to create classifier of many points
template2
  :: (Elt e, IsFloating e) =>
     (Acc (Array DIM3 e)
     -> Acc (Array DIM3 e)
     -> Acc (Array DIM2 e))
     -> Acc (Array DIM2 e)
     -> Acc (Vector e)
     -> Acc (Vector e)
     -> Exp e
     -> Acc (Array DIM2 e)
     -> Acc (Vector e)
template2 kfn xs ys as' b zs = 
  -- Array (Z :. 3) :. 3 [z1*x1, z2*x1, z3*x1, 
  --                      z1*x2, z2*x2, z3*x2, 
  --                      z1*x3, z2*x3, z3*x3]
  -- TODO: cast kfn 221 to kfn 332  
  let zsxs = (cm kfn) zs xs  
      as = use $ run as' -- cache as
      Z :. yh = unlift (shape ys) :: (Z:. Exp Int)
      iy = (replicate (lift $ Z :. All :. yh) (indicesOf ys)) :: Acc(Array DIM2 DIM1)
      vs = sum $ map (\iab -> let Z :. a :. b = unlift iab 
                                                :: (Z:. Exp Int :. Exp Int) 
                                  ia = (index1 a)
                                  ib = (index1 b)
                               in
                               (ys!ia)*(as!ia)*(zs!iab))
                      (indicesOf iy)
  in map (\v -> (-b + v >* 0) ? (1, -1)) vs
                   
-- Train a support vector machine and return a classifier of each point
train
  :: (Plain t ~ t, IsFloating t, Elt t, Lift t) =>
     (Acc (Array DIM2 t) -> Acc (Array DIM2 t) -> Acc (Vector t))
     -> (Acc (Array DIM3 t) -> Acc (Array DIM3 t) -> Acc (Array DIM2 t))
     -> Acc (Array DIM2 t)
     -> Acc (Vector t)
     -> Acc (Array DIM2 t)
     -> Acc (Vector t)
train kfn kfn3 xs ys =
  let (c, r) = (4, 0.001)
      args = (c, r, kfn, xs, ys)
      (as, b) = minimize args False 0
  in template2 kfn3 xs ys as (lift b)

-- One x kfn-ed with each of ys
vm
  :: (Elt e, IsFloating e) =>
     (Acc (Array DIM2 e) -> Acc (Array DIM2 e) -> Acc (Vector e))
     -> Acc (Vector e)
     -> Acc (Array DIM2 e)
     -> Acc (Vector e)
vm kfn xsv ys = kfn xsm ys
  where xsm =  (replicate (lift $ Z :. yh:.All) xsv)
        Z :. yh :. yw = unlift (shape ys) :: (Z:. Exp Int :. Exp Int)
        
type Number = Float	 

-- Vector matrix multiplcation kernel function. 
-- Can only guarantee to work with 1st order heuristic
mmmult
  :: (Elt e, IsFloating e) =>
     Acc (Array DIM2 e)
     -> Acc (Array DIM2 e)
     -> Acc (Vector e)
mmmult xs ys = Acc.fold (+) 0 (Acc.zipWith (*) xs ys)

-- gaussian kernel function
gaussian
  :: (Elt e, IsFloating e) =>
     Acc (Array DIM2 e)
     -> Acc (Array DIM2 e)
     -> Acc (Vector e)
gaussian xs ys = 
  Acc.map (\x -> exp (-x)) 
          (Acc.fold (+) 0 (Acc.zipWith (\x y -> ((x-y)^2)) xs ys))

-- gaussian kernel function but for DIM3 Arrays
gaussian3
  :: (Elt e, IsFloating e) =>
     Acc (Array DIM3 e)
     -> Acc (Array DIM3 e)
     -> Acc (Array DIM2 e)
gaussian3 xs ys = 
  Acc.map (\x -> exp (-x)) 
          (Acc.fold (+) 0 (Acc.zipWith (\x y -> ((x-y)^2)) xs ys))

-- each of xs kfn-ed with each of ys
cm kfn xs ys = kfn xs3 ys3
  where xs3 = (replicate (lift $ Z :. All :. yh :. All) xs)
        ys3 = (replicate (lift $ Z :. yh :. All :. All) ys) 
        Z :. yh :. yw = unlift (shape ys) :: (Z:. Exp Int :. Exp Int)

-- points
xs = createArray (index2 10 8) 
     ([6,148,72,35,0,33.6,0.627,50,
       1,85,66,29,0,26.6,0.351,31,
       8,183,64,0,0,23.3,0.672,32,
       1,89,66,23,94,28.1,0.167,21,
       0,137,40,35,168,43.1,2.288,33,
       5,116,74,0,0,25.6,0.201,30,
       3,78,50,32,88,31,0.248,26,
       10,115,0,0,0,35.3,0.134,29,
       2,197,70,45,543,30.5,0.158,53,
       8,125,96,0,0,0,0.232,54]::[Number])
-- labels
ys = createArray (index1 10) ([1,-1,1,-1,1,-1,1,-1,1,1]::[Number])

-- classifier
classifier = (train gaussian gaussian3 xs ys)

-- classify all 10 points
classify = classifier xs :: Acc (Vector Number)

main :: IO ()
main = putStrLn $ show $ run classify
