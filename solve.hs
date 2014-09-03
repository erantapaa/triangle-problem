{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.Monad
import Data.Array
import Data.Char (isDigit, intToDigit)
import qualified Data.Set as S
import Data.STRef
import Data.Array.ST
import Control.Monad.ST
import Data.List (permutations,sort,groupBy,nub,isPrefixOf,intercalate)
import Data.Function (on)
import Data.Maybe (fromMaybe)
import System.Environment (getArgs)

type Grid = Array (Int,Int) Char

subsequencesOfSize :: Int -> [a] -> [[a]]
subsequencesOfSize n xs = let l = length xs
                          in if n>l then [] else subsequencesBySize xs !! (l-n)
 where
   subsequencesBySize [] = [[[]]]
   subsequencesBySize (x:xs) = let next = subsequencesBySize xs
                             in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])

moveEast (i,j) = (i,j+1)
moveNorth (i,j) = (i-1,j)
moveSouth (i,j) = (i+1,j)
moveWest (i,j) = (i,j-1)

isVariable c = 'A' <= c && c <= 'J'
isNumber c = isDigit c || c == '(' || c == ')'
isOpen c = c == ' ' || isVariable c

pad :: Int -> String -> String
pad !n [] = replicate n ' '
pad !n (c:cs) = c : pad (n-1) cs

padBorder n cs = "#" ++ pad n cs ++ "#"

-- return the number at grid position (i,j)
-- (i,j) should point to a '(', digit or ')'
numberAt grid (i,j) = do
  let leftj j0
        | c == '('  = Just (j0+1)
        | isDigit c = leftj (j0-1)
        | c == ')'  = leftj (j0-1)
        | otherwise = Nothing
          where c = grid!(i,j0)
  -- j0 = start of number
  j0 <- leftj j
  let nstr = takeWhile isDigit [ grid!(i,j1) | j1 <- [j0,j0+1..] ]
  return $ ((i, j0), read nstr) :: Maybe ((Int, Int), Int)

cellCorners :: Grid -> (Int,Int) -> [((Int,Int), Int)]
cellCorners grid ij0 = runST $ do
  seen <- newArray (bounds grid) False :: ST s (STUArray s (Int,Int) Bool)
  nums <- newSTRef S.empty
  let addNumber ij = do
        if isNumber (grid!ij)
          then case numberAt grid ij of
                 Nothing -> return ()
                 Just x -> do s <- readSTRef nums
                              writeSTRef nums (S.insert x s)
          else return ()

      checkNorthTip (i,j)  = mapM_ addNumber [ (i-1,j-1), (i-1,j), (i-1,j+1) ]
      checkSouthTip (i,j)  = mapM_ addNumber [ (i+1,j-1), (i+1,j), (i+1,j+1) ]
      checkNorthTip2 (i,j) = mapM_ addNumber [ (i-1,j), (i-1,j+1) ]
      checkSouthTip2 (i,j) = mapM_ addNumber [ (i+1,j), (i+1,j+1) ]
      visit' from ij@(i,j)
        | isOpen c   = mapM_ (visit ij) [ (i-1,j), (i+1,j), (i,j-1), (i,j+1) ]
        | isNumber c = addNumber ij -- parse the number
        | c == '/'  && d == '\\' = checkNorthTip2 ij
        | c == '\\' && d == '/'  = checkSouthTip2 ij
        | c == '/' && fromEast   = visit ij (i+1,j)
        | c == '/' && fromWest   = visit ij (i-1,j)
        | c == '\\' && fromEast  = visit ij (i-1,j)
        | c == '\\' && fromWest  = visit ij (i+1,j)
        | c == '^'               = checkNorthTip ij
        | c == 'v'               = checkSouthTip ij
        | otherwise              = return ()
          where c = grid!ij
                d = grid!(moveEast ij)
                fromEast = moveWest from == ij
                fromWest = moveEast from == ij
      visit from ij = do
        b <- readArray seen ij
        if b
          then return ()
          else do writeArray seen ij True; visit' from ij
  visit ij0 ij0
  s <- readSTRef nums
  return $ S.elems s

groupByFirst :: (Ord a, Ord b) => [ (a,b) ] -> [ (a, [b]) ]
groupByFirst pairs =
  [ (fst (head xys), map snd xys) |  xys <- groupBy (on (==) fst) (sort pairs) ]

evalEq ::[(Char, Int)] -> [Char] -> Int
evalEq assigns vars = sum [ fromMaybe 0 (lookup v assigns) | v <- vars  ]

-- return True if an equaltion is satisfied given a list of assignments
checkEq :: [(Char, Int)] -> (Int, [Char]) -> Bool
checkEq assigns (rhs, vars) = evalEq assigns vars == rhs

solve :: [String] -> IO ()
solve rows' = do
  let rows = filter (not . isPrefixOf "#") rows' -- allow for comments
      width = maximum $ map length rows
      height = length rows
      hborder = replicate (width+2) '#'
      grid = listArray ((0,0),(height+1,width+1)) $
                hborder ++ concatMap (padBorder width) rows ++ hborder
      -- locations of the variables
      vars = [ i | (i,v) <- assocs grid, isVariable v ]
      allcorners = nub $ concatMap (cellCorners grid) vars
      varNames = [ grid!ij | ij <- vars ]

      supports = groupByFirst [ (cij,v) | ij <- vars, let v = grid!ij, (cij,_) <- cellCorners grid ij ]
      equations = [ (z,vs) | (v, vs) <- supports, let Just z = lookup v allcorners ]

  -- show the equations
  putStrLn "Equations:"
  forM_ equations $ \(rhs,vs) -> do
    putStrLn $ "    " ++ show rhs ++ " = " ++ (intercalate " + " [ [x] | x <- vs] )
  -- find all solutions
  let vcount = length varNames
  forM_ (concatMap permutations $ subsequencesOfSize vcount [1..9]) $ \p -> do
    let assigns = zip varNames p
        allok = all (checkEq assigns) equations
    if allok
      then do putStrLn ""
              putStrLn $ "Found solution:"
              putStrLn $ "    " ++ (intercalate ", " [ [v] ++ " = " ++ show i | (v,i) <- assigns ])
              putStrLn $ unlines $ substitute grid assigns
      else return ()
{-
  forM_ equations $ \e@(rhs,vs) -> do
    let a = evalEq assigns0 vs
        b = checkEq assigns0 e
    putStrLn $ "equation " ++ show e ++ ": eval = " ++ show a ++ " rhs: " ++ show rhs ++ " check: " ++ show b
-}

substitute :: Grid -> [(Char,Int)] -> [[Char]]
substitute grid assigns =
  let ((ilo,jlo),(ihi,jhi)) = bounds grid
      go i j = let c = grid!(i,j) in maybe c intToDigit (lookup c assigns)
  in [ [ go i j | j <- [jlo+1..jhi-1] ] | i <- [ilo+1..ihi-1] ]

solveFile path = fmap lines (readFile path) >>= solve

test1 = solveFile "problem1"

main = do
  (arg1:_) <- getArgs
  solveFile arg1
