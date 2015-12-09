import Data.List (find)

class Metric a where
  distance :: a -> a -> Double

newtype Euclid2d = Euclid2d (Double, Double)
  deriving Show

instance Metric Euclid2d where
  distance (Euclid2d (x, y)) (Euclid2d (x', y')) = sqrt (dx2 + dy2)
    where
      dx2 = (x' - x) * (x' - x)
      dy2 = (y' - y) * (y' - y)

instance Metric a => Metric (a, b) where
  distance (x, _) (y, _) = distance x y

data MMNode a = Lf (MMLeaf a)
              | Ex a a Double (MMLeaf a) (MMLeaf a) (MMLeaf a) (MMLeaf a)
              | In a a Double (MMNode a) (MMNode a) (MMNode a) (MMNode a)
  deriving Show

data MMLeaf a = Zero
              | One a
              | Two a a Double
  deriving Show
  
insertLf :: Metric a => a -> MMLeaf a -> Maybe (MMLeaf a)
insertLf x Zero        = Just $ One x
insertLf x (One y)     = Just $ Two y x (distance x y)
insertLf _ (Two _ _ _) = Nothing

empty :: MMNode a
empty = Lf Zero

insert' :: Metric a => a -> MMNode a -> MMNode a
insert' x (Lf Zero) = Lf (One x)
insert' x (Lf (One y)) = Lf (Two y x (distance x y))
insert' x (Lf (Two y z r)) =
  let dy = distance x y
      dz = distance x z in
  if dy < r then
    if dz < r then
      Ex y z r (One x) Zero Zero Zero
    else
      Ex y z r Zero (One x) Zero Zero
  else
    if dz < r then
      Ex y z r Zero Zero (One x) Zero
    else
      Ex y z r Zero Zero Zero (One x)
insert' x (Ex y z r l1 l2 l3 l4) = {- No semi-balancing -}
  let dy = distance x y
      dz = distance x z in
  if dy < r then
    if dz < r then
      case insertLf x l1 of
        Just l1' ->
          Ex y z r l1' l2 l3 l4
        Nothing ->
          In y z r (insert' x (Lf l1)) (Lf l2) (Lf l3) (Lf l4)
    else
      case insertLf x l2 of
        Just l2' ->
          Ex y z r l1 l2' l3 l4
        Nothing ->
          In y z r (Lf l1) (insert' x (Lf l2)) (Lf l3) (Lf l4)
  else
    if dz < r then
      case insertLf x l3 of
        Just l3' ->
          Ex y z r l1 l2 l3' l4
        Nothing ->
          In y z r (Lf l1) (Lf l2) (insert' x (Lf l3)) (Lf l4)
    else
      case insertLf x l4 of
        Just l4' ->
          Ex y z r l1 l2 l3 l4'
        Nothing ->
          In y z r (Lf l1) (Lf l2) (Lf l3) (insert' x (Lf l4))
insert' x (In y z r n1 n2 n3 n4) =
  let dy = distance x y
      dz = distance x z in
  if dy < r then
    if dz < r then
      In y z r (insert' x n1) n2 n3 n4
    else
      In y z r n1 (insert' x n2) n3 n4
  else
    if dz < r then
      In y z r n1 n2 (insert' x n3) n4
    else
      In y z r n1 n2 n3 (insert' x n4)

insert :: Metric a => a -> MMNode a -> MMNode a
insert x (Ex y z r l1 l2 l3 l4) = balance x y z r l1 l2 l3 l4
insert x mmnode                 = insert' x mmnode

balance :: Metric a => a -> a -> a -> Double
           -> MMLeaf a -> MMLeaf a -> MMLeaf a -> MMLeaf a
           -> MMNode a
balance x y z r l1 l2 l3 l4 = {- Semi-balancing -}
  let ls = x : y : z : concatMap toList [l1, l2, l3, l4] in
    if length ls > 8 then
      insert' x (In y z r (Lf l1) (Lf l2) (Lf l3) (Lf l4))
    else
      let ins (a, b, other) = foldr insert' (Lf (two a b)) other
          isEx (Ex _ _ _ _ _ _ _) = True
          isEx _                  = False in
      case find isEx (map ins (allPairs ls)) of
        Just mmnode ->
          mmnode
        Nothing     ->
          insert' x (In y z r (Lf l1) (Lf l2) (Lf l3) (Lf l4))

allPairs :: [a] -> [(a, a, [a])]
allPairs xs = map go (take 2 xs)
  where
    go ((x:y:[]), r) = (x, y, r)
    take 0 xs     = [([], xs)]
    take _ []     = []
    take n (x:xs) = t1 ++ t2
      where
        t1 = map (\(l, r) -> (x:l, r)) (take (n-1) xs)
        t2 = map (\(l, r) -> (l, x:r)) (take n xs)

toList :: MMLeaf a -> [a]
toList Zero        = []
toList (One x)     = [x]
toList (Two x y _) = [x, y]

intersect :: Metric a => a -> Double -> MMNode (a, b) -> Bool
intersect _ _  (Lf Zero) = False
intersect p rq (Lf (One (pa, _))) = distance p pa < rq
intersect p rq (Lf (Two (pa, _) (pb, _) r)) = intersect2 p rq pa pb r
intersect p rq (Ex (pa, _) (pb, _) r _ _ _ _) = intersect2 p rq pa pb r
intersect p rq (In (pa, _) (pb, _) r _ _ _ _) = intersect2 p rq pa pb r

intersect2 :: Metric a => a -> Double -> a -> a -> Double -> Bool
intersect2 p rq pa pb r = r1 || r2 || r3 || r4
  where
    da = distance p pa
    db = distance p pb
    r1 = db < rq + r && da < rq + r
    r2 = db + rq >= r && da < rq + r
    r3 = db < rq + r && da + rq >= r
    r4 = db + rq >= r && da + rq >= r

two :: Metric a => a -> a -> MMLeaf a
two x y = Two x y (distance x y)

ex = foldl (flip insert) (Lf Zero) (zip (map Euclid2d coords) names)
  where
    names = [ "a",    "b",   "c",    "d",   "e",     "f",     "g",    "h"]
    coords = [(-2,0), (2,0), (-1.2,0.2), (0.9,-1), (-3.5, -1), (-3.5, -3.5), (3.5, -3), (-0.5, 0.5)]
