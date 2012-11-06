{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses, RankNTypes, FlexibleInstances, TypeFamilies, RecordWildCards, FlexibleContexts #-}

import qualified Diagrams.Prelude as D
import Diagrams.Prelude ((#))
import Diagrams.Backend.Cairo
import Diagrams.Backend.Cairo.Internal

import Data.Monoid

import Prelude hiding (lookup, zip)
import qualified Data.Map as Map
import Data.Key hiding (zipWith)
import Data.List hiding (lookup, zip)
import Data.Maybe
import Debug.Trace

import Data.Colour.CIE

class Keyed t => MutableKeys t where
  crossWith :: (FoldableWithKey t1, FoldableWithKey t2, Ord (Key t)) =>
    ((Key t1) -> (Key t2) -> (Key t))  -> (a -> b -> Maybe c) -> t1 a -> t2 b -> t c
  keyedAppend :: (FoldableWithKey t, Ord (Key t)) =>
    (a -> a -> a) -> t a -> t a -> t a

instance MutableKeys (Map.Map k) where
  crossWith kf vf a b = let as = toKeyedList a
                            bs = toKeyedList b
                        in Map.fromList [ (kf ka kb, fromJust $ vf va vb) | (ka,va) <- as, (kb, vb) <- bs,
                                                                  isJust $ vf va vb ]
  keyedAppend vf a b = let as = toKeyedList a
                           bs = toKeyedList b
                       in Map.fromListWith vf (as ++ bs)

class Label a
  where
  labelString :: a -> String

-- TODO: More Instances

instance Label String
  where
  labelString a = a

instance Label Char
  where
  labelString a = [a]

instance Label Int
  where
  labelString a = show a

data ConvertableDomain b = forall a . (Label a, Ord a, Ord b) => MkConvertableDomain a b

pack :: (Label a, Ord a, Ord b) => a -> b -> ConvertableDomain b
pack a b = MkConvertableDomain a b

instance (Show b) => Show (ConvertableDomain b)
  where
  show (MkConvertableDomain a b) = (labelString a) ++ "'"

instance Eq (ConvertableDomain b)
  where
  (==) (MkConvertableDomain _ x) (MkConvertableDomain _ y) = x == y

instance Ord (ConvertableDomain b)
  where
  (<=) (MkConvertableDomain _ x) (MkConvertableDomain _ y) = x <= y

instance Label (ConvertableDomain b)
  where
  labelString (MkConvertableDomain x _) = labelString x

data Codomain a = Codomain [a] deriving (Show,Eq)

newtype Range a = Range [a] deriving (Eq)
newtype Domain a = Domain [Range a]

data DataType = Continuous | Categorical deriving (Show, Eq)

instance (Show c, Ord c) => Show (Range c) where
  show (Range xs) = "{" ++ (intercalate "," $ map show xs) ++ "}"

instance (Show a, Ord a) => Show (Domain a) where
  show (Domain (r:[])) = show r
  show (Domain (r:rs)) = "" ++ (intercalate " x " $ map show $ r:rs) ++ ""

showTypedRange r Categorical = show (Range r)
showTypedRange r Continuous = "[" ++ (show $ minimum r) ++ "," ++ (show $ maximum r) ++ "]"

showTypedDomain dt (Domain rs) = intercalate " x " $ 
  map (\(r,t) -> showTypedRange r t) $ zip (map (\(Range r) -> r) rs) dt

-- Todo include Object -> Domain mapping

data Varset l c d m = Varset { label :: [l]
                             , codomain :: Codomain c
                             , domain :: [Domain d]
                             , dataTypes :: [DataType]
                             , objectMap :: m [c]}

type VarsetMap l c d = Varset l c d (Map.Map [d])

dim = length . label

instance (Label l, Show d, Ord d, Ord c, Show c, FoldableWithKey m, Lookup m, (Key m) ~ [d]) =>
  Show (Varset l c d m)
  where
  show v@(Varset l (Codomain codom) dom dt objM) =
    let d = dim v
        numRows = length codom
        widths = foldlWithKey dimWidths (take d $ repeat 0) objM
        widthsWithLabels = zipWith max widths (map (length . labelString) l)
        keyWidth = maximum $ 3:(map (\r -> length $ show r) codom)
        fullWidth = 3*(d+1)+1+(sum widthsWithLabels)+keyWidth
        vs = sort $ foldlWithKey voCollect [] objM
        rows = map (\(id,i) -> "| " ++ (blank $ (keyWidth - length (show id))) ++ (show id) ++
                              " | " ++ intercalate " | "
                          (map (\cd -> let pr =  show (i !! cd)
                                       in (blank $ (widthsWithLabels !! cd) - length pr) ++ pr)
                               [0..(d-1)])
                           ++ " |") vs
    in hline fullWidth ++
       "| KEY" ++ (blank $ (keyWidth - 3)) ++ " | " ++ intercalate " | " (map (\cd -> let pr = labelString (l !! cd)
                                       in (blank $ (widthsWithLabels !! cd) - length pr) ++ pr)
                                      [0..(d-1)]) ++ " |\n" ++
       hline fullWidth ++
       (intercalate "\n" $ rows) ++
       "\n" ++ hline fullWidth ++
       "Number of rows: " ++ (show numRows) ++ "\n" ++
       "Domain: " ++ (intercalate ", " $ map (showTypedDomain dt) dom)
    where dimWidths a c _ = zipWith max a (map (length . show) c)
          hline l = (take l $ repeat '-') ++ "\n"
          blank l = (take l $ repeat ' ')
          voCollect xs v os = (map (\o -> (o,v)) os) ++ xs

continuous :: Varset l c d m -> Varset l c d m
continuous (Varset l cod dom dt objM) = Varset l cod dom (map (const Continuous) dt) objM

fromList :: (Label l, Ord c) => l -> [c] -> VarsetMap l Int c
fromList l xs =
  let ix = [0..(length xs - 1)]
      vm = Map.fromListWith (++) $ (map (\i -> ([xs !! i], [i] )) ix)
      dom = [Domain [Range $ sort $ nub xs]]
  in Varset [l] (Codomain $ ix) dom [Categorical] vm

nonEmptyIntersect a b = let c = intersect a b
                        in if c == [] then Nothing else Just c


domainToKeys :: Domain a -> [[a]]
domainToKeys (Domain ranges) = foldr inflate [[]] ranges
  where inflate (Range vs) rs = concatMap (\r -> map (\v -> v : r) vs) rs

infixr 7 ///
infixr 6 /*/
infixr 5 /+/

class Crossable a b c ma mb mc
  where
  (/*/) :: (Label l, Eq o, FoldableWithKey ma, FoldableWithKey mb, MutableKeys mc) =>
              Varset l o a ma -> Varset l o b mb -> Varset l o c mc

instance (a ~ b, b ~ c, ma ~ mb, mb ~ mc, Key mc ~ Key ma, Key ma ~ Key mb, Key ma ~ [a], Ord a)
  => Crossable a b c ma mb mc where
  (/*/) (Varset l1 (Codomain codom1) dom1 dt1 objM1) (Varset l2 (Codomain codom2) dom2 dt2 objM2) =
    let dom = [Domain $ c1 ++ c2 | (Domain c1) <- dom1, (Domain c2) <- dom2]
        objM = crossWith (++) nonEmptyIntersect objM1 objM2
    in Varset (l1 ++ l2)
              (Codomain (intersect codom1 codom2))
              dom
              (dt1 ++ dt2)
              objM

class Nestable a b c ma mb mc
  where
  (///) :: (Label l, Eq o, FoldableWithKey ma, FoldableWithKey mb, Lookup mc, MutableKeys mc) =>
              Varset l o a ma -> Varset l o b mb -> Varset l o c mc

instance (a ~ b, b ~ c, ma ~ mb, mb ~ mc, Key mc ~ Key ma, Key ma ~ Key mb, Key ma ~ [a], Ord a)
  => Nestable a b c ma mb mc where
  (///) (Varset l1 (Codomain codom1) dom1 dt1 objM1) (Varset l2 (Codomain codom2) dom2 dt2 objM2) =
    let objM = crossWith (++) nonEmptyIntersect objM1 objM2
        keys2 = map fst $ toKeyedList objM2
        keys1 = map fst $ toKeyedList objM1
        dom = map (\x -> Domain x) $ concat $
              [let keys2 = domainToKeys d2
                   keys1 = domainToKeys d1
               in filter (not . null)
                  [ let keys1' = filter (\k1 -> isJust $ lookup (k1++k2) objM) keys1
                    in if keys1' == []  then []
                       else ( map (\vs -> Range $ nub vs) $ transpose $ keys1') ++
                        (map (\e -> Range [e]) k2)  | k2 <- keys2 ] | d1 <- dom1, d2 <- dom2]
    in Varset (l1 ++ l2)
              (Codomain (intersect codom1 codom2))
              dom
              (dt1 ++ dt2)
              objM

class Blendable a b c m
  where
  (/+/) :: (Label l, Eq o, FoldableWithKey m, MutableKeys m) =>
              Varset l o a m -> Varset l o a m -> Varset l o a m

instance (a ~ b, b ~ c, Ord (Key m), (Key m) ~ [a], Eq a, Show a, Ord a)
  => Blendable a b c m where
  (/+/) (Varset l1 (Codomain codom1) dom1 dt1 objM1) (Varset l2 (Codomain codom2) dom2 dt2 objM2) =
    let objM = keyedAppend (++) objM1 objM2
        domList = map (\(Domain d) -> d) (dom1 ++ dom2)
        jointDom = domainUnion $ groupBy domainOverlap domList
    in if dt1 == dt2 then Varset l1
                          (Codomain (union codom1 codom2))
                          jointDom
                          dt1
                          objM else error "Data type mismatch"
    where rangeUnion (Range a) (Range b) = Range (union a b)
          rangeOverlap (Range a) (Range b) = a /= b
          domainOverlap a b = length (filter id $ zipWith rangeOverlap a b) <= 1
          domainUnion dss = map (\(d:ds) -> Domain $ foldr du d ds) dss
          du nd d = zipWith rangeUnion d nd

-- TODO: map varsets

-- Graphics

-- Shapes: dot, sqr, cross, diamond, tri

-- Colour

-- Also point :: ShapeSpec -> Varset l c Double -> Varset l c D.Diagram b D.R2
-- Need to handle several domains, general domain split function, include domain mapping
-- in varset

type ShapeSpec d b = [d] -> D.Diagram b D.R2

infixr 4 <#>
(<#>) f g = \ds -> (f ds) # (g ds)

-- Aka const
shape :: D.Diagram b D.R2 -> [d] -> D.Diagram b D.R2
shape dia _ = dia

varshape f ds = f (ds !! 0)

position ds = D.translate (D.r2 (ds !! 0, ds !! 1))

pick :: [Int] -> [a] -> [a]
pick ids xs  = ids # map(xs !!)

dimsel :: [Int] -> ([d] -> a) -> ([d] -> a)
dimsel ids f = \ds -> f (pick ids ds)

point :: (FoldableWithKey m, (Key m) ~ [Double],
            D.PathLike (D.Diagram b D.R2)) 
          => ShapeSpec Double b 
          -> Varset l c Double m 
          -> D.Diagram b D.R2
point shapeSpec (Varset l (Codomain codom) dom dt objM) =
  foldrWithKey pointGen D.mempty objM
  where pointGen ds obj diagram = (shapeSpec ds) `D.atop` diagram


testVarset = ((fromList "Test" [1,2,3,4]) /*/ (fromList "Bla" [0.5,0.2,0.1,0.8])) /*/ (fromList "Bla" [2,1,4,3])

dia :: D.Diagram Cairo D.R2
dia = point (varshape (\d -> (D.circle $ d*0.5) # (D.fc $ cieXYZ d d 0.5)) # dimsel [1] <#> position # dimsel [0,2]) testVarset


testRender = do fst $ D.renderDia Cairo (CairoOptions "test.pdf" (D.Dims 200 200) PDF) dia