{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Data.ECTA.Internal.ECTA.Enumeration (
    TermFragment(..)
  , termFragToTruncatedTerm

  , SuspendedConstraint(..)
  , scGetPathTrie
  , scGetUVar
  , descendScs
  , UVarValue(..)

  , EnumerationState(..)
  , uvarCounter
  , uvarRepresentative
  , uvarValues
  , initEnumerationState
  , initEnumerationConfig


  , EnumerateM
  , getUVarRepresentative
  , assimilateUvarVal
  , mergeNodeIntoUVarVal
  , getUVarValue
  , getTermFragForUVar
  , runEnumerateM


  , enumerateNode
  , enumerateEdge
  , firstExpandableUVar
  , enumerateOutUVar
  , enumerateOutFirstExpandableUVar
  , enumerateFully
  , expandTermFrag
  , expandUVar

  , getAllTruncatedTerms
  , getAllTerms
  , naiveDenotation
  , naiveDenotationBounded
  ) where

import Control.Monad ( forM_, guard, unless )
import Control.Monad.State.Strict ( StateT(..) )
import qualified Data.IntMap as IntMap
import Data.Maybe ( fromMaybe, isJust )
import Data.Monoid ( Any(..) )
import Data.Semigroup ( Max(..) )
import           Data.Sequence ( Seq((:<|), (:|>)) )
import qualified Data.Sequence as Sequence
import Control.Monad.Identity ( Identity )

import Control.Lens ( use, ix, (%=), (.=) )
import Control.Lens.TH ( makeLenses )
import           Pipes
import qualified Pipes.Prelude as Pipes

import Data.List.Index ( imapM )

import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Paths
import Data.ECTA.Term
import           Data.Persistent.UnionFind ( UnionFind, UVar, uvarToInt, intToUVar, UVarGen )
import qualified Data.Persistent.UnionFind as UnionFind
import Data.Text.Extended.Pretty
import Control.Monad.Reader
import Text.ParserCombinators.ReadPrec (reset)
import Data.Map (Map, singleton, findWithDefault, insert)
import qualified Control.Applicative as Map
import qualified Control.Lens as Map
import qualified Data.HashMap.Lazy as Map

-------------------------------------------------------------------------------


---------------------------------------------------------------------------
------------------------------- Term fragments ----------------------------
---------------------------------------------------------------------------

data TermFragment = TermFragmentNode !Symbol ![TermFragment]
                  | TermFragmentUVar UVar
  deriving ( Eq, Ord, Show )

termFragToTruncatedTerm :: TermFragment -> Term
termFragToTruncatedTerm (TermFragmentNode s ts) = Term s (map termFragToTruncatedTerm ts)
termFragToTruncatedTerm (TermFragmentUVar uv)   = Term (Symbol $ "v" <> pretty (uvarToInt uv)) []

---------------------------------------------------------------------------
------------------------------ Enumeration state --------------------------
---------------------------------------------------------------------------

-----------------------
------- Suspended constraints
-----------------------

data SuspendedConstraint = SuspendedConstraint !PathTrie !UVar
  deriving ( Eq, Ord, Show )

scGetPathTrie :: SuspendedConstraint -> PathTrie
scGetPathTrie (SuspendedConstraint pt _) = pt

scGetUVar :: SuspendedConstraint -> UVar
scGetUVar (SuspendedConstraint _ uv) = uv

descendScs :: Int -> Seq SuspendedConstraint -> Seq SuspendedConstraint
descendScs i scs = Sequence.filter (not . isEmptyPathTrie . scGetPathTrie)
                   $ fmap (\(SuspendedConstraint pt uv) -> SuspendedConstraint (pathTrieDescend pt i) uv)
                          scs

-----------------------
------- UVarValue
-----------------------

data UVarValue = UVarUnenumerated { contents    :: !(Maybe Node)
                                  , constraints :: !(Seq SuspendedConstraint)
                                  }
               | UVarEnumerated   { termFragment :: !TermFragment }
               | UVarEliminated
  deriving ( Eq, Ord, Show )

intersectUVarValue :: UVarValue -> UVarValue -> UVarValue
intersectUVarValue (UVarUnenumerated mn1 scs1) (UVarUnenumerated mn2 scs2) =
  let newContents = case (mn1, mn2) of
                      (Nothing, x      ) -> x
                      (x,       Nothing) -> x
                      (Just n1, Just n2) -> Just (intersect n1 n2)
      newConstraints = scs1 <> scs2
  in UVarUnenumerated newContents newConstraints

intersectUVarValue UVarEliminated            _                         = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _                         UVarEliminated            = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _                         _                         = error "intersectUVarValue: Intersecting with enumerated value not implemented"


-----------------------
------- Top-level state
-----------------------

data EnumerationState = EnumerationState {
    _uvarCounter        :: UVarGen
  , _uvarRepresentative :: UnionFind
  , _uvarValues         :: Seq UVarValue
  , _uvarMaxDepth       :: Map UVar Int
  }
  deriving ( Eq, Ord, Show )

makeLenses ''EnumerationState

defaultUnrollingDepth :: Int
defaultUnrollingDepth = 5

initEnumerationState :: Node -> EnumerationState
initEnumerationState n = let (uvg, uv) = UnionFind.nextUVar UnionFind.initUVarGen
                         in EnumerationState uvg
                                             (UnionFind.withInitialValues [uv])
                                             (Sequence.singleton (UVarUnenumerated (Just n) Sequence.Empty))
                                             (singleton uv defaultUnrollingDepth)


-----------------------
------- Top-level state
-----------------------

newtype EnumerationConfig = EnumerationConfig {
    maxDepth       :: Int
  }
  deriving ( Eq, Ord, Show )

initEnumerationConfig :: Int -> EnumerationConfig
initEnumerationConfig = EnumerationConfig


---------------------------------------------------------------------------
---------------------------- Enumeration monad ----------------------------
---------------------------------------------------------------------------

---------------------
-------- Monad
---------------------


type EnumerateM = ReaderT EnumerationConfig (StateT EnumerationState [])

runEnumerateM :: EnumerateM a -> EnumerationConfig -> EnumerationState -> [(a, EnumerationState)]
runEnumerateM f cfg = runStateT (runReaderT f cfg)


---------------------
-------- UVar accessors
---------------------

nextUVar :: EnumerateM UVar
nextUVar = do c <- use uvarCounter
              let (c', uv) = UnionFind.nextUVar c
              uvarCounter .= c'
              return uv

addUVarValue :: Maybe Node -> Int -> EnumerateM UVar
addUVarValue x d = do
                    uv <- nextUVar
                    uvarValues %= (:|> UVarUnenumerated x Sequence.Empty)
                    uvarMaxDepth %= insert uv d
                    return uv

getUVarValue :: UVar -> EnumerateM UVarValue
getUVarValue uv = do uv' <- getUVarRepresentative uv
                     let idx = uvarToInt uv'
                     values <- use uvarValues
                     return $ Sequence.index values idx

getTermFragForUVar :: UVar -> EnumerateM TermFragment
getTermFragForUVar uv =  termFragment <$> getUVarValue uv

getUVarRepresentative :: UVar -> EnumerateM UVar
getUVarRepresentative uv = do uf <- use uvarRepresentative
                              let (uv', uf') = UnionFind.find uv uf
                              uvarRepresentative .= uf'
                              return uv'

---------------------
-------- Creating UVar's
---------------------

pecToSuspendedConstraint :: PathEClass -> EnumerateM SuspendedConstraint
pecToSuspendedConstraint pec = do uv <- addUVarValue Nothing defaultUnrollingDepth
                                  return $ SuspendedConstraint (getPathTrie pec) uv


---------------------
-------- Merging UVar's / nodes
---------------------

assimilateUvarVal :: UVar -> UVar -> EnumerateM ()
assimilateUvarVal uvTarg uvSrc
                                | uvTarg == uvSrc      = return ()
                                | otherwise            = do
  values <- use uvarValues
  let srcVal  = Sequence.index values (uvarToInt uvSrc)
  let targVal = Sequence.index values (uvarToInt uvTarg)
  case srcVal of
    UVarEliminated -> return () -- Happens from duplicate constraints
    _              -> do
      let v = intersectUVarValue srcVal targVal
      guard (contents v /= Just EmptyNode)
      uvarValues.(ix $ uvarToInt uvTarg) .= v
      uvarValues.(ix $ uvarToInt uvSrc)  .= UVarEliminated


mergeNodeIntoUVarVal :: UVar -> Node -> Seq SuspendedConstraint -> EnumerateM ()
mergeNodeIntoUVarVal uv n scs = do
  uv' <- getUVarRepresentative uv
  let idx = uvarToInt uv'
  uvarValues.(ix idx) %= intersectUVarValue (UVarUnenumerated (Just n) scs)
  newValues <- use uvarValues
  guard (contents (Sequence.index newValues idx) /= Just EmptyNode)


---------------------
-------- Variant maintainer
---------------------

-- This thing here might be a performance issue. UPDATE: Yes it is; clocked at 1/3 the time and 1/2 the
-- allocations of enumerateFully
--
-- It exists because it was easier to code / might actually be faster
-- to update referenced uvars here than inline in firstExpandableUVar.
-- There is no Sequence.foldMapWithIndexM.
refreshReferencedUVars :: EnumerateM ()
refreshReferencedUVars = do
  values <- use uvarValues
  updated <- traverse (\case UVarUnenumerated n scs ->
                               UVarUnenumerated n <$>
                                   mapM (\sc -> SuspendedConstraint (scGetPathTrie sc)
                                                                       <$> getUVarRepresentative (scGetUVar sc))
                                        scs

                             x                      -> return x)
                      values

  uvarValues .= updated


---------------------
-------- Core enumeration algorithm
---------------------

enumerateNode :: Seq SuspendedConstraint -> Node -> EnumerateM TermFragment
enumerateNode _   EmptyNode = mzero
enumerateNode scs n         =
  let (hereConstraints, descendantConstraints) = Sequence.partition (\(SuspendedConstraint pt _) -> isTerminalPathTrie pt) scs
  in case hereConstraints of
       -- here, instead of enumerating constraints recursively, the Mu node is suspended and discarded
       Sequence.Empty -> case n of
                          --  Mu m    -> TermFragmentUVar <$> addUVarValue (Just n) -- assign to the mu node a variable, and move on with life
                           Mu _    -> do
                            config <- ask
                            if maxDepth config <= 0 then
                              TermFragmentUVar <$> addUVarValue (Just n) 0
                            else
                              local (\x -> initEnumerationConfig (maxDepth x - 1)) (enumerateNode scs (unfoldOuterRec n))
                           Node es -> enumerateEdge scs =<< lift (lift es) -- for each of its incoming edges, enumerate and assimilate for output (I guess this implicitly forces left to right DFS)
                           _       -> error $ "enumerateNode: unexpected node " <> show n

       -- this case is identical between Mu and "Lambda" nodes
       (x :<| xs)     -> do reps <- mapM (getUVarRepresentative . scGetUVar) hereConstraints
                            forM_ xs $ \sc -> uvarRepresentative %= UnionFind.union (scGetUVar x) (scGetUVar sc) -- we know these are of the type \epsilon = v_i, so all v_i are now equal
                            uv <- getUVarRepresentative (scGetUVar x)
                            mapM_ (assimilateUvarVal uv) reps -- actually intersect their p terms

                            mergeNodeIntoUVarVal uv n descendantConstraints -- intersect this node with whatever remains of the other p terms
                            return $ TermFragmentUVar uv -- mark this node as uv, and return the fragment of uv

enumerateEdge :: Seq SuspendedConstraint -> Edge -> EnumerateM TermFragment
enumerateEdge scs e = do
  let highestConstraintIndex = getMax $ foldMap (\sc -> Max $ fromMaybe (-1) $ getMaxNonemptyIndex $ scGetPathTrie sc) scs
  guard $ highestConstraintIndex < length (edgeChildren e) -- if this fails, the constraint is unsat on this edge

  newScs <- Sequence.fromList <$> mapM pecToSuspendedConstraint (unsafeGetEclasses $ edgeEcs e)
  let scs' = scs <> newScs -- append this edge's constraints onto the running list
  TermFragmentNode (edgeSymbol e) <$> imapM (\i n -> enumerateNode (descendScs i scs') n) (edgeChildren e)

-- mu a. f(g(a), g(a))
-- g(mu a. g(f(a), f(a)))

-- f(mu a. g(f(a,a)) | z, mu a. g(f(a,a)) | z)

m1 = Mu $ \r -> Node [mkEdge "f" [Node [Edge "g" [r], Edge "g" [r]]] (mkEqConstraints [[path [0, 0, 0], path [0, 0, 1]]]), Edge "f" [Node [Edge "z" [], Edge "z" []]]]
m2 = Node [Edge "f" [Mu $ \r -> Node [mkEdge "g" [Node [Edge "f" [r, r]]] (mkEqConstraints [[path [0, 0], path [0, 1]]]), Edge "z" []], Mu $ \r -> Node [mkEdge "g" [Node [Edge "f" [r, r]]] (mkEqConstraints [[path [0, 0], path [0, 1]]]), Edge "z" []]]]

---------------------
-------- Enumeration-loop control
---------------------

data ExpandableUVarResult = ExpansionStuck | ExpansionDone | ExpansionNext !UVar

-- Can speed this up with bitvectors
firstExpandableUVar :: EnumerateM ExpandableUVarResult
firstExpandableUVar = do
    values <- use uvarValues
    -- check representative uvars because only representatives are updated
    candidateMaps <- mapM (\i -> do rep <- getUVarRepresentative (intToUVar i)
                                    v <- getUVarValue rep
                                    varDepth <- use uvarMaxDepth
                                    guard $ findWithDefault 0 rep varDepth > 0
                                    case v of
                                        -- TODO: SANKALP: what does this mean for mu enumeration?
                                        -- here for the core algorithm :
                                        -- (UVarUnenumerated (Just (Mu _)) Sequence.Empty) -> return IntMap.empty                                    -- if there is a Mu node with no constraints, leave it be
                                        (UVarUnenumerated (Just (Mu _)) _             ) -> return $ IntMap.singleton (uvarToInt rep) (Any False)  -- if there is a constrained Mu node, continue unfolding till you get lasso
                                        (UVarUnenumerated (Just _)      _)              -> return $ IntMap.singleton (uvarToInt rep) (Any False)  -- if there is a normal node, keep unfolding it
                                        _                                               -> return IntMap.empty)
                              [0..(Sequence.length values - 1)]
    let candidates = IntMap.unions candidateMaps

    if IntMap.null candidates then
      return ExpansionDone
     else do
      let ruledOut = foldMap
                      (\case (UVarUnenumerated _ scs) -> foldMap
                                                             (\sc -> IntMap.singleton (uvarToInt $ scGetUVar sc) (Any True))
                                                             scs

                             _                         -> IntMap.empty)
                      values

      let unconstrainedCandidateMap = IntMap.filter (not . getAny) (ruledOut <> candidates)
      case IntMap.lookupMin unconstrainedCandidateMap of -- TODO: SANKALP: this causes enumeration of only one side
        Nothing     -> return ExpansionStuck
        Just (i, _) -> return $ ExpansionNext $ intToUVar i

enumerateOutUVar :: UVar -> EnumerateM TermFragment
enumerateOutUVar uv = do UVarUnenumerated (Just n) scs <- getUVarValue uv
                         uv' <- getUVarRepresentative uv

                         t <- case n of
                                Mu _ -> do
                                        config <- ask
                                        varDepth <- use uvarMaxDepth
                                        let depth = max (maxDepth config) (findWithDefault 0 uv' varDepth)
                                        if depth <= 0 then
                                          TermFragmentUVar <$> addUVarValue (Just n) 0 -- a variable not to be unrolled more
                                        else
                                          local (const $ initEnumerationConfig (depth - 1)) (enumerateNode scs (unfoldOuterRec n))
                                _    -> enumerateNode scs n


                         uvarValues.ix (uvarToInt uv') .= UVarEnumerated t
                         refreshReferencedUVars
                         return t

enumerateOutFirstExpandableUVar :: EnumerateM ()
enumerateOutFirstExpandableUVar = do
  muv <- firstExpandableUVar
  case muv of
    ExpansionNext uv -> void $ enumerateOutUVar uv
    ExpansionDone    -> mzero
    ExpansionStuck   -> mzero

enumerateFully :: EnumerateM ()
enumerateFully = do
  muv <- firstExpandableUVar
  case muv of
    ExpansionStuck   -> mzero
    ExpansionDone    -> return ()
    ExpansionNext uv -> enumerateOutUVar uv
                        >>
                        do
                        config <- ask
                        unless (maxDepth config <= 0) $ local (\x -> initEnumerationConfig (maxDepth x - 1)) enumerateFully

---------------------
-------- Expanding an enumerated term fragment into a term
---------------------

expandTermFrag :: TermFragment -> EnumerateM Term
expandTermFrag (TermFragmentNode s ts) = Term s <$> mapM expandTermFrag ts
expandTermFrag (TermFragmentUVar uv)   = do val <- getUVarValue uv
                                            case val of
                                              UVarEnumerated t                 -> expandTermFrag t
                                              UVarUnenumerated (Just (Mu _)) _ -> return $ Term "Mu" []
                                              _                                -> error "expandTermFrag: Non-recursive, unenumerated node encountered"

expandUVar :: UVar -> EnumerateM Term
expandUVar uv = do UVarEnumerated t <- getUVarValue uv
                   expandTermFrag t


---------------------
-------- Full enumeration
---------------------

-- rotate the arguments of a three argument function one step
rotate3 :: (t1 -> t2 -> t3 -> t4) -> t2 -> t3 -> t1 -> t4
rotate3 f x y z = f z x y

getAllTruncatedTerms :: Node -> [Term]
getAllTruncatedTerms n = map (termFragToTruncatedTerm . fst) $
                         rotate3 runEnumerateM (initEnumerationConfig defaultUnrollingDepth) (initEnumerationState n) $ do
                           enumerateFully
                           getTermFragForUVar (intToUVar 0)

getAllTerms :: Node -> [Term]
getAllTerms n = map fst $ rotate3 runEnumerateM (initEnumerationConfig defaultUnrollingDepth) (initEnumerationState n) $ do
                  enumerateFully
                  expandUVar (intToUVar 0)


-- | Inefficient enumeration
--
-- For ECTAs with 'Mu' nodes may produce an infinite list or may loop indefinitely, depending on the ECTAs. For example, for
--
-- > createMu $ \r -> Node [Edge "f" [r], Edge "a" []]
--
-- it will produce
--
-- > [ Term "a" []
-- > , Term "f" [Term "a" []]
-- > , Term "f" [Term "f" [Term "a" []]]
-- > , ...
-- > ]
--
-- This happens to work currently because non-recursive edges are interned before recursive edges.
--
-- TODO: It would be much nicer if this did fair enumeration. It would avoid the beforementioned dependency on interning
-- order, and it would give better enumeration for examples such as
--
-- > Node [Edge "h" [
-- >     createMu $ \r -> Node [Edge "f" [r], Edge "a" []]
-- >   , createMu $ \r -> Node [Edge "g" [r], Edge "b" []]
-- >   ]]
--
-- This will currently produce
--
-- > [ Term "h" [Term "a" [], Term "b" []]
-- > , Term "h" [Term "a" [], Term "g" [Term "b" []]]
-- > , Term "h" [Term "a" [], Term "g" [Term "g" [Term "b" []]]]
-- > , ..
-- > ]
--
-- where it always unfolds the /second/ argument to @h@, never the first.
naiveDenotation :: Node -> [Term]
naiveDenotation = naiveDenotationBounded Nothing

-- | set a boundary on the depth of Mu node unfolding
-- if the boundary is set to @Just n@, then @n@ levels of Mu node unfolding will be performed
-- if the boundary is set to @Nothing@, then no boundary is set and the Mu nodes will be always unfolded
naiveDenotationBounded :: Maybe Int -> Node -> [Term]
naiveDenotationBounded maxDepth node = Pipes.toList $ every (go maxDepth node)
  where
    -- | Note that this code uses the decision that f(a,a) does not satisfy the constraint 0.0=1.0 because those paths are empty.
    --   It would be equally valid to say that it does.
    ecsSatisfied :: Term -> EqConstraints -> Bool
    ecsSatisfied t ecs = all (\ps -> isJust (getPath (head ps) t) && all (\p' -> getPath (head ps) t == getPath p' t) ps)
                             (map unPathEClass $ unsafeGetEclasses ecs)

    go :: Maybe Int -> Node -> ListT Identity Term
    go _       EmptyNode = mzero
    go mbDepth n@(Mu _)  = case mbDepth of
                             Nothing            -> go Nothing (unfoldOuterRec n)
                             Just d | d <= 0    -> mzero
                                    | otherwise -> go (Just $ d - 1) (unfoldOuterRec n)
    go _       (Rec _)   = error "naiveDenotation: unexpected Rec"
    go mbDepth (Node es) = do
      e <- Select $ each es

      children <- mapM (go mbDepth) (edgeChildren e)

      let res = Term (edgeSymbol e) children
      guard $ ecsSatisfied res (edgeEcs e)
      return res
