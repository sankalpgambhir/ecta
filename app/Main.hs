{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.List ( nub )
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import System.IO ( hFlush, stdout )

import System.Console.CmdArgs ( Data, Typeable, cmdArgs, argPos, auto, (&=), help )

import Data.ECTA
import Data.ECTA.Internal.ECTA.Enumeration
import Data.ECTA.Term
import Data.Persistent.UnionFind
import Application.TermSearch.Evaluation
import Application.TermSearch.Type
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.ECTA.Visualization

----------------------------------------------------------

printAllEdgeSymbols :: Node -> IO ()
printAllEdgeSymbols n = print $ nub $ crush (onNormalNodes $ \(Node es) -> map edgeSymbol es) n

-- TODO: Sankalp: FIX THIS NEATLY

rotate3 f x y z = f z x y

getTermsNoOccursCheck :: Node -> [Term]
getTermsNoOccursCheck n = map (termFragToTruncatedTerm . fst) $
                          rotate3 runEnumerateM (initEnumerationConfig 5) (initEnumerationState n) $ do
                            _ <- enumerateOutUVar (intToUVar 0)
                            getTermFragForUVar    (intToUVar 0)

--------------------------------------------------------------------------------

data HPPArgs = HPPArgs { benchmark    :: String
                       , ablation     :: AblationType
                       , timeoutLimit :: Int
                       }
  deriving (Data, Typeable)

hppArgs :: HPPArgs
hppArgs = HPPArgs {
    benchmark = "" &= argPos 0
  , ablation  = Default &= help "Ablation type. choices: [default, no-reduction, no-enumeration]"
  , timeoutLimit = 300 &= help "Timeout limit in seconds"
  } &= auto


prettyTerm :: Term -> Term
prettyTerm (Term "app" ns) = Term
  "app"
  [prettyTerm (ns !! (length ns - 2)), prettyTerm (ns !! (length ns - 1))]
prettyTerm (Term "filter" ns) = prettyTerm (last ns)
prettyTerm (Term s        _ ) = Term s []

m1 = Mu $ \r -> Node [mkEdge "f" [Node [Edge "g" [r]], Node [Edge "g" [r]]] (mkEqConstraints [[path [0, 0, 0], path [0, 0, 1]]]), Edge "f" [Node [Edge "z" []], Node [Edge "z" []]]]
m2 = Node [mkEdge "f" 
            [
              Mu $ \r -> Node [mkEdge "g" [Node [Edge "f" [r, r]]] (mkEqConstraints [[path [0, 0], path [0, 1]]])
                , Edge "z" []]
            , Mu $ \r -> Node [mkEdge "g" [Node [Edge "f" [r, r]]] (mkEqConstraints [[path [0, 0], path [0, 1]]])
                , Edge "z" []]
            ] (mkEqConstraints [[path [0], path [1]]])
          ]
m3 = Node [mkEdge "f" 
            [
              Mu $ \r -> Node [mkEdge "g" [Node [Edge "f" [r, r]]] (mkEqConstraints [[path [0, 0], path [0, 1]]])
                , Edge "z" []]
            , Mu $ \r -> Node [mkEdge "g" [Node [Edge "f" [r, r]]] (mkEqConstraints [[path [0, 0], path [0, 1]]])
                , Edge "z" []]
            ] (mkEqConstraints [])
          ]

main :: IO ()
main = do
    -- query <- cmdArgs hppArgs
    -- runBenchmark (read $ benchmark query) (ablation query) (timeoutLimit query)
    -- let m1 = Mu $ \r -> Node [mkEdge "f" [Node [Edge "g" [r], Edge "g" [r]]] (mkEqConstraints [[path [0, 0, 0], path [0, 0, 1]]]), Edge "f" [Node [Edge "z" [], Edge "z" []]]]
    let mTest = Mu $ \r -> Node [Edge "z" [], Edge "f" [r]]
    print (getAllTerms mTest)
    print (intersect m1 m2)