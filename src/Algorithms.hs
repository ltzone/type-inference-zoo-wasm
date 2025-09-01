module Algorithms (runAlgorithmInference, runAlgorithmSubtyping, runAlgorithmInferenceWithVariant, runAlgorithmSubtypingWithVariant, getAllAlgorithmMeta) where

import Lib (AlgMeta (..), InferResult (..))
import Syntax (Trm, Typ)

-- Import the algorithms we want to include
import Typing.HM.AlgW (algWMeta, runAlgW)
import Typing.HM.AlgR (algRMeta, runAlgR)
import Typing.DK.DK (dkMeta, runDK)
import Typing.Local.Contextual.Contextual (contextualMeta, runContextual)
import Typing.DK.Worklist.DK (worklistMeta, runWorklist)
import Typing.DK.Worklist.Elementary (elementaryMeta, runElementary)
import Typing.DK.Worklist.Bounded (boundedMeta, runBounded)
import Typing.DK.Worklist.IU (iuMeta, runIU)
import Subtyping.Recursive.Nominal (revisitingMeta, runNominalSubtyping)
import Subtyping.Recursive.Fsubmu (fsubmuMeta)
import Subtyping.Recursive.Distributive (distributiveMeta, runDistributiveSubtyping)

-- | Algorithm types
data AlgEntry 
  = InferAlg String AlgMeta (Trm -> InferResult)
  | SubAlg String AlgMeta (Typ -> Typ -> InferResult)

-- | Registry of all available algorithms
allAlgs :: [AlgEntry]
allAlgs = 
  [ InferAlg "W" algWMeta runAlgW
  , InferAlg "R" algRMeta runAlgR
  , InferAlg "DK" dkMeta runDK
  , InferAlg "Contextual" contextualMeta runContextual
  , InferAlg "Worklist" worklistMeta runWorklist
  , InferAlg "Elementary" elementaryMeta runElementary
  , InferAlg "Bounded" boundedMeta runBounded
  , InferAlg "IU" iuMeta runIU
  , SubAlg "Revisiting" revisitingMeta runNominalSubtyping
  , SubAlg "Distributive" distributiveMeta runDistributiveSubtyping
  , SubAlg "Fsubmu" fsubmuMeta (\_ _ -> InferResult False Nothing [] (Just "Fsubmu not implemented") False)
  ]

-- | Extract algorithm ID
algId :: AlgEntry -> String
algId (InferAlg id' _ _) = id'
algId (SubAlg id' _ _) = id'

-- | Extract algorithm metadata
algMeta :: AlgEntry -> AlgMeta
algMeta (InferAlg _ meta _) = meta
algMeta (SubAlg _ meta _) = meta

-- | Run inference for a specific algorithm
runAlgorithmInference :: String -> Trm -> InferResult
runAlgorithmInference id' tm = 
  case findAlg id' of
    Just (InferAlg _ _ runFn) -> runFn tm
    Just (SubAlg _ _ _) -> InferResult False Nothing [] (Just $ id' ++ " is a sub alg, not an infer alg") False
    Nothing -> InferResult False Nothing [] (Just $ "Unknown alg: " ++ id') False

-- | Run subtyping for a specific algorithm  
runAlgorithmSubtyping :: String -> Typ -> Typ -> InferResult
runAlgorithmSubtyping id' lty rty = 
  case findAlg id' of
    Just (SubAlg _ _ runFn) -> runFn lty rty
    Just (InferAlg _ _ _) -> InferResult False Nothing [] (Just $ id' ++ " is an infer alg, not a sub alg") False
    Nothing -> InferResult False Nothing [] (Just $ "Unknown alg: " ++ id') False

-- | Find algorithm by ID
findAlg :: String -> Maybe AlgEntry
findAlg targetId = foldr (\x acc -> if algId x == targetId then Just x else acc) Nothing allAlgs

-- | Run inference for a specific algorithm with variant (for now, ignore variant)
runAlgorithmInferenceWithVariant :: String -> Maybe String -> Trm -> InferResult
runAlgorithmInferenceWithVariant id' _variant tm = runAlgorithmInference id' tm

-- | Run subtyping for a specific algorithm with variant (for now, ignore variant)
runAlgorithmSubtypingWithVariant :: String -> Maybe String -> Typ -> Typ -> InferResult
runAlgorithmSubtypingWithVariant id' _variant lty rty = runAlgorithmSubtyping id' lty rty

-- | Get all algorithm metadata
getAllAlgorithmMeta :: [AlgMeta]
getAllAlgorithmMeta = map algMeta allAlgs
