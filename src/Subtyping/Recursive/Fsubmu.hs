module Subtyping.Recursive.Fsubmu (fsubmuMeta) where

import Lib (AlgMeta (..), Paper (..), Rule (..))

-- Fsubmu algorithm metadata
fsubmuMeta :: AlgMeta
fsubmuMeta = AlgMeta
  { metaId = "Fsubmu"
  , metaName = "Recursive Subtyping for All"
  , metaLabels = ["Subtyping", "System Fsub", "Recursive Types"]
  , metaViewMode = "tree"
  , metaMode = "subtyping"
  , metaPaper = Paper
    { paperTitle = "Recursive Subtyping for All"
    , paperAuthors = ["Litao Zhou", "Yaoda Zhou", "Qianyong Wan", "Bruno C. d. S. Oliveira"]
    , paperYear = 2025
    , paperUrl = "https://i.cs.hku.hk/~bruno/papers/jfp25.pdf"
    }
  , metaVariants = Nothing
  , metaDefaultVariant = Nothing
  , metaRules = [Rule "placeholder" "TBA" [] "\\text{Rules will be added soon.}" Nothing Nothing]
  , metaRuleGroups = Nothing
  , metaVariantRules = Nothing
  }
