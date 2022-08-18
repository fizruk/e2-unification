module E2.Rule where

import           Data.Void
import           E2.Term

-- | A rule \(t \to u\).
--
-- FIXME: missing context.
data Rule metavar a
  = Term metavar a :-> Term metavar a
  deriving (Eq, Show)

-- | Extract rule's left hand side.
ruleLHS :: Rule m Void -> Term m Void
ruleLHS (lhs :-> _rhs) = lhs

-- | Extract left hand side from a collection of rules.
rulesLHS :: [Rule m Void] -> [Term m Void]
rulesLHS = map ruleLHS

-- | Pretty-print a rewrite rule.
ppRules :: [Rule Variable Void] -> String
ppRules = unlines . map ppRule
  where
    ppRule (t :-> t') = ppTerm defaultFreshVars absurd t <> " ——» " <> ppTerm defaultFreshVars absurd t'

