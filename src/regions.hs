import qualified Data.Map as Map

newtype Region = [Var] deriving Eq
newtype RegionData = [Region]

-- Finds which region a variable belongs to
findRegion :: Var -> Maybe Region
findRegion v [] = Nothing
findRegion v (r : rest) = if v `elem` r then r else findRegion v rest
