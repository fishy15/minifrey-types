import qualified Data.Map as Map
import qualified Data.Set as Set

-- Single variables

data RefType = Iso | Tracking | Regular deriving Eq
data Type = Value | StructPtr [RefInfo]

data RefInfo = RefInfo { refOf :: RefType, typeOf :: Type, regionOf :: Region }
data Var = Var { varName :: String, varInfo :: RefInfo }

-- Expressions

data Expression = Constant
                | FieldAccess String Int
                | AssignVar Var Expression
                | AssignField Var Int Expression
                | Seq Expression Expression
                | Skip

getVar :: State -> String -> Maybe Var
getVar (State vs _ _ _) name = getVar' vs name
    where getVar' :: [Var] -> String -> Maybe Var
          getVar' [] _ = Nothing
          getVar' (v:vs) name = if varName v == name then Just v else getVar' vs name

-- Regions
newtype Region = Region Int deriving (Eq, Ord)

--- Type state
data State = State { 
    stateVars :: [Var],
    regionCount :: Int,
    isoRegions :: (Set.Set Region),
    trackedRegions :: (Set.Set Region)
}

allocRegion :: State -> (State, Region)
allocRegion (State vars regionCount is ts) = (State vars (regionCount + 1) is ts, Region regionCount)

-- Checking

getType :: Expression -> State -> Maybe (RefInfo, State)

getType Constant s = Just ((RefInfo Regular Value region'), state')
    where (state', region') = allocRegion s

getType (FieldAccess name idx) state = do 
    var <- getVar state name
    case typeOf (varInfo var) of
        Value -> Nothing
        StructPtr fields -> accessField fields idx state
    where accessField :: [RefInfo] -> Int -> State -> Maybe (RefInfo, State)
          accessField [] _ _ = Nothing
          accessField (f:_) 0 s = convertRefInfo f s
          accessField (_:fs) n s = accessField fs (n - 1) s

          convertRefInfo :: RefInfo -> State -> Maybe (RefInfo, State)

          -- if the reference is currently being tracked, then we cannot make another reference
          -- otherwise, we make add the region to the tracking set and return a reference
          convertRefInfo (RefInfo Iso t r) (State vs rc isIso isTracked)
            = if Set.member r isTracked 
                then Nothing 
                else Just ((RefInfo Tracking t r), (State vs rc isIso isTracked'))
            where isTracked' = Set.insert r isTracked

          -- cannot have a tracking in a struct field
          convertRefInfo (RefInfo Tracking t r) s = Nothing

          -- just returns a direct reference in the same region
          convertRefInfo (RefInfo Regular t r) s = Just ((RefInfo Regular t r), s)

getType (AssignVar var expr) state = do
    (value, state') <- getType expr state
    Nothing

-- getType (FieldAccess name (RefInfo Iso _ _)) state = do
--     var <- getVar state name
--     Nothing