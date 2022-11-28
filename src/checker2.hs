import qualified Data.Map as Map
import qualified Data.Set as Set

-- Single variables

data RefType = Iso | Tracking | Regular deriving Eq
data Type = Value | StructPtr [RefInfo]

data RefInfo = RefInfo { refOf :: RefType, typeOf :: Type, regionOf :: Region }
data Var = Var { varName :: String, varInfo :: RefInfo }

-- Expressions

data Expression = Constant
                | VarAccess String
                | FieldAccess String Int
                | AssignVar String RefType Expression
                | AssignField String Int Expression
                | Seq Expression Expression
                | Skip

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

getVar :: String -> State -> Maybe Var
getVar name (State vs _ _ _) = getVar' name vs
    where getVar' :: String -> [Var] -> Maybe Var
          getVar' _ [] = Nothing
          getVar' name (v:vs) = if varName v == name then Just v else getVar' name vs

addVar :: String -> RefInfo -> State -> State
addVar name value (State vars rc ir tr) = State newVars rc ir tr
    where newVars = ((Var name value):newVars)

releaseVar :: String -> State -> Maybe State
releaseVar name state = case getVar name state of
    Just _ -> Nothing
    Nothing -> Just state

isRegIso :: Region -> State -> Bool
isRegIso r (State _ _ ir _) = Set.member r ir

addRegIso :: Region -> State -> State
addRegIso r (State vs rc ir tr) = State vs rc (Set.insert r ir) tr

isRegTracked :: Region -> State -> Bool
isRegTracked r (State _ _ _ tr) = Set.member r tr

addRegTracked :: Region -> State -> State
addRegTracked r (State vs rc ir tr) = State vs rc ir (Set.insert r tr)

-- Checking

getType :: Expression -> State -> Maybe (RefInfo, State)

getType Constant s = Just ((RefInfo Regular Value region'), state')
    where (state', region') = allocRegion s

getType (VarAccess name) state = do
    var <- getVar name state
    Just ((varInfo var), state)

getType (FieldAccess name idx) state = do 
    var <- getVar name state
    case typeOf (varInfo var) of
        Value -> Nothing
        StructPtr fields -> accessField fields idx state
    where accessField :: [RefInfo] -> Int -> State -> Maybe (RefInfo, State)
          accessField [] _ _ = Nothing
          accessField (f:_) 0 s = Just (f, s) 
          accessField (_:fs) n s = accessField fs (n - 1) s

getType (AssignVar name Iso expr) state = do
    (value, state) <- getType expr state
    state <- releaseVar name state
    case (refOf value) of
        Iso -> handleUnique name value state
        Tracking -> handleUnique name value state
        Regular -> Nothing
        where handleUnique :: String -> RefInfo -> State -> Maybe (RefInfo, State)
              handleUnique name value state = if isRegIso reg state
                                                then Nothing
                                                else Just (value, addVar name value addedState)
                where reg = regionOf value
                      addedState = addRegIso reg state

getType (AssignVar name Tracking expr) state = do
    (value, state) <- getType expr state
    state <- releaseVar name state
    case (refOf value) of
        Iso -> handleUnique name value state
        Tracking -> handleUnique name value state
        Regular -> Nothing
        where handleUnique :: String -> RefInfo -> State -> Maybe (RefInfo, State)
              handleUnique name value state = if isRegTracked reg state
                                                then Nothing
                                                else Just (value, addVar name value addedState)
                where reg = regionOf value
                      addedState = addRegTracked reg state

getType (AssignVar name Regular expr) state = do
    (value, state) <- getType expr state
    case (getVar name state) of
        -- need to replace an already existing variable
        Just var -> do
            released <- releaseVar name state
            if (regionOf value == regionOf (varInfo var))
                then Just (value, addVar name value released)
                else Nothing
        -- create a new variable
        Nothing -> Just (value, addVar name value state)

--- Helper functions

-- Takes a RefInfo and produces another reference to it
createNewRef :: RefInfo -> State -> Maybe (RefInfo, State)

-- if the reference is currently being tracked, then we cannot make another reference
-- otherwise, we make add the region to the tracking set and return a reference
createNewRef (RefInfo Iso t r) (State vs rc isIso isTracked)
    = if Set.member r isTracked 
        then Nothing 
        else Just ((RefInfo Tracking t r), (State vs rc isIso isTracked'))
    where isTracked' = Set.insert r isTracked

-- cannot have a tracking in a struct field
createNewRef (RefInfo Tracking t r) s = Nothing

-- just returns a direct reference in the same region
createNewRef (RefInfo Regular t r) s = Just ((RefInfo Regular t r), s)