import qualified Data.Map as Map
import qualified Data.Set as Set

-- Single variables

data RefType = Iso | Tracking | Regular deriving Eq
data Type = Type String

data RefInfo = RefInfo { refOf :: RefType, typeOf :: Type, regionOf :: Region }
data Var = Var { varName :: String, varInfo :: RefInfo }

-- Expressions

data Expression = New Type
                | VarAccess String
                | FieldAccess String Int
                | AssignVar String RefType Expression
                | AssignField String Int Expression
                | Seq Expression Expression

data Function = Function { funcParams :: [(String, Type)], funcBody :: Expression }

-- Regions
newtype Region = Region Int deriving (Eq, Ord)

--- Type state

type StructInfo = Map.Map String [(RefType, Type)] 

data State = State { 
    stateVars :: [Var],
    regionCount :: Int,
    isoRegions :: Set.Set Region,
    trackedRegions :: Set.Set Region,
    structInfo :: StructInfo,
    fieldRegs :: Map.Map (Region, Type) [Region]
}

emptyState :: StructInfo -> State
emptyState si = State [] 0 Set.empty Set.empty si Map.empty

-- allocates a previously unused state
allocRegion :: State -> (State, Region)
allocRegion (State vars regionCount is ts si fr) = (State vars (regionCount + 1) is ts si fr, Region regionCount)

-- gets information about the variable with the given name
-- if no such variable, returns Nothing
getVar :: String -> State -> Maybe Var
getVar name state = getVar' name (stateVars state)
    where getVar' :: String -> [Var] -> Maybe Var
          getVar' _ [] = Nothing
          getVar' name (v:vs) = if varName v == name then Just v else getVar' name vs

-- adds a variable to the current context
addVar :: String -> RefInfo -> State -> State
addVar name value (State vars rc ir tr si fr) = State newVars rc ir tr si fr
    where newVars = ((Var name value):newVars)

-- removes a variable from the current context
-- currently, always fails
releaseVar :: String -> State -> Maybe State
releaseVar name state = case getVar name state of
    Just _ -> Nothing
    Nothing -> Just state

-- checks if the given region has an iso pointer to it
isRegIso :: Region -> State -> Bool
isRegIso r state = Set.member r (isoRegions state)

-- marks that the given region has an iso pointer to it
-- assumes that there was no such pointer earlier
addRegIso :: Region -> State -> State
addRegIso r (State vs rc ir tr si fr) = State vs rc (Set.insert r ir) tr si fr

-- checks if the given region is being tracked
isRegTracked :: Region -> State -> Bool
isRegTracked r state = Set.member r (trackedRegions state)

-- marks that the given region is being tracked
-- assumes that there was no such pointer earlier
addRegTracked :: Region -> State -> State
addRegTracked r (State vs rc ir tr si fr) = State vs rc ir (Set.insert r tr) si fr

-- given a type, gets the fields of the type based on the struct context
-- returns nothing if no struct with that name exists
getFields :: Type -> State -> Maybe [(RefType, Type)]
getFields (Type name) state = Map.lookup name (structInfo state)

-- adds a struct to a given region
-- allocates a new region to each iso field of that struct,
-- but reuses the same region for regular fields of the struct
addStruct :: Region -> Type -> State -> Maybe State
addStruct reg t state  = do
    fields <- getFields t state
    let ((State vs rc ir tr si fr), fieldRegs) = allocRegsForFields fields reg state
    return (State vs rc ir tr si (added fieldRegs fr)) 
    where added regs fr = Map.insert (reg, t) regs fr

          allocRegsForFields :: [(RefType, Type)] -> Region -> State -> (State, [Region])
          allocRegsForFields [] _ s = (s, [])
          allocRegsForFields ((rt, t):fs) orig s
            | rt == Regular = (s', (orig:rest))
            | otherwise = (sAlloc, (reg:rest))
            where (s', rest) = allocRegsForFields fs orig s
                  (sAlloc, reg) = allocRegion s'

-- Checking

checkFunction :: Function -> StructInfo -> Bool

checkFunction (Function params body) si = distinctNames && validBody
    where distinctNames = distinctNames' params
          distinctNames' :: [(String, Type)] -> Bool
          distinctNames' [] = True
          distinctNames' ((name, _):ps) = null (filter (\(n, _) -> n == name) ps) && distinctNames' ps

          initState = makeState params (emptyState si)
          makeState :: [(String, Type)] -> State -> State
          makeState [] s = s
          makeState ((name, t):ps) s = makeState ps (addVar name (RefInfo Iso t reg) s')
            where (s', reg) = allocRegion s

          validBody = case (getType body initState) of
            Just _ -> True
            Nothing -> False

getType :: Expression -> State -> Maybe (RefInfo, State)

-- just gives Value to construct a value since types are not being checked
getType (New t) s = do 
    let (state, region) = allocRegion s
    state' <- addStruct region t state
    return ((RefInfo Iso t region), state')

getType (VarAccess name) state = do
    var <- getVar name state
    Just ((varInfo var), state)

getType (FieldAccess name idx) state = do 
    var <- getVar name state
    let (Type name) = typeOf (varInfo var)
    fields <- Map.lookup name (structInfo state)
    accessField fields idx state
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

getType (Seq expr1 expr2) state = do
    -- just lose the value of the first expression
    (_, state) <- getType expr1 state
    getType expr2 state

--- Helper functions

-- Takes a RefInfo and produces another reference to it
-- createNewRef :: RefInfo -> State -> Maybe (RefInfo, State)

-- if the reference is currently being tracked, then we cannot make another reference
-- otherwise, we make add the region to the tracking set and return a reference
-- createNewRef (RefInfo Iso t r) (State vs rc isIso isTracked si)
--     = if Set.member r isTracked 
--         then Nothing 
--         else Just ((RefInfo Tracking t r), (State vs rc isIso isTracked' si))
--     where isTracked' = Set.insert r isTracked

-- cannot have a tracking in a struct field
-- createNewRef (RefInfo Tracking t r) s = Nothing

-- just returns a direct reference in the same region
-- createNewRef (RefInfo Regular t r) s = Just ((RefInfo Regular t r), s)