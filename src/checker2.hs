import qualified Data.Map as Map
import qualified Data.Set as Set

-- Single variables

data RefType = Iso | Tracking | Regular deriving Eq
data Type = Type String deriving (Eq, Ord)

data RefInfo = RefInfo { refOf :: RefType, typeOf :: Type, regionOf :: Region }

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
    stateVars :: Map.Map String RefInfo,
    regionCount :: Int,
    isoRegions :: Set.Set Region,
    trackedRegions :: Set.Set Region,
    structInfo :: StructInfo,
    fieldRegs :: Map.Map (Region, Type) [Region]
}

emptyState :: StructInfo -> State
emptyState si = State Map.empty 0 Set.empty Set.empty si Map.empty

-- allocates a previously unused state
allocRegion :: State -> (State, Region)
allocRegion (State vars regionCount is ts si fr) = (State vars (regionCount + 1) is ts si fr, Region regionCount)

-- gets information about the variable with the given name
-- if no such variable, returns Nothing
getVar :: String -> State -> Maybe RefInfo
getVar name state = Map.lookup name (stateVars state)

-- adds a variable to the current context
addVar :: String -> RefInfo -> State -> State
addVar name value state = state { stateVars = newVars }
    where newVars = Map.insert name value (stateVars state)

-- removes a variable from the current context
-- currently, always fails
releaseVar :: String -> State -> Maybe State
releaseVar name state = case getVar name state of
    Just ri -> Just state { stateVars = removedVar, isoRegions = removedIso, trackedRegions = removedTrack }
        where removedVar   = Map.delete name (stateVars state)
              removedIso   = Set.delete (regionOf ri) (isoRegions state)
              removedTrack = Set.delete (regionOf ri) (trackedRegions state)
    Nothing -> Just state

-- checks if the given region has an iso pointer to it
isRegIso :: Region -> State -> Bool
isRegIso r state = Set.member r (isoRegions state)

-- marks that the given region has an iso pointer to it
-- assumes that there was no such pointer earlier
addRegIso :: Region -> State -> State
addRegIso reg state = state { isoRegions = insertedIso }
    where insertedIso = Set.insert reg (isoRegions state)

-- checks if the given region is being tracked
isRegTracked :: Region -> State -> Bool
isRegTracked r state = Set.member r (trackedRegions state)

-- marks that the given region is being tracked
-- assumes that there was no such pointer earlier
addRegTracked :: Region -> State -> State
addRegTracked reg state = state { trackedRegions = insertedTrack }
    where insertedTrack = Set.insert reg (trackedRegions state)

-- given a type, gets the fields of the type based on the struct context
-- returns nothing if no struct with that name exists
getFields :: Type -> State -> Maybe [(RefType, Type)]
getFields (Type name) state = Map.lookup name (structInfo state)

-- given the region something lives in and its type,
-- finds the RefInfo for each of the fields
getFieldRefInfo :: Region -> Type -> State -> Maybe [RefInfo]
getFieldRefInfo reg t s = do
    fields <- getFields t s
    regions <- Map.lookup (reg, t) (fieldRegs s)
    return (zipWith (\(rt, t) r -> RefInfo rt t r) fields regions)

-- adds a struct to a given region
-- allocates a new region to each iso field of that struct,
-- but reuses the same region for regular fields of the struct
addStructToRegion :: Region -> Type -> State -> Maybe State
addStructToRegion reg t s = do
    fields <- getFields t s
    let (s', regList) = allocRegsForFields fields reg s
    let addedToFieldRegs = Map.insert (reg, t) regList (fieldRegs s')
    return (s' { fieldRegs = addedToFieldRegs })

allocRegsForFields :: [(RefType, Type)] -> Region -> State -> (State, [Region])
allocRegsForFields [] _ s = (s, [])
allocRegsForFields ((rt, t):fs) orig s
    | rt == Regular = (s', (orig:rest))
    | otherwise     = (sAlloc, (reg:rest))
    where (s', rest)    = allocRegsForFields fs orig s
          (sAlloc, reg) = allocRegion s'

replaceFieldReg :: Region -> Type -> Int -> Region -> State -> Maybe State
replaceFieldReg varReg t idx fieldReg s = do
    fields <- getFieldRefInfo varReg t s
    let regions = map regionOf fields
    newRegions <- replaceNthReg regions idx fieldReg
    let newFieldRegs = Map.insert (varReg, t) newRegions (fieldRegs s)
    Just s { fieldRegs = newFieldRegs }
    where replaceNthReg :: [Region] -> Int -> Region -> Maybe [Region]
          replaceNthReg [] _ _       = Nothing
          replaceNthReg (r:rs) 0 new = Just (new:rs)
          replaceNthReg (r:rs) n new = do
            rest <- replaceNthReg rs (n - 1) new
            return (r:rest) 

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
    state' <- addStructToRegion region t state
    return ((RefInfo Iso t region), state')

getType (VarAccess name) state = do
    varRef <- getVar name state
    Just (varRef, state)

getType (FieldAccess name idx) state = do 
    varRef <- getVar name state
    let (Type name) = typeOf varRef
    case (getFieldRefInfo (regionOf varRef) (typeOf varRef) state) of
        -- this type has already been allocated in the context
        Just fields -> do
            value <- accessField fields idx
            return (value, state)
        -- we need to allocate a new version in the context
        Nothing -> do
            allocState <- addStructToRegion (regionOf varRef) (typeOf varRef) state
            -- below line should not fail if we have added successfully
            fields <- getFieldRefInfo (regionOf varRef) (typeOf varRef) allocState
            value <- accessField fields idx
            return (value, allocState)

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
        Just varRef -> do
            released <- releaseVar name state
            if (regionOf value == regionOf varRef)
                then Just (value, addVar name value released)
                else Nothing
        -- create a new variable
        Nothing -> Just (value, addVar name value state)

getType (AssignField name idx expr) state = do
    (value, state) <- getType expr state
    varInfo <- getVar name state
    fields <- getFieldRefInfo (regionOf varInfo) (typeOf varInfo) state
    fieldOldRef <- accessField fields idx
    resultState <- if canSet fieldOldRef value
                then replaceFieldReg (regionOf varInfo) (typeOf varInfo) idx (regionOf value) state
                else Nothing
    return (value, resultState)

getType (Seq expr1 expr2) state = do
    -- just lose the value of the first expression
    (_, state) <- getType expr1 state
    getType expr2 state

--- Helper functions

accessField :: [RefInfo] -> Int -> Maybe RefInfo
accessField [] _ = Nothing
accessField (f:_) 0 = Just f
accessField (_:fs) n = accessField fs (n - 1)

canSet :: RefInfo -> RefInfo -> Bool
canSet old new
    | refOf old == Regular = (refOf new == Regular) && (regionOf old == regionOf new)
    | otherwise            = (refOf new == Iso) || (refOf new == Tracking)

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