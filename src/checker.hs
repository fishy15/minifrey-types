module Checker where

import State

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
    state <- releaseVar name Iso state
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
    state <- releaseVar name Tracking state
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
    if refOf value == Regular
        then case (getVar name state) of
                -- need to replace an already existing variable
                Just varRef -> do
                    released <- releaseVar name Regular state
                    if (regionOf value == regionOf varRef)
                        then Just (value, addVar name value released)
                        else Nothing
                -- create a new variable
                Nothing -> Just (value, addVar name value state)
        else Nothing

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