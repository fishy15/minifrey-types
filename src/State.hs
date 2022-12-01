module State where

import qualified Data.Map as Map
import qualified Data.Set as Set

data RefType = Iso | Tracking | Regular deriving (Eq, Show)
newtype Type = Type String deriving (Eq, Ord, Show)
newtype Region = Region Int deriving (Eq, Ord, Show)

data RefInfo = RefInfo { refOf :: RefType, typeOf :: Type, regionOf :: Region } deriving Show

--- Type state

type StructInfo = Map.Map String [(RefType, Type)]

data State = State { 
    stateVars :: Map.Map String RefInfo,
    regionCount :: Int,
    isoRegions :: Set.Set Region,
    trackedRegions :: Set.Set Region,
    structInfo :: StructInfo,
    fieldRegs :: Map.Map (Region, Type) [Region],
    sentRegions :: Set.Set Region
} deriving Show

emptyState :: StructInfo -> State
emptyState si = State Map.empty 0 Set.empty Set.empty si Map.empty Set.empty

-- allocates a previously unused state
allocRegion :: State -> (State, Region)
allocRegion state = (state { regionCount = rc + 1 }, Region rc)
    where rc = regionCount state

-- gets information about the variable with the given name
-- if no such variable, returns Nothing
getVar :: String -> State -> Maybe RefInfo
getVar name state = do
    value <- Map.lookup name (stateVars state)
    if validRegion (regionOf value) state
        then return value
        else Nothing

-- adds a variable to the current context
addVar :: String -> RefInfo -> State -> State
addVar name value state = state { stateVars = newVars }
    where newVars = Map.insert name value (stateVars state)

-- removes a variable from the current context
-- currently, always fails
releaseVar :: String -> RefType -> State -> Maybe State
releaseVar name rt state = case getVar name state of
    Just ri -> Just state { stateVars = removedVar, isoRegions = removedIso, trackedRegions = removedTrack }
        where removedVar   = Map.delete name (stateVars state)
              removedIso   = if rt == Iso then Set.delete (regionOf ri) (isoRegions state) else (isoRegions state)
              removedTrack = if rt == Tracking then Set.delete (regionOf ri) (trackedRegions state) else (trackedRegions state)
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
    where allocRegsForFields :: [(RefType, Type)] -> Region -> State -> (State, [Region])
          allocRegsForFields [] _ s = (s, [])
          allocRegsForFields ((rt, t):fs) orig s
            | rt == Regular = (s', (orig:rest))
            | otherwise     = (sAlloc, (reg:rest))
                where (s', rest)    = allocRegsForFields fs orig s
                      (sAlloc, reg) = allocRegion s'

-- replaces the region corresponding to a field with another region
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

-- checks if a path of references exists from first to second register
reachable :: Region -> Region -> State -> Bool
reachable a b s = a == b || any (\r -> reachable r b s) reachableFromA
    where structsInRegion = filter (\((r, _), _) -> r == a) $ Map.assocs $ fieldRegs s
          reachableFromA  = filter (/= a) $ concat $ map snd structsInRegion

-- checks if one region is reachable from the other
eitherReachable :: Region -> Region -> State -> Bool
eitherReachable a b s = reachable a b s || reachable b a s

-- checks if the region is currently valid or not (unreachable from any of the sent regions)
validRegion :: Region -> State -> Bool
validRegion reg state = not $ any (\r -> reachable r reg state) (sentRegions state)

-- checks if the region can be sent (unreachable from any sent regions, cannot reach sent regions)
sendable :: Region -> State -> Bool
sendable reg state = not $ any (\r -> eitherReachable r reg state) invalidRegs
    where invalidRegs = Set.elems (sentRegions state)
 
-- adds the given region to the set of sent regions
addToSent :: Region -> State -> State
addToSent reg state = state { sentRegions = Set.insert reg (sentRegions state) }