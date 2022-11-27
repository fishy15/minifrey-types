import qualified Data.Map as Map

---------- old stuff

data TypeInfo = TIso | TTrack | TRegular deriving Eq
data RealType = Value | Struct (Map.Map String Type)
data Type = Type { typeInfo :: TypeInfo, actualType :: RealType, regionOf :: Region }
data Var = Var { varName :: String, varType :: Type }

data Expr = VarValue Var | NewValue

data Statement = Assign Var Expr

data State 

data Func = MkFunc { params :: [Var], body :: [Statement] }

checkFunction :: Func -> Bool
checkFunction f = all (\v -> typeInfo (varType v) == TIso) (params f)
    && checkBody initState body