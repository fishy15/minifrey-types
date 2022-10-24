import qualified Data.Map as M

main :: IO ()
main = return ()

-- define types
data Type = Int 
          | Float 
          | Function Type Type
          | Var String deriving Eq

data Expr = Literal Type 
          | VarInit 
          | Add Expr Expr 
          | Apply Expr Expr deriving Eq

-- defines which types are valid with built-in operators
-- for these operators, both types must match
addable :: Type -> Bool
addable Int = True
addable Float = True
addable _ = False

-- returns Nothing if there is a typing issue
getType :: Expr -> Maybe Type

getType (Literal t) = Just t

getType (Add e1 e2) = do
    type1 <- getType e1
    type2 <- getType e2
    if type1 == type2 && addable type1 
        then Just type1 
        else Nothing

getType (Apply f x) = do
    functionType <- getType f
    inputType <- getType x
    result functionType inputType
        where result (Function a b) x
                | a == x    = Just b
                | otherwise = Nothing
              result _ _ = Nothing

