import qualified Data.Map as Map
import Checker
import State

data TestCase = TestCase String Bool Bool
runTestCase :: TestCase -> IO ()
runTestCase (TestCase name result expected) = putStrLn $ name ++ ": " ++ resultStr
    where resultStr = if result == expected then "pass" else "fail"

assignIso :: Bool
assignIso = checkFunction func si
    where func = Function [] body1
          body1 = AssignVar "x" Iso (New (Type "A"))
          si = Map.fromList [("A", [])]

assignRegular :: Bool
assignRegular = checkFunction func si
    where func = Function [] body1
          body1 = AssignVar "x" Regular (New (Type "A"))
          si = Map.fromList [("A", [])]

tests :: [TestCase]
tests = [
    TestCase "Assign to Iso" assignIso True,
    TestCase "Assign to Regular" assignRegular False
    ]

main :: IO ()
main = do
    mapM runTestCase tests 
    return ()



    
