import qualified Data.Map as Map
import Checker
import State

data TestCase = TestCase String Bool Bool
runTestCase :: TestCase -> IO ()
runTestCase (TestCase name result expected) = putStrLn $ name ++ ": " ++ resultStr
    where resultStr = if result == expected then "pass" else "fail"

-- Assignment tests

assignIso = checkFunction func si
    where func = Function [] body
          body = AssignVar "x" Iso (New (Type "A"))
          si = Map.fromList [("A", [])]

assignRegular = checkFunction func si
    where func = Function [] body
          body = AssignVar "x" Regular (New (Type "A"))
          si = Map.fromList [("A", [])]

reassignIso = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A")))
                     (AssignVar "y" Iso (VarAccess "x"))
          si = Map.fromList [("A", [])]

assignTracking = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A")))
                     (AssignVar "y" Tracking (VarAccess "x"))
          si = Map.fromList [("A", [])]

assignIsoToRegular = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A")))
                     (AssignVar "y" Regular (VarAccess "x"))
          si = Map.fromList [("A", [])]

tests :: [TestCase]
tests = [
    TestCase "Assign to Iso" assignIso True,
    TestCase "Assign to Regular" assignRegular False,
    TestCase "Re-assign an Iso to Iso" reassignIso False,
    TestCase "Assign Iso to Tracking" assignTracking True,
    TestCase "Assign Iso to Regular" assignIsoToRegular False
    ]

main :: IO ()
main = do
    mapM runTestCase tests 
    return ()



    
