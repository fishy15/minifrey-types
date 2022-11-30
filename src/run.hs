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
          si   = Map.fromList [("A", [])]

assignRegular = checkFunction func si
    where func = Function [] body
          body = AssignVar "x" Regular (New (Type "A"))
          si   = Map.fromList [("A", [])]

reassignIso = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A")))
                     (AssignVar "y" Iso (VarAccess "x"))
          si   = Map.fromList [("A", [])]

assignTracking = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A")))
                     (AssignVar "y" Tracking (VarAccess "x"))
          si   = Map.fromList [("A", [])]

assignIsoToRegular = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A")))
                     (AssignVar "y" Regular (VarAccess "x"))
          si   = Map.fromList [("A", [])]

transferIso = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                 (Seq (AssignVar "y" Tracking (VarAccess "x"))
                 (Seq (AssignVar "x" Iso (New (Type "A")))
                     ((AssignVar "z" Iso (VarAccess "y")))))
          si   = Map.fromList [("A", [])]

readdTrack = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                 (Seq (AssignVar "y" Tracking (VarAccess "x"))
                 (Seq (AssignVar "y" Tracking (New (Type "A")))
                     ((AssignVar "z" Tracking (VarAccess "x")))))
          si   = Map.fromList [("A", [])]

transferIsoItself = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                      (AssignVar "x" Iso (VarAccess "x"))
          si   = Map.fromList [("A", [])]

transferTrackItself = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                 (Seq (AssignVar "y" Tracking (VarAccess "x"))
                     ((AssignVar "y" Tracking (VarAccess "y"))))
          si   = Map.fromList [("A", [])]

-- Function parameter tests

singleParam = checkFunction func si
    where func = Function [("x", Type "A")] body
          body = Seq (AssignVar "y" Tracking (VarAccess "x")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

noParamToIso = checkFunction func si
    where func = Function [("x", Type "A")] body
          body = Seq (AssignVar "y" Iso (VarAccess "x")) $ 
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

noDuplicateParams = checkFunction func si
    where func = Function [("x", Type "A"), ("x", Type "A")] body
          body = AssignVar "y" Iso (New (Type "A"))
          si   = Map.fromList [("A", [])]

newRegionParam = checkFunction func si
    where func = Function [("x", Type "A")] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

returnSameRegion = checkFunction func si
    where func = Function [("x", Type "A")] body
          body = Seq (AssignVar "y" Tracking (VarAccess "x")) $
                 Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "x" Iso (VarAccess "y")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

returnSameAsParam = checkFunction func si
    where func = Function [("x", Type "A")] body
          body = VarAccess "x"
          si   = Map.fromList [("A", [])]

-- Field tests

accessIso = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                      (AssignVar "y" Tracking (FieldAccess "x" 0))
          si   = Map.fromList [("A", [(Iso, Type "B")]), ("B", [])]

accessRegular = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                      (AssignVar "y" Regular (FieldAccess "x" 0))
          si   = Map.fromList [("A", [(Regular, Type "B")]), ("B", [])]

accessRegularMultiple = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                 (Seq (AssignVar "y" Regular (FieldAccess "x" 0))
                      (AssignVar "z" Regular (FieldAccess "x" 0)))
          si   = Map.fromList [("A", [(Regular, Type "B")]), ("B", [])]

setIsoField = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                      (AssignField "x" 0 (New (Type "B")))
          si   = Map.fromList [("A", [(Iso, Type "B")]), ("B", [])]

setRegularDiffRegion = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A"))) $
                  Seq (AssignVar "y" Iso (New (Type "A"))) $
                      (AssignField "y" 0 (FieldAccess "x" 0))
          si   = Map.fromList [("A", [(Regular, Type "B")]), ("B", [])]

setRegularSameRegion = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "firstB" Regular (FieldAccess "x" 0)) $
                 Seq (AssignVar "secondB" Regular (FieldAccess "x" 1)) $
                     (AssignField "firstB" 0 (FieldAccess "secondB" 0))
          si   = Map.fromList [("A", [(Regular, Type "B"), (Regular, Type "B")]), 
                               ("B", [(Regular, Type "C")]),
                               ("C", [])]

noTrackingFields = checkFunction func si
    where func = Function [] body
          body = AssignVar "x" Iso (New (Type "A"))
          si   = Map.fromList [("A", [(Tracking, Type "B")])]

-- Sending tests

sendIso = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (Send "x") $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

useAfterSend = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (Send "x") $
                 Seq (AssignVar "y" Iso (VarAccess "x")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

returnAfterSend = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (Send "x") $
                 Seq (AssignVar "y" Iso (VarAccess "x"))
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

sendParam = checkFunction func si
    where func = Function [("x", Type "A")] body
          body = Seq (Send "x") $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

sendRegular = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "y" Regular (FieldAccess "x" 0)) $
                 Seq (Send "y") $
                     (New (Type "A"))
          si   = Map.fromList [("A", [(Regular, Type "B")]),
                               ("B", [])]

tryAccessReachable = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "y" Regular (FieldAccess "x" 0)) $
                 Seq (Send "x") $
                 Seq (AssignVar "z" Regular (VarAccess "y")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [(Regular, Type "B")]),
                               ("B", [])]

tryAccessReachableIso = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "y" Iso (FieldAccess "x" 0)) $
                 Seq (Send "x") $
                 Seq (AssignVar "z" Tracking (VarAccess "y")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [(Iso, Type "B")]),
                               ("B", [])]

tryFieldAccessSent = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (Send "x") $
                 Seq (AssignVar "y" Tracking (FieldAccess "x" 0)) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [(Iso, Type "B")]),
                               ("B", [])]

tryAccessAlias = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "y" Tracking (VarAccess "x")) $
                 Seq (Send "x") $
                 Seq (AssignVar "x" Iso (VarAccess "y")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [(Iso, Type "B")]),
                               ("B", [])]

-- Receiving tests

receiveIso = checkFunction func si
    where func = Function [] body
          body = AssignVar "x" Iso (Receive (Type "A"))
          si   = Map.fromList [("A", [])]

receiveRegular = checkFunction func si
    where func = Function [] body
          body = AssignVar "x" Regular (Receive (Type "A"))
          si   = Map.fromList [("A", [])]

tests :: [TestCase]
tests = [
    TestCase "Assign to Iso" assignIso True,
    TestCase "Assign to Regular" assignRegular False,
    TestCase "Re-assign an Iso to Iso" reassignIso False,
    TestCase "Assign Iso to Tracking" assignTracking True,
    TestCase "Assign Iso to Regular" assignIsoToRegular False,
    TestCase "Transfer Iso Ownership" transferIso True,
    TestCase "Transfer Tracking" readdTrack True,
    TestCase "Transfer Iso Ownership to Itself" transferIsoItself True,
    TestCase "Transfer Tracking to Itself" transferTrackItself True,
    TestCase "Single Function Parameter" singleParam True,
    TestCase "Parameter Treated as Iso" noParamToIso True,
    TestCase "No Duplicate Parameters" noDuplicateParams False,
    TestCase "Modify Parameter Region" newRegionParam False,
    TestCase "Return to Same Parameter Region" returnSameRegion True,
    TestCase "Return Same Region as a Parameter" returnSameAsParam False,
    TestCase "Access an Iso Struct Field" accessIso True,
    TestCase "Access a Regular Struct Field" accessRegular True,
    TestCase "Access a Regular Struct Field Multiple Times" accessRegularMultiple True,
    TestCase "Set an Iso Struct Field" setIsoField True,
    TestCase "Error on Assigning to Different Regular Regions" setRegularDiffRegion False,
    TestCase "Set on Assigning to the Same Regular Regions" setRegularSameRegion True,
    TestCase "No Fields with Tracking" noTrackingFields False,
    TestCase "Send an Iso Variable" sendIso True,
    TestCase "Access a Variable after Sending" useAfterSend False,
    TestCase "Return a Value after Sending" returnAfterSend False,
    TestCase "Send a Parameter" sendParam False,
    TestCase "Send a Regular Variable" sendRegular False,
    TestCase "Try to Access Reachable Regular Field from Sent" tryAccessReachable False,
    TestCase "Try to Access Reachable Iso Field from Sent" tryAccessReachableIso False,
    TestCase "Try to Access Field of Sent" tryFieldAccessSent False,
    TestCase "Try to Access Alias of Sent" tryAccessAlias False,
    TestCase "Receive Iso" receiveIso True,
    TestCase "Receive Regular" receiveRegular False
    ]

main :: IO ()
main = do
    mapM runTestCase tests
    let passCount = length $ filter (\(TestCase _ actual expected) -> actual == expected) tests
    let total = length tests
    putStrLn ""
    putStrLn $ show passCount ++ "/" ++ show total ++ " passed"