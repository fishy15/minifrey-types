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
                     (AssignVar "y" Iso (AccessVar "x"))
          si   = Map.fromList [("A", [])]

assignTracking = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A")))
                     (AssignVar "y" Tracking (AccessVar "x"))
          si   = Map.fromList [("A", [])]

assignIsoToRegular = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A")))
                     (AssignVar "y" Regular (AccessVar "x"))
          si   = Map.fromList [("A", [])]

transferIso = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                 (Seq (AssignVar "y" Tracking (AccessVar "x"))
                 (Seq (AssignVar "x" Iso (New (Type "A")))
                     ((AssignVar "z" Iso (AccessVar "y")))))
          si   = Map.fromList [("A", [])]

readdTrack = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                 (Seq (AssignVar "y" Tracking (AccessVar "x"))
                 (Seq (AssignVar "y" Tracking (New (Type "A")))
                     ((AssignVar "z" Tracking (AccessVar "x")))))
          si   = Map.fromList [("A", [])]

transferIsoItself = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                      (AssignVar "x" Iso (AccessVar "x"))
          si   = Map.fromList [("A", [])]

transferTrackItself = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                 (Seq (AssignVar "y" Tracking (AccessVar "x"))
                     ((AssignVar "y" Tracking (AccessVar "y"))))
          si   = Map.fromList [("A", [])]

-- Function parameter tests

singleParam = checkFunction func si
    where func = Function [("x", Type "A")] body
          body = Seq (AssignVar "y" Tracking (AccessVar "x")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

noParamToIso = checkFunction func si
    where func = Function [("x", Type "A")] body
          body = Seq (AssignVar "y" Iso (AccessVar "x")) $ 
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
          body = Seq (AssignVar "y" Tracking (AccessVar "x")) $
                 Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "x" Iso (AccessVar "y")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

returnSameAsParam = checkFunction func si
    where func = Function [("x", Type "A")] body
          body = AccessVar "x"
          si   = Map.fromList [("A", [])]

-- Field tests

accessIso = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                      (AssignVar "y" Tracking (AccessField "x" 0))
          si   = Map.fromList [("A", [(Iso, Type "B")]), ("B", [])]

accessRegular = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                      (AssignVar "y" Regular (AccessField "x" 0))
          si   = Map.fromList [("A", [(Regular, Type "B")]), ("B", [])]

accessRegularMultiple = checkFunction func si
    where func = Function [] body
          body =  Seq (AssignVar "x" Iso (New (Type "A")))
                 (Seq (AssignVar "y" Regular (AccessField "x" 0))
                      (AssignVar "z" Regular (AccessField "x" 0)))
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
                      (AssignField "y" 0 (AccessField "x" 0))
          si   = Map.fromList [("A", [(Regular, Type "B")]), ("B", [])]

setRegularSameRegion = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "firstB" Regular (AccessField "x" 0)) $
                 Seq (AssignVar "secondB" Regular (AccessField "x" 1)) $
                     (AssignField "firstB" 0 (AccessField "secondB" 0))
          si   = Map.fromList [("A", [(Regular, Type "B"), (Regular, Type "B")]), 
                               ("B", [(Regular, Type "C")]),
                               ("C", [])]

noTrackingFields = checkFunction func si
    where func = Function [] body
          body = AssignVar "x" Iso (New (Type "A"))
          si   = Map.fromList [("A", [(Tracking, Type "B")])]

-- Function call tests

noParams = checkFunction func si
    where func = Function [] body
          body = FuncCall [] (Type "A")
          si   = Map.fromList [("A", [])]

twoParams = checkFunction func si
    where func = Function [] body
          body = FuncCall [New (Type "A"), New (Type "A")] (Type "A")
          si   = Map.fromList [("A", [])]

sameRegParams = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                     (FuncCall [(AccessField "x" 0), (AccessField "x" 1)]) (Type "A")
          si   = Map.fromList [("A", [(Regular, Type "B"), (Regular, Type "B")]),
                               ("B", [])]

-- Sending tests

sendIso = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (Send (AccessVar "x")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

useAfterSend = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (Send (AccessVar "x")) $
                 Seq (AssignVar "y" Iso (AccessVar "x")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

returnAfterSend = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (Send (AccessVar "x")) $
                 Seq (AssignVar "y" Iso (AccessVar "x"))
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

sendParam = checkFunction func si
    where func = Function [("x", Type "A")] body
          body = Seq (Send (AccessVar "x")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

sendRegular = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "y" Regular (AccessField "x" 0)) $
                 Seq (Send (AccessVar "y")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [(Regular, Type "B")]),
                               ("B", [])]

tryAccessReachable = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "y" Regular (AccessField "x" 0)) $
                 Seq (Send (AccessVar "x")) $
                 Seq (AssignVar "z" Regular (AccessVar "y")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [(Regular, Type "B")]),
                               ("B", [])]

tryAccessReachableIso = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "y" Iso (AccessField "x" 0)) $
                 Seq (Send (AccessVar "x")) $
                 Seq (AssignVar "z" Tracking (AccessVar "y")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [(Iso, Type "B")]),
                               ("B", [])]

tryAccessFieldSent = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (Send (AccessVar "x")) $
                 Seq (AssignVar "y" Tracking (AccessField "x" 0)) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [(Iso, Type "B")]),
                               ("B", [])]

tryAccessAlias = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "y" Tracking (AccessVar "x")) $
                 Seq (Send (AccessVar "x")) $
                 Seq (AssignVar "x" Iso (AccessVar "y")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [(Iso, Type "B")]),
                               ("B", [])]

sendTwice = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (Send (AccessVar "x")) $
                 Seq (Send (AccessVar "x")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [])]

sendField = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "y" Regular (AccessField "x" 0)) $
                 Seq (Send (AccessVar "y")) $
                 Seq (AssignVar "x" Iso (AccessVar "x")) $
                     (New (Type "A"))
          si   = Map.fromList [("A", [(Regular, Type "B")]),
                               ("B", [])]

sendNotCompleteValid = checkFunction func si
    where func = Function [] body
          body = Seq (AssignVar "x" Iso (New (Type "A"))) $
                 Seq (AssignVar "y" Iso (AccessField "x" 0)) $
                 Seq (Send (AccessVar "y")) $
                     (Send (AccessVar "x"))
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

-- larger example programs

-- corresponds to the following program (examples/buildTree.txt):
-- this should succeed
-- buildTree() {
--     root = new Tree;
--     left = recv<Tree>();
--     right = recv<Tree>();
--     root.left = left;
--     root.right = right;
--     send(root)
-- }

buildTree = checkFunction func si
    where func = Function [] body
          body = Seq ((AssignVar "root" Iso (New (Type "Tree")))) $
                 Seq ((AssignVar "left" Tracking (Receive (Type "Tree")))) $
                 Seq ((AssignVar "right" Tracking (Receive (Type "Tree")))) $
                 Seq ((AssignField "root" 0 (AccessVar "left"))) $
                 Seq ((AssignField "root" 1 (AccessVar "right"))) $
                     (Send (AccessVar "root"))
          si   = Map.fromList [("Tree", [(Iso, Type "Tree"), (Iso, Type "Tree")])]

-- corresponds to the following program (examples/findMinimumIncorrect.txt):
-- this should fail
-- buildAndFindMin() {
--     root = new Tree;
--     left = recv<Tree>();
--     right = recv<Tree>();
--     root.left = left;
--     root.right = right;
--     send(root);
--     findMin(root.left)
-- }

buildAndFindMin = checkFunction func si
    where func = Function [] body
          body = Seq ((AssignVar "root" Iso (New (Type "Tree")))) $
                 Seq ((AssignVar "left" Tracking (Receive (Type "Tree")))) $
                 Seq ((AssignVar "right" Tracking (Receive (Type "Tree")))) $
                 Seq ((AssignField "root" 0 (AccessVar "left"))) $
                 Seq ((AssignField "root" 1 (AccessVar "right"))) $
                 Seq (Send (AccessVar "root")) $
                     (FuncCall [AccessField "root" 0] (Type "Tree"))
          si   = Map.fromList [("Tree", [(Iso, Type "Tree"), (Iso, Type "Tree")])]

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
    TestCase "Call a Function with No Parameters" noParams True,
    TestCase "Call a Function with Two Parameters" twoParams True,
    TestCase "Call a Function with Two Parameters in the Same Region" sameRegParams False,
    TestCase "Send an Iso Variable" sendIso True,
    TestCase "Access a Variable after Sending" useAfterSend False,
    TestCase "Return a Value after Sending" returnAfterSend False,
    TestCase "Send a Parameter" sendParam False,
    TestCase "Send a Regular Variable" sendRegular True,
    TestCase "Try to Access Reachable Regular Field from Sent" tryAccessReachable False,
    TestCase "Try to Access Reachable Iso Field from Sent" tryAccessReachableIso False,
    TestCase "Try to Access Field of Sent" tryAccessFieldSent False,
    TestCase "Try to Access Alias of Sent" tryAccessAlias False,
    TestCase "Try Sending the Same Variable Twice" sendTwice False,
    TestCase "Send Field of an Iso Struct" sendField False,
    TestCase "Send a Struct With Invalid Fields" sendNotCompleteValid False,
    TestCase "Receive Iso" receiveIso True,
    TestCase "Receive Regular" receiveRegular False,
    TestCase "Build Tree" buildTree True,
    TestCase "Build and Find Min" buildAndFindMin False
    ]

main :: IO ()
main = do
    mapM runTestCase tests
    let passCount = length $ filter (\(TestCase _ actual expected) -> actual == expected) tests
    let total = length tests
    putStrLn ""
    putStrLn $ show passCount ++ "/" ++ show total ++ " passed"