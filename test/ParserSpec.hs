module ParserSpec where

import Parsing
import Test.Hspec
import VampExp
import Constraints

-- Tests order of operations parsing
oooSpec :: Spec
oooSpec = describe "Operations Parser" $ do
    it "parses single number" $ 
         runInitParser expr "42" `shouldBe` Right (ConstantE 42)
    it "parses simple exponent" $ 
         runInitParser expr "2 ^ 3" `shouldBe` Right (Infix Exponentiate (ConstantE 2) (ConstantE 3))
    it "parses simple multiplication" $ 
         runInitParser expr "5* 7" `shouldBe` Right (Infix Multiply (ConstantE 5) (ConstantE 7))
    it "parses simple addition" $ 
         runInitParser expr "1 + 2" `shouldBe` Right (Infix Add (ConstantE 1) (ConstantE 2))
    it "parses negation" $ 
         runInitParser expr "1 - - 2" `shouldBe` Right (Infix Subtract (ConstantE 1) (Negate (ConstantE 2)))
    it "respects order of operations" $ 
             runInitParser expr "2 + 3 * 4" `shouldBe` Right (Infix Add (ConstantE 2) (Infix Multiply (ConstantE 3) (ConstantE 4)))
    it "respects order of operations 2" $ 
             runInitParser expr "2 * 3 ^ 4" `shouldBe` Right (Infix Multiply (ConstantE 2) (Infix Exponentiate (ConstantE 3) (ConstantE 4)))
    it "respects parens" $ 
            runInitParser expr "(2 + 3) * 4" `shouldBe` Right (Infix Multiply (Infix Add (ConstantE 2) (ConstantE 3)) (ConstantE 4))
    it "respects order of operations 3 and variable naming" $ 
             runInitParser expr "x = 1 + y & 3 * 5 ^ 7 = 15 + x" `shouldBe` 
        Right (Infix And 
                  (Infix Equal (VarExpr (Variable (Just "x") 0)) (Infix Add (ConstantE 1) (VarExpr (Variable (Just "y") 1))))
                  (Infix Equal 
                        (Infix Multiply (ConstantE 3) (Infix Exponentiate (ConstantE 5) (ConstantE 7)))
                        (Infix Add (ConstantE 15) (VarExpr (Variable (Just "x") 0))))
                )
    it "Check that arith ops don't prevent futher expressions" $ 
        runInitParser expr "(1 1) + 2" `shouldBe` 
        Right (Infix Add 
                  (Application (ConstantE 1) (ConstantE 1))
                  (ConstantE 2)
                )

intSpec :: Spec
intSpec = describe "Integer Parser" $ do
    it "parses single number" $ 
         runInitParser integerLiteral "15" `shouldBe` Right 15
    it "parses hexadecimal number 0xff as 255" $ 
        runInitParser integerLiteral "0xff" `shouldBe` Right 255
    it "parses octal number 0o77 as 63" $ 
        runInitParser integerLiteral "0o77" `shouldBe` Right 63
    it "parses binary number 0b1101 as 13" $ 
        runInitParser integerLiteral "0b1101" `shouldBe` Right 13
    it "parses decimal number 1234 as 1234" $ 
        runInitParser integerLiteral "1234" `shouldBe` Right 1234

exprSpec :: Spec
exprSpec = describe "Expression Parser" $ do
    it "Parsing pair" $ 
         runInitParser expr "(1 , 2)" `shouldBe` Right (PairE (ConstantE 1) (ConstantE 2))
    it "Parsing triple" $ 
         runInitParser expr "(1, 2 ,3)" `shouldBe` Right (PairE (ConstantE 1) (PairE (ConstantE 2) (ConstantE 3)))
    it "Parsing quadruple" $ 
         runInitParser expr "(1,2,3 ,4 )" `shouldBe` Right (PairE (ConstantE 1) (PairE (ConstantE 2) (PairE (ConstantE 3) (ConstantE 4))))
    it "nested pair" $ 
         runInitParser expr "(1, (2, 3, 4), 5, (6, 7))" `shouldBe` Right (PairE (ConstantE 1) (PairE (PairE (ConstantE 2) (PairE (ConstantE 3) (ConstantE 4))) (PairE (ConstantE 5) (PairE (ConstantE 6) (ConstantE 7)))))
    it "list" $ 
         runInitParser expr "1 : 2 :3:[]" `shouldBe` Right (ConsE (ConstantE 1) (ConsE (ConstantE 2) (ConsE (ConstantE 3) NilE)))
    it "list in pair" $
        runInitParser expr "(1, (2:3:4 ), 5, 6)" `shouldBe` Right (PairE (ConstantE 1) (PairE (ConsE (ConstantE 2) (ConsE (ConstantE 3) (ConstantE 4))) (PairE (ConstantE 5) (ConstantE 6))))
    it "arith in pair" $
        runInitParser expr "(1 + 2, 5 * 6)" `shouldBe` Right (PairE (Infix Add (ConstantE 1) (ConstantE 2)) (Infix Multiply (ConstantE 5) (ConstantE 6)) )
    it "arith in list" $
        runInitParser expr "(1 + 2 : 5 * 6)" `shouldBe` Right (ConsE (Infix Add (ConstantE 1) (ConstantE 2)) (Infix Multiply (ConstantE 5) (ConstantE 6)) )

parserSpec :: Spec
parserSpec = describe "Full Parser Test" $ do
    intSpec
    oooSpec
    exprSpec