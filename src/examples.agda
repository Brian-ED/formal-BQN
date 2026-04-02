module examples where

open import grammer
open import Data.Maybe using (just) renaming (nothing to ignore)
open import Data.List using ([])
open import Data.Sum using (_⊎_; inj₁; inj₂)

module grammerEx where
  1+1Prog : PROGRAM
  1+1Prog = Program
    ignore
    []
    (ExprAsStmt (subExprAsExpr (argAsSubExpr (DervCallAsArg
      (just (inj₁ (atomAsSubject (literalAsAtom "1"))))
      (FuncAsDerv (FuncLiteralAsFunc "+"))
      (argAsSubExpr (subjectAsArg (atomAsSubject (literalAsAtom "1"))))
    ))))
    ignore
