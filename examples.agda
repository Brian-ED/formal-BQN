module examples where

open import grammer
open import Data.Maybe using (just) renaming (nothing to ignore)
open import Data.List using ([])
open import Data.Sum using (_⊎_; inj₁; inj₂)

module grammerEx where
  example : PROGRAM
  example = Program
    ignore
    []
    (ExprAsStmt (subExprAsExpr (argToSubExpr (DervCallToArg
      (just (inj₁ (atomToSubject (literalAsAtom "1"))))
      (FuncToDerv (FuncLiteralAsFunc "+"))
      (argToSubExpr (subjectToArg (atomToSubject (literalAsAtom "1"))))
    ))))
    ignore
