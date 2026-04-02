module grammer where

open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_)
open import Data.String using () renaming (String to Var)
open import Data.Sum using (_⊎_)
open import Data.Bool using (Bool)

data PROGRAM   : Set
data STMT      : Set
data EXPR      : Set
data EXPORT    : Set
data ANY       : Set
data -mod2-    : Set
data -mod1     : Set
data Func      : Set
data atom      : Set
data nothing   : Set
data array     : Set
data subject   : Set
data ASGN      : Set
data -m2Expr-  : Set
data -m1Expr   : Set
data Derv      : Set
data Operand   : Set
data Fork      : Set
data Train     : Set
data FuncExpr  : Set
data arg       : Set
data noExpr    : Set
data subExpr   : Set
data NAME      : Set
data LHS-SUB   : Set
data LHS-ANY   : Set
data LHS-ATOM  : Set
data LHS-ELT   : Set
data LHS-ENTRY : Set
data lhsStr    : Set
data lhsList   : Set
data lhsArray  : Set
data lhsComp   : Set
data lhs       : Set
data headW     : Set
data headX     : Set
data HeadF     : Set
data HeadG     : Set
data FuncLab   : Set
data Mod1Lab   : Set
data Mod2Lab   : Set
data FuncName  : Set
data Mod1Name  : Set
data Mod2Name  : Set
data LABEL     : Set
data IMM-HEAD  : Set
data ARG-HEAD  : Set
data BODY      : Set
data I-CASE    : Set
data A-CASE    : Set
data S-CASE    : Set
data IMM-BLK   : Set
data ARG-BLK   : Set
data blSub     : Set
data BlFunc    : Set
data -blMod1   : Set
data -blMod2-  : Set


data ⋄ : Set where
  ⋄ₗ : ⋄

data PROGRAM where
  Program : Maybe ⋄ → List ( STMT × ⋄ ) → STMT → Maybe ⋄ → PROGRAM

data STMT where
  ExprAsStmt : EXPR → STMT
  NoExprAsStmt : noExpr → STMT
  ExportAsStmt : EXPORT → STMT

data EXPR where
  subExprAsExpr : subExpr → EXPR
  FuncExprAsExpr : FuncExpr → EXPR
  -m1ExprAsExpr : -m1Expr → EXPR
  -m2-ExprAsExpr : -m2Expr- → EXPR

data EXPORT where
  _⇐ : (Maybe LHS-ELT) → EXPORT

data ANY where
  case1 : atom → ANY
  case2 : Func → ANY
  case3 : -mod1 → ANY
  case4 : -mod2- → ANY

data -mod2- where
  dot : Maybe atom → Var → -mod2-
  case2 : Var → -mod2-
  ⟨_⟩₂ : -m2Expr- → -mod2-
  case4 : -blMod2- → -mod2-

data -mod1 where
  case1• : Maybe atom → Var → -mod1
  case2 : Var → -mod1
  ⟨case3⟩ : -m1Expr → -mod1
  case4 : -blMod1 → -mod1

data Func where
  VarAsFunc : Maybe atom → Var → Func
  FuncLiteralAsFunc : Var → Func
  EnclosedFuncExprAsFunc : FuncExpr → Func
  BlockLiteralAsFunc : BlFunc → Func

data atom where
  varAsAtom : Maybe atom → Var → atom
  literalAsAtom : Var → atom
  enclosedSubExprAsAtom : subExpr → atom
  blockSubExprAsAtom : blSub → atom
  arrayAsAtom : array → atom

data nothing where
  · : nothing
  case2 : noExpr → nothing

data array where
  ⟨_⟩ : Maybe ⋄ → Maybe ((List (EXPR × ⋄)) × EXPR × (Maybe ⋄)) → array
  [_] : Maybe ⋄ → List(EXPR × ⋄) → EXPR → Maybe ⋄ → array

data subject where
  atomAsSubject : atom → subject
  _‿_‿_ : ANY → ANY → List ANY → subject

data ASGN where
  ← : ASGN
  ⇐ : ASGN
  ↩ : ASGN

data -m2Expr- where
  case1 : -mod2- → -m2Expr-
  case2 : Var → ASGN → -m2Expr- → -m2Expr-

data -m1Expr where
  case1 : -mod1 → -m1Expr
  case2 : Var → ASGN → -m1Expr → -m1Expr

data Derv where
  FuncAsDerv : Func → Derv
  -mod1CallAsDerv : Operand → -mod1 → Derv
  -mod2-CallAsDerv : Operand → -mod2- → ( subject ⊎ Func ) → Derv

data Operand where
  case1 : subject → Operand
  case2 : Derv → Operand

data Fork where
  case1 : Derv → Fork
  3-train : Operand → Derv → Fork → Fork
  2-train : nothing → Derv → Fork → Fork

data Train where
  case1 : Fork → Train
  2-train : Derv → Fork → Train

data FuncExpr where
  case1 : Train → FuncExpr
  case2 : Var → ASGN → FuncExpr → FuncExpr

data arg where
  subjectAsArg : subject → arg
  DervCallAsArg : Maybe (subject ⊎ nothing) → Derv → subExpr → arg

data noExpr where
  case1 : nothing → noExpr
  case2 : Maybe (subject ⊎ nothing) → Derv → noExpr → noExpr

data subExpr where
  argAsSubExpr : arg → subExpr
  assignment : lhs → ASGN → subExpr → subExpr
  Modified-assignment : lhs → Derv → Maybe subExpr → subExpr

data NAME where
  case1 : Var → NAME
  case2 : Var → NAME
  case3 : Var → NAME
  case4 : Var → NAME

data LHS-SUB where
  • : LHS-SUB
  case2 : lhsList → LHS-SUB
  case3 : lhsArray → LHS-SUB
  case4 : Var → LHS-SUB

data LHS-ANY where
  case1 : NAME → LHS-ANY
  case2 : LHS-SUB → LHS-ANY
  ⟨case3⟩ : LHS-ELT → LHS-ANY

data LHS-ATOM where
  case1 : LHS-ANY → LHS-ATOM
  ⟨case2⟩ : lhsStr → LHS-ATOM

data LHS-ELT where
  case1 : LHS-ANY → LHS-ELT
  case2 : lhsStr → LHS-ELT

data LHS-ENTRY where
  case1 : LHS-ELT → LHS-ENTRY
  _⇐_ : lhs → NAME → LHS-ENTRY

data lhsStr where
  case1 : LHS-ATOM → LHS-ATOM → List LHS-ATOM → lhsStr

data lhsList where
  ⟨_⟩ : Maybe ⋄ → Maybe ( (List ( LHS-ENTRY × ⋄ )) × LHS-ENTRY × (Maybe ⋄) ) → lhsList

data lhsArray where
  [_] : Maybe ⋄ → Maybe ( (List ( LHS-ELT × ⋄ )) × LHS-ELT × (Maybe ⋄) ) → lhsArray

data lhsComp where
  case1 : LHS-SUB → lhsComp
  case2 : lhsStr → lhsComp
  ⟨⟨_⟩⟩ : lhs → lhsComp

data lhs where
  case1 : Var → lhs
  case2 : lhsComp → lhs

data headW where
  case1 : lhs → headW
  𝕨 : headW

data headX where
  case1 : lhs → headX
  𝕩 : headX

data HeadF where
  case1 : lhs → HeadF
  case2 : Var → HeadF
  𝕗 : HeadF
  𝔽 : HeadF

data HeadG where
  case1 : lhs → HeadG
  case2 : Var → HeadG
  𝕘 : HeadG
  𝔾 : HeadG

data FuncLab where
  case1 : Var → FuncLab
  𝕊 : FuncLab

data Mod1Lab where
  case1 : Var → Mod1Lab
  -𝕣 : Mod1Lab

data Mod2Lab where
  case1 : Var → Mod2Lab
  -𝕣- : Mod2Lab

data FuncName where
  case1 : FuncLab → FuncName

data Mod1Name where
  case1 : HeadF → Mod1Lab → Mod1Name

data Mod2Name where
  case1 : HeadF → Mod2Lab → HeadG → Mod2Name

data LABEL where
  case1 : FuncLab → LABEL
  case2 : Mod1Lab → LABEL
  case3 : Mod2Lab → LABEL

data IMM-HEAD where
  case1 : LABEL → IMM-HEAD
  case2 : FuncName → IMM-HEAD
  case3 : Mod1Name → IMM-HEAD
  case4 : Mod2Name → IMM-HEAD

data ARG-HEAD where
  case1 : LABEL → ARG-HEAD
  case2 : Maybe headW → IMM-HEAD → (⁼ : Bool) → headX → ARG-HEAD
  ˜⁼ : headW → IMM-HEAD → headX → ARG-HEAD
  ⁼ : FuncName → (˜ : Bool) → ARG-HEAD
  case5 : lhsComp → ARG-HEAD

data BODY where
  case1? : Maybe ⋄ → List ( (STMT × ⋄) ⊎ (EXPR × (Maybe ⋄) × (Maybe ⋄) )) → STMT → Maybe ⋄ → BODY

data I-CASE where
  case1∶ : Maybe ( (Maybe ⋄) × IMM-HEAD × (Maybe ⋄) ) → BODY → I-CASE

data A-CASE where
  case1∶ : Maybe ((Maybe ⋄) × ARG-HEAD × (Maybe ⋄)  ) → BODY → A-CASE

data S-CASE where
  case1∶ : Maybe ( (Maybe ⋄) × Var × (Maybe ⋄) ) → BODY → S-CASE

data IMM-BLK where
  ⟨⨾⟩ : List I-CASE → I-CASE → IMM-BLK

data ARG-BLK where
  ⟨⨾𝕩⟩ : List A-CASE → A-CASE → ARG-BLK

data blSub where
  ⟨⨾⟩ : List S-CASE → S-CASE → blSub

data BlFunc where
  case1 : ARG-BLK → BlFunc

data -blMod1 where
  case1 : IMM-BLK → -blMod1
  case2 : ARG-BLK → -blMod1

data -blMod2- where
  case1 : IMM-BLK → -blMod2-
  case2 : ARG-BLK → -blMod2-
