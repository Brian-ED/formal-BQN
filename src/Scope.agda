open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import grammer

module Scope where

-- A scope is a PROGRAM, I_CASE, A_CASE, or S_CASE node as defined by the BQN grammar
data Scope : Set where
  programScope : PROGRAM → Scope
  iCaseScope : I-CASE → Scope
  aCaseScope : A-CASE → Scope
  sCaseScope : S-CASE → Scope

-- An identifier instance is an s, F, _m, or _c_ node.
-- TODO I do not understand the rest of this:
--   "This does not include the special names that some block
--    types allow for these terms, and the names used only for
--    namespace field access as described below are explicitly excluded."
-- Its *containing scope* is the "smallest" scope
-- that contains it—the scope that contains the
-- identifier but not any other scopes containing the identifier
data IdentifierInstance : Set where
  -- Brian: Current Agda definition tries to avoid ever having to deal with
  -- an "instance". An actual instance in Agda would need a path and
  -- a Scope that the path is relative to
  ident-inst--2mod- : (2m : -mod2-) → (containing-scope : Scope) → IdentifierInstance
  ident-inst--1mod  : (1m : -mod1) → (containing-scope : Scope) → IdentifierInstance
  ident-inst-Func   : (f : Func) → (containing-scope : Scope) → IdentifierInstance
  ident-inst-atom   : (a : atom) → (containing-scope : Scope) → IdentifierInstance

-- TODO implementing the runtime, implement the following behavior for creating identifier instances
-- An identifier instance is defined when it is contained
-- in the left hand side of an ← assignment expression,
-- that is, the leftmost component of one of the four grammatical
-- rules with ASGN, provided that the ASGN node is "←" or "⇐", or
-- in a scope header, that is, IMM_HEAD, ARG_HEAD, or the s term in S_CASE.
-- Each identifier instance in a valid BQN program corresponds to exactly
-- one such defined identifier, called its definition, and two instances
-- are considered to refer to the same identifier if they have the same definition.
