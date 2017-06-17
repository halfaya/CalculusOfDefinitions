module CalculusOfDefinitions where

-- Formalization of Thierry Coquand's unpublished "A Calculus of Definitions" (June 13, 2017 draft).

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data Vec (A : Set) : ℕ → Set where
  []   :                          Vec A zero
  _∷_  :  {n : ℕ} → A → Vec A n → Vec A (suc n)

data Maybe (A : Set) : Set where
  Nothing :     Maybe A
  Just    : A → Maybe A

-- constructor names are represented as ℕ
Name : Set
Name = ℕ

mutual
  data Program : Set where
    access : ℕ                      → Program
    app    : Program → Program      → Program
    lam    : Program                → Program
    pi     : Program → Program      → Program
    appdef : Program → Definition   → Program
    con    : Name    → List Program → Program
    branch : Branch                 → Program
    sum    : Sum                    → Program

  data Definition : Set where
    def : List Program → List Program → Definition

  data Branch : Set where
    branch : {k : ℕ} → Vec Program k → Branch

  data Sum : Set where
    sum  : {k : ℕ} → Vec (List Program) k → Sum

  data Environment : Set where
    []   : Environment
    _∷ᵣ_ : Environment → Value       → Environment
    def  : Definition  → Environment → Environment

  data Context : Set where
    []   : Context
    _∷ᵣ_ : Context → Value → Context

  data Value : Set where
    prog : List Program → Environment → Value  -- TODO: Should be List Program rather than Program?
    app  : Value → Value → Value
    base : ℕ → Value -- TODO: This is X_l; see if it's what is intended.
    con  : Name → List Value → Value
    pi   : Value → Value → Value

lookup : ℕ → Environment → Maybe Value
lookup _       []                   = Nothing
lookup zero    (_ ∷ᵣ u)             = Just u
lookup (suc n) (σ ∷ᵣ _)             = lookup n σ
lookup zero    ρ@(def (def ms _) _) = Just (prog ms ρ)
lookup (suc n) (def _ σ)            = lookup n σ

-- TODO: Determine meaning of vector M.
eval : Program → Environment → Maybe Value
eval (access n)   ρ = lookup n ρ
eval (app m p)    ρ = {!!}
eval (lam m)      ρ = {!!}
eval (pi m p)     ρ = {!!}
eval (appdef m d) ρ = Just (prog (m ∷ []) (def d ρ))
eval (con c ms)   ρ = {!Just (con c (prog ms ρ))!}
eval (branch x)   ρ = {!!}
eval (sum x)      ρ = {!!}
