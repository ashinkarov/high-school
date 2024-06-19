open import Function
open import Data.Fin 
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum hiding ([_,_])
open import Data.Product
open import Data.Empty

module lam-alt-problem (n : ℕ) where

data Ty : Set

data Con : Set where
  ε   : Con
  _▷_ : Con → Ty → Con

data Ty where
  base : Fin n → Ty
  _⇒_ : Ty → Ty → Ty

infixr 5 _⇒_

variable
  Γ Δ Ψ Ξ Γσ Δσ : Con
  τ σ σ' δ δ' ρ : Ty
  i j   : Fin n

dom : Ty → Con
dom (base i) = ε
dom (σ ⇒ τ) = dom τ ▷ σ

cod : Ty → Fin n
cod (base i) = i
cod (σ ⇒ τ) = cod τ

_⇒*_ : Con → Fin n → Ty
ε ⇒* i = base i
(Γ ▷ σ) ⇒* i = σ ⇒ (Γ ⇒* i)

data Var : Con → Ty → Set where
  zero : Var (Γ ▷ σ) σ
  suc : Var Γ σ → Var (Γ ▷ τ) σ

data Nf : Con → Ty → Set
data Ne : Con → Ty → Set where
  var : Var Γ σ → Ne Γ σ
  app : Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ

data Nf where
  lam : Nf (Γ ▷ σ) τ → Nf Γ (σ ⇒ τ)
  ne : Ne Γ (base i) → Nf Γ (base i)

record _~_ (σ τ : Ty) : Set

data Insert : Con → Ty → Con → Set where
  zero : σ ~ σ' → Insert Δ σ (Δ ▷ σ')
  suc : Insert Γ σ Γσ → Insert (Γ ▷ τ) σ (Γσ ▷ τ)

data _~C_ : Con → Con → Set where
  refl-ε : ε ~C ε
  ext : Γ ~C Δ → Insert Δ σ Δσ → (Γ ▷ σ) ~C Δσ 

record _~_ σ τ  where
  inductive
  field
    dom~ : (dom σ) ~C (dom τ)
    cod≡ : cod σ ≡ cod τ

open _~_

{-
data _~_ where
  refl-base : base i ~ base i
  ext : σ ~ τ → Insert τ δ τδ → (δ ⇒ σ) ~ τδ   

refl~ : σ ~ σ
refl~ {σ = base i} = refl-base
refl~ {σ = σ ⇒ τ} = ext refl~ (zero refl~)
-}

refl~C : Γ ~C Γ
refl~ : σ ~ σ
refl~ = record { dom~ = refl~C ; cod≡ = refl }
{-
dom~ refl~ = refl~C
cod≡ refl~ = refl
-}

refl~C {Γ = ε} = refl-ε
refl~C {Γ = Γ ▷ σ} = ext refl~C (zero (refl~ {σ = σ}))

tst : (σ ⇒ τ  ⇒ base i) ~ (τ ⇒ σ ⇒ base i)
dom~ tst = {!!}
cod≡ tst = refl

sym~ : σ ~ τ → τ ~ σ
sym~ = {!!}


app-nf : Nf Γ (σ ⇒ τ) → Nf Γ σ → Nf Γ τ
app-nf = {!!}

_∘-nf_ : Nf Γ (τ ⇒ ρ) → Nf Γ (σ ⇒ τ) → Nf Γ (σ ⇒ ρ) 
_∘-nf_ = {!!}

id-nf : Nf Γ (σ ⇒ σ)
id-nf = {!!}

record _≅_ (σ τ : Ty) : Set where
  field
    φ : Nf ε (σ ⇒ τ)
    ψ : Nf ε (τ ⇒ σ)
    φψ : φ ∘-nf ψ ≡ id-nf
    ψφ : ψ ∘-nf φ ≡ id-nf

open _≅_

symsym : (στ : σ ~ τ) → στ ≡ sym~ (sym~ στ)
symsym = {!!}

sound-fun : σ ~ τ → Nf ε (σ ⇒ τ)
sound-fun = {!!}

sound-retr : (στ : σ ~ τ) → (sound-fun στ) ∘-nf (sound-fun (sym~ στ)) ≡ id-nf
sound-retr = {!!}

sound : σ ~ τ → σ ≅ τ 
φ (sound στ) = sound-fun στ
ψ (sound στ) = sound-fun (sym~ στ)
φψ (sound στ) = sound-retr στ
ψφ (sound στ) = {!!} -- use rewrite symsym
{-
types are hedperm ⇒ definitional iso 
definitional iso ⇒ types are hedperm

-}
  
