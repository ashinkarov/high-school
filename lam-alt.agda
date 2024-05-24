open import Function
open import Data.Fin 
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum hiding ([_,_])
open import Data.Product
open import Data.Empty

module lam-alt (n : ℕ) where

data Ty : Set

data Con : Set where
  ε   : Con
  _▷_ : Con → Ty → Con

data Ty where
  base : Fin n → Ty
  _⇒_ : Ty → Ty → Ty

variable
  Γ Δ Ψ Ξ : Con
  τ σ δ σδ τδ δ' ρ : Ty
  i j   : Fin n

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

data _~_ : Ty → Ty → Set

data Insert : Ty → Ty → Ty → Set where
  zero : δ ~ δ' → Insert σ δ (δ' ⇒ σ)
  suc : Insert σ δ σδ → Insert (ρ ⇒ σ) ρ (ρ ⇒ σδ)  

data _~*_ : Ty → Ty → Set where
  refl* : base i ~* base i
  ext : σ ~* τ → Insert τ δ τδ → (δ ⇒ σ) ~* τδ   

data _~_ where
  perm : σ ~* τ → (σ ⇒ base i) ~ (τ ⇒ base i) 

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
  
