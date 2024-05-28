open import Function
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum hiding ([_,_])
open import Data.Product
open import Data.Empty

module lam-alt (n : ℕ) where

data Ty : Set

data Con : Set where
  ε   : Con
  _▹_ : Con → Ty → Con

data Ty where
  base : Fin n → Ty
  _⇒_ : Ty → Ty → Ty

infixr 10 _⇒_

variable
  Γ Δ Ψ Ξ Γσ Δσ : Con
  τ τ' σ σ' δ δ' ρ : Ty
  i j k  : Fin n

{-
dom : Ty → Con
dom (base i) = ε
dom (σ ⇒ τ) = dom τ ▷ σ

cod : Ty → Fin n
cod (base i) = i
cod (σ ⇒ τ) = cod τ

_⇒*_ : Con → Fin n → Ty
ε ⇒* i = base i
(Γ ▷ σ) ⇒* i = σ ⇒ (Γ ⇒* i)
-}

--data Var : Con → Ty → Set where
--  zero : Var (Γ ▷ σ) σ
--  suc : Var Γ σ → Var (Γ ▷ τ) σ

infixl 10 _∈_
data _∈_ : Ty → Con → Set where
  v₀  : τ ∈ (Γ ▹ τ)
  vₛ  : τ ∈ Γ → τ ∈ (Γ ▹ σ)

data Nf : Con → Ty → Set
data Ne : Con → Ty → Set where
  var : σ ∈ Γ → Ne Γ σ
  app : Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ

data Nf where
  lam : Nf (Γ ▹ σ) τ → Nf Γ (σ ⇒ τ)
  ne : Ne Γ (base i) → Nf Γ (base i)

--record _~_ (σ τ : Ty) : Set

module P where
  data _~_ : Ty → Ty → Set 
  
  data Ins : Ty → Ty → Ty → Set where
    zero : τ ~ τ' → Ins τ σ (τ' ⇒ σ)
    suc  : Ins τ σ δ → Ins τ (ρ ⇒ σ) (ρ ⇒ δ) 

  data _~_ where
    zero : base i ~ base i
    suc  : τ ~ σ → Ins δ σ σ' → (δ ⇒ τ) ~ σ'


  prefl : τ ~ τ

  ins-zero : Ins τ σ (τ ⇒ σ)
  ins-zero = zero prefl

  prefl {base _} = zero
  prefl {_ ⇒ _}  = suc prefl (ins-zero)


  sym~ : τ ~ σ → σ ~ τ
  symh : τ ~ σ → Ins δ τ σ' → σ' ~ (δ ⇒ σ)
  symh p (zero t) = suc p (zero (sym~ t))
  symh (suc p x) (suc i) = suc (symh p i) (suc x)
  
  sym~ zero = zero
  sym~ (suc p x) = symh (sym~ p) x

  module SanityTests where
    test₀ : (base i ⇒ base j) ~ (base i ⇒ base j)
    test₀ = suc zero (zero zero)

    test₁ : (τ ⇒ σ ⇒ δ) ~ (σ ⇒ τ ⇒ δ)
    test₁ = suc (suc prefl ins-zero) (suc ins-zero)

    test-eq₁ : (τ ⇒ σ ⇒ base i) ~ (τ ⇒ σ ⇒ base i)
    test-eq₁ = suc (suc zero (ins-zero)) ins-zero

    test-eq₂ : (τ ⇒ σ ⇒ base i) ~ (τ ⇒ σ ⇒ base i)
    test-eq₂ = suc prefl ins-zero

    test-eq-eq : test-eq₁ {τ}{σ}{i} ≡ test-eq₂
    test-eq-eq = refl

open P

app-nf : Nf Γ (σ ⇒ τ) → Nf Γ σ → Nf Γ τ
app-nf = {!!}

_∘-nf_ : Nf Γ (τ ⇒ ρ) → Nf Γ (σ ⇒ τ) → Nf Γ (σ ⇒ ρ) 
_∘-nf_ = {!!}



cod : Ty → Fin n
cod (base x) = x
cod (τ ⇒ σ) = cod σ

ext : Ty → Con → Con
ext (base x) Γ = Γ
ext (τ ⇒ σ) Γ = (ext σ (Γ ▹ τ))

len : Ty → ℕ
len (base x) = 0
len (τ ⇒ σ) = 1 + len σ

data Minus : Con → ℕ → Set where
  base : Minus Γ 0
  step : ∀ {n} → Minus Γ n → Minus (Γ ▹ τ) (suc n)


--ext₁ : (τ : Ty) → (Γ : Con) → Σ (Con × ℕ) λ (Δ , n) → 



testext : Ty → Ty → Fin n → Con → Con
testext τ σ i Γ = ext (τ ⇒ σ ⇒ base i) Γ

data _⊆_ : Con → Con → Set where
  ε    : ε ⊆ ε
  skip : Γ ⊆ Δ → Γ ⊆ (Δ ▹ τ)
  keep : Γ ⊆ Δ → (Γ ▹ τ) ⊆ (Δ ▹ τ)

⊆-eq : Γ ⊆ Γ
⊆-eq {ε}     = ε
⊆-eq {Γ ▹ τ} = keep ⊆-eq

prev : (Γ ▹ τ) ⊆ Δ → Γ ⊆ Δ
prev (skip p) = skip (prev p)
prev (keep p) = skip p

wke : Γ ⊆ Δ → Ne Γ τ → Ne Δ τ


domcod : (τ : Ty) → (Γ : Con) → Σ Con λ Δ → Γ ⊆ Δ
domcod (base x) Γ = (Γ ) , ⊆-eq
domcod (τ ⇒ σ) Γ = let Δ , f = domcod σ (Γ ▹ τ) in Δ ,  prev f


var-nf : Ne Γ τ → Nf Γ τ
var-nf {τ = base x} v = ne v
var-nf {τ = τ ⇒ σ}  v = lam (var-nf (app (wke (skip ⊆-eq) v) (var-nf (var v₀))))

var-nfv : τ ∈ Γ → Nf Γ τ
var-nfv v = var-nf (var v)

id-nf : Nf Γ (σ ⇒ σ)
id-nf = lam (var-nfv v₀)

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


{-
data Con* : Set 

record Ty* : Set where
  inductive
  field
    dom : Con*
    cod : Fin n

open Ty*

variable
  Γ* Δ* Ψ* Γσ* Δσ* : Con*
  τ* σ* σ*' δ* δ*' ρ* : Ty*

data Con*  where
  ε   : Con*
  _▷_ : Con* → Ty* → Con*

ty→ty* : Ty → Ty*
dom (ty→ty* (base i)) = ε
cod (ty→ty* (base i)) = i
dom (ty→ty* (σ ⇒ τ)) = dom (ty→ty* τ) ▷ (ty→ty* σ)
cod (ty→ty* (σ ⇒ τ)) = cod (ty→ty* τ)

_⇒*_ : Con* → Fin n → Ty
ty*→ty : Ty* → Ty
ty*→ty record { dom = dom ; cod = cod } = dom ⇒* cod

ε ⇒* i = base i
(Γ ▷ σ) ⇒* i = (ty*→ty σ) ⇒ (Γ ⇒* i)

record _~*_ (σ τ : Ty*) : Set

data Insert : Con* → Ty* → Con* → Set where
  zero : σ* ~* σ*' → Insert Δ* σ* (Δ* ▷ σ*')
  suc : Insert Γ* σ* Γσ* → Insert (Γ* ▷ τ*) σ* (Γσ* ▷ τ*)

data _~C*_ : Con* → Con* → Set where
  refl-ε : ε ~C* ε
  ext : Γ* ~C* Δ* → Insert Δ* σ* Δσ* → (Γ* ▷ σ*) ~C* Δσ* 

record _~*_ σ τ  where
  inductive
  field
    dom~ : (dom σ) ~C* (dom τ)
    cod≡ : cod σ ≡ cod τ

open _~*_

refl~C* : Γ* ~C* Γ*

refl~* : σ* ~* σ*
refl~* {σ* = record { dom = dom ; cod = cod }} =
  record { dom~ = refl~C* {Γ* = dom} ;
           cod≡ = refl }

refl~C* {Γ* = ε} = refl-ε
refl~C* {Γ* = Γ* ▷ σ*} = ext refl~C* (zero refl~*)
-}


{-
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
refl~ = 
{-
dom~ refl~ = refl~C
cod≡ refl~ = refl
-}

refl~C {Γ = ε} = refl-ε
refl~C {Γ = Γ ▷ σ} = ext refl~C (zero (refl~ {σ = σ}))

{-
tst : (σ ⇒ τ  ⇒ base i) ~ (τ ⇒ σ ⇒ base i)
dom~ tst = {!!}
cod≡ tst = refl
-}
sym~ : σ ~ τ → τ ~ σ
sym~ = {!!}


  
-}
