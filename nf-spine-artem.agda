{- implement spinal Nfs -}

open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality hiding ([_])

module _(n : ℕ) where

TVar : Set
TVar = Fin n

variable X Y Z : TVar

data Tel : Set 

data Ty : Set where
  _⇒Var_ : Tel → TVar → Ty

data Tel where
  • : Tel
  _◁_ : Ty → Tel → Tel

variable Θ Ξ : Tel
variable A B C : Ty

ty-var : TVar → Ty
ty-var x = • ⇒Var x

{-
_▷_ : Tel → Ty → Tel
• ▷ B = B ◁ •
(A ◁ Θ) ▷ B = A ◁ (Θ ▷ B)
-}

_⇒_ : Ty → Ty → Ty
A ⇒ (Θ ⇒Var x) = (A ◁ Θ) ⇒Var x 

data Con : Set where
  • : Con
  _▷_ : Con → Ty → Con

variable Γ Δ Φ : Con

data Var : Con → Ty → Set where
  zero : Var (Γ ▷ A) A
  suc : Var Γ A → Var (Γ ▷ B) A

data Ne : Con → Ty → Set

data Nf : Con → Ty → Set where
  lam : Nf (Γ ▷ A) (Θ ⇒Var X) → Nf Γ ((A ◁ Θ) ⇒Var X)
  ne : Ne Γ (• ⇒Var X) → Nf Γ (• ⇒Var X)

{-
  lam : Nf (Γ ▷ A) B → Nf Γ (A ⇒ B)
  ne : Ne Γ (ty-var X) → Nf Γ (ty-var X)

app-nf : Nf Γ ((A ◁ Θ) ⇒Var X) → Nf (Γ ▷ A) (Θ ⇒Var X)
app-nf (lam t) = t
-}

app-nf : Nf Γ (A ⇒ B) → Nf (Γ ▷ A) B
app-nf {B = x ⇒Var x₁} (lam u) = u

data Spine : Con → Ty → Ty → Set where
  ε : Spine Γ A A
  cons : Nf Γ B → Spine Γ C A → Spine Γ (B ⇒ C) A

data Ne where
  app : Var Γ B → Spine Γ B A → Ne Γ A

app-sp : Spine Γ A (B ⇒ C) → Nf Γ B → Spine Γ A C
app-sp ε t = cons t ε
app-sp (cons u sp) t = cons u (app-sp sp t)

data Vars : Con → Con → Set where
  ε : Vars Γ •
  _,_ : Vars Γ Δ → Var Γ A → Vars Γ (Δ ▷ A)

data Nfs : Con → Con → Set where
  ε : Nfs Γ •
  _,_ : Nfs Γ Δ → Nf Γ A → Nfs Γ (Δ ▷ A)
  
suc-vars : Vars Γ Δ → Vars (Γ ▷ A) Δ
suc-vars ε = ε
suc-vars (xs , x) = (suc-vars xs) , (suc x)

_▷-vars :  Vars Γ Δ → Vars (Γ ▷ A) (Δ ▷ A)
δ ▷-vars = suc-vars δ , zero

id-vars : Vars Γ Γ
id-vars {Γ = •} = ε
id-vars {Γ = Γ ▷ A} = id-vars ▷-vars

wk-var : Vars (Γ ▷ A) Γ
wk-var = suc-vars id-vars 

_[_]v-v : Var Δ A → Vars Γ Δ → Var Γ A
zero [ _ , x ]v-v = x
suc x [ δ , _ ]v-v = x [ δ ]v-v

_*v_ : Spine Γ A B → Vars Δ Γ → Spine Δ A B


_[_]ne-v : Ne Δ A → Vars Γ Δ → Ne Γ A
app x ϑ [ δ ]ne-v = app (x [ δ ]v-v) (ϑ *v δ)

_[_]nf-v : Nf Δ A → Vars Γ Δ → Nf Γ A
lam t [ δ ]nf-v = lam (t [ δ ▷-vars ]nf-v)
ne x [ δ ]nf-v = ne (x [ δ ]ne-v)

ε *v δ = ε
cons t sp *v δ = cons (t [ δ ]nf-v) (sp *v δ)

suc-nf : Nf Δ A → Nf (Δ ▷ B) A
suc-nf a = a [ wk-var ]nf-v

suc-nfs : Nfs Δ Γ → Nfs (Δ ▷ B) Γ
suc-nfs ε = ε
suc-nfs (γ , a) = suc-nfs γ , suc-nf a

suc-sp : Spine Γ A B → Spine (Γ ▷ C) A B
suc-sp sp = sp *v wk-var 

ne→nf : Ne Γ A → Nf Γ A
var→nf : Var Γ A → Nf Γ A

var→nf x = ne→nf (app x ε)

ne→nf {A = • ⇒Var X} = ne
ne→nf {A = (B ◁ Θ) ⇒Var X} (app x sp) = lam (ne→nf (app (suc x) (app-sp (suc-sp sp) (var→nf zero))))

zero-nf : Nf (Γ ▷ A) A
zero-nf = var→nf zero

_▷-nfs :  Nfs Γ Δ → Nfs (Γ ▷ A) (Δ ▷ A)
δ ▷-nfs = suc-nfs δ , zero-nf

_[_]v-nf : Var Δ A → Nfs Γ Δ → Nf Γ A
zero [ _ , x ]v-nf = x
suc x [ δ , _ ]v-nf = x [ δ ]v-nf

_[_] : Nf Γ A → Nfs Δ Γ → Nf Δ A
_[_]ne : Ne Γ A → Nfs Δ Γ → Nf Δ A
_*nfs_ : Spine Γ A B → Nfs Δ Γ → Spine Δ A B
app* : Nf Γ A → Spine Γ A B → Nf Γ B

lam t [ us ] = lam (t [ us ▷-nfs ])
ne t [ us ] = t [ us ]ne

app x sp [ us ]ne = app* (x [ us ]v-nf) (sp *nfs us)

ε *nfs us = ε
cons x sp *nfs us = cons (x [ us ]) (sp *nfs us)

app* {B = • ⇒Var X} t ε = t
app* {B = • ⇒Var X} t (cons x sp) = {!app-nf t !}
app* {B = (x ◁ x₂) ⇒Var x₁} t sp = {!!}

{-
app* (lam t) sp = {!!}
app* (ne (app x sp')) sp = {!ne!}
-}
{-
Goal: Ne Δ A
————————————————————————————————————————————————————————————
us : Nfs Δ Γ
sp : Spine Γ B A
t  : Var Γ B

t [ us ] : Nf Δ B

app* sp us : Spine Δ B A



-}

{-

_*v_ : Nf* Δ Θ → Vars Γ Δ → Nf* Γ Θ 





_[_] : Nf Γ A → Nfs Δ Γ → Nf Δ A
_[_] = {!!}

_∘_ : Nfs Γ Φ → Nfs Δ Γ → Nfs Δ Φ
ε ∘ us = ε
(ts , t) ∘ us = (ts ∘ us) , (t [ us ])

sucs : Nfs Γ Δ → Nfs (Γ ▷ B) Δ
sucs ε = ε
sucs (ts , t) = (sucs ts) , (suc-nf t)

_▷nfs_ : Nfs Γ Δ → (A : Ty) → Nfs (Γ ▷ A) (Δ ▷ A)
_▷nfs_ ts A = (sucs ts) , zero-nf

id : {Γ : Con} → Nfs Γ Γ
id {•} = ε
id {Γ ▷ A} = id {Γ} ▷nfs A






-}
