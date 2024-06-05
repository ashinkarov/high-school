open import Function
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum hiding ([_,_])
open import Data.Product
open import Data.Empty

module lam-alt (n : ℕ) where

data Ty : Set

infixl 15 _▹_
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
--data Ne : Con → Ty → Set where
--  var : σ ∈ Γ → Ne Γ σ
--  app : Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ


infixr 15 _◃_
-- A list of arguments for the function
-- For example:
--    a : Nf τ
--    b : Nf σ
--   ------------------------------
--    a ◃ (b ◃ ε) : Sp (a ⇒ b ⇒ c)
--
data Sp : Con → Ty → Ty → Set where
  ε   : Sp Γ τ τ
  _◃_ : Nf Γ τ → Sp Γ σ δ → Sp Γ (τ ⇒ σ) δ

data Ne : Con → Ty → Set where
  app : τ ∈ Γ → Sp Γ τ σ → Ne Γ σ

data Nf where
  lam : Nf (Γ ▹ σ) τ → Nf Γ (σ ⇒ τ)
  -- While `Ne` can be inlined, it is easier to keep
  -- the pair of variable and arguments in a single structure.
  ne : Ne Γ (base i) → Nf Γ (base i)

module P where
  data _~_ : Ty → Ty → Set

  data Ins : Ty → Ty → Ty → Set where
    zero : τ ~ τ' → Ins τ σ (τ' ⇒ σ)
    suc  : Ins τ σ δ → Ins τ (ρ ⇒ σ) (ρ ⇒ δ)

  data _~_ where
    zero : base i ~ base i
    suc  : τ ~ σ → Ins δ σ σ' → (δ ⇒ τ) ~ σ'

  refl~ : τ ~ τ

  ins-zero : Ins τ σ (τ ⇒ σ)
  ins-zero = zero refl~

  refl~ {base _} = zero
  refl~ {_ ⇒ _}  = suc refl~ (ins-zero)


  sym~ : τ ~ σ → σ ~ τ
  symh : τ ~ σ → Ins δ τ σ' → σ' ~ (δ ⇒ σ)
  symh p (zero t) = suc p (zero (sym~ t))
  symh (suc p x) (suc i) = suc (symh p i) (suc x)

  sym~ zero = zero
  sym~ (suc p x) = symh (sym~ p) x

  trans~ : τ ~ σ → σ ~ δ → τ ~ δ

  module SanityTests where
    test₀ : (base i ⇒ base j) ~ (base i ⇒ base j)
    test₀ = suc zero (zero zero)

    test₁ : (τ ⇒ σ ⇒ δ) ~ (σ ⇒ τ ⇒ δ)
    test₁ = suc (suc refl~ ins-zero) (suc ins-zero)

    test-eq₁ : (τ ⇒ σ ⇒ base i) ~ (τ ⇒ σ ⇒ base i)
    test-eq₁ = suc (suc zero (ins-zero)) ins-zero

    test-eq₂ : (τ ⇒ σ ⇒ base i) ~ (τ ⇒ σ ⇒ base i)
    test-eq₂ = suc refl~ ins-zero

    test-eq-eq : test-eq₁ {τ}{σ}{i} ≡ test-eq₂
    test-eq-eq = refl

open P

-- Γ / v computes a new context which is Γ without the variable v
_/_ : (Γ : Con) → τ ∈ Γ → Con
(Γ ▹ τ) / v₀    = Γ
(Γ ▹ τ) / vₛ v  = (Γ / v) ▹ τ

-- Weakening
module _ where
  wkv  : (v : τ ∈ Γ) → σ ∈ (Γ / v) → σ ∈ Γ
  wkv v₀     w      = vₛ w
  wkv (vₛ v) v₀     = v₀
  wkv (vₛ v) (vₛ w) = vₛ (wkv v w)


  wknf   : (v : τ ∈ Γ) → Nf (Γ / v) σ → Nf Γ σ
  wksp   : (v : τ ∈ Γ) → Sp (Γ / v) σ δ → Sp Γ σ δ

  wknf v (lam e) = lam (wknf (vₛ v) e)
  wknf v (ne (app w s)) = ne (app (wkv v w) (wksp v s))

  wksp v ε = ε
  wksp v (x ◃ s) = wknf v x ◃ wksp v s

  _↑ : Nf Γ σ → Nf (Γ ▹ τ) σ
  _↑ = wknf v₀


-- Equality of two variables
data Eq : τ ∈ Γ → σ ∈ Γ → Set where
  eq  : {x : τ ∈ Γ} → Eq x x
  neq : (x : τ ∈ Γ) → (y : σ ∈ Γ / x) → Eq x (wkv x y)


eq? : (x : τ ∈ Γ) (y : σ ∈ Γ) → Eq x y
eq? v₀ v₀ = eq
eq? v₀ (vₛ y) = neq v₀ y
eq? (vₛ x) v₀ = neq (vₛ x) v₀
eq? (vₛ x) (vₛ y) with eq? x y
... | eq = eq
... | neq .x y = neq (vₛ x) (vₛ y)


-- Some helper functions
cod : Ty → Fin n
cod (base x) = x
cod (τ ⇒ σ) = cod σ

ext : Ty → Con → Con
ext (base x) Γ = Γ
ext (τ ⇒ σ) Γ = (ext σ (Γ ▹ τ))

len : Ty → ℕ
len (base x) = 0
len (τ ⇒ σ) = 1 + len σ

codh : Ins δ τ σ → cod τ ≡ cod σ
codh (zero x) = refl
codh (suc i)  = codh i

cod~ : τ ~ σ → cod τ ≡ cod σ
cod~ zero      = refl
cod~ (suc p i) = trans (cod~ p) (codh i)

liftnf : Nf Γ τ → Nf (ext τ Γ) (base $ cod τ)
liftnf {τ = base x} e = e
liftnf {τ = τ ⇒ τ₁} (lam e) = liftnf e

foldnf : Nf (ext τ Γ) (base $ cod τ) → Nf Γ τ
foldnf {τ = base x} e = e
foldnf {τ = τ ⇒ τ₁} e = lam (foldnf e)

lift-fold : (e : Nf Γ τ) → foldnf (liftnf e) ≡ e
lift-fold {τ = base x} e = refl
lift-fold {τ = τ ⇒ τ₁} (lam e) = cong lam (lift-fold e)

record Var (Γ : Con) (τ : Ty) : Set where
  constructor var
  field
    {α} : Ty
    τ~α : τ ~ α
    v   : α ∈ Γ

-- Renamings and their operations
Ren : Con → Con → Set
Ren Γ Δ = ∀ {τ} → τ ∈ Δ → ∃ λ σ → (τ ~ σ) × σ ∈ Γ

idᵣ : Ren Γ Γ
idᵣ v = _ , (refl~ , v)

_∘ᵣ_ : Ren Ψ Δ → Ren Γ Ψ → Ren Γ Δ
(f ∘ᵣ g) v =
   let
     _ , (f~ , fv) = f v
     _ , (g~ , gfv) = g fv
   in _ , (trans~ f~ g~) , gfv

rprep : Ren Γ Δ → σ ~ τ → Ren (Γ ▹ τ) (Δ ▹ σ)
rprep r p~ v₀ = _ , p~ , v₀
rprep r p~ (vₛ v) =
   let
     _ , (r~ , rv) = r v
   in _ , r~ , vₛ rv

ext-ren : Ren Γ Δ → Ren (ext τ Γ) (ext τ Δ)
ext-ren {τ = base x} r = r
ext-ren {τ = τ ⇒ τ₁} r = ext-ren {τ = τ₁} (rprep r refl~)

ext-var : τ ∈ Γ → τ ∈ ext σ Γ
ext-var {σ = base x} v = v
ext-var {σ = σ ⇒ σ'} v = ext-var {σ = σ'} (vₛ v)

-- ins-var : Ins δ σ σ' → Var (ext σ' Γ) δ
-- ins-var {σ = σ} (zero p) = var p (ext-var {σ = σ} v₀)
-- ins-var (suc i) = ins-var i

-- Comput renaming from the _~_
module _ where
  perm~ : τ ~ σ → Ren Γ Δ → Ren (ext τ Γ) (ext σ Δ)

  data Veq : τ ∈ Γ → σ ∈ Γ → Set where
    eq : ∀ (x : τ ∈ Γ) → Veq x x

  ext-eq : (w : τ ∈ Γ) → (v : τ' ∈ ext σ Γ)
      → (Veq v (ext-var {σ = σ} w)) ⊎ (τ' ∈ ext σ (Γ / w))
  ext-eq {σ = base x} w v with eq? w v
  ... | eq       = inj₁ (eq w)
  ... | neq .w y = inj₂ y
  ext-eq {σ = σ ⇒ σ₁} w v = ext-eq {σ = σ₁} (vₛ w) v

  ext-suc : (w : δ ∈ Γ) → τ ∈ ext σ (Γ / w) → τ ∈ ext σ Γ
  ext-suc {σ = base x} w v = wkv w v
  ext-suc {σ = σ ⇒ σ₁} w v = ext-suc {σ = σ₁} (vₛ w) v

  insh : Ren (ext τ Γ) (ext σ Δ) → Ins δ σ σ' → Ren (ext (δ ⇒ τ) Γ) (ext σ' Δ)
  insh {τ = τ}{Γ = Γ}{σ = σ}{Δ = Δ} r (zero {τ' = τ'} x) v
    with ext-eq {σ = σ} v₀ v
  ... | inj₁ (eq .(ext-var {σ = σ} v₀)) = _ , (sym~ x) , (ext-var {σ = τ} v₀)
  ... | inj₂ y = let _ , p~ , y' = r y in _ , p~ , (ext-suc {σ = τ} v₀ y')
  insh {τ = τ} r (suc i) = insh {τ = τ} r i

  ins~ : τ ~ σ → Ins δ σ σ' → Ren Γ Δ → Ren (ext (δ ⇒ τ) Γ) (ext σ' Δ)
  ins~ p~ (zero x) r = perm~ p~ (rprep r $ sym~ x)
  ins~ {τ = τ} p~ (suc i) r = insh {τ = τ} (perm~ p~ r) i

  perm~ zero r = r
  perm~ (suc p~ x) r = ins~ p~ x r

-- Transport terms over _~_
module _ where
  {-# TERMINATING #-} -- Fuck you Agda, this is fine!
  rennf : Ren (ext τ Γ) (ext σ Δ) → cod τ ≡ cod σ
        → Nf Δ σ → Nf Γ τ

  ren' : τ ~ σ → Nf Γ σ → Nf Γ τ
  ren' p~ e = rennf (perm~ p~ idᵣ) (cod~ p~) e

  inssp : Sp Γ τ (base i) → Ins δ τ τ' → Nf Γ δ → Sp Γ τ' (base i)
  inssp ε       (zero p~) x = ren' (sym~ p~) x ◃ ε
  inssp (h ◃ s) (zero p~) x = ren' (sym~ p~) x ◃ h ◃ s
  inssp (h ◃ s) (suc i)   x = h ◃ inssp s i x

  shufsp : Ren (ext τ Γ) (ext σ Δ) → cod τ ≡ cod σ
         → τ' ~ σ' → Sp (ext τ Γ) τ' (base $ cod σ)
         → Sp (ext τ Γ) σ' (base $ cod σ)
  shufsp r i=j zero s = s
  shufsp {τ = τ}{σ = σ} r i=j (suc p~ i) (h ◃ s)
    = inssp (shufsp {τ = τ}{σ = σ} r i=j p~ s) i h

  rensp : Ren (ext τ Γ) (ext σ Δ) → cod τ ≡ cod σ
          → Sp (ext σ Δ) τ' σ' → Sp (ext τ Γ) τ' σ'
  rennf {τ = τ}{σ = σ}{Δ = Δ} r i=j e with liftnf e
  ... | ne (app f sp) =
    let
      _ , (f~ , f') = r f
      sp' = rensp {τ = τ}{σ = σ}{Δ = Δ} r i=j sp
      sp'' = shufsp {τ = τ}{σ = σ} r i=j f~ sp'
      sp''' = subst (λ x → Sp _ _ (base x)) (sym i=j) sp''
    in foldnf (ne (app f' sp'''))

  rensp r i=j ε = ε
  rensp {τ = τ}{σ = σ} r i=j (_◃_ {τ = τ'} x s)
    = rennf (ext-ren {τ = τ'} r) refl x ◃ rensp {τ = τ}{σ = σ} r i=j s



appsp : Sp Γ τ (σ ⇒ δ) → Nf Γ σ → Sp Γ τ δ
appsp ε       e = e ◃ ε
appsp (x ◃ s) e = x ◃ appsp s e

nenf : Ne Γ σ → Nf Γ σ
nvar : τ ∈ Γ → Nf Γ τ
nvar v = nenf (app v ε)

nenf {σ = base x} v         = ne v
nenf {σ = τ ⇒ δ}  (app v s) = lam (nenf (app (vₛ v) (appsp (wksp v₀ s) (nvar v₀))))

-- Id does not need substitutions
id-nf : Nf Γ (σ ⇒ σ)
id-nf = lam (nenf (app v₀ ε))


module SanityRenTest where
  testtm : Nf Γ (τ ⇒ σ ⇒ τ)
  testtm = lam (lam (nvar (vₛ v₀)))

  -- NOTE: this is is self inverse in terms of sym~
  test~ : (τ ⇒ σ ⇒ δ) ~ (σ ⇒ τ ⇒ δ)
  test~ = suc (suc refl~ ins-zero) (suc ins-zero)

  test-ren : Nf Γ (base i ⇒ base j ⇒ base j)
  test-ren = ren' test~ testtm

  _ : test-ren {Γ = Γ}{i = i}{j = j}
      ≡ lam (lam (ne (app v₀ ε)))
  _ = refl

  testtm₁ : Nf Γ ((τ ⇒ σ ⇒ (base i)) ⇒ τ ⇒ σ ⇒ (base i))
  testtm₁ = lam (lam (lam (ne (app ((vₛ (vₛ v₀))) ((nvar (vₛ v₀)) ◃ (nvar v₀) ◃ ε)))))

  test₁~ : ((τ ⇒ σ ⇒ base i) ⇒ τ ⇒ σ ⇒ base i)
           ~ (τ ⇒ (σ ⇒ τ ⇒ base i) ⇒ σ ⇒ base i)
  test₁~ = suc (suc (suc zero (zero refl~)) (zero refl~)) (suc (zero test~))

  test-ren₁ : Nf Γ (base i ⇒ (base j ⇒ base i ⇒ base k) ⇒ base j ⇒ base k)
  test-ren₁ = ren' (sym~ test₁~) testtm₁

  _ : test-ren₁ {Γ = Γ}{i = i}{j = j}{k = k}
      ≡ lam
         (lam
          (lam
           (ne (app (vₛ v₀)
               (ne (app v₀ ε)
                ◃ ne (app (vₛ (vₛ v₀)) ε)
                ◃ ε)))))
  _ = refl

-- These have to be defined mutually
module _ where
  appnf : Nf Γ (τ ⇒ σ) → Nf Γ τ → Nf Γ σ

  subsp : (v : τ ∈ Γ) → Sp Γ σ δ → Nf (Γ / v) τ → Sp (Γ / v) σ δ

  app-nf-sp : Nf Γ τ → Sp Γ τ σ → Nf Γ σ
  app-nf-sp e ε = e
  app-nf-sp e (x ◃ s) = app-nf-sp (appnf e x) s

  sub : (v : τ ∈ Γ) → Nf Γ σ → Nf (Γ / v) τ → Nf (Γ / v) σ
  sub v (lam e) e₁ = lam (sub (vₛ v) e (e₁ ↑))
  sub v (ne (app w s)) e₁ with eq? v w
  ... | eq        = app-nf-sp e₁ (subsp v s e₁)
  ... | neq .v w′ = ne (app w′ (subsp v s e₁))

  subsp v ε e = ε
  subsp v (x ◃ s) e = sub v x e ◃ subsp v s e

  appnf (lam f) x = sub v₀ f x


_∘-nf_ : Nf Γ (τ ⇒ ρ) → Nf Γ (σ ⇒ τ) → Nf Γ (σ ⇒ ρ)
f ∘-nf g = lam (appnf (wknf v₀ f) (appnf (wknf v₀ g) (nvar v₀)))


-- The main result that relates _~_ with term equality
record _≅_ (σ τ : Ty) : Set where
  field
    φ : Nf ε (σ ⇒ τ)
    ψ : Nf ε (τ ⇒ σ)
    φψ : φ ∘-nf ψ ≡ id-nf
    ψφ : ψ ∘-nf φ ≡ id-nf

open _≅_

symsym : (στ : σ ~ τ) → στ ≡ sym~ (sym~ στ)
symsym = {!!}


-- FIXME: termination chcker gets upset
module _ where
  {-# TERMINATING #-}
  sound-fun : τ ~ σ → Nf Γ (τ ⇒ σ)


  ins-to-ext : Ins δ σ σ' → Nf (ext σ' Γ) δ
  ins-to-ext {σ = σ} (zero p~) =
    -- FIXME: This is where Agda's termination checker gets upset.
    --        We need to convert `Nf Γ τ` (which is a variable) into
    --        `Nf Γ σ`, and we have `τ ~ σ`.
    let
      r = sound-fun (sym~ p~)
      q = appnf r (nvar $ ext-var {σ = σ} v₀)
    in q
  ins-to-ext (suc i) = ins-to-ext i

  ext-wk-nf' : (v : τ ∈ Γ) → Nf (ext σ (Γ / v)) δ → Nf (ext σ Γ) δ
  ext-wk-nf' {σ = base x} v e = wknf v e
  ext-wk-nf' {σ = σ ⇒ σ₁} v e = ext-wk-nf' {σ = σ₁} (vₛ v) e

  ext-wk-sp' : (v : τ ∈ Γ) → Sp (ext σ (Γ / v)) τ' σ' → Sp (ext σ Γ) τ' σ'
  ext-wk-sp' {σ = base x} v s = wksp v s
  ext-wk-sp' {σ = σ ⇒ σ₁} v s = ext-wk-sp' {σ = σ₁} (vₛ v) s


  ext-wk-nfi : Nf (ext σ Γ) τ → Ins δ σ σ' → Nf (ext σ' Γ) τ
  ext-wk-nfi {σ = σ} e (zero x) = ext-wk-nf' {σ = σ} v₀ e
  ext-wk-nfi e (suc i) = ext-wk-nfi e i

  ext-wk-spi : Sp (ext σ Γ) τ (base i) → Ins δ σ σ' → Sp (ext σ' Γ) τ (base i)
  ext-wk-spi ε i = ε
  ext-wk-spi {σ = σ} (x ◃ s) (zero x₁) = ext-wk-nf' {σ = σ} v₀ x ◃ ext-wk-sp' {σ = σ} v₀ s
  ext-wk-spi (x ◃ s) (suc i) = ext-wk-nfi x i ◃ ext-wk-spi s i

  sp-step : Sp (ext σ Γ) τ (base i) → Ins δ σ σ' → Sp (ext σ' Γ) (δ ⇒ τ) (base i)
  sp-step s i = ins-to-ext i ◃ ext-wk-spi s i

  soundsp : τ ~ σ → Sp (ext σ (Γ )) τ (base $ cod τ)
  soundsp zero = ε
  soundsp {τ} {σ} (suc p~ i) = sp-step (soundsp p~) i

  sound-fun {τ} {σ} p~ =
    let
      sp = soundsp {Γ = _ ▹ τ} p~
      -- TODO: try to get rid of this conversion
      sp' = subst (λ x → Sp (ext σ _) τ (base x)) (cod~ p~) sp
    in lam (foldnf (ne (app (ext-var {σ = σ} v₀) sp')))

  sound-funε : τ ~ σ → Nf ε (τ ⇒ σ)
  sound-funε = sound-fun


sound-retr : (στ : σ ~ τ) → (sound-funε στ) ∘-nf (sound-funε (sym~ στ)) ≡ id-nf
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
