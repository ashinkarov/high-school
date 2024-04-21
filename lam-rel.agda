-- NOTE: This file will be merged with lam.agda.
--       I resolved non-tremination of the substitution in lam,
--       but I didn't find the time to merge the two.


open import Function
open import Data.Fin 
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum hiding ([_,_])
open import Data.Product

module lam-rel (n : ℕ) where


data Ty : Set

data Con : Set where
  ε   : Con
  _▹_ : Con → Ty → Con

data Ty where
  _⇒_ : Con → Fin n → Ty

pattern base τ = _⇒_ ε τ 

variable
  Γ Δ Ψ Ξ : Con
  τ σ δ : Ty
  i j   : Fin n

infixl 10 _∈_
data _∈_ : Ty → Con → Set where
  v₀  : τ ∈ (Γ ▹ τ)
  vₛ  : τ ∈ Γ → τ ∈ (Γ ▹ σ)


-- Merge Γ Δ Ψ = Γ ⊕ Δ = Ψ 
data Merge : Con → Con → Con → Set where
  ε    : Merge ε ε ε
  skip : Merge Γ Δ Ψ → Merge Γ (Δ ▹ τ) (Ψ ▹ τ)
  keep : Merge Γ Δ Ψ → Merge (Γ ▹ τ) Δ (Ψ ▹ τ)

_++_ : Con → Con → Con
Γ ++ ε       = Γ
Γ ++ (Δ ▹ x) = (Γ ++ Δ) ▹ x

-- Normal forms
data Nf : Con → Ty → Set
data Sub : Con → Con → Set where
  ε   : Sub Γ ε
  _,_ : Sub Γ Δ → Nf Γ τ → Sub Γ (Δ ▹ τ)

{-
data _⊆_ : Con → Con → Set where
  ε    : ε ⊆ ε
  skip : Γ ⊆ Δ → Γ ⊆ (Δ ▹ τ)
  keep : Γ ⊆ Δ → (Γ ▹ τ) ⊆ (Δ ▹ τ)

left : Γ ⊆ Δ → Con
left {Γ = Γ} m = Γ

right : Γ ⊆ Δ → Con
right {Δ = ε}     ε        = ε
right {Δ = Δ ▹ x} (skip s) = right s ▹ x
right {Δ = Δ ▹ x} (keep s) = right s

-}

data Nf where
  lam : (Ψ ⇒ i) ∈ (Γ ++ Δ) → Sub (Γ ++ Δ) Ψ → Nf Γ (Δ ⇒ i)
  --lam : Merge Γ Δ Ψ → (Ξ ⇒ i) ∈ Ψ → Sub Ψ Ξ → Nf Γ (Δ ⇒ i)
  
  --lam : ∀ {ΓΔ} → (m : Γ ⊆ ΓΔ) → (Ψ ⇒ i) ∈ (ΓΔ) → Sub (ΓΔ) Ψ → Nf (left m) (right m ⇒ i)
 
{-
ren : (s : Γ ⊆ Δ) → τ ∈ left s → τ ∈ Δ
ren (skip s) v = vₛ (ren s v)
ren (keep s) v₀ = v₀
ren (keep s) (vₛ v) = vₛ (ren s v)

ren′ : (s : Γ ⊆ Δ) → τ ∈ right s → τ ∈ Δ
ren′ (skip s) v₀ = v₀
ren′ (skip s) (vₛ v) = vₛ (ren′ s v)
ren′ (keep s) v = vₛ (ren′ s v)


_/_ : (Γ : Con) → τ ∈ Γ → Con
(Γ ▹ τ) / v₀    = Γ
(Γ ▹ τ) / vₛ v  = (Γ / v) ▹ τ

⊆-refl : Γ ⊆ Γ
⊆-refl {ε}     = ε
⊆-refl {Γ ▹ x} = keep ⊆-refl

/-⊆ : (v : τ ∈ Γ) → (Γ / v) ⊆ Γ
/-⊆ v₀ = skip ⊆-refl
/-⊆ (vₛ v) = keep (/-⊆ v)

xxx : (v : τ ∈ Γ) → (Γ / v) ⊆ Δ → ∃ λ Ψ → Γ ⊆ Ψ
xxx v₀ s = _ , keep s
xxx (vₛ v) (skip s) = let Ψ , r = xxx (vₛ v) s in _ , r
xxx (vₛ v) (keep s) = let Ψ , r = xxx v s in _ , keep r

wkv  : (v : τ ∈ Γ) → σ ∈ (Γ / v) → σ ∈ Γ
wkv v w = ren (/-⊆ v) w

wk   : (v : τ ∈ Γ) → Nf (Γ / v) σ → Nf Γ σ
wk v (lam s w sp) = let
  Ψ , r = xxx v s
  k = lam r ? ?
  in ?

-}




-- Heredetary permutation
data Insert : Con → Ty → Con → Set where
  zero : Insert Γ τ (Γ ▹ τ)
  suc  : Insert Γ τ Δ → Insert (Γ ▹ σ) τ (Δ ▹ σ)

data _~ᶜ_ : Con → Con → Set
data _~_ : Ty → Ty → Set where
  perm : Γ ~ᶜ Δ → (Γ ⇒ i) ~ (Δ ⇒ i)

data _~ᶜ_ where
  ε : ε ~ᶜ ε
  ext : Γ ~ᶜ Δ → τ ~ σ → Insert Δ σ Ψ → (Γ ▹ τ) ~ᶜ Ψ


-- Sublists
data SL : Con → Con → Set where
  ε : SL ε ε
  skip : SL Γ Δ → SL Γ (Δ ▹ τ)
  keep : SL Γ Δ → SL (Γ ▹ τ) (Δ ▹ τ)

sl-eq : SL Γ Γ
sl-eq {ε} = ε
sl-eq {Γ ▹ x} = keep sl-eq

sl-ε : SL ε Γ
sl-ε {ε} = ε
sl-ε {Γ ▹ x} = skip sl-ε

-- TODO: Brush these implementations
sl-++-l : SL Γ (Γ ++ Δ)
sl-++-l {Δ = ε} = sl-eq
sl-++-l {Δ = Δ ▹ x} = skip sl-++-l

sl-++-r : SL Δ (Γ ++ Δ)
sl-++-r {Δ = ε} = sl-ε
sl-++-r {Δ = Δ ▹ x} = keep sl-++-r

++-right : SL Γ Δ → SL (Γ ++ Ψ) (Δ ++ Ψ)
++-right {Ψ = ε} s = s
++-right {Ψ = Ψ ▹ x} s = keep (++-right s)

++-left : SL Γ Δ → SL (Ψ ++ Γ) (Ψ ++ Δ)
++-left ε = sl-eq
++-left (skip sl) = skip (++-left sl)
++-left (keep sl) = keep (++-left sl)

skip-left-++ : SL Γ Δ → SL Γ (Δ ++ Ψ)
skip-left-++ {Ψ = ε} sl = sl
skip-left-++ {Ψ = Ψ ▹ x} sl = skip (skip-left-++ sl)


_/_ : (Γ : Con) → τ ∈ Γ → Con
(Γ ▹ τ) / v₀    = Γ
(Γ ▹ τ) / vₛ v  = (Γ / v) ▹ τ

wkv  : (v : τ ∈ Γ) → σ ∈ (Γ / v) → σ ∈ Γ
wk   : (v : τ ∈ Γ) → Nf (Γ / v) σ → Nf Γ σ
↑_ : Nf Γ σ → Nf (Γ ▹ τ) σ
↑_ = wk v₀

ren : SL Γ Δ → τ ∈ Γ → τ ∈ Δ
ren (skip s) x = vₛ (ren s x)
ren (keep s) v₀ = v₀
ren (keep s) (vₛ x) = vₛ (ren s x)

sub-p : Sub Δ Γ → Sub (Δ ▹ τ) Γ
sub-p ε = ε
sub-p (s , x) = sub-p s , (↑ x)

sub-eq : SL Γ Δ → Sub Δ Γ
sub-eq ε = ε
sub-eq (skip s) = sub-p (sub-eq s)
sub-eq (keep {τ = Ψ ⇒ i} s) = sub-p (sub-eq s) , lam (ren sl-++-l v₀) (sub-eq sl-++-r)


emb : Sub Γ Δ → SL Γ Ψ → Sub Ψ Δ
wk-sl : SL Γ Δ → Nf Γ τ → Nf Δ τ
wk-sl ε e = e
wk-sl (skip s) (lam v sp) = lam (ren (++-right (skip s)) v) (emb sp (++-right (skip s)))
wk-sl (keep s) (lam v sp) = lam (ren (++-right (keep s)) v) (emb sp (++-right (keep s)))

emb ε sl = ε
emb (s , x) ε = s , x
emb (s , x) (skip sl) = emb s (skip sl) , wk-sl (skip sl) x
emb (s , x) (keep sl) = emb s (keep sl) , wk-sl (keep sl) x


wkv v₀ w = vₛ w
wkv (vₛ v) v₀ = v₀
wkv (vₛ v) (vₛ w) = vₛ (wkv v w)

wksub : (v : τ ∈ Γ) → Sub (Γ / v) Δ → Sub Γ Δ
wksub v  ε       = ε
wksub v  (s , t) = wksub v s , wk v t

sl-/ : (v : τ ∈ Γ) → SL (Γ / v) Γ
sl-/ v₀ = skip sl-eq
sl-/ (vₛ v) = keep (sl-/ v)

wkv++ : (v : τ ∈ Γ) → σ ∈ ((Γ / v) ++ Δ) → σ ∈ (Γ ++ Δ)
wkv++ v x = ren (++-right (sl-/ v)) x

wksub++ : (v : τ ∈ Γ) → Sub ((Γ / v) ++ Δ) Ψ → Sub (Γ ++ Δ) Ψ
wksub++ v s = emb s (++-right (sl-/ v))


wk v (lam t s) = lam (wkv++ v t) (wksub++ v s)

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


-- # Here is my attempt to do subsitutions

split : τ ∈ (Γ ++ Δ) → τ ∈ Γ ⊎ τ ∈ Δ
split {Δ = ε} v = inj₁ v
split {Δ = Δ ▹ x} v₀ = inj₂ v₀
split {Δ = Δ ▹ x} (vₛ v) with split {Δ = Δ} v
... | inj₁ v = inj₁ v
... | inj₂ v = inj₂ (vₛ v)


wk-vars : SL Δ Ψ → Nf Γ (Δ ⇒ i) → Nf Γ (Ψ ⇒ i)
wk-vars ε (lam v sp) = lam v sp
wk-vars (skip sl) (lam v sp) = lam (ren (skip (++-left sl)) v) (emb sp (skip (++-left sl)))
wk-vars (keep sl) (lam v sp) = lam (ren (keep (++-left sl)) v) (emb sp (keep (++-left sl)))


-- This works
sub-var : (v : τ ∈ Γ) → σ ∈ Γ → Nf (Γ / v) τ → Nf (Γ / v) σ
sub-var x y e with eq? x y
... | eq = e
sub-var {σ = Δ ⇒ i} x .(wkv x y) e | neq .x y = lam (ren sl-++-l y) (sub-eq sl-++-r)

-- This works
sub-var-++ : (v : τ ∈ Γ) → σ ∈ (Γ ++ Δ) → Nf (Γ / v) τ → Nf ((Γ / v) ++ Δ) σ
sub-var-++ {Γ = Γ} {Δ = Δ} x y e with split {Γ = Γ}{Δ} y
... | inj₁ y′ 
  = let t = sub-var x y′ e in wk-sl sl-++-l t
sub-var-++ {Γ = Γ} {σ = Ψ ⇒ i} {Δ = Δ} x y e | inj₂ y′ 
  = lam (ren (skip-left-++ {Ψ = Ψ} sl-++-r) y′) (sub-eq sl-++-r)


-- Implemented, doesn't termiante
sub-sp : (v : τ ∈ Γ) (sp : Sub Γ Δ) → Nf (Γ / v) τ → Sub (Γ / v) Δ

-- Some helper functions
sl-assoc : SL ((Γ ++ Δ) ++ Ψ) (Γ ++ (Δ ++ Ψ))
sl-assoc {Ψ = ε}     = sl-eq
sl-assoc {Ψ = Ψ ▹ x} = keep (sl-assoc {Ψ = Ψ})

sl-assoc-≡ : ((Γ ++ Δ) ++ Ψ) ≡ (Γ ++ (Δ ++ Ψ))
sl-assoc-≡ {Ψ = ε} = refl
sl-assoc-≡ {Ψ = Ψ ▹ x} = cong (_▹ x) (sl-assoc-≡ {Ψ = Ψ})


lshift : Nf Γ (Δ ⇒ i) → Nf (Γ ++ Δ) (ε ⇒ i)
lshift {Δ = ε} e = e
lshift {Δ = Δ ▹ x} (lam v sp) = lam v sp

rshift : Nf (Γ ++ Δ) (ε ⇒ i) → Nf Γ (Δ ⇒ i)
rshift {Δ = ε} e = e
rshift {Δ = Δ ▹ x} (lam v sp) = lam v sp

rshift′ : Nf (Γ ++ Δ) (Ξ ⇒ i) → Nf Γ ((Δ ++ Ξ) ⇒ i)
rshift′ {Ξ = ε} e = rshift e
rshift′ {Ξ = Ξ ▹ x} (lam v sp) = lam (ren (keep (sl-assoc {Ψ = Ξ})) v) 
                                     (emb sp (keep (sl-assoc {Ψ = Ξ})))

shift-con : (Ψ : Con) (Γ : Con) → Con
shift-con ε Γ = ε
shift-con (Ψ ▹ (Ξ ⇒ i)) Γ = shift-con Ψ Γ ▹ ((Γ ++ Ξ) ⇒ i)

shift-sub : Sub (Γ ++ Δ) Ψ → Sub Γ (shift-con Ψ Δ)
shift-sub {Ψ = ε} s = ε
shift-sub {Ψ = Ψ ▹ (Ξ ⇒ i)} (s , x) = shift-sub s , rshift′ x


-- Apply the function to the arguments.
app : Nf Γ (Δ ⇒ i) → Sub Γ Δ → Nf Γ (ε ⇒ i)

app₁ : Nf Γ ((Δ ▹ τ) ⇒ i) → Nf Γ τ → Nf Γ (Δ ⇒ i)
app₁ (lam v₀ sp) e = 
  let 
    -- Morally we are doing `app e sp`
    r = sub-sp v₀ sp (wk-sl sl-++-l e)
    u = wk-sl sl-++-l e
    x = app u r
  in rshift x
app₁ (lam (vₛ v) sp) e = lam v (sub-sp v₀ sp (wk-sl sl-++-l e))

app {Δ = ε} e s = e
app {Δ = Δ ▹ τ} e (s , x) = app (app₁ e x) s


-- sub₀ : (v : τ ∈ Γ) (e : Nf Γ (base i)) (e₁ : Nf (Γ / v) τ) → Nf (Γ / v) (base i)
-- sub₀ v (lam w sp) e₁ with eq? v w
-- ... | eq = app e₁ (sub-sp v sp e₁)
-- ... | neq .v y = lam y (sub-sp v sp e₁)


-- sub₁ : (v : τ ∈ Γ) (e : Nf Γ ((ε ▹ δ) ⇒ i)) (e₁ : Nf (Γ / v) τ) → Nf (Γ / v) ((ε ▹ δ) ⇒ i)
-- sub₁ v (lam w sp) e₁ with eq? (vₛ v) w
-- ... | eq = 
--   let 
--     r = wk-sl (skip sl-eq) e₁
--     u = app r (sub-sp (vₛ v) sp r)
--   in rshift u
-- ... | neq .(vₛ v) y = lam y (sub-sp (vₛ v) sp (wk-sl (skip sl-eq) e₁))


sl-eq-id : (v : τ ∈ Γ) → ren sl-eq v ≡ v
sl-eq-id v₀     = refl
sl-eq-id (vₛ v) = cong vₛ (sl-eq-id v)

ren-v-to-++ : (v : τ ∈ Γ) → SL (Γ / v) ((Γ ++ Δ) / ren sl-++-l v)
ren-v-to-++ {Δ = ε} v rewrite sl-eq-id v = sl-eq
ren-v-to-++ {Δ = Δ ▹ x} v = skip (ren-v-to-++ {Δ = Δ} v)

ren-++-to-ren-v : (v : τ ∈ Γ) → SL ((Γ ++ Δ) / ren sl-++-l v) ((Γ / v) ++ Δ)
ren-++-to-ren-v {Δ = ε} v rewrite sl-eq-id v = sl-eq -- TODO this rewrite can be eliminated
ren-++-to-ren-v {Δ = Δ ▹ x} v = keep (ren-++-to-ren-v v)

ren-++-≡-ren-v : (v : τ ∈ Γ) → ((Γ ++ Δ) / ren sl-++-l v) ≡ ((Γ / v) ++ Δ)
ren-++-≡-ren-v {Δ = ε} v rewrite sl-eq-id v = refl
ren-++-≡-ren-v {Δ = Δ ▹ x} v = cong (_▹ x) (ren-++-≡-ren-v v)


sub : (v : τ ∈ Γ) (e : Nf Γ σ) (e₁ : Nf (Γ / v) τ) → Nf (Γ / v) σ
sub-sp-++ : (v : τ ∈ Γ) (sp : Sub (Γ ++ Δ) Ψ) → Nf (Γ / v) τ → Sub ((Γ / v) ++ Δ) Ψ
sub-sp-++ {Δ = ε} v sp e = sub-sp v sp e
sub-sp-++ {Δ = Δ ▹ x} v ε e = ε
sub-sp-++ {Δ = Δ ▹ x} v (_,_ {τ = τ} sp x₁) e
  = sub-sp-++ v sp e 
  , let k = sub (ren sl-++-l v) x₁ (wk-sl (ren-v-to-++ {Δ = Δ ▹ x} v) e) 
    --in subst (λ G → Nf G τ) (cong (_▹ x) (ren-++-≡-ren-v v)) k
    in wk-sl (keep (ren-++-to-ren-v v)) k

wk-ctx : Nf Γ τ → Nf (Γ ++ Δ) τ
wk-ctx {Δ = ε} t = t
wk-ctx {Δ = Δ ▹ x} t = wk v₀ (wk-ctx t)


sub {σ = Δ ⇒ i} v (lam w sp) e₁ with split {Δ = Δ} w
... | inj₂ y = lam (ren sl-++-r y) (sub-sp-++ v sp e₁)
... | inj₁ x with eq? v x
... | eq = let 
  sp′ = (sub-sp-++ v sp e₁)
  r = app (wk-ctx e₁) sp′
  in rshift r
... | neq .v y = lam (ren sl-++-l y) (sub-sp-++ v sp e₁) 

-- sub : (v : τ ∈ Γ) (e : Nf Γ σ) (e₁ : Nf (Γ / v) τ) → Nf (Γ / v) σ
-- sub {σ = Δ ⇒ i} v e e₁ =
--   let
--     e′ = lshift e
--     e₁′ = wk-sl sl-++-l e₁
--     v′ = ren sl-++-l v
--     u = sub₀ v′ e′ (wk-sl (ren-v-to-++ {Δ = Δ} v) e₁′)
--     q = wk-sl (ren-++-to-ren-v v) u
--   in rshift q

--sub-sp : (v : τ ∈ Γ) (sp : Sub Γ Δ) → Nf (Γ / v) τ → Sub (Γ / v) Δ
sub-sp v ε e₁ = ε
sub-sp v (sp , x) e₁ = sub-sp v sp e₁ , sub v x e₁




-- My attempt to introduce SubList as a basis for recursion.
{-
-- Doesn't seem to work
module SubViaMinus where
  _⊝_ : (Γ : Con) → SL Δ Γ → Con
  ε ⊝ ε = ε
  (Γ ▹ x) ⊝ skip sl = (Γ ⊝ sl) ▹ x
  (Γ ▹ _) ⊝ keep sl = Γ ⊝ sl
  
  lookup : Sub Γ Δ → τ ∈ Δ → Nf Γ τ
  lookup (s , x) v₀ = x
  lookup (s , x) (vₛ v) = lookup s v
  
  
  ssub-sp : -- (v : τ ∈ Γ)   (sp : Sub Γ Δ) → Nf (Γ / v) τ → Sub (Γ / v) Δ
               (sl : SL Δ Γ) (sp : Sub Γ Ψ) → Sub (Γ ⊝ sl) Γ → Sub (Γ ⊝ sl) Ψ
  
  ssub-var : (sl : SL Δ Γ) → σ ∈ Γ → Sub (Γ ⊝ sl) Γ → Nf (Γ ⊝ sl) σ
  ssub-var sl v s = lookup s v
  
  
  ssub : -- (v : τ ∈ Γ)   (e : Nf Γ σ) (e₁ : Nf (Γ / v) τ) → Nf (Γ / v) σ
            (sl : SL Δ Γ) (e : Nf Γ σ) → (Sub (Γ ⊝ sl) Γ) → Nf (Γ ⊝ sl) σ
  ssub ε (lam v sp) s = lam v sp
  ssub (skip sl) (lam v sp) s = ?
  ssub (keep sl) (lam v sp) s = ?
-}


_[_] : Nf Γ τ → Sub Δ Γ → Nf Δ τ
lam v sp [ us ] = ?


-- # Main theorem

-- This works.
id-nf : Nf (Γ ▹ τ) τ
id-nf {τ = Δ ⇒ i} = lam (ren sl-++-l v₀) (sub-eq sl-++-r)

record _≅_ (τ σ : Ty) : Set where
  field
    φ  : Nf (ε ▹ τ) σ
    ψ  : Nf (ε ▹ σ) τ
    Φψ : φ [ ε , ψ ] ≡ id-nf
    ψφ : ψ [ ε , φ ] ≡ id-nf

-- TODO
thm : τ ~ σ ↔ τ ≅ σ
thm = {!!}



{-
module T where
  data Tys (n : ℕ) : Set
  
  data Ty (n : ℕ) : Set where
    _⇒_ : Tys n → Fin n → Ty n
  
  data Tys n where
    • : Tys n
    _,_ : Tys n → Ty n → Tys n
  
  variable m n : ℕ
  variable i j : Fin n
  variable Γ Δ Θ   : Tys n
  variable A B : Ty n
  
  _++_ : Tys n → Tys n → Tys n
  Γ ++ • = Γ
  Γ ++ (Δ , A) = (Γ ++ Δ) , A
  
  data Var : Tys n → Ty n → Set where
    zero : Var (Γ , A) A
    suc : Var Γ A → Var (Γ , B) A
  
  data Subst : Tys n → Tys m → Set
  
  -- data Ne : Tys n → Fin n → Set
  
  data Nf : Tys n → Ty n → Set where
  --  lam : Ne (Γ ++ Δ) i → Nf Γ (Δ ⇒ i)
    lam : Var (Γ ++ Δ) (Θ ⇒ i) → Subst (Γ ++ Δ) Θ → Nf Γ (Δ ⇒ i) 
    
  -- data Ne where
  --   app : Var Γ (Δ ⇒ i) → Subst Γ Δ → Ne Γ i
  
  data Subst where
    ε : Subst {n = n} Γ (• {n = n})
    _,_ : Subst Γ Δ → Nf Γ A → Subst Γ (Δ , A)
  
  --- Heredetary permutations
  
  module _{n : ℕ} where
  
    data Insert  : Tys n → Ty n → Tys n → Set where
      zero : Insert Γ A (Γ , A)
      suc : Insert Γ A Δ → Insert (Γ , B) A (Δ , B)
  
    data _~_ : Ty n → Ty n → Set 
  
    data _~s_ : Tys n → Tys n → Set where
      • : • ~s • 
      ext : Γ ~s Δ → A ~ B → Insert Δ B Θ → (Γ , A) ~s Θ
  
    data _~_ where
      perm : Γ ~s Δ → (Γ ⇒ i) ~ (Δ ⇒ i)
  
  -- Heredetary substitutions
  
  zero-nf : Nf (Γ , A) A
  zero-nf = {!!}
  
  _[_] : Nf Γ A → Subst Δ Γ → Nf Δ A
  t [ us ] = {!!}
  -- https://dl.acm.org/doi/pdf/10.1145/1863597.1863601
  
  -- definitional isomorphism
  
  record _≅_ (A B : Ty n) : Set where
    field
      φ : Nf (• , A) B
      ψ : Nf (• , B) A
      Φψ : (φ [ (ε , ψ) ]) ≡ zero-nf
      ψφ : (ψ [ (ε , φ) ]) ≡ zero-nf
  
  thm : A ~ B ↔ A ≅ B
  thm = {!!}
-}
