open import Function
open import Data.Fin 
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum hiding ([_,_])
open import Data.Product
open import Data.Empty

module lam (n : ℕ) where

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


_++_ : Con → Con → Con
Γ ++ ε       = Γ
Γ ++ (Δ ▹ x) = (Γ ++ Δ) ▹ x

-- Normal forms
data Nf : Con → Ty → Set
data Sub : Con → Con → Set where
  ε   : Sub Γ ε
  _,_ : Sub Γ Δ → Nf Γ τ → Sub Γ (Δ ▹ τ)


data Nf where
  lam : (Ψ ⇒ i) ∈ (Γ ++ Δ) → Sub (Γ ++ Δ) Ψ → Nf Γ (Δ ⇒ i)


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

data _⊆_ : Con → Con → Set where
  ε    : ε ⊆ ε
  skip : Γ ⊆ Δ → Γ ⊆ (Δ ▹ τ)
  keep : Γ ⊆ Δ → (Γ ▹ τ) ⊆ (Δ ▹ τ)

⊆-eq : Γ ⊆ Γ
⊆-eq {ε}     = ε
⊆-eq {Γ ▹ τ} = keep ⊆-eq

⊆-ε : ε ⊆ Γ
⊆-ε {ε}     = ε
⊆-ε {Γ ▹ τ} = skip ⊆-ε

⊆-skip-++-r : Γ ⊆ Δ → Γ ⊆ (Δ ++ Ψ)
⊆-skip-++-r {Ψ = ε}     s = s
⊆-skip-++-r {Ψ = Ψ ▹ τ} s = skip (⊆-skip-++-r s)

⊆-skip-++-l : Γ ⊆ Δ → Γ ⊆ (Ψ ++ Δ)
⊆-skip-++-l ε        = ⊆-ε
⊆-skip-++-l (skip s) = skip (⊆-skip-++-l s)
⊆-skip-++-l (keep s) = keep (⊆-skip-++-l s)

⊆-cong-++-l : Γ ⊆ Δ → (Ψ ++ Γ) ⊆ (Ψ ++ Δ)
⊆-cong-++-l ε        = ⊆-eq
⊆-cong-++-l (skip s) = skip (⊆-cong-++-l s)
⊆-cong-++-l (keep s) = keep (⊆-cong-++-l s)

⊆-cong-++-r : Γ ⊆ Δ → (Γ ++ Ψ) ⊆ (Δ ++ Ψ)
⊆-cong-++-r {Ψ = ε}     s = s
⊆-cong-++-r {Ψ = Ψ ▹ τ} s = keep (⊆-cong-++-r s)

r-⊆-++ : Δ ⊆ (Γ ++ Δ)
r-⊆-++ = ⊆-skip-++-l ⊆-eq

l-⊆-++ : Γ ⊆ (Γ ++ Δ)
l-⊆-++ = ⊆-skip-++-r ⊆-eq

-- This might be easier to use this self-contained formulation
-- in the proofs, beacuse it kind of inlines ⊆-eq.
--l-⊆-++ : SL Γ (Γ ++ Δ)
--l-⊆-++ {ε}     {Δ = ε}     = ε
--l-⊆-++ {Γ ▹ τ} {Δ = ε}     = keep l-⊆-++
--l-⊆-++ {Γ ▹ _} {Δ = Δ ▹ τ} = skip l-⊆-++


-- Γ / v computes a new context which is Γ without the variable v
_/_ : (Γ : Con) → τ ∈ Γ → Con
(Γ ▹ τ) / v₀    = Γ
(Γ ▹ τ) / vₛ v  = (Γ / v) ▹ τ

/⇒⊆ : (v : τ ∈ Γ) → (Γ / v) ⊆ Γ
/⇒⊆ v₀     = skip ⊆-eq
/⇒⊆ (vₛ v) = keep (/⇒⊆ v)

ren : Γ ⊆ Δ → τ ∈ Γ → τ ∈ Δ
ren (skip s) x      = vₛ (ren s x)
ren (keep s) v₀     = v₀
ren (keep s) (vₛ x) = vₛ (ren s x)

-- Specialcase of renaming that we use in Eq,
-- but we cannot simply write `wkv = ren (/⇒⊆ v)` because
-- Γ ⊆ Γ is not a constructor.
wkv  : (v : τ ∈ Γ) → σ ∈ (Γ / v) → σ ∈ Γ
wk   : (v : τ ∈ Γ) → Nf (Γ / v) σ → Nf Γ σ

wkv v₀     w      = vₛ w
wkv (vₛ v) v₀     = v₀
wkv (vₛ v) (vₛ w) = vₛ (wkv v w)


emb : Γ ⊆ Ψ → Sub Γ Δ → Sub Ψ Δ
wk-sl : Γ ⊆ Δ → Nf Γ τ → Nf Δ τ
wk-sl ε        e          = e
wk-sl (skip s) (lam v sp) = lam (ren (⊆-cong-++-r (skip s)) v) (emb (⊆-cong-++-r (skip s)) sp)
wk-sl (keep s) (lam v sp) = lam (ren (⊆-cong-++-r (keep s)) v) (emb (⊆-cong-++-r (keep s)) sp)

emb sl        ε        = ε
emb ε         (s , x)  = s , x
emb (skip sl) (s , x)  = emb (skip sl) s , wk-sl (skip sl) x
emb (keep sl) (s , x)  = emb (keep sl) s , wk-sl (keep sl) x

wk v e = wk-sl (/⇒⊆ v) e

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


split : τ ∈ (Γ ++ Δ) → τ ∈ Γ ⊎ τ ∈ Δ
split {Δ = ε} v = inj₁ v
split {Δ = Δ ▹ x} v₀ = inj₂ v₀
split {Δ = Δ ▹ x} (vₛ v) with split {Δ = Δ} v
... | inj₁ v = inj₁ v
... | inj₂ v = inj₂ (vₛ v)


-- Shift part of the context into the type and back
-- This is a different way to look at the same term
lshift : Nf Γ (Δ ⇒ i) → Nf (Γ ++ Δ) (ε ⇒ i)
lshift {Δ = ε}     e          = e
lshift {Δ = Δ ▹ τ} (lam v sp) = lam v sp

rshift : Nf (Γ ++ Δ) (ε ⇒ i) → Nf Γ (Δ ⇒ i)
rshift {Δ = ε}     e          = e
rshift {Δ = Δ ▹ τ} (lam v sp) = lam v sp

-- wk-vars : SL Δ Ψ → Nf Γ (Δ ⇒ i) → Nf Γ (Ψ ⇒ i)
-- wk-vars ε (lam v sp) = lam v sp
-- wk-vars (skip sl) (lam v sp) = lam (ren (skip (⊆-cong-++-l sl)) v) (emb sp (skip (⊆-cong-++-l sl)))
-- wk-vars (keep sl) (lam v sp) = lam (ren (keep (⊆-cong-++-l sl)) v) (emb sp (keep (⊆-cong-++-l sl)))


-- The interplay between ren, _++_ and l-⊆-++
-- 
-- We need these equations for the induction step inside the
-- substitution.  We can eiter use equalites (≡), or we can reduce
-- all the expressions downto ⊆
⊆-eq-id : (v : τ ∈ Γ) → ren ⊆-eq v ≡ v
⊆-eq-id v₀     = refl
⊆-eq-id (vₛ v) = cong vₛ (⊆-eq-id v)

ren-v-eq₁ : (v : τ ∈ Γ) → (Γ / v) ⊆ (Γ / ren l-⊆-++ v)
ren-v-eq₁ v₀     = ⊆-eq
ren-v-eq₁ (vₛ v) = keep (ren-v-eq₁ v)

ren-v-eq₂ : (v : τ ∈ Γ) → (Γ / ren l-⊆-++ v) ⊆ (Γ / v) 
ren-v-eq₂ v₀     = ⊆-eq
ren-v-eq₂ (vₛ v) = keep (ren-v-eq₂ v)

ren-v-to-++ : (v : τ ∈ Γ) → (Γ / v) ⊆ ((Γ ++ Δ) / ren l-⊆-++ v)
ren-v-to-++ {Δ = ε}     v = ren-v-eq₁ v -- rewrite ⊆-eq-id v = ⊆-eq
ren-v-to-++ {Δ = Δ ▹ τ} v = skip (ren-v-to-++ {Δ = Δ} v)

ren-++-to-ren-v : (v : τ ∈ Γ) → ((Γ ++ Δ) / ren l-⊆-++ v) ⊆ ((Γ / v) ++ Δ)
ren-++-to-ren-v {Δ = ε}     v = ren-v-eq₂ v -- rewrite ⊆-eq-id v = ⊆-eq
ren-++-to-ren-v {Δ = Δ ▹ τ} v = keep (ren-++-to-ren-v v)

⊆-++-assocₗ : ((Γ ++ Δ) ++ Ψ) ⊆ (Γ ++ (Δ ++ Ψ))
⊆-++-assocₗ {Ψ = ε}     = ⊆-eq
⊆-++-assocₗ {Ψ = Ψ ▹ x} = keep (⊆-++-assocₗ {Ψ = Ψ})

⊆-++-assocᵣ : (Γ ++ (Δ ++ Ψ)) ⊆ ((Γ ++ Δ) ++ Ψ)
⊆-++-assocᵣ {Ψ = ε}     = ⊆-eq
⊆-++-assocᵣ {Ψ = Ψ ▹ τ} = keep (⊆-++-assocᵣ {Ψ = Ψ})

-- Thes properties are not needed yet
module _ where
  _∙_ : Ψ ⊆ Δ → Γ ⊆ Ψ → Γ ⊆ Δ
  ε      ∙ p      = p
  skip s ∙ p      = skip (s ∙ p)
  keep s ∙ skip p = skip (s ∙ p)
  keep s ∙ keep p = keep (s ∙ p)

  ++-assoc : (Γ ++ Δ) ++ Ψ ≡ Γ ++ (Δ ++ Ψ)
  ++-assoc {Ψ = ε}     = refl
  ++-assoc {Ψ = Ψ ▹ τ} = cong (_▹ τ) (++-assoc {Ψ = Ψ})

  Γ▹τ⊈Γ : (Γ ++ (Δ ▹ τ)) ⊆ Γ → ⊥
  Γ▹τ⊈Γ {.(Γ ▹ τ)} {Δ} {τ₁} (skip {Δ = Γ} {τ} s) 
    rewrite ++-assoc {Γ} {ε ▹ τ} {Δ ▹ τ₁} = Γ▹τ⊈Γ s
  Γ▹τ⊈Γ {.((Δ ▹ x) ▹ _)} {ε} (keep {Δ = Δ ▹ x} (skip s)) = Γ▹τ⊈Γ s
  Γ▹τ⊈Γ {.((Δ ▹ x) ▹ x)} {ε} (keep {Δ = Δ ▹ x} (keep s)) = Γ▹τ⊈Γ s
  Γ▹τ⊈Γ {.(Γ ▹ τ)} {Δ ▹ x} {τ} (keep {Δ = Γ} s) 
    rewrite ++-assoc {Γ} {ε ▹ τ} {Δ ▹ x} = Γ▹τ⊈Γ s

  ⊆⇒≡ : Γ ⊆ Δ → Δ ⊆ Γ → Γ ≡ Δ
  ⊆⇒≡ ε p               = refl
  ⊆⇒≡ (skip s) p        = ⊥-elim (Γ▹τ⊈Γ (s ∙ p))
  ⊆⇒≡ (keep s) (skip p) = ⊥-elim (Γ▹τ⊈Γ (s ∙ p))
  ⊆⇒≡ (keep s) (keep p) = cong₂ _▹_ (⊆⇒≡ s p) refl


sub-sp : (v : τ ∈ Γ) (sp : Sub Γ Δ) → Nf (Γ / v) τ → Sub (Γ / v) Δ

-- Apply the function to the arguments.
app  : Nf Γ (Δ ⇒ i) → Sub Γ Δ → Nf Γ (ε ⇒ i)
app₁ : Nf Γ ((Δ ▹ τ) ⇒ i) → Nf Γ τ → Nf Γ (Δ ⇒ i)

app₁ (lam v₀ sp) e = 
  let 
    -- Morally we are doing `app e sp`
    r = sub-sp v₀ sp (wk-sl l-⊆-++ e)
    u = wk-sl l-⊆-++ e
    x = app u r
  in rshift x
app₁ (lam (vₛ v) sp) e = lam v (sub-sp v₀ sp (wk-sl l-⊆-++ e))

app {Δ = ε}     e s       = e
app {Δ = Δ ▹ τ} e (s , x) = app (app₁ e x) s


-- sub₀ : (v : τ ∈ Γ) (e : Nf Γ (base i)) (e₁ : Nf (Γ / v) τ) → Nf (Γ / v) (base i)
-- sub₀ v (lam w sp) e₁ with eq? v w
-- ... | eq = app e₁ (sub-sp v sp e₁)
-- ... | neq .v y = lam y (sub-sp v sp e₁)


-- sub₁ : (v : τ ∈ Γ) (e : Nf Γ ((ε ▹ δ) ⇒ i)) (e₁ : Nf (Γ / v) τ) → Nf (Γ / v) ((ε ▹ δ) ⇒ i)
-- sub₁ v (lam w sp) e₁ with eq? (vₛ v) w
-- ... | eq = 
--   let 
--     r = wk-sl (skip ⊆-eq) e₁
--     u = app r (sub-sp (vₛ v) sp r)
--   in rshift u
-- ... | neq .(vₛ v) y = lam y (sub-sp (vₛ v) sp (wk-sl (skip ⊆-eq) e₁))

-- ren-++-≡-ren-v : (v : τ ∈ Γ) → ((Γ ++ Δ) / ren l-⊆-++ v) ≡ ((Γ / v) ++ Δ)
-- ren-++-≡-ren-v {Δ = ε} v rewrite ⊆-eq-id v = refl
-- ren-++-≡-ren-v {Δ = Δ ▹ x} v = cong (_▹ x) (ren-++-≡-ren-v v)


sub : (v : τ ∈ Γ) (e : Nf Γ σ) (e₁ : Nf (Γ / v) τ) → Nf (Γ / v) σ

sub-sp-++ : (v : τ ∈ Γ) (sp : Sub (Γ ++ Δ) Ψ) → Nf (Γ / v) τ → Sub ((Γ / v) ++ Δ) Ψ
sub-sp-++ {Δ = ε}     v sp e = sub-sp v sp e
sub-sp-++ {Δ = Δ ▹ x} v ε  e = ε
sub-sp-++ {Δ = Δ ▹ x} v (_,_ {τ = τ} sp x₁) e
  = sub-sp-++ v sp e 
  , let k = sub (ren l-⊆-++ v) x₁ (wk-sl (ren-v-to-++ {Δ = Δ ▹ x} v) e) 
    in wk-sl (keep (ren-++-to-ren-v v)) k

-- TODO: Upgrade to general Γ ⊆ Δ → Nf Γ → Nf Δ
wk-ctx : Nf Γ τ → Nf (Γ ++ Δ) τ
wk-ctx {Δ = ε} t = t
wk-ctx {Δ = Δ ▹ x} t = wk v₀ (wk-ctx t)


sub {σ = Δ ⇒ i} v (lam w sp) e₁ with split {Δ = Δ} w
... | inj₂ y = lam (ren r-⊆-++ y) (sub-sp-++ v sp e₁)
... | inj₁ x with eq? v x
... | eq = let 
  sp′ = (sub-sp-++ v sp e₁)
  r = app (wk-ctx e₁) sp′
  in rshift r
... | neq .v y = lam (ren l-⊆-++ y) (sub-sp-++ v sp e₁) 


sub-sp v ε e₁ = ε
sub-sp v (sp , x) e₁ = sub-sp v sp e₁ , sub v x e₁


-- TODO, we can inline these helpers
rshiftx : Nf (Γ ++ Δ) (Ψ ⇒ i) → Nf Γ ((Δ ++ Ψ) ⇒ i)
rshiftx {Γ} {Δ} {Ψ} e =
  let 
    e₁ = lshift e
    e₂ = wk-sl (⊆-++-assocₗ {Γ} {Δ}) e₁
  in rshift e₂

lshiftx : Nf Γ ((Δ ++ Ψ) ⇒ i) → Nf (Γ ++ Δ) (Ψ ⇒ i)
lshiftx {Γ} {Δ} {Ψ} e =
  let
    e₁ = lshift e
    e₂ = wk-sl (⊆-++-assocᵣ {Γ} {Δ}) e₁
  in rshift e₂



_[_] : Nf Γ σ → Sub Δ Γ → Nf Δ σ
_[_] {ε}     e s = wk-sl ⊆-ε e
_[_] {Γ ▹ τ} {Ψ ⇒ i} {Δ} e (s , x) =
  let
    e₁ : Nf Γ (((ε ▹ τ) ++ Ψ) ⇒ i)
    e₁ = rshiftx e

    e₂ = e₁ [ s ]

    e₃ = Nf (Δ ▹ τ) (Ψ ⇒ i)
    e₃ = lshiftx {Δ = ε ▹ τ} e₂

  in sub v₀ e₃ x


-- # Main theorem

-- XXX this looks complicated, can we simplify this a bit?
↑_ : Nf Γ σ → Nf (Γ ▹ τ) σ
↑_ = wk v₀

sub-p : Sub Δ Γ → Sub (Δ ▹ τ) Γ
sub-p ε       = ε
sub-p (s , x) = sub-p s , (↑ x)

sub-eq : Γ ⊆ Δ → Sub Δ Γ
sub-eq ε                    = ε
sub-eq (skip s)             = sub-p (sub-eq s)
sub-eq (keep {τ = Ψ ⇒ i} s) = sub-p (sub-eq s) , lam (ren l-⊆-++ v₀) (sub-eq r-⊆-++)

-- This works.
id-nf : Nf (Γ ▹ τ) τ
id-nf {τ = Δ ⇒ i} = lam (ren l-⊆-++ v₀) (sub-eq r-⊆-++)

record _≅_ (τ σ : Ty) : Set where
  field
    φ  : Nf (ε ▹ τ) σ
    ψ  : Nf (ε ▹ σ) τ
    Φψ : φ [ ε , ψ ] ≡ id-nf
    ψφ : ψ [ ε , φ ] ≡ id-nf

-- TODO
thm : τ ~ σ ↔ τ ≅ σ
thm = {!!}



