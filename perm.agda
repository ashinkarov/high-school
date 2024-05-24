open import Data.List
open import Data.Product
open import Data.Fin 

variable A : Set
variable a b : A
variable as bs cs as' bs' cs' : List A

data Add {A : Set} : A → List A → List A → Set where
  zero : Add a as (a ∷ as) 
  suc : Add a as bs → Add a (b ∷ as) (b ∷ bs)

data Perm {A : Set} : List A → List A → Set where
  nil : Perm {A} [] []
  cons : Perm as cs → Add a cs bs → Perm (a ∷ as) bs

perm→fun : Perm as bs → Fin (length as) → Fin (length bs)
perm→fun p = {!!}

reflPerm : Perm as as
reflPerm {as = []} = nil
reflPerm {as = a ∷ as} = cons (reflPerm {as = as}) zero

addLem : Add a as bs → Add b bs cs
       → Σ (List A) (λ ds → Add b as ds × Add a ds cs)
addLem zero zero = _ , zero , suc zero
addLem zero (suc q) = _ , q , zero
addLem (suc p) zero = _ , zero , suc (suc p)
addLem (suc p) (suc q) with addLem p q
...                      |  bs' , p' , q' = _ , suc p' , suc q'

transLem : Perm bs cs → Add a bs' bs
           → Σ (List A) (λ cs' → Perm bs' cs' × Add a cs' cs)
transLem (cons p x) zero = _ , p , x
transLem (cons p x) (suc q) with transLem p q
... | cs' , p' , q' with addLem q' x
...                   |   ds , y , z = ds , cons p' y , z

transPerm : Perm as bs → Perm bs cs → Perm as cs
transPerm nil nil = nil
transPerm (cons p x) q with transLem q x
... | (cs' , q' , y) = cons (transPerm p q') y

symLem : Perm cs as → Add a cs bs → Perm bs (a ∷ as)
symLem p zero = cons p zero
symLem (cons p x) (suc q) = cons (symLem p q) (suc x) 

symPerm : Perm as bs → Perm bs as
symPerm nil = nil
symPerm (cons p x) = symLem (symPerm p) x

remPerm : Perm (a ∷ as) (a ∷ bs) → Perm as bs
remPerm (cons p zero) = p
remPerm (cons p (suc x)) = transPerm p (cons reflPerm x) 

open import Relation.Binary.PropositionalEquality

easy : Perm (a ∷ []) (b ∷ []) → a ≡ b
easy (cons nil zero) = refl

add++lem : Add a as bs → Add a (as ++ cs) (bs ++ cs)
add++lem zero = zero
add++lem (suc p) = suc (add++lem p)

cong++ : Perm as bs → Perm as' bs' → Perm (as ++ as') (bs ++ bs')
cong++ nil q = q
cong++ (cons p x) q = cons (cong++ p q) (add++lem x)

swap-perm : Perm (a ∷ b ∷ as) (b ∷ a ∷ as)
swap-perm = cons reflPerm (suc zero)
