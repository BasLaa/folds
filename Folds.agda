module Folds where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Properties using (++-identityˡ)
open import Function using (_∘_; flip; id; _$_)

_≐_ : {A B : Set} → (A → B) → (A → B) → Set 
f ≐ g = ∀ x → f x ≡ g x
infix 4 _≐_

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr _⊕_ e []  = e
foldr _⊕_ e (x ∷ xs) = x ⊕ (foldr _⊕_ e xs)


foldr-universal : ∀ {A B : Set} (h : List A -> B) _⊕_ e ->
  (h [] ≡ e) -> (∀ x xs -> h (x ∷ xs) ≡ x ⊕ (h xs)) -> (h ≐ foldr _⊕_ e)
foldr-universal h f e base step [] = base
foldr-universal h f e base step (x ∷ xs) =
    h (x ∷ xs)
  ≡⟨ step x xs ⟩
    f x (h xs)
  ≡⟨ cong (f x) (foldr-universal h f e base step xs)⟩
    f x (foldr f e xs)
  ≡⟨⟩
    foldr f e (x ∷ xs)
  ∎

foldr-fusion : ∀ {A B C : Set} (g : B -> C) (_⊕_ : A -> B -> B) (_*_ : A -> C -> C) (e : B) ->
  (∀ a b -> g (a ⊕ b) ≡ a * (g b)) -> g ∘ (foldr _⊕_ e) ≐ foldr _*_ (g e)
foldr-fusion h _⊕_ _*_ e fuse =
    foldr-universal (h ∘ (foldr _⊕_ e)) _*_ (h e) refl (λ x xs -> fuse x (foldr _⊕_ e xs))


map : {A B : Set} -> (A -> B) -> (List A -> List B)
map f = foldr (_∷_ ∘ f) []

map-foldr-fusion : ∀ {A B C : Set} (_⊕_ : A -> B -> B) (g : C -> A) (e : B) ->
  (foldr _⊕_ e) ∘ (map g) ≐ foldr (_⊕_ ∘ g) e
map-foldr-fusion _ _ _ [] = refl
map-foldr-fusion _⊕_ g e (x ∷ xs) =
    (foldr _⊕_ e) (map g (x ∷ xs))
  ≡⟨⟩
    (foldr _⊕_ e) (g x ∷ map g xs)
  ≡⟨⟩
    (g x) ⊕ (foldr _⊕_ e (map g xs))
  ≡⟨ cong ((_⊕_) (g x)) (map-foldr-fusion _⊕_ g e xs) ⟩
    (g x) ⊕ (foldr (_⊕_ ∘ g) e xs)
  ≡⟨⟩ 
    foldr (_⊕_ ∘ g) e (x ∷ xs)
  ∎


data RList (A : Set) : Set where
  nil : RList A
  snoc : RList A -> A -> RList A

foldl : {A B : Set} -> (B -> A -> B) -> B -> List A -> B
foldl _⊕_ e [] = e
foldl _⊕_ e (x ∷ xs) = foldl _⊕_ (e ⊕ x) xs

foldl' : {A B : Set} -> (B -> A -> B) -> B -> RList A -> B
foldl' _⊕_ e nil = e
foldl' _⊕_ e (snoc xs x) = foldl' _⊕_ e xs ⊕ x


foldl-universal : ∀ {A B : Set} (h : B -> List A -> B) _⊕_ ->
  (∀ b -> (h b [] ≡ b)) -> (∀ b x xs -> h b (x ∷ xs) ≡ h (b ⊕ x) xs) -> (∀ b -> h b ≐ foldl _⊕_ b)
foldl-universal h _⊕_ base step b [] = base b
foldl-universal h _⊕_ base step b (x ∷ xs) = 
    h b (x ∷ xs)
  ≡⟨ step b x xs ⟩
    h (b ⊕ x) xs
  ≡⟨ foldl-universal h _⊕_ base step (b ⊕ x) xs ⟩
    foldl _⊕_ (b ⊕ x) xs
  ≡⟨⟩
    foldl _⊕_ b (x ∷ xs)
  ∎

foldl-fusion : ∀ {A B C : Set} (f : B -> C) (_⊕_ : B -> A -> B) (_*_ : C -> A -> C) ->
  (∀ b a -> f (b ⊕ a) ≡ (f b) * a) -> (∀ e -> f ∘ foldl _⊕_ e ≐ foldl _*_ (f e))
foldl-fusion f _⊕_ _*_ h e [] = refl
foldl-fusion f _⊕_ _*_ h e (x ∷ xs) =
    f (foldl _⊕_ e (x ∷ xs))
  ≡⟨⟩
    f (foldl _⊕_ (e ⊕ x) xs)
  ≡⟨ foldl-fusion f _⊕_ _*_ h (e ⊕ x) xs ⟩
    foldl _*_ (f (e ⊕ x)) xs
  ≡⟨ cong-app (cong (foldl _*_) (h e x)) xs ⟩
    foldl _*_ (f e * x) xs
  ≡⟨⟩
    foldl _*_ (f e) (x ∷ xs)
  ∎


second-duality : ∀ {A B : Set} (_⊕_ : A -> B -> B) (_*_ : B -> A -> B) (e : B) ->
  (∀ a b c -> a ⊕ (b * c) ≡ (a ⊕ b) * c) -> (∀ a' -> a' ⊕ e ≡ e * a') -> (foldr _⊕_ e ≐ foldl _*_ e)
second-duality _⊕_ _*_ e assoc neu [] = refl
second-duality _⊕_ _*_ e assoc neu (x ∷ xs) =
    foldr _⊕_ e (x ∷ xs)
  ≡⟨⟩
    x ⊕ (foldr _⊕_ e xs)
  ≡⟨ cong (_⊕_ x) (second-duality _⊕_ _*_ e assoc neu xs) ⟩
    x ⊕ (foldl _*_ e xs)
  ≡⟨ (foldl-fusion (_⊕_ x) _*_ _*_ (assoc x) e) xs ⟩
    foldl _*_ (x ⊕ e) xs
  ≡⟨ cong-app (cong (foldl _*_) (neu x)) xs ⟩
    foldl _*_ (e * x) xs
  ≡⟨⟩
    foldl _*_ e (x ∷ xs)
  ∎


reverse : {A : Set} -> List A -> List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])


foldl-concat : ∀ {A B : Set} (_⊕_ : B -> A -> B) (e : B) (xs ys : List A) ->
  (foldl _⊕_ e (xs ++ ys) ≡ foldl _⊕_ (foldl _⊕_ e xs) ys)
foldl-concat _⊕_ e [] ys = 
    foldl _⊕_ e ([] ++ ys)
  ≡⟨ cong (foldl _⊕_ e) (++-identityˡ ys) ⟩
    foldl _⊕_ e ys
  ≡⟨⟩
    foldl _⊕_ (foldl _⊕_ e []) ys
  ∎
foldl-concat _⊕_ e (x ∷ xs) ys =
    foldl _⊕_ e ((x ∷ xs) ++ ys)
  ≡⟨⟩
    foldl _⊕_ e (x ∷ (xs ++ ys))
  ≡⟨⟩
    foldl _⊕_ (e ⊕ x) (xs ++ ys)
  ≡⟨ foldl-concat _⊕_ (e ⊕ x) xs ys ⟩
    foldl _⊕_ (foldl _⊕_ (e ⊕ x) xs) ys
  ≡⟨⟩
    foldl _⊕_ (foldl _⊕_ e (x ∷ xs)) ys
  ∎

third-duality : ∀ {A B : Set} (_⊕_ : A -> B -> B) (e : B) (xs : List A) ->
  (foldr _⊕_ e xs ≡ foldl (flip _⊕_) e (reverse xs))
third-duality _⊕_ e [] = refl
third-duality _⊕_ e (x ∷ xs) =
    foldr _⊕_ e (x ∷ xs)
  ≡⟨⟩
    x ⊕ (foldr _⊕_ e xs)
  ≡⟨ cong (_⊕_ x) (third-duality _⊕_ e xs) ⟩
    x ⊕ (foldl (flip _⊕_) e (reverse xs))
  ≡⟨⟩
    foldl (flip _⊕_) (x ⊕ (foldl (flip _⊕_) e (reverse xs))) []
  ≡⟨⟩
    foldl (flip _⊕_) (foldl (flip _⊕_) e (reverse xs)) (x ∷ [])
  ≡⟨ sym (foldl-concat (flip _⊕_) e (reverse xs) (x ∷ [])) ⟩
    foldl (flip _⊕_) e (reverse xs ++ (x ∷ []))
  ≡⟨⟩
    foldl (flip _⊕_) e (reverse (x ∷ xs))
  ∎


foldr-leftwards : ∀ {A B : Set} (h : List A -> B) (_⊕_ : A -> B -> B) (e : B) ->
  (h ≐ foldr _⊕_ e) -> (∀ (xs xs' : List A) (a : A) -> h xs ≡ h xs' -> h (a ∷ xs) ≡ h (a ∷ xs'))
foldr-leftwards h _⊕_ e m xs xs' a n =
    h (a ∷ xs)
  ≡⟨ m (a ∷ xs) ⟩
    a ⊕ (foldr _⊕_ e xs)
  ≡⟨ cong (_⊕_ a) (sym (m xs))  ⟩
    a ⊕ h xs
  ≡⟨ cong (_⊕_ a) n ⟩
    a ⊕ h xs'
  ≡⟨ cong (_⊕_ a) (m xs') ⟩
    foldr _⊕_ e (a ∷ xs')
  ≡⟨ sym (m (a ∷ xs')) ⟩
    h (a ∷ xs')
  ∎


record Monoid (A : Set) : Set where
  field
    ε : A
    _∙_   : A → A → A

    ε-identity-left : ∀ (x : A) → ε ∙ x ≡ x
    ε-identity-right : ∀ (x : A) → x ∙ ε ≡ x
    ∙-assoc : ∀ (x y z : A) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

  ε-identity : (x : A) → ε ∙ x ≡ x ∙ ε
  ε-identity x = trans (ε-identity-left x) (sym (ε-identity-right x))
open Monoid {{...}} public

foldMap : ∀ {A B : Set} -> {{mb : Monoid B}} → (A → B) → List A → B
foldMap f []       = ε
foldMap f (x ∷ xs) = f x ∙ foldMap f xs


foldMap-foldr-map : ∀ {A B : Set} -> {{mb : Monoid B}} -> ∀ (f : A -> B) ->
  foldMap f ≐ foldr _∙_ ε ∘ map f
foldMap-foldr-map f [] = refl
foldMap-foldr-map f (x ∷ xs) = cong (_∙_ (f x)) (foldMap-foldr-map f xs) 


first-hom-theorem : ∀ {A B : Set} -> {{mb : Monoid B}} -> ∀ (f : A -> B) ->
  foldMap f ≐ foldMap id ∘ map f
first-hom-theorem f [] = refl
first-hom-theorem f (x ∷ xs) =
    foldMap f (x ∷ xs)
  ≡⟨⟩
    f x ∙ foldMap f xs
  ≡⟨ cong (_∙_ (f x)) (first-hom-theorem f xs) ⟩
    f x ∙ (foldMap id (map f xs))
  ≡⟨⟩
    foldMap id (map f (x ∷ xs))
  ∎

second-hom-theorem-right : ∀ {A B : Set} -> {{mb : Monoid B}} -> ∀ (f : A -> B) ->
  foldMap f ≐ foldr (λ a b -> f a ∙ b) ε
second-hom-theorem-right f [] = refl
second-hom-theorem-right f (x ∷ xs) =
    foldMap f (x ∷ xs)
  ≡⟨⟩
    f x ∙ foldMap f xs
  ≡⟨ cong (_∙_ (f x)) (second-hom-theorem-right f xs) ⟩
    f x ∙ foldr (λ a b -> f a ∙ b) ε xs
  ≡⟨⟩
    (λ a b -> f a ∙ b) x (foldr (λ a b -> f a ∙ b) ε xs)
  ≡⟨⟩
    foldr (λ a b -> f a ∙ b) ε (x ∷ xs)
  ∎

second-hom-theorem-folds : ∀ {A B : Set} -> {{mb : Monoid B}} -> ∀ (f : A -> B) ->
  foldr (λ a b -> f a ∙ b) ε ≐ foldl (λ b a -> b ∙ f a) ε
second-hom-theorem-folds f = 
  second-duality 
    (λ a b -> f a ∙ b) (λ b a -> b ∙ f a) ε 
    (λ a b c -> sym (∙-assoc (f a) b (f c))) 
    (λ x -> sym (ε-identity (f x)))

second-hom-theorem-left : ∀ {A B : Set} -> {{mb : Monoid B}} -> ∀ (f : A -> B) ->
  foldMap f ≐ foldl (λ b a -> b ∙ f a) ε
second-hom-theorem-left f xs = 
  trans (second-hom-theorem-right f xs) (second-hom-theorem-folds f xs)


instance
  FuncMonoid : ∀ {A : Set} → Monoid (A -> A)
  ε {{FuncMonoid}} = id
  _∙_   {{FuncMonoid}} f g = f ∘ g
  ε-identity-left {{FuncMonoid}} f = refl
  ε-identity-right {{FuncMonoid}} f = refl
  ∙-assoc {{FuncMonoid}} f g h = refl

trick : ∀ {A B : Set} (_⊕_ : A -> B -> B) (e : B) (xs : List A) ->
  foldr _⊕_ e xs ≡ (foldMap _⊕_ xs) e
trick _⊕_ e xs =
    foldr _⊕_ e xs
  ≡⟨ sym (map-foldr-fusion _$_ _⊕_ e xs) ⟩
    foldr _$_ e (map _⊕_ xs)
  ≡⟨ sym (foldr-fusion (λ f -> f $ e) (λ f g -> f ∘ g) (λ f x -> f $ x) id (λ a b -> refl) (map _⊕_ xs)) ⟩
    (foldr (λ f g -> f ∘ g) id (map _⊕_ xs)) e
  ≡⟨ cong-app (sym (foldMap-foldr-map _⊕_ xs)) e ⟩
    (foldMap _⊕_ xs) e
  ∎


hom-endo-hom : ∀ {A B : Set} -> {{mb : Monoid B}} -> (f : A -> B) (xs : List A) ->
  foldMap f xs ≡ (foldMap (_∙_ ∘ f) xs) ε
hom-endo-hom f xs =
    foldMap f xs
  ≡⟨ second-hom-theorem-right f xs ⟩
    foldr (λ a b -> f a ∙ b) ε xs
  ≡⟨⟩
    foldr (_∙_ ∘ f) ε xs
  ≡⟨ trick (_∙_ ∘ f) ε xs ⟩
    (foldMap (_∙_ ∘ f) xs) ε
  ∎