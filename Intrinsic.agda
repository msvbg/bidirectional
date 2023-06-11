module Intrinsic where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)

infix 2 _⟶_

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_

data Type : Set where
  `ℕ  : Type
  _⇒_ : Type → Type → Type
  _`×_  : Type → Type → Type
  _`⨄_  : Type → Type → Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
    → Γ , A ∋ A
  S_ : ∀ {Γ A B}
    → Γ ∋ A
    → Γ , B ∋ A

data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A
  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A ⇒ B
  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    → Γ ⊢ B
  `zero : ∀ {Γ} → Γ ⊢ `ℕ
  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
    → Γ ⊢ `ℕ
  caseℕ : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
    → Γ ⊢ A
  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
    → Γ ⊢ A
  `inj₁ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ A `⨄ B
  `inj₂ : ∀ {Γ A B}
    → Γ ⊢ B
    → Γ ⊢ A `⨄ B
  case⨄ : ∀ {Γ A B C}
    → Γ ⊢ A `⨄ B
    → Γ , A ⊢ C
    → Γ , B ⊢ C
    → Γ ⊢ C
  `⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
    → Γ ⊢ A `× B
  `proj₁ : ∀ {Γ A B}
    → Γ ⊢ A `× B
    → Γ ⊢ A
  `proj₂ : ∀ {Γ A B}
    → Γ ⊢ A `× B
    → Γ ⊢ B

_ : ∅ , `ℕ , `ℕ `× `ℕ  ⊢ `ℕ
_ = ` (S Z)

_ : ∅ ⊢ `ℕ ⇒ `ℕ `× `ℕ
_ = ƛ `⟨ ` Z , `suc ` Z ⟩

_ : ∅ ⊢ `ℕ `⨄ `ℕ ⇒ `ℕ
_ = ƛ case⨄ (` Z) (` Z) (` Z)

length : Context → ℕ
length ∅ =  zero
length (Γ , _) =  suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero}    (s≤s z≤n) =  A
lookup {(Γ , _)} {(suc n)} (s≤s p) =  lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n) =  Z
count {Γ , _} {(suc n)} (s≤s p) =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ} =  ` count (toWitness n∈Γ)

ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z =  Z
ext ρ (S x) =  S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → ∀ {B} → Γ ⊢ B → Δ ⊢ B
rename ρ (` x) =  ` (ρ x)
rename ρ (ƛ N) =  ƛ (rename (ext ρ) N)
rename ρ (L · M) =  (rename ρ L) · (rename ρ M)
rename ρ (`zero) =  `zero
rename ρ (`suc M) =  `suc (rename ρ M)
rename ρ (caseℕ L M N) =  caseℕ (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N) =  μ (rename (ext ρ) N)
rename ρ (`inj₁ L) = `inj₁ (rename ρ L)
rename ρ (`inj₂ R) = `inj₂ (rename ρ R)
rename ρ (`proj₁ P) = `proj₁ (rename ρ P) 
rename ρ (`proj₂ P) = `proj₂ (rename ρ P)
rename ρ (`⟨ L , R ⟩) = `⟨ (rename ρ L) , (rename ρ R) ⟩
rename ρ (case⨄ L M N) = case⨄ (rename ρ L) (rename (ext ρ) M) (rename (ext ρ) N)

exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z =  ` Z
exts σ (S x) =  rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k) =  σ k
subst σ (ƛ N) =  ƛ (subst (exts σ) N)
subst σ (L · M) =  (subst σ L) · (subst σ M)
subst σ (`zero) =  `zero
subst σ (`suc M) =  `suc (subst σ M)
subst σ (caseℕ L M N) =  caseℕ (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N) =  μ (subst (exts σ) N)
subst σ (`inj₁ L) = `inj₁ (subst σ L)
subst σ (`inj₂ R) = `inj₂ (subst σ R)
subst σ (`proj₁ P) = `proj₁ (subst σ P)
subst σ (`proj₂ P) = `proj₂ (subst σ P)
subst σ (`⟨ L , R ⟩) = `⟨ (subst σ L) , (subst σ R) ⟩
subst σ (case⨄ L M N) = case⨄ (subst σ L) (subst (exts σ) M) (subst (exts σ) N)

_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z =  M
  σ (S x) =  ` x

data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
    → Value (ƛ N)
  V-zero : ∀ {Γ}
    → Value (`zero {Γ})
  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
    → Value (`suc V)
  V-⟨,⟩ : ∀ {Γ A B} {L : Γ ⊢ A} {R : Γ ⊢ B}
    → Value L
    → Value R
    → Value (`⟨ L , R ⟩)
  V-inj₁ : ∀ {Γ A B} {VL : Γ ⊢ A}
    → Value VL
    → Value (`inj₁ {_} {_} {B} VL)
  V-inj₂ : ∀ {Γ A B} {VR : Γ ⊢ B}
    → Value VR
    → Value (`inj₂ {_} {A} {_} VR)

data _⟶_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ⟶ L′
    → L · M ⟶ L′ · M
  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M ⟶ M′
    → V · M ⟶ V · M′
  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
    → (ƛ N) · W ⟶ N [ W ]
  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M ⟶ M′
    → `suc M ⟶ `suc M′
  ξ-inj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A}
    → L ⟶ L′
    → `inj₁ {_} {_} {B} L ⟶ `inj₁ {_} {_} {B} L′
  ξ-inj₂ : ∀ {Γ A B} {R R′ : Γ ⊢ B}
    → R ⟶ R′
    → `inj₂ {_} {A} R ⟶ `inj₂ {_} {A} R′
  ξ-proj₁ : ∀ {Γ A B} {P P′ : Γ ⊢ A `× B}
    → P ⟶ P′
    → `proj₁ P ⟶ `proj₁ P′
  ξ-proj₂ : ∀ {Γ A B} {P P′ : Γ ⊢ A `× B}
    → P ⟶ P′
    → `proj₂ P ⟶ `proj₂ P′
  ξ-⟨,⟩₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A} {R : Γ ⊢ B}
    → L ⟶ L′
    → `⟨ L , R ⟩ ⟶ `⟨ L′ , R ⟩
  ξ-⟨,⟩₂ : ∀ {Γ A B} {VL : Γ ⊢ A} {R R′ : Γ ⊢ B}
    → Value VL
    → R ⟶ R′
    → `⟨ VL , R ⟩ ⟶ `⟨ VL , R′ ⟩
  ξ-caseℕ : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L ⟶ L′
    → caseℕ L M N ⟶ caseℕ L′ M N
  ξ-case⨄ : ∀ {Γ A B C} {L L′ : Γ ⊢ A `⨄ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → L ⟶ L′
    → case⨄ L M N ⟶ case⨄ L′ M N
  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → caseℕ `zero M N ⟶ M
  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
    → caseℕ (`suc V) M N ⟶ N [ V ]
  β-inj₁ : ∀ {Γ A B C} {VL : Γ ⊢ A} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value VL
    → case⨄ (`inj₁ VL) M N ⟶ M [ VL ]
  β-inj₂ : ∀ {Γ A B C} {VR : Γ ⊢ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C}
    → Value VR
    → case⨄ (`inj₂ VR) M N ⟶ N [ VR ]
  β-proj₁ : ∀ {Γ A B} {VL : Γ ⊢ A} {P : Γ ⊢ A `× B} 
    → Value VL
    → (`proj₁ P) ⟶ VL 
  β-proj₂ : ∀ {Γ A B} {VR : Γ ⊢ B} {P : Γ ⊢ A `× B} 
    → Value VR
    → (`proj₂ P) ⟶ VR
  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
    → μ N ⟶ N [ μ N ]

data Progress {A} (M : ∅ ⊢ A) : Set where
  step : ∀ {N : ∅ ⊢ A}
    → M ⟶ N
    → Progress M
  done :
      Value M
    → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ N) = done V-ƛ
progress (L · M) with progress L
... | step L⟶L′ = step (ξ-·₁ L⟶L′)
... | done V-ƛ with progress M
...   | step M⟶M′ = step (ξ-·₂ V-ƛ M⟶M′)
...   | done VM = step (β-ƛ VM)
progress (`zero) = done V-zero
progress (`suc M) with progress M
... | step M⟶M′ = step (ξ-suc M⟶M′)
... | done VM = done (V-suc VM)
progress (caseℕ L M N) with progress L
... | step L⟶L′ = step (ξ-caseℕ L⟶L′)
... | done V-zero = step (β-zero)
... | done (V-suc VL) = step (β-suc VL)
progress (μ N) = step (β-μ)
progress (`inj₁ L) with progress L
... | step L⟶L′ = step (ξ-inj₁ L⟶L′)
... | done VL = done (V-inj₁ VL)
progress (`inj₂ L) with progress L
... | step R⟶R′ = step (ξ-inj₂ R⟶R′)
... | done VR = done (V-inj₂ VR)
progress (case⨄ L M N) with progress L
... | step L⟶L′ = step (ξ-case⨄ L⟶L′)
... | done (V-inj₁ VL) = step (β-inj₁ VL)
... | done (V-inj₂ VR) = step (β-inj₂ VR)
progress (`proj₁ P) with progress P
... | step P⟶P′ = step (ξ-proj₁ P⟶P′)
... | done (V-⟨,⟩ L R) = step (β-proj₁ L)
progress (`proj₂ P) with progress P
... | step P⟶P′ = step (ξ-proj₂ P⟶P′)
... | done (V-⟨,⟩ L R) = step (β-proj₂ R)
progress (`⟨ L , R ⟩) with progress L | progress R
... | step L⟶L′ | step R⟶R′ = step (ξ-⟨,⟩₁ L⟶L′)
... | done VL | step R⟶R′ = step (ξ-⟨,⟩₂ VL R⟶R′)
... | step L⟶L′ | done y = step (ξ-⟨,⟩₁ L⟶L′)
... | done VL | done VR = done (V-⟨,⟩ VL VR)

program : ∅ ⊢ `ℕ
program = (ƛ `suc # 0) · `zero

eval : program ⟶ `suc `zero
eval with progress program
... | step x @ (β-ƛ V-zero) = x