module Bidi where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
import Intrinsic as Intr

infix   4  _∋_
infix   4 [_,_]Var
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_

infixr  7  _⇒_
infixr  9 _`×_

infix   5  ƛ_
infix   5  μ_
infix   6  _↑
infix   6  _↓_
infixl  7  _·_
infix   8  `suc_
infix   9  #_

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type
  _`×_   : Type → Type → Type
  _`⨄_   : Type → Type → Type

data Context : Set where
  ∅     : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → Γ , A ∋ A
  S : ∀ {Γ A B}
    → Γ ∋ A
    → Γ , B ∋ A

Index : Set
Index = ℕ

index : ∀ {Γ A} → Γ ∋ A → ℕ
index Z = 0
index (S x) = suc (index x)

record Var (Γ : Context) (A : Type) (x : ℕ) : Set where
  constructor [_,_]Var
  field
    ∋x : Γ ∋ A
    idx≡ : index ∋x ≡ x

data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  #_                       : Index → Term⁺
  _·_                      : Term⁺ → Term⁻ → Term⁺
  `proj₁                   : Term⁺ → Term⁺
  `proj₂                   : Term⁺ → Term⁺
  `⟨_,_⟩                   : Term⁺ → Term⁺ → Term⁺
  `zero                    : Term⁺
  `suc_                    : Term⁺ → Term⁺
  `caseℕ_[zero⇒_|suc⇒_]    : Term⁺ → Term⁺ → Term⁻ → Term⁺
  `case⨄_[inj₁⇒_|inj₂⇒_]   : Term⁺ → Term⁺ → Term⁻ → Term⁺
  _↓_                      : Term⁻ → Type → Term⁺

data Term⁻ where
  ƛ_                       : Term⁻ → Term⁻
  μ_                       : Term⁻ → Term⁻
  `inj₁                    : Term⁺ → Term⁻
  `inj₂                    : Term⁺ → Term⁻
  _↑                       : Term⁺ → Term⁻

data _⊢_↑_ : Context → Term⁺ → Type → Set
data _⊢_↓_ : Context → Term⁻ → Type → Set

data _⊢_↑_ where
  ⊢` : ∀ {Γ A x}
    → (Var Γ A x)
    → Γ ⊢ # x ↑ A
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑ A ⇒ B
    → Γ ⊢ M ↓ A
    → Γ ⊢ L · M ↑ B
  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
    → Γ ⊢ (M ↓ A) ↑ A
  ⊢proj₁ : ∀ {Γ P A B}
    → Γ ⊢ P ↑ (A `× B)
    → Γ ⊢ (`proj₁ P) ↑ A
  ⊢proj₂ : ∀ {Γ P A B}
    → Γ ⊢ P ↑ (A `× B)
    → Γ ⊢ (`proj₂ P) ↑ B
  ⊢⟨,⟩ : ∀ {Γ L R A B}
    → Γ ⊢ L ↑ A
    → Γ ⊢ R ↑ B
    → Γ ⊢ `⟨ L , R ⟩ ↑ (A `× B)
  ⊢zero : ∀ {Γ} → Γ ⊢ `zero ↑ `ℕ
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ↑ `ℕ
    → Γ ⊢ `suc M ↑ `ℕ
  ⊢caseℕ : ∀ {Γ L M N C}
    → Γ ⊢ L ↑ `ℕ
    → Γ ⊢ M ↑ C
    → Γ , `ℕ ⊢ N ↓ C
    → Γ ⊢ `caseℕ L [zero⇒ M |suc⇒ N ] ↑ C
  ⊢case⨄ : ∀ {Γ A B C L M N}
    → Γ ⊢ L ↑ A `⨄ B
    → Γ , A ⊢ M ↑ C
    → Γ , B ⊢ N ↓ C
    → Γ ⊢ `case⨄ L [inj₁⇒ M |inj₂⇒ N ] ↑ C

data _⊢_↓_ where
  ⊢ƛ : ∀ {Γ N A B}
    → Γ , A ⊢ N ↓ B
    → Γ ⊢ ƛ N ↓ A ⇒ B
  ⊢μ : ∀ {Γ N A}
    → Γ , A ⊢ N ↓ A
    → Γ ⊢ μ N ↓ A
  ⊢inj₁ : ∀ {Γ L A B}
    → Γ ⊢ L ↑ A
    → Γ ⊢ (`inj₁ L) ↓ A `⨄ B
  ⊢inj₂ : ∀ {Γ R A B}
    → Γ ⊢ R ↑ B
    → Γ ⊢ (`inj₂ R) ↓ A `⨄ B
  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≡ B
    → Γ ⊢ (M ↑) ↓ B

_ : ∅ , `ℕ ⊢ # 0 ↑ `ℕ
_ = ⊢` [ Z , refl ]Var

_ : ∅ ⊢ (ƛ (# zero) ↑) ↓ `ℕ ⇒ `ℕ
_ = ⊢ƛ (⊢↑ (⊢` [ Z , refl ]Var) refl)

_≟Tp_ : (A B : Type) → Dec (A ≡ B)
`ℕ      ≟Tp `ℕ               = yes refl
(A ⇒ B) ≟Tp (A′ ⇒ B′)
  with A ≟Tp A′ | B ≟Tp B′
...  | no A≢    | _          = no λ{refl → A≢ refl}
...  | yes _    | no B≢      = no λ{refl → B≢ refl}
...  | yes refl | yes refl   = yes refl
(A `× B) ≟Tp (A′ `× B′)
  with A ≟Tp A′ | B ≟Tp B′
...  | no A≢    | _          = no λ{refl → A≢ refl}
...  | yes _    | no B≢      = no λ{refl → B≢ refl}
...  | yes refl | yes refl   = yes refl
(A `⨄ B) ≟Tp (A′ `⨄ B′)
  with A ≟Tp A′ | B ≟Tp B′
...  | no A≢    | _          = no λ{refl → A≢ refl}
...  | yes _    | no B≢      = no λ{refl → B≢ refl}
...  | yes refl | yes refl   = yes refl

(a `⨄ a₁) ≟Tp `ℕ = no λ()
(a `× a₁) ≟Tp (b `⨄ b₁)      = no λ()
(a `⨄ a₁) ≟Tp (b ⇒ b₁)       = no λ()
(a `⨄ a₁) ≟Tp (b `× b₁)      = no λ()
`ℕ      ≟Tp (A ⇒ B)          = no λ()
`ℕ      ≟Tp (A `× B)         = no λ()
`ℕ      ≟Tp (A `⨄ B)         = no λ()
(A ⇒ B) ≟Tp `ℕ               = no λ()
(A ⇒ B) ≟Tp (x `× x₁)        = no λ()
(A ⇒ B) ≟Tp (x `⨄ x₁)        = no λ()
(A `× B) ≟Tp `ℕ = no λ ()
(A `× B) ≟Tp (x ⇒ x₁) = no λ ()

dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
left×≡ : ∀ {A A′ B B′} → A `× B ≡ A′ `× B′ → A ≡ A′
right×≡ : ∀ {A A′ B B′} → A `× B ≡ A′ `× B′ → B ≡ B′
left⨄≡ : ∀ {A B A′ B′} → (A `⨄ B) ≡ (A′ `⨄ B′) → A ≡ A′
right⨄≡ : ∀ {A B A′ B′} → (A `⨄ B) ≡ (A′ `⨄ B′) → B ≡ B′
ℕ≢⇒ : ∀ {A B} → `ℕ ≢ A ⇒ B
ℕ≢× : ∀ {A B} → `ℕ ≢ A `× B
ℕ≢⨄ : ∀ {A B} → `ℕ ≢ A `⨄ B
×≢⇒ : ∀ {A B C D} → (A `× B) ≢ C ⇒ D
⨄≢⇒ : ∀ {A B C D} → (A `⨄ B) ≢ C ⇒ D
⨄≢× : ∀ {A B C D} → (A `⨄ B) ≢ (C `× D)

dom≡ refl = refl
rng≡ refl = refl
left×≡ refl = refl
right×≡ refl = refl
left⨄≡ refl = refl
right⨄≡ refl = refl
ℕ≢⇒ ()
ℕ≢× ()
ℕ≢⨄ ()
×≢⇒ ()
⨄≢⇒ ()
⨄≢× ()

uniq-∋ : ∀ {Γ A B}
  → (∋x : Γ ∋ A)
  → (∋x′ : Γ ∋ B)
  → (index ∋x ≡ index ∋x′)
  → A ≡ B
uniq-∋ Z Z p            = refl
uniq-∋ (S ∋x) (S ∋x′) p = uniq-∋ ∋x ∋x′ (suc-injective p)

≡↓ : ∀ {Γ M A B}
  → A ≡ B
  → Γ ⊢ M ↓ A
  → Γ ⊢ M ↓ B
≡↓ A≡B ⊢M rewrite A≡B = ⊢M

uniq-↑ : ∀ {Γ M A B}
  → Γ ⊢ M ↑ A
  → Γ ⊢ M ↑ B
  → A ≡ B
uniq-↑ (⊢` [ ∋x , idx≡ ]Var) (⊢` [ ∋x′ , idx≡′ ]Var) = uniq-∋ ∋x ∋x′ (trans idx≡ (sym idx≡′))
uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′)       = rng≡ (uniq-↑ ⊢L ⊢L′)
uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)            = refl
uniq-↑ (⊢proj₁ ⊢P) (⊢proj₁ ⊢P′)    = left×≡ (uniq-↑ ⊢P ⊢P′) 
uniq-↑ (⊢proj₂ ⊢P) (⊢proj₂ ⊢P′)    = right×≡ (uniq-↑ ⊢P ⊢P′)
uniq-↑ (⊢⟨,⟩ ⊢L ⊢R) (⊢⟨,⟩ ⊢L′ ⊢R′)
  rewrite uniq-↑ ⊢L ⊢L′
  rewrite uniq-↑ ⊢R ⊢R′            = refl
uniq-↑ ⊢zero ⊢zero                 = refl
uniq-↑ (⊢suc ⊢N) (⊢suc ⊢N′)        = refl
uniq-↑ (⊢caseℕ ⊢L ⊢M ⊢N) (⊢caseℕ ⊢L′ ⊢M′ ⊢N′)
  rewrite uniq-↑ ⊢L ⊢L′            = uniq-↑ ⊢M ⊢M′
uniq-↑ (⊢case⨄ ⊢L ⊢M ⊢N) (⊢case⨄ ⊢L′ ⊢M′ ⊢N′)
  rewrite left⨄≡ (uniq-↑ ⊢L ⊢L′)   = uniq-↑ ⊢M ⊢M′

ext∋ : ∀ {Γ B x}
  → ¬ (∃[ A ] Var Γ A x)
  → ¬ (∃[ A ] Var (Γ , B) A (suc x))
ext∋ ¬∃ ⟨ A , [ (S ∋x) , idx≡ ]Var ⟩  = ¬∃ ⟨ A , [ ∋x , suc-injective idx≡ ]Var ⟩

lookup : ∀ (Γ : Context) (x : Index)
  → Dec (∃[ A ] Var Γ A x )
lookup ∅ x                        = no  (λ ())
lookup (Γ , B) zero = yes ⟨ B , [ Z , refl ]Var ⟩
lookup (Γ , _) (suc x) with lookup Γ x
... | no ¬∃ = no (ext∋ ¬∃)
... | yes ⟨ A , [ ∋x , idx≡ ]Var ⟩ = yes ⟨ A , [ (S ∋x) , cong suc idx≡ ]Var ⟩

¬arg : ∀ {Γ A B L M}
  → Γ ⊢ L ↑ A ⇒ B
  → ¬ Γ ⊢ M ↓ A
  → ¬ (∃[ B′ ] Γ ⊢ L · M ↑ B′)
¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′

¬switch : ∀ {Γ M A B}
  → Γ ⊢ M ↑ A
  → A ≢ B
  → ¬ Γ ⊢ (M ↑) ↓ B
¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = A≢B A′≡B

⊢↑subst : ∀ {Γ M C A A′}
  → A ≡ A′
  → (Γ , A′ ⊢ M ↑ C)
  → (Γ , A ⊢ M ↑ C)
⊢↑subst refl Γ = Γ

⊢↓subst : ∀ {Γ M C A A′}
  → A ≡ A′
  → (Γ , A′ ⊢ M ↓ C)
  → (Γ , A ⊢ M ↓ C)
⊢↓subst refl Γ = Γ

synthesize : ∀ (Γ : Context) (M : Term⁺)
  → Dec (∃[ A ] Γ ⊢ M ↑ A )

inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
  → Dec (Γ ⊢ M ↓ A)

synthesize Γ (# x) with lookup Γ x
... | no  ¬∃              = no  λ{ ⟨ A , ⊢` ∋x ⟩ → ¬∃ ⟨ A , ∋x ⟩ }
... | yes ⟨ A , ∋x ⟩      = yes ⟨ A , ⊢` ∋x ⟩
synthesize Γ (L · M) with synthesize Γ L
... | no  ¬∃              = no  λ{ ⟨ _ , ⊢L  · _  ⟩  →  ¬∃ ⟨ _ , ⊢L ⟩ }
... | yes ⟨ `ℕ ,     ⊢L ⟩ = no  λ{ ⟨ _ , ⊢L′ · _  ⟩  →  ℕ≢⇒ (uniq-↑ ⊢L ⊢L′) }
... | yes ⟨ A `× B , ⊢L ⟩ = no  λ{ ⟨ _ , ⊢L′ · _  ⟩  →  ×≢⇒ ((uniq-↑ ⊢L ⊢L′)) }
... | yes ⟨ A `⨄ B , ⊢L ⟩ = no  λ{ ⟨ _ , ⊢L′ · _  ⟩  →  ⨄≢⇒ ((uniq-↑ ⊢L ⊢L′)) }
... | yes ⟨ A ⇒ B ,  ⊢L ⟩ with inherit Γ M A
...    | no  ¬⊢M          = no  (¬arg ⊢L ¬⊢M)
...    | yes ⊢M           = yes ⟨ B , ⊢L · ⊢M ⟩
synthesize Γ (M ↓ A) with inherit Γ M A
... | no  ¬∃             = no  λ{ ⟨ _ , ⊢↓ ⊢M ⟩  →  ¬∃ ⊢M }
... | yes ⊢M              = yes ⟨ A , ⊢↓ ⊢M ⟩
synthesize Γ (`proj₁ P) with synthesize Γ P 
... | no ¬∃               = no  λ{ ⟨ A , ⊢proj₁ {_} {_} {_} {B} v ⟩ → ¬∃ ⟨ A `× B , v ⟩}
... | yes ⟨ `ℕ ,     ⊢P ⟩ = no  λ{ ⟨ _ , ⊢proj₁ ⊢P′ ⟩ → ℕ≢× (uniq-↑ ⊢P ⊢P′) }
... | yes ⟨ _ ⇒ _ ,  ⊢P ⟩ = no  λ{ ⟨ _ , ⊢proj₁ ⊢P′ ⟩ → ×≢⇒ (uniq-↑ ⊢P′ ⊢P) }
... | yes ⟨ _ `⨄ _ , ⊢P ⟩ = no  λ{ ⟨ _ , ⊢proj₁ ⊢P′ ⟩ → ⨄≢× (uniq-↑ ⊢P ⊢P′) }
... | yes ⟨ A `× _ , ⊢P ⟩ = yes ⟨ A , ⊢proj₁ ⊢P ⟩
synthesize Γ (`proj₂ P) with synthesize Γ P 
... | no ¬∃               = no  λ{ ⟨ B , ⊢proj₂ {_} {_} {A} {_} v ⟩ → ¬∃ ⟨ A `× B , v ⟩}
... | yes ⟨ `ℕ ,     ⊢P ⟩ = no  λ{ ⟨ _ , ⊢proj₂ ⊢P′ ⟩ → ℕ≢× (uniq-↑ ⊢P ⊢P′) }
... | yes ⟨ _ ⇒ _ ,  ⊢P ⟩ = no  λ{ ⟨ _ , ⊢proj₂ ⊢P′ ⟩ → ×≢⇒ (uniq-↑ ⊢P′ ⊢P) }
... | yes ⟨ _ `⨄ _ , ⊢P ⟩ = no  λ{ ⟨ _ , ⊢proj₂ ⊢P′ ⟩ → ⨄≢× (uniq-↑ ⊢P ⊢P′) }
... | yes ⟨ _ `× B , ⊢P ⟩ = yes ⟨ B , ⊢proj₂ ⊢P ⟩
synthesize Γ (`⟨ L , R ⟩) with synthesize Γ L | synthesize Γ R
... | no ¬L          | no ¬R          = no λ{ ⟨ (_ `× B) , ⊢⟨,⟩ _ ⊢R ⟩ → ¬R ⟨ B , ⊢R ⟩ }
... | yes ¬L         | no ¬R          = no λ{ ⟨ (_ `× B) , ⊢⟨,⟩ _ ⊢R ⟩ → ¬R ⟨ B , ⊢R ⟩ }
... | no ¬L          | yes ¬R         = no λ{ ⟨ (A `× _) , ⊢⟨,⟩ ⊢L _ ⟩ → ¬L ⟨ A , ⊢L ⟩ }
... | yes ⟨ A , ⊢L ⟩ | yes ⟨ B , ⊢R ⟩ = yes ⟨ A `× B , (⊢⟨,⟩ ⊢L ⊢R) ⟩
synthesize Γ `zero = yes ⟨ `ℕ , ⊢zero ⟩
synthesize Γ (`suc N) with synthesize Γ N
... | no ¬∃                    = no λ{ ⟨ .`ℕ , ⊢suc ⊢N ⟩ → ¬∃ ⟨ `ℕ , ⊢N ⟩ }
... | yes ⟨ `ℕ          , ⊢N ⟩ = yes ⟨ `ℕ , (⊢suc ⊢N) ⟩
... | yes ⟨ _ ⇒ _       , ⊢N ⟩ = no λ{ ⟨ .`ℕ , ⊢suc ⊢N′ ⟩ → ℕ≢⇒ ((uniq-↑ ⊢N′ ⊢N)) }
... | yes ⟨ _ `× _ , ⊢N ⟩ = no λ{ ⟨ .`ℕ , ⊢suc ⊢N′ ⟩ → ℕ≢× ((uniq-↑ ⊢N′ ⊢N)) }
... | yes ⟨ _ `⨄ _ , ⊢N ⟩ = no λ{ ⟨ .`ℕ , ⊢suc ⊢N′ ⟩ → ℕ≢⨄ ((uniq-↑ ⊢N′ ⊢N)) }

synthesize Γ `caseℕ L [zero⇒ M |suc⇒ N ] with synthesize Γ L
... | no ¬∃               = no λ{ ⟨ _ , (⊢caseℕ ⊢L _ _) ⟩ → ¬∃  ⟨ `ℕ , ⊢L ⟩ }
... | yes ⟨ _ ⇒ _ , ⊢L ⟩  = no λ{ ⟨ _ , ⊢caseℕ ⊢L′ _ _ ⟩ → ℕ≢⇒ ((uniq-↑ ⊢L′ ⊢L))}
... | yes ⟨ _ `× _ , ⊢L ⟩ = no λ{ ⟨ _ , ⊢caseℕ ⊢L′ _ _ ⟩ → ℕ≢× ((uniq-↑ ⊢L′ ⊢L))}
... | yes ⟨ _ `⨄ _ , ⊢L ⟩ = no λ{ ⟨ _ , ⊢caseℕ ⊢L′ _ _ ⟩ → ℕ≢⨄ ((uniq-↑ ⊢L′ ⊢L))}
... | yes ⟨ `ℕ , ⊢L ⟩ with synthesize Γ M
...   | no ¬∃ = no λ{ ⟨ C , ⊢caseℕ _ ⊢M _ ⟩ → ¬∃ ⟨ C , ⊢M ⟩ }
...   | yes ⟨ C , ⊢M ⟩ with inherit (Γ , `ℕ) N C
...     | no ¬∃  = no λ{ ⟨ _ , ⊢caseℕ _ ⊢M′ ⊢N ⟩ → ¬∃ (≡↓ (uniq-↑ ⊢M′ ⊢M) ⊢N) }
...     | yes ⊢N = yes ⟨ _ , ⊢caseℕ ⊢L ⊢M ⊢N ⟩
synthesize Γ `case⨄ L [inj₁⇒ M |inj₂⇒ N ] with synthesize Γ L
... | no ¬∃               = no λ{ ⟨ _ , (⊢case⨄ ⊢L _ _) ⟩ → ¬∃  ⟨ _ , ⊢L ⟩ }
... | yes ⟨ _ ⇒ _ , ⊢L ⟩  = no λ{ ⟨ _ , ⊢case⨄ ⊢L′ _ _ ⟩ → ⨄≢⇒ ((uniq-↑ ⊢L′ ⊢L))}
... | yes ⟨ _ `× _ , ⊢L ⟩ = no λ{ ⟨ _ , ⊢case⨄ ⊢L′ _ _ ⟩ → ⨄≢× ((uniq-↑ ⊢L′ ⊢L))}
... | yes ⟨ `ℕ , ⊢L ⟩     = no λ{ ⟨ _ , ⊢case⨄ ⊢L′ _ _ ⟩ → ℕ≢⨄ ((uniq-↑ ⊢L ⊢L′))}
... | yes ⟨ A `⨄ B , ⊢L ⟩ with synthesize (Γ , A) M
...   | no ¬∃ = no λ{ ⟨ C , ⊢case⨄ ⊢L′ ⊢M _ ⟩ → ¬∃ ⟨ C , ⊢↑subst (left⨄≡ (uniq-↑ ⊢L ⊢L′)) ⊢M ⟩ }
...   | yes ⟨ C , ⊢M ⟩ with inherit (Γ , B) N C
...     | no ¬∃ = no λ{ ⟨ C′ , ⊢case⨄ ⊢L′ ⊢M′ ⊢N ⟩ → ¬∃ (
          ⊢↓subst
            (right⨄≡ (uniq-↑ ⊢L ⊢L′))
            (≡↓
              (uniq-↑ (⊢↑subst (left⨄≡ (uniq-↑ ⊢L ⊢L′)) ⊢M′) ⊢M)
              ⊢N))}
...     | yes ⊢N = yes ⟨ C , ⊢case⨄ ⊢L ⊢M ⊢N ⟩

inherit Γ (ƛ N) `ℕ          = no (λ ())
inherit Γ (ƛ N) (A `× B) = no (λ ())
inherit Γ (ƛ N) (A ⇒ B) with inherit (Γ , A) N B
... | no ¬∃  = no  (λ{ (⊢ƛ ⊢N) → ¬∃ ⊢N })
... | yes ⊢N = yes (⊢ƛ ⊢N)
inherit Γ (μ N) A with inherit (Γ , A) N A
... | no ¬∃  = no  (λ{ (⊢μ ⊢N) → ¬∃ ⊢N })
... | yes ⊢N = yes (⊢μ ⊢N)
inherit Γ (M ↑) B with synthesize Γ M
... | no  ¬∃ = no (λ{ (⊢↑ ⊢M _) → ¬∃ ⟨ _ , ⊢M ⟩ })
... | yes ⟨ A , ⊢M ⟩ with A ≟Tp B
...   | no  A≢B = no  (¬switch ⊢M A≢B)
...   | yes A≡B = yes (⊢↑ ⊢M A≡B) 
inherit Γ (ƛ a) (b `⨄ b₁)     = no λ()

inherit Γ (`inj₁ a) `ℕ        = no λ()
inherit Γ (`inj₁ a) (x ⇒ x₁)  = no λ()
inherit Γ (`inj₁ a) (x `× x₁) = no λ()
inherit Γ (`inj₁ L) (A `⨄ B) with synthesize Γ L
... | no ¬E = no (λ{ (⊢inj₁ L′) → ¬E ⟨ A , L′ ⟩ })
... | yes ⟨ A′ , ⊢A ⟩ with A ≟Tp A′
...   | no A′≢A               = no λ{ (⊢inj₁ ⊢A′) → A′≢A (uniq-↑ ⊢A′ ⊢A )}
...   | yes A′≡A rewrite A′≡A = yes (⊢inj₁ ⊢A)
inherit Γ (`inj₂ a) `ℕ = no λ()
inherit Γ (`inj₂ a) (x ⇒ x₁) = no λ()
inherit Γ (`inj₂ a) (x `× x₁) = no λ()
inherit Γ (`inj₂ R) (A `⨄ B) with synthesize Γ R
... | no ¬E = no (λ{ (⊢inj₂ R′) → ¬E ⟨ B , R′ ⟩ })
... | yes ⟨ B′ , ⊢B ⟩ with B ≟Tp B′
...   | no B′≢B               = no λ{ (⊢inj₂ ⊢B′) → B′≢B (uniq-↑ ⊢B′ ⊢B )}
...   | yes B′≡B rewrite B′≡B = yes (⊢inj₂ ⊢B)

_ : synthesize ∅ (`suc `zero) ≡ yes ⟨ `ℕ , ⊢suc ⊢zero ⟩
_ = refl

_ : synthesize ∅
        (`case⨄ ((`inj₂ `zero) ↓ ((`ℕ `× `ℕ) `⨄ `ℕ))
          [inj₁⇒ `proj₁ (# 0)
          |inj₂⇒ (# 0) ↑ ])
    ≡ yes ⟨
      `ℕ ,
      ⊢case⨄
        (⊢↓ (⊢inj₂ ⊢zero))
        (⊢proj₁ (⊢` [ Z , refl ]Var))
        (⊢↑ (⊢` [ Z , refl ]Var) refl) ⟩
_ = refl

_ : inherit ∅
      (ƛ (`⟨ `proj₂ (# 0) , `proj₁ (# 0) ⟩ ↑)) (`ℕ `× `ℕ ⇒ `ℕ `× `ℕ)
    ≡ yes (⊢ƛ (⊢↑ (⊢⟨,⟩ (⊢proj₂ (⊢` [ Z , refl ]Var)) (⊢proj₁ (⊢` [ Z , refl ]Var))) refl))
_ = refl

∥_∥Tp : Type → Intr.Type
∥ `ℕ ∥Tp     = Intr.`ℕ
∥ A ⇒ B ∥Tp  = ∥ A ∥Tp Intr.⇒ ∥ B ∥Tp
∥ A `× B ∥Tp = ∥ A ∥Tp Intr.`× ∥ B ∥Tp
∥ A `⨄ B ∥Tp = ∥ A ∥Tp Intr.`⨄ ∥ B ∥Tp

∥_∥Cx : Context → Intr.Context
∥ ∅ ∥Cx     = Intr.∅
∥ Γ , A ∥Cx = ∥ Γ ∥Cx Intr., ∥ A ∥Tp

∥_∥∋ : ∀ {Γ A} → Γ ∋ A → ∥ Γ ∥Cx Intr.∋ ∥ A ∥Tp
∥ Z ∥∋    = Intr.Z
∥ S ∋x ∥∋ = Intr.S ∥ ∋x ∥∋

∥_∥⁺ : ∀ {Γ M A} → Γ ⊢ M ↑ A → ∥ Γ ∥Cx Intr.⊢ ∥ A ∥Tp
∥_∥⁻ : ∀ {Γ M A} → Γ ⊢ M ↓ A → ∥ Γ ∥Cx Intr.⊢ ∥ A ∥Tp

∥ ⊢` [ ⊢x , _ ]Var ∥⁺   = Intr.` ∥ ⊢x ∥∋
∥ ⊢L · ⊢M ∥⁺         = ∥ ⊢L ∥⁺ Intr.· ∥ ⊢M ∥⁻
∥ ⊢↓ ⊢M ∥⁺           = ∥ ⊢M ∥⁻
∥ ⊢zero ∥⁺           = Intr.`zero
∥ ⊢suc ⊢M ∥⁺         = Intr.`suc ∥ ⊢M ∥⁺
∥ ⊢proj₁ ⊢P ∥⁺       = Intr.`proj₁ ∥ ⊢P ∥⁺
∥ ⊢proj₂ ⊢P ∥⁺       = Intr.`proj₂ ∥ ⊢P ∥⁺
∥ ⊢⟨,⟩ ⊢L ⊢R ∥⁺      = Intr.`⟨ ∥ ⊢L ∥⁺ , ∥ ⊢R ∥⁺ ⟩
∥ ⊢caseℕ ⊢L ⊢M ⊢N ∥⁺ = Intr.caseℕ ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁺ ∥ ⊢N ∥⁻
∥ ⊢case⨄ ⊢L ⊢M ⊢N ∥⁺ = Intr.case⨄  ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁺ ∥ ⊢N ∥⁻

∥ ⊢ƛ ⊢N ∥⁻           = Intr.ƛ ∥ ⊢N ∥⁻
∥ ⊢μ ⊢M ∥⁻           = Intr.μ ∥ ⊢M ∥⁻
∥ ⊢↑ ⊢M refl ∥⁻      = ∥ ⊢M ∥⁺
∥ ⊢inj₁ ⊢L ∥⁻        = Intr.`inj₁ ∥ ⊢L ∥⁺
∥ ⊢inj₂ ⊢R ∥⁻        = Intr.`inj₂ ∥ ⊢R ∥⁺

⟪_⟫Tp : Intr.Type → Type
⟪ M Intr.⇒ N ⟫Tp  = ⟪ M ⟫Tp ⇒ ⟪ N ⟫Tp
⟪ Intr.`ℕ ⟫Tp = `ℕ
⟪ A Intr.`× B ⟫Tp = ⟪ A ⟫Tp `× ⟪ B ⟫Tp
⟪ A Intr.`⨄ B ⟫Tp = ⟪ A ⟫Tp `⨄ ⟪ B ⟫Tp

⟪_⟫Cx : Intr.Context → Context
⟪ Intr.∅ ⟫Cx = ∅
⟪ Γ Intr., A ⟫Cx = ⟪ Γ ⟫Cx , ⟪ A ⟫Tp

⟪_⟫∋ : ∀ {Γ A} → Γ Intr.∋ A → ⟪ Γ ⟫Cx ∋ ⟪ A ⟫Tp
⟪ Intr.Z ⟫∋ = Z
⟪ Intr.S ∋x ⟫∋ = S ⟪ ∋x ⟫∋ 

⟪_⟫⁺ : ∀ {Γ} → {A : Intr.Type} → Γ Intr.⊢ A → Term⁺
⟪_⟫⁻ : ∀ {Γ} → {A : Intr.Type} → Γ Intr.⊢ A → Term⁻

⟪ Intr.` x ⟫⁺ = # index ⟪ x ⟫∋
⟪ L Intr.· M ⟫⁺ = ⟪ L ⟫⁺ · ⟪ M ⟫⁻
⟪ Intr.`zero ⟫⁺ = `zero
⟪ Intr.`suc N ⟫⁺ = `suc ⟪ N ⟫⁺ 
⟪ Intr.caseℕ L M N ⟫⁺ = `caseℕ ⟪ L ⟫⁺ [zero⇒ ⟪ M ⟫⁺ |suc⇒ ⟪ N ⟫⁻ ]
⟪ Intr.case⨄ L M N ⟫⁺ = `case⨄ ⟪ L ⟫⁺ [inj₁⇒ ⟪ M ⟫⁺ |inj₂⇒ ⟪ N ⟫⁻ ]
⟪ Intr.`⟨ L , R ⟩ ⟫⁺ = `⟨ ⟪ L ⟫⁺ , ⟪ R ⟫⁺ ⟩
⟪ Intr.`proj₁ P ⟫⁺ = `proj₁ ⟪ P ⟫⁺
⟪ Intr.`proj₂ P ⟫⁺ = `proj₂ ⟪ P ⟫⁺
⟪_⟫⁺ {_} {A} (Intr.ƛ N) = (ƛ ⟪ N ⟫⁻) ↓ ⟪ A ⟫Tp
⟪_⟫⁺ {_} {A} (Intr.μ N) = (μ ⟪ N ⟫⁻) ↓ ⟪ A ⟫Tp
⟪_⟫⁺ {_} {A} (Intr.`inj₁ L) = `inj₁ ⟪ L ⟫⁺ ↓ ⟪ A ⟫Tp
⟪_⟫⁺ {_} {A} (Intr.`inj₂ R) = `inj₂ ⟪ R ⟫⁺ ↓ ⟪ A ⟫Tp

⟪ Intr.` x ⟫⁻ = (# index ⟪ x ⟫∋) ↑
⟪ L Intr.· M ⟫⁻ = (⟪ L ⟫⁺ · ⟪ M ⟫⁻) ↑
⟪ Intr.`zero ⟫⁻ = `zero ↑
⟪ Intr.`suc N ⟫⁻ = `suc ⟪ N ⟫⁺  ↑
⟪ Intr.caseℕ L M N ⟫⁻ = `caseℕ ⟪ L ⟫⁺ [zero⇒ ⟪ M ⟫⁺ |suc⇒ ⟪ N ⟫⁻ ] ↑
⟪ Intr.case⨄ L M N ⟫⁻ = `case⨄ ⟪ L ⟫⁺ [inj₁⇒ ⟪ M ⟫⁺ |inj₂⇒ ⟪ N ⟫⁻ ] ↑
⟪ Intr.`⟨ L , R ⟩ ⟫⁻ = `⟨ ⟪ L ⟫⁺ , ⟪ R ⟫⁺ ⟩ ↑
⟪ Intr.`proj₁ P ⟫⁻ = `proj₁ ⟪ P ⟫⁺ ↑
⟪ Intr.`proj₂ P ⟫⁻ = `proj₂ ⟪ P ⟫⁺ ↑
⟪ Intr.ƛ N ⟫⁻ = ƛ ⟪ N ⟫⁻
⟪ Intr.μ N ⟫⁻ = μ ⟪ N ⟫⁻
⟪ Intr.`inj₁ L ⟫⁻ = `inj₁ ⟪ L ⟫⁺
⟪ Intr.`inj₂ R ⟫⁻ = `inj₂ ⟪ R ⟫⁺

⟪_⟫↑ : ∀ {Γ} → {A : Intr.Type} → (M : Γ Intr.⊢ A) → ⟪ Γ ⟫Cx ⊢ ⟪ M ⟫⁺ ↑ ⟪ A ⟫Tp
⟪_⟫↓ : ∀ {Γ} → {A : Intr.Type} → (M : Γ Intr.⊢ A) → ⟪ Γ ⟫Cx ⊢ ⟪ M ⟫⁻ ↓ ⟪ A ⟫Tp

⟪ Intr.` x ⟫↑ = ⊢` [ ⟪ x ⟫∋ , refl ]Var
⟪ L Intr.· M ⟫↑ = ⟪ L ⟫↑ · ⟪ M ⟫↓
⟪ Intr.`zero ⟫↑ = ⊢zero
⟪ Intr.`suc M ⟫↑ = ⊢suc ⟪ M ⟫↑
⟪ Intr.caseℕ L M N ⟫↑ = ⊢caseℕ ⟪ L ⟫↑ ⟪ M ⟫↑ ⟪ N ⟫↓
⟪ Intr.case⨄ L M N ⟫↑ = ⊢case⨄ ⟪ L ⟫↑ ⟪ M ⟫↑ ⟪ N ⟫↓
⟪ Intr.`⟨ L , R ⟩ ⟫↑ = ⊢⟨,⟩ ⟪ L ⟫↑ ⟪ R ⟫↑
⟪ Intr.`proj₁ P ⟫↑ = ⊢proj₁ ⟪ P ⟫↑
⟪ Intr.`proj₂ P ⟫↑ = ⊢proj₂ ⟪ P ⟫↑
⟪ Intr.ƛ N ⟫↑ = ⊢↓ (⊢ƛ ⟪ N ⟫↓)
⟪ Intr.μ N ⟫↑ = ⊢↓ (⊢μ ⟪ N ⟫↓)
⟪ Intr.`inj₁ L ⟫↑ = ⊢↓ (⊢inj₁ ⟪ L ⟫↑)
⟪ Intr.`inj₂ R ⟫↑ = ⊢↓ (⊢inj₂ ⟪ R ⟫↑)

⟪ Intr.` x ⟫↓ = ⊢↑ (⊢` [ ⟪ x ⟫∋ , refl ]Var) refl
⟪ Intr.ƛ M ⟫↓ = ⊢ƛ ⟪ M ⟫↓
⟪ L Intr.· M ⟫↓ = ⊢↑ (⟪ L ⟫↑ · ⟪ M ⟫↓) refl
⟪ Intr.`zero ⟫↓ = ⊢↑ ⊢zero refl
⟪ Intr.`suc N ⟫↓ = ⊢↑ (⊢suc ⟪ N ⟫↑) refl
⟪ Intr.caseℕ L M N ⟫↓ = ⊢↑ (⊢caseℕ ⟪ L ⟫↑ ⟪ M ⟫↑ ⟪ N ⟫↓) refl
⟪ Intr.μ N ⟫↓ = ⊢μ ⟪ N ⟫↓
⟪ Intr.`inj₁ M ⟫↓ = ⊢inj₁ ⟪ M ⟫↑
⟪ Intr.`inj₂ M ⟫↓ = ⊢inj₂ ⟪ M ⟫↑
⟪ Intr.case⨄ L M N ⟫↓ = ⊢↑ (⊢case⨄ ⟪ L ⟫↑ ⟪ M ⟫↑ ⟪ N ⟫↓) refl
⟪ Intr.`⟨ L , R ⟩ ⟫↓ = ⊢↑ (⊢⟨,⟩ ⟪ L ⟫↑ ⟪ R ⟫↑) refl
⟪ Intr.`proj₁ P ⟫↓ = ⊢↑ (⊢proj₁ ⟪ P ⟫↑) refl
⟪ Intr.`proj₂ P ⟫↓ = ⊢↑ (⊢proj₂ ⟪ P ⟫↑) refl
