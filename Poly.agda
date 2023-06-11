module Poly where

infix  4 _∋_
infix  4 _⊢type
infix  4 _⊢ctx
infix  4 _∣_∋_
infixl 5 _,_
infix  6 `∀_
infixr 7 _⇒_

data Kind : Set where
  * : Kind

data TyContext : Set where
  ∅ : TyContext
  _,_ : TyContext → Kind → TyContext

data _∋_ : TyContext → Kind → Set where
  Z : ∀ {Δ A}
    → Δ , A ∋ A
  S_ : ∀ {Δ A B}
    → Δ ∋ A
    → Δ , B ∋ A

data _⊢type : TyContext → Set where
  `ℕ : ∀ {Δ} → Δ ⊢type
  _⇒_ : ∀ {Δ}
    → Δ ⊢type
    → Δ ⊢type
    → Δ ⊢type
  `∀_ : ∀ {Δ : TyContext} 
    → (Δ , *) ⊢type
    → Δ ⊢type
  `var : ∀ {Δ A}
    → Δ ∋ A
    → Δ ⊢type

_ : ∅ ⊢type 
_ = `∀ `var Z ⇒ `var Z

data _⊢ctx (Δ : TyContext) : Set where
  ∅   : Δ ⊢ctx
  _,_ : Δ ⊢ctx → Δ ⊢type → Δ ⊢ctx

data _∣_∋_ : (Δ : TyContext) → Δ ⊢ctx → Δ ⊢type → Set where
  Z : ∀ {Δ Γ A}
    → Δ ∣ Γ , A ∋ A
  S_ : ∀ {Δ Γ A B}
    → Δ ∣ Γ ∋ A
    → Δ ∣ Γ , B ∋ A

ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)

rename : ∀ {Δ Δ′}
  → (∀ {A} → Δ ∋ A → Δ′ ∋ A)
  → (Δ ⊢type → Δ′ ⊢type)

exts : ∀ {Δ Δ′}
  → (∀ {A} →       Δ ∋ A →     Δ′ ⊢type)
  → (∀ {A B} → Δ , B ∋ A → Δ′ , B ⊢type)

subst : ∀ {Δ Δ′}
  → (∀ {A} → Δ ∋ A → Δ′ ⊢type)
  → Δ ⊢type
  → Δ′ ⊢type

substOne : ∀ {Δ}
  → Δ , * ⊢type
  → Δ ⊢type
  → Δ ⊢type

ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
rename ρ (`var x)          =  `var (ρ x)
rename ρ (M ⇒ N)          =   (rename ρ M) ⇒ (rename ρ N)
rename ρ `ℕ = `ℕ
rename ρ (`∀ z) = `∀ (rename (ext ρ) z)

exts σ Z      =  `var Z
exts σ (S x)  =  rename S_ (σ x)

subst σ (`var k) =  σ k
subst σ (M ⇒ N)  =  (subst σ M) ⇒ (subst σ N)
subst σ `ℕ       = `ℕ
subst σ (`∀ N)   = `∀ subst (exts σ) N

substOne {Δ} N M = subst {Δ , *} {Δ} σ N
  where
  σ : ∀ {A} → Δ , * ∋ A → Δ ⊢type
  σ Z      =  M
  σ (S x)  =  `var x

weakTy : ∀ {Δ} → Δ ⊢type → (Δ , *) ⊢type
weakTy ty = rename S_ ty

weakCtx : ∀ {Δ} → Δ ⊢ctx → (Δ , *) ⊢ctx
weakCtx ∅ = ∅
weakCtx (Γ , ty) = weakCtx Γ , weakTy ty

module Intrinsic where
  infix  4 _∣_⊢_
  infix  5 ƛ_
  infix  5 Λ_

  data _∣_⊢_ : ∀ {Δ Γ} → TyContext → Γ ⊢ctx → Δ ⊢type → Set where
    `_ : ∀ {Δ Γ A}
      → Δ ∣ Γ ∋ A
      → Δ ∣ Γ ⊢ A
    `zero : ∀ {Δ : TyContext} {Γ : Δ ⊢ctx}
      → Δ ∣ Γ ⊢ `ℕ {Δ}
    `suc : ∀ {Δ : TyContext} {Γ : Δ ⊢ctx}
      → Δ ∣ Γ ⊢ `ℕ {Δ}
      → Δ ∣ Γ ⊢ `ℕ {Δ}
    _·_ : ∀ {Δ : TyContext} {Γ : Δ ⊢ctx} {A : Δ ⊢type} {B : Δ ⊢type}
      → Δ ∣ Γ ⊢ A ⇒ B
      → Δ ∣ Γ ⊢ A
      → Δ ∣ Γ ⊢ B
    ƛ_ : ∀ {Δ A B} {Γ : Δ ⊢ctx}
      → Δ ∣ Γ , A ⊢ B
      → Δ ∣ Γ ⊢ A ⇒ B
    Λ_ : ∀ {Δ : TyContext} {Γ : Δ ⊢ctx} {B : (Δ , *) ⊢type}
      → Δ , * ∣ weakCtx Γ ⊢ B
      → Δ ∣ Γ ⊢ `∀ B
    _[_] : ∀ {Δ : TyContext} {Γ : Δ ⊢ctx} {B : (Δ , *) ⊢type}
      → Δ ∣ Γ ⊢ `∀ B
      → (A : Δ ⊢type)
      → Δ ∣ Γ ⊢ substOne B A

  f : ∅ ∣ ∅ ⊢ `∀ `∀ `var (S Z) ⇒ `var (S Z)
  f = Λ Λ ƛ ` Z

  _ : ∅ ∣ ∅ ⊢ `∀ (`ℕ ⇒ `ℕ) 
  _ = f [ `ℕ ]

module Bidirectional where

  infix  4 _∣_⊢_↑_ 
  infix  4 _∣_⊢_↓_ 
  infix  4 [_,_]Var
  infix  5 Λ_
  infix  6 _↑
  infix  9 #_
  
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
  open import Data.Nat.Properties using (suc-injective)

  Index : Set
  Index = ℕ

  index : ∀ {Δ Γ A} → Δ ∣ Γ ∋ A → ℕ
  index Z = 0
  index (S x) = suc (index x)

  record Var (Δ : TyContext) (Γ : Δ ⊢ctx) (A : Δ ⊢type) (x : ℕ) : Set where
    constructor [_,_]Var
    field
      ∋x : Δ ∣ Γ ∋ A
      idx≡ : index ∋x ≡ x
  
  ext∋ : ∀ {Δ Γ B x}
    → ¬ (∃[ A ] Var Δ Γ A x)
    → ¬ (∃[ A ] Var Δ (Γ , B) A (suc x))
  ext∋ ¬∃ ⟨ A , [ (S ∋x) , idx≡ ]Var ⟩  = ¬∃ ⟨ A , [ ∋x , suc-injective idx≡ ]Var ⟩

  lookup : ∀ {Δ} → (Γ : Δ ⊢ctx ) (x : Index)
    → Dec (∃[ A ] Var Δ Γ A x )
  lookup ∅ x                        = no  (λ ())
  lookup (Γ , B) zero = yes ⟨ B , [ Z , refl ]Var ⟩
  lookup (Γ , _) (suc x) with lookup Γ x
  ... | no ¬∃ = no (ext∋ ¬∃)
  ... | yes ⟨ A , vx ⟩ = yes ⟨ A , [ (S (Var.∋x vx)) , cong suc (Var.idx≡ vx) ]Var ⟩

  data Term⁺ : Set
  data Term⁻ : Set

  data Term⁺ where
    #_                       : Index → Term⁺
    `zero                    : Term⁺ 
    `suc_                    : Term⁺ → Term⁺
    _·_                      : Term⁺ → Term⁻ → Term⁺
    _[_]                     : Term⁺ → ∅ ⊢type → Term⁺ 
    _↓_                      : Term⁻ → ∅ ⊢type → Term⁺

  data Term⁻ where
    ƛ_                       : Term⁻ → Term⁻
    Λ_                       : Term⁻ → Term⁻
    _↑                       : Term⁺ → Term⁻

  weakEmptyTy : ∀ {Δ}
    → ∅ ⊢type
    → Δ ⊢type
  weakEmptyTy {∅} A = A
  weakEmptyTy {Δ , _} A = rename S_ (weakEmptyTy {Δ} A)

  data _∣_⊢_↑_   : (Δ : TyContext) → Δ ⊢ctx → Term⁺ → Δ ⊢type → Set
  data _∣_⊢_↓_   : (Δ : TyContext) → Δ ⊢ctx → Term⁻ → Δ ⊢type → Set

  data _∣_⊢_↑_ where
    ⊢` : ∀ {Δ : TyContext} {Γ : Δ ⊢ctx} {A : Δ ⊢type} {x : ℕ}
      → (Var Δ Γ A x)
      → Δ ∣ Γ ⊢ # x ↑ A
    ⊢zero : ∀ {Δ Γ}
      → Δ ∣ Γ ⊢ `zero ↑ `ℕ
    ⊢suc : ∀ {Δ Γ M}
      → Δ ∣ Γ ⊢ M ↑ `ℕ
      → Δ ∣ Γ ⊢ `suc M ↑ `ℕ
    _·_ : ∀ {Δ Γ L M A B}
      → Δ ∣ Γ ⊢ L ↑ A ⇒ B
      → Δ ∣ Γ ⊢ M ↓ A
      → Δ ∣ Γ ⊢ L · M ↑ B
    ⊢[] : ∀ {Δ Γ M B A}
      → Δ ∣ Γ ⊢ M ↑ `∀ B
      → Δ ∣ Γ ⊢ M [ A ] ↑ substOne B (weakEmptyTy A)
    ⊢↓ : ∀ {Δ Γ M A}
      → Δ ∣ Γ ⊢ M ↓ weakEmptyTy A
      → Δ ∣ Γ ⊢ (M ↓ A) ↑ weakEmptyTy A
  
  data _∣_⊢_↓_ where
    ⊢ƛ : ∀ {Δ Γ A B N}
      → Δ ∣ Γ , A ⊢ N ↓ B
      → Δ ∣ Γ ⊢ ƛ N ↓ A ⇒ B
    ⊢Λ : ∀ {Δ Γ M B}
      → Δ ⊢ctx
      → Δ , * ∣ weakCtx Γ ⊢ M ↓ B
      → Δ ∣ Γ ⊢ Λ M ↓ `∀ B
    ⊢↑ : ∀ {Δ Γ M A B}
      → Δ ∣ Γ ⊢ M ↑ A
      → A ≡ B
      → Δ ∣ Γ ⊢ (M ↑) ↓ B

  _ : ∅ ∣ ∅ ⊢ Λ (ƛ ((# 0) ↑)) ↓ (`∀ `var Z ⇒ `var Z)
  _ = ⊢Λ ∅ (⊢ƛ (⊢↑ (⊢` [ Z , refl ]Var) refl))

  ℕ≢⇒ : ∀ {Δ A B} → `ℕ {Δ} ≢ A ⇒ B
  ℕ≢var : ∀ {Δ A N} → `ℕ {Δ} ≢ `var {Δ} {A} N
  ⇒≢∀ : ∀ {Δ A B C} → (_⇒_ {Δ} A B) ≢ `∀ C
  ⇒≢var : ∀ {Δ A B C D} → (_⇒_ {Δ} A B) ≢ `var {Δ} {C} D
  var≢∀ : ∀ {Δ A B C} → (`var {Δ} {A} B) ≢ `∀ C
  ∀≡ : ∀ {Δ A B} → `∀_ {Δ} A ≡ `∀ B → A ≡ B
  dom≡ : ∀ {Δ} {A A′ B B′ : Δ ⊢type} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
  rng≡ : ∀ {Δ} {A A′ B B′ : Δ ⊢type} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′

  ℕ≢∀ : ∀ {Δ N} → `ℕ {Δ} ≢ `∀ N
  ℕ≢∀ ()
  ℕ≢⇒ ()
  ℕ≢var ()
  ⇒≢∀ ()
  ⇒≢var ()
  var≢∀ ()
  ∀≡ refl = refl
  dom≡ refl = refl
  rng≡ refl = refl

  uniq-∋ : ∀ {Δ Γ A B}
    → (∋x : Δ ∣ Γ ∋ A)
    → (∋x′ : Δ ∣ Γ ∋ B)
    → (index ∋x ≡ index ∋x′)
    → A ≡ B
  uniq-∋ Z Z p            = refl
  uniq-∋ (S ∋x) (S ∋x′) p = uniq-∋ ∋x ∋x′ (suc-injective p)

  uniq-↑ : ∀ {Δ Γ M A B}
    → Δ ∣ Γ ⊢ M ↑ A
    → Δ ∣ Γ ⊢ M ↑ B
    → A ≡ B
  uniq-↑ (⊢` [ ∋x , idx≡ ]Var) (⊢` [ ∋x′ , idx≡′ ]Var) = uniq-∋ ∋x ∋x′ (trans idx≡ (sym idx≡′))
  uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′) = refl
  uniq-↑ ⊢zero ⊢zero = refl
  uniq-↑ (⊢suc ⊢N) (⊢suc ⊢N′) = refl
  uniq-↑ (⊢[] ⊢M) (⊢[] ⊢M′) rewrite ∀≡ (uniq-↑ ⊢M ⊢M′) = refl
  uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′) = rng≡ (uniq-↑ ⊢L ⊢L′)

  _≟Tp_ : ∀ {Δ} → (A B : Δ ⊢type) → Dec (A ≡ B)
  (A ⇒ B) ≟Tp `ℕ               = no λ()
  (A ⇒ B) ≟Tp (A′ ⇒ B′)
    with A ≟Tp A′ | B ≟Tp B′
  ...  | no A≢    | _          = no λ{refl → A≢ refl}
  ...  | yes _    | no B≢      = no λ{refl → B≢ refl}
  ...  | yes refl | yes refl   = yes refl
  `ℕ      ≟Tp `ℕ               = yes refl
  (`∀ N) ≟Tp (`∀ N′) with N ≟Tp N′
  ... | no ¬∃ = no λ{ refl → ¬∃ refl }
  ... | yes refl = yes refl
  `ℕ ≟Tp (A ⇒ B) = no λ()
  `ℕ ≟Tp (`∀ _) = no λ ()
  `ℕ ≟Tp `var _ = no λ ()
  (_ ⇒ _) ≟Tp (`∀ _) = no λ()
  (_ ⇒ _) ≟Tp `var _ = no λ()
  (`∀ _) ≟Tp `ℕ = no λ()
  (`∀ _) ≟Tp (_ ⇒ _) = no λ()
  (`∀ _) ≟Tp `var _ = no λ()
  `var _ ≟Tp `ℕ = no λ()
  `var _ ≟Tp (_ ⇒ _) = no λ()
  `var _ ≟Tp (`∀ _) = no λ()
  `var Z ≟Tp `var Z = yes refl
  `var Z ≟Tp `var (S _) = no λ()
  `var (S _) ≟Tp `var Z = no λ()
  `var (S x) ≟Tp `var (S y) with `var x ≟Tp `var y
  ... | no ¬∃ = no λ{ refl → ¬∃ refl }
  ... | yes refl = yes refl

  ¬arg : ∀ {Δ Γ A B L M}
    → Δ ∣ Γ ⊢ L ↑ A ⇒ B
    → ¬ Δ ∣ Γ ⊢ M ↓ A
    → ¬ (∃[ B′ ] Δ ∣ Γ ⊢ L · M ↑ B′)
  ¬arg ⊢L ¬∃ ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬∃ ⊢M′

  ¬switch : ∀ {Δ Γ M A B}
    → Δ ∣ Γ ⊢ M ↑ A
    → A ≢ B
    → ¬ Δ ∣ Γ ⊢ (M ↑) ↓ B
  ¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = A≢B A′≡B

  synthesize : ∀ (Δ : TyContext) (Γ : Δ ⊢ctx) (M : Term⁺)
    → Dec (∃[ A ] Δ ∣ Γ ⊢ M ↑ A)

  inherit : ∀ (Δ : TyContext) (Γ : Δ ⊢ctx) (M : Term⁻) (A : Δ ⊢type)
    → Dec (Δ ∣ Γ ⊢ M ↓ A)

  synthesize Δ Γ `zero = yes ⟨ `ℕ , ⊢zero ⟩
  synthesize Δ Γ (# x) with lookup Γ x
  ... | no ¬∃ = no λ{ ⟨ A , ⊢` ∋x ⟩ → ¬∃ ⟨ A , ∋x ⟩ }
  ... | yes ⟨ A , ∋x ⟩ = yes ⟨ A , ⊢` ∋x ⟩
  synthesize Δ Γ (`suc N) with synthesize Δ Γ N
  ... | no ¬∃ = no λ{ ⟨ .`ℕ , ⊢suc ⊢N ⟩ → ¬∃ ⟨ `ℕ , ⊢N ⟩ }
  ... | yes ⟨ `ℕ , ⊢N ⟩ = yes ⟨ `ℕ , (⊢suc ⊢N) ⟩
  ... | yes ⟨ `∀_ N , ⊢N ⟩ = no λ{ ⟨ `ℕ , ⊢suc ⊢N′ ⟩ → ℕ≢∀ (uniq-↑ ⊢N′ ⊢N) }
  ... | yes ⟨ `var _ , ⊢N ⟩ = no λ{ ⟨ .`ℕ , ⊢suc ⊢N′ ⟩ → ℕ≢var (uniq-↑ ⊢N′ ⊢N) }
  ... | yes ⟨ _ ⇒ _ , ⊢N ⟩ = no λ{ ⟨ .`ℕ , ⊢suc ⊢N′ ⟩ → ℕ≢⇒ (uniq-↑  ⊢N′ ⊢N) } 
  synthesize Δ Γ (L · M) with synthesize Δ Γ L
  ... | no  ¬∃ = no  λ{ ⟨ _ , ⊢L  · _  ⟩ → ¬∃ ⟨ _ , ⊢L ⟩ }
  ... | yes ⟨ `ℕ ,     ⊢L ⟩ = no  λ{ ⟨ _ , ⊢L′ · _  ⟩ → ℕ≢⇒ (uniq-↑ ⊢L ⊢L′) }
  ... | yes ⟨ `∀ N ,   ⊢L ⟩ = no  λ{ ⟨ _ , ⊢L′ · _  ⟩ → ⇒≢∀ (uniq-↑ ⊢L′ ⊢L) }
  ... | yes ⟨ `var x , ⊢L ⟩ = no λ{ ⟨ _ , ⊢L′ · _ ⟩ → ⇒≢var (uniq-↑ ⊢L′ ⊢L) }
  ... | yes ⟨ A ⇒ B ,  ⊢L ⟩ with inherit Δ Γ M A
  ...    | no  ¬∃ = no  (¬arg ⊢L ¬∃)
  ...    | yes ⊢M = yes ⟨ B , ⊢L · ⊢M ⟩
  synthesize Δ Γ (N [ A ]) with synthesize Δ Γ N
  ... | no ¬∃ = no λ{ ⟨ _ , ⊢[] ⊢N ⟩ → ¬∃ ⟨ _ , ⊢N ⟩ }
  ... | yes ⟨ `ℕ , ⊢N ⟩ = no λ{ ⟨ _ , ⊢[] ⊢N′ ⟩ → ℕ≢∀ (uniq-↑ ⊢N ⊢N′) }
  ... | yes ⟨ _ ⇒ _ , ⊢N ⟩ = no λ{ ⟨ _ , ⊢[] ⊢N′ ⟩ → ⇒≢∀ (uniq-↑ ⊢N ⊢N′) }
  ... | yes ⟨ `∀ _ , ⊢N ⟩ = yes ⟨ _ , ⊢[] ⊢N ⟩
  ... | yes ⟨ `var _ , ⊢N ⟩ = no λ{ ⟨ _ , ⊢[] ⊢N′ ⟩ → var≢∀ (uniq-↑ ⊢N ⊢N′) }
  synthesize Δ Γ (M ↓ A) with inherit Δ Γ M (weakEmptyTy A)
  ... | no  ¬∃ = no  λ{ ⟨ _ , ⊢↓ ⊢M ⟩  →  ¬∃ ⊢M }
  ... | yes ⊢M = yes ⟨ _ , ⊢↓ ⊢M ⟩

  inherit Δ Γ (ƛ x) `ℕ = no λ ()
  inherit Δ Γ (ƛ N) (A ⇒ B) with inherit Δ (Γ , A) N B
  ... | no ¬∃  = no  (λ{ (⊢ƛ ⊢N) → ¬∃ ⊢N })
  ... | yes ⊢N = yes (⊢ƛ ⊢N)
  inherit Δ Γ (ƛ x) (`∀ A) = no λ ()
  inherit Δ Γ (ƛ x) (`var x₁) = no λ ()
  inherit Δ Γ (Λ N) `ℕ = no λ ()
  inherit Δ Γ (Λ N) (_ ⇒ _) = no λ ()
  inherit Δ Γ (Λ N) (`var _) = no λ ()
  inherit Δ Γ (Λ N) (`∀ A) with inherit (Δ , *) (weakCtx Γ) N A
  ... | no ¬∃ = no λ{ (⊢Λ _ ⊢N) → ¬∃ ⊢N }
  ... | yes (⊢ƛ N) = yes (⊢Λ Γ (⊢ƛ N))
  ... | yes (⊢Λ Γ′ ⊢N) = yes (⊢Λ Γ (⊢Λ Γ′ ⊢N))
  ... | yes (⊢↑ ⊢N A≡A′) = yes (⊢Λ Γ (⊢↑ ⊢N A≡A′))
  inherit Δ Γ (M ↑) B with synthesize Δ Γ M
  ... | no  ¬∃ = no (λ{ (⊢↑ ⊢M _) → ¬∃ ⟨ _ , ⊢M ⟩ })
  ... | yes ⟨ A , ⊢M ⟩ with A ≟Tp B
  ...   | no  A≢B = no  (¬switch ⊢M A≢B)
  ...   | yes A≡B = yes (⊢↑ ⊢M A≡B) 

  _ : synthesize ∅ ∅
        (((Λ (ƛ (# 0 ↑))) ↓ (`∀ `var Z ⇒ `var Z)) [ `ℕ ])
      ≡ yes ⟨ `ℕ ⇒ `ℕ , ⊢[] (⊢↓ (⊢Λ ∅ (⊢ƛ (⊢↑ (⊢` [ Z , refl ]Var) refl)))) ⟩
  _ = refl

  _ : inherit ∅ ∅
          (Λ (ƛ ((# 0) ↑))) (`∀ `var Z ⇒ `var Z)
        ≡ yes (⊢Λ ∅ (⊢ƛ (⊢↑ (⊢` [ Z , refl ]Var) refl))) 
  _ = refl