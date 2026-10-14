# Naturality of specified identifications

Naturality fixes the operation values, their exact actions, and the chosen
components. Input substitution needs a map on changes as well as values.
The calculus below pastes, whiskers and replaces the actual square edges;
it adds no parameter-uniformity or functoriality assumption.
An operation records its values and exact actions on changes. Inputs and
their changes are external data; the input tuples are not categorical products.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section02.Naturality where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair⁼)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (const-comp; pre-constant; post-constant; unitˡ-natural; unitʳ-natural; assoc-natural)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (identity-square₌; paste-square₌; pre-square₌; post-square₌; replace-sides₌; replace-edges₌)

record Inputs₂ {ι υ : Level} (I : Set ι) (J : Set υ) : Set (ι ⊔ υ) where
  constructor inputs₂
  field
    first : I
    second : J

record Inputs₃ {ι υ ω : Level} (I : Set ι) (J : Set υ) (K : Set ω) : Set (ι ⊔ υ ⊔ ω) where
  constructor inputs₃
  field
    first : I
    second : J
    third : K

module _ {Γ : Context} where
  record Operation {ι χ : Level} (I : Set ι)
    (Change : CAT Γ → I → I → Set χ) (C D : CAT Γ)
    : Set (ι ⊔ χ ⊔ c ⊔ m) where
    field
      value : I → MAP C D
      action : {X : CAT Γ} {i j : I}
        → Change X i j → MAP X (Equal (value i) (value j))

  module _ {ι χ : Level} {I : Set ι} {Change : CAT Γ → I → I → Set χ} {C D : CAT Γ} where
    NaturalityAt : (F G : Operation I Change C D)
      (d : (i : I) → Operation.value F i =₁ Operation.value G i)
      {X : CAT Γ} {i j : I} → Change X i j → Set m
    NaturalityAt F G d {i = i} {j} δ =
      (const (d j) ∙ Operation.action F δ) =₁ (Operation.action G δ ∙ const (d i))

    Naturality : (F G : Operation I Change C D)
      → ((i : I) → Operation.value F i =₁ Operation.value G i)
      → Set (ι ⊔ χ ⊔ c ⊔ m)
    Naturality F G d = {X : CAT Γ} {i j : I} (δ : Change X i j) → NaturalityAt F G d δ

    record NaturalIdentification (F G : Operation I Change C D)
      : Set (ι ⊔ χ ⊔ c ⊔ m) where
      field
        component : (i : I) → Operation.value F i =₁ Operation.value G i
        naturality : Naturality F G component

  HomChange : (C D : CAT Γ) → CAT Γ → MAP C D → MAP C D → Set m
  HomChange C D X f g = MAP X (Equal f g)

  PairChange : {ι υ χ ψ : Level} {I : Set ι} {J : Set υ}
    → (CAT Γ → I → I → Set χ) → (CAT Γ → J → J → Set ψ)
    → CAT Γ → Inputs₂ I J → Inputs₂ I J → Set (χ ⊔ ψ)
  PairChange Δ Ε X i j = Inputs₂
    (Δ X (Inputs₂.first i) (Inputs₂.first j))
    (Ε X (Inputs₂.second i) (Inputs₂.second j))

  TripleChange : {ι υ ω χ ψ ζ : Level} {I : Set ι} {J : Set υ} {K : Set ω}
    → (CAT Γ → I → I → Set χ) → (CAT Γ → J → J → Set ψ)
    → (CAT Γ → K → K → Set ζ)
    → CAT Γ → Inputs₃ I J K → Inputs₃ I J K → Set (χ ⊔ ψ ⊔ ζ)
  TripleChange Δ Ε Ζ X i j = Inputs₃
    (Δ X (Inputs₃.first i) (Inputs₃.first j))
    (Ε X (Inputs₃.second i) (Inputs₃.second j))
    (Ζ X (Inputs₃.third i) (Inputs₃.third j))

  Input : (C D : CAT Γ) → Operation (MAP C D) (HomChange C D) C D
  Input C D = record { value = λ f → f; action = λ α → α }

  Post : {ι χ : Level} {I : Set ι} {Change : CAT Γ → I → I → Set χ}
    {B C D : CAT Γ} → MAP C D → Operation I Change B C → Operation I Change B D
  Post u F = record { value = λ i → u ∘ Operation.value F i; action = λ δ → u ◁ Operation.action F δ }

  Pre : {ι χ : Level} {I : Set ι} {Change : CAT Γ → I → I → Set χ}
    {B C D : CAT Γ} → MAP B C → Operation I Change C D → Operation I Change B D
  Pre k F = record { value = λ i → Operation.value F i ∘ k; action = λ δ → Operation.action F δ ▷ k }

  Compose : {ι χ : Level} {I : Set ι} {Change : CAT Γ → I → I → Set χ}
    {B C D : CAT Γ} → Operation I Change C D → Operation I Change B C → Operation I Change B D
  Compose G F = record
    { value = λ i → Operation.value G i ∘ Operation.value F i
    ; action = λ δ → Operation.action G δ ⋆ Operation.action F δ }

  Substitute : {ι υ χ ψ : Level} {I : Set ι} {J : Set υ}
    {Change : CAT Γ → I → I → Set χ} {Change′ : CAT Γ → J → J → Set ψ}
    {C D : CAT Γ} → Operation I Change C D → (h : J → I)
    → ({X : CAT Γ} {i j : J} → Change′ X i j → Change X (h i) (h j))
    → Operation J Change′ C D
  Substitute F h change = record
    { value = λ i → Operation.value F (h i); action = λ δ → Operation.action F (change δ) }

  PairInput₁ : (B C D E : CAT Γ)
    → Operation (Inputs₂ (MAP B C) (MAP D E)) (PairChange (HomChange B C) (HomChange D E)) B C
  PairInput₁ B C D E = record { value = Inputs₂.first; action = Inputs₂.first }

  PairInput₂ : (B C D E : CAT Γ)
    → Operation (Inputs₂ (MAP B C) (MAP D E)) (PairChange (HomChange B C) (HomChange D E)) D E
  PairInput₂ B C D E = record { value = Inputs₂.second; action = Inputs₂.second }

  TripleInput₁ : (A B C D E F : CAT Γ)
    → Operation (Inputs₃ (MAP A B) (MAP C D) (MAP E F))
        (TripleChange (HomChange A B) (HomChange C D) (HomChange E F)) A B
  TripleInput₁ A B C D E F = record { value = Inputs₃.first; action = Inputs₃.first }

  TripleInput₂ : (A B C D E F : CAT Γ)
    → Operation (Inputs₃ (MAP A B) (MAP C D) (MAP E F))
        (TripleChange (HomChange A B) (HomChange C D) (HomChange E F)) C D
  TripleInput₂ A B C D E F = record { value = Inputs₃.second; action = Inputs₃.second }

  TripleInput₃ : (A B C D E F : CAT Γ)
    → Operation (Inputs₃ (MAP A B) (MAP C D) (MAP E F))
        (TripleChange (HomChange A B) (HomChange C D) (HomChange E F)) E F
  TripleInput₃ A B C D E F = record { value = Inputs₃.third; action = Inputs₃.third }

  LeftUnit : (C D : CAT Γ) → Operation (MAP C D) (HomChange C D) C D
  LeftUnit C D = record
    { value = λ f → id D ∘ f; action = λ α → const (id₌ (id D)) ⋆ α }

  RightUnit : (C D : CAT Γ) → Operation (MAP C D) (HomChange C D) C D
  RightUnit C D = record
    { value = λ f → f ∘ id C; action = λ α → α ⋆ const (id₌ (id C)) }

  AssocLeft : (B C D E : CAT Γ)
    → Operation (Inputs₃ (MAP B C) (MAP C D) (MAP D E))
        (TripleChange (HomChange B C) (HomChange C D) (HomChange D E)) B E
  AssocLeft B C D E = Compose
    (Compose (TripleInput₃ B C C D D E) (TripleInput₂ B C C D D E))
    (TripleInput₁ B C C D D E)

  AssocRight : (B C D E : CAT Γ)
    → Operation (Inputs₃ (MAP B C) (MAP C D) (MAP D E))
        (TripleChange (HomChange B C) (HomChange C D) (HomChange D E)) B E
  AssocRight B C D E = Compose (TripleInput₃ B C C D D E)
    (Compose (TripleInput₂ B C C D D E) (TripleInput₁ B C C D D E))
```

## The primitive coherences are natural

The primitive axioms in Coherence are explicit equations on their universal
parameter categories. Specialization proves those equations for arbitrary
families. Here they give naturality properties and natural identifications
with exactly the supplied unitor and associator components.

```agda
module _ {Γ : Context} where
  unitˡ-naturality : (C D : CAT Γ)
    → Naturality (LeftUnit C D) (Input C D) (λ f → comp-unitˡ f)
  unitˡ-naturality C D α = unitˡ-natural α

  unitʳ-naturality : (C D : CAT Γ)
    → Naturality (RightUnit C D) (Input C D) (λ f → comp-unitʳ f)
  unitʳ-naturality C D α = unitʳ-natural α

  assoc-naturality : (B C D E : CAT Γ)
    → Naturality (AssocLeft B C D E) (AssocRight B C D E)
        (λ q → comp-assoc (Inputs₃.first q) (Inputs₃.second q) (Inputs₃.third q))
  assoc-naturality B C D E (inputs₃ α β γ) = assoc-natural γ β α

  unitˡ-identification : (C D : CAT Γ)
    → NaturalIdentification (LeftUnit C D) (Input C D)
  unitˡ-identification C D = record
    { component = λ f → comp-unitˡ f; naturality = unitˡ-naturality C D }

  unitʳ-identification : (C D : CAT Γ)
    → NaturalIdentification (RightUnit C D) (Input C D)
  unitʳ-identification C D = record
    { component = λ f → comp-unitʳ f; naturality = unitʳ-naturality C D }

  assoc-identification : (B C D E : CAT Γ)
    → NaturalIdentification (AssocLeft B C D E) (AssocRight B C D E)
  assoc-identification B C D E = record
    { component = λ q → comp-assoc (Inputs₃.first q) (Inputs₃.second q) (Inputs₃.third q)
    ; naturality = assoc-naturality B C D E }
```

## Composition, whiskering and substitution

```agda
module _ {Γ : Context} {ι χ : Level} {I : Set ι} {Change : CAT Γ → I → I → Set χ} where
  Pair : {B C D : CAT Γ} → Operation I Change B C → Operation I Change B D
    → Operation I Change B (C × D)
  Pair F G = record
    { value = λ i → pair (Operation.value F i) (Operation.value G i)
    ; action = λ δ → pair⁼ (Operation.action F δ) (Operation.action G δ) }

  module _ {C D : CAT Γ} where
    Action : Operation I Change C D → Set (ι ⊔ χ ⊔ c ⊔ m)
    Action F = {X : CAT Γ} {i j : I} → Change X i j
      → MAP X (Equal (Operation.value F i) (Operation.value F j))

    ReAct : (F : Operation I Change C D) → Action F → Operation I Change C D
    ReAct F action′ = record { value = Operation.value F; action = action′ }

    naturality-id : (F : Operation I Change C D)
      → Naturality F F (λ i → id₌ (Operation.value F i))
    naturality-id F δ = identity-square₌ (Operation.action F δ)

    naturality-compose : {F G H : Operation I Change C D}
      {d : (i : I) → Operation.value F i =₁ Operation.value G i}
      {e : (i : I) → Operation.value G i =₁ Operation.value H i}
      → Naturality F G d → Naturality G H e
      → Naturality F H (λ i → e i ∙ d i)
    naturality-compose {d = d} {e} first second {i = i} {j} δ =
      replace-sides₌ (const-comp (e i) (d i)) (const-comp (e j) (d j))
        (paste-square₌ (first δ) (second δ))

    naturality-transport : {F G : Operation I Change C D}
      {d : (i : I) → Operation.value F i =₁ Operation.value G i}
      (top : Action F) (bottom : Action G)
      → ({X : CAT Γ} {i j : I} (δ : Change X i j) → Operation.action F δ =₁ top δ)
      → ({X : CAT Γ} {i j : I} (δ : Change X i j) → Operation.action G δ =₁ bottom δ)
      → Naturality F G d → Naturality (ReAct F top) (ReAct G bottom) d
    naturality-transport top bottom p q n δ = replace-edges₌ (p δ) (q δ) (n δ)

  naturality-post : {B C D : CAT Γ} {F G : Operation I Change B C}
    {d : (i : I) → Operation.value F i =₁ Operation.value G i}
    (u : MAP C D) → Naturality F G d
    → Naturality (Post u F) (Post u G) (λ i → u ◁ d i)
  naturality-post {d = d} u n {i = i} {j} δ =
    replace-sides₌ (post-constant u (d i)) (post-constant u (d j)) (post-square₌ u (n δ))

  naturality-pre : {B C D : CAT Γ} {F G : Operation I Change C D}
    {d : (i : I) → Operation.value F i =₁ Operation.value G i}
    (k : MAP B C) → Naturality F G d
    → Naturality (Pre k F) (Pre k G) (λ i → d i ▷ k)
  naturality-pre {d = d} k n {i = i} {j} δ =
    replace-sides₌ (pre-constant (d i) k) (pre-constant (d j) k) (pre-square₌ k (n δ))

  naturality-substitute : {υ ψ : Level} {J : Set υ} {Change′ : CAT Γ → J → J → Set ψ}
    {C D : CAT Γ} {F G : Operation I Change C D}
    {d : (i : I) → Operation.value F i =₁ Operation.value G i}
    (h : J → I)
    (change : {X : CAT Γ} {i j : J} → Change′ X i j → Change X (h i) (h j))
    → Naturality F G d
    → Naturality (Substitute F h change) (Substitute G h change) (λ i → d (h i))
  naturality-substitute h change n δ = n (change δ)
```

`ReAct` changes only the action at the same values. Its transport law leaves
the component family fixed. Fixed pre/postcomposition is defined with literal
whiskering, rather than horizontal composition with a constant identity.
