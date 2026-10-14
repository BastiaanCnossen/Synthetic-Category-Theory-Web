# Whiskering by an equivalence

Whiskering by an equivalence induces equivalences between identification
animae. First, composing with a fixed identification gives an equivalence.
Squares between functors then handle changes of endpoints, identities and
composites. The two main proofs use two-out-of-six and the fixed-input forms
of interchange.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section03.Squares
open import SCT.VolumeI.Chapter01.Section03.Equivalences
open import SCT.VolumeI.Chapter01.Section03.Factorizations
  using (Factorization; factor-through-equiv)
```

## Composing with a fixed identification

Postcomposition with `β : g =₁ h` and precomposition with `β : f =₁ g` are
functors between identification animae. Evaluated at a family they give
the expected vertical composites with constant families. Their inverses
compose with `β ⁻¹`; the inverse laws are the family inverse reductions,
after identifying the constant family of `β ⁻¹` with the inverse of the
constant family of `β`.

```agda
module _ {Γ : Context} where
  postcomp₌ : {C D : CAT Γ} {f g h : MAP C D}
    → g =₁ h → MAP (Equal f g) (Equal f h)
  postcomp₌ β = const β ∙ id _

  precomp₌ : {C D : CAT Γ} {f g h : MAP C D}
    → f =₁ g → MAP (Equal g h) (Equal f h)
  precomp₌ β = id _ ∙ const β

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    postcomp₌-evaluate : {C D : CAT Γ} {f g h : MAP C D}
      (β : g =₁ h) (α : f ＝ g)
      → (postcomp₌ β ∘ α) =₁ (const β ∙ α)
    postcomp₌-evaluate β α = comp₌-evaluate-One (const β) (id _) α
      (const-pre β α) (comp-unitˡ α)

    precomp₌-evaluate : {C D : CAT Γ} {f g h : MAP C D}
      (β : f =₁ g) (α : g ＝ h)
      → (precomp₌ β ∘ α) =₁ (α ∙ const β)
    precomp₌-evaluate β α = comp₌-evaluate-One (id _) (const β) α
      (comp-unitˡ α) (const-pre β α)

  postcomp₌-isEquiv : {C D : CAT Γ} {f g h : MAP C D}
    (β : g =₁ h) → IsEquiv (postcomp₌ {f = f} β)
  postcomp₌-isEquiv {f = f} β =
    let back : (postcomp₌ (β ⁻¹) ∘ postcomp₌ β) =₁ id _
        back = inv-comp-left (const β) (id _) ∙
          (comp₌-cong (const-inv β) (id₌ (postcomp₌ β)) ∙
            postcomp₌-evaluate (β ⁻¹) (postcomp₌ β))
        forth : (postcomp₌ β ∘ postcomp₌ (β ⁻¹)) =₁ id _
        forth = comp-inv-left (const β) (id _) ∙
          (comp₌-cong (id₌ (const β)) (comp₌-cong (const-inv β) (id₌ (id _))) ∙
            postcomp₌-evaluate β (postcomp₌ (β ⁻¹)))
    in record
      { inverse = postcomp₌ (β ⁻¹)
      ; left-inverse-law = back ⁻¹
      ; right-inverse-law = forth ⁻¹ }

  precomp₌-isEquiv : {C D : CAT Γ} {f g h : MAP C D}
    (β : f =₁ g) → IsEquiv (precomp₌ {h = h} β)
  precomp₌-isEquiv {h = h} β =
    let back : (precomp₌ (β ⁻¹) ∘ precomp₌ β) =₁ id _
        back = comp-inv-right (id _) (const β) ∙
          (comp₌-cong (id₌ (precomp₌ β)) (const-inv β) ∙
            precomp₌-evaluate (β ⁻¹) (precomp₌ β))
        forth : (precomp₌ β ∘ precomp₌ (β ⁻¹)) =₁ id _
        forth = inv-comp-right (id _) (const β) ∙
          (comp₌-cong (comp₌-cong (id₌ (id _)) (const-inv β)) (id₌ (const β)) ∙
            precomp₌-evaluate β (precomp₌ (β ⁻¹)))
    in record
      { inverse = precomp₌ (β ⁻¹)
      ; left-inverse-law = back ⁻¹
      ; right-inverse-law = forth ⁻¹ }
```

## Changing endpoints through a square

Let `u : MAP X (f ＝ g)` and `v : MAP X (f′ ＝ g′)` be families, and let
`α : f =₁ f′` and `β : g =₁ g′` change their endpoints. A commuting square of
identification families with top `u`, bottom `v` and prescribed constant
sides `const α` and `const β` gives a square between functors from `v` to
`postcomp₌ β`: its source map is `u`, its target map is `precomp₌ α`, and
the evaluation laws convert the family square into its cell. Postcomposition
and precomposition are equivalences, so the square results of Equivalences
transfer the equivalence property between `u` and `v` in both directions.

```agda
module _ {Γ : Context} where
  endpoint-square : {X C D : CAT Γ} {f g f′ g′ : MAP C D}
    (u : MAP X (Equal f g)) (v : MAP X (Equal f′ g′))
    (α : f =₁ f′) (β : g =₁ g′)
    → SquareCell₌ u v (const α) (const β)
    → Square v (postcomp₌ β)
  endpoint-square u v α β κ = square u (precomp₌ α)
    ((precomp₌-evaluate α v) ⁻¹ ∙ (κ ∙ postcomp₌-evaluate β u))

  endpoint-change-reflects-isEquiv : {X C D : CAT Γ} {f g f′ g′ : MAP C D}
    (u : MAP X (Equal f g)) (v : MAP X (Equal f′ g′))
    (α : f =₁ f′) (β : g =₁ g′)
    → SquareCell₌ u v (const α) (const β) → IsEquiv v → IsEquiv u
  endpoint-change-reflects-isEquiv u v α β κ =
    square-source-map-isEquiv (endpoint-square u v α β κ)
      (postcomp₌-isEquiv β) (precomp₌-isEquiv α)

  endpoint-change-preserves-isEquiv : {X C D : CAT Γ} {f g f′ g′ : MAP C D}
    (u : MAP X (Equal f g)) (v : MAP X (Equal f′ g′))
    (α : f =₁ f′) (β : g =₁ g′)
    → SquareCell₌ u v (const α) (const β) → IsEquiv u → IsEquiv v
  endpoint-change-preserves-isEquiv u v α β κ =
    square-functor-isEquiv (endpoint-square u v α β κ)
      (postcomp₌-isEquiv β) (precomp₌-isEquiv α)
```

## Identity functors and identified functors

Whiskering by an identity functor is identified with the identity of the
identification anima after changing endpoints by the unitors. The required
family square is the whiskering law for identity functors at the universal
family `id (f ＝ g)`. Whiskering by identified functors `F` and `G` is
related by changing endpoints along the whiskered identification. The family
square is fixed-input interchange at the universal family.

```agda
module _ {Γ : Context} where
  postWhisker-id-isEquiv : {C D : CAT Γ} (f g : MAP C D)
    → IsEquiv (postWhisker {f = f} {g} (id D))
  postWhisker-id-isEquiv {D = D} f g =
    endpoint-change-reflects-isEquiv (postWhisker (id D)) (id (Equal f g))
      (comp-unitˡ f) (comp-unitˡ g)
      (postWhisker-id (id (Equal f g)) ∙
        (comp₌-cong (id₌ _) (comp-unitʳ (postWhisker (id D)))) ⁻¹)
      (id-isEquiv (Equal f g))

  preWhisker-id-isEquiv : {C D : CAT Γ} (f g : MAP C D)
    → IsEquiv (preWhisker {f = f} {g} (id C))
  preWhisker-id-isEquiv {C} f g =
    endpoint-change-reflects-isEquiv (preWhisker (id C)) (id (Equal f g))
      (comp-unitʳ f) (comp-unitʳ g)
      (preWhisker-id (id (Equal f g)) ∙
        (comp₌-cong (id₌ _) (comp-unitʳ (preWhisker (id C)))) ⁻¹)
      (id-isEquiv (Equal f g))

  postWhisker-transport-isEquiv : {B C D : CAT Γ} {F G : MAP C D}
    (τ : F =₁ G) (f g : MAP B C)
    → IsEquiv (postWhisker {f = f} {g} G) → IsEquiv (postWhisker {f = f} {g} F)
  postWhisker-transport-isEquiv {F = F} {G} τ f g =
    endpoint-change-reflects-isEquiv (postWhisker F) (postWhisker G)
      (τ ▷ f) (τ ▷ g)
      (comp₌-cong (comp-unitʳ (postWhisker G)) (id₌ _) ∙
        (interchange-fixedOuter τ (id (Equal f g)) ∙
          (comp₌-cong (id₌ _) (comp-unitʳ (postWhisker F))) ⁻¹))

  preWhisker-transport-isEquiv : {B C D : CAT Γ} {h k : MAP B C}
    (σ : h =₁ k) (f g : MAP C D)
    → IsEquiv (preWhisker {f = f} {g} k) → IsEquiv (preWhisker {f = f} {g} h)
  preWhisker-transport-isEquiv {h = h} {k} σ f g =
    endpoint-change-reflects-isEquiv (preWhisker h) (preWhisker k)
      (f ◁ σ) (g ◁ σ)
      (comp₌-cong (comp-unitʳ (preWhisker k)) (id₌ _) ∙
        ((interchange-fixedInner (id (Equal f g)) σ) ⁻¹ ∙
          (comp₌-cong (id₌ _) (comp-unitʳ (preWhisker h))) ⁻¹))
```

## Whiskering by composites and equivalences

The composition laws transfer equivalence between whiskering by a composite
and composing the whiskering functors, keeping both endpoint associators.
For a chosen inverse `G` of `F`, the two successive composites in the
alternating sequence of whiskering by `F`, `G`, `F` are equivalences.
Two-out-of-six proves that whiskering by `F` is an equivalence, without
constructing a separate corrected inverse.

```agda
module _ {Γ : Context} where
  postWhisker-composite-isEquiv : {B C D E : CAT Γ} (f g : MAP B C) (u : MAP C D) (v : MAP D E)
    → IsEquiv (postWhisker {f = f} {g} (v ∘ u))
    → IsEquiv (postWhisker v ∘ postWhisker {f = f} {g} u)
  postWhisker-composite-isEquiv f g u v =
    endpoint-change-preserves-isEquiv (postWhisker (v ∘ u))
      (postWhisker v ∘ postWhisker u) (comp-assoc f u v) (comp-assoc g u v)
      (comp₌-cong (postWhisker v ◁ comp-unitʳ (postWhisker u)) (id₌ _) ∙
        (postWhisker-comp (id (Equal f g)) u v ∙
          (comp₌-cong (id₌ _) (comp-unitʳ (postWhisker (v ∘ u)))) ⁻¹))

  preWhisker-composite-isEquiv : {A B C D : CAT Γ} (f g : MAP C D) (k : MAP B C) (l : MAP A B)
    → IsEquiv (preWhisker {f = f} {g} (k ∘ l))
    → IsEquiv (preWhisker l ∘ preWhisker {f = f} {g} k)
  preWhisker-composite-isEquiv f g k l =
    endpoint-change-reflects-isEquiv (preWhisker l ∘ preWhisker k)
      (preWhisker (k ∘ l)) (comp-assoc l k f) (comp-assoc l k g)
      (comp₌-cong (comp-unitʳ (preWhisker (k ∘ l))) (id₌ _) ∙
        (preWhisker-comp (id (Equal f g)) k l ∙
          (comp₌-cong (id₌ _) (preWhisker l ◁ comp-unitʳ (preWhisker k))) ⁻¹))

  postWhisker-isEquiv : {B C D : CAT Γ} (F : MAP C D) → IsEquiv F
    → (f g : MAP B C) → IsEquiv (postWhisker {f = f} {g} F)
  postWhisker-isEquiv F e f g =
    let G = IsEquiv.inverse e
        first = postWhisker-composite-isEquiv f g F G
          (postWhisker-transport-isEquiv ((IsEquiv.left-inverse-law e) ⁻¹) f g
            (postWhisker-id-isEquiv f g))
        second = postWhisker-composite-isEquiv (F ∘ f) (F ∘ g) G F
          (postWhisker-transport-isEquiv ((IsEquiv.right-inverse-law e) ⁻¹) (F ∘ f) (F ∘ g)
            (postWhisker-id-isEquiv (F ∘ f) (F ∘ g)))
    in TwoOutOfSix.first (two-out-of-six (postWhisker F) (postWhisker G)
         (postWhisker F) first second)

  preWhisker-isEquiv : {C D E : CAT Γ} (F : MAP C D) → IsEquiv F
    → (f g : MAP D E) → IsEquiv (preWhisker {f = f} {g} F)
  preWhisker-isEquiv F e f g =
    let G = IsEquiv.inverse e
        first = preWhisker-composite-isEquiv f g F G
          (preWhisker-transport-isEquiv ((IsEquiv.right-inverse-law e) ⁻¹) f g
            (preWhisker-id-isEquiv f g))
        second = preWhisker-composite-isEquiv (f ∘ F) (g ∘ F) G F
          (preWhisker-transport-isEquiv ((IsEquiv.left-inverse-law e) ⁻¹) (f ∘ F) (g ∘ F)
            (preWhisker-id-isEquiv (f ∘ F) (g ∘ F)))
    in TwoOutOfSix.first (two-out-of-six (preWhisker F) (preWhisker G)
         (preWhisker F) first second)
```

## Factoring through whiskering

Whiskering by an equivalence is an equivalence, so every family of
identifications between the whiskered functors factors through it, with a
specified triangle. The family parameter `A` is arbitrary. Applying the
construction again to identification animae factors families of higher
identifications; the suffix ₂ marks these second-level inputs.

```agda
module _ {Γ : Context} where
  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    factor-through-postWhisker : {B C D : CAT Γ} (F : MAP C D) → IsEquiv F
      → {f g : MAP B C} → (α : (F ∘ f) ＝ (F ∘ g))
      → Factorization (postWhisker F) α
    factor-through-postWhisker F e {f} {g} α =
      factor-through-equiv (postWhisker-isEquiv F e f g) α

    factor-through-preWhisker : {C D E : CAT Γ} (F : MAP C D) → IsEquiv F
      → {f g : MAP D E} → (α : (f ∘ F) ＝ (g ∘ F))
      → Factorization (preWhisker F) α
    factor-through-preWhisker F e {f} {g} α =
      factor-through-equiv (preWhisker-isEquiv F e f g) α

  factor-through-postWhisker₂ : {A A′ B C D : CAT Γ} (F : MAP C D) → IsEquiv F
    → {f g : MAP B C} (α β : MAP A (Equal f g))
    → (p : MAP A′ (Equal (F ◁ α) (F ◁ β)))
    → Factorization (postWhisker (postWhisker F)) p
  factor-through-postWhisker₂ F e {f} {g} α β p =
    factor-through-postWhisker (postWhisker F) (postWhisker-isEquiv F e f g) p

  factor-through-preWhisker₂ : {A A′ C D E : CAT Γ} (F : MAP C D) → IsEquiv F
    → {f g : MAP D E} (α β : MAP A (Equal f g))
    → (p : MAP A′ (Equal (α ▷ F) (β ▷ F)))
    → Factorization (postWhisker (preWhisker F)) p
  factor-through-preWhisker₂ F e {f} {g} α β p =
    factor-through-postWhisker (preWhisker F) (preWhisker-isEquiv F e f g) p
```

## Contractible codomains

Postwhiskering with the terminal equivalence identifies the full
identification anima with its contractible terminal target.

```agda
module _ {Γ : Context} where
  contractible-identifications : {C X : CAT Γ} → IsContractible C
    → (f g : MAP X C) → IsContractible (Equal f g)
  contractible-identifications {C} e f g =
    contractible-source (postWhisker (terminate C))
      (postWhisker-isEquiv (terminate C) e f g)
      (terminal-identifications-isEquiv (terminate C ∘ f) (terminate C ∘ g))
```
