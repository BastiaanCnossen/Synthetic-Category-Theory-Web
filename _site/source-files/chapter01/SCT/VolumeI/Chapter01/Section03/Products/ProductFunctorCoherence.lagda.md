# Coherence of the product functor

The specified identification `productMap-comp f F g G` is the paired
evaluation of the two postcomposed square cells of the product projections.
Its naturality in the outer functors `F`, `G` is therefore the naturality of
paired evaluation in its inputs (`pair-evaluation-natural-inputs`), and its
naturality in the inner functors `f`, `g` the naturality of paired
evaluation in the restricting functor (`pair-evaluation-natural`), each
applied to the naturality squares of the two square cells. Pasting the two
naturality squares along the common side gives naturality in all four
functors. The unit laws of `productMap-comp` are computed coordinatewise by
the unit-projection lemmas of Triangles.

Naturality is stated for identification families with constant sides; the
instances at `One` have the suffix `-One`.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; postWhisker-id₌; preWhisker-id₌;
    module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (postWhisker-id; preWhisker-id)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (productMap; productMap-id; productMap-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (post-triangle-change)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
```

## Naturality of composition

```agda
module _ {Γ : Context} where
  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    productMap-comp-natural-outer : {C C′ C″ D D′ D″ : CAT Γ}
      (f : MAP C C′) (g : MAP D D′) {F F′ : MAP C′ C″} {G G′ : MAP D′ D″}
      (θ : F ＝ F′) (ψ : G ＝ G′)
      → SquareCell₌ (productMap-cong θ ψ ▷ productMap f g) (productMap-cong (θ ▷ f) (ψ ▷ g))
          (const (productMap-comp f F g G)) (const (productMap-comp f F′ g G′))
    productMap-comp-natural-outer  f g {F} {F′} {G} {G′} θ ψ =
      let h = productMap f g
          b = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
          d = pair-β₂ (f ∘ pr₁) (g ∘ pr₂)
          e = post-square-cell F pr₁ f pr₁ h b
          e′ = post-square-cell F′ pr₁ f pr₁ h b
          k = post-square-cell G pr₂ g pr₂ h d
          k′ = post-square-cell G′ pr₂ g pr₂ h d
      in replace-sides₌ (pair-evaluation-const h e k) (pair-evaluation-const h e′ k′)
        (pair-evaluation-natural-inputs (θ ▷ pr₁) (ψ ▷ pr₂) h
          (const e) (const e′) (const k) (const k′) ((θ ▷ f) ▷ pr₁) ((ψ ▷ g) ▷ pr₂)
          (post-square-cell-outer pr₁ f pr₁ h b θ) (post-square-cell-outer pr₂ g pr₂ h d ψ))

    productMap-comp-natural-inner : {C C′ C″ D D′ D″ : CAT Γ}
      {f f′ : MAP C C′} {g g′ : MAP D D′}
      (α : f ＝ f′) (β : g ＝ g′) (F : MAP C′ C″) (G : MAP D′ D″)
      → SquareCell₌ (productMap F G ◁ productMap-cong α β) (productMap-cong (F ◁ α) (G ◁ β))
          (const (productMap-comp f F g G)) (const (productMap-comp f′ F g′ G))
    productMap-comp-natural-inner  {f = f} {f′} {g} {g′} α β F G =
      let h = productMap f g
          h′ = productMap f′ g′
          δ = productMap-cong α β
          b = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
          b′ = pair-β₁ (f′ ∘ pr₁) (g′ ∘ pr₂)
          d = pair-β₂ (f ∘ pr₁) (g ∘ pr₂)
          d′ = pair-β₂ (f′ ∘ pr₁) (g′ ∘ pr₂)
          e = post-square-cell F pr₁ f pr₁ h b
          e′ = post-square-cell F pr₁ f′ pr₁ h′ b′
          k = post-square-cell G pr₂ g pr₂ h d
          k′ = post-square-cell G pr₂ g′ pr₂ h′ d′
      in replace-sides₌ (pair-evaluation-const h e k) (pair-evaluation-const h′ e′ k′)
        (pair-evaluation-natural (F ∘ pr₁) (G ∘ pr₂) δ
          (const e) (const e′) (const k) (const k′) ((F ◁ α) ▷ pr₁) ((G ◁ β) ▷ pr₂)
          (post-square-cell-inner pr₁ pr₁ F b b′ α δ (productMap-cong-triangle₁ α β))
          (post-square-cell-inner pr₂ pr₂ G d d′ β δ (productMap-cong-triangle₂ α β)))

    productMap-comp-natural : {C C′ C″ D D′ D″ : CAT Γ}
      {f f′ : MAP C C′} {g g′ : MAP D D′}
      {F F′ : MAP C′ C″} {G G′ : MAP D′ D″}
      (α : f ＝ f′) (β : g ＝ g′)
      (θ : F ＝ F′) (ψ : G ＝ G′)
      → SquareCell₌ (productMap-cong θ ψ ⋆ productMap-cong α β)
          (productMap-cong (θ ⋆ α) (ψ ⋆ β))
          (const (productMap-comp f F g G)) (const (productMap-comp f′ F′ g′ G′))
    productMap-comp-natural {f′ = f′} {g′ = g′} {F} {G = G} α β θ ψ =
      replace-edges₌ (id₌ _) ((productMap-cong-comp (θ ▷ f′) (F ◁ α) (ψ ▷ g′) (G ◁ β)) ⁻¹)
        (adjoin-square₌ (productMap-comp-natural-inner α β F G)
          (productMap-comp-natural-outer f′ g′ θ ψ))

  productMap-comp-natural-outer-One : {C C′ C″ D D′ D″ : CAT Γ}
    (f : MAP C C′) (g : MAP D D′) {F F′ : MAP C′ C″} {G G′ : MAP D′ D″}
    (θ : F =₁ F′) (ψ : G =₁ G′)
    → SquareCell₌ (productMap-cong θ ψ ▷ productMap f g) (productMap-cong (θ ▷ f) (ψ ▷ g))
        (productMap-comp f F g G) (productMap-comp f F′ g G′)
  productMap-comp-natural-outer-One f g θ ψ =
    unconst-sides₌ (productMap-comp-natural-outer f g θ ψ)

  productMap-comp-natural-inner-One : {C C′ C″ D D′ D″ : CAT Γ}
    {f f′ : MAP C C′} {g g′ : MAP D D′}
    (α : f =₁ f′) (β : g =₁ g′) (F : MAP C′ C″) (G : MAP D′ D″)
    → SquareCell₌ (productMap F G ◁ productMap-cong α β) (productMap-cong (F ◁ α) (G ◁ β))
        (productMap-comp f F g G) (productMap-comp f′ F g′ G)
  productMap-comp-natural-inner-One α β F G =
    unconst-sides₌ (productMap-comp-natural-inner α β F G)

  productMap-comp-natural-One : {C C′ C″ D D′ D″ : CAT Γ}
    {f f′ : MAP C C′} {g g′ : MAP D D′}
    {F F′ : MAP C′ C″} {G G′ : MAP D′ D″}
    (α : f =₁ f′) (β : g =₁ g′) (θ : F =₁ F′) (ψ : G =₁ G′)
    → SquareCell₌ (productMap-cong θ ψ ⋆ productMap-cong α β)
        (productMap-cong (θ ⋆ α) (ψ ⋆ β))
        (productMap-comp f F g G) (productMap-comp f′ F′ g′ G′)
  productMap-comp-natural-One α β θ ψ =
    unconst-sides₌ (productMap-comp-natural α β θ ψ)
```

The four inputs vary independently: the universal instance is parameterized
by the product of the four identification animae.

```agda
  module UniversalComposition {C C′ C″ D D′ D″ : CAT Γ}
    (f f′ : MAP C C′) (g g′ : MAP D D′)
    (F F′ : MAP C′ C″) (G G′ : MAP D′ D″) where

    source : CAT Γ
    source = ((Equal F F′) × (Equal G G′)) × ((Equal f f′) × (Equal g g′))

    firstOuter : MAP source (Equal F F′)
    firstOuter = pr₁ ∘ pr₁

    secondOuter : MAP source (Equal G G′)
    secondOuter = pr₂ ∘ pr₁

    firstInner : MAP source (Equal f f′)
    firstInner = pr₁ ∘ pr₂

    secondInner : MAP source (Equal g g′)
    secondInner = pr₂ ∘ pr₂

    naturality : SquareCell₌
      (productMap-cong firstOuter secondOuter ⋆ productMap-cong firstInner secondInner)
      (productMap-cong (firstOuter ⋆ firstInner) (secondOuter ⋆ secondInner))
      (const (productMap-comp f F g G)) (const (productMap-comp f′ F′ g′ G′))
    naturality = productMap-comp-natural firstInner secondInner firstOuter secondOuter
```

## Unit laws

The projection triangles of `productMap-id` combine those of
`pair-projections` and of the pairing of left unitors. The unit laws of
`productMap-comp` then hold coordinatewise.

```agda
module _ {Γ : Context} where
  productMap-id-triangle₁ : (C D : CAT Γ)
    → (comp-unitʳ pr₁ ∙ (pr₁ ◁ productMap-id C D)) =₂
        (comp-unitˡ pr₁ ∙ pair-β₁ (id C ∘ pr₁) (id D ∘ pr₂))
  productMap-id-triangle₁ C D =
    pair⁼-triangle₁-One (comp-unitˡ pr₁) (comp-unitˡ pr₂) ∙
    (comp₌-cong pair-projections-triangle₁
        (id₌ (pr₁ ◁ pair⁼ (comp-unitˡ pr₁) (comp-unitˡ pr₂))) ∙
      project-composite pr₁ pair-projections
        (pair⁼ (comp-unitˡ pr₁) (comp-unitˡ pr₂)) (comp-unitʳ pr₁))

  productMap-id-triangle₂ : (C D : CAT Γ)
    → (comp-unitʳ pr₂ ∙ (pr₂ ◁ productMap-id C D)) =₂
        (comp-unitˡ pr₂ ∙ pair-β₂ (id C ∘ pr₁) (id D ∘ pr₂))
  productMap-id-triangle₂ C D =
    pair⁼-triangle₂-One (comp-unitˡ pr₁) (comp-unitˡ pr₂) ∙
    (comp₌-cong pair-projections-triangle₂
        (id₌ (pr₂ ◁ pair⁼ (comp-unitˡ pr₁) (comp-unitˡ pr₂))) ∙
      project-composite pr₂ pair-projections
        (pair⁼ (comp-unitˡ pr₁) (comp-unitˡ pr₂)) (comp-unitʳ pr₂))

  productMap-unitˡ : {C C′ D D′ : CAT Γ} (f : MAP C C′) (g : MAP D D′)
    → (productMap-cong (comp-unitˡ f) (comp-unitˡ g) ∙ productMap-comp f (id C′) g (id D′)) =₂
        (comp-unitˡ (productMap f g) ∙ (productMap-id C′ D′ ▷ productMap f g))
  productMap-unitˡ {C} {C′} {D} {D′} f g =
    let h = productMap f g
        h′ = productMap (id C′ ∘ f) (id D′ ∘ g)
        J = productMap (id C′) (id D′)
        δ = productMap-id C′ D′
        b = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
        d = pair-β₂ (f ∘ pr₁) (g ∘ pr₂)
        b′ = pair-β₁ ((id C′ ∘ f) ∘ pr₁) ((id D′ ∘ g) ∘ pr₂)
        d′ = pair-β₂ ((id C′ ∘ f) ∘ pr₁) ((id D′ ∘ g) ∘ pr₂)
        bJ = pair-β₁ (id C′ ∘ pr₁) (id D′ ∘ pr₂)
        dJ = pair-β₂ (id C′ ∘ pr₁) (id D′ ∘ pr₂)
        out = productMap-cong (comp-unitˡ f) (comp-unitˡ g)
        step = productMap-comp f (id C′) g (id D′)
        e = post-square-cell (id C′) pr₁ f pr₁ h b
        k = post-square-cell (id D′) pr₂ g pr₂ h d
    in pair₌-extensionality
      (left-unit-projection pr₁ f pr₁ h h′ J δ b b′ bJ out step
        (productMap-id-triangle₁ C′ D′)
        (pair⁼-triangle₁-One (comp-unitˡ f ▷ pr₁) (comp-unitˡ g ▷ pr₂))
        (pair-evaluation-over₁-One (id C′ ∘ pr₁) (id D′ ∘ pr₂) h e k))
      (left-unit-projection pr₂ g pr₂ h h′ J δ d d′ dJ out step
        (productMap-id-triangle₂ C′ D′)
        (pair⁼-triangle₂-One (comp-unitˡ f ▷ pr₁) (comp-unitˡ g ▷ pr₂))
        (pair-evaluation-over₂-One (id C′ ∘ pr₁) (id D′ ∘ pr₂) h e k))

  productMap-unitʳ : {C C′ D D′ : CAT Γ} (f : MAP C C′) (g : MAP D D′)
    → (productMap-cong (comp-unitʳ f) (comp-unitʳ g) ∙ productMap-comp (id C) f (id D) g) =₂
        (comp-unitʳ (productMap f g) ∙ (productMap f g ◁ productMap-id C D))
  productMap-unitʳ {C} {C′} {D} {D′} f g =
    let h = productMap f g
        h′ = productMap (f ∘ id C) (g ∘ id D)
        J = productMap (id C) (id D)
        δ = productMap-id C D
        b = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
        d = pair-β₂ (f ∘ pr₁) (g ∘ pr₂)
        b′ = pair-β₁ ((f ∘ id C) ∘ pr₁) ((g ∘ id D) ∘ pr₂)
        d′ = pair-β₂ ((f ∘ id C) ∘ pr₁) ((g ∘ id D) ∘ pr₂)
        bJ = pair-β₁ (id C ∘ pr₁) (id D ∘ pr₂)
        dJ = pair-β₂ (id C ∘ pr₁) (id D ∘ pr₂)
        out = productMap-cong (comp-unitʳ f) (comp-unitʳ g)
        step = productMap-comp (id C) f (id D) g
        e = post-square-cell f pr₁ (id C) pr₁ J bJ
        k = post-square-cell g pr₂ (id D) pr₂ J dJ
    in pair₌-extensionality
      (right-unit-projection pr₁ f pr₁ h h′ J δ b b′ bJ out step
        (productMap-id-triangle₁ C D)
        (pair⁼-triangle₁-One (comp-unitʳ f ▷ pr₁) (comp-unitʳ g ▷ pr₂))
        (pair-evaluation-over₁-One (f ∘ pr₁) (g ∘ pr₂) J e k))
      (right-unit-projection pr₂ g pr₂ h h′ J δ d d′ dJ out step
        (productMap-id-triangle₂ C D)
        (pair⁼-triangle₂-One (comp-unitʳ f ▷ pr₁) (comp-unitʳ g ▷ pr₂))
        (pair-evaluation-over₂-One (f ∘ pr₁) (g ∘ pr₂) J e k))
```

## Changing one factor at a time

A product functor changing only the first factor composes with another such
functor, and a change of the first factor commutes with a change of the
second. Both comparisons are natural in identification families of the
changed factor.

```agda
module _ {Γ : Context} where
  private
    module _ {A : CAT Γ} where
      open Terms.Equalities A using (_＝_)

      fixed-second-square : {X X′ Y Y′ : CAT Γ} {f f′ : MAP X X′} {g k : MAP Y Y′}
        (α : f ＝ f′) (δ : g =₁ k)
        → SquareCell₌ (productMap-cong α (const (id₌ g))) (productMap-cong α (const (id₌ k)))
            (const (productMap-cong (id₌ f) δ)) (const (productMap-cong (id₌ f′) δ))
      fixed-second-square  {f = f} {f′} α δ =
        replace-sides₌ (productMap-cong-constant (id₌ f) δ) (productMap-cong-constant (id₌ f′) δ)
          (productMap-cong-square (identity-square₌ α)
            (transpose-square₌ (identity-square₌ (const {P = A} δ))))

      unit-square : {X Y : CAT Γ} {f g : MAP X Y} (ρ : f =₁ g) (u : f ＝ f)
        → u =₁ const (id₌ f) → SquareCell₌ u (const (id₌ g)) (const ρ) (const ρ)
      unit-square  ρ u p =
        replace-edges₌ (p ⁻¹) (id₌ _) (transpose-square₌ (identity-square₌ (const {P = A} ρ)))

    normalize-side : {A X Y : CAT Γ} {a b c d e : MAP X Y}
      (r₄ : e =₁ d) (r₃ : d =₁ c) (r₂ : b =₁ c) (r₁ : a =₁ b)
      → ((const {P = A} r₄) ⁻¹ ∙ ((const r₃) ⁻¹ ∙ (const r₂ ∙ const r₁))) =₁
          const (r₄ ⁻¹ ∙ (r₃ ⁻¹ ∙ (r₂ ∙ r₁)))
    normalize-side {A} r₄ r₃ r₂ r₁ =
      const-comp {X = A} (r₄ ⁻¹) (r₃ ⁻¹ ∙ (r₂ ∙ r₁)) ∙
        comp₌-cong ((const-inv {X = A} r₄) ⁻¹)
          (const-comp {X = A} (r₃ ⁻¹) (r₂ ∙ r₁) ∙
            comp₌-cong ((const-inv {X = A} r₃) ⁻¹) (const-comp {X = A} r₂ r₁))

  productMap-first-comp : {Y X Z C : CAT Γ} (f : MAP X Z) (σ : MAP Y X)
    → (productMap f (id C) ∘ productMap σ (id C)) =₁ productMap (f ∘ σ) (id C)
  productMap-first-comp {C = C} f σ =
    productMap-cong (id₌ (f ∘ σ)) (comp-unitˡ (id C)) ∙ productMap-comp σ f (id C) (id C)

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    productMap-first-comp-inputs : {Y X Z C : CAT Γ} {f g : MAP X Z}
      (α : f ＝ g) (σ : MAP Y X)
      → SquareCell₌ (productMap-cong α (const (id₌ (id C))) ▷ productMap σ (id C))
          (productMap-cong (α ▷ σ) (const (id₌ (id C))))
          (const (productMap-first-comp f σ)) (const (productMap-first-comp g σ))
    productMap-first-comp-inputs  {C = C} {f} {g} α σ =
      let identity = const {P = A} (id₌ (id C))
          reduce = const-cong (preWhisker-id₌ (id C) (id C)) ∙ pre-constant (id₌ (id C)) (id C)
          first = replace-edges₌ (id₌ _) (productMap-cong₂ (id₌ (α ▷ σ)) reduce)
            (productMap-comp-natural-outer σ (id C) α identity)
      in replace-sides₌
        (const-comp {X = A} (productMap-cong (id₌ (f ∘ σ)) (comp-unitˡ (id C)))
          (productMap-comp σ f (id C) (id C)))
        (const-comp {X = A} (productMap-cong (id₌ (g ∘ σ)) (comp-unitˡ (id C)))
          (productMap-comp σ g (id C) (id C)))
        (paste-square₌ first (fixed-second-square (α ▷ σ) (comp-unitˡ (id C))))

    productMap-first-comp-substitution : {Y X Z C : CAT Γ} (f : MAP X Z)
      {σ τ : MAP Y X} (γ : σ ＝ τ)
      → SquareCell₌ (productMap f (id C) ◁ productMap-cong γ (const (id₌ (id C))))
          (productMap-cong (f ◁ γ) (const (id₌ (id C))))
          (const (productMap-first-comp f σ)) (const (productMap-first-comp f τ))
    productMap-first-comp-substitution  {C = C} f {σ} {τ} γ =
      let identity = const {P = A} (id₌ (id C))
          reduce = const-cong (postWhisker-id₌ (id C) (id C)) ∙ post-constant (id C) (id₌ (id C))
          first = replace-edges₌ (id₌ _) (productMap-cong₂ (id₌ (f ◁ γ)) reduce)
            (productMap-comp-natural-inner γ identity f (id C))
      in replace-sides₌
        (const-comp {X = A} (productMap-cong (id₌ (f ∘ σ)) (comp-unitˡ (id C)))
          (productMap-comp σ f (id C) (id C)))
        (const-comp {X = A} (productMap-cong (id₌ (f ∘ τ)) (comp-unitˡ (id C)))
          (productMap-comp τ f (id C) (id C)))
        (paste-square₌ first (fixed-second-square (f ◁ γ) (comp-unitˡ (id C))))

  productMap-cong-identity-One : {X Y C : CAT Γ} {σ τ : MAP Y X} (γ : σ =₁ τ)
    → productMap-cong γ (const (id₌ (id C))) =₂ productMap-cong γ (id₌ (id C))
  productMap-cong-identity-One {C = C} γ =
    productMap-cong₂ (id₌ γ) (const-One (id₌ (id C)))

  productMap-separate : {A B C D : CAT Γ} (f : MAP A C) (g : MAP B D)
    → (productMap (id C) g ∘ productMap f (id B)) =₁
        (productMap f (id D) ∘ productMap (id A) g)
  productMap-separate {A} {B} {C} {D} f g =
    (productMap-comp (id A) f g (id D)) ⁻¹ ∙
    ((productMap-cong (comp-unitʳ f) (comp-unitˡ g)) ⁻¹ ∙
    (productMap-cong (comp-unitˡ f) (comp-unitʳ g) ∙ productMap-comp f (id C) (id B) g))

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    productMap-separate-inputs : {X Y B C : CAT Γ} {u v : MAP X Y}
      (γ : u ＝ v) (i : MAP B C)
      → SquareCell₌ (productMap (id Y) i ◁ productMap-cong γ (const (id₌ (id B))))
          (productMap-cong γ (const (id₌ (id C))) ▷ productMap (id X) i)
          (const (productMap-separate u i)) (const (productMap-separate v i))
    productMap-separate-inputs  {X} {Y} {B} {C} {u} {v} γ i =
      let identityB = const {P = A} (id₌ (id B))
          identityC = const {P = A} (id₌ (id C))
          step₁ = productMap-comp-natural-inner γ identityB (id Y) i
          step₂ = replace-sides₌
            (productMap-cong-constant (comp-unitˡ u) (comp-unitʳ i))
            (productMap-cong-constant (comp-unitˡ v) (comp-unitʳ i))
            (productMap-cong-square (postWhisker-id γ)
              (unit-square (comp-unitʳ i) (i ◁ identityB)
                (const-cong (postWhisker-id₌ i (id B)) ∙ post-constant i (id₌ (id B)))))
          step₃ = inverse-square₌ (replace-sides₌
            (productMap-cong-constant (comp-unitʳ u) (comp-unitˡ i))
            (productMap-cong-constant (comp-unitʳ v) (comp-unitˡ i))
            (productMap-cong-square (preWhisker-id γ)
              (unit-square (comp-unitˡ i) (identityC ▷ i)
                (const-cong (preWhisker-id₌ (id C) i) ∙ pre-constant (id₌ (id C)) i))))
          step₄ = inverse-square₌ (productMap-comp-natural-outer (id X) i γ identityC)
      in replace-sides₌
        (normalize-side (productMap-comp (id X) u i (id C))
          (productMap-cong (comp-unitʳ u) (comp-unitˡ i))
          (productMap-cong (comp-unitˡ u) (comp-unitʳ i))
          (productMap-comp u (id Y) (id B) i))
        (normalize-side (productMap-comp (id X) v i (id C))
          (productMap-cong (comp-unitʳ v) (comp-unitˡ i))
          (productMap-cong (comp-unitˡ v) (comp-unitʳ i))
          (productMap-comp v (id Y) (id B) i))
        (paste-square₌ (paste-square₌ (paste-square₌ step₁ step₂) step₃) step₄)
```

## Associativity of the actual product compositor

Both private projection calculations retain the selected raw compositor.
Pairing reflection assembles their full associativity equation.

```agda
private
  module RawProductCalculation where
    module _ {Γ : Context} where
      module CoordinateComposition {V0 V1 V2 K0 K1 K2 K3 : CAT Γ}
        (π0 : MAP V0 K0) (π1 : MAP V1 K1) (π2 : MAP V2 K2)
        (a : MAP K0 K1) (b : MAP K1 K2) (c : MAP K2 K3)
        (F : MAP V0 V1) (G : MAP V1 V2) (GF : MAP V0 V2)
        (δ : (G ∘ F) =₁ GF)
        (βf : (π1 ∘ F) =₁ (a ∘ π0))
        (βg : (π2 ∘ G) =₁ (b ∘ π1))
        (βgf : (π2 ∘ GF) =₁ ((b ∘ a) ∘ π0)) where
        Dfg = post-square-cell b π0 a π1 F βf
        Dgh = post-square-cell c π1 b π2 G βg
        Dfhg = post-square-cell (c ∘ b) π0 a π1 F βf
        Dgfh = post-square-cell c π0 (b ∘ a) π2 GF βgf

        compatibility : SquareCell₌ (π2 ◁ δ) Dfg
            (restrict-triangle π2 G βg F) βgf →
          (Dgfh ∙ (((c ∘ π2) ◁ δ) ∙ comp-assoc F G (c ∘ π2))) =₂
          ((comp-assoc a b c ▷ π0) ∙ (Dfhg ∙ (Dgh ▷ F)))
        compatibility image =
          let outside = (comp-assoc π0 (b ∘ a) c) ⁻¹
              leftImage = c ◁ βgf
              inputA = comp-assoc GF π2 c
              change = (c ∘ π2) ◁ δ
              sourceA = comp-assoc F G (c ∘ π2)
              normalizeShort = comp₌-cong (id₌ outside)
                (post-triangle-change c π2 G F GF δ βg βgf Dfg image) ∙
                comp₌-assoc outside (leftImage ∙ inputA) (change ∙ sourceA)
              η = comp-assoc a b c ▷ π0
              sourceCorner = comp-assoc π1 b c
              imageBefore = (c ◁ βg) ∙ comp-assoc G π2 c
              nextCoordinate = post-square-cell c π0 (b ∘ a) (b ∘ π1) F Dfg
              outerSquare = (post-square-cell-comp π0 a π1 F βf b c) ⁻¹
              simplifyCorner = (preWhisker F ◁ comp-inv-left sourceCorner imageBefore) ∙
                (preWhisker-comp₌ sourceCorner Dgh F) ⁻¹
              normalizeLong = comp₌-cong (id₌ outside)
                (comp₌-assoc (c ◁ Dfg) (comp-assoc F (b ∘ π1) c) (imageBefore ▷ F)) ∙
                (comp₌-assoc outside
                  ((c ◁ Dfg) ∙ comp-assoc F (b ∘ π1) c) (imageBefore ▷ F) ∙
                (comp₌-cong (id₌ nextCoordinate) simplifyCorner ∙
                (comp₌-assoc nextCoordinate (sourceCorner ▷ F) (Dgh ▷ F) ∙
                (comp₌-cong outerSquare (id₌ (Dgh ▷ F)) ∙
                  (comp₌-assoc η Dfhg (Dgh ▷ F)) ⁻¹))))
          in normalizeLong ⁻¹ ∙ normalizeShort

      module ProductCompositorImages {X0 X1 X2 A0 A1 A2 : CAT Γ}
        (f : MAP X0 X1) (g : MAP X1 X2) (u : MAP A0 A1) (v : MAP A1 A2) where
        F = productMap f u
        G = productMap g v
        first = post-square-cell g pr₁ f pr₁ F (pair-β₁ (f ∘ pr₁) (u ∘ pr₂))
        second = post-square-cell v pr₂ u pr₂ F (pair-β₂ (f ∘ pr₁) (u ∘ pr₂))
        first-image : SquareCell₌ (pr₁ ◁ productMap-comp f g u v) first
          (restrict-triangle pr₁ G (pair-β₁ (g ∘ pr₁) (v ∘ pr₂)) F)
          (pair-β₁ ((g ∘ f) ∘ pr₁) ((v ∘ u) ∘ pr₂))
        first-image = pair-evaluation-over₁-One (g ∘ pr₁) (v ∘ pr₂) F first second
        second-image : SquareCell₌ (pr₂ ◁ productMap-comp f g u v) second
          (restrict-triangle pr₂ G (pair-β₂ (g ∘ pr₁) (v ∘ pr₂)) F)
          (pair-β₂ ((g ∘ f) ∘ pr₁) ((v ∘ u) ∘ pr₂))
        second-image = pair-evaluation-over₂-One (g ∘ pr₁) (v ∘ pr₂) F first second

      module RawProductAssociativity {X0 X1 X2 X3 A0 A1 A2 A3 : CAT Γ}
        (f : MAP X0 X1) (g : MAP X1 X2) (h : MAP X2 X3)
        (u : MAP A0 A1) (v : MAP A1 A2) (w : MAP A2 A3) where
        F = productMap f u
        G = productMap g v
        H = productMap h w
        GF = productMap (g ∘ f) (v ∘ u)
        δ = productMap-comp f g u v
        βf1 = pair-β₁ (f ∘ pr₁) (u ∘ pr₂)
        βf2 = pair-β₂ (f ∘ pr₁) (u ∘ pr₂)
        βg1 = pair-β₁ (g ∘ pr₁) (v ∘ pr₂)
        βg2 = pair-β₂ (g ∘ pr₁) (v ∘ pr₂)
        βh1 = pair-β₁ (h ∘ pr₁) (w ∘ pr₂)
        βh2 = pair-β₂ (h ∘ pr₁) (w ∘ pr₂)
        βgf1 = pair-β₁ ((g ∘ f) ∘ pr₁) ((v ∘ u) ∘ pr₂)
        βgf2 = pair-β₂ ((g ∘ f) ∘ pr₁) ((v ∘ u) ∘ pr₂)
        βhg1 = pair-β₁ ((h ∘ g) ∘ pr₁) ((w ∘ v) ∘ pr₂)
        βhg2 = pair-β₂ ((h ∘ g) ∘ pr₁) ((w ∘ v) ∘ pr₂)
        module First = CoordinateComposition pr₁ pr₁ pr₁ f g h F G GF δ βf1 βg1 βgf1
        module Second = CoordinateComposition pr₂ pr₂ pr₂ u v w F G GF δ βf2 βg2 βgf2

        L : ((H ∘ G) ∘ F) =₁ productMap (h ∘ (g ∘ f)) (w ∘ (v ∘ u))
        L = productMap-comp (g ∘ f) h (v ∘ u) w ∙ ((H ◁ δ) ∙ comp-assoc F G H)
        R : ((H ∘ G) ∘ F) =₁ productMap (h ∘ (g ∘ f)) (w ∘ (v ∘ u))
        R = productMap-cong (comp-assoc f g h) (comp-assoc u v w) ∙
          (productMap-comp f (h ∘ g) u (w ∘ v) ∙ (productMap-comp g h v w ▷ F))

        private
          short1 = lies-over-comp pr₁
            (lies-over-comp pr₁ (restrict-triangle-assoc pr₁ H βh1 G F)
              (restrict-change-square-One pr₁ H (h ∘ pr₁) βh1 δ))
            (ProductCompositorImages.first-image (g ∘ f) h (v ∘ u) w)
          short2 = lies-over-comp pr₂
            (lies-over-comp pr₂ (restrict-triangle-assoc pr₂ H βh2 G F)
              (restrict-change-square-One pr₂ H (w ∘ pr₂) βh2 δ))
            (ProductCompositorImages.second-image (g ∘ f) h (v ∘ u) w)
          long1 = lies-over-comp pr₁
            (lies-over-comp pr₁
              (restrict-square-One pr₁ (productMap-comp g h v w) (ProductCompositorImages.first g h v w)
                (restrict-triangle pr₁ H βh1 G) βhg1 F (ProductCompositorImages.first-image g h v w))
              (ProductCompositorImages.first-image f (h ∘ g) u (w ∘ v)))
            (unconst-sides₌ (productMap-cong-triangle₁ (comp-assoc f g h) (comp-assoc u v w)))
          long2 = lies-over-comp pr₂
            (lies-over-comp pr₂
              (restrict-square-One pr₂ (productMap-comp g h v w) (ProductCompositorImages.second g h v w)
                (restrict-triangle pr₂ H βh2 G) βhg2 F (ProductCompositorImages.second-image g h v w))
              (ProductCompositorImages.second-image f (h ∘ g) u (w ∘ v)))
            (unconst-sides₌ (productMap-cong-triangle₂ (comp-assoc f g h) (comp-assoc u v w)))

        compatibility : L =₂ R
        compatibility = pair₌-unique short1 short2
          (replace-edges₌ (id₌ _) ((First.compatibility (ProductCompositorImages.first-image f g u v)) ⁻¹) long1)
          (replace-edges₌ (id₌ _) ((Second.compatibility (ProductCompositorImages.second-image f g u v)) ⁻¹) long2)
module _ {Γ : Context} where
  productMap-comp-associativity : {X0 X1 X2 X3 A0 A1 A2 A3 : CAT Γ}
    (f : MAP X0 X1) (g : MAP X1 X2) (h : MAP X2 X3)
    (u : MAP A0 A1) (v : MAP A1 A2) (w : MAP A2 A3)
    → (productMap-comp (g ∘ f) h (v ∘ u) w ∙
        ((productMap h w ◁ productMap-comp f g u v) ∙
          comp-assoc (productMap f u) (productMap g v) (productMap h w))) =₂
      (productMap-cong (comp-assoc f g h) (comp-assoc u v w) ∙
        (productMap-comp f (h ∘ g) u (w ∘ v) ∙
          (productMap-comp g h v w ▷ productMap f u)))
  productMap-comp-associativity = RawProductCalculation.RawProductAssociativity.compatibility
```
