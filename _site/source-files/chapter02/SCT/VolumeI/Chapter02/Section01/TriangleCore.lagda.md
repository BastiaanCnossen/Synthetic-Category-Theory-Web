# The three points of the triangle core

The actual three-vertex copair has a concrete inverse obtained from the
four-corner equivalence, the chosen j₀ inclusion and p₀ collapse. The proof
constructs the two ordinary inverse laws directly. It does not construct a
full Retract or assert compatibility between independently chosen squares.
No anima predicate for the three-point or four-point category is needed.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.TriangleCore where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_; _＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization using (const-pre; const-One)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-compose; equiv-transport; equiv-inverse; equiv-cancel-left)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (productMap; product-unitʳ-inverse; product-unitʳ-isEquiv)
open import SCT.VolumeI.Chapter01.Section03.Products.Equivalences using (productMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section04.Core using (Core)
open import SCT.VolumeI.Chapter01.Section04.Points using (name; name⁼)
open import SCT.VolumeI.Chapter01.Section04.Functoriality
  using (mapPost; mapPost-name; mapPost-comp; mapPost-id; mapPost⁼)
open import SCT.VolumeI.Chapter01.Section04.MappingProducts using (module ProductEquivalence)
open import SCT.VolumeI.Chapter01.Section05.Coproducts using (_⊔_; in₁; in₂)
open import SCT.VolumeI.Chapter01.Section05.Copairing
  using (copair; copair-post; copair-cong; copair-β₁; copair-β₂;
    copair-pre₁; copair-pre₂; copair-η; copair-inclusions)
open import SCT.VolumeI.Chapter01.Section05.CoproductConstructions
  using (coproductMap; coproductMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section05.IdentificationRestriction
  using (module IdentificationFromRestrictions)
open import SCT.VolumeI.Chapter01.Section06.Distributivity using (module Distributivity)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism
  using ([1]; zero; one; intervalCore; intervalCore-isEquiv)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  using ([2]; d₁; s₀; vertex₀; vertex₁; vertex₂; d₁-zero; s₀-vertex₁)
open import SCT.VolumeI.Chapter02.Section01.SquareGluing
  using (j₀; j₁; p₀; j₀-vertex₀; j₀-vertex₁; j₀-vertex₂; j₁-vertex₁; p₀-j₀; p₀-j₁)
```

The finite rectangle uses the existing product-distributivity equivalence.
Its two rows are recovered from their point restrictions. Only the recovered
identifications are used; no higher comparison between copair choices is
needed for these ordinary inverse laws.

```agda
module _ {Γ : Context} where
  Two Three Four : CAT Γ
  Two = One ⊔ One
  Three = Two ⊔ One
  Four = Two ⊔ Two

  points₃ : {C : CAT Γ} → MAP One C → MAP One C → MAP One C → MAP Three C
  points₃ x y z = copair (copair x y) z

  points₃-post : {C D : CAT Γ} (h : MAP C D) (x y z : MAP One C) →
    (h ∘ points₃ x y z) =₁ points₃ (h ∘ x) (h ∘ y) (h ∘ z)
  points₃-post h x y z = copair-cong (copair-post x y h) (id₌ (h ∘ z)) ∙
    copair-post (copair x y) z h

  points₃-cong : {C : CAT Γ} {x y z x′ y′ z′ : MAP One C} →
    x =₁ x′ → y =₁ y′ → z =₁ z′ → points₃ x y z =₁ points₃ x′ y′ z′
  points₃-cong α β γ = copair-cong (copair-cong α β) γ

  points₄ : {C : CAT Γ} → MAP One C → MAP One C → MAP One C → MAP One C → MAP Four C
  points₄ x y z w = copair (copair x y) (copair z w)

  points₄-post : {C D : CAT Γ} (h : MAP C D) (x y z w : MAP One C) →
    (h ∘ points₄ x y z w) =₁ points₄ (h ∘ x) (h ∘ y) (h ∘ z) (h ∘ w)
  points₄-post h x y z w =
    copair-cong (copair-post x y h) (copair-post z w h) ∙
      copair-post (copair x y) (copair z w) h

  points₄-cong : {C : CAT Γ} {x y z w x′ y′ z′ w′ : MAP One C} →
    x =₁ x′ → y =₁ y′ → z =₁ z′ → w =₁ w′ →
      points₄ x y z w =₁ points₄ x′ y′ z′ w′
  points₄-cong α β γ δ = copair-cong (copair-cong α β) (copair-cong γ δ)

  private
    grid : MAP Four (Two × Two)
    grid = copair (pair (id Two) (const in₁)) (pair (id Two) (const in₂))

    module Distribution = Distributivity Two One One using (distribute; distribute-isEquiv)

    grid-isEquiv : IsEquiv grid
    grid-isEquiv = equiv-transport comparison
      (equiv-compose units Distribution.distribute
        (coproductMap-isEquiv _ _ unit-equivalence unit-equivalence)
        Distribution.distribute-isEquiv)
      where
        units : MAP Four ((Two × One) ⊔ (Two × One))
        units = coproductMap (product-unitʳ-inverse Two) (product-unitʳ-inverse Two)
        unit-equivalence : IsEquiv (product-unitʳ-inverse Two)
        unit-equivalence = equiv-inverse (product-unitʳ-isEquiv Two)
        component : (j : MAP One Two) →
          (productMap (id Two) j ∘ product-unitʳ-inverse Two) =₁ pair (id Two) (const j)
        component j = pair⁼ (comp-unitˡ (id Two)) (id₌ (const j)) ∙
          productMap-pair (id Two) j (id Two) (terminate Two)
        comparison : (Distribution.distribute ∘ units) =₁ grid
        comparison = copair-cong
          (component in₁ ∙ copair-pre₁ _ _ (product-unitʳ-inverse Two))
          (component in₂ ∙ copair-pre₂ _ _ (product-unitʳ-inverse Two)) ∙
            copair-post _ _ Distribution.distribute

    module Rectangle {C D : CAT Γ} (x₀ x₁ : MAP One C) (y₀ y₁ : MAP One D) where
      rectangle : MAP Four (C × D)
      rectangle = points₄ (pair x₀ y₀) (pair x₁ y₀) (pair x₀ y₁) (pair x₁ y₁)
      horizontalPoints : MAP Two C
      horizontalPoints = copair x₀ x₁
      verticalPoints : MAP Two D
      verticalPoints = copair y₀ y₁

      row : (j : MAP One Two) (y : MAP One D) → (verticalPoints ∘ j) =₁ y →
        (productMap horizontalPoints verticalPoints ∘ pair (id Two) (const j)) =₁
          copair (pair x₀ y) (pair x₁ y)
      row j y ε = row-copair ∙ row-normal
        where
          constant-at : (i : MAP One Two) → (const y ∘ i) =₁ y
          constant-at i = const-One y ∙ const-pre y i
          left-restriction :
            (pair horizontalPoints (const y) ∘ in₁) =₁ (copair (pair x₀ y) (pair x₁ y) ∘ in₁)
          left-restriction = (copair-β₁ (pair x₀ y) (pair x₁ y)) ⁻¹ ∙
            (pair⁼ (copair-β₁ x₀ x₁) (constant-at in₁) ∙ pair-pre horizontalPoints (const y) in₁)
          right-restriction :
            (pair horizontalPoints (const y) ∘ in₂) =₁ (copair (pair x₀ y) (pair x₁ y) ∘ in₂)
          right-restriction = (copair-β₂ (pair x₀ y) (pair x₁ y)) ⁻¹ ∙
            (pair⁼ (copair-β₂ x₀ x₁) (constant-at in₂) ∙ pair-pre horizontalPoints (const y) in₂)
          module Recovered = IdentificationFromRestrictions
            (pair horizontalPoints (const y)) (copair (pair x₀ y) (pair x₁ y))
            left-restriction right-restriction
          row-copair : pair horizontalPoints (const y) =₁ copair (pair x₀ y) (pair x₁ y)
          row-copair = Recovered.identification
          row-normal : (productMap horizontalPoints verticalPoints ∘ pair (id Two) (const j)) =₁
            pair horizontalPoints (const y)
          row-normal = pair⁼ (comp-unitʳ horizontalPoints)
            ((ε ▷ terminate Two) ∙ (comp-assoc (terminate Two) j verticalPoints) ⁻¹) ∙
              productMap-pair horizontalPoints verticalPoints (id Two) (const j)

      comparison : (productMap horizontalPoints verticalPoints ∘ grid) =₁ rectangle
      comparison = copair-cong (row in₁ y₀ (copair-β₁ y₀ y₁))
        (row in₂ y₁ (copair-β₂ y₀ y₁)) ∙ copair-post _ _ (productMap horizontalPoints verticalPoints)

      isEquiv : IsEquiv horizontalPoints → IsEquiv verticalPoints → IsEquiv rectangle
      isEquiv ex ey = equiv-transport comparison
        (equiv-compose grid (productMap horizontalPoints verticalPoints) grid-isEquiv
          (productMap-isEquiv horizontalPoints verticalPoints ex ey))
```

The actual vertex and corner copairs have the historical finite ordering.
The missing10 corner collapses to vertex zero, using p₀'s second restriction;
the other three corner comparisons use its actual first restriction.

```agda
  triangleCore : MAP Three (Core ([2] {Γ = Γ}))
  triangleCore = points₃ (name vertex₀) (name vertex₁) (name vertex₂)

  fourCorners : MAP Four (Core ([1] {Γ = Γ} × [1]))
  fourCorners = points₄ (name (pair zero zero)) (name (pair one zero))
    (name (pair zero one)) (name (pair one one))

  private
    module CoreProduct = ProductEquivalence {Γ = Γ} One [1] [1] using (forward; forward-isEquiv)
    module CoreRectangle = Rectangle (name zero) (name one) (name zero) (name one)
      using (rectangle; isEquiv)

    core-pair-point : (x y : MAP One ([1] {Γ = Γ})) →
      (CoreProduct.forward ∘ name (pair x y)) =₁ pair (name x) (name y)
    core-pair-point x y = pair⁼
      (name⁼ (pair-β₁ x y) ∙ mapPost-name pr₁ (pair x y))
      (name⁼ (pair-β₂ x y) ∙ mapPost-name pr₂ (pair x y)) ∙
        pair-pre (mapPost pr₁) (mapPost pr₂) (name (pair x y))

  fourCorners-isEquiv : IsEquiv (fourCorners)
  fourCorners-isEquiv = equiv-cancel-left fourCorners CoreProduct.forward CoreProduct.forward-isEquiv
    (equiv-transport (comparison ⁻¹) (CoreRectangle.isEquiv intervalCore-isEquiv intervalCore-isEquiv))
    where
      comparison : (CoreProduct.forward ∘ fourCorners) =₁ CoreRectangle.rectangle
      comparison = points₄-cong (core-pair-point zero zero) (core-pair-point one zero)
        (core-pair-point zero one) (core-pair-point one one) ∙
          points₄-post CoreProduct.forward _ _ _ _

  private
    t₀ t₁ t₂ : MAP One (Three)
    t₀ = in₁ ∘ in₁
    t₁ = in₁ ∘ in₂
    t₂ = in₂
    c₀₀ c₁₀ c₀₁ c₁₁ : MAP One (Four)
    c₀₀ = in₁ ∘ in₁
    c₁₀ = in₁ ∘ in₂
    c₀₁ = in₂ ∘ in₁
    c₁₁ = in₂ ∘ in₂

    include : MAP (Three) Four
    include = points₃ c₀₀ c₀₁ c₁₁
    collapse : MAP (Four) Three
    collapse = points₄ t₀ t₀ t₁ t₂

    point₃₀ : {C : CAT Γ} (x y z : MAP One C) → (points₃ x y z ∘ t₀) =₁ x
    point₃₀ x y z = copair-β₁ x y ∙ copair-pre₁ (copair x y) z in₁
    point₃₁ : {C : CAT Γ} (x y z : MAP One C) → (points₃ x y z ∘ t₁) =₁ y
    point₃₁ x y z = copair-β₂ x y ∙ copair-pre₁ (copair x y) z in₂
    point₃₂ : {C : CAT Γ} (x y z : MAP One C) → (points₃ x y z ∘ t₂) =₁ z
    point₃₂ x y z = copair-β₂ (copair x y) z

    point₄₀₀ : {C : CAT Γ} (x y z w : MAP One C) → (points₄ x y z w ∘ c₀₀) =₁ x
    point₄₀₀ x y z w = copair-β₁ x y ∙ copair-pre₁ (copair x y) (copair z w) in₁
    point₄₀₁ : {C : CAT Γ} (x y z w : MAP One C) → (points₄ x y z w ∘ c₀₁) =₁ z
    point₄₀₁ x y z w = copair-β₁ z w ∙ copair-pre₂ (copair x y) (copair z w) in₁
    point₄₁₁ : {C : CAT Γ} (x y z w : MAP One C) → (points₄ x y z w ∘ c₁₁) =₁ w
    point₄₁₁ x y z w = copair-β₂ z w ∙ copair-pre₂ (copair x y) (copair z w) in₂

    collapse-include : (collapse ∘ include) =₁ id (Three)
    collapse-include = copair-inclusions Two One ∙
      (copair-cong (copair-η in₁) (id₌ in₂) ∙
        (points₃-cong (point₄₀₀ t₀ t₀ t₁ t₂) (point₄₀₁ t₀ t₀ t₁ t₂) (point₄₁₁ t₀ t₀ t₁ t₂) ∙
          points₃-post collapse c₀₀ c₀₁ c₁₁))

    retract-corner : (v : MAP One ([2] {Γ = Γ})) (z : MAP One ([1] × [1])) →
      (j₀ ∘ v) =₁ z → (p₀ ∘ z) =₁ v
    retract-corner v z ε = comp-unitˡ v ∙ ((p₀-j₀ ▷ v) ∙
      ((comp-assoc v j₀ p₀) ⁻¹ ∙ (p₀ ◁ ε ⁻¹)))

    p₀-corner₀₀ : (p₀ ∘ pair (zero {Γ = Γ}) zero) =₁ vertex₀
    p₀-corner₀₀ = retract-corner vertex₀ _ j₀-vertex₀
    p₀-corner₀₁ : (p₀ ∘ pair (zero {Γ = Γ}) one) =₁ vertex₁
    p₀-corner₀₁ = retract-corner vertex₁ _ j₀-vertex₁
    p₀-corner₁₁ : (p₀ ∘ pair (one {Γ = Γ}) one) =₁ vertex₂
    p₀-corner₁₁ = retract-corner vertex₂ _ j₀-vertex₂
    p₀-corner₁₀ : (p₀ ∘ pair (one {Γ = Γ}) zero) =₁ vertex₀
    p₀-corner₁₀ = d₁-zero ∙ ((d₁ ◁ s₀-vertex₁) ∙
      (comp-assoc vertex₁ s₀ d₁ ∙ ((p₀-j₁ ▷ vertex₁) ∙
        ((comp-assoc vertex₁ j₁ p₀) ⁻¹ ∙ (p₀ ◁ j₁-vertex₁ ⁻¹)))))

    inclusion-square : (fourCorners ∘ include) =₁ (mapPost j₀ ∘ triangleCore)
    inclusion-square = (points₃-cong
      (name⁼ j₀-vertex₀ ∙ mapPost-name j₀ vertex₀)
      (name⁼ j₀-vertex₁ ∙ mapPost-name j₀ vertex₁)
      (name⁼ j₀-vertex₂ ∙ mapPost-name j₀ vertex₂) ∙
        points₃-post (mapPost j₀) _ _ _) ⁻¹ ∙
      (points₃-cong (point₄₀₀ _ _ _ _) (point₄₀₁ _ _ _ _) (point₄₁₁ _ _ _ _) ∙
        points₃-post fourCorners c₀₀ c₀₁ c₁₁)

    collapse-square : (triangleCore ∘ collapse) =₁ (mapPost p₀ ∘ fourCorners)
    collapse-square = (points₄-cong
      (name⁼ p₀-corner₀₀ ∙ mapPost-name p₀ (pair zero zero))
      (name⁼ p₀-corner₁₀ ∙ mapPost-name p₀ (pair one zero))
      (name⁼ p₀-corner₀₁ ∙ mapPost-name p₀ (pair zero one))
      (name⁼ p₀-corner₁₁ ∙ mapPost-name p₀ (pair one one)) ∙
        points₄-post (mapPost p₀) _ _ _ _) ⁻¹ ∙
      (points₄-cong (point₃₀ _ _ _) (point₃₀ _ _ _) (point₃₁ _ _ _) (point₃₂ _ _ _) ∙
        points₄-post triangleCore t₀ t₀ t₁ t₂)

    u : MAP (Core ([1] {Γ = Γ} × [1])) Four
    u = IsEquiv.inverse fourCorners-isEquiv
    k : MAP (Core ([2] {Γ = Γ})) (Core ([1] × [1]))
    k = mapPost j₀
    l : MAP (Core ([1] {Γ = Γ} × [1])) (Core [2])
    l = mapPost p₀
    target-retraction : (l ∘ k) =₁ id (Core ([2] {Γ = Γ}))
    target-retraction = mapPost-id One [2] ∙ (mapPost⁼ p₀-j₀ ∙ mapPost-comp j₀ p₀)

  triangleCore-inverse : MAP (Core ([2] {Γ = Γ})) Three
  triangleCore-inverse = collapse ∘ (u ∘ k)

  triangleCore-inverse-left : (triangleCore-inverse ∘ triangleCore) =₁ id (Three)
  triangleCore-inverse-left = collapse-include ∙ ((collapse ◁ comp-unitˡ include) ∙
    ((collapse ◁ ((IsEquiv.left-inverse-law fourCorners-isEquiv) ⁻¹ ▷ include)) ∙
      ((collapse ◁ (comp-assoc include fourCorners u) ⁻¹) ∙
        ((collapse ◁ (u ◁ inclusion-square ⁻¹)) ∙
          ((collapse ◁ comp-assoc triangleCore k u) ∙ comp-assoc triangleCore (u ∘ k) collapse)))))

  triangleCore-inverse-right : (triangleCore ∘ triangleCore-inverse) =₁ id (Core ([2] {Γ = Γ}))
  triangleCore-inverse-right = target-retraction ∙ ((l ◁ comp-unitˡ k) ∙
    ((l ◁ ((IsEquiv.right-inverse-law fourCorners-isEquiv) ⁻¹ ▷ k)) ∙
      ((l ◁ (comp-assoc k u fourCorners) ⁻¹) ∙
        (comp-assoc (u ∘ k) fourCorners l ∙ ((collapse-square ▷ (u ∘ k)) ∙
          (comp-assoc (u ∘ k) collapse triangleCore) ⁻¹)))))

  triangleCore-isEquiv : IsEquiv (triangleCore)
  triangleCore-isEquiv = record
    { inverse = triangleCore-inverse
    ; left-inverse-law = triangleCore-inverse-left ⁻¹
    ; right-inverse-law = triangleCore-inverse-right ⁻¹ }
```

The existing core-of-functor-category equivalence sends the three named
triangle vertices to the two constant interval functors and the identity.
The point calculation uses its actual evaluation-induced definition.

```agda
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (product-unitˡ-inverse; product-unitˡ-pr₂-inverse)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map)
open import SCT.VolumeI.Chapter01.Section04.Points using (name-decode)
open import SCT.VolumeI.Chapter01.Section04.Functoriality using (mapPre; mapPre-name)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluation-forward; evaluation-specialize)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun
  using (funName; funName-β; coreFunUncurrying; coreFunUncurrying-isEquiv)

private
  module NamedEndomorphisms {Γ : Context} where
    I : CAT Γ
    I = [1]
    e : MAP (Fun I I × I) I
    e = funEval
    H : MAP (Core (Fun I I)) (Map (One × I) I)
    H = evaluation-forward e One
    r : MAP I (One × I)
    r = product-unitˡ-inverse I

    named-evaluation : (g : MAP One (Fun I I)) →
      (H ∘ name g) =₁ name (funUncurry g)
    named-evaluation g = name⁼ (evaluation-specialize e One g) ∙
      (name-decode (H ∘ name g)) ⁻¹

    decoded-name : (f : MAP I I) → (funUncurry (funName f) ∘ r) =₁ f
    decoded-name f = comp-unitʳ f ∙
      ((f ◁ product-unitˡ-pr₂-inverse I) ∙
        (comp-assoc r pr₂ f ∙ (funName-β f ▷ r)))

    point : (f : MAP I I) →
      (coreFunUncurrying I I ∘ name (funName f)) =₁ name f
    point f = name⁼ (decoded-name f) ∙
      (mapPre-name r (funUncurry (funName f)) ∙
        ((mapPre r ◁ named-evaluation (funName f)) ∙
          comp-assoc (name (funName f)) H (mapPre r)))

module _ {Γ : Context} where
  intervalEndomorphisms : MAP (Three {Γ = Γ}) (Map [1] [1])
  intervalEndomorphisms = points₃ (name (const zero)) (name (id [1])) (name (const one))

  intervalEndomorphisms-image :
    (coreFunUncurrying [1] [1] ∘ triangleCore {Γ = Γ}) =₁ intervalEndomorphisms
  intervalEndomorphisms-image = points₃-cong
    (NamedEndomorphisms.point (const zero)) (NamedEndomorphisms.point (id [1]))
    (NamedEndomorphisms.point (const one)) ∙
      points₃-post (coreFunUncurrying [1] [1]) _ _ _

  intervalEndomorphisms-isEquiv : IsEquiv {Γ = Γ} intervalEndomorphisms
  intervalEndomorphisms-isEquiv = equiv-transport intervalEndomorphisms-image
    (equiv-compose triangleCore (coreFunUncurrying [1] [1]) triangleCore-isEquiv
      (coreFunUncurrying-isEquiv [1] [1]))
```
