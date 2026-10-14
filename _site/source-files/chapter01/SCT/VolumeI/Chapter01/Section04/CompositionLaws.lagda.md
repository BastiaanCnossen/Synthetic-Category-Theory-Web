# Composition laws for mapping terms

The directly recovered laws at an anima parameter have specified complete
relative evaluation images. Universal choices at mapping animae then give
laws at arbitrary term sources by restriction. These choices are kept
separate: recovery itself requires an anima parameter.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.CompositionLaws where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (const-pre)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter01.Section03.Products.PairingOverBase using (product-over)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Composition
open import SCT.VolumeI.Chapter01.Section04.EvaluationOverBase

module _ {Γ : Context} where
  module _ {P : CAT Γ} where
    open Terms.InContext P using (Term)

    evaluation-unitˡ : {C D : CAT Γ} (x : Term (Map C D))
      → IdentificationOver {A = One {Γ}}
          (evaluation-over (compose (identity-map D) x)) (evaluation-over x)
    evaluation-unitˡ {D = D} x =
      let F = evaluation-over x
          ε = evaluation-identity P D
          middle = identification-over
            (IdentificationOver.identification ε ▷ FunctorOverBase.functor F)
            (identification-over-pre F (IdentificationOver.over ε))
          last = identification-over (comp-unitˡ (FunctorOverBase.functor F))
            (identification-over-unitˡ F)
      in comp-identification-over last
          (comp-identification-over middle (evaluation-compose (identity-map D) x))

    evaluation-unitʳ : {C D : CAT Γ} (x : Term (Map C D))
      → IdentificationOver {A = One {Γ}}
          (evaluation-over (compose x (identity-map C))) (evaluation-over x)
    evaluation-unitʳ {C} x =
      let F = evaluation-over x
          ε = evaluation-identity P C
          middle = identification-over
            (FunctorOverBase.functor F ◁ IdentificationOver.identification ε)
            (identification-over-post F (IdentificationOver.over ε))
          last = identification-over (comp-unitʳ (FunctorOverBase.functor F))
            (identification-over-unitʳ F)
      in comp-identification-over last
          (comp-identification-over middle (evaluation-compose x (identity-map C)))

    evaluation-assoc : {A B C D : CAT Γ}
      (z : Term (Map C D)) (y : Term (Map B C)) (x : Term (Map A B))
      → IdentificationOver {A = One {Γ}}
          (evaluation-over (compose (compose z y) x))
          (evaluation-over (compose z (compose y x)))
    evaluation-assoc z y x =
      let H = evaluation-over z
          G = evaluation-over y
          F = evaluation-over x
          hg = evaluation-compose z y
          gf = evaluation-compose y x
          first = evaluation-compose (compose z y) x
          second = identification-over
            (IdentificationOver.identification hg ▷ FunctorOverBase.functor F)
            (identification-over-pre F (IdentificationOver.over hg))
          third = identification-over
            (comp-assoc (FunctorOverBase.functor F) (FunctorOverBase.functor G) (FunctorOverBase.functor H))
            (identification-over-assoc H G F)
          fourth = inverse-identification-over (identification-over
            (FunctorOverBase.functor H ◁ IdentificationOver.identification gf)
            (identification-over-post H (IdentificationOver.over gf)))
          fifth = inverse-identification-over (evaluation-compose z (compose y x))
      in comp-identification-over fifth (comp-identification-over fourth
          (comp-identification-over third (comp-identification-over second first)))

  module Recovered {P : CAT Γ} (pAn : isAn P) where
    open Terms.InContext P using (Term)

    unitˡ : {C D : CAT Γ} (x : Term (Map C D)) → compose (identity-map D) x =₁ x
    unitˡ x = evaluation-recover pAn (evaluation-unitˡ x)

    unitʳ : {C D : CAT Γ} (x : Term (Map C D)) → compose x (identity-map C) =₁ x
    unitʳ x = evaluation-recover pAn (evaluation-unitʳ x)

    assoc : {A B C D : CAT Γ}
      (z : Term (Map C D)) (y : Term (Map B C)) (x : Term (Map A B))
      → compose (compose z y) x =₁ compose z (compose y x)
    assoc z y x = evaluation-recover pAn (evaluation-assoc z y x)

    unitˡ-image : {C D : CAT Γ} (x : Term (Map C D))
      → evaluation⁼ (unitˡ x) =₂ IdentificationOver.identification (evaluation-unitˡ x)
    unitˡ-image x = evaluation-recover-β pAn (evaluation-unitˡ x)

    unitʳ-image : {C D : CAT Γ} (x : Term (Map C D))
      → evaluation⁼ (unitʳ x) =₂ IdentificationOver.identification (evaluation-unitʳ x)
    unitʳ-image x = evaluation-recover-β pAn (evaluation-unitʳ x)

    assoc-image : {A B C D : CAT Γ}
      (z : Term (Map C D)) (y : Term (Map B C)) (x : Term (Map A B))
      → evaluation⁼ (assoc z y x) =₂ IdentificationOver.identification (evaluation-assoc z y x)
    assoc-image z y x = evaluation-recover-β pAn (evaluation-assoc z y x)

  mapComp-unitˡ : (C D : CAT Γ)
    → compose (identity-map D) (id (Map C D)) =₁ id (Map C D)
  mapComp-unitˡ C D = Recovered.unitˡ (map-isAn C D) (id (Map C D))

  mapComp-unitʳ : (C D : CAT Γ)
    → compose (id (Map C D)) (identity-map C) =₁ id (Map C D)
  mapComp-unitʳ C D = Recovered.unitʳ (map-isAn C D) (id (Map C D))

  mapComp-assoc : (A B C D : CAT Γ)
    → let P = (Map C D × Map B C) × Map A B
          z : MAP P (Map C D)
          z = pr₁ ∘ pr₁
          y : MAP P (Map B C)
          y = pr₂ ∘ pr₁
          x : MAP P (Map A B)
          x = pr₂
      in compose (compose z y) x =₁ compose z (compose y x)
  mapComp-assoc A B C D = Recovered.assoc
    (product-isAn (product-isAn (map-isAn C D) (map-isAn B C)) (map-isAn A B))
    (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) pr₂

  private
    specialize : {P Q Z : CAT Γ} {x y : MAP P Z} (α : x =₁ y) (r : MAP Q P)
      {x′ y′ : MAP Q Z} → (x ∘ r) =₁ x′ → (y ∘ r) =₁ y′ → x′ =₁ y′
    specialize α r l t = t ∙ ((α ▷ r) ∙ (l ⁻¹))

    compose-evaluate : {P Q A B C : CAT Γ}
      (y : MAP P (Map B C)) (x : MAP P (Map A B)) (r : MAP Q P)
      {y′ : MAP Q (Map B C)} {x′ : MAP Q (Map A B)}
      → (y ∘ r) =₁ y′ → (x ∘ r) =₁ x′ → (compose y x ∘ r) =₁ compose y′ x′
    compose-evaluate y x r α β = compose⁼ α β ∙ compose-pre y x r

  module _ {P : CAT Γ} where
    open Terms.InContext P using (Term)

    compose-unitˡ : {C D : CAT Γ} (x : Term (Map C D)) → compose (identity-map D) x =₁ x
    compose-unitˡ {C} {D} x = specialize (mapComp-unitˡ C D) x
      (compose-evaluate (identity-map D) (id (Map C D)) x
        (const-pre (mapId D) x) (comp-unitˡ x)) (comp-unitˡ x)

    compose-unitʳ : {C D : CAT Γ} (x : Term (Map C D)) → compose x (identity-map C) =₁ x
    compose-unitʳ {C} {D} x = specialize (mapComp-unitʳ C D) x
      (compose-evaluate (id (Map C D)) (identity-map C) x
        (comp-unitˡ x) (const-pre (mapId C) x)) (comp-unitˡ x)

    compose-assoc : {A B C D : CAT Γ}
      (z : Term (Map C D)) (y : Term (Map B C)) (x : Term (Map A B))
      → compose (compose z y) x =₁ compose z (compose y x)
    compose-assoc {A} {B} {C} {D} z y x =
      let triple = pair (pair z y) x
          first = pair-β₁ z y ∙
            ((pr₁ ◁ pair-β₁ (pair z y) x) ∙ comp-assoc triple pr₁ pr₁)
          second = pair-β₂ z y ∙
            ((pr₂ ◁ pair-β₁ (pair z y) x) ∙ comp-assoc triple pr₁ pr₂)
          third = pair-β₂ (pair z y) x
      in specialize (mapComp-assoc A B C D) triple
        (compose-evaluate (compose (pr₁ ∘ pr₁) (pr₂ ∘ pr₁)) pr₂ triple
          (compose-evaluate (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) triple first second) third)
        (compose-evaluate (pr₁ ∘ pr₁) (compose (pr₂ ∘ pr₁) pr₂) triple first
          (compose-evaluate (pr₂ ∘ pr₁) pr₂ triple second third))
```

The triangle and pentagon use the existing diagram types. Their vertices
and routes are the default composition laws above. Defining these diagrams
does not assert their commutativity.

```agda
module _ {Γ : Context} {P : CAT Γ} where
  open Terms.InContext P using (Term)
  open Boundaries using (TriangleDiagram; triangle-diagram; PentagonDiagram; pentagon-diagram)

  compositionTriangle : {A B C : CAT Γ} (x : Term (Map A B)) (y : Term (Map B C))
    → TriangleDiagram {X = One {Γ}}
        (compose (compose y (identity-map B)) x)
        (compose y (compose (identity-map B) x)) (compose y x)
  compositionTriangle x y = triangle-diagram
    (compose⁼ (compose-unitʳ y) (id₌ x))
    (compose-assoc y (identity-map _) x)
    (compose⁼ (id₌ y) (compose-unitˡ x))

  compositionPentagon : {A B C D E : CAT Γ}
    (x : Term (Map A B)) (y : Term (Map B C)) (z : Term (Map C D)) (w : Term (Map D E))
    → PentagonDiagram {X = One {Γ}}
        (compose (compose (compose w z) y) x)
        (compose (compose w z) (compose y x))
        (compose w (compose z (compose y x)))
        (compose (compose w (compose z y)) x)
        (compose w (compose (compose z y) x))
  compositionPentagon x y z w = pentagon-diagram
    (compose-assoc (compose w z) y x)
    (compose-assoc w z (compose y x))
    (compose⁼ (compose-assoc w z y) (id₌ x))
    (compose-assoc w (compose z y) x)
    (compose⁼ (id₌ w) (compose-assoc z y x))
```
