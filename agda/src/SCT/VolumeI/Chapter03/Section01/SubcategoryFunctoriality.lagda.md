# Functoriality of the subcategory construction

For `cons:Functoriality_Subcategory`, a functor preserving collections
induces a functor between their presentations. The comparison with the
ambient functor is retained. Embedding of the target inclusion gives
compatibility with identities, composition, and natural isomorphisms,
as recorded in `rmk:Functoriality_Subcategory`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.Section01.SubcategoryFunctoriality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M using (mapPost; mapPost-comp)
open import SCT.VolumeI.Chapter01.Section06.Embeddings 𝒯 P using (embedding-reflect)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S
  using (SubcategoryPresentation)
open import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences 𝒯 M ℱ P I E S
  using (module Presented)

module Induced {C D : CAT} {V : MorphismCollection C} {W : MorphismCollection D}
  (A : SubcategoryPresentation V) (B : SubcategoryPresentation W)
  (f : MAP C D) (preserves : PreservesMorphisms f V W) where

  i = SubcategoryPresentation.inclusion A
  j = FunctorLift.lift (SubcategoryPresentation.arrows A)
  k = FunctorLift.lift preserves

  arrows : FunctorLift (MorphismCollection.inclusion W) (mapPost {C = [1]} (f ∘ i))
  arrows = record { lift = k ∘ j
    ; comparison = mapPost-comp i f ∙
        ((mapPost f ◁ FunctorLift.comparison (SubcategoryPresentation.arrows A)) ∙
          (comp-assoc j (MorphismCollection.inclusion V) (mapPost f) ∙
            ((FunctorLift.comparison preserves ▷ j) ∙
              (comp-assoc j k (MorphismCollection.inclusion W)) ⁻¹))) }

  module Factor = Presented.Factor W B (f ∘ i) arrows using (factor; comparison)

  functor : MAP (SubcategoryPresentation.subcategory A) (SubcategoryPresentation.subcategory B)
  functor = Factor.factor

  comparison : (SubcategoryPresentation.inclusion B ∘ functor) =₁ (f ∘ i)
  comparison = Factor.comparison

induced-identity : {C : CAT} {W : MorphismCollection C} (A : SubcategoryPresentation W) →
  Induced.functor A A (id C) (identity-preserves W) =₁ id (SubcategoryPresentation.subcategory A)
induced-identity {W = W} A = embedding-reflect (SubcategoryPresentation.inclusion A)
  (Presented.inclusion-isEmbedding W A) _ _
  ((comp-unitʳ (SubcategoryPresentation.inclusion A)) ⁻¹ ∙
    (comp-unitˡ (SubcategoryPresentation.inclusion A) ∙
      Induced.comparison A A (id _) (identity-preserves W)))

induced-composition : {C D E : CAT}
  {U : MorphismCollection C} {V : MorphismCollection D} {W : MorphismCollection E}
  (A : SubcategoryPresentation U) (B : SubcategoryPresentation V) (G : SubcategoryPresentation W)
  (f : MAP C D) (g : MAP D E) (F : PreservesMorphisms f U V) (H : PreservesMorphisms g V W) →
  (Induced.functor B G g H ∘ Induced.functor A B f F) =₁
    Induced.functor A G (g ∘ f) (composition-preserves f g {U} {V} {W} F H)
induced-composition {U = U} {V = V} {W = W} A B G f g F H = embedding-reflect (SubcategoryPresentation.inclusion G)
  (Presented.inclusion-isEmbedding W G) _ _
  ((Induced.comparison A G (g ∘ f) (composition-preserves f g {U} {V} {W} F H)) ⁻¹ ∙
    ((comp-assoc (SubcategoryPresentation.inclusion A) f g) ⁻¹ ∙
      ((g ◁ Induced.comparison A B f F) ∙
        (comp-assoc (Induced.functor A B f F) (SubcategoryPresentation.inclusion B) g ∙
          ((Induced.comparison B G g H ▷ Induced.functor A B f F) ∙
            (comp-assoc (Induced.functor A B f F) (Induced.functor B G g H)
              (SubcategoryPresentation.inclusion G)) ⁻¹)))))

induced-cong : {C D : CAT} {V : MorphismCollection C} {W : MorphismCollection D}
  (A : SubcategoryPresentation V) (B : SubcategoryPresentation W)
  {f g : MAP C D} (F : PreservesMorphisms f V W) (G : PreservesMorphisms g V W) →
  f =₁ g → Induced.functor A B f F =₁ Induced.functor A B g G
induced-cong {W = W} A B F G α = embedding-reflect (SubcategoryPresentation.inclusion B)
  (Presented.inclusion-isEmbedding W B) _ _
  ((Induced.comparison A B _ G) ⁻¹ ∙
    ((α ▷ SubcategoryPresentation.inclusion A) ∙ Induced.comparison A B _ F))
```
