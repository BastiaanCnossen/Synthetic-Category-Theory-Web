# The action of a functor on mapping animae

This is `cons:Post_Composition_On_Mapping_Spaces`. We curry internal
composition to obtain the map sending a functor to its action on mapping
animae. The comparisons below identify its specialization with ordinary
postcomposition and construct the naturality square used in the definition
of a subcategory.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open import SCT.VolumeI.Chapter01.Section04.Currying 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Composition 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M
  using (nameMap; decodeMap; oneProduct-in; nameMapIso; name-decode)
open import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence 𝒯 M
  using (evaluate-compose)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M
  using (coreInclusion; core-evaluation)

mappingAction : (E C D : CAT) → MAP (Map C D) (Map (Map E C) (Map E D))
mappingAction E C D = mapCurry (map-isAn C D) mapComp

mappingAction-β : (E C D : CAT) →
  mapUncurry (mappingAction E C D) =₁ mapComp
mappingAction-β E C D = mapCurry-β (map-isAn C D) mapComp

apply-mapPost : {Γ E C D : CAT} (f : MAP C D)
  (g : MAP Γ (Map E C)) (x : MAP Γ E) →
  applyTerm (mapPost f ∘ g) x =₁ (f ∘ applyTerm g x)
apply-mapPost f g x = comp-assoc (pair g x) mapEval f ∙
  ((mapPost-β f ▷ pair g x) ∙ (mapUncurry-at (mapPost f) g x) ⁻¹)

apply-nameMap : {Γ C D : CAT} (f : MAP C D) (x : MAP Γ C) →
  applyTerm (const (nameMap f)) x =₁ (f ∘ x)
apply-nameMap {Γ} f x = (f ◁ pair-β₂ (terminate Γ) x) ∙
  (comp-assoc (pair (terminate Γ) x) pr₂ f ∙
    ((mapCurry-β one-isAn (f ∘ pr₂) ▷ pair (terminate Γ) x) ∙
      (mapUncurry-at (nameMap f) (terminate Γ) x) ⁻¹))

mapPost-compose : {Γ E C D F : CAT} (f : MAP D F)
  (g : MAP Γ (Map C D)) (h : MAP Γ (Map E C)) → isAn Γ →
  (mapPost f ∘ composeTerm g h) =₁ composeTerm (mapPost f ∘ g) h
mapPost-compose f g h Γ-an = mapReflect Γ-an _ _ (right ⁻¹ ∙ left)
  where
  left = (f ◁ evaluate-compose g h) ∙ mapPost-uncurry f (composeTerm g h)
  right = apply-mapPost f (g ∘ pr₁) (applyTerm (h ∘ pr₁) pr₂) ∙
    (applyTerm-cong (comp-assoc pr₁ g (mapPost f)) (idIso (applyTerm (h ∘ pr₁) pr₂)) ∙
      evaluate-compose (mapPost f ∘ g) h)

mapComp-projections : {E C D : CAT} →
  composeTerm (pr₁ {Map C D} {Map E C}) pr₂ =₁ mapComp
mapComp-projections = comp-unitʳ mapComp ∙ (mapComp ◁ pair-projections)

mapComp-post : {E C D F : CAT} (f : MAP D F) →
  (mapPost f ∘ mapComp {E} {C} {D}) =₁
    (mapComp ∘ productMap (mapPost f) (id (Map E C)))
mapComp-post {E} {C} {D} f =
  (mapComp ◁ pair-cong (idIso (mapPost f ∘ pr₁)) (comp-unitˡ pr₂)) ⁻¹ ∙
    (mapPost-compose f pr₁ pr₂ (product-isAn (map-isAn C D) (map-isAn E C)) ∙
      (mapPost f ◁ mapComp-projections ⁻¹))

mappingAction-natural : {A C : CAT} (E D : CAT) (f : MAP A C) →
  (mapPost (mapPost {C = E} f) ∘ mappingAction E D A) =₁
    (mappingAction E D C ∘ mapPost f)
mappingAction-natural {A} {C} E D f = mapReflect (map-isAn D A) _ _
  (right ⁻¹ ∙ (mapComp-post f ∙ left))
  where
  left = (mapPost f ◁ mappingAction-β E D A) ∙
    mapPost-uncurry (mapPost f) (mappingAction E D A)
  right = (mappingAction-β E D C ▷ productMap (mapPost f) (id (Map E D))) ∙
    mapUncurry-restrict (mappingAction E D C) (mapPost f)

compose-nameMap : {Γ E C D : CAT} (f : MAP C D)
  (g : MAP Γ (Map E C)) → isAn Γ →
  composeTerm (const (nameMap f)) g =₁ (mapPost f ∘ g)
compose-nameMap f g Γ-an = mapReflect Γ-an _ _ (right ⁻¹ ∙ left)
  where
  left = apply-nameMap f (applyTerm (g ∘ pr₁) pr₂) ∙
    (applyTerm-cong (const-pre (nameMap f) pr₁) (idIso (applyTerm (g ∘ pr₁) pr₂)) ∙
      evaluate-compose (const (nameMap f)) g)
  right = (f ◁ mapUncurry-as-apply g) ∙ mapPost-uncurry f g

mappingAction-at : {Γ E C D : CAT}
  (g : MAP Γ (Map C D)) (h : MAP Γ (Map E C)) →
  applyTerm (mappingAction E C D ∘ g) h =₁ composeTerm g h
mappingAction-at {E = E} {C} {D} g h =
  (mappingAction-β E C D ▷ pair g h) ∙
    (mapUncurry-at (mappingAction E C D) g h) ⁻¹

mappingAction-specialize : {C D : CAT} (E : CAT) (f : MAP C D) →
  decodeMap (mappingAction E C D ∘ nameMap f) =₁ mapPost {C = E} f
mappingAction-specialize {C} {D} E f = comp-unitʳ (mapPost f) ∙
  (compose-nameMap f (id (Map E C)) (map-isAn E C) ∙
    (mappingAction-at (const (nameMap f)) (id (Map E C)) ∙
      (applyTerm-cong (comp-assoc (terminate (Map E C)) (nameMap f) (mappingAction E C D))
        (idIso (id (Map E C))) ∙
        mapUncurry-at (mappingAction E C D ∘ nameMap f)
          (terminate (Map E C)) (id (Map E C)))))

mappingAction-name : {C D : CAT} (E : CAT) (f : MAP C D) →
  (mappingAction E C D ∘ nameMap f) =₁ nameMap (mapPost {C = E} f)
mappingAction-name {C} {D} E f = nameMapIso (mappingAction-specialize E f) ∙
  (name-decode (mappingAction E C D ∘ nameMap f)) ⁻¹

apply-mapPre : {Γ B C D : CAT} (f : MAP B C)
  (g : MAP Γ (Map C D)) (x : MAP Γ B) →
  applyTerm (mapPre f ∘ g) x =₁ applyTerm g (f ∘ x)
apply-mapPre f g x =
  (mapEval ◁ (pair-cong (comp-unitˡ g) (idIso (f ∘ x)) ∙
    productMap-pair (id _) f g x)) ∙
  (comp-assoc (pair g x) (productMap (id _) f) mapEval ∙
    ((mapPre-β f ▷ pair g x) ∙ (mapUncurry-at (mapPre f) g x) ⁻¹))

compose-named-right : {Γ B C D : CAT} (f : MAP B C)
  (g : MAP Γ (Map C D)) → isAn Γ →
  composeTerm g (const (nameMap f)) =₁ (mapPre f ∘ g)
compose-named-right f g Γ-an = mapReflect Γ-an _ _ (right ⁻¹ ∙ left)
  where
  inner = apply-nameMap f pr₂ ∙
    applyTerm-cong (const-pre (nameMap f) pr₁) (idIso pr₂)
  left = applyTerm-cong (idIso (g ∘ pr₁)) inner ∙
    evaluate-compose g (const (nameMap f))
  right = apply-mapPre f (g ∘ pr₁) pr₂ ∙
    (applyTerm-cong (comp-assoc pr₁ g (mapPre f)) (idIso pr₂) ∙
      mapUncurry-as-apply (mapPre f ∘ g))

evaluate-mapPre : {Γ C D : CAT} (x : Obj-abs C) (f : MAP Γ (Map C D)) →
  (coreInclusion D ∘ (mapPre x ∘ f)) =₁ applyTerm f (const x)
evaluate-mapPre {Γ} x f = applyTerm-cong (comp-unitʳ f) (idIso (const x)) ∙
  (apply-mapPre x (f ∘ id Γ) (terminate Γ) ∙
    (applyTerm-cong (comp-assoc (id Γ) f (mapPre x)) (idIso (terminate Γ)) ∙
      (mapUncurry-at (mapPre x ∘ f) (id Γ) (terminate Γ) ∙
        (core-evaluation (mapPre x ∘ f)) ⁻¹)))

mappingAction-restrict-point : {Γ B C D : CAT} (f : MAP B C)
  (g : MAP Γ (Map C D)) → isAn Γ →
  (coreInclusion (Map B D) ∘ (mapPre (nameMap f) ∘ (mappingAction B C D ∘ g))) =₁
    (mapPre f ∘ g)
mappingAction-restrict-point f g Γ-an = compose-named-right f g Γ-an ∙
  (mappingAction-at g (const (nameMap f)) ∙
    evaluate-mapPre (nameMap f) (mappingAction _ _ _ ∘ g))
```
