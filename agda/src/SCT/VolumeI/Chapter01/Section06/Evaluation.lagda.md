# The evaluation-induced uncurrying functor

For an arbitrary evaluation `e : F × C → D`, the book constructs an
actual functor `Map T F → Map (T × C) D`. Only its parameter, a mapping
anima, is used for mapping-anima currying. No condition on `T` or `F`
is imposed here. This is the construction preceding `def:Functor_Category`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section06.Evaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Uncurrying 𝒯 M using (module Reassociation; productMap-pair)
open import SCT.VolumeI.Chapter01.Section03.Specialization 𝒯 M

module Evaluation {F C D : CAT} (e : MAP (F × C) D) where
  uncurry : {T : CAT} → MAP T F → MAP (T × C) D
  uncurry {T} g = e ∘ productMap g (id C)

  uncurry-cong : {T : CAT} {g h : MAP T F} → =₁ g h → =₁ (uncurry g) (uncurry h)
  uncurry-cong α = e ◁ productMap-cong α (idIso (id C))

  uncurry-pre : {S T : CAT} (g : MAP T F) (r : MAP S T) →
    =₁ (uncurry (g ∘ r)) (uncurry g ∘ productMap r (id C))
  uncurry-pre g r = invIso (comp-assoc (productMap r (id C)) (productMap g (id C)) e) ∙
    (e ◁ invIso (productMap-cong (idIso (g ∘ r)) (comp-unitˡ (id C)) ∙
      productMap-comp r g (id C) (id C)))

  uncurry-id : =₁ (uncurry (id F)) e
  uncurry-id = comp-unitʳ e ∙ (e ◁ productMap-id F C)

  module At (T : CAT) where
    parameter = Map T F
    evaluation : MAP (parameter × (T × C)) D
    evaluation = uncurry mapEval ∘ Associativity.backward parameter T C

    forward : MAP parameter (Map (T × C) D)
    forward = mapCurry (map-isAn T F) evaluation

    represents : {X : CAT} (g : MAP X parameter) →
      =₁ (mapUncurry (forward ∘ g))
        (uncurry (mapUncurry g) ∘ Associativity.backward X T C)
    represents {X} g =
      (invIso (uncurry-pre mapEval (productMap g (id T))) ▷ Associativity.backward X T C) ∙
      (invIso (comp-assoc (Associativity.backward X T C)
        (productMap (productMap g (id T)) (id C)) (uncurry mapEval)) ∙
      (((uncurry mapEval) ◁ Reassociation.backward-natural g) ∙
      (comp-assoc (productMap g (id (T × C))) (Associativity.backward parameter T C) (uncurry mapEval) ∙
      ((mapCurry-β (map-isAn T F) evaluation ▷ productMap g (id (T × C))) ∙
        mapUncurry-pre forward g))))

    terminal-regroup : =₁
      (Associativity.backward One T C ∘ oneProduct-in (T × C))
      (productMap (oneProduct-in T) (id C))
    terminal-regroup = pair-cong
      (invIso (pair-pre (terminate T) (id T) pr₁) ∙
        pair-cong (terminal-iso _ _)
          (invIso (comp-unitˡ pr₁) ∙ comp-unitʳ pr₁ ∙
            ((pr₁ ◁ oneProduct-retraction (T × C)) ∙ comp-assoc (oneProduct-in (T × C)) (pr₂ {One} {T × C}) (pr₁ {T} {C}))) ∙
        pair-pre pr₁ (pr₁ ∘ pr₂) (oneProduct-in (T × C)))
      (invIso (comp-unitˡ pr₂) ∙ comp-unitʳ pr₂ ∙
        ((pr₂ ◁ oneProduct-retraction (T × C)) ∙ comp-assoc (oneProduct-in (T × C)) (pr₂ {One} {T × C}) (pr₂ {T} {C}))) ∙
      pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) (oneProduct-in (T × C))

    decode-forward : (p : Obj-abs parameter) →
      =₁ (decodeMap (forward ∘ p)) (uncurry (decodeMap p))
    decode-forward p = invIso (uncurry-pre (mapUncurry p) (oneProduct-in T)) ∙
      (((uncurry (mapUncurry p)) ◁ terminal-regroup) ∙
      (comp-assoc (oneProduct-in (T × C)) (Associativity.backward One T C) (uncurry (mapUncurry p)) ∙
        (represents p ▷ oneProduct-in (T × C))))

    specialize-β : (g : MAP T F) → =₁ (specializeMap forward g) (uncurry g)
    specialize-β g = uncurry-cong (decode-name g) ∙ decode-forward (nameMap g)
```



