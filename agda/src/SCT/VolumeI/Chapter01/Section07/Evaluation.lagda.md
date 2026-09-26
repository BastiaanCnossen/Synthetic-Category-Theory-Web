# The evaluation-induced uncurrying functor

For an arbitrary evaluation `e : F × C → D`, the book constructs an
actual functor `Map T F → Map (T × C) D`. Only its parameter, a mapping
anima, is used for mapping-anima currying. No condition on `T` or `F`
is imposed here. This is the construction preceding `def:Functor_Category`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter01.Section07.Evaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (module Reassociation; productMap-pair)
open import SCT.VolumeI.Chapter01.Section04.Substitution.Specialization 𝒯 M

module Evaluation {F C D : CAT} (e : MAP (F × C) D) where
  uncurry : {T : CAT} → MAP T F → MAP (T × C) D
  uncurry {T} g = e ∘ productMap g (id C)

  uncurry-cong : {T : CAT} {g h : MAP T F} → g =₁ h → (uncurry g) =₁ (uncurry h)
  uncurry-cong α = e ◁ productMap-cong α (idIso (id C))

  uncurry-restrict : {S T : CAT} (g : MAP T F) (r : MAP S T) →
    (uncurry (g ∘ r)) =₁ (uncurry g ∘ productMap r (id C))
  uncurry-restrict g r = (comp-assoc (productMap r (id C)) (productMap g (id C)) e) ⁻¹ ∙
    (e ◁ (productMap-cong (idIso (g ∘ r)) (comp-unitˡ (id C)) ∙
      productMap-comp r g (id C) (id C)) ⁻¹)

  uncurry-id : (uncurry (id F)) =₁ e
  uncurry-id = comp-unitʳ e ∙ (e ◁ productMap-id F C)

  module At (T : CAT) where
    parameter = Map T F
    evaluation : MAP (parameter × (T × C)) D
    evaluation = uncurry mapEval ∘ Associativity.backward parameter T C

    forward : MAP parameter (Map (T × C) D)
    forward = mapCurry (map-isAn T F) evaluation

    represents : {X : CAT} (g : MAP X parameter) →
      (mapUncurry (forward ∘ g)) =₁
        (uncurry (mapUncurry g) ∘ Associativity.backward X T C)
    represents {X} g =
      ((uncurry-restrict mapEval (productMap g (id T))) ⁻¹ ▷ Associativity.backward X T C) ∙
      ((comp-assoc (Associativity.backward X T C)
        (productMap (productMap g (id T)) (id C)) (uncurry mapEval)) ⁻¹ ∙
      (((uncurry mapEval) ◁ Reassociation.backward-natural g) ∙
      (comp-assoc (productMap g (id (T × C))) (Associativity.backward parameter T C) (uncurry mapEval) ∙
      ((mapCurry-β (map-isAn T F) evaluation ▷ productMap g (id (T × C))) ∙
        mapUncurry-restrict forward g))))

    terminal-regroup :
      (Associativity.backward One T C ∘ oneProduct-in (T × C)) =₁
      (productMap (oneProduct-in T) (id C))
    terminal-regroup = pair-cong
      ((pair-pre (terminate T) (id T) pr₁) ⁻¹ ∙
        pair-cong (terminal-iso _ _)
          ((comp-unitˡ pr₁) ⁻¹ ∙ comp-unitʳ pr₁ ∙
            ((pr₁ ◁ oneProduct-retraction (T × C)) ∙ comp-assoc (oneProduct-in (T × C)) (pr₂ {One} {T × C}) (pr₁ {T} {C}))) ∙
        pair-pre pr₁ (pr₁ ∘ pr₂) (oneProduct-in (T × C)))
      ((comp-unitˡ pr₂) ⁻¹ ∙ comp-unitʳ pr₂ ∙
        ((pr₂ ◁ oneProduct-retraction (T × C)) ∙ comp-assoc (oneProduct-in (T × C)) (pr₂ {One} {T × C}) (pr₂ {T} {C}))) ∙
      pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) (oneProduct-in (T × C))

    decode-forward : (p : Obj-abs parameter) →
      (decodeMap (forward ∘ p)) =₁ (uncurry (decodeMap p))
    decode-forward p = (uncurry-restrict (mapUncurry p) (oneProduct-in T)) ⁻¹ ∙
      (((uncurry (mapUncurry p)) ◁ terminal-regroup) ∙
      (comp-assoc (oneProduct-in (T × C)) (Associativity.backward One T C) (uncurry (mapUncurry p)) ∙
        (represents p ▷ oneProduct-in (T × C))))

    specialize-β : (g : MAP T F) → (specializeMap forward g) =₁ (uncurry g)
    specialize-β g = uncurry-cong (decode-name g) ∙ decode-forward (nameMap g)
```



