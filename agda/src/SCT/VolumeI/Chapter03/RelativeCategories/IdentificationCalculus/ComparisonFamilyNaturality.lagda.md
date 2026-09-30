# Restricting encoded families of relative identifications

An encoded family retains both an identification and its triangle. Its
value respects comparisons of parameters and restriction of the parameter
category. Both statements follow by decoding the entire cone comparison.
Here restriction changes the parameter of the identification family;
it does not yet assert compatibility with prewhiskering its relative
functors or with the base-change compositor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonFamilyNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ComparisonEncoding 𝒯 M ℱ P using (module Encoding)

module Families {C D S : CAT} {f : MAP C S} {g : MAP D S}
  (u v : FunctorOver f g) where
  module Encoded = Encoding u v

  value : {A : CAT} → Cone Encoded.leftMap Encoded.rightMap A →
    Obj-abs A → FunctorOverIso u v
  value cone x = Encoded.decode (conePre x cone)

  opaque
    naturality : {A : CAT} (cone : Cone Encoded.leftMap Encoded.rightMap A)
      {x y : Obj-abs A} → x =₁ y → FunctorOverIso₂ (value cone x) (value cone y)
    naturality cone δ = Encoded.decode-comparison (cone-action cone δ)

    restriction : {A B : CAT} (r : MAP B A)
      (cone : Cone Encoded.leftMap Encoded.rightMap A) (x : Obj-abs B) →
      FunctorOverIso₂ (value (conePre r cone) x) (value cone (r ∘ x))
    restriction r cone x = Encoded.decode-comparison (conePre-assoc x r cone)

    comparison : {A : CAT} {cone other : Cone Encoded.leftMap Encoded.rightMap A} →
      ConeIso cone other → (x : Obj-abs A) → FunctorOverIso₂ (value cone x) (value other x)
    comparison Φ x = Encoded.decode-comparison (coneIso-pre x Φ)
```
