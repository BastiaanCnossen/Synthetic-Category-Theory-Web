# Beck–Chevalley on mapping animae

Take cores of the comparison of uncurrying functors. The composition
comparisons identify these cores with the stipulated base-change and
postcomposition maps. Since the other three sides are equivalences,
the pulled evaluation has the dependent-product universal property.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyMapping
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalleyUncurrying 𝒯 M ℱ P using (module Square)

module Stability {S T S′ T′ C D : CAT} (p : MAP S T) (b : MAP T′ T)
  (square : Cone p b S′) (square-isPullback : IsPullback square) (g : MAP D T) (f : MAP C S)
  (ε : FunctorOver (pullback₂ {f = g} {p}) f) where
  module Functors = Square p b square square-isPullback g f ε using (pulled; module At)
  h = Cone.left square
  p′ = Cone.right square
  t : MAP (Pullback g b) T′
  t = pullback₂
  f′ : MAP (Pullback f h) S′
  f′ = pullback₂
  pulled = Functors.pulled

  module At {K : CAT} (k : MAP K T′) where
    module F = Functors.At k using (left; right; comparison; restriction-maps-isEquiv; module A; module B; module Restrict; module NewBC; module NewPost; module OldBC; module OldPost)
    module A = F.A using (maps; functor; maps-isEquiv)
    module B = F.B using (maps; functor; maps-isEquiv)
    module R = F.Restrict using (maps; functor)
    module NewBC = F.NewBC using (maps; functor; maps-as-core)
    module NewPost = F.NewPost using (maps; functor; maps-as-core)
    module OldBC = F.OldBC using (maps; functor; maps-as-core)
    module OldPost = F.OldPost using (maps; functor; maps-as-core)
    new-uncurry = EvaluationAlong.uncurrying p′ f′ t pulled k
    old-uncurry = EvaluationAlong.uncurrying p f g ε (b ∘ k)
    left = B.maps ∘ new-uncurry
    right = R.maps ∘ (old-uncurry ∘ A.maps)
    old-functor = OldPost.functor ∘ OldBC.functor

    abstract
      new-core : new-uncurry =₁ mapPost (NewPost.functor ∘ NewBC.functor)
      new-core = mapPost-comp NewBC.functor NewPost.functor ∙
        ((mapPost NewPost.functor ◁ NewBC.maps-as-core) ∙ (NewPost.maps-as-core ▷ NewBC.maps))

      old-core : old-uncurry =₁ mapPost old-functor
      old-core = mapPost-comp OldBC.functor OldPost.functor ∙
        ((mapPost OldPost.functor ◁ OldBC.maps-as-core) ∙ (OldPost.maps-as-core ▷ OldBC.maps))

      left-core : left =₁ mapPost F.left
      left-core = mapPost-comp (NewPost.functor ∘ NewBC.functor) B.functor ∙ (mapPost B.functor ◁ new-core)

      right-core : right =₁ mapPost F.right
      right-core = mapPost-comp (OldPost.functor ∘ (OldBC.functor ∘ A.functor)) R.functor ∙
        (mapPost R.functor ◁
          (mapPost-cong (comp-assoc A.functor OldBC.functor OldPost.functor) ∙
            (mapPost-comp A.functor old-functor ∙ (old-core ▷ A.maps))))

      comparison : left =₁ right
      comparison = right-core ⁻¹ ∙ (mapPost-cong F.comparison ∙ left-core)

      isEquiv : IsDependentProduct p f g ε → IsEquiv new-uncurry
      isEquiv universal = equiv-cancel-left new-uncurry B.maps B.maps-isEquiv
        (equiv-transport (comparison ⁻¹)
          (equiv-compose (old-uncurry ∘ A.maps) R.maps
            (equiv-compose A.maps old-uncurry A.maps-isEquiv (IsDependentProduct.universal universal (b ∘ k)))
            (F.restriction-maps-isEquiv)))

  abstract
    universal : IsDependentProduct p f g ε → IsDependentProduct p′ f′ t pulled
    universal old = record { universal = λ k → At.isEquiv k old }
```
