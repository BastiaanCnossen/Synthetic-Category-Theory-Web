# Arrows in a coproduct

The two-point category is a groupoid by the interval-core clause and
recognition. Consequently its arrow category is covered by the two
copies of `Ar One`. Applying `Fun [1]` to the coproduct universality
squares and using descent proves `cor:1_Simplex_Is_Connected`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section01.IntervalCore as Interval
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition

module SCT.VolumeI.Chapter02.Section05.ArrowCoproducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (A : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R)
  (B : Coproducts.CoproductStructure 𝒯 M)
  (K : Interval.IntervalCoreAxiom 𝒯 M B I)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open Recognition 𝒯 M ℱ P I E R
open Consequences A
open Coproducts.CoproductStructure B
open Universality 𝒯 M B P
open CoproductUniversality U
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.UniversalCoproductDescent 𝒯 M B P U
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P
open import SCT.VolumeI.Chapter02.Section04.ConstantFunctoriality 𝒯 M ℱ using (constant-natural)
open import SCT.VolumeI.Chapter02.Section05.TwoPointAnima 𝒯 M ℱ P I E R A B K

arrowCopair : (C D : CAT) → MAP (Ar C ⊔ Ar D) (Ar (C ⊔ D))
arrowCopair C D = copair (funPost in₁) (funPost in₂)

identity-copair : (C D : CAT) →
  (arrowCopair C D ∘ coproductMap (identityArrow {C}) (identityArrow {D})) =₁ identityArrow
identity-copair C D = copair-η identityArrow ∙
  (copair-cong
    (constant-natural [1] in₁ ∙ copair-pre₁ (funPost in₁) (funPost in₂) identityArrow)
    (constant-natural [1] in₂ ∙ copair-pre₂ (funPost in₁) (funPost in₂) identityArrow) ∙
      copair-post (in₁ ∘ identityArrow) (in₂ ∘ identityArrow) (arrowCopair C D))

two-point-cover : IsEquiv (arrowCopair One One)
two-point-cover = equiv-cancel-right (coproductMap identityArrow identityArrow) (arrowCopair One One)
  (coproductMap-isEquiv identityArrow identityArrow terminal-isGroupoid terminal-isGroupoid)
  (equiv-transport ((identity-copair One One) ⁻¹) two-point-isGroupoid)

arrowCopair-isEquiv : (C D : CAT) → IsEquiv (arrowCopair C D)
arrowCopair-isEquiv C D = Cover.copair-isEquiv
  (funPost in₁) (funPost in₂) (funPost (coproductMap (terminate C) (terminate D)))
  (mappedCone [1] (coproductSquare₁ (terminate C) (terminate D)))
  (mappedCone [1] (coproductSquare₂ (terminate C) (terminate D)))
  (fun-preserves-pullback [1] _ (inclusion₁-isPullback (terminate C) (terminate D)))
  (fun-preserves-pullback [1] _ (inclusion₂-isPullback (terminate C) (terminate D)))
  two-point-cover

coproduct-isGroupoid : (C D : CAT) → IsGroupoid C → IsGroupoid D → IsGroupoid (C ⊔ D)
coproduct-isGroupoid C D eC eD = equiv-transport (identity-copair C D)
  (equiv-compose (coproductMap identityArrow identityArrow) (arrowCopair C D)
    (coproductMap-isEquiv identityArrow identityArrow eC eD) (arrowCopair-isEquiv C D))

coproduct-isAn : (C D : CAT) → isAn C → isAn D → isAn (C ⊔ D)
coproduct-isAn C D cAn dAn = groupoid-isAn
  (coproduct-isGroupoid C D (anima-isGroupoid cAn) (anima-isGroupoid dAn))
```

The last two declarations prove `cor:Groupoids_Closed_Under_Disjoint_Unions`
and the coproduct clause of `cor:Initial_And_Coproduct_Animae`.
