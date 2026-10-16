# Arrows in a coproduct

Recognition and the interval-core equivalence make the two-point category an
anima, hence a groupoid. Its identity arrows therefore cover its arrow category.
Applying Fun([1],-) to the two coproduct universality squares and pulling back
this cover shows that every arrow in C ⊔ D belongs to one of its summands
(`cor:1_Simplex_Is_Connected`).

The comparison is the actual copair of postcomposition by the two inclusions.
Its compatibility with identity arrows then proves closure of groupoids, and
by recognition animae, under binary coproducts. Initiality was treated in
Recognition; no primitive coproduct closure of animae is assumed.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section05.ArrowCoproducts where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-compose; equiv-transport; equiv-cancel-right)
open import SCT.VolumeI.Chapter01.Section04.Core using (core-isAn)
open import SCT.VolumeI.Chapter01.Section05.Coproducts using (_⊔_; in₁; in₂)
open import SCT.VolumeI.Chapter01.Section05.Copairing
  using (copair; copair-η; copair-cong; copair-post; copair-pre₁; copair-pre₂)
open import SCT.VolumeI.Chapter01.Section05.CoproductConstructions
  using (coproductMap; coproductMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts
  using (coproductSquare₁; coproductSquare₂; inclusion₁-isPullback; inclusion₂-isPullback)
open import SCT.VolumeI.Chapter01.Section06.CoproductCover using (pullback-cover-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost)
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks
  using (mappedCone; fun-preserves-pullback)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism
  using ([1]; intervalCore; intervalCore-isEquiv)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; identityArrow)
open import SCT.VolumeI.Chapter02.Section04.Groupoids using (IsGroupoid)
open import SCT.VolumeI.Chapter02.Section04.BasicClosure
  using (constant-natural; terminal-isGroupoid)
open import SCT.VolumeI.Chapter02.Section05.Recognition
  using (anima-isGroupoid; groupoid-isAn; equivalence-reflects-anima)

module _ {Γ : Context} where
  two-point-isAn : isAn (One {Γ = Γ} ⊔ One)
  two-point-isAn = equivalence-reflects-anima intervalCore intervalCore-isEquiv (core-isAn [1])

  arrowCopair : (C D : CAT Γ) → MAP (Ar C ⊔ Ar D) (Ar (C ⊔ D))
  arrowCopair C D = copair (funPost {C = [1]} in₁) (funPost {C = [1]} in₂)

  identity-copair : (C D : CAT Γ)
    → (arrowCopair C D ∘ coproductMap (identityArrow {C = C}) (identityArrow {C = D}))
      =₁ identityArrow {C = C ⊔ D}
  identity-copair C D = copair-η identityArrow ∙
    (copair-cong
      (constant-natural [1] in₁ ∙ copair-pre₁ (funPost in₁) (funPost in₂) identityArrow)
      (constant-natural [1] in₂ ∙ copair-pre₂ (funPost in₁) (funPost in₂) identityArrow) ∙
        copair-post (in₁ ∘ identityArrow) (in₂ ∘ identityArrow) (arrowCopair C D))

  private
    two-point-cover : IsEquiv (arrowCopair (One {Γ = Γ}) One)
    two-point-cover = equiv-cancel-right (coproductMap identityArrow identityArrow) (arrowCopair One One)
      (coproductMap-isEquiv identityArrow identityArrow terminal-isGroupoid terminal-isGroupoid)
      (equiv-transport ((identity-copair One One) ⁻¹) (anima-isGroupoid two-point-isAn))

  arrowCopair-isEquiv : (C D : CAT Γ) → IsEquiv (arrowCopair C D)
  arrowCopair-isEquiv C D = pullback-cover-isEquiv
    (funPost {C = [1]} in₁) (funPost {C = [1]} in₂)
    (funPost {C = [1]} (coproductMap (terminate C) (terminate D)))
    (mappedCone [1] (coproductSquare₁ (terminate C) (terminate D)))
    (mappedCone [1] (coproductSquare₂ (terminate C) (terminate D)))
    (fun-preserves-pullback [1] _ (inclusion₁-isPullback (terminate C) (terminate D)))
    (fun-preserves-pullback [1] _ (inclusion₂-isPullback (terminate C) (terminate D)))
    two-point-cover

  coproduct-isGroupoid : (C D : CAT Γ)
    → IsGroupoid C → IsGroupoid D → IsGroupoid (C ⊔ D)
  coproduct-isGroupoid C D eC eD = equiv-transport (identity-copair C D)
    (equiv-compose (coproductMap identityArrow identityArrow) (arrowCopair C D)
      (coproductMap-isEquiv identityArrow identityArrow eC eD) (arrowCopair-isEquiv C D))

  coproduct-isAn : (C D : CAT Γ) → isAn C → isAn D → isAn (C ⊔ D)
  coproduct-isAn C D cAn dAn = groupoid-isAn
    (coproduct-isGroupoid C D (anima-isGroupoid cAn) (anima-isGroupoid dAn))
```
