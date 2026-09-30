# Reversing a map of cospans

Swapping both cospans exchanges the two specified squares. The comparison
below retains the complete matching of the mapped cone, including its
whiskered source matching. This supports the symmetric form of pullback
transport.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanSymmetry
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)

swap-cospan : {C D E C′ D′ E′ : CAT} {f : MAP C E} {g : MAP D E}
  {f′ : MAP C′ E′} {g′ : MAP D′ E′} → CospanMap f g f′ g′ → CospanMap g f g′ f′
swap-cospan F = record
  { left = CospanMap.right F ; right = CospanMap.left F ; base = CospanMap.base F
  ; leftSquare = CospanMap.rightSquare F ; rightSquare = CospanMap.leftSquare F }

private
  inverse-triple : {A B : CAT} {a₀ a₁ a₂ a₃ : MAP A B}
    (γ : a₂ =₁ a₃) (β : a₁ =₁ a₂) (α : a₀ =₁ a₁) →
    ((γ ∙ (β ∙ α)) ⁻¹) =₂ (α ⁻¹ ∙ (β ⁻¹ ∙ γ ⁻¹))
  inverse-triple γ β α = isoComp-assoc-at (α ⁻¹) (β ⁻¹) (γ ⁻¹) ∙
    (isoComp-cong (inverse-composite β α) (idIso (γ ⁻¹)) ∙
      inverse-composite γ (β ∙ α))

  group-prefix : {A B : CAT} {a₀ a₁ a₂ a₃ a₄ : MAP A B}
    (δ : a₃ =₁ a₄) (γ : a₂ =₁ a₃) (β : a₁ =₁ a₂) (α : a₀ =₁ a₁) →
    (δ ∙ (γ ∙ (β ∙ α))) =₂ ((δ ∙ (γ ∙ β)) ∙ α)
  group-prefix δ γ β α = (isoComp-assoc-at δ (γ ∙ β) α) ⁻¹ ∙
    isoComp-cong (idIso δ) ((isoComp-assoc-at γ β α) ⁻¹)

module At {C D E C′ D′ E′ X : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (s : Cone f g X) where
  private
    u = CospanMap.left F
    v = CospanMap.right F
    w = CospanMap.base F
    α = CospanMap.leftSquare F
    β = CospanMap.rightSquare F
    p = Cone.left s
    q = Cone.right s
    τ = Cone.match s
    A = comp-assoc q v g′
    B = β ⁻¹ ▷ q
    C₀ = (comp-assoc q g w) ⁻¹
    D₀ = w ◁ τ
    E₀ = comp-assoc p f w
    F₀ = α ▷ p
    G = (comp-assoc p u f′) ⁻¹
    L = E₀ ∙ (F₀ ∙ G)
    R = A ∙ (B ∙ C₀)
    L′ = comp-assoc p u f′ ∙ ((α ⁻¹ ▷ p) ∙ (comp-assoc p f w) ⁻¹)
    R′ = comp-assoc q g w ∙ ((β ▷ q) ∙ (comp-assoc q v g′) ⁻¹)

    abstract
      left-inverse : (L ⁻¹) =₂ L′
      left-inverse = isoComp-cong (inverse-inverse (comp-assoc p u f′))
        (isoComp-cong ((pre-inverse α p) ⁻¹) (idIso (E₀ ⁻¹))) ∙
        inverse-triple E₀ F₀ G

      right-inverse : (R ⁻¹) =₂ R′
      right-inverse = isoComp-cong (inverse-inverse (comp-assoc q g w))
        (isoComp-cong ((preWhisker q ◁ inverse-inverse β) ∙ (pre-inverse (β ⁻¹) q) ⁻¹)
          (idIso (A ⁻¹))) ∙ inverse-triple A B C₀

      matching : ((Cone.match (CospanMap.mapCone F s)) ⁻¹) =₂
        Cone.match (CospanMap.mapCone (swap-cospan F) (coneSwap s))
      matching = (group-prefix (comp-assoc p u f′) (α ⁻¹ ▷ p)
          ((comp-assoc p f w) ⁻¹) ((w ◁ τ ⁻¹) ∙ R′)) ⁻¹ ∙
        (isoComp-cong left-inverse
          (isoComp-cong ((post-inverse w τ) ⁻¹) right-inverse) ∙
        (inverse-triple R D₀ L ∙
          (＝-inv ◁ group-prefix A B C₀ (D₀ ∙ L))))

  comparison : ConeIso (coneSwap (CospanMap.mapCone F s))
    (CospanMap.mapCone (swap-cospan F) (coneSwap s))
  comparison = cone-match-change _ _ _ _ matching
```
