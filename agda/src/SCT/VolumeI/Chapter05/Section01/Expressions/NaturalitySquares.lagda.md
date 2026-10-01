# Naturality squares for transport

The square calculations compare the action of identification functors with boundary transport. They provide the naturality input to normalization of higher witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.Expressions.TermCalculus as Calculus

module SCT.VolumeI.Chapter05.Section01.Expressions.NaturalitySquares {l : Level} (T : Theory l l l) where
open View T
module L = Calculus.Local T
open L public using (paste; inverse-square)
open L hiding (paste; inverse-square)

opaque
  pre : {B C D : CAT} {f f' g g' : MAP C D}
    (u : f =₁ f') (v : g =₁ g') (a : f =₁ g) (b : f' =₁ g')
    → (v ∙ a) =₂ (b ∙ u) → (k : MAP B C)
    → ((v ▷ k) ∙ (a ▷ k)) =₂ ((b ▷ k) ∙ (u ▷ k))
  pre u v a b square k = (preWhisker-isoComp-at v a k) ⁻¹ then
    (preWhisker k ◁ square) then preWhisker-isoComp-at b u k

  post : {C D E : CAT} {f f' g g' : MAP C D}
    (u : f =₁ f') (v : g =₁ g') (a : f =₁ g) (b : f' =₁ g')
    → (v ∙ a) =₂ (b ∙ u) → (h : MAP D E)
    → ((h ◁ v) ∙ (h ◁ a)) =₂ ((h ◁ b) ∙ (h ◁ u))
  post u v a b square h = (postWhisker-isoComp-at h v a) ⁻¹ then
    (postWhisker h ◁ square) then postWhisker-isoComp-at h b u

  inverse-boundary : {C D : CAT} {f f' g g' : MAP C D}
    (u : f =₁ f') (v : g =₁ g') (a : f =₁ g) (b : f' =₁ g')
    → (v ∙ a) =₂ (b ∙ u) → ((v ⁻¹) ∙ b) =₂ (a ∙ (u ⁻¹))
  inverse-boundary u v a b square = (inverse-square a b u v (square ⁻¹)) ⁻¹

  change-arrows : {C D : CAT} {f f' g g' : MAP C D}
    (u : f =₁ f') (v : g =₁ g') (a a' : f =₁ g) (b b' : f' =₁ g')
    → a' =₂ a → b =₂ b' → (v ∙ a) =₂ (b ∙ u)
    → (v ∙ a') =₂ (b' ∙ u)
  change-arrows u v a a' b b' first second square =
    isoComp-cong (idIso _) first then square then isoComp-cong second (idIso _)
```
