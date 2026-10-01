# Whiskering commuting squares

The square calculations retain constant endpoint identifications while applying precomposition or postcomposition. They are used when normalizing horizontal composites.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ParameterizedWhiskering as P

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.HorizontalSquares {l : Level} (T : Theory l l l) where
open View T
open Calculus T

opaque
  post-const : {X C D E : CAT} {f g : MAP C D} (u : MAP D E) (p : f =₁ g)
    → (u ◁ const {P = X} p) =₁ const (u ◁ p)
  post-const {X} u p = (comp-assoc (terminate X) p (postWhisker u)) ⁻¹

  pre-const : {X B C D : CAT} {f g : MAP C D} (p : f =₁ g) (k : MAP B C)
    → (const {P = X} p ▷ k) =₁ const (p ▷ k)
  pre-const {X} p k = (comp-assoc (terminate X) p (preWhisker k)) ⁻¹

  post : {X C D E : CAT} {f f' g g' : MAP C D} (u : MAP D E)
    (p : f =₁ f') (q : g =₁ g') (alpha : MAP X (f ＝ g)) (beta : MAP X (f' ＝ g'))
    → (const q ∙ alpha) =₁ (beta ∙ const p)
    → (const (u ◁ q) ∙ (u ◁ alpha)) =₁ ((u ◁ beta) ∙ const (u ◁ p))
  post u p q alpha beta square =
    isoComp-cong ((post-const u q) ⁻¹) (idIso _) then
    (P.post-comp T u (const q) alpha) ⁻¹ then (postWhisker u ◁ square) then
    P.post-comp T u beta (const p) then isoComp-cong (idIso _) (post-const u p)

  pre : {X B C D : CAT} {f f' g g' : MAP C D} (k : MAP B C)
    (p : f =₁ f') (q : g =₁ g') (alpha : MAP X (f ＝ g)) (beta : MAP X (f' ＝ g'))
    → (const q ∙ alpha) =₁ (beta ∙ const p)
    → (const (q ▷ k) ∙ (alpha ▷ k)) =₁ ((beta ▷ k) ∙ const (p ▷ k))
  pre k p q alpha beta square =
    isoComp-cong ((pre-const q k) ⁻¹) (idIso _) then
    (P.pre-comp T (const q) alpha k) ⁻¹ then (preWhisker k ◁ square) then
    P.pre-comp T beta (const p) k then isoComp-cong (idIso _) (pre-const p k)

  four-middle : {X C D : CAT} {f₀ f₁ f₂ f₃ f₄ z : MAP C D}
    (a : MAP X (f₃ ＝ f₄)) (b : MAP X (f₂ ＝ f₃))
    (c : MAP X (f₁ ＝ f₂)) (d : MAP X (f₀ ＝ f₁))
    (e : MAP X (z ＝ f₃)) (v : MAP X (f₁ ＝ z))
    → (b ∙ c) =₁ (e ∙ v) → ((a ∙ b) ∙ (c ∙ d)) =₁ ((a ∙ e) ∙ (v ∙ d))
  four-middle a b c d e v square = assoc a b (c ∙ d) then
    isoComp-cong (idIso a) ((assoc b c d) ⁻¹ then isoComp-cong square (idIso d) then assoc e v d) then
    (assoc a e (v ∙ d)) ⁻¹

  horizontal-square : {X B C D : CAT}
    {f f' F F' : MAP B C} {g g' G G' : MAP C D}
    (u : f =₁ F) (v : f' =₁ F') (p : g =₁ G) (q : g' =₁ G')
    (alpha : MAP X (f ＝ f')) (alpha' : MAP X (F ＝ F'))
    (beta : MAP X (g ＝ g')) (beta' : MAP X (G ＝ G'))
    → (const v ∙ alpha) =₁ (alpha' ∙ const u)
    → (const q ∙ beta) =₁ (beta' ∙ const p)
    → (const (q ⋆ v) ∙ (beta ⋆ alpha)) =₁ ((beta' ⋆ alpha') ∙ const (p ⋆ u))
  horizontal-square {F' = F'} {g} {g'} {G} u v p q alpha alpha' beta beta' first second =
    isoComp-cong ((const-comp (q ▷ F') (g' ◁ v)) ⁻¹) (idIso _) then
    four-middle (const (q ▷ F')) (const (g' ◁ v)) (beta ▷ _) (g ◁ alpha)
      (beta ▷ F') (const (g ◁ v)) ((P.fixed-inner T beta v) ⁻¹) then
    isoComp-cong (pre F' p q beta beta' second) (post g u v alpha alpha' first) then
    four-middle (beta' ▷ F') (const (p ▷ F')) (g ◁ alpha') (const (g ◁ u))
      (G ◁ alpha') (const (p ▷ _)) (P.fixed-outer T p alpha') then
    isoComp-cong (idIso _) (const-comp (p ▷ _) (g ◁ u))
```
