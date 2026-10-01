# Endpoint adjustment and commuting squares

Conjugation changes the endpoints of an identification family. The square-solving formulas pass between the conjugated equation and its commuting-square form, retaining their selected identification chains.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares {l : Level} (T : Theory l l l) where
open View T
open Calculus T
open Boundaries (identity T) using (conjugate)

evaluate : {X C D : CAT} {f f' g g' : MAP C D}
  (p : f =₁ f') (q : g =₁ g') (alpha : MAP X (f ＝ g))
  → (conjugate p q ∘ alpha) =₁ (const q ∙ (alpha ∙ const (p ⁻¹)))
evaluate {f = f} {g = g} p q alpha =
  isoComp-evaluate (const q) (id (f ＝ g) ∙ const (p ⁻¹)) alpha
    (const-pre q alpha)
    (isoComp-evaluate (id (f ＝ g)) (const (p ⁻¹)) alpha
      (comp-unitˡ alpha) (const-pre (p ⁻¹) alpha))

solve : {X C D : CAT} {f f' g g' : MAP C D}
  (p : f =₁ f') (q : g =₁ g') (alpha : MAP X (f ＝ g)) (beta : MAP X (f' ＝ g'))
  → (const q ∙ alpha) =₁ (beta ∙ const p)
  → (conjugate p q ∘ alpha) =₁ beta
solve p q alpha beta square = evaluate p q alpha then
  (assoc (const q) alpha (const (p ⁻¹))) ⁻¹ then
  isoComp-cong square (idIso _) then right-cancel p beta

unsolve : {X C D : CAT} {f f' g g' : MAP C D}
  (p : f =₁ f') (q : g =₁ g') (alpha : MAP X (f ＝ g)) (beta : MAP X (f' ＝ g'))
  → (conjugate p q ∘ alpha) =₁ beta
  → (const q ∙ alpha) =₁ (beta ∙ const p)
unsolve p q alpha beta solved =
  (right-cancelʳ p (const q ∙ alpha)) ⁻¹ then
  isoComp-cong (assoc (const q) alpha (const (p ⁻¹)) then
    (evaluate p q alpha) ⁻¹ then solved) (idIso _)

paste : {X C D : CAT} {f₀ f₁ f₂ g₀ g₁ g₂ : MAP C D}
  (p : f₀ =₁ f₁) (p' : f₁ =₁ f₂) (q : g₀ =₁ g₁) (q' : g₁ =₁ g₂)
  (alpha : MAP X (f₀ ＝ g₀)) (beta : MAP X (f₁ ＝ g₁)) (gamma : MAP X (f₂ ＝ g₂))
  → (const q ∙ alpha) =₁ (beta ∙ const p)
  → (const q' ∙ beta) =₁ (gamma ∙ const p')
  → (const (q' ∙ q) ∙ alpha) =₁ (gamma ∙ const (p' ∙ p))
paste p p' q q' alpha beta gamma first second =
  isoComp-cong ((const-comp q' q) ⁻¹) (idIso _) then
  assoc (const q') (const q) alpha then
  isoComp-cong (idIso _) first then
  (assoc (const q') beta (const p)) ⁻¹ then
  isoComp-cong second (idIso _) then
  assoc gamma (const p') (const p) then
  isoComp-cong (idIso _) (const-comp p' p)

change : {X C D : CAT} {f f' g g' : MAP C D}
  (p : f =₁ f') (q : g =₁ g')
  {alpha alpha' : MAP X (f ＝ g)} {beta beta' : MAP X (f' ＝ g')}
  → (const q ∙ alpha) =₁ (beta ∙ const p)
  → alpha =₁ alpha' → beta =₁ beta'
  → (const q ∙ alpha') =₁ (beta' ∙ const p)
change p q square a b = isoComp-cong (idIso _) (a ⁻¹) then square then
  isoComp-cong b (idIso _)

precompose : {Y X C D : CAT} {f f' g g' : MAP C D}
  (p : f =₁ f') (q : g =₁ g')
  (alpha : MAP X (f ＝ g)) (beta : MAP X (f' ＝ g'))
  → (const q ∙ alpha) =₁ (beta ∙ const p) → (r : MAP Y X)
  → (const q ∙ (alpha ∘ r)) =₁ ((beta ∘ r) ∙ const p)
precompose p q alpha beta square r =
  (isoComp-evaluate (const q) alpha r (const-pre q r) (idIso _)) ⁻¹ then
  (square ▷ r) then
  isoComp-evaluate beta (const p) r (idIso _) (const-pre p r)

at : {X C D : CAT} {f f' g g' : MAP C D}
  (p : f =₁ f') (q : g =₁ g')
  (alpha : MAP X (f ＝ g)) (beta : MAP X (f' ＝ g'))
  → (const q ∙ alpha) =₁ (beta ∙ const p) → (r : MAP One X)
  → (q ∙ (alpha ∘ r)) =₂ ((beta ∘ r) ∙ p)
at p q alpha beta square r =
  isoComp-cong ((const-One q) ⁻¹) (idIso _) then
  precompose p q alpha beta square r then
  isoComp-cong (idIso _) (const-One p)

term-solve : {C D : CAT} {f f' g g' : MAP C D}
  (p : f =₁ f') (q : g =₁ g') (alpha : f =₁ g) (beta : f' =₁ g')
  → (q ∙ alpha) =₂ (beta ∙ p)
  → (conjugate p q ∘ alpha) =₂ beta
term-solve p q alpha beta square = solve p q alpha beta
  (isoComp-cong (const-One q) (idIso _) then square then
    isoComp-cong (idIso _) ((const-One p) ⁻¹))

term-change : {C D : CAT} {f f' g g' : MAP C D}
  {p p' : f =₁ f'} {q q' : g =₁ g'} {alpha alpha' : f =₁ g} {beta beta' : f' =₁ g'}
  → (q ∙ alpha) =₂ (beta ∙ p)
  → p =₂ p' → q =₂ q' → alpha =₂ alpha' → beta =₂ beta'
  → (q' ∙ alpha') =₂ (beta' ∙ p')
term-change square p q a b = (isoComp-cong q a) ⁻¹ then square then isoComp-cong b p
```
