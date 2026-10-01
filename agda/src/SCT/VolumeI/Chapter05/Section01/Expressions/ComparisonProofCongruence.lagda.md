# Congruence of the selected comparison formulas

The formulas compare the chosen square-solving and conjugation proofs at the next dimension. They use synthetic identifications, without proof irrelevance or host-language equality of witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares

module SCT.VolumeI.Chapter05.Section01.Expressions.ComparisonProofCongruence {l : Level} (T : Theory l l l) where
open View T
open Calculus T
open Squares T using (solve; unsolve; term-solve; evaluate)

opaque
  pair-iso-cong : {X C D : CAT} {f g : MAP X (C × D)}
    {a a' : (pr₁ ∘ f) =₁ (pr₁ ∘ g)} {b b' : (pr₂ ∘ f) =₁ (pr₂ ∘ g)}
    → a =₂ a' → b =₂ b' → pair-iso a b =₂ pair-iso a' b'
  pair-iso-cong {f = f} {g} p q = IsEquiv.inverse (product-isoMap-isEquiv f g) ◁ pair-cong p q

  pair-cong-cong : {X C D : CAT} {a a' : MAP X C} {b b' : MAP X D}
    {p p' : a =₁ a'} {q q' : b =₁ b'}
    → p =₂ p' → q =₂ q' → pair-cong p q =₂ pair-cong p' q'
  pair-cong-cong {a = a} {a'} {b} {b'} u v = pair-iso-cong {f = pair a b} {g = pair a' b'}
    (isoComp-cong (idIso _) (isoComp-cong u (idIso _)))
    (isoComp-cong (idIso _) (isoComp-cong v (idIso _)))

  isoComp-cong-cong : {X C D : CAT} {f g h : MAP C D}
    {b b' : MAP X (g ＝ h)} {a a' : MAP X (f ＝ g)}
    {p p' : b =₁ b'} {q q' : a =₁ a'}
    → p =₂ p' → q =₂ q' → isoComp-cong p q =₂ isoComp-cong p' q'
  isoComp-cong-cong {b = b} {b'} {a} {a'} u v = postWhisker isoComp ◁
    pair-cong-cong {a = b} {a' = b'} {b = a} {b' = a'} u v

  chain-cong : {C D : CAT} {f₀ f₁ f₂ f₃ : MAP C D}
    (a : f₀ =₁ f₁) (b b' : f₁ =₁ f₂) (c : f₂ =₁ f₃)
    → b =₂ b' → (c ∙ (b ∙ a)) =₂ (c ∙ (b' ∙ a))
  chain-cong a b b' c r = isoComp-cong (idIso c) (isoComp-cong r (idIso a))

  right-compose-cong : {C D : CAT} {f₀ f₁ f₂ : MAP C D}
    (a : f₀ =₁ f₁) (b b' : f₁ =₁ f₂)
    → b =₂ b' → (b ∙ a) =₂ (b' ∙ a)
  right-compose-cong a b b' r = isoComp-cong r (idIso a)

  solve-cong : {X C D : CAT} {f f' g g' : MAP C D}
    (p : f =₁ f') (q : g =₁ g') (a : MAP X (f ＝ g)) (b : MAP X (f' ＝ g'))
    {s t : (const q ∙ a) =₁ (b ∙ const p)}
    → s =₂ t → solve p q a b s =₂ solve p q a b t
  solve-cong {X} {C} {D} {f} {f'} {g} {g'} p q a b {s} {t} r =
    chain-cong (evaluate p q a then (assoc (const q) a (const (p ⁻¹))) ⁻¹)
      (isoComp-cong s (idIso (const (p ⁻¹)))) (isoComp-cong t (idIso (const (p ⁻¹))))
      (right-cancel p b) middle
    where
    middle : isoComp-cong s (idIso (const {P = X} (p ⁻¹))) =₂
      isoComp-cong t (idIso (const {P = X} (p ⁻¹)))
    middle = isoComp-cong-cong {X = X} {C = C} {D = D} {f = f'} {g = f} {h = g'}
      {b = const q ∙ a} {b' = b ∙ const p} {a = const (p ⁻¹)} {a' = const (p ⁻¹)}
      {p = s} {p' = t} {q = idIso _} {q' = idIso _} r (idIso _)

  term-solve-cong : {C D : CAT} {f f' g g' : MAP C D}
    (p : f =₁ f') (q : g =₁ g') (a : f =₁ g) (b : f' =₁ g')
    {s t : (q ∙ a) =₂ (b ∙ p)}
    → s =₃ t → term-solve p q a b s =₃ term-solve p q a b t
  term-solve-cong {C} {D} {f} {f'} {g} {g'} p q a b {s} {t} r =
    solve-cong {X = One} {C = C} {D = D} {f = f} {f' = f'} {g = g} {g' = g'} p q a b
    (chain-cong (isoComp-cong (const-One q) (idIso a)) s t
      (isoComp-cong (idIso b) ((const-One p) ⁻¹)) r)

-- These compare the ACTUAL chosen proof recipes at the next dimension. They
-- do not use host equality, proof irrelevance, or an unproved assertion that
-- solve and unsolve are mutually inverse on their selected witnesses.
```
