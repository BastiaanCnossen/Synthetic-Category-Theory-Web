# Sections represented by local functors

A local functor gives an absolute object of the dependent product of its
mapping anima. Postcomposition has the expected computation on these
objects. The dependent product of `Map B 1` is terminal.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
import SCT.VolumeI.Chapter05.Section01.Coherence as Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductIdentifications as Identifications

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.ProductNames
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (M : Mapping.MappingAnimae T) (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
module P = Products.DependentProducts P
module A = Action W P using (Π-map; Π-map-β; reflect; uncurry-pre)
module M = Setup T M
  using (Map; map-isAn; mapPost; mapPost-name; mapReflect; nameMap)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

name : {B C : T.CAT} → T.MAP B C → S.MAP S.One (P.Π (M.Map B C))
name f = P.curry (M.nameMap f ∘ T.terminate (W.cat S.One))

post-image : {B C D : T.CAT} (f : T.MAP C D) (g : T.MAP B C)
  → T._=₁_ (P.uncurry (S._∘_ (A.Π-map (M.mapPost f)) (name g))) (P.uncurry (name (f ∘ g)))
post-image f g = A.uncurry-pre (A.Π-map (M.mapPost f)) (name g) then
    ((A.Π-map-β (M.mapPost f)) ⁻¹ ▷ W.map (name g)) then
    T.comp-assoc (W.map (name g)) (P.evaluation _) (M.mapPost f) then
    (M.mapPost f ◁ (P.curry-β (M.nameMap g ∘ T.terminate (W.cat S.One))) ⁻¹) then
    (T.comp-assoc (T.terminate (W.cat S.One)) (M.nameMap g) (M.mapPost f)) ⁻¹ then
    (M.mapPost-name f g ▷ T.terminate (W.cat S.One)) then
    P.curry-β (M.nameMap (f ∘ g) ∘ T.terminate (W.cat S.One))

post : {B C D : T.CAT} (f : T.MAP C D) (g : T.MAP B C)
  → S._=₁_ (S._∘_ (A.Π-map (M.mapPost f)) (name g)) (name (f ∘ g))
post f g = A.reflect (post-image f g)

module Computation (K : Coherence.OperationCompatibility W) where
  post-β : {B C D : T.CAT} (f : T.MAP C D) (g : T.MAP B C)
    → T._=₂_ (Identifications.action W K P (post f g)) (post-image f g)
  post-β f g = Identifications.reflect-β W K P (post-image f g)

terminal-isEquiv : (B : T.CAT) → S.IsEquiv (S.terminate (P.Π (M.Map B T.One)))
terminal-isEquiv B = record
  { inverse = name (T.terminate B)
  ; sectionIso = A.reflect (M.mapReflect (W.anima (P.Π-isAn (M.map-isAn B T.One))) _ _
      (T.terminal-iso _ _))
  ; retractionIso = S.terminal-iso _ _ }
```
