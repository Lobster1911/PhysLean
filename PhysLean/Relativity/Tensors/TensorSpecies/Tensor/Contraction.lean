/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.TensorSpecies.Tensor.Basic
/-!

# Contractions of tensors

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {S : TensorSpecies k}

namespace Tensor


/-!

## Pure.contrPCoeff


-/

namespace Pure

/-!

## dropPairEmb

-/

variable {n : ℕ} {c : Fin (n + 1 + 1) → S.C}

def dropPairEmb (i j : Fin (n + 1 + 1)) (hij : i ≠ j) : Fin n ↪o Fin (n + 1 + 1) :=
  (Finset.orderEmbOfFin {i, j}ᶜ
  (by rw [Finset.card_compl]; simp [Finset.card_pair hij]))


lemma dropPairEmb_apply_eq_orderIsoOfFin {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (m : Fin n) :
    (dropPairEmb i j hij) m = (Finset.orderIsoOfFin {i, j}ᶜ
      (by rw [Finset.card_compl]; simp [Finset.card_pair hij])) m := by
  simp [dropPairEmb]


lemma dropPairEmb_symm (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    dropPairEmb i j hij = dropPairEmb j i hij.symm := by
  simp only [dropPairEmb, Finset.pair_comm]

@[simp]
lemma permCond_dropPairEmb_symm (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    PermCond (c ∘ dropPairEmb i j hij) (c ∘ dropPairEmb j i hij.symm) id :=
  And.intro (Function.bijective_id) (by rw [dropPairEmb_symm]; simp)


@[simp]
lemma dropPairEmb_range {i j : Fin (n + 1 + 1)} (hij : i ≠ j) :
    Set.range (dropPairEmb i j hij) = {i, j}ᶜ := by
  rw [dropPairEmb, Finset.range_orderEmbOfFin]
  simp only [Finset.compl_insert, Finset.coe_erase, Finset.coe_compl, Finset.coe_singleton]
  ext x : 1
  simp only [Set.mem_diff, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff, not_or]
  apply Iff.intro
  · intro a
    simp_all only [not_false_eq_true, and_self]
  · intro a
    simp_all only [not_false_eq_true, and_self]

lemma dropPairEmb_image_compl {i j : Fin (n + 1 + 1)} (hij : i ≠ j)
      (X : Set (Fin n)) :
    (dropPairEmb i j hij) '' Xᶜ = ({i, j} ∪ dropPairEmb i j hij '' X)ᶜ := by
  rw [← compl_inj_iff, Function.Injective.compl_image_eq (dropPairEmb i j hij).injective]
  simp only [compl_compl, dropPairEmb_range,  Set.union_singleton]
  exact Set.union_comm (⇑(dropPairEmb i j hij) '' X) {i, j}

@[simp]
lemma fst_neq_dropPairEmb_pre (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin n) :
    ¬ i = (dropPairEmb i j hij) m  := by
  by_contra hn
  have hi : i ∉ Set.range (dropPairEmb i j hij) := by
    simp [dropPairEmb]
  nth_rewrite 2 [hn] at hi
  simp [- dropPairEmb_range] at hi

@[simp]
lemma snd_neq_dropPairEmb_pre (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin n) :
    ¬ j = (dropPairEmb i j hij) m  := by
  by_contra hn
  have hi : j ∉ Set.range (dropPairEmb i j hij) := by
    simp [dropPairEmb]
  nth_rewrite 2 [hn] at hi
  simp [- dropPairEmb_range] at hi

def dropPairEmbPre (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) : Fin n :=
    (Finset.orderIsoOfFin {i, j}ᶜ (by rw [Finset.card_compl]; simp [Finset.card_pair hij])).symm
    ⟨m, by simp [hm]⟩

@[simp]
lemma dropPairEmb_dropPairEmbPre (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) : dropPairEmb i j hij (dropPairEmbPre i j hij m hm) = m := by
  rw [dropPairEmb_apply_eq_orderIsoOfFin, dropPairEmbPre]
  simp

@[simp]
lemma dropPairEmbPre_injective (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m1 m2 : Fin (n + 1 + 1)) (hm1 : m1 ≠ i ∧ m1 ≠ j) (hm2 : m2 ≠ i ∧ m2 ≠ j) :
    dropPairEmbPre i j hij m1 hm1 = dropPairEmbPre i j hij m2 hm2  ↔ m1 = m2 := by
  rw [← Function.Injective.eq_iff (dropPairEmb i j hij).injective]
  simp

lemma dropPairEmb_comm (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) :
    let i2' := (dropPairEmb i1 j1 hij1 i2);
    let j2' := (dropPairEmb i1 j1 hij1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', dropPairEmb, hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    dropPairEmb i1 j1 hij1 ∘ dropPairEmb i2 j2 hij2 =
    dropPairEmb i2' j2' hi2j2' ∘
    dropPairEmb i1' j1' (by simp [i1', j1', hij1]) := by
  intro i2' j2' hi2j2'
  let fl : Fin n ↪o Fin (n + 1 + 1 + 1 + 1) :=
    ⟨⟨dropPairEmb i1 j1 hij1 ∘ dropPairEmb i2 j2 hij2, by
      refine (EmbeddingLike.comp_injective (⇑(dropPairEmb i2 j2 hij2)) (dropPairEmb i1 j1 hij1)).mpr ?_
      exact RelEmbedding.injective (dropPairEmb i2 j2 hij2)⟩, by simp⟩
  let fr : Fin n ↪o Fin (n + 1 + 1 + 1 + 1) :=
    ⟨⟨dropPairEmb i2' j2' hi2j2' ∘ dropPairEmb (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']))
      (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2'])) (by simp [hij1]),
      by
      refine (EmbeddingLike.comp_injective _ _).mpr ?_
      exact RelEmbedding.injective _⟩, by simp⟩
  have h : fl = fr := by
    rw [← OrderEmbedding.range_inj]
    simp [fl, fr, Set.range_comp]
    rw [dropPairEmb_image_compl, dropPairEmb_image_compl]
    congr 1
    rw [Set.image_pair, Set.image_pair]
    simp only [Set.union_singleton, dropPairEmb_dropPairEmbPre, i2', j2', fl, fr]
    exact Set.union_comm {i1, j1} {(dropPairEmb i1 j1 hij1) i2, (dropPairEmb i1 j1 hij1) j2}
  ext1 a
  simpa [fl, fr] using congrFun (congrArg (fun x => x.toFun) h) a

lemma dropPairEmb_comm_apply  (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) (m : Fin n) :
    let i2' := (dropPairEmb i1 j1 hij1 i2);
    let j2' := (dropPairEmb i1 j1 hij1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', dropPairEmb, hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    dropPairEmb i2' j2' hi2j2'
    (dropPairEmb i1' j1' (by simp [i1', j1', hij1])  m) =
    dropPairEmb i1 j1 hij1  (dropPairEmb i2 j2 hij2 m) := by
  intro i2' j2' hi2j2' i1' j1'
  change _ = (dropPairEmb i1 j1 hij1 ∘ dropPairEmb i2 j2 hij2) m
  rw [dropPairEmb_comm i1 j1 i2 j2 hij1 hij2]
  rfl


@[simp]
lemma permCond_dropPairEmb_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → S.C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) :
    let i2' := (dropPairEmb i1 j1 hij1 i2);
    let j2' := (dropPairEmb i1 j1 hij1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', dropPairEmb, hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    PermCond
      ((c ∘ dropPairEmb i2' j2' hi2j2') ∘ dropPairEmb i1' j1' (by simp [i1', j1', hij1]))
      ((c ∘ dropPairEmb i1 j1 hij1) ∘ dropPairEmb i2 j2 hij2)
      id := by
  apply And.intro (Function.bijective_id)
  simp
  intro i
  rw [dropPairEmb_comm_apply]


/-!

## dropPair

-/

def dropEm {n : ℕ} {c : Fin n → S.C} {m : ℕ} (f : Fin m ↪o Fin n) (p : Pure S c) : Pure S (c ∘ f) :=
  fun i => p (f i)

def dropPair (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c) :
    Pure S (c ∘ dropPairEmb i j hij) :=
  dropEm (dropPairEmb i j hij) p

@[simp]
lemma dropPair_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c) (g : S.G) :
    dropPair i j hij (g • p) = g • dropPair i j hij p := by
  ext m
  simp only [dropPair, dropEm, actionP_eq]
  rfl

lemma dropPair_symm (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (p : Pure S c) : dropPair i j hij p =
    permP id (by simp) (dropPair j i hij.symm p) := by
  ext m
  simp [dropPair, dropEm, permP]
  refine (congr_right _ _ _ ?_).symm
  rw [dropPairEmb_symm]

lemma dropPair_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → S.C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) (p : Pure S c) :
    let i2' := (dropPairEmb i1 j1 hij1 i2);
    let j2' := (dropPairEmb i1 j1 hij1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', dropPairEmb, hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    dropPair i2 j2 hij2 (dropPair i1 j1 hij1 p) =
    permP id (permCond_dropPairEmb_comm i1 j1 i2 j2 hij1 hij2)
    ((dropPair i1' j1' (by simp [i1', j1', hij1]) (dropPair i2' j2' hi2j2' p))) := by
  ext m
  simp [dropPair, dropEm, permP]
  apply (congr_right _ _ _ ?_).symm
  rw [dropPairEmb_comm_apply]

TODO "Prove lemmas relating to the commutation rules of `dropPair` and `prodP`."

/-!

## Contraction coefficent

-/


noncomputable def contrPCoeff {n : ℕ} {c : Fin n → S.C}
    (i j : Fin n) (hij : i ≠ j ∧ c i = S.τ (c j)) (p : Pure S c) : k :=
    (S.contr.app (Discrete.mk (c i))) (p i ⊗ₜ ((S.FD.map (eqToHom (by simp [hij]))) (p j)))

lemma contrPCoeff_dropPair {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
     (a b : Fin (n + 1 + 1 )) (hab : a ≠ b)
    (i j : Fin n) (hij : i ≠ j ∧ c (dropPairEmb a b hab i) = S.τ (c (dropPairEmb a b hab j)))
    (p : Pure S c) : (p.dropPair a b hab).contrPCoeff i j hij =
    p.contrPCoeff (dropPairEmb a b hab i) (dropPairEmb a b hab j)
      (by simpa using hij) := by rfl

lemma contrPCoeff_symm {n : ℕ} {c : Fin n → S.C} {i j : Fin n} {hij : i ≠ j ∧ c i = S.τ (c j)} {p : Pure S c} :
    p.contrPCoeff i j hij = p.contrPCoeff j i ⟨hij.1.symm, by simp [hij]⟩ := by
  rw [contrPCoeff, contrPCoeff]
  erw [S.contr_tmul_symm]
  rw [S.contr_congr (S.τ (c i)) (c j) ]
  simp
  change _ = (ConcreteCategory.hom (S.contr.app { as := c j }).hom) _
  congr 2
  · change ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
    rw [← S.FD.map_comp]
    simp
  · change ( (S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
    rw [← S.FD.map_comp]
    simp
    rfl
  · simp [hij.2]

lemma contrPCoeff_mul_dropPair {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → S.C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1 ∧ c i1 = S.τ (c j1))
    (hij2 : i2 ≠ j2 ∧ c (dropPairEmb i1 j1 hij1.1 i2) = S.τ (c (dropPairEmb i1 j1 hij1.1 j2)))
    (p : Pure S c) :
    let i2' := (dropPairEmb i1 j1 hij1.1 i2);
    let j2' := (dropPairEmb i1 j1 hij1.1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', dropPairEmb, hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    (p.contrPCoeff i1 j1 hij1) * (dropPair i1 j1 hij1.1 p).contrPCoeff i2 j2 hij2  =
    (p.contrPCoeff i2' j2' (by simp [i2', j2', hij2])) *
    (dropPair i2' j2' (by simp [i2', j2', hij2]) p).contrPCoeff i1' j1' (by simp [i1', j1', hij1]) := by
  simp only [ne_eq, contrPCoeff_dropPair, dropPairEmb_dropPairEmbPre]
  rw [mul_comm]

@[simp]
lemma contrPCoeff_invariant {n : ℕ} {c : Fin n → S.C} {i j : Fin n}
    {hij : i ≠ j ∧ c i = S.τ (c j)} {p : Pure S c}
    (g : S.G) : (g • p).contrPCoeff i j hij = p.contrPCoeff i j hij := by
  calc (g • p).contrPCoeff i j hij
    _ =  (S.contr.app (Discrete.mk (c i)))
          ((S.FD.obj _).ρ g (p i) ⊗ₜ ((S.FD.map (eqToHom (by simp [hij])))
          ((S.FD.obj _).ρ g (p j)))) := rfl
    _ = (S.contr.app (Discrete.mk (c i)))
          ((S.FD.obj _).ρ g (p i) ⊗ₜ (S.FD.obj _).ρ g ((S.FD.map (eqToHom (by simp [hij])))
          (p j))) := by
        congr 2
        simp
        have h1 := (S.FD.map (eqToHom (by simp [hij] : { as := c j } =
          (Discrete.functor (Discrete.mk ∘ S.τ)).obj { as := c i }))).comm g
        have h2 := congrFun (congrArg (fun x => x.hom) h1) (p j)
        simp at h2
        exact h2
  have h1 := (S.contr.app (Discrete.mk (c i))).comm g
  have h2 := congrFun (congrArg (fun x => x.hom) h1) ( (p i) ⊗ₜ
    ((S.FD.map (eqToHom (by simp [hij]))) (p j)))
  simp at h2
  exact h2

/-!

## Contractions

-/

noncomputable def contrP {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ c i = S.τ (c j)) (p : Pure S c) :
    S.Tensor (c ∘ dropPairEmb i j hij.1) :=
  (p.contrPCoeff i j hij) • (p.dropPair i j hij.1).toTensor

@[simp]
lemma contrP_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ c i = S.τ (c j)) (p : Pure S c) (g : S.G) :
    contrP i j hij (g • p) = g • contrP i j hij p := by
  simp [contrP, contrPCoeff_invariant, dropPair_equivariant, actionT_toTensor]

lemma contrP_symm {n : ℕ} {c : Fin (n + 1 + 1) → S.C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ c i = S.τ (c j)} {p : Pure S c} :
    contrP i j hij p = permT id (by simp)
    (contrP j i ⟨hij.1.symm, by simp [hij]⟩ p) := by
  rw [contrP, contrPCoeff_symm, dropPair_symm]
  simp [contrP, permT_pure]

#lint only simpNF
end Pure


noncomputable def Pure.contrPCoeff {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) (p : Pure S c) : k :=
    (S.contr.app (Discrete.mk (c i)))
      (p i ⊗ₜ ((S.FD.map (eqToHom (by simp [hij]))) (p (i.succAbove j))))

@[simp]
lemma Pure.contrPCoeff_invariant {n : ℕ}
    {c : Fin (n + 1 + 1) → S.C} {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)} {p : Pure S c}
    (g : S.G) : (g • p).contrPCoeff i j hij = p.contrPCoeff i j hij := by
  calc (g • p).contrPCoeff i j hij
    _ =  (S.contr.app (Discrete.mk (c i)))
          ((S.FD.obj _).ρ g (p i) ⊗ₜ ((S.FD.map (eqToHom (by simp [hij])))
          ((S.FD.obj _).ρ g (p (i.succAbove j))))) := rfl
    _ = (S.contr.app (Discrete.mk (c i)))
          ((S.FD.obj _).ρ g (p i) ⊗ₜ (S.FD.obj _).ρ g ((S.FD.map (eqToHom (by simp [hij])))
          (p (i.succAbove j)))) := by
        congr 2
        simp
        have h1 := (S.FD.map (eqToHom (by simp [hij] : { as := c (i.succAbove j) } =
          (Discrete.functor (Discrete.mk ∘ S.τ)).obj { as := c i }))).comm g
        have h2 := congrFun (congrArg (fun x => x.hom) h1) (p (i.succAbove j))
        simp at h2
        exact h2
  have h1 := (S.contr.app (Discrete.mk (c i))).comm g
  have h2 := congrFun (congrArg (fun x => x.hom) h1) ( (p i) ⊗ₜ
    ((S.FD.map (eqToHom (by simp [hij]))) (p (i.succAbove j))))
  simp at h2
  exact h2

lemma Pure.contrPCoeff_update_of_neq {n : ℕ}
    [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → S.C} {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)} {p : Pure S c}
    {k : Fin (n + 1 + 1)} {x :  S.FD.obj (Discrete.mk (c k))} (hk : k ≠ i ∧ k ≠ i.succAbove j) :
    (p.update k x).contrPCoeff i j hij = p.contrPCoeff i j hij := by
  rw [contrPCoeff]
  congr
  · rw [update, Function.update_of_ne]
    exact Ne.symm hk.1
  · rw [update, Function.update_of_ne]
    exact Ne.symm hk.2

@[simp]
lemma Pure.contrPCoeff_update_fst_add {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → S.C} {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)}
    {x y :  S.FD.obj (Discrete.mk (c i))} {p : Pure S c} :
    (p.update i (x + y)).contrPCoeff i j hij  =
    (p.update i x).contrPCoeff i j hij + (p.update i y).contrPCoeff i j hij := by
  simp [contrPCoeff, update, TensorProduct.add_tmul, map_add]
  change ((S.contr.app { as := c i })).hom.hom' _ = ((S.contr.app { as := c i })).hom.hom' _
    + ((S.contr.app { as := c i })).hom.hom' _
  simp
  congr 4
  · rw [Function.update_of_ne, Function.update_of_ne]
    · exact Fin.succAbove_ne i j
    · exact Fin.succAbove_ne i j
  · rw [Function.update_of_ne, Function.update_of_ne]
    · exact Fin.succAbove_ne i j
    · exact Fin.succAbove_ne i j

@[simp]
lemma Pure.contrPCoeff_update_fst_smul  {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → S.C} {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)}
    {r : k} {y :  S.FD.obj (Discrete.mk (c i))} {p : Pure S c} :
    (p.update i (r • y)).contrPCoeff i j hij  =
    r * (p.update i y).contrPCoeff i j hij := by
  simp [contrPCoeff, update, TensorProduct.smul_tmul, map_add]
  change ((S.contr.app { as := c i })).hom.hom' _ = r * _
  simp
  congr 1
  change ((S.contr.app { as := c i })).hom.hom' _ = ((S.contr.app { as := c i })).hom.hom' _
  congr 3
  · rw [Function.update_of_ne, Function.update_of_ne]
    · exact Fin.succAbove_ne i j
    · exact Fin.succAbove_ne i j

@[simp]
lemma Pure.contrPCoeff_update_snd_add {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → S.C} {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)}
    {x y :  S.FD.obj (Discrete.mk (c (i.succAbove j)))} {p : Pure S c} :
    (p.update (i.succAbove j) (x + y)).contrPCoeff i j hij  =
    (p.update (i.succAbove j) x).contrPCoeff i j hij +
      (p.update (i.succAbove j) y).contrPCoeff i j hij := by
  simp [contrPCoeff, update, TensorProduct.add_tmul, map_add]
  change ((S.contr.app { as := c i })).hom.hom' _ = ((S.contr.app { as := c i })).hom.hom' _
    + ((S.contr.app { as := c i })).hom.hom' _
  rw [Function.update_of_ne (Fin.ne_succAbove i j), Function.update_of_ne (Fin.ne_succAbove i j),
    Function.update_of_ne (Fin.ne_succAbove i j)]
  conv_lhs =>
    enter [2, 3]
    change ((S.FD.map (eqToHom _))).hom.hom' (x + y)
  simp [contrPCoeff, update, TensorProduct.tmul_add, map_add]
  rfl

@[simp]
lemma Pure.contrPCoeff_update_snd_smul {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → S.C} {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)}
    {r : k} {y :  S.FD.obj (Discrete.mk (c (i.succAbove j)))} {p : Pure S c} :
    (p.update (i.succAbove j) (r • y)).contrPCoeff i j hij  =
    r * (p.update (i.succAbove j) y).contrPCoeff i j hij := by
  simp [contrPCoeff, update, TensorProduct.add_tmul, map_add]
  change ((S.contr.app { as := c i })).hom.hom' _ =  r * _
  rw [Function.update_of_ne (Fin.ne_succAbove i j), Function.update_of_ne (Fin.ne_succAbove i j)]
  conv_lhs =>
    enter [2, 3]
    change ((S.FD.map (eqToHom _))).hom.hom' (r • y)
  simp
  rfl


end Tensor

end TensorSpecies
/-- The contraction of indices of a pure tensor. This is a map into
  `Tensor c` as when `n = 0` it does not give back a pure tensor. -/
noncomputable def Pure.contrP {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) (p : Pure S c) :
    S.Tensor (c ∘ i.succAbove ∘ j.succAbove) :=
    (p.contrPCoeff i j hij) • ((p.drop i).drop j).toTensor

@[simp]
lemma Pure.contrP_update_add {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) (p : Pure S c)
    (k : Fin (n + 1 + 1)) (x y :  S.FD.obj (Discrete.mk (c k))) :
    (update p k (x + y)).contrP i j hij =
    (update p k x).contrP i j hij + (update p k y).contrP i j hij := by
  rw [contrP, contrP, contrP]
  by_cases hk : k ≠ i ∧ k ≠ i.succAbove j
  · rw [Pure.contrPCoeff_update_of_neq hk, Pure.contrPCoeff_update_of_neq hk,
        Pure.contrPCoeff_update_of_neq hk]
    rw [← smul_add]
    congr
    have hk' := Fin.eq_self_or_eq_succAbove i k
    simp_all
    obtain ⟨k, rfl⟩ := hk'
    simp
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hk
    have hk' := Fin.eq_self_or_eq_succAbove j k
    simp_all
    obtain ⟨k, rfl⟩ := hk'
    simp
  · rw [Mathlib.Tactic.PushNeg.not_and_or_eq] at hk
    simp at hk
    rcases hk with rfl | rfl
    · simp [add_smul]
    · simp [add_smul]

lemma Pure.contrP_update_smul {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) (p : Pure S c)
    (m : Fin (n + 1 + 1)) (r : k) (x :  S.FD.obj (Discrete.mk (c m))) :
    (update p m (r • x)).contrP i j hij =
    r • (update p m x).contrP i j hij := by
  rw [contrP, contrP]
  by_cases hk : m ≠ i ∧ m ≠ i.succAbove j
  · rw [Pure.contrPCoeff_update_of_neq hk, Pure.contrPCoeff_update_of_neq hk]
    rw [← smul_comm]
    congr
    have hk' := Fin.eq_self_or_eq_succAbove i m
    simp_all
    obtain ⟨m, rfl⟩ := hk'
    simp
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hk
    have hk' := Fin.eq_self_or_eq_succAbove j m
    simp_all
    obtain ⟨m, rfl⟩ := hk'
    simp
  · rw [Mathlib.Tactic.PushNeg.not_and_or_eq] at hk
    simp at hk
    rcases hk with rfl | rfl
    · simp [smul_smul]
    · simp [smul_smul]

noncomputable def Pure.contrPMap {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) :
    MultilinearMap k (fun i => S.FD.obj (Discrete.mk (c i)))
    (S.Tensor (c ∘ i.succAbove ∘ j.succAbove)) where
  toFun p :=  contrP i j hij p
  map_update_add' p k x y := by
    change (update p k (x + y)).contrP i j hij = _
    rw [Pure.contrP_update_add]
    rfl
  map_update_smul' p k r y := by
    change (update p k (r • y)).contrP i j hij = _
    rw [Pure.contrP_update_smul]
    rfl

noncomputable def contrT {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) :
    Tensor S c →ₗ[k] Tensor S (c ∘ i.succAbove ∘ j.succAbove) :=
  PiTensorProduct.lift (Pure.contrPMap i j hij)

@[simp]
lemma contrT_pure {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) (p : Pure S c) :
    contrT i j hij p.toTensor = p.contrP i j hij := by
  simp only [contrT, Pure.toTensor]
  change _ = ((Pure.contrPMap i j hij) p)
  conv_rhs => rw [← PiTensorProduct.lift.tprod]
  rfl

@[simp]
lemma contrT_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → S.C} (i : Fin (n + 1 + 1))
    (j : Fin (n + 1)) (hij : c (i.succAbove j) = S.τ (c i)) (g : S.G)
    (t : Tensor S c) :
    contrT i j hij (g • t) = g • contrT i j hij t := by
  let P (t : Tensor S c) : Prop := contrT i j hij (g • t) = g • contrT i j hij t
  change P t
  apply induction_on_pure
  · intro p
    simp [P]
    rw [actionT_toTensor, contrT_pure]
    simp [Pure.contrP]
    congr 1
    exact Eq.symm actionT_toTensor
  · intro p q hp
    simp [P, hp]
  · intro p r hr hp
    simp [P, hp, hr]


/-!

## Pairs and quads for drop
-/

lemma Pure.drop_pair_set_eq_or {n : ℕ}  {i i'  : Fin (n + 1 + 1)} {j j' : Fin (n + 1)}
    (hSet : {i, i.succAbove j} = ({i', i'.succAbove j'} : Finset (Fin (n + 1 +1)))) :
    (i' = i ∧ j' = j) ∨ (i = i'.succAbove j' ∧ i' = i.succAbove j) := by
  rw [Finset.ext_iff] at hSet
  have hSeti := hSet i
  have hSetj := hSet (i.succAbove j)
  simp at hSeti hSetj
  have ht : i.succAbove j ≠ i := by exact Fin.succAbove_ne i j
  rcases hSeti with hSeti | hSeti
  · subst hSeti
    simp_all
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hSetj
    exact Or.symm (Or.inr (id (Eq.symm hSetj)))
  · subst hSeti
    simp_all

lemma Pure.drop_pair_set_succAbove {n : ℕ}  {i i'  : Fin (n + 1 + 1)}
    {j j' : Fin (n + 1)}
    (hSet : {i, i.succAbove j} = ({i', i'.succAbove j'} : Finset (Fin (n + 1 +1))))
    (m : Fin n) : i.succAbove (j.succAbove m) = i'.succAbove (j'.succAbove m) := by
  let f : Fin n ↪o Fin (n + 1 + 1) :=
    ⟨⟨i.succAboveOrderEmb ∘ j.succAboveOrderEmb, by
      refine (EmbeddingLike.comp_injective _ i.succAboveOrderEmb).mpr ?_
      exact RelEmbedding.injective j.succAboveOrderEmb⟩,
      by simp [Fin.succAbove_le_succAbove_iff]⟩
  let g : Fin n ↪o Fin (n + 1 + 1) := ⟨⟨i'.succAboveOrderEmb ∘ j'.succAboveOrderEmb, by
      refine (EmbeddingLike.comp_injective _ i'.succAboveOrderEmb).mpr ?_
      exact RelEmbedding.injective j'.succAboveOrderEmb⟩,
      by simp [Fin.succAbove_le_succAbove_iff]⟩
  have hx {n : ℕ} (X : Set (Fin n)) (i : Fin (n + 1)) :
      i.succAbove '' Xᶜ = ({i} ∪ i.succAbove '' X)ᶜ := by
    rw [← compl_inj_iff, Function.Injective.compl_image_eq Fin.succAbove_right_injective]
    simp
  have h : f = g := by
    rw [← OrderEmbedding.range_inj]
    simp [f, g, Set.range_comp]
    change i.succAbove '' Set.range j.succAbove = i'.succAbove '' Set.range j'.succAbove
    rw [Fin.range_succAbove, Fin.range_succAbove, hx, hx ]
    simp
    rw [Set.pair_comm]
    refine Set.toFinset_inj.mp ?_
    simp
    rw [hSet]
    exact Finset.pair_comm i' (i'.succAbove j')
  simpa [f,g] using congrFun (congrArg (fun x => x.toFun) h) m

lemma Pure.pair_set_colour {n : ℕ}
    {c : Fin (n + 1 + 1) → S.C} {i  : Fin (n + 1 + 1)}
    {j : Fin (n + 1)}
    {i' : Fin (n + 1 + 1)} {j' : Fin (n + 1)}
    (hSet : {i, i.succAbove j} = ({i', i'.succAbove j'} : Finset (Fin (n + 1 +1))))
    (hij : c (i.succAbove j) = S.τ (c i)) : c (i'.succAbove j') = S.τ (c i') := by
  have hn := drop_pair_set_eq_or hSet
  rcases hn with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · subst hi hj
    exact hij
  · conv_rhs => rw [hj, hij]
    simp [hi]

lemma Pure.contrPCoeff_eq_finset {n : ℕ}
    {c : Fin (n + 1 + 1) → S.C} {i  : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)}
    (i' : Fin (n + 1 + 1)) (j' : Fin (n + 1))
    (hSet : {i, i.succAbove j} = ({i', i'.succAbove j'} : Finset (Fin (n + 1 +1))))
    {p : Pure S c} : p.contrPCoeff i j hij = p.contrPCoeff i' j' (pair_set_colour hSet hij) := by
  have hn := drop_pair_set_eq_or hSet
  rcases hn with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · subst hi hj
    rfl
  · simp [contrPCoeff]
    erw [S.contr_tmul_symm]
    rw [S.contr_congr (S.τ (c i)) (c i') (by rw [← hij, hj])]
    simp
    change _ = (ConcreteCategory.hom (S.contr.app { as := c i' }).hom) _
    congr 2
    · change ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
      rw [← S.FD.map_comp]
      simp
      simp [← Pure.congr_right _ _ _ hj]
      rfl
    · change ( (S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
      rw [← S.FD.map_comp]
      simp
      simp [← Pure.congr_right _ _ _ hi]
      change ( (S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
      rw [← S.FD.map_comp]
      simp
      rfl

lemma PermCond.succAbove_pair_finset  {n : ℕ}
    {c : Fin (n + 1 + 1) → S.C} {i  : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {i' : Fin (n + 1 + 1)} {j' : Fin (n + 1)}
    (hSet : {i, i.succAbove j} = ({i', i'.succAbove j'} : Finset (Fin (n + 1 +1)))) :
    PermCond (c ∘ i'.succAbove ∘ j'.succAbove) (c ∘ i.succAbove ∘ j.succAbove) id := by
  apply And.intro (Function.bijective_id)
  · simp
    intro m
    rw [Pure.drop_pair_set_succAbove hSet]

lemma contrT_eq_finset {n : ℕ}
    {c : Fin (n + 1 + 1) → S.C} {i  : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)}
    (i' : Fin (n + 1 + 1)) (j' : Fin (n + 1))
    (hSet : {i, i.succAbove j} = ({i', i'.succAbove j'} : Finset (Fin (n + 1 +1))))
    {t : Tensor S c} : t.contrT i j hij = permT id (PermCond.succAbove_pair_finset hSet)
    (t.contrT i' j' (Pure.pair_set_colour hSet hij)) := by
  let P (t : Tensor S c) : Prop := t.contrT i j hij =
    permT id (PermCond.succAbove_pair_finset hSet) (t.contrT i' j'
    (Pure.pair_set_colour hSet hij))
  change P t
  apply induction_on_pure
  · intro p
    simp [P, Pure.contrP]
    congr 1
    · exact Pure.contrPCoeff_eq_finset i' j' hSet
    rw [permT_pure]
    congr
    ext m
    simp [Pure.drop, Pure.permP]
    refine (Pure.congr_right _ _ _ ?_).symm
    exact Pure.drop_pair_set_succAbove hSet m
  · intro r t ht
    simp_all [P]
  · intro t1 t2 ht1 ht2
    simp_all [P]

lemma Pure.pair_swap_finset_eq {n : ℕ} (i  : Fin (n + 1 + 1))
    (j : Fin (n + 1)) :
    {i, i.succAbove j} = ({i.succAbove j,
      (i.succAbove j).succAbove (j.predAbove i)} : Finset (Fin (n + 1 +1))) := by
  have hl : (i.succAbove j).succAbove (j.predAbove i) = i := by
    ext
    simp [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.le_def]
    split_ifs
    all_goals
      simp_all [Fin.lt_def, Fin.le_def]
      try omega
  rw [hl]
  exact Finset.pair_comm i (i.succAbove j)


open Pure in
lemma contrT_swap {n : ℕ} {c : Fin (n + 1 + 1) → S.C} {i  : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)}  {t : Tensor S c} :
    t.contrT i j hij = permT id (PermCond.succAbove_pair_finset (pair_swap_finset_eq i j))
    (t.contrT (i.succAbove j) (j.predAbove i)
    (Pure.pair_set_colour (pair_swap_finset_eq i j) hij)) := by
  rw [contrT_eq_finset]
  exact pair_swap_finset_eq i j

def DropSetQuad  {n : ℕ} (i4 i4'  : Fin (n + 1 + 1 + 1 + 1))
    (i3 i3'  : Fin (n + 1 + 1 + 1)) (i2 i2'  : Fin (n + 1 + 1)) (i1 i1'  : Fin (n + 1)) :
    Prop := {{i4, i4.succAbove i3}, {i4.succAbove (i3.succAbove i2),
    i4.succAbove (i3.succAbove (i2.succAbove i1))}} =
    ({{i4', i4'.succAbove i3'}, {i4'.succAbove (i3'.succAbove i2'),
    i4'.succAbove (i3'.succAbove (i2'.succAbove i1'))}} : Finset (Finset (Fin (n + 1 + 1 + 1 + 1))))

namespace DropSetQuad

variable {n : ℕ} {i4 i4'  : Fin (n + 1 + 1 + 1 + 1)}
    {i3 i3' : Fin (n + 1 + 1 + 1)} {i2 i2'  : Fin (n + 1 + 1)} {i1 i1'  : Fin (n + 1)}
    (d : DropSetQuad i4 i4' i3 i3' i2 i2' i1 i1')

instance : Decidable (DropSetQuad i4 i4' i3 i3' i2 i2' i1 i1') :=
  inferInstanceAs (Decidable ({{i4, i4.succAbove i3}, {i4.succAbove (i3.succAbove i2),
    i4.succAbove (i3.succAbove (i2.succAbove i1))}} =
    ({{i4', i4'.succAbove i3'}, {i4'.succAbove (i3'.succAbove i2'),
    i4'.succAbove (i3'.succAbove (i2'.succAbove i1'))}} :
    Finset (Finset (Fin (n + 1 + 1 + 1 + 1))))))


end DropSetQuad

lemma
end Tensor

end TensorSpecies
