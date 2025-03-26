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

lemma Pure.drop_pair_set_succAbove_succAbove {n : ℕ}  {i i'  : Fin (n + 1 + 1)}
    {j j' : Fin (n + 1)}
    (hSet : {i, i.succAbove j} = ({i', i'.succAbove j'} : Finset (Fin (n + 1 +1))))
    (m : Fin n) : i.succAbove (j.succAbove m) = i'.succAbove (j'.succAbove m) := by
  have hn := drop_pair_set_eq_or hSet
  rcases hn with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · subst hi hj
    rfl
  ·



lemma Pure.contrPCoeff_eq_finset {n : ℕ}
    {c : Fin (n + 1 + 1) → S.C} {i  : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)}
    (i' : Fin (n + 1 + 1)) (j' : Fin (n + 1)) (hij' : c (i'.succAbove j') = S.τ (c i'))
    (hSet : {i, i.succAbove j} = ({i', i'.succAbove j'} : Finset (Fin (n + 1 +1))))
    {p : Pure S c} : p.contrPCoeff i j hij = p.contrPCoeff i' j' hij' := by
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
    · change ( (S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
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


lemma contrT_eq_finset {n : ℕ}
    {c : Fin (n + 1 + 1) → S.C} {i  : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {hij : c (i.succAbove j) = S.τ (c i)}
    (i' : Fin (n + 1 + 1)) (j' : Fin (n + 1)) (hij' : c (i'.succAbove j') = S.τ (c i'))
    (hSet : {i, i.succAbove j} = ({i', i'.succAbove j'} : Finset (Fin (n + 1 +1))))
    {t : Tensor S c} : t.contrT i j hij = permT id (by sorry) (t.contrT i' j' hij') := by
  let P (t : Tensor S c) : Prop := t.contrT i j hij = permT id (by sorry) (t.contrT i' j' hij')
  change P t
  apply induction_on_pure
  · intro p
    simp [P, Pure.contrP]
    congr 1
    · exact Pure.contrPCoeff_eq_finset i' j' hij' hSet
    rw [permT_pure]
    congr
    ext m
    simp [Pure.drop, Pure.permP]
  · sorry
  · sorry


end Tensor

end TensorSpecies
